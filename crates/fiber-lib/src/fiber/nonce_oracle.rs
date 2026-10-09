//! MuSig2 nonce-use oracle, for fault-injection runs (fiber-jepsen) and unit tests.
//!
//! Compiled into unit tests, and into other builds with the `nonce-oracle` feature. It
//! records every partial signature this process produces, keyed by a hash of the signer's
//! *public* nonce, together with a hash of the signing context: the aggregated key, the
//! aggregate nonce and the message. Secret nonces are never written anywhere.
//!
//! Records:
//! - `Sent`: a partial signature that leaves the node. Every V2 signature is recorded as
//!   `Sent`, because a V2 nonce may sign exactly one context, sent or aggregated.
//! - `Aggregated`: a V1 partial signature combined locally with the peer's. It becomes
//!   visible only if that transaction is published.
//! - `Cached`: V2 returned the signature it had already made for this nonce and context.
//! - `Conflict`: V2 refused to bind a consumed nonce to a different context.
//! - `Reestablish`: a channel started reestablishing. Coverage only, not a signature.
//! - `Replay`: V2 reestablishment resent its stored CommitmentSigned and/or RevokeAndAck
//!   verbatim, without signing again. Coverage only: the peer had not received them.
//!
//! With two-nonce MuSig2, partial signatures from one secret nonce over three different
//! contexts reveal the signing key. A nonce sent in two different contexts is reported as a
//! violation: one more revealed signature, such as a published transaction signed with the
//! same nonce, would be enough.
//!
//! When `FIBER_NONCE_ORACLE_FILE` is set, every record is also appended to that file, with
//! one `write(2)` per line, before the signature is returned to the caller. The history
//! survives a killed process (SIGKILL, not a power loss) and can be checked across
//! restarts: each line carries the process id and a per-process `boot` tag.

use std::collections::HashMap;
use std::io::Write;
use std::panic::Location;
use std::sync::{LazyLock, Mutex, MutexGuard};

use ckb_hash::blake2b_256;
use musig2::{secp::Point, AggNonce, BinaryEncoding, KeyAggContext, PubNonce, SecNonce};

/// How a partial signature leaves the signing code.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Use {
    /// Leaves the node (sent to the peer); every V2 signature.
    Sent,
    /// Aggregated locally (V1); visible only if the transaction is published.
    Aggregated,
    /// V2 returned its cached signature for the same nonce and context.
    Cached,
}

type Id = [u8; 16];

#[derive(Default)]
struct NonceUses {
    sent: Vec<Id>,
    aggregated: Vec<Id>,
}

#[derive(Default)]
struct State {
    nonces: HashMap<Id, NonceUses>,
    cached: u64,
    conflicts: u64,
    reestablishes: u64,
    replayed_cs: u64,
    replayed_ack: u64,
    violations: u64,
}

static STATE: LazyLock<Mutex<State>> = LazyLock::new(|| Mutex::new(State::default()));

struct Log {
    file: std::fs::File,
    boot: String,
}

static LOG: LazyLock<Option<Mutex<Log>>> = LazyLock::new(|| {
    let path = std::env::var_os("FIBER_NONCE_ORACLE_FILE")?;
    #[allow(unused_mut)]
    let mut file = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(&path)
        .ok()?;
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or_default();
    let boot = format!("{:08x}", (nanos as u32) ^ std::process::id().rotate_left(16));
    #[cfg(feature = "nonce-oracle-plant")]
    plant_after_restart(&path, &mut file, &boot);
    Some(Mutex::new(Log { file, boot }))
});

fn state() -> MutexGuard<'static, State> {
    STATE.lock().unwrap_or_else(|e| e.into_inner())
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn id(bytes: &[u8]) -> Id {
    let mut out = [0; 16];
    out.copy_from_slice(&blake2b_256(bytes)[..16]);
    out
}

fn nonce_id(public_nonce: &PubNonce) -> Id {
    id(&public_nonce.to_bytes())
}

fn aggregated_key(key_agg_ctx: &KeyAggContext) -> [u8; 32] {
    key_agg_ctx.aggregated_pubkey::<Point>().serialize_xonly()
}

fn context_id(key_agg_ctx: &KeyAggContext, agg_nonce: &AggNonce, message: &[u8]) -> Id {
    id(&[
        aggregated_key(key_agg_ctx).as_slice(),
        agg_nonce.to_bytes().as_slice(),
        message,
    ]
    .concat())
}

/// Appends one record line. Nothing is written unless `FIBER_NONCE_ORACLE_FILE` is set.
fn write_line(record: std::fmt::Arguments<'_>) {
    if let Some(log) = LOG.as_ref() {
        let mut log = log.lock().unwrap_or_else(|e| e.into_inner());
        let line = format!(
            "NONCE-ORACLE {record} pid={} boot={}\n",
            std::process::id(),
            log.boot
        );
        let _ = log.file.write_all(line.as_bytes());
    }
}

/// A label for V2 records: channel, commitment owner, commitment number and purpose.
pub(crate) fn v2_label(channel_id: &[u8], owner: &[u8], number: u64, purpose: &str) -> String {
    format!(
        "ch={}/owner={}/n={number}/{purpose}",
        hex(&channel_id[..4]),
        hex(&owner[1..5])
    )
}

/// Records one V1 partial signature, before it leaves the signing code.
#[track_caller]
pub(crate) fn record(
    usage: Use,
    secnonce: &SecNonce,
    key_agg_ctx: &KeyAggContext,
    agg_nonce: &AggNonce,
    message: &[u8],
) {
    let label = format!("key={}", hex(&aggregated_key(key_agg_ctx)[..4]));
    record_at(
        Location::caller(),
        usage,
        nonce_id(&secnonce.public_nonce()),
        context_id(key_agg_ctx, agg_nonce, message),
        &label,
    );
}

/// Records one V2 partial signature (or a cached one), before it leaves the signing code.
#[track_caller]
pub(crate) fn record_public(
    usage: Use,
    public_nonce: &PubNonce,
    key_agg_ctx: &KeyAggContext,
    agg_nonce: &AggNonce,
    message: &[u8],
    label: &str,
) {
    record_at(
        Location::caller(),
        usage,
        nonce_id(public_nonce),
        context_id(key_agg_ctx, agg_nonce, message),
        label,
    );
}

/// Records that V2 refused to bind a consumed nonce to a different context.
#[track_caller]
pub(crate) fn conflict(public_nonce: &PubNonce, label: &str) {
    let site = Location::caller();
    write_line(format_args!(
        "Conflict nonce={} context=- site={}:{} label={label}",
        hex(&nonce_id(public_nonce)),
        site.file(),
        site.line()
    ));
    state().conflicts += 1;
}

/// Records that a channel started reestablishing (V1 or V2).
#[track_caller]
pub(crate) fn reestablish(channel_id: &[u8], version: u8) {
    let site = Location::caller();
    write_line(format_args!(
        "Reestablish channel={} v={version} site={}:{}",
        hex(&channel_id[..8]),
        site.file(),
        site.line()
    ));
    state().reestablishes += 1;
}

/// Records what a V2 reestablishment resent verbatim: its stored CommitmentSigned (`cs`)
/// and/or its cached RevokeAndAck (`ack`).
#[track_caller]
pub(crate) fn replay(channel_id: &[u8], cs: bool, ack: bool) {
    let site = Location::caller();
    write_line(format_args!(
        "Replay channel={} cs={cs} ack={ack} site={}:{}",
        hex(&channel_id[..8]),
        site.file(),
        site.line()
    ));
    let mut state = state();
    state.replayed_cs += u64::from(cs);
    state.replayed_ack += u64::from(ack);
}

/// Returns true when this call made the nonce a violation.
fn record_at(site: &Location<'_>, usage: Use, nonce: Id, context: Id, label: &str) -> bool {
    write_line(format_args!(
        "{usage:?} nonce={} context={} site={}:{} label={label}",
        hex(&nonce),
        hex(&context),
        site.file(),
        site.line()
    ));

    let mut state = state();
    if usage == Use::Cached {
        state.cached += 1;
        return false;
    }
    let (sent, aggregated_only) = {
        let uses = state.nonces.entry(nonce).or_default();
        let list = match usage {
            Use::Sent => &mut uses.sent,
            _ => &mut uses.aggregated,
        };
        if list.contains(&context) {
            return false;
        }
        list.push(context);
        let aggregated_only = uses
            .aggregated
            .iter()
            .filter(|c| !uses.sent.contains(c))
            .count();
        (uses.sent.len(), aggregated_only)
    };
    if usage != Use::Sent || sent < 2 {
        return false;
    }
    state.violations += 1;
    eprintln!(
        "NONCE-ORACLE VIOLATION nonce={} sent_contexts={sent} aggregated_only_contexts={aggregated_only} site={}:{} label={label} thread={:?}",
        hex(&nonce),
        site.file(),
        site.line(),
        std::thread::current().name(),
    );
    true
}

/// One line for the end of an in-process run: nonces seen, nonces sent in two or more
/// contexts, nonces sent once that also signed a different context aggregated locally (V1
/// does this for commitment transactions), the most contexts one nonce aggregated, cached
/// signatures, refused conflicts, reestablishments, verbatim V2 replays and violations.
#[allow(dead_code)]
pub(crate) fn summary() -> String {
    let state = state();
    let sent_twice = state.nonces.values().filter(|u| u.sent.len() >= 2).count();
    let sent_once_and_aggregated = state
        .nonces
        .values()
        .filter(|u| u.sent.len() == 1 && u.aggregated.iter().any(|c| !u.sent.contains(c)))
        .count();
    let max_aggregated = state
        .nonces
        .values()
        .map(|u| u.aggregated.len())
        .max()
        .unwrap_or(0);
    format!(
        "nonces={} sent_in_2plus_contexts={sent_twice} sent_once_plus_other_aggregated={sent_once_and_aggregated} max_aggregated_contexts={max_aggregated} cached={} conflicts={} reestablish={} replayed_cs={} replayed_ack={} violations={}",
        state.nonces.len(),
        state.cached,
        state.conflicts,
        state.reestablishes,
        state.replayed_cs,
        state.replayed_ack,
        state.violations
    )
}

/// Planted-reuse self-test (feature `nonce-oracle-plant`, never in a measured build): when a
/// process starts on a file an earlier process wrote, it appends a second `Sent` record, with
/// a made-up context, for the last nonce the earlier process sent. A checker that pools the
/// file across restarts must report that nonce as a violation.
#[cfg(feature = "nonce-oracle-plant")]
fn plant_after_restart(path: &std::ffi::OsStr, file: &mut std::fs::File, boot: &str) {
    let Ok(previous) = std::fs::read_to_string(path) else {
        return;
    };
    let Some(last) = previous
        .lines()
        .rev()
        .find(|l| l.starts_with("NONCE-ORACLE Sent "))
    else {
        return;
    };
    let field = |name: &str| last.split(' ').find_map(|f| f.strip_prefix(name));
    let (Some(nonce), Some(context)) = (field("nonce="), field("context=")) else {
        return;
    };
    let planted = hex(&id(&[context.as_bytes(), b"planted"].concat()));
    let _ = file.write_all(
        format!(
            "NONCE-ORACLE Sent nonce={nonce} context={planted} site=planted:0 label=planted pid={} boot={boot}\n",
            std::process::id()
        )
        .as_bytes(),
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::gen_utils::gen_rand_fiber_public_key;
    use musig2::SecNonceBuilder;

    fn fresh_secnonce() -> SecNonce {
        SecNonceBuilder::new(rand::random::<[u8; 32]>()).build()
    }

    fn key_agg_ctx() -> KeyAggContext {
        KeyAggContext::new([gen_rand_fiber_public_key(), gen_rand_fiber_public_key()])
            .expect("valid keys")
    }

    fn at(usage: Use, secnonce: &SecNonce, ctx: &KeyAggContext, agg: &AggNonce, msg: &[u8]) -> bool {
        record_at(
            Location::caller(),
            usage,
            nonce_id(&secnonce.public_nonce()),
            context_id(ctx, agg, msg),
            "test",
        )
    }

    #[test]
    fn test_nonce_oracle_flags_a_nonce_sent_in_two_contexts() {
        let ctx = key_agg_ctx();
        let secnonce = fresh_secnonce();
        let agg_nonce = AggNonce::sum([secnonce.public_nonce(), fresh_secnonce().public_nonce()]);
        let other_agg_nonce =
            AggNonce::sum([secnonce.public_nonce(), fresh_secnonce().public_nonce()]);

        // The same context twice, and a different context that is only aggregated locally,
        // are V1's normal use of a commitment nonce.
        assert!(!at(Use::Sent, &secnonce, &ctx, &agg_nonce, b"commitment"));
        assert!(!at(Use::Sent, &secnonce, &ctx, &agg_nonce, b"commitment"));
        assert!(!at(Use::Aggregated, &secnonce, &ctx, &agg_nonce, b"local commitment"));
        // The same message with another aggregate nonce is a second sent context.
        assert!(at(Use::Sent, &secnonce, &ctx, &other_agg_nonce, b"commitment"));
        // So is another message with the first aggregate nonce.
        assert!(at(Use::Sent, &secnonce, &ctx, &agg_nonce, b"other"));
    }

    #[test]
    fn test_nonce_oracle_cached_replays_are_not_new_contexts() {
        let ctx = key_agg_ctx();
        let secnonce = fresh_secnonce();
        let agg_nonce = AggNonce::sum([secnonce.public_nonce(), fresh_secnonce().public_nonce()]);

        assert!(!at(Use::Sent, &secnonce, &ctx, &agg_nonce, b"commitment"));
        // A cached replay, even of another context, is counted but never a violation: the
        // cache returns a signature that was already made.
        assert!(!at(Use::Cached, &secnonce, &ctx, &agg_nonce, b"commitment"));
        assert!(!at(Use::Cached, &secnonce, &ctx, &agg_nonce, b"other"));
        conflict(&secnonce.public_nonce(), "test");
        assert!(state().cached >= 2);
        assert!(state().conflicts >= 1);
    }
}
