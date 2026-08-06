//! Balance accounting kernel — multi-asset `(pubkey, asset)` ledger.
//!
//! Rust shadow of `src/core/balance_kernel.py` (the transition form of
//! `src/state/balances.py`). Two operations compose from the authoritative
//! `BalanceTable`:
//!
//! * `credit` — funding primitive (genesis / settlement payout).
//! * `transfer` — supply-conserving move of `amount` of `asset` from `sender`
//!   to `recipient`; rejects insufficient balance.
//!
//! Balances are keyed per `(pubkey, asset)`; an operation on one key never
//! perturbs another (the balance-kernel analogue of the fee-router asset-scoping
//! lesson; see `docs/runtime/SEMANTIC_DRIFT_CONTROLS.md`).

use std::collections::BTreeMap;

use thiserror::Error;
use zenodex_asset_transfer_core::{
    settle_transfer_balances_v1, AssetTransferArithmeticRejectV1,
    MAX_ASSET_TRANSFER_BALANCE_ATOMS_V1,
};

use crate::canonical::{
    domain_sep_bytes, encode_bytes, encode_uvarint, hex_to_bytes_fixed, sha256_hex,
};

/// Bound on any balance / amount (matches the fee-router u128 boundary).
pub const MAX_BALANCE: u128 = MAX_ASSET_TRANSFER_BALANCE_ATOMS_V1;
const PUBKEY_NBYTES: usize = 48;
const ASSET_NBYTES: usize = 32;
const STATE_LABEL: &str = "balance_table";
const RECEIPT_LABEL: &str = "balance_receipt";
const STATE_VERSION: u32 = 1;
const RECEIPT_VERSION: u32 = 1;
const KIND_CREDIT: &str = "credit";
const KIND_TRANSFER: &str = "transfer";

/// Why a balance operation was rejected. Stable `code()` matches Python.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum BalanceRejectedReason {
    #[error("invalid sender")]
    InvalidSender,
    #[error("invalid recipient")]
    InvalidRecipient,
    #[error("invalid asset")]
    InvalidAsset,
    #[error("invalid amount")]
    InvalidAmount,
    #[error("self transfer")]
    SelfTransfer,
    #[error("insufficient balance")]
    InsufficientBalance,
    #[error("balance overflow")]
    BalanceOverflow,
}

impl BalanceRejectedReason {
    pub fn code(self) -> &'static str {
        match self {
            BalanceRejectedReason::InvalidSender => "invalid_sender",
            BalanceRejectedReason::InvalidRecipient => "invalid_recipient",
            BalanceRejectedReason::InvalidAsset => "invalid_asset",
            BalanceRejectedReason::InvalidAmount => "invalid_amount",
            BalanceRejectedReason::SelfTransfer => "self_transfer",
            BalanceRejectedReason::InsufficientBalance => "insufficient_balance",
            BalanceRejectedReason::BalanceOverflow => "balance_overflow",
        }
    }

    pub fn reason_str(self) -> String {
        self.code().to_string()
    }
}

fn python_strip(value: &str) -> &str {
    value.trim_matches(|c: char| {
        c.is_whitespace() || matches!(c, '\u{001c}' | '\u{001d}' | '\u{001e}' | '\u{001f}')
    })
}

fn canonical_hex(value: &str, nbytes: usize) -> Option<String> {
    let trimmed = python_strip(value);
    let body = trimmed
        .strip_prefix("0x")
        .or_else(|| trimmed.strip_prefix("0X"))
        .unwrap_or(trimmed);
    if body.len() != nbytes * 2 || !body.bytes().all(|b| b.is_ascii_hexdigit()) {
        return None;
    }
    Some(format!("0x{}", body.to_ascii_lowercase()))
}

/// Canonicalize a 48-byte pubkey, else `None`.
///
/// Mirrors `canonical_hex_fixed_allow_0x`: raw hex, `0x` / `0X` prefixes,
/// mixed case, and surrounding whitespace collapse to lowercase `0x` form.
pub fn canonical_pubkey(value: &str) -> Option<String> {
    canonical_hex(value, PUBKEY_NBYTES)
}

/// Canonicalize a 32-byte asset id, else `None`.
pub fn canonical_asset(value: &str) -> Option<String> {
    canonical_hex(value, ASSET_NBYTES)
}

fn raw_pubkey_bytes(canonical: &str) -> Vec<u8> {
    hex_to_bytes_fixed(canonical, PUBKEY_NBYTES).expect("validated canonical pubkey hex")
}

fn raw_asset_bytes(canonical: &str) -> Vec<u8> {
    hex_to_bytes_fixed(canonical, ASSET_NBYTES).expect("validated canonical asset hex")
}

/// Sparse `(pubkey, asset) -> amount` table (no zero entries).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct BalanceState {
    balances: BTreeMap<(String, String), u128>,
}

impl BalanceState {
    /// Build a sparse balance state from explicit entries.
    ///
    /// Used by the live authority bridge to evaluate one transition from the
    /// current Python balance table. Entries are canonicalized; duplicate
    /// decoded `(pubkey, asset)` keys and zero/out-of-domain balances reject.
    pub fn from_entries<I, P, A>(entries: I) -> Result<BalanceState, &'static str>
    where
        I: IntoIterator<Item = (P, A, u128)>,
        P: AsRef<str>,
        A: AsRef<str>,
    {
        let mut balances = BTreeMap::new();
        for (pubkey, asset, amount) in entries {
            let pk = canonical_pubkey(pubkey.as_ref()).ok_or("invalid_recipient")?;
            let ast = canonical_asset(asset.as_ref()).ok_or("invalid_asset")?;
            if !valid_amount(amount) {
                return Err("invalid_amount");
            }
            if balances.insert((pk, ast), amount).is_some() {
                return Err("duplicate_balance_key");
            }
        }
        Ok(BalanceState { balances })
    }

    /// Canonical sparse entries in root-encoding order.
    pub fn entries(&self) -> impl Iterator<Item = (&str, &str, u128)> {
        self.balances
            .iter()
            .map(|((pubkey, asset), amount)| (pubkey.as_str(), asset.as_str(), *amount))
    }

    /// Balance for `(pubkey, asset)` (0 if absent / invalid).
    pub fn balance_of(&self, pubkey: &str, asset: &str) -> u128 {
        match (canonical_pubkey(pubkey), canonical_asset(asset)) {
            (Some(pk), Some(a)) => *self.balances.get(&(pk, a)).unwrap_or(&0),
            _ => 0,
        }
    }

    fn set(&self, pubkey: &str, asset: &str, amount: u128) -> BalanceState {
        let mut balances = self.balances.clone();
        let key = (pubkey.to_string(), asset.to_string());
        if amount == 0 {
            balances.remove(&key);
        } else {
            balances.insert(key, amount);
        }
        BalanceState { balances }
    }

    /// Canonical state root. BTreeMap iterates `(pubkey, asset)` in sorted
    /// (== raw-byte) order, matching the Python encoder and `state_root.py`.
    pub fn state_root(&self) -> String {
        let mut buf = domain_sep_bytes(STATE_LABEL, STATE_VERSION);
        buf.extend(encode_uvarint(self.balances.len() as u128));
        for ((pubkey, asset), amount) in &self.balances {
            buf.extend(raw_pubkey_bytes(pubkey));
            buf.extend(raw_asset_bytes(asset));
            buf.extend(encode_uvarint(*amount));
        }
        sha256_hex(&buf)
    }
}

/// Receipt for a credit / transfer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BalanceReceipt {
    pub kind: &'static str,
    pub sender: Option<String>,
    pub recipient: String,
    pub asset: String,
    pub amount: u128,
}

impl BalanceReceipt {
    pub fn receipt_hash(&self) -> String {
        let mut buf = domain_sep_bytes(RECEIPT_LABEL, RECEIPT_VERSION);
        buf.extend_from_slice(b"KND");
        buf.extend(encode_bytes(self.kind.as_bytes()));
        buf.extend_from_slice(b"SND");
        match &self.sender {
            None => buf.extend(encode_uvarint(0)),
            Some(s) => {
                buf.extend(encode_uvarint(1));
                buf.extend(raw_pubkey_bytes(s));
            }
        }
        buf.extend_from_slice(b"RCP");
        buf.extend(raw_pubkey_bytes(&self.recipient));
        buf.extend_from_slice(b"AST");
        buf.extend(raw_asset_bytes(&self.asset));
        buf.extend_from_slice(b"AMT");
        buf.extend(encode_uvarint(self.amount));
        sha256_hex(&buf)
    }
}

/// Successful operation: a receipt plus the next state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BalanceAccepted {
    pub receipt: BalanceReceipt,
    pub state: BalanceState,
}

fn valid_amount(amount: u128) -> bool {
    (1..=MAX_BALANCE).contains(&amount)
}

/// Pure arithmetic core of [`transfer`].
///
/// Given the sender/recipient pre-balances for one `(pubkey, asset)` pair and a
/// **validated** `amount` (`1 <= amount <= MAX_BALANCE`, enforced by the
/// caller), compute the post-balances or the typed rejection. Reject order is
/// insufficient-before-overflow, matching the Python authority. Total and
/// panic-free for ANY `u128` inputs: the debit is guarded by the insufficient
/// check (no underflow) and the credit is checked. Machine-proved by the Kani
/// harnesses in `kani_contracts` — this is the consensus-critical arithmetic of
/// the running `transfer`, isolated from the heap-heavy string/map layer so the
/// proof runs on the actual code rather than a port.
fn settle_transfer_amounts(
    sender_balance: u128,
    recipient_balance: u128,
    amount: u128,
) -> Result<(u128, u128), BalanceRejectedReason> {
    match settle_transfer_balances_v1(sender_balance, recipient_balance, amount) {
        Ok(post) => Ok((post.source_atoms(), post.destination_atoms())),
        Err(AssetTransferArithmeticRejectV1::InsufficientBalance) => {
            Err(BalanceRejectedReason::InsufficientBalance)
        }
        Err(AssetTransferArithmeticRejectV1::BalanceOverflow) => {
            Err(BalanceRejectedReason::BalanceOverflow)
        }
    }
}

/// Pure arithmetic core of [`credit`]: the recipient's post-balance for a
/// **validated** `amount`, or `BalanceOverflow`. Credit MINTS by design (supply
/// grows by `amount`); only [`transfer`] conserves. Kani-proved.
fn settle_credit_amount(
    recipient_balance: u128,
    amount: u128,
) -> Result<u128, BalanceRejectedReason> {
    recipient_balance
        .checked_add(amount)
        .filter(|v| *v <= MAX_BALANCE)
        .ok_or(BalanceRejectedReason::BalanceOverflow)
}

/// Credit `amount` of `asset` to `recipient`.
pub fn credit(
    state: &BalanceState,
    recipient: &str,
    asset: &str,
    amount: u128,
) -> Result<BalanceAccepted, BalanceRejectedReason> {
    let rcp = canonical_pubkey(recipient).ok_or(BalanceRejectedReason::InvalidRecipient)?;
    let ast = canonical_asset(asset).ok_or(BalanceRejectedReason::InvalidAsset)?;
    if !valid_amount(amount) {
        return Err(BalanceRejectedReason::InvalidAmount);
    }
    let new_recipient = settle_credit_amount(state.balance_of(&rcp, &ast), amount)?;
    Ok(BalanceAccepted {
        receipt: BalanceReceipt {
            kind: KIND_CREDIT,
            sender: None,
            recipient: rcp.clone(),
            asset: ast.clone(),
            amount,
        },
        state: state.set(&rcp, &ast, new_recipient),
    })
}

/// Move `amount` of `asset` from `sender` to `recipient` (supply-conserving).
pub fn transfer(
    state: &BalanceState,
    sender: &str,
    recipient: &str,
    asset: &str,
    amount: u128,
) -> Result<BalanceAccepted, BalanceRejectedReason> {
    let snd = canonical_pubkey(sender).ok_or(BalanceRejectedReason::InvalidSender)?;
    let rcp = canonical_pubkey(recipient).ok_or(BalanceRejectedReason::InvalidRecipient)?;
    let ast = canonical_asset(asset).ok_or(BalanceRejectedReason::InvalidAsset)?;
    if !valid_amount(amount) {
        return Err(BalanceRejectedReason::InvalidAmount);
    }
    if snd == rcp {
        return Err(BalanceRejectedReason::SelfTransfer);
    }
    let sender_balance = state.balance_of(&snd, &ast);
    let recipient_balance = state.balance_of(&rcp, &ast);
    let (new_sender, new_recipient) =
        settle_transfer_amounts(sender_balance, recipient_balance, amount)?;

    // Distinct keys (snd != rcp): debit then credit is order-independent.
    let next = state
        .set(&snd, &ast, new_sender)
        .set(&rcp, &ast, new_recipient);
    Ok(BalanceAccepted {
        receipt: BalanceReceipt {
            kind: KIND_TRANSFER,
            sender: Some(snd.clone()),
            recipient: rcp.clone(),
            asset: ast.clone(),
            amount,
        },
        state: next,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn pk(tag: u8) -> String {
        format!("0x{}", hex::encode([tag; PUBKEY_NBYTES]))
    }
    fn asset(tag: u8) -> String {
        format!("0x{}", hex::encode([tag; ASSET_NBYTES]))
    }

    #[test]
    fn credit_then_transfer_conserves_supply() {
        let (a, b, x) = (pk(0x11), pk(0x22), asset(0xAA));
        let st = credit(&BalanceState::default(), &a, &x, 100).unwrap().state;
        let st = transfer(&st, &a, &b, &x, 30).unwrap().state;
        assert_eq!(st.balance_of(&a, &x), 70);
        assert_eq!(st.balance_of(&b, &x), 30);
        assert_eq!(st.balance_of(&a, &x) + st.balance_of(&b, &x), 100);
    }

    #[test]
    fn raw_and_upper_hex_match_runtime_canonicalization() {
        let a = pk(0x11);
        let x = asset(0xAA);
        let raw_a = a.strip_prefix("0x").unwrap();
        let upper_x = format!("0X{}", x.strip_prefix("0x").unwrap().to_ascii_uppercase());
        let spaced_a = format!("  {}  ", raw_a.to_ascii_uppercase());
        let amount = 100u128;
        let prefixed = credit(&BalanceState::default(), &a, &x, amount).unwrap();
        let raw = credit(&BalanceState::default(), raw_a, &upper_x, amount).unwrap();
        let spaced = credit(&BalanceState::default(), &spaced_a, &x, amount).unwrap();
        assert_eq!(raw.receipt.recipient, a);
        assert_eq!(raw.receipt.asset, x);
        assert_eq!(spaced.receipt.recipient, a);
        assert_eq!(prefixed.receipt.receipt_hash(), raw.receipt.receipt_hash());
        assert_eq!(
            prefixed.receipt.receipt_hash(),
            spaced.receipt.receipt_hash()
        );
        assert_eq!(prefixed.state.state_root(), raw.state.state_root());
        assert_eq!(prefixed.state.state_root(), spaced.state.state_root());
    }

    #[test]
    fn python_info_separator_controls_are_trimmed() {
        let a = pk(0x11);
        let x = asset(0xAA);
        let wrapped_a = format!("\u{001c}{a}\u{001f}");
        let wrapped_x = format!("\u{001d}{}\u{001e}", x.strip_prefix("0x").unwrap());
        let acc = credit(&BalanceState::default(), &wrapped_a, &wrapped_x, 100).unwrap();
        assert_eq!(acc.receipt.recipient, a);
        assert_eq!(acc.receipt.asset, x);
    }

    #[test]
    fn rejections_have_stable_codes() {
        let (a, b, x) = (pk(0x11), pk(0x22), asset(0xAA));
        let st = credit(&BalanceState::default(), &a, &x, 100).unwrap().state;
        assert_eq!(
            transfer(&st, &a, &a, &x, 10),
            Err(BalanceRejectedReason::SelfTransfer)
        );
        assert_eq!(
            transfer(&st, &a, &b, &x, 1000),
            Err(BalanceRejectedReason::InsufficientBalance)
        );
        assert_eq!(
            transfer(&st, "0x11", &b, &x, 10),
            Err(BalanceRejectedReason::InvalidSender)
        );
        assert_eq!(
            transfer(&st, &a, &b, "0xbb", 10),
            Err(BalanceRejectedReason::InvalidAsset)
        );
        assert_eq!(
            transfer(&st, &a, &b, &x, 0),
            Err(BalanceRejectedReason::InvalidAmount)
        );
    }

    #[test]
    fn full_balance_transfer_is_sparse() {
        let (a, b, x) = (pk(0x11), pk(0x22), asset(0xAA));
        let st = credit(&BalanceState::default(), &a, &x, 50).unwrap().state;
        let st = transfer(&st, &a, &b, &x, 50).unwrap().state;
        assert_eq!(st.balance_of(&a, &x), 0);
        assert!(!st.balances.contains_key(&(a, x)));
    }

    #[test]
    fn from_entries_canonicalizes_and_rejects_duplicate_decoded_keys() {
        let a = pk(0x11);
        let x = asset(0xAA);
        let raw_a = a.strip_prefix("0x").unwrap().to_string();
        let upper_x = format!("0X{}", x.strip_prefix("0x").unwrap().to_ascii_uppercase());
        let state = BalanceState::from_entries([(raw_a.clone(), upper_x.clone(), 7)]).unwrap();
        assert_eq!(state.balance_of(&a, &x), 7);
        assert_eq!(
            BalanceState::from_entries([(a, x, 1), (raw_a, upper_x, 2)]),
            Err("duplicate_balance_key")
        );
    }

    #[test]
    fn from_entries_rejects_invalid_stored_amount() {
        let a = pk(0x11);
        let x = asset(0xAA);
        assert_eq!(
            BalanceState::from_entries([(a.clone(), x.clone(), 0)]),
            Err("invalid_amount")
        );
        assert_eq!(
            BalanceState::from_entries([(a, x, MAX_BALANCE + 1)]),
            Err("invalid_amount")
        );
    }

    proptest! {
        // INVARIANT: transfers conserve per-asset supply; credit increases it by
        // exactly `amount`; balances never exceed MAX or go negative (u128).
        #[test]
        fn supply_conservation_and_bounds(
            ops in proptest::collection::vec(
                (0u8..2, 0u8..3, 0u8..3, 1u128..=50), 0..60
            )
        ) {
            let accts = [pk(0xA0), pk(0xB0), pk(0xC0)];
            let x = asset(0xAA);
            let mut state = BalanceState::default();
            let mut credited: u128 = 0;
            for (op, i, j, amount) in ops {
                if op == 0 {
                    if let Ok(acc) = credit(&state, &accts[i as usize], &x, amount) {
                        state = acc.state;
                        credited += amount;
                    }
                } else if let Ok(acc) =
                    transfer(&state, &accts[i as usize], &accts[j as usize], &x, amount)
                {
                    state = acc.state;
                }
            }
            let supply: u128 = accts.iter().map(|p| state.balance_of(p, &x)).sum();
            prop_assert_eq!(supply, credited);
            for p in &accts {
                prop_assert!(state.balance_of(p, &x) <= MAX_BALANCE);
            }
        }

        // INVARIANT: an asset-X transfer/credit never changes an asset-Y balance.
        #[test]
        fn per_asset_isolation(amount in 1u128..=1000) {
            let (a, b, x, y) = (pk(0x11), pk(0x22), asset(0xAA), asset(0xBB));
            let mut state = credit(&BalanceState::default(), &a, &x, MAX_BALANCE.min(2000)).unwrap().state;
            state = credit(&state, &a, &y, 1234).unwrap().state;
            let before_y_a = state.balance_of(&a, &y);
            let before_y_b = state.balance_of(&b, &y);
            if let Ok(acc) = transfer(&state, &a, &b, &x, amount) {
                prop_assert_eq!(acc.state.balance_of(&a, &y), before_y_a);
                prop_assert_eq!(acc.state.balance_of(&b, &y), before_y_b);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// CBC_CORE_V0 — Kani contracts on the ACTUAL runtime arithmetic core.
//
// `settle_transfer_amounts` / `settle_credit_amount` are the pure integer cores
// the running `transfer` / `credit` call after canonicalizing keys and reading
// balances. They carry the consensus-critical arithmetic (debit/credit,
// insufficient, overflow) where value-creation / underflow / overflow bugs
// live. Kani discharges them fast because they are heap-free (no String /
// BTreeMap / sha2): TOTALITY holds over ALL u128 inputs, while the conservation
// / mint / reject-precedence obligations hold under the caller-enforced domain
// (balances in `[0, MAX_BALANCE]` — 0 models an absent sparse key — and amounts
// in `[1, MAX_BALANCE]`, validated by the wrapper before the core is reached;
// see `arb_balance` / `arb_amount`). The string-
// canonicalization and map-plumbing layer of `transfer`/`credit` (which CBMC
// cannot model in bounded time) stays covered by the proptest invariants above
// and the Python<->Rust differential. Run: `cargo kani -p zenodex-runtime-core`.
// ---------------------------------------------------------------------------
#[cfg(kani)]
mod kani_contracts {
    use super::*;

    /// A symbolic in-domain balance: `0 ..= MAX_BALANCE` (0 models an absent
    /// sparse key — `balance_of` returns 0 for it).
    fn arb_balance() -> u128 {
        let v: u128 = kani::any();
        kani::assume(v <= MAX_BALANCE);
        v
    }
    /// A symbolic validated amount: `1 ..= MAX_BALANCE` (the caller validates).
    fn arb_amount() -> u128 {
        let v: u128 = kani::any();
        kani::assume(v >= 1 && v <= MAX_BALANCE);
        v
    }

    /// TOTALITY (absence of runtime errors). For ANY `u128` pre-balances and
    /// amount, the transfer core never panics / overflows / underflows. The
    /// debit `sender_balance - amount` is reached only after the insufficient
    /// guard, and the credit is `checked_add`.
    #[kani::proof]
    fn settle_transfer_is_total() {
        let _ = settle_transfer_amounts(kani::any(), kani::any(), kani::any());
    }

    /// CONSERVATION + EXACT MOVE. On accept, the sender is debited and the
    /// recipient credited by exactly `amount`, and the two-key total is
    /// preserved: `new_sender + new_recipient == sender_balance + recipient_balance`.
    /// `sb, rb <= MAX_BALANCE = 2^112-1` => `sb + rb <= 2^113 < 2^128`, so the
    /// conservation sum cannot overflow.
    #[kani::proof]
    fn settle_transfer_conserves_and_moves_exact() {
        let sb = arb_balance();
        let rb = arb_balance();
        let amt = arb_amount();
        if let Ok((new_sender, new_recipient)) = settle_transfer_amounts(sb, rb, amt) {
            assert_eq!(new_sender, sb - amt); // exact debit
            assert_eq!(new_recipient, rb + amt); // exact credit
            assert_eq!(new_sender + new_recipient, sb + rb); // conservation
            assert!(new_recipient <= MAX_BALANCE); // in-domain
        }
    }

    /// REJECT PRECEDENCE + REJECT => NO POST-STATE. The core emits exactly
    /// `InsufficientBalance` (when `sb < amt`, checked first) or `BalanceOverflow`
    /// (when sufficient but `rb + amt > MAX`), never any other code; on reject no
    /// `(new_sender, new_recipient)` is produced. Mirrors the Python order
    /// (`balance_kernel.py:385-389`): insufficient before overflow.
    #[kani::proof]
    fn settle_transfer_reject_precedence() {
        let sb = arb_balance();
        let rb = arb_balance();
        let amt = arb_amount();
        match settle_transfer_amounts(sb, rb, amt) {
            Ok((new_sender, _)) => {
                assert!(sb >= amt);
                assert_eq!(new_sender, sb - amt);
            }
            Err(BalanceRejectedReason::InsufficientBalance) => assert!(sb < amt),
            Err(BalanceRejectedReason::BalanceOverflow) => {
                assert!(sb >= amt); // insufficient is checked strictly first
                assert!(rb.checked_add(amt).map_or(true, |v| v > MAX_BALANCE));
            }
            // The core can only ever emit the two codes above; any other variant
            // is dead (Kani proves this branch unreachable).
            Err(_) => unreachable!("transfer core emits only insufficient/overflow"),
        }
    }

    /// CREDIT TOTALITY: the credit core never panics / overflows for ANY input.
    #[kani::proof]
    fn settle_credit_is_total() {
        let _ = settle_credit_amount(kani::any(), kani::any());
    }

    /// CREDIT MINTS BY DESIGN + ACCEPT-COMPLETENESS. Exhaustive `match` over the
    /// core's result proves it accepts IFF `rb + amount <= MAX_BALANCE`: on
    /// accept the recipient post-balance is exactly `rb + amount` (supply grows —
    /// NOT conserved); the ONLY reject is `BalanceOverflow`, and it fires exactly
    /// when `rb + amount > MAX_BALANCE`. (Both directions: the Ok arm forces
    /// in-domain, the Overflow arm forces out-of-domain, and any other variant is
    /// unreachable — so `rb + amount <= MAX` cannot reject.)
    #[kani::proof]
    fn settle_credit_mints_or_overflows() {
        let rb = arb_balance();
        let amt = arb_amount();
        match settle_credit_amount(rb, amt) {
            Ok(new_recipient) => {
                assert!(rb + amt <= MAX_BALANCE); // accept => in-domain
                assert_eq!(new_recipient, rb + amt); // exact mint
            }
            Err(BalanceRejectedReason::BalanceOverflow) => {
                assert!(rb + amt > MAX_BALANCE); // overflow => out-of-domain
            }
            // The credit core can only ever emit overflow; any other variant is
            // dead (Kani proves this branch unreachable).
            Err(_) => unreachable!("credit core emits only overflow"),
        }
    }

    /// NON-VACUITY (credit): both accept and overflow are reachable (Kani fails
    /// an unsatisfiable cover), so the credit contract is not vacuous.
    #[kani::proof]
    fn credit_covers_are_reachable() {
        let rb = arb_balance();
        let amt = arb_amount();
        let res = settle_credit_amount(rb, amt);
        kani::cover!(res.is_ok());
        kani::cover!(res == Err(BalanceRejectedReason::BalanceOverflow));
    }

    /// NON-VACUITY. Accept, insufficient, and overflow are each reachable (Kani
    /// fails an unsatisfiable cover), so the contracts above are not vacuous.
    #[kani::proof]
    fn covers_are_reachable() {
        let sb = arb_balance();
        let rb = arb_balance();
        let amt = arb_amount();
        let res = settle_transfer_amounts(sb, rb, amt);
        kani::cover!(res.is_ok());
        kani::cover!(res == Err(BalanceRejectedReason::InsufficientBalance));
        kani::cover!(res == Err(BalanceRejectedReason::BalanceOverflow));
    }
}
