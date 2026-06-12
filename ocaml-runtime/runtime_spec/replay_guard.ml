(** Replay-guard nonce policy — OCaml spec oracle.

    Mirrors the strict-sequential per-sender decision of [admit] in
    [src/core/replay_guard.py], over the (last_accepted, nonce) pair. Sender
    canonicalization is out of scope for this oracle (the differential drives a
    single fixed sender); only the nonce policy is modelled. *)

let u32_max = 0xFFFFFFFF

(** [admit ~last ~nonce] returns the stable decision code:
    - ["invalid_nonce"] when [nonce] is outside [1, 2^32 - 1];
    - ["duplicate_nonce"] when [nonce = last];
    - ["stale_nonce"] when [nonce < last];
    - ["nonce_gap"] when [nonce > last + 1];
    - ["accept"] when [nonce = last + 1].

    Evaluation order matches the authority: the range check precedes the
    duplicate / stale / gap checks. *)
let admit ~last ~nonce =
  if nonce < 1 || nonce > u32_max then "invalid_nonce"
  else if nonce = last then "duplicate_nonce"
  else if nonce < last then "stale_nonce"
  else if nonce > last + 1 then "nonce_gap"
  else "accept"
