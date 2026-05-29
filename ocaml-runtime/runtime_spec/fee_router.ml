(** Fee-router split conservation — OCaml spec oracle.

    Mirrors the per-call arithmetic of [route_fee] in [src/core/fee_router.py]
    with an empty accumulator (dust_in = 0): each bucket is a floor split of the
    amount, and the dust is the conservation remainder. This is the same kernel
    the SPARK [Route] procedure models, expressed as a pure OCaml function. *)

let bps_denom = 10_000

(** [route ~amount ~buyburn_bps ~stakers_bps ~reserve_bps ~hosts_bps] returns
    [(buyburn, stakers, reserve, hosts, dust)] where each bucket is
    [floor (amount * bps / 10_000)] and [dust = amount - sum]. Conservation
    ([buyburn + stakers + reserve + hosts + dust = amount]) holds by construction
    whenever the four bps are non-negative and sum to [bps_denom] or less. *)
let route ~amount ~buyburn_bps ~stakers_bps ~reserve_bps ~hosts_bps =
  let split bps = amount * bps / bps_denom in
  let buyburn = split buyburn_bps in
  let stakers = split stakers_bps in
  let reserve = split reserve_bps in
  let hosts = split hosts_bps in
  let dust = amount - (buyburn + stakers + reserve + hosts) in
  (buyburn, stakers, reserve, hosts, dust)
