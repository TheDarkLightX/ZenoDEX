--  SPARK 2014 buyback burn-rail conservation kernel (ADVISORY sidecar).
--
--  High-assurance specification of the burn (do_burn = 1) conservation that the
--  Python reference (src/core/burn_receipts.py rails) and the Rust shadow
--  (zenodex-runtime-core::burn_receipts) implement:
--
--      supply_after            = supply_before - burn_amount   (supply leaves)
--      batch_after             = batch_before + burn_amount     (accumulator grows)
--      supply_before - supply_after = batch_after - batch_before (what leaves
--                                       total supply enters the public burn
--                                       accumulator, one-for-one)
--      burn cannot cross zero  (burn_amount <= supply_before => supply_after >= 0)
--      burn is budget-capped   (burn_amount <= burn_budget)
--
--  The do_burn = 0 (no-op) case is trivial (supply/accumulator unchanged) and is
--  not modelled here. This kernel is *advisory*: not compiled or proved in the
--  CI container (no gnatprove available here). See README.md for toolchain
--  instructions and proof status.

package Burn_Rails with
   SPARK_Mode
is

   --  Per-receipt field bounds, matching the Python rails (burn/supply/batch
   --  fields are validated to [0, 0x7FFF]; the post-burn accumulator may reach
   --  0xFFFF).
   Max_Amount      : constant := 16#7FFF#;
   Max_Batch_After : constant := 16#FFFF#;

   subtype Amount is Integer range 0 .. Max_Amount;
   subtype Batch is Integer range 0 .. Max_Batch_After;

   --  Burn Burn_Amount units of supply into the public burn accumulator.
   procedure Burn
     (Supply_Before : in     Amount;
      Burn_Amount   : in     Amount;
      Batch_Before  : in     Amount;
      Burn_Budget   : in     Amount;
      Supply_After  :    out Amount;
      Batch_After   :    out Batch)
   with
     Pre  => Burn_Amount > 0
       and then Burn_Amount <= Supply_Before
       and then Burn_Amount <= Burn_Budget
       and then Batch_Before + Burn_Amount <= Max_Batch_After,
     Post => Supply_After = Supply_Before - Burn_Amount
       and then Batch_After = Batch_Before + Burn_Amount
       and then Supply_After >= 0
       and then (Supply_Before - Supply_After) = (Batch_After - Batch_Before);

end Burn_Rails;
