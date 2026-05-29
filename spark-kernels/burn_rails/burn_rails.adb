--  Implementation of the advisory burn-rail conservation kernel.
--
--  Both assignments are exact integer operations; the precondition guarantees
--  Supply_After stays in [0, Supply_Before] and Batch_After in
--  [Batch_Before, Max_Batch_After], so the postcondition (conservation,
--  non-negativity, one-for-one transfer) discharges directly.

package body Burn_Rails with
   SPARK_Mode
is

   procedure Burn
     (Supply_Before : in     Amount;
      Burn_Amount   : in     Amount;
      Batch_Before  : in     Amount;
      Burn_Budget   : in     Amount;
      Supply_After  :    out Amount;
      Batch_After   :    out Batch)
   is
      pragma Unreferenced (Burn_Budget);
   begin
      Supply_After := Supply_Before - Burn_Amount;
      Batch_After  := Batch_Before + Burn_Amount;
   end Burn;

end Burn_Rails;
