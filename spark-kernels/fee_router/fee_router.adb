package body Fee_Router with
   SPARK_Mode
is

   procedure Route
     (Amount  : in     Money;
      S       : in     Split;
      Buyburn :    out Money;
      Stakers :    out Money;
      Reserve :    out Money;
      Hosts   :    out Money;
      Dust    :    out Money)
   is
      --  Intermediate kept as Long_Long_Integer (not Money) so the sum does not
      --  trip a spurious range check before the dust subtraction.
      Distributed : Long_Long_Integer;
   begin
      Buyburn := (Amount * Long_Long_Integer (S.Buyburn)) / Bps_Denom;
      Stakers := (Amount * Long_Long_Integer (S.Stakers)) / Bps_Denom;
      Reserve := (Amount * Long_Long_Integer (S.Reserve)) / Bps_Denom;
      Hosts   := (Amount * Long_Long_Integer (S.Hosts)) / Bps_Denom;

      Distributed := Buyburn + Stakers + Reserve + Hosts;

      --  Floor subadditivity: with the shares summing to Bps_Denom, the sum of
      --  the per-bucket floors never exceeds Amount, so Dust is non-negative.
      Dust := Amount - Distributed;
   end Route;

end Fee_Router;
