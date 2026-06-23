--  SPARK 2014 fee-split conservation kernel (ADVISORY sidecar).
--
--  High-assurance specification of the single-split conservation property that
--  the Python reference (src/core/fee_router.py) and the Rust shadow
--  (zenodex-runtime-core) implement:
--
--      buyburn + stakers + reserve + hosts + dust = amount
--      all outputs >= 0
--
--  This is the dust_in = 0 case (one split, no carry), matching the task's
--  literal conservation statement. It is *advisory*: not compiled or proved in
--  the CI container (no gnatprove available here). See README.md for the
--  toolchain instructions and proof status.

package Fee_Router with
   SPARK_Mode
is

   Bps_Denom : constant := 10_000;

   subtype Bps is Integer range 0 .. Bps_Denom;

   --  Bounded so that Amount * Bps cannot overflow Long_Long_Integer
   --  (2**40 * 10_000 < 2**54 < 2**63).
   Max_Amount : constant := 2 ** 40;
   subtype Money is Long_Long_Integer range 0 .. Max_Amount;

   type Split is record
      Buyburn : Bps;
      Stakers : Bps;
      Reserve : Bps;
      Hosts   : Bps;
   end record;

   --  The four shares must partition the basis-point denominator exactly.
   function Sums_To_Denom (S : Split) return Boolean is
     (Integer (S.Buyburn) + Integer (S.Stakers) +
      Integer (S.Reserve) + Integer (S.Hosts) = Bps_Denom);

   --  Route Amount across the four buckets with floor rounding; the remainder
   --  becomes Dust. Conservation and non-negativity are the postcondition.
   procedure Route
     (Amount  : in     Money;
      S       : in     Split;
      Buyburn :    out Money;
      Stakers :    out Money;
      Reserve :    out Money;
      Hosts   :    out Money;
      Dust    :    out Money)
   with
     Pre  => Sums_To_Denom (S),
     Post => Buyburn + Stakers + Reserve + Hosts + Dust = Amount
       and then Buyburn >= 0 and then Stakers >= 0
       and then Reserve >= 0 and then Hosts >= 0 and then Dust >= 0;

end Fee_Router;
