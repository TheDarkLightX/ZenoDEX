object fee_note_v1;
name FeeNote;
cli_help "Build a FeeNote FIRE object";
version v1;
family capped_index_note;
settlement zUSD;
summary "N * min(FeeIndex_T, Cap)";
ir_hash sha256:1d2740320070d63cc487bbc9333d10ca0d6c43e102ac1940bc4daa517a0492ba;
term n_notional "Notional amount" Amount[zUSD] 0 1000;
term cap_index "Payoff cap index" Index 0 1000;
term source_upper "Certified source upper bound" Index 0 1000;
contract fee_contract Index const:0 term:source_upper;
import fee_final fee_index_v1 fee_final contract:fee_contract;
witness FeeIndexPacket "1 epoch" contract:fee_contract;
output settlement_payoff "Certified settlement payoff bound" Amount[zUSD] = mul(exact_param(n_notional), cap(source_bound(fee_final), exact_param(cap_index)));
expression = mul(exact_param(n_notional), cap(source_bound(fee_final), exact_param(cap_index)));
end
