object burn_boost_call_v1;
name BurnBoostCall;
cli_help "Build a BurnBoostCall FIRE object";
version v1;
family capped_index_call;
settlement zUSD;
summary "N * min(max(BurnIndex_T - K, 0), Cap)";
ir_hash sha256:b26b68dbadb3313ef59399eeb2f7f180ea9775bffd3e797c27186a0d5daddc61;
term n_notional "Notional amount" Amount[zUSD] 0 1000;
term strike_index "Strike index" Index 0 1000;
term cap_index "Payoff cap index" Index 0 1000;
term source_upper "Certified source upper bound" Index 0 1000;
contract burn_contract Index const:0 term:source_upper;
import burn_final burn_index_v1 burn_final contract:burn_contract;
witness "BurnCertificate[TDEX]" "1 epoch" contract:burn_contract;
output settlement_payoff "Certified settlement payoff bound" Amount[zUSD] = mul(exact_param(n_notional), cap(positive_part(sub(source_bound(burn_final), exact_param(strike_index))), exact_param(cap_index)));
expression = mul(exact_param(n_notional), cap(positive_part(sub(source_bound(burn_final), exact_param(strike_index))), exact_param(cap_index)));
end
