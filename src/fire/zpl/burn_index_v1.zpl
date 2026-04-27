object burn_index_v1;
name BurnIndex;
cli_help "Load a BurnIndex FIRE interface object";
version v1;
family index_source;
settlement TDEX;
summary "BurnIndex_T";
ir_hash sha256:8f0d0fe8f9f6717e15dc4de0a5c0db322b5f2884efd6efbb9352964d46c57954;
term burn_final "Certified burn index final value" Index 0 1000;
contract burn_contract Index term:burn_final term:burn_final;
witness "BurnCertificate[TDEX]" "1 epoch" contract:burn_contract;
output burn_final "Certified burn index final value" Index = exact_param(burn_final);
expression = exact_param(burn_final);
end
