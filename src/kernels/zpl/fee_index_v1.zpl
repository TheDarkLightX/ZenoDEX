object fee_index_v1;
name FeeIndex;
cli_help "Load a FeeIndex FIRE interface object";
version v1;
family index_source;
settlement zUSD;
summary "FeeIndex_T";
ir_hash sha256:4d9bf4a7741cc92df0185f607e6f4364fb63f9e98c55df433b579756870fb871;
term fee_final "Certified fee index final value" Index 0 1000;
contract fee_contract Index term:fee_final term:fee_final;
witness FeeIndexPacket "1 epoch" contract:fee_contract;
output fee_final "Certified fee index final value" Index = exact_param(fee_final);
expression = exact_param(fee_final);
end
