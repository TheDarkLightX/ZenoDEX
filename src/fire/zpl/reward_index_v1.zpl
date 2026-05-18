object reward_index_v1;
name RewardIndex;
cli_help "Load a RewardIndex FIRE interface object";
version v1;
family index_source;
settlement zUSD;
summary "RewardIndex_T";
ir_hash sha256:c52f76d084635dfb2fcbe9d01081f37a0deefbcf8a01bcf184e19a5fdf7c1d59;
term reward_final "Certified reward index final value" Index 0 1000;
contract reward_contract Index term:reward_final term:reward_final;
witness RewardIndexPacket "1 epoch" contract:reward_contract;
output reward_final "Certified reward index final value" Index = exact_param(reward_final);
expression = exact_param(reward_final);
end
