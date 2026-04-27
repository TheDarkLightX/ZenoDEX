object lp_value_v1;
name LPValue;
cli_help "Load an LPValue FIRE interface object";
version v1;
family value_source;
settlement zUSD;
summary "LPValue_T";
ir_hash sha256:5f03d9eec0db8a749d06f6b992c18c5168a9cb4f2195d098889befb91dc35ef4;
term lpv_lower "Certified lower LP value bound" Amount[zUSD] 0 1000;
term lpv_upper "Certified upper LP value bound" Amount[zUSD] 0 1000;
contract lpv_contract Amount[zUSD] term:lpv_lower term:lpv_upper;
source lpv_final contract:lpv_contract;
witness LPValuePacket "1 epoch" contract:lpv_contract;
output lpv_final "Certified LP value interval" Amount[zUSD] = source_bound(lpv_final);
expression = source_bound(lpv_final);
end
