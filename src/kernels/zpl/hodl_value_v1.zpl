object hodl_value_v1;
name HODLValue;
cli_help "Load a HODLValue FIRE interface object";
version v1;
family value_source;
settlement zUSD;
summary "HODLValue_T";
ir_hash sha256:7f0ea8efd30f6e647ad4f9ec3fcc70d712e30ad7772df4fc9e72be7433aeb64b;
term hodl_lower "Certified lower HODL value bound" Amount[zUSD] 0 1000;
term hodl_upper "Certified upper HODL value bound" Amount[zUSD] 0 1000;
contract hodl_contract Amount[zUSD] term:hodl_lower term:hodl_upper;
source hodl_final contract:hodl_contract;
witness HODLValuePacket "1 epoch" contract:hodl_contract;
output hodl_final "Certified HODL value interval" Amount[zUSD] = source_bound(hodl_final);
expression = source_bound(hodl_final);
end
