use zenodex_zrpf_risc0_spot_settlement_v7_input_builder::{
    parse_spot_settlement_v7_input_builder_args_v1, run_spot_settlement_v7_input_builder_v1,
};

fn main() {
    let result = parse_spot_settlement_v7_input_builder_args_v1(std::env::args_os().skip(1))
        .and_then(|paths| run_spot_settlement_v7_input_builder_v1(&paths));
    if let Err(error) = result {
        eprintln!("spot settlement V7 input builder rejected: {error}");
        std::process::exit(1);
    }
}
