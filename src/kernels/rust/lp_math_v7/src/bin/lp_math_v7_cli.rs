use lp_math_v7::{
    burn_liquidity, mint_liquidity, mint_liquidity_initial, mint_liquidity_initial_witness,
    optimal_liquidity, LpError, MIN_LP_LOCK,
};
use std::env;
use std::process;

fn parse_u128(raw: &str) -> Result<u128, String> {
    raw.parse::<u128>().map_err(|_| "invalid_u128".to_string())
}

fn arg(args: &[String], idx: usize) -> Result<u128, String> {
    args.get(idx)
        .ok_or_else(|| format!("missing_arg:{idx}"))
        .and_then(|raw| parse_u128(raw))
}

fn emit_error(err: LpError) {
    println!("{{\"ok\":false,\"error\":\"{}\"}}", err.code());
}

fn emit_parse_error(err: &str) {
    println!("{{\"ok\":false,\"error\":\"{}\"}}", err);
}

fn require_len(args: &[String], expected: usize) -> Result<(), String> {
    if args.len() == expected {
        Ok(())
    } else {
        Err("wrong_arity".to_string())
    }
}

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    if args.is_empty() {
        emit_parse_error("missing_operation");
        process::exit(2);
    }

    let result = match args[0].as_str() {
        "optimal" => run_optimal(&args),
        "mint_initial" => run_mint_initial(&args),
        "mint_initial_witness" => run_mint_initial_witness(&args),
        "mint" => run_mint(&args),
        "burn" => run_burn(&args),
        _ => Err("unknown_operation".to_string()),
    };

    if let Err(err) = result {
        emit_parse_error(&err);
        process::exit(2);
    }
}

fn run_optimal(args: &[String]) -> Result<(), String> {
    require_len(args, 5)?;
    match optimal_liquidity(arg(args, 1)?, arg(args, 2)?, arg(args, 3)?, arg(args, 4)?) {
        Ok(res) => println!(
            "{{\"ok\":true,\"result\":{{\"amount0_used\":{},\"amount1_used\":{},\"amount0_refund\":{},\"amount1_refund\":{}}}}}",
            res.amount0_used, res.amount1_used, res.amount0_refund, res.amount1_refund
        ),
        Err(err) => emit_error(err),
    }
    Ok(())
}

fn run_mint_initial(args: &[String]) -> Result<(), String> {
    require_len(args, 3)?;
    match mint_liquidity_initial(arg(args, 1)?, arg(args, 2)?, MIN_LP_LOCK) {
        Ok((minted, total_supply)) => println!(
            "{{\"ok\":true,\"result\":{{\"liquidity_minted\":{},\"total_supply\":{}}}}}",
            minted, total_supply
        ),
        Err(err) => emit_error(err),
    }
    Ok(())
}

fn run_mint_initial_witness(args: &[String]) -> Result<(), String> {
    require_len(args, 4)?;
    match mint_liquidity_initial_witness(arg(args, 1)?, arg(args, 2)?, arg(args, 3)?, MIN_LP_LOCK) {
        Ok((minted, total_supply)) => println!(
            "{{\"ok\":true,\"result\":{{\"liquidity_minted\":{},\"total_supply\":{}}}}}",
            minted, total_supply
        ),
        Err(err) => emit_error(err),
    }
    Ok(())
}

fn run_mint(args: &[String]) -> Result<(), String> {
    require_len(args, 7)?;
    match mint_liquidity(
        arg(args, 1)?,
        arg(args, 2)?,
        arg(args, 3)?,
        arg(args, 4)?,
        arg(args, 5)?,
        arg(args, 6)?,
    ) {
        Ok(res) => println!(
            "{{\"ok\":true,\"result\":{{\"liquidity_minted\":{},\"amount0_used\":{},\"amount1_used\":{},\"amount0_refund\":{},\"amount1_refund\":{},\"new_reserve0\":{},\"new_reserve1\":{},\"new_total_supply\":{}}}}}",
            res.liquidity_minted,
            res.amount0_used,
            res.amount1_used,
            res.amount0_refund,
            res.amount1_refund,
            res.new_reserve0,
            res.new_reserve1,
            res.new_total_supply
        ),
        Err(err) => emit_error(err),
    }
    Ok(())
}

fn run_burn(args: &[String]) -> Result<(), String> {
    require_len(args, 5)?;
    match burn_liquidity(arg(args, 1)?, arg(args, 2)?, arg(args, 3)?, arg(args, 4)?) {
        Ok(res) => println!(
            "{{\"ok\":true,\"result\":{{\"amount0_out\":{},\"amount1_out\":{}}}}}",
            res.amount0_out, res.amount1_out
        ),
        Err(err) => emit_error(err),
    }
    Ok(())
}
