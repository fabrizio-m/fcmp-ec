#![allow(non_snake_case)]

use helioselene_contest::{
    test_gen_random_helios_point, test_gen_random_helios_scalar, test_gen_random_selene_point,
    test_gen_random_selene_scalar,
};

use helioselene::{
    group::ff::Field as FieldRef, HeliosPoint as HeliosPointRef, SelenePoint as SelenePointRef,
};
use helioselene_contest_src::{group::GroupEncoding, HeliosPoint, SelenePoint,ElemExt};

use std::time;

enum OpType {
    SelenePointAdd,
    HeliosPointAdd,
    HelioseleneMul,
    HelioseleneInvert,
    SelenePointDecompression,
    HeliosPointDecompression,
    HelioseleneAdd,
    HelioseleneSub,
    SelenePointMul,
    HeliosPointMul,
}

fn op_weight(op: OpType) -> f64 {
    match op {
        OpType::SelenePointAdd => 0.30,
        OpType::HeliosPointAdd => 0.15,
        OpType::HelioseleneMul => 0.15,
        OpType::HelioseleneInvert => 0.10,
        OpType::SelenePointDecompression => 0.075,
        OpType::HeliosPointDecompression => 0.075,
        OpType::HelioseleneAdd => 0.05,
        OpType::HelioseleneSub => 0.05,
        OpType::SelenePointMul => 0.025,
        OpType::HeliosPointMul => 0.025,
    }
}

macro_rules! run_bench {
    ($op_type:ident, $op:expr, $op_ref:expr, $n_iters:expr, $weighted_improvement_tally:expr, $weight_tally:expr) => {{
        // Start by measuring the reference impl
        let start = time::Instant::now();
        for _ in 0..$n_iters {
            let _ = core::hint::black_box($op_ref);
        }
        let ref_time_to_run = (time::Instant::now() - start).as_millis() as f64;

        // Then the custom implemented
        let start = time::Instant::now();
        for _ in 0..$n_iters {
            let _ = core::hint::black_box($op);
        }
        let time_to_run = (time::Instant::now() - start).as_millis() as f64;

        let improvement = (ref_time_to_run - time_to_run) / ref_time_to_run * 100f64;
        let weight = op_weight(OpType::$op_type);
        let weighted_improvement = weight * improvement;

        println!(
            "Reference took {}ms, your implementation took {}ms",
            ref_time_to_run, time_to_run
        );
        println!(
            "Improvement: {:.2}%, Weight: {}%, Weighted Improvement: {:.2}%",
            improvement,
            weight * 100f64,
            weighted_improvement
        );
        println!("\n");

        $weighted_improvement_tally += weighted_improvement;
        $weight_tally += weight;
    }};
}

fn main() {
    let mut weighted_improvement_tally = 0f64;
    let mut weight_tally = 0f64;

    // Do all the initialization
    let (A_S, A_S_ref) = test_gen_random_selene_point();
    let (B_S, B_S_ref) = test_gen_random_selene_point();

    let (A_H, A_H_ref) = test_gen_random_helios_point();
    let (B_H, B_H_ref) = test_gen_random_helios_point();

    let (a_h, a_h_ref) = test_gen_random_helios_scalar();
    let (b_h, b_h_ref) = test_gen_random_helios_scalar();

    let (a_s, a_s_ref) = test_gen_random_selene_scalar();

    let A_S_bytes = A_S.to_bytes();
    let A_S_ref_bytes = A_S_ref.to_bytes();

    let A_H_bytes = A_H.to_bytes();
    let A_H_ref_bytes = A_H_ref.to_bytes();

    // Selene Point Add
    println!("Selene Point Add...");
    run_bench!(
        SelenePointAdd,
        A_S + B_S,
        A_S_ref + B_S_ref,
        2_000_000,
        weighted_improvement_tally,
        weight_tally
    );

    // Helios Point Add
    println!("Helios Point Add...");
    run_bench!(
        HeliosPointAdd,
        A_H + B_H,
        A_H_ref + B_H_ref,
        2_000_000,
        weighted_improvement_tally,
        weight_tally
    );

    // helioselene Mul
    println!("helioselene Mul...");
    run_bench!(
        HelioseleneMul,
        a_h * b_h,
        a_h_ref * b_h_ref,
        50_000_000,
        weighted_improvement_tally,
        weight_tally
    );

    // helioselene invert
    println!("helioselene invert...");
    run_bench!(
        HelioseleneInvert,
        a_h.invert(),
        a_h_ref.invert(),
        200_000,
        weighted_improvement_tally,
        weight_tally
    );

    // Selene Point decompression
    println!("Selene Point Decompression...");
    run_bench!(
        SelenePointDecompression,
        SelenePoint::from_bytes(&A_S_bytes),
        SelenePointRef::from_bytes(&A_S_ref_bytes),
        100_000,
        weighted_improvement_tally,
        weight_tally
    );

    // Helios Point decompression
    println!("Helios Point Decompression...");
    run_bench!(
        HeliosPointDecompression,
        HeliosPoint::from_bytes(&A_H_bytes),
        HeliosPointRef::from_bytes(&A_H_ref_bytes),
        100_000,
        weighted_improvement_tally,
        weight_tally
    );

    // Helioselene Add
    println!("helioselene Add...");
    run_bench!(
        HelioseleneAdd,
        a_h + b_h,
        a_h_ref + b_h_ref,
        200_000_000,
        weighted_improvement_tally,
        weight_tally
    );

    // Helioselene Sub
    println!("helioselene Sub...");
    run_bench!(
        HelioseleneSub,
        a_h - b_h,
        a_h_ref - b_h_ref,
        200_000_000,
        weighted_improvement_tally,
        weight_tally
    );

    // Selene Point Mul
    println!("Selene Point Mul...");
    run_bench!(
        SelenePointMul,
        A_S * a_s,
        A_S_ref * a_s_ref,
        10_000,
        weighted_improvement_tally,
        weight_tally
    );

    /*// Helios Point Mul
    println!("Helios Point Mul...");
    run_bench!(
        HeliosPointMul,
        A_H * a_h,
        A_H_ref * a_h_ref,
        10_000,
        weighted_improvement_tally,
        weight_tally
    );*/

    // Done with the tests
    // assert_eq!(weight_tally, 1f64);
    println!("Overall improvement: {:.2}%\n", weighted_improvement_tally);
    println!("The overall improvement must be >20% in order to qualify as a valid submission.");
    println!("\n");
}
