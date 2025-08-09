#![allow(non_snake_case)]

use helioselene_contest::{
    test_gen_random_helios_point, test_gen_random_helios_scalar, test_gen_random_selene_point,
    test_gen_random_selene_scalar,
};

use helioselene::{
    group::ff::Field as FieldRef, Field25519 as Field25519Ref, HeliosPoint as HeliosPointRef,
    HelioseleneField as HelioseleneFieldRef, SelenePoint as SelenePointRef,
};
use helioselene_contest_src::{
    group::{ff::PrimeField, Group, GroupEncoding},
    Field25519, HeliosPoint, HelioseleneField, SelenePoint,
    ElemExt
};

use rand_core::OsRng;

fn test_field_ops(
    a: HelioseleneField,
    b: HelioseleneField,
    a_ref: HelioseleneFieldRef,
    b_ref: HelioseleneFieldRef,
) {
    // Add
    let res = a + b;
    let res_ref = a_ref + b_ref;
    assert_eq!(res.to_repr(), res_ref.to_repr());

    // Mul
    let res = a * b;
    let res_ref = a_ref * b_ref;
    assert_eq!(res.to_repr(), res_ref.to_repr());

    // Sub
    let res = a - b;
    let res_ref = a_ref - b_ref;
    assert_eq!(res.to_repr(), res_ref.to_repr());

    // Square
    let res = a.square();
    let res_ref = a_ref.square();
    assert_eq!(res.to_repr(), res_ref.to_repr());

    // Double
    let res = a.double();
    let res_ref = a_ref.double();
    assert_eq!(res.to_repr(), res_ref.to_repr());

    // Invert
    let res_ref = a_ref.invert().unwrap();
    let res = a.invert().expect("Failed to invert");
    assert_eq!(res.to_repr(), res_ref.to_repr());

    // Sqrt a square
    let res_ref = a_ref.square().sqrt().unwrap();
    let res = a.square().sqrt().expect("Failed to sqrt");
    assert_eq!(res.to_repr(), res_ref.to_repr());

    // Pow
    let res = a.pow(b);
    let res_ref = a_ref.pow(b_ref);
    assert_eq!(res.to_repr(), res_ref.to_repr());

    // Neg
    let res = -a;
    let res_ref = -a_ref;
    assert_eq!(res.to_repr(), res_ref.to_repr());

    // Odd
    let res = bool::from(a.is_odd());
    let res_ref = bool::from(a_ref.is_odd());
    assert_eq!(res, res_ref);

    // Even
    let res = bool::from(a.is_even());
    let res_ref = bool::from(a_ref.is_even());
    assert_eq!(res, res_ref);
}

fn test_helios_point_ops(
    A: HeliosPoint,
    B: HeliosPoint,
    A_ref: HeliosPointRef,
    B_ref: HeliosPointRef,
    s: HelioseleneField,
    s_ref: HelioseleneFieldRef,
) {
    // Compress point
    let A_bytes = A.to_bytes();
    let A_ref_bytes = A_ref.to_bytes();
    assert_eq!(A_bytes.len(), 32);
    assert_eq!(A_ref_bytes.len(), 32);
    assert_eq!(A_bytes, A_ref_bytes);

    // De-compress point
    assert_eq!(A_ref, HeliosPointRef::from_bytes(&A_ref_bytes).unwrap());
    assert_eq!(A, HeliosPoint::from_bytes(&A_bytes).unwrap());

    // Add
    let res = A + B;
    let res_ref = A_ref + B_ref;
    assert_eq!(res.to_bytes(), res_ref.to_bytes());

    // Mul
    // let res = A * s;
    // let res_ref = A_ref * s_ref;
    // assert_eq!(res.to_bytes(), res_ref.to_bytes());

    // Mul by generator
    // let res = HeliosPoint::generator() * s;
    // let res_ref = HeliosPointRef::generator() * s_ref;
    // assert_eq!(res.to_bytes(), res_ref.to_bytes());

    // Sub
    let res = A - B;
    let res_ref = A_ref - B_ref;
    assert_eq!(res.to_bytes(), res_ref.to_bytes());

    // Double
    let res = A.double();
    let res_ref = A_ref.double();
    assert_eq!(res.to_bytes(), res_ref.to_bytes());

    // Neg
    let res = -A;
    let res_ref = -A_ref;
    assert_eq!(res.to_bytes(), res_ref.to_bytes());
}

fn test_selene_point_ops(
    A: SelenePoint,
    B: SelenePoint,
    A_ref: SelenePointRef,
    B_ref: SelenePointRef,
    s: Field25519,
    s_ref: Field25519Ref,
) {
    // Compress point
    let A_bytes = A.to_bytes();
    let A_ref_bytes = A_ref.to_bytes();
    assert_eq!(A_bytes.len(), 32);
    assert_eq!(A_ref_bytes.len(), 32);
    assert_eq!(A_bytes, A_ref_bytes);

    // De-compress point
    assert_eq!(A_ref, SelenePointRef::from_bytes(&A_ref_bytes).unwrap());
    assert_eq!(A, SelenePoint::from_bytes(&A_bytes).unwrap());

    // Add
    let res = A + B;
    let res_ref = A_ref + B_ref;
    assert_eq!(res.to_bytes(), res_ref.to_bytes());

    // Mul
    let res = A * s;
    let res_ref = A_ref * s_ref;
    assert_eq!(res.to_bytes(), res_ref.to_bytes());

    // Mul by generator
    let res = SelenePoint::generator() * s;
    let res_ref = SelenePointRef::generator() * s_ref;
    assert_eq!(res.to_bytes(), res_ref.to_bytes());

    // Sub
    let res = A - B;
    let res_ref = A_ref - B_ref;
    assert_eq!(res.to_bytes(), res_ref.to_bytes());

    // Double
    let res = A.double();
    let res_ref = A_ref.double();
    assert_eq!(res.to_bytes(), res_ref.to_bytes());

    // Neg
    let res = -A;
    let res_ref = -A_ref;
    assert_eq!(res.to_bytes(), res_ref.to_bytes());
}

static N_ITERS: usize = 1000;

/*#[test]
pub fn test_helioselene_field() {
    ff_group_tests::prime_field::test_prime_field_bits::<_, HelioseleneField>(&mut OsRng);

    // Test that the implementation in ../helioselene-contest-src produces the
    // same results as the reference implementation
    for _ in 0..N_ITERS {
        let (a, a_ref) = test_gen_random_helios_scalar();
        let (b, b_ref) = test_gen_random_helios_scalar();
        test_field_ops(a, b, a_ref, b_ref);
    }
}*/

#[test]
pub fn test_helios_point() {
    ff_group_tests::group::test_prime_group_bits::<_, HeliosPoint>(&mut OsRng);
    for _ in 0..N_ITERS {
        let (A, A_ref) = test_gen_random_helios_point();
        let (B, B_ref) = test_gen_random_helios_point();
        let (s, s_ref) = test_gen_random_helios_scalar();
        test_helios_point_ops(A, B, A_ref, B_ref, s, s_ref);
    }
}

#[test]
pub fn test_selene_point() {
    ff_group_tests::group::test_prime_group_bits::<_, SelenePoint>(&mut OsRng);
    for _ in 0..N_ITERS {
        let (A, A_ref) = test_gen_random_selene_point();
        let (B, B_ref) = test_gen_random_selene_point();
        let (s, s_ref) = test_gen_random_selene_scalar();
        test_selene_point_ops(A, B, A_ref, B_ref, s, s_ref);
    }
}
