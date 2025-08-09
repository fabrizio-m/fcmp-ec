use core::{
  ops::{Add, Mul, Neg, Sub},
};
use rand_core::RngCore;
use subtle::{
  Choice, ConditionallyNegatable, ConditionallySelectable, ConstantTimeEq, ConstantTimeGreater,
  CtOption,
};
use zeroize::Zeroize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Element([u64; 4]);

const MODULUS: Element =
  Element([0x6eb6d2727927c79f, 0xbf7f782cb7656b58, 0xffffffffffffffff, 0x7fffffffffffffff]);

/// MODULUS - 2 for fermat inversion
const MODULUS_FERMAT: Element =
  Element([0x6eb6d2727927c79d, 0xbf7f782cb7656b58, 0xffffffffffffffff, 0x7fffffffffffffff]);

const C: [u64; 2] = [2491153715641217218, 9295728313944582479];

// same as u64::carrying_add, which I was sure was stable, but is actually
// nightly.
fn carrying_add(a: u64, b: u64, carry: bool) -> (u64, bool) {
  // While this may be variable time depending on the callign scope,
  // it should be statically defined, and constant-time at runtime.
  let (c, ov1) = a.overflowing_add(b);
  let (c, ov2) = c.overflowing_add(carry as u64);
  (c, ov1 | ov2)
}

fn borrowing_sub(a: u64, b: u64, carry: bool) -> (u64, bool) {
  let (c, ov1) = a.overflowing_sub(b);
  let (c, ov2) = c.overflowing_sub(carry as u64);
  (c, ov1 | ov2)
}

/// With A >= B
#[inline(always)]
fn add_assing<const A: usize, const B: usize>(a: &mut [u64; A], b: &[u64; B]) -> bool {
  let mut carry = false;
  for i in 0..B {
    let (c, new_carry) = carrying_add(a[i], b[i], carry);
    a[i] = c;
    carry = new_carry;
  }
  if A > B {
    for i in B..A {
      let (c, new_carry) = a[i].overflowing_add(carry as u64);
      a[i] = c;
      carry = new_carry;
    }
  }
  carry
}

/// With A >= B
/// computes c = a - b.
#[inline(always)]
fn sub_assing<const A: usize, const B: usize>(a: &mut [u64; A], b: &[u64; B]) -> bool {
  let mut borrow = false;
  for i in 0..B {
    let (c, new_borrow) = borrowing_sub(a[i], b[i], borrow);
    a[i] = c;
    borrow = new_borrow;
  }
  if A > B {
    for i in B..A {
      let (c, new_carry) = a[i].overflowing_sub(borrow as u64);
      a[i] = c;
      borrow = new_carry;
    }
  }
  borrow
}

impl ConstantTimeEq for Element {
  fn ct_eq(&self, other: &Self) -> Choice {
    self.0[0].ct_eq(&other.0[0])
      & self.0[1].ct_eq(&other.0[1])
      & self.0[2].ct_eq(&other.0[2])
      & self.0[3].ct_eq(&other.0[3])
  }
}

impl ConstantTimeGreater for Element {
  fn ct_gt(&self, other: &Self) -> Choice {
    let mut copy = other.0;
    let borrow = sub_assing(&mut copy, &self.0);
    Choice::from(borrow as u8)
  }
}

impl ConditionallySelectable for Element {
  fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
    let (a, b) = (a.0, b.0);
    let limbs = [
      u64::conditional_select(&a[0], &b[0], choice),
      u64::conditional_select(&a[1], &b[1], choice),
      u64::conditional_select(&a[2], &b[2], choice),
      u64::conditional_select(&a[3], &b[3], choice),
    ];
    Element(limbs)
  }
}

const ZERO: Element = Element([0, 0, 0, 0]);
const ONE: Element = Element([1, 0, 0, 0]);

fn correct_with_carry(mut elem: [u64; 4], carry: bool) -> Element {
  let mut correction = C;
  let select = u64::MAX.wrapping_add(if carry { 0 } else { 1 });
  correction[0] &= select;
  correction[1] &= select;
  let carry = add_assing(&mut elem, &correction);
  debug_assert!(!carry);
  let elem = Element(elem);

  let mut copy = elem;
  let borrow = sub_assing(&mut copy.0, &MODULUS.0);
  let elem = if borrow { elem } else { copy };
  // let mut copy = elem;
  // let borrow = sub_assing(&mut copy.0, &MODULUS.0);
  // let elem = if borrow { elem } else { copy };

  debug_assert!(bool::from(MODULUS.ct_gt(&elem)));
  elem
}

impl Add for Element {
  type Output = Self;

  fn add(mut self, rhs: Self) -> Self::Output {
    let c = add_assing(&mut self.0, &rhs.0);
    debug_assert!(!c);

    let mut copy = self;
    let borrow = sub_assing(&mut copy.0, &MODULUS.0);
    let elem = if borrow { self } else { copy };
    debug_assert!(bool::from(MODULUS.ct_gt(&elem)));
    elem
  }
}

impl Sub for Element {
  type Output = Self;

  fn sub(self, rhs: Self) -> Self::Output {
    let (mut a, b) = (self.0, rhs.0);
    let borrow = sub_assing(&mut a, &b);
    let mut copy = a;
    add_assing(&mut copy, &MODULUS.0);
    //TODO: check compiler doesn't get too smart here.
    let res = if borrow { copy } else { a };
    Element(res)
  }
}

/// (low, high)
fn split(x: u128) -> (u64, u64) {
  let low = x as u64;
  let high = (x >> 64) as u64;
  (low, high)
}

/// Crandall reduction
fn reduce(high: [u64; 4], mut low: [u64; 4]) -> Element {
  let (xc_low, mut xc_high) = {
    let xc = product_scanning_4x2(high, C);
    let [l0, l1, l2, l3, l4, l5] = xc;
    ([l0, l1, l2, l3], [l4, l5])
  };

  let carry = add_assing(&mut low, &xc_low);
  // no overflow risk as xc_high has space for u64::MAX + 1;
  xc_high[0] += if carry { 1 } else { 0 };

  let (xc_low, xc_high) = {
    let xc = product_scanning_2x2(xc_high, C);
    let [l0, l1, l2, l3] = xc;
    ([l0, l1], [l2, l3])
  };

  let xc = [xc_low[0], xc_low[1], xc_high[0], xc_high[1]];
  let carry = add_assing(&mut low, &xc);
  let elem = correct_with_carry(low, carry);
  debug_assert!(bool::from(MODULUS.ct_gt(&elem)));
  elem
}

#[inline(always)]
fn reduce_simple(x: [u64; 5]) -> Element {
  let high = x[4];
  let elem = [x[0], x[1], x[2], x[3]];

  let mut copy = elem;
  let borrow = sub_assing(&mut copy, &MODULUS.0);
  let mut elem = if borrow { elem } else { copy };

  {
    let (l, h) = mul_wide_add(C[0], high, elem[0]);
    elem[0] = l;
    let (l, h) = mul_wide_add2(C[1], high, h, elem[1]);
    elem[1] = l;
    let (l, h) = h.overflowing_add(elem[2]);
    elem[2] = l;
    elem[3] += h as u64;
  }

  let mut copy = elem;
  let borrow = sub_assing(&mut copy, &MODULUS.0);
  let elem = if borrow { elem } else { copy };
  let elem = Element(elem);

  debug_assert!(bool::from(MODULUS.ct_gt(&elem)));
  elem
}

/// (low,high)
#[inline(always)]
fn mul_wide(a: u64, b: u64) -> (u64, u64) {
  let ab = a as u128 * b as u128;
  split(ab)
}

#[inline(always)]
// (low,high)
fn add_carry(a_low: &mut u64, a_high: &mut u64, b: u64, c: bool) -> bool {
  let (a0, c1) = a_low.overflowing_add(b);
  let (a0, c2) = a0.overflowing_add(c as u64);
  *a_low = a0;
  let (a1, c) = a_high.overflowing_add(c1 as u64 + c2 as u64);
  *a_high = a1;
  c
}

/// (low,high)
/// a * b + c
#[inline(always)]
fn mul_wide_add(a: u64, b: u64, c: u64) -> (u64, u64) {
  let ab = a as u128 * b as u128 + c as u128;
  split(ab)
}

#[inline(always)]
/// a * b + c + d
fn mul_wide_add2(a: u64, b: u64, c: u64, d: u64) -> (u64, u64) {
  let ab = a as u128 * b as u128 + c as u128 + d as u128;
  split(ab)
}

/// a * b + c[0] + c[1] .. + c[N-1]
/// May overflow in general, should be used only when some operand
/// is a constant which guarantees overflow won't happen.
#[inline(always)]
fn mul_wide_add_unchecked<const N: usize>(a: u64, b: u64, c: [u64; N]) -> (u64, u64) {
  let mut ab = a as u128 * b as u128;
  for c in c {
    ab += c as u128;
  }
  split(ab)
}

#[inline(always)]
fn add_bits(a: bool, b: bool) -> u8 {
  a as u8 + b as u8
}

fn product_scanning_4x4(a: [u64; 4], b: [u64; 4]) -> [u64; 8] {
  let mut res = [0; 8];
  let c = {
    // 0x0
    let a0b0 = a[0] as u128 * b[0] as u128;
    let (l, h) = split(a0b0);
    res[0] = l;
    h
  };
  let (cl, ch) = {
    // 0x1,1x0
    let (l1, h1) = mul_wide(a[0], b[1]);
    let (l2, h2) = mul_wide_add(a[1], b[0], c);
    let (low, ovf1) = l1.overflowing_add(l2);
    res[1] = low;
    let (high, ovf2) = h1.overflowing_add(h2);
    let (high, ovf3) = high.overflowing_add(ovf1 as u64);
    (high, ovf2 | ovf3)
  };
  let (cl, ch) = {
    // 1x1, 0x2, 2x0
    let (l1, h1) = mul_wide(a[1], b[1]);
    let (l2, h2) = mul_wide(a[0], b[2]);
    let (l3, h3) = mul_wide_add(a[2], b[0], cl);
    let (low, ovf1) = l1.overflowing_add(l2);
    let (low, ovf2) = low.overflowing_add(l3);
    res[2] = low;
    let ovf_l = add_bits(ovf1, ovf2) + ch as u8;
    let (h, ovf3) = h1.overflowing_add(h2);
    let (h, ovf4) = h.overflowing_add(h3);
    let (h, ovf5) = h.overflowing_add(ovf_l as u64);
    let ovf = add_bits(ovf3, ovf4) + ovf5 as u8;
    (h, ovf)
  };
  let (cl, ch) = {
    // 0x3, 3x0, 1x2, 2x1
    let (l1, h1) = mul_wide(a[0], b[3]);
    let (l2, h2) = mul_wide(a[3], b[0]);
    let (l3, h3) = mul_wide(a[1], b[2]);
    let (l4, h4) = mul_wide_add(a[2], b[1], cl);
    let (low, ovf1) = l1.overflowing_add(l2);
    let (low, ovf2) = low.overflowing_add(l3);
    let (low, ovf3) = low.overflowing_add(l4);
    res[3] = low;
    let ovf_low = add_bits(ovf1, ovf2) + ovf3 as u8 + ch;
    let (h, ovf1) = h1.overflowing_add(h2);
    let (h, ovf2) = h.overflowing_add(h3);
    let (h, ovf3) = h.overflowing_add(h4);
    let (h, ovf4) = h.overflowing_add(ovf_low as u64);
    let ovf_high = add_bits(ovf1, ovf2) + add_bits(ovf3, ovf4);
    (h, ovf_high)
  };
  let (cl, ch) = {
    // 1x3, 3x1, 2x2
    let (l1, h1) = mul_wide(a[1], b[3]);
    let (l2, h2) = mul_wide(a[3], b[1]);
    let (l3, h3) = mul_wide_add(a[2], b[2], cl);
    let (low, ovf1) = l1.overflowing_add(l2);
    let (low, ovf2) = low.overflowing_add(l3);
    res[4] = low;
    let ovf_l = add_bits(ovf1, ovf2) + ch;
    let (h, ovf3) = h1.overflowing_add(h2);
    let (h, ovf4) = h.overflowing_add(h3);
    let (h, ovf5) = h.overflowing_add(ovf_l as u64);
    let ovf = add_bits(ovf3, ovf4) + ovf5 as u8;
    (h, ovf)
  };
  let (cl, ch) = {
    //2x3, 3x2,
    let (l1, h1) = mul_wide(a[2], b[3]);
    let (l2, h2) = mul_wide_add(a[3], b[2], cl);
    let (low, ovf1) = l1.overflowing_add(l2);
    let ovf_low = ovf1 as u8 + ch;
    res[5] = low;
    let (h, ovf2) = h1.overflowing_add(h2);
    let (h, ovf3) = h.overflowing_add(ovf_low as u64);
    let ovf_high = add_bits(ovf2, ovf3);
    (h, ovf_high)
  };
  let cl = {
    //3x3
    let (low, h) = mul_wide_add(a[3], b[3], cl);
    res[6] = low;
    let (h, ovf) = h.overflowing_add(ch as u64);
    debug_assert!(!ovf);
    h
  };
  {
    res[7] = cl;
  };
  res
}

fn mul_u128(a: u64, b: u64) -> u128 {
  a as u128 * b as u128
}

fn square_scanning_4x4(x: [u64; 4]) -> [u64; 8] {
  let mut res = [0; 8];
  let c = {
    // 0x0
    let x = x[0] as u128;
    let a0b0 = x * x;
    let (l, h) = split(a0b0);
    res[0] = l;
    h
  };
  let (cl, ch) = {
    // (0x1,1x0)
    let ab = mul_u128(x[0], x[1]);
    let (l1, h1) = split(ab);
    let (l2, h2) = split(ab + c as u128);
    // let (l2, h2) = mul_wide_add(a[1], b[0], c);
    let (low, ovf1) = l1.overflowing_add(l2);
    res[1] = low;
    let (high, ovf2) = h1.overflowing_add(h2);
    let (high, ovf3) = high.overflowing_add(ovf1 as u64);
    (high, ovf2 | ovf3)
  };
  let (cl, ch) = {
    // 1x1, (0x2, 2x0)
    let (l1, h1) = mul_wide(x[2], x[0]);
    let (l2, h2) = mul_wide(x[2], x[0]);
    let (l3, h3) = mul_wide_add(x[1], x[1], cl);
    let (low, ovf1) = l1.overflowing_add(l2);
    let (low, ovf2) = low.overflowing_add(l3);
    res[2] = low;
    let ovf_l = add_bits(ovf1, ovf2) + ch as u8;
    let (h, ovf3) = h1.overflowing_add(h2);
    let (h, ovf4) = h.overflowing_add(h3);
    let (h, ovf5) = h.overflowing_add(ovf_l as u64);
    let ovf = add_bits(ovf3, ovf4) + ovf5 as u8;
    (h, ovf)
  };
  let (cl, ch) = {
    // (0x3, 3x0), (1x2, 2x1)
    let (l1, h1) = mul_wide(x[0], x[3]);
    let (l2, h2) = (l1, h1);
    let x21 = mul_u128(x[1], x[2]);
    let (l3, h3) = split(x21);
    let (l4, h4) = split(x21 + cl as u128);
    let (low, ovf1) = l1.overflowing_add(l2);
    let (low, ovf2) = low.overflowing_add(l3);
    let (low, ovf3) = low.overflowing_add(l4);
    res[3] = low;
    let ovf_low = add_bits(ovf1, ovf2) + ovf3 as u8 + ch;
    let (h, ovf1) = h1.overflowing_add(h2);
    let (h, ovf2) = h.overflowing_add(h3);
    let (h, ovf3) = h.overflowing_add(h4);
    let (h, ovf4) = h.overflowing_add(ovf_low as u64);
    let ovf_high = add_bits(ovf1, ovf2) + add_bits(ovf3, ovf4);
    (h, ovf_high)
  };
  let (cl, ch) = {
    // (1x3, 3x1), 2x2
    let (l1, h1) = mul_wide(x[1], x[3]);
    let (l2, h2) = (l1, h1);
    let (l3, h3) = mul_wide_add(x[2], x[2], cl);
    let (low, ovf1) = l1.overflowing_add(l2);
    let (low, ovf2) = low.overflowing_add(l3);
    res[4] = low;
    let ovf_l = add_bits(ovf1, ovf2) + ch;
    let (h, ovf3) = h1.overflowing_add(h2);
    let (h, ovf4) = h.overflowing_add(h3);
    let (h, ovf5) = h.overflowing_add(ovf_l as u64);
    let ovf = add_bits(ovf3, ovf4) + ovf5 as u8;
    (h, ovf)
  };
  let (cl, ch) = {
    //(2x3, 3x2),
    let x23 = mul_u128(x[2], x[3]);
    let (l1, h1) = split(x23);
    let (l2, h2) = split(x23 + cl as u128);
    let (low, ovf1) = l1.overflowing_add(l2);
    let ovf_low = ovf1 as u8 + ch;
    res[5] = low;
    let (h, ovf2) = h1.overflowing_add(h2);
    let (h, ovf3) = h.overflowing_add(ovf_low as u64);
    let ovf_high = add_bits(ovf2, ovf3);
    (h, ovf_high)
  };
  let cl = {
    //3x3
    let (low, h) = mul_wide_add(x[3], x[3], cl);
    res[6] = low;
    let (h, ovf) = h.overflowing_add(ch as u64);
    debug_assert!(!ovf);
    h
  };
  {
    res[7] = cl;
  };
  res
}

fn product_scanning_4x2(a: [u64; 4], b: [u64; 2]) -> [u64; 6] {
  let mut res = [0; 6];
  let c = {
    // 0x0
    let a0b0 = a[0] as u128 * b[0] as u128;
    let (l, h) = split(a0b0);
    res[0] = l;
    h
  };
  let (cl, ch) = {
    // 0x1,1x0
    let (l1, h1) = mul_wide(a[0], b[1]);
    let (l2, h2) = mul_wide_add(a[1], b[0], c);
    let (low, ovf1) = l1.overflowing_add(l2);
    res[1] = low;
    let (high, ovf2) = h1.overflowing_add(h2);
    let (high, ovf3) = high.overflowing_add(ovf1 as u64);
    (high, ovf2 | ovf3)
  };
  let (cl, ch) = {
    // 1x1, 2x0
    let (l1, h1) = mul_wide(a[1], b[1]);
    let (l2, h2) = mul_wide_add(a[2], b[0], cl);
    let (low, ovf1) = l1.overflowing_add(l2);
    res[2] = low;
    let ovf_l = add_bits(ovf1, ch);
    let (h, ovf3) = h1.overflowing_add(h2);
    let (h, ovf4) = h.overflowing_add(ovf_l as u64);
    let ovf = add_bits(ovf3, ovf4);
    (h, ovf)
  };
  let (cl, ch) = {
    // 3x0, 2x1
    let (l1, h1) = mul_wide(a[3], b[0]);
    let (l2, h2) = mul_wide_add(a[2], b[1], cl);
    let (low, ovf1) = l1.overflowing_add(l2);
    res[3] = low;
    let ovf_low = ovf1 as u8 + ch;
    let (h, ovf1) = h1.overflowing_add(h2);
    let (h, ovf2) = h.overflowing_add(ovf_low as u64);
    let ovf_high = add_bits(ovf1, ovf2);
    (h, ovf_high)
  };
  let cl = {
    // 3x1
    let (low, h) = mul_wide_add(a[3], b[1], cl);
    res[4] = low;
    let ovf_l = ch;
    let (h, ovf) = h.overflowing_add(ovf_l as u64);
    h + ovf as u64
  };
  {
    res[5] = cl;
  };
  res
}

#[inline(always)]
fn product_scanning_4x1(a: [u64; 4], b: u64) -> [u64; 5] {
  let mut res = [0; 5];
  let c = {
    // 0x0
    let a0b0 = a[0] as u128 * b as u128;
    let (l, h) = split(a0b0);
    res[0] = l;
    h
  };
  let c = {
    // 1x0
    let (low, high) = mul_wide_add(a[1], b, c);
    res[1] = low;
    high
  };
  let c = {
    //  2x0
    let (low, high) = mul_wide_add(a[2], b, c);
    res[2] = low;
    high
  };
  let c = {
    // 3x0
    let (low, high) = mul_wide_add(a[3], b, c);
    res[3] = low;
    high
  };
  {
    res[4] = c;
  };
  res
}

fn product_scanning_2x2(a: [u64; 2], b: [u64; 2]) -> [u64; 4] {
  let mut res = [0; 4];
  let c = {
    // 0x0
    let a0b0 = a[0] as u128 * b[0] as u128;
    let (l, h) = split(a0b0);
    res[0] = l;
    h
  };
  let (cl, ch) = {
    // 0x1, 1x0
    let (l1, h1) = mul_wide(a[0], b[1]);
    let (l2, h2) = mul_wide_add(a[1], b[0], c);
    let (low, ovf1) = l1.overflowing_add(l2);
    res[1] = low;
    let (high, ovf2) = h1.overflowing_add(h2);
    let (high, ovf3) = high.overflowing_add(ovf1 as u64);
    (high, ovf2 | ovf3)
  };
  let cl = {
    // 1x1
    let (low, h) = mul_wide_add(a[1], b[1], cl);
    res[2] = low;
    let (h, ovf) = h.overflowing_add(ch as u64);
    h + ovf as u64
  };
  {
    res[3] = cl;
  };
  res
}

#[inline(always)]
pub fn hybrid_scanning(a: [u64; 4], b: [u64; 4]) -> (bool, [u64; 4]) {
  let mut res = [0; 4];
  // carry of res[2], which should be added into res[3]
  let mut carry2;
  // carry of res[3], to be multiplied by C and added to the result.
  let carry3;
  let c = {
    // 0x0
    let a0b0 = a[0] as u128 * b[0] as u128;
    let (l, h) = split(a0b0);
    res[0] = l;
    h
  };
  let (cl, ch) = {
    // 0x1,1x0
    let (l1, h1) = mul_wide(a[0], b[1]);
    let (l2, h2) = mul_wide_add(a[1], b[0], c);
    let (low, ovf1) = l1.overflowing_add(l2);
    res[1] = low;
    let (high, ovf2) = h1.overflowing_add(h2);
    let (high, ovf3) = high.overflowing_add(ovf1 as u64);
    (high, ovf2 | ovf3)
  };
  let (cl, ch) = {
    // 1x1, 0x2, 2x0
    let (l1, h1) = mul_wide(a[1], b[1]);
    let (l2, h2) = mul_wide(a[0], b[2]);
    let (l3, h3) = mul_wide_add(a[2], b[0], cl);
    let (low, ovf1) = l1.overflowing_add(l2);
    let (low, ovf2) = low.overflowing_add(l3);
    res[2] = low;
    let ovf_l = add_bits(ovf1, ovf2) + ch as u8;
    let (h, ovf3) = h1.overflowing_add(h2);
    let (h, ovf4) = h.overflowing_add(h3);
    let (h, ovf5) = h.overflowing_add(ovf_l as u64);
    let ovf = add_bits(ovf3, ovf4) + ovf5 as u8;
    (h, ovf)
  };
  let (cl, ch) = {
    // 0x3, 3x0, 1x2, 2x1
    let (l1, h1) = mul_wide(a[0], b[3]);
    let (l2, h2) = mul_wide(a[3], b[0]);
    let (l3, h3) = mul_wide(a[1], b[2]);
    let (l4, h4) = mul_wide_add(a[2], b[1], cl);
    let (low, ovf1) = l1.overflowing_add(l2);
    let (low, ovf2) = low.overflowing_add(l3);
    let (low, ovf3) = low.overflowing_add(l4);
    res[3] = low;
    let ovf_low = add_bits(ovf1, ovf2) + ovf3 as u8 + ch;
    let (h, ovf1) = h1.overflowing_add(h2);
    let (h, ovf2) = h.overflowing_add(h3);
    let (h, ovf3) = h.overflowing_add(h4);
    let (h, ovf4) = h.overflowing_add(ovf_low as u64);
    let ovf_high = add_bits(ovf1, ovf2) + add_bits(ovf3, ovf4);
    (h, ovf_high)
  };
  let (cl, ch) = {
    // 1x3, 3x1, 2x2
    let (l1, h1) = mul_wide(a[1], b[3]);
    let (l2, h2) = mul_wide(a[3], b[1]);
    let (l3, h3) = mul_wide_add(a[2], b[2], cl);
    let (low, ovf1) = l1.overflowing_add(l2);
    let (low, ovf2) = low.overflowing_add(l3);
    let res_4 = low;
    {
      let (r0, h) = mul_wide_add(res_4, C[0], res[0]);
      res[0] = r0;
      let (r1, h) = mul_wide_add2(res_4, C[1], res[1], h);
      res[1] = r1;
      let (r2, h) = res[2].overflowing_add(h);
      res[2] = r2;
      // carries[2] = h as u8;
      carry2 = h;
    }
    let ovf_l = add_bits(ovf1, ovf2) + ch;
    let (h, ovf3) = h1.overflowing_add(h2);
    let (h, ovf4) = h.overflowing_add(h3);
    let (h, ovf5) = h.overflowing_add(ovf_l as u64);
    let ovf = add_bits(ovf3, ovf4) + ovf5 as u8;
    (h, ovf)
  };
  let (cl, ch) = {
    //2x3, 3x2,
    let (l1, h1) = mul_wide(a[2], b[3]);
    let (l2, h2) = mul_wide_add(a[3], b[2], cl);
    let (low, ovf1) = l1.overflowing_add(l2);
    let ovf_low = ovf1 as u8 + ch;
    let res_5 = low;
    {
      let (r1, h) = mul_wide_add(res_5, C[0], res[1]);
      res[1] = r1;
      let (r2, h) = mul_wide_add2(res_5, C[1], res[2], h);
      res[2] = r2;
      let (r3, h1) = res[3].overflowing_add(h);
      let (r3, h2) = r3.overflowing_add(carry2 as u64);
      res[3] = r3;
      carry3 = h1 | h2;
    }
    let (h, ovf2) = h1.overflowing_add(h2);
    let (h, ovf3) = h.overflowing_add(ovf_low as u64);
    let ovf_high = add_bits(ovf2, ovf3);
    (h, ovf_high)
  };
  let cl = {
    //3x3
    let (low, h) = mul_wide_add(a[3], b[3], cl);
    let res_6 = low;
    {
      //2x0c
      let (r2, h) = mul_wide_add(res_6, C[0], res[2]);
      let (r3, hc) = mul_wide_add2(res_6, C[1], res[3], h);
      res[3] = r3;

      let (r0, h) = mul_wide_add(hc, C[0], res[0]);
      res[0] = r0;
      let (r1, h) = mul_wide_add2(hc, C[1], res[1], h);
      res[1] = r1;
      let (r2, h) = r2.overflowing_add(h);
      res[2] = r2;
      carry2 = h;
    }
    let (h, ovf) = h.overflowing_add(ch as u64);
    debug_assert!(!ovf);
    h
  };
  let b = {
    let res_7 = cl;

    //7x0 - 4 = 3x0
    let (r3, h) = mul_wide_add2(res_7, C[0], res[3], carry2 as u64);
    res[3] = r3;
    // 3x1
    let (r4, r5) = mul_wide_add2(res_7, C[1], h, carry3 as u64);

    //0x0
    let (r0, h) = mul_wide_add(r4, C[0], res[0]);
    res[0] = r0;
    //0x1 1x0
    let (r11, h1) = mul_wide_add2(r5, C[0], h, res[1]);
    let (r12, h2) = mul_wide(r4, C[1]);
    let (r1, ovb) = r11.overflowing_add(r12);
    res[1] = r1;
    //1x1
    // as C[1] < u64::MAX, we can add a third value without overflow.
    let (r2, r3) = mul_wide_add_unchecked(r5, C[1], [h1, h2, ovb as u64, res[2]]);
    res[2] = r2;
    let (r3, h) = r3.overflowing_add(res[3]);
    res[3] = r3;
    h
  };
  (b, res)
}

#[inline(always)]
/// Full modular multiplication, result < MODULUS.
pub fn mod_product_scanning(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
  let mut res = [0; 4];

  // 0: 0x0
  let r1 = {
    let (l, h) = mul_wide(a[0], b[0]);
    res[0] = l;
    h
  };

  // 1: 1x0 0x1
  let (r2, r3) = {
    let (r1, r2) = mul_wide_add(a[1], b[0], r1);
    let (r1, h) = mul_wide_add(a[0], b[1], r1);
    res[1] = r1;
    carrying_add(r2, h, false)
  };

  // 2: 2x0 0x2 1x1
  let (r3, r4) = {
    let mut r3 = r3 as u64;
    let mut r4 = 0;

    let (r2, h) = mul_wide_add(a[2], b[0], r2);
    let _ = add_carry(&mut r3, &mut r4, h, false);

    let (r2, h) = mul_wide_add(a[0], b[2], r2);
    let _ = add_carry(&mut r3, &mut r4, h, false);

    let (r2, h) = mul_wide_add(a[1], b[1], r2);
    let _ = add_carry(&mut r3, &mut r4, h, false);

    res[2] = r2;
    (r3, r4)
  };

  // 3: 3x0 0x3 2x1 1x2
  let (r4, r5) = {
    let (mut r4, mut r5) = (r4, 0);

    let (r3, h) = mul_wide_add(a[3], b[0], r3);
    let _ = add_carry(&mut r4, &mut r5, h, false);

    let (r3, h) = mul_wide_add(a[0], b[3], r3);
    let _ = add_carry(&mut r4, &mut r5, h, false);

    let (r3, h) = mul_wide_add(a[2], b[1], r3);
    let _ = add_carry(&mut r4, &mut r5, h, false);

    let (r3, h) = mul_wide_add(a[1], b[2], r3);
    let _ = add_carry(&mut r4, &mut r5, h, false);

    res[3] = r3;
    (r4, r5)
  };

  // 4: 3x1 1x3 2x2
  let (r4, r5, r6) = {
    let (mut r5, mut r6) = (r5, 0);

    let (r4, h) = mul_wide_add(a[3], b[1], r4);
    let _ = add_carry(&mut r5, &mut r6, h, false);

    let (r4, h) = mul_wide_add(a[1], b[3], r4);
    let _ = add_carry(&mut r5, &mut r6, h, false);

    let (r4, h) = mul_wide_add(a[2], b[2], r4);
    let _ = add_carry(&mut r5, &mut r6, h, false);

    (r4, r5, r6)
  };

  // 5: 3x2 2x3
  let (r5, r6, r7) = {
    let (mut r6, mut r7) = (r6, 0);

    let (r5, h) = mul_wide_add(a[3], b[2], r5);
    let _ = add_carry(&mut r6, &mut r7, h, false);

    let (r5, h) = mul_wide_add(a[2], b[3], r5);
    let _ = add_carry(&mut r6, &mut r7, h, false);

    (r5, r6, r7)
  };

  // 6: 3x3
  let (r6, r7) = {
    let (r6, h) = mul_wide_add(a[3], b[3], r6);
    // let r7 = r7.wrapping_add(h);
    let r7 = r7 + h;
    (r6, r7)
  };

  // First Reduction

  let a = [r4, r5, r6, r7];

  // 0: 0x0
  let r1 = {
    let (r0, r1) = mul_wide_add(a[0], C[0], res[0]);
    res[0] = r0;
    r1
  };

  // 1: 0x1 1x0
  let (r2, r3) = {
    let mut r3 = 0;

    let (r1, mut r2) = mul_wide_add2(a[0], C[1], r1, res[1]);

    let (r1, h) = mul_wide_add(a[1], C[0], r1);
    let _ = add_carry(&mut r2, &mut r3, h, false);

    res[1] = r1;
    (r2, r3)
  };

  // 2: 2x0 !0x2 1x1
  let (r3, r4) = {
    let (mut r3, mut r4) = (r3, 0);

    let (r2, h) = mul_wide_add2(a[2], C[0], r2, res[2]);
    let _ = add_carry(&mut r3, &mut r4, h, false);

    let (r2, h) = mul_wide_add(a[1], C[1], r2);
    let _ = add_carry(&mut r3, &mut r4, h, false);

    res[2] = r2;
    (r3, r4)
  };

  // 3: 3x0 !0x3 2x1 !1x2
  let (r4, r5) = {
    let (mut r4, mut r5) = (r4, 0);

    let (r3, h) = mul_wide_add2(a[3], C[0], r3, res[3]);
    let _ = add_carry(&mut r4, &mut r5, h, false);

    let (r3, h) = mul_wide_add(a[2], C[1], r3);
    let _ = add_carry(&mut r4, &mut r5, h, false);

    res[3] = r3;

    (r4, r5)
  };

  // 4: 3x1 !1x3 !2x2
  let (r4, r5) = {
    let (r4, h) = mul_wide_add(a[3], C[1], r4);
    (r4, r5 + h)
  };

  // Second Reduction
  let a = [r4, r5];

  //0: 0x0
  let r1 = {
    let (r0, r1) = mul_wide_add(a[0], C[0], res[0]);
    res[0] = r0;
    r1
  };

  //1: 0x1 1x0
  let r2 = {
    let (r1, r2_1) = mul_wide_add2(a[0], C[1], r1, res[1]);
    let (r1, r2_2) = mul_wide_add(a[1], C[0], r1);
    res[1] = r1;
    (r2_1, r2_2)
  };

  //2: !0x2 !2x0 1x1
  let r3 = {
    let (r2, r3) = mul_wide_add_unchecked(a[1], C[1], [r2.0, r2.1, res[2]]);
    res[2] = r2;
    r3
  };

  let r4 = {
    let (r3, r4) = carrying_add(r3, res[3], false);
    res[3] = r3;
    r4
  };

  // Final correction

  let mut copy = res;
  let borrow = sub_assing(&mut copy, &MODULUS.0);
  let res = if borrow { res } else { copy };

  let res = {
    let a = r4 as u64;
    let (r0, r1) = mul_wide_add(a, C[0], res[0]);
    let (r1, r2) = mul_wide_add2(a, C[1], res[1], r1);
    let (r2, r3) = carrying_add(r2, res[2], false);
    let r3 = r3 as u64 + res[3];
    [r0, r1, r2, r3]
  };

  let mut copy = res;
  let borrow = sub_assing(&mut copy, &MODULUS.0);
  if borrow {
    res
  } else {
    copy
  }
}

impl Mul for Element {
  type Output = Self;

  #[inline(always)]
  fn mul(self, rhs: Self) -> Self::Output {
    let (a, b) = (self.0, rhs.0);
    let elem = Element(mod_product_scanning(&a, &b));
    debug_assert!(bool::from(MODULUS.ct_gt(&elem)));
    elem
  }
}

const MASK: u64 = 1 << 63;

impl Element {
  pub const ZERO: Self = ZERO;
  pub const ONE: Self = ONE;

  pub const fn new(words: [u64; 4]) -> Self {
    Self(words)
  }

  fn pow_u64(self, exp: u64, chain: Option<Self>) -> Self {
    let mut res = chain.unwrap_or(ONE);
    for i in 0..64 {
      res = res.square();
      let bit = (exp & (MASK >> i)).count_ones();
      let choice = Choice::from(bit as u8);
      let mut to_multiply = ONE;
      to_multiply.conditional_assign(&self, choice);
      res = res * to_multiply;
    }
    res
  }

  pub fn pow(self, exp: Self) -> Self {
    let mut res = ONE;
    for i in 0..4 {
      let exp = exp.0[3 - i];
      res = self.pow_u64(exp, Some(res));
    }
    res
  }

  /// Using Fermat's Little Theorem for simplicity, the EEA may
  /// be better for performance.
  fn inverse_fermat(self) -> Self {
    self.pow(MODULUS_FERMAT)
  }

  #[inline(always)]
  pub fn square(self) -> Self {
    //NOTE: specialized square doesn't seem to have a drastic improvement over this.
    let elem = Element(mod_product_scanning(&self.0, &self.0));
    debug_assert!(bool::from(MODULUS.ct_gt(&elem)));
    elem
  }
  const TWO_INV: Element =
    Element([0x375b69393c93e3d0, 0xdfbfbc165bb2b5ac, 0xffffffffffffffff, 0x3fffffffffffffff]);

  fn halve(self) -> Self {
    let (even, borrow) = shift(self);
    let odd = even + Self::TWO_INV;
    if borrow {
      odd
    } else {
      even
    }
  }

  pub fn is_even(&self) -> bool {
    self.0[0] & 0x1 == 0
  }

  // plus-minus inversion method adapted for constant time
  fn inverse(self) -> Self {
    let mut a = self;
    let mut b = MODULUS;
    let mut u = (ONE, ZERO);
    //TODO: make constant time
    for _ in 0..(256 * 2 + 4) {
      if a.is_even() {
        let (new_a, overflow) = shift(a);
        a = new_a;
        u.0 = u.0.halve();
        debug_assert!(!overflow);
      } else {
        if bool::from(b.ct_gt(&a)) {
          core::mem::swap(&mut a, &mut b);
          core::mem::swap(&mut u.0, &mut u.1);
        }

        let ab = a + b;
        let plus = (ab.0[0] & 0b11) == 0;

        if plus {
          let (new_a, overflow) = shift(ab);
          a = new_a;
          debug_assert!(!overflow);
          u.0 = (u.0 + u.1).halve();
        } else {
          let (new_a, overflow) = shift(a - b);
          a = new_a;
          debug_assert!(!overflow);
          u.0 = (u.0 - u.1).halve();
        }
      }
    }

    if b.0[0] == 1 {
      u.1
    } else {
      u.1.neg()
    }
  }

  #[inline(always)]
  fn simple_mul(self, rhs: u64) -> Self {
    let x = product_scanning_4x1(self.0, rhs);
    reduce_simple(x)
  }

  /// Compress A into a single u64 made up of the highest 33 bits, and the lowest 31.
  /// Same with B, but the highest bits are taken from the same range as A.
  /// B is expected to be smaller than A.
  /// When bits(A) < 64 this is equivalent to just take the lowest limb.
  fn compress(mut a: Self, mut b: Self) -> (u64, u64) {
    let swap = bool::from(b.ct_gt(&a));
    if swap {
      core::mem::swap(&mut a, &mut b);
    }
    debug_assert!(!bool::from(b.ct_gt(&a)));
    let (a, b) = (a.0, b.0);
    let small_a = ((1 << 31) - 1) & a[0];
    let small_b = ((1 << 31) - 1) & b[0];

    let mut ab = (a[0] >> 31, b[0] >> 31);

    for i in 0..3 {
      let non_zero = a[i + 1].ct_ne(&0);
      let high_bits = u64::BITS - a[i + 1].leading_zeros();

      let high = a[i + 1] >> (high_bits.saturating_sub(33));
      let high = high << (33_u32.saturating_sub(high_bits));
      let a = high | ((a[i] >> 32) >> (high_bits.saturating_sub(1)));

      let high = b[i + 1] >> (high_bits.saturating_sub(33));
      let high = high << (33_u32.saturating_sub(high_bits));
      let b = high | ((b[i] >> 32) >> (high_bits.saturating_sub(1)));

      ab.0.conditional_assign(&a, non_zero);
      ab.1.conditional_assign(&b, non_zero);
    }

    let mut a = small_a | (ab.0 << 31);
    let mut b = small_b | (ab.1 << 31);
    if swap {
      core::mem::swap(&mut a, &mut b);
    }
    (a, b)
  }

  /// The inverse of 2^31
  const fn inverse_shift() -> Self {
    Element([9242182130291577655, 15289291369412052737, 18446744073709551615, 6265751320813109247])
  }

  /// 2^(-31 * 16)
  const fn inverse_shift16() -> Self {
    Element([10262430887218310098, 7186200574519028691, 16424616000314463248, 6329167355612373177])
  }

  fn gcd_word(a: Self, b: Self) -> (Self, Self, [i64; 4]) {
    let (old_a, old_b) = (a, b);
    let (mut a, mut b) = Self::compress(old_a, old_b);
    // (u.0,u.1) <- (f0 * u.0 + g0 * u.1, f1 * u.0 + g1 * u.1)
    let [mut f0, mut g0, mut f1, mut g1] = [1i64, 0, 0, 1];
    for _ in 0..31 {
      if a % 2 == 0 {
        let new_a = a >> 1;
        a = new_a;
        f1 <<= 1;
        g1 <<= 1;
        continue;
      }

      if bool::from(b.ct_gt(&a)) {
        core::mem::swap(&mut a, &mut b);
        core::mem::swap(&mut f0, &mut f1);
        core::mem::swap(&mut g0, &mut g1);
      }

      let new_a = (a - b) >> 1;
      a = new_a;

      f0 -= f1;
      g0 -= g1;
      f1 <<= 1;
      g1 <<= 1;
    }

    let shift = Self::inverse_shift();

    let mut a = (old_a * f0 + old_b * g0) * shift;
    let neg_a = -a;
    let negate = a.ct_gt(&neg_a);
    a.conditional_assign(&neg_a, negate);
    f0.conditional_negate(negate);
    g0.conditional_negate(negate);

    let mut b = (old_a * f1 + old_b * g1) * shift;
    let neg_b = -b;
    let negate = b.ct_gt(&neg_b);
    b.conditional_assign(&neg_b, negate);
    f1.conditional_negate(negate);
    g1.conditional_negate(negate);

    (a, b, [f0, g0, f1, g1])
  }

  fn inverse_fast(self) -> Self {
    //https://eprint.iacr.org/2020/972.pdf
    let mut a = self;
    let mut b = MODULUS;
    let mut u = (ONE, ZERO);
    for _ in 0..16 {
      let (new_a, new_b, factors) = Self::gcd_word(a, b);
      a = new_a;
      b = new_b;
      let [f0, g0, f1, g1] = factors;
      let new_u0 = u.0 * f0 + u.1 * g0;
      let new_u1 = u.0 * f1 + u.1 * g1;
      u = (new_u0, new_u1);
    }
    let shift = Self::inverse_shift16();
    let u = u.1 * shift;
    debug_assert_eq!(b, ONE);
    u
  }
}

impl Mul<u64> for Element {
  type Output = Self;

  #[inline(always)]
  fn mul(self, rhs: u64) -> Self::Output {
    self.simple_mul(rhs)
  }
}
impl Mul<i64> for Element {
  type Output = Self;

  #[inline(always)]
  fn mul(mut self, rhs: i64) -> Self::Output {
    let negative = rhs < 0;
    self.conditional_negate(Choice::from(negative as u8));
    self * rhs.unsigned_abs()
  }
}

fn shift(mut x: Element) -> (Element, bool) {
  let low_bit = (x.0[0] & 0x1) == 1;
  for i in 0..3 {
    x.0[i] >>= 1;
    x.0[i] |= x.0[i + 1] << 63;
  }
  x.0[3] >>= 1;
  (x, low_bit)
}

impl From<u64> for Element {
  fn from(value: u64) -> Self {
    Self([value, 0, 0, 0])
  }
}

impl Neg for Element {
  type Output = Self;

  fn neg(self) -> Self::Output {
    ZERO - self
  }
}

pub trait ElemExt: Sized {
  type Repr: Copy + Default + Send + Sync + 'static + AsRef<[u8]> + AsMut<[u8]>;
  fn random(rng: impl RngCore) -> Self;
  fn to_repr(&self) -> Self::Repr;
  fn from_repr(repr: Self::Repr) -> CtOption<Self>;
  fn is_odd(&self) -> Choice;
  fn invert(&self) -> CtOption<Self>;
  fn double(self) -> Self;
  fn sqrt(self) -> CtOption<Self>;
  fn is_zero(&self) -> Choice;
}

/// (MODULUS + 1) / 4
const SQRT_EXP: Element =
  Element([0x1badb49c9e49f1e8, 0xefdfde0b2dd95ad6, 0xffffffffffffffff, 0x1fffffffffffffff]);

impl ElemExt for Element {
  type Repr = [u8; 32];

  fn random(mut rng: impl RngCore) -> Self {
    let low = [(); 4].map(|_| rng.next_u64());
    let high = [(); 4].map(|_| rng.next_u64());
    reduce(high, low)
  }

  fn to_repr(&self) -> Self::Repr {
    let mut repr = [0; 32];
    for i in 0..4 {
      let word: [u8; 8] = self.0[i].to_le_bytes();
      for j in 0..8 {
        repr[i * 8 + j] = word[j]
      }
    }
    repr
  }

  fn from_repr(repr: Self::Repr) -> CtOption<Self> {
    let mut elem = ZERO;
    let mut word_bytes = [0; 8];
    for i in 0..4 {
      word_bytes.clone_from_slice(&repr[(i * 8)..(i * 8 + 8)]);
      elem.0[i] = u64::from_le_bytes(word_bytes);
    }
    let valid = MODULUS.ct_gt(&elem);
    CtOption::new(elem, valid)
  }

  fn is_odd(&self) -> Choice {
    let lowest = self.0[0] as u8;
    Choice::from(lowest & 1)
  }

  fn invert(&self) -> CtOption<Self> {
    let is_zero = ZERO.ct_eq(self);
    CtOption::new(self.inverse_fast(), !is_zero)
  }

  fn double(self) -> Self {
    self + self
  }

  fn sqrt(self) -> CtOption<Self> {
    let sqrt = self.pow(SQRT_EXP);
    let is_sqrt = self.ct_eq(&sqrt.square());
    CtOption::new(sqrt, is_sqrt)
  }

  fn is_zero(&self) -> Choice {
    ZERO.ct_eq(self)
  }
}

#[test]
fn test_sqrt() {
  for i in 0..100 {
    let x = Element([i, 34, i, 1241]);
    let xx = x.square();
    let sqrt = xx.sqrt().unwrap();
    assert_eq!(xx, sqrt.square());
  }
}

#[test]
fn test_inverse() {
  for i in 1..200 {
    let x = Element([i, 0, i, 0]);
    let inv = x.inverse_fermat();
    assert_eq!(x * inv, ONE);
    assert_eq!(inv.inverse_fermat(), x);
  }
}

#[test]
fn test_inverse_fast() {
  for i in 1..255 {
    let x = Element([i, 0, i, 0]);
    let inv_good = x.inverse_fermat();
    let inv_fast = x.inverse_fast();
    assert_eq!(inv_good, inv_fast);
    let new_x = inv_fast.inverse_fast();
    assert_eq!(new_x, x);
  }
}

impl Zeroize for Element {
  fn zeroize(&mut self) {
    self.0[0].zeroize();
    self.0[1].zeroize();
    self.0[2].zeroize();
    self.0[3].zeroize();
  }
}

impl ConditionallyNegatable for Element {
  fn conditional_negate(&mut self, choice: Choice) {
    let negated = -*self;
    self.conditional_assign(&negated, choice);
  }
}

/*mod tests {
  use super::*;

  #[test]
  fn test_doubles() {
    let two = Element([2, 0, 0, 0]);

    let p = 260;
    let mut x = two;
    for i in 0..p {
      x = x * two;
      if i >= (p - 10) {
        println!("x_{i}: {:?}", x);
      }
    }
    let mut x = two;
    for i in 0..260 {
      let ol_x = x;
      x = x + x;
      if i >= p {
        assert_eq!(ol_x, x - ol_x);
        // println!("x_{i}: {:?}", x);
      }
    }
  }

  #[test]
  fn test_pow_full() {
    for i in 1..500_u64 {
      let x = Element([i, 0, i, 0]);
      let exp1 = i;
      let exp2 = i.wrapping_pow(32145);

      let c1 = x.pow_u64(exp1, None) * x.pow_u64(exp2, None);
      let c2 = x.pow_u64(exp1 + exp2, None);
      assert_eq!(c1, c2, "failed with i = {i}");
    }
  }

  #[ignore = "for debug"]
  #[test]
  fn test_mul() {
    let a = Element([7, 0, 7, 0]);
    let b = Element([
      2514618358437031971,
      7144711670143738068,
      17866140284543166071,
      4010535337322065924,
    ]);

    println!("MOD = {:?}", MODULUS);
    println!("a = {:?}", a);
    println!("b = {:?}", b);
    println!("a*b = {:?}", a * b);

    println!("b*a = {:?}", b * a);
    println!("a+a = {:?}", a + a);
    let a2 = a + a;
    assert!(bool::from(MODULUS.ct_gt(&a2)));
    assert!(!bool::from(MODULUS.ct_eq(&a2)));
    let ab = a * b;
    let ab = ab - Element([C[0], C[1], 0, 0]);
    println!("a*b+c = {:?}", ab);
  }

  #[ignore = "just to find C"]
  #[test]
  fn find_c() {
    let mut c = ZERO;
    let borrow = sub_assing(&mut c.0, &MODULUS.0);
    assert!(borrow);
    let borrow = sub_assing(&mut c.0, &MODULUS.0);
    assert!(!borrow);
    println!("C: {:?}", c);
  }
}
*/

// (x + 1)2 = x/2 + 1/2

#[test]
fn halving() {
  // println!("2 inv: {:x?}", (Element([2, 0, 0, 0])).inverse());
  for i in 1..1000 {
    let x = [i, 23, i, i];
    let x = Element(x);
    // println!("x: {:?}", x);
    assert_eq!(x, (x * Element::TWO_INV) * (ONE + ONE));
    // println!("diff {:x?}", (x * Element::TWO_INV) - x.halve());
    assert_eq!(x.halve(), x * Element::TWO_INV);
  }
}

#[test]
fn bench_mul() {
  for i in 0..10000 {
    let x = Element([124124, i, 214214, i]);
    let _inv = x.inverse_fermat();
  }
}

#[test]
fn compress() {
  // checking Element::compress works as expected.
  let mut a: u64 = 3;
  for _ in 0..100 {
    a = a.wrapping_mul(a);
    let mut x = Element([a | 1 << 63, 0, 0, 0]);
    for _ in 0..192 {
      let (aa, _) = Element::compress(x, ZERO);
      assert_eq!(aa >> 32, (a | (1 << 63)) >> 32);
      x = x.double();
    }
  }
}
