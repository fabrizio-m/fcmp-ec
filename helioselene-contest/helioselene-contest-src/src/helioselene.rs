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

  debug_assert!(bool::from(MODULUS.ct_gt(&elem)));
  elem
}

impl Add for Element {
  type Output = Self;

  fn add(mut self, rhs: Self) -> Self::Output {
    let carry = add_assing(&mut self.0, &rhs.0);
    correct_with_carry(self.0, carry)
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

/// (low,high)
#[inline(always)]
fn mul_wide(a: u64, b: u64) -> (u64, u64) {
  let ab = a as u128 * b as u128;
  split(ab)
}

/// (low,high)
/// a * b + c
#[inline(always)]
fn mul_wide_add(a: u64, b: u64, c: u64) -> (u64, u64) {
  let ab = a as u128 * b as u128 + c as u128;
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

impl Mul for Element {
  type Output = Self;

  fn mul(self, rhs: Self) -> Self::Output {
    let (a, b) = (self.0, rhs.0);
    let res = product_scanning_4x4(a, b);
    let [r0, r1, r2, r3, r4, r5, r6, r7] = res;
    let res_low = [r0, r1, r2, r3];
    let res_high = [r4, r5, r6, r7];

    let elem = reduce(res_high, res_low);
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
  fn inverse(self) -> Self {
    self.pow(MODULUS_FERMAT)
  }

  pub fn square(self) -> Self {
    let res = square_scanning_4x4(self.0);
    let [r0, r1, r2, r3, r4, r5, r6, r7] = res;
    let res_low = [r0, r1, r2, r3];
    let res_high = [r4, r5, r6, r7];

    let elem = reduce(res_high, res_low);
    debug_assert!(bool::from(MODULUS.ct_gt(&elem)));
    elem
  }
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
    CtOption::new(self.inverse(), !is_zero)
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
    let inv = x.inverse();
    assert_eq!(x * inv, ONE);
    assert_eq!(inv.inverse(), x);
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

#[test]
fn bench_mul() {
  for i in 0..10000 {
    let x = Element([124124, i, 214214, i]);
    let _inv = x.inverse();
  }
}
