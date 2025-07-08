use core::ops::{Add, Mul, Neg, Sub};
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
    let gt3 = self.0[3].ct_gt(&other.0[3]);
    let gt2 = self.0[2].ct_gt(&other.0[2]);
    let gt1 = self.0[1].ct_gt(&other.0[1]);
    let gt0 = self.0[0].ct_gt(&other.0[0]);

    let eq3 = self.0[3].ct_eq(&other.0[3]);
    let eq2 = self.0[2].ct_eq(&other.0[1]);
    let eq1 = self.0[1].ct_eq(&other.0[2]);

    let c1 = gt3;
    let c2 = eq3 & gt2;
    let c3 = eq3 & eq2 & gt1;
    let c4 = eq3 & eq2 & eq1 & gt0;
    c1 | c2 | c3 | c4
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
  let mut correction = [0, 0];
  let carry = Choice::from(carry as u8);
  correction[0].conditional_assign(&C[0], carry);
  correction[1].conditional_assign(&C[1], carry);
  let carry = add_assing(&mut elem, &correction);
  debug_assert!(!carry);
  let mut elem = Element(elem);

  let correct = !MODULUS.ct_gt(&elem);
  let correction = Element::conditional_select(&ZERO, &MODULUS, correct);
  sub_assing(&mut elem.0, &correction.0);

  let correct = !MODULUS.ct_gt(&elem);
  let correction = Element::conditional_select(&ZERO, &MODULUS, correct);
  sub_assing(&mut elem.0, &correction.0);

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

  fn sub(mut self, mut rhs: Self) -> Self::Output {
    let lhs_greater = self.ct_gt(&rhs);
    Self::conditional_swap(&mut self, &mut rhs, !lhs_greater);
    let borrow = sub_assing(&mut self.0, &rhs.0);
    debug_assert!(!borrow);
    debug_assert!(bool::from(MODULUS.ct_gt(&self)));
    self
  }
}

// (low, high)
fn split(x: u128) -> (u64, u64) {
  let low = x as u64;
  let high = (x >> 64) as u64;
  (low, high)
}

fn simple_mul<const N: usize>(mut a: [u64; N], b: u64) -> ([u64; N], u64) {
  let b = b as u128;
  let mut carry: u64 = 0;
  for i in 0..N {
    let wide = (a[i] as u128) * b;
    // considering that:
    // (2^64 - 1)(2^64 - 1) = 2^128 - 2*2^64 + 1
    // u64::MAX^2 fits in a u128 and there is space to
    // add 2 u64::MAX and a 1.
    let (low, high) = split(wide + carry as u128);
    a[i] = low;
    carry = high;
  }
  (a, carry)
}

// A should be >= 2, with lowest part being returned as [_;A], and highest as [_;2]
// (low, high)
fn mul2<const N: usize>(a: [u64; N], b: [u64; 2]) -> ([u64; N], [u64; 2]) {
  let [b0, b1] = b;
  let (mut res_low, carry1) = simple_mul(a, b0);
  let (mut partial, carry2) = simple_mul(a, b1);
  let mut res_high = {
    let (h0, c) = carry1.overflowing_add(partial[N - 1]);
    let h1 = carry2 + c as u64;
    [h0, h1]
  };
  for i in 0..(N - 1) {
    partial[N - i - 1] = partial[N - i - 1 - 1];
  }
  partial[0] = 0;
  let c = add_assing(&mut res_low, &partial);
  res_high[0] += c as u64;
  (res_low, res_high)
}

/// Crandall reduction
fn reduce(high: [u64; 4], mut low: [u64; 4]) -> Element {
  let (xc_low, mut xc_high) = mul2(high, C);
  let carry = add_assing(&mut low, &xc_low);
  // no overflow risk as xc_high has space for u64::MAX + 1;
  xc_high[0] += if carry { 1 } else { 0 };
  let (xc_low, xc_high) = mul2(xc_high, C);
  let xc = [xc_low[0], xc_low[1], xc_high[0], xc_high[1]];
  let carry = add_assing(&mut low, &xc);
  let elem = correct_with_carry(low, carry);
  debug_assert!(bool::from(MODULUS.ct_gt(&elem)));
  elem
}

impl Mul for Element {
  type Output = Self;

  fn mul(self, rhs: Self) -> Self::Output {
    let (a, b) = (self.0, rhs.0);
    let mut res_low;
    let mut res_high = [0, 0, 0, 0];
    let mut half_carry = 0;
    {
      let (partial, partial_carry) = simple_mul(a, b[0]);
      res_low = partial;
      let high = [partial_carry, 0, 0, 0];
      let c = add_assing(&mut res_high, &high);
      debug_assert!(!c);
    };
    {
      let (partial, partial_carry) = simple_mul(a, b[1]);
      let low = [0, partial[0], partial[1], partial[2]];
      let carry = add_assing(&mut res_low, &low) as u8;
      half_carry += carry as u8;
      let high = [partial[3], partial_carry, 0, 0];
      let c = add_assing(&mut res_high, &high);
      //
      debug_assert!(!c);
    };
    {
      let (partial, partial_carry) = simple_mul(a, b[2]);
      let low = [0, 0, partial[0], partial[1]];
      let carry = add_assing(&mut res_low, &low) as u8;
      half_carry += carry as u8;
      let high = [partial[2], partial[3], partial_carry, 0];
      let c = add_assing(&mut res_high, &high);
      debug_assert!(!c);
    };
    {
      let (partial, partial_carry) = simple_mul(a, b[3]);
      let low = [0, 0, 0, partial[0]];
      let carry = add_assing(&mut res_low, &low) as u8;
      half_carry += carry as u8;
      let high = [partial[1], partial[2], partial[3], partial_carry];
      let c = add_assing(&mut res_high, &high);
      debug_assert!(!c);
    };
    let c = add_assing(&mut res_high, &[half_carry as u64]);
    debug_assert!(!c);

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
      //TODO: implement square
      res = res * res;
      let bit = (exp & (MASK >> i)).count_ones();
      let choice = Choice::from(bit as u8);
      let mut to_multiply = ONE;
      to_multiply.conditional_assign(&self, choice);
      res = res * to_multiply;
    }
    res
  }

  fn pow(self, exp: Self) -> Self {
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

  //TODO: specialize
  pub fn square(self) -> Self {
    self * self
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
      word_bytes.clone_from_slice(&repr[i * 8..]);
      elem.0[i] = u64::from_le_bytes(word_bytes);
    }
    let valid = !MODULUS.ct_gt(&elem);
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
    todo!()
  }

  fn is_zero(&self) -> Choice {
    ZERO.ct_eq(self)
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

/*
mod tests {
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
