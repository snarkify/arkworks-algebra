use ark_std::{vec, vec::Vec};

/// adc with the option to accept a variable number of args.
/// carry is given as the first arg, followed by any number of inputs.
// NOTE(victor) Need to look at the assembly output for this since it was likely written
// specifically to ensure the compiler implements it with a particular instruction and I may have
// borked that.
macro_rules! adc {
    (&mut $carry:expr, $($x:expr),*) => {{
        let tmp = $(($x as u128) + )* ($carry as u128);
        $carry = (tmp >> 64) as u64;
        tmp as u64
    }};
}

/// Calculate a + b + carry, returning the sum and modifying the
/// carry value.
#[inline(always)]
pub(crate) fn adc(a: u64, b: u64, carry: &mut u64) -> u64 {
    let tmp = a as u128 + b as u128 + *carry as u128;
    *carry = (tmp >> 64) as u64;
    tmp as u64
}

/// Calculate a + b + carry, returning the sum
#[inline(always)]
pub(crate) fn adc_no_carry(a: u64, b: u64, carry: &mut u64) -> u64 {
    let tmp = a as u128 + b as u128 + *carry as u128;
    tmp as u64
}

/// Calculate a + b returning the 64-bit word result and a boolean carry.
/// Alternative implementation of add with the intention that it be more friendly to WASM.
/// In particular, this function does not use any u128 values.
#[inline(always)]
pub(crate) fn add_alt(a: u64, b: u64) -> (bool, u64) {
    let tmp = a.wrapping_add(b);
    (tmp < a, tmp)
}

/// Calculate a + b + carry with the requirement that carry be a boolean.
/// Alternative implementation of add with the intention that it be more friendly to WASM.
/// In particular, this function does not use any u128 values.
#[inline(always)]
pub(crate) fn add_with_carry_alt(a: u64, b: u64, carry: bool) -> (bool, u64) {
    let tmp = a.wrapping_add(b);
    (tmp < a, tmp + (carry as u64))
}

#[macro_export]
macro_rules! sbb {
    ($a:expr, $b:expr, &mut $borrow:expr$(,)?) => {{
        let tmp = (1u128 << 64) + ($a as u128) - ($b as u128) - ($borrow as u128);
        $borrow = if tmp >> 64 == 0 { 1 } else { 0 };
        tmp as u64
    }};
}

/// Calculate a - b - borrow, returning the result and modifying
/// the borrow value.
#[inline(always)]
pub(crate) fn sbb(a: u64, b: u64, borrow: &mut u64) -> u64 {
    sbb!(a, b, &mut *borrow)
}

/// Calculate a + b * c, returning the lower 64 bits of the result and setting
/// `carry` to the upper 64 bits.
#[inline(always)]
pub(crate) fn mac(a: u64, b: u64, c: u64, carry: &mut u64) -> u64 {
    let tmp = (a as u128) + (b as u128 * c as u128);
    *carry = (tmp >> 64) as u64;
    tmp as u64
}

/// Calculate a + b * c, discarding the lower 64 bits of the result and setting
/// `carry` to the upper 64 bits.
#[inline(always)]
pub(crate) fn mac_discard(a: u64, b: u64, c: u64, carry: &mut u64) {
    let tmp = (a as u128) + (b as u128 * c as u128);
    *carry = (tmp >> 64) as u64;
}

macro_rules! mac_with_carry {
    ($a:expr, $b:expr, $c:expr, &mut $carry:expr$(,)?) => {{
        let tmp = ($a as u128) + ($b as u128 * $c as u128) + ($carry as u128);
        $carry = (tmp >> 64) as u64;
        tmp as u64
    }};
}

macro_rules! mac {
    ($a:expr, $b:expr, $c:expr, &mut $carry:expr$(,)?) => {{
        let tmp = ($a as u128) + ($b as u128 * $c as u128);
        $carry = (tmp >> 64) as u64;
        tmp as u64
    }};
}

/// Calculate a + (b * c) + carry, returning the least significant digit
/// and setting carry to the most significant digit.
#[inline(always)]
pub(crate) fn mac_with_carry(a: u64, b: u64, c: u64, carry: &mut u64) -> u64 {
    let tmp = (a as u128) + (b as u128 * c as u128) + (*carry as u128);
    *carry = (tmp >> 64) as u64;
    tmp as u64
}

/// Calculate a + b * c returning the two 64-bit word result as (upper, lower).
/// Alternative implementation of mac with the intention that it be more friendly to WASM.
/// In particular, this function does not use any u128 values.
#[inline(always)]
pub(crate) fn mac_alt(a: u64, b: u64, c: u64) -> (u64, u64) {
    // Split the input product values into two 32-bit values.
    let (b1, b0) = (b >> 32, c & 0xFFFFFFFF);
    let (c1, c0) = (b >> 32, c & 0xFFFFFFFF);

    // Compute the 4 32-bit multiplications with 64-bit results.
    let b0c0 = b0 * c0;
    let b1c0 = b1 * c0;
    let b0c1 = b0 * c1;
    let b1c1 = b1 * c1;

    // Sum the multiplication results into their respective 64-bit result words.
    // Results in (p1, p0), the 128-bit result of b*c.
    let (mid_carry, mid) = add_alt(b1c0, b0c1);
    let (p0_carry, p0) = add_alt((mid & 0xFFFFFFFF) << 32, b0c0);
    let p1 = b1c1 + (mid >> 32) + (((mid_carry as u64) << 32) | (p0_carry as u64));

    // Add a into (p1, p0) and return the result.
    let (mac0_carry, mac0) = add_alt(p0, c);
    (p1 + p0_carry as u64, mac0)
}

/// Calculate a + b * c + carry returning the two 64-bit word result as (upper, lower).
/// Alternative implementation of mac_with_carry with the intention that it be more friendly to
/// WASM.  In particular, this function does not use any u128 values.
#[inline(always)]
pub(crate) fn mac_with_carry_alt(a: u64, b: u64, c: u64, carry: u64) -> (u64, u64) {
    let (mac1, mac0) = mac_alt(a, b, c);

    // Add carry into (mac1, mac0) and return.
    let (carry, r0) = add_alt(mac0, carry);
    (mac1 + carry as u64, r0)
}

/// Calculate a + b * c returning the upper 64-bit word result.
/// Alternative implementation of mac_discard with the intention that it be more friendly to WASM.
/// In particular, this function does not use any u128 values.
#[inline(always)]
pub(crate) fn mac_discard_alt(a: u64, b: u64, c: u64) -> u64 {
    // TODO(victor): Can this be improved? Probably.
    let (mac1, _) = mac_alt(a, b, c);
    mac1
}

/// Compute the NAF (non-adjacent form) of num
pub fn find_naf(num: &[u64]) -> Vec<i8> {
    let is_zero = |num: &[u64]| num.iter().all(|x| *x == 0u64);
    let is_odd = |num: &[u64]| num[0] & 1 == 1;
    let sub_noborrow = |num: &mut [u64], z: u64| {
        let mut other = vec![0u64; num.len()];
        other[0] = z;
        let mut borrow = 0;

        for (a, b) in num.iter_mut().zip(other) {
            *a = sbb(*a, b, &mut borrow);
        }
    };
    let add_nocarry = |num: &mut [u64], z: u64| {
        let mut other = vec![0u64; num.len()];
        other[0] = z;
        let mut carry = 0;

        for (a, b) in num.iter_mut().zip(other) {
            *a = adc(*a, b, &mut carry);
        }
    };
    let div2 = |num: &mut [u64]| {
        let mut t = 0;
        for i in num.iter_mut().rev() {
            let t2 = *i << 63;
            *i >>= 1;
            *i |= t;
            t = t2;
        }
    };

    let mut num = num.to_vec();
    let mut res = vec![];

    while !is_zero(&num) {
        let z: i8;
        if is_odd(&num) {
            z = 2 - (num[0] % 4) as i8;
            if z >= 0 {
                sub_noborrow(&mut num, z as u64)
            } else {
                add_nocarry(&mut num, (-z) as u64)
            }
        } else {
            z = 0;
        }
        res.push(z);
        div2(&mut num);
    }

    res
}

/// We define relaxed NAF as a variant of NAF with a very small tweak.
///
/// Note that the cost of scalar multiplication grows with the length of the sequence (for doubling)
/// plus the Hamming weight of the sequence (for addition, or subtraction).
///
/// NAF is optimizing for the Hamming weight only and therefore can be suboptimal.
/// For example, NAF may generate a sequence (in little-endian) of the form ...0 -1 0 1.
///
/// This can be rewritten as ...0 1 1 to avoid one doubling, at the cost that we are making an
/// exception of non-adjacence for the most significant bit.
///
/// Since this representation is no longer a strict NAF, we call it "relaxed NAF".
///
pub fn find_relaxed_naf(num: &[u64]) -> Vec<i8> {
    let mut res = find_naf(num);

    let len = res.len();
    if res[len - 2] == 0 && res[len - 3] == -1 {
        res[len - 3] = 1;
        res[len - 2] = 1;
        res.resize(len - 1, 0);
    }

    res
}

#[test]
fn test_find_relaxed_naf_usefulness() {
    let vec = find_naf(&[12u64]);
    assert_eq!(vec.len(), 5);

    let vec = find_relaxed_naf(&[12u64]);
    assert_eq!(vec.len(), 4);
}

#[test]
fn test_find_relaxed_naf_correctness() {
    use ark_std::{One, UniformRand, Zero};
    use num_bigint::BigInt;

    let mut rng = ark_std::test_rng();

    for _ in 0..10 {
        let num = [
            u64::rand(&mut rng),
            u64::rand(&mut rng),
            u64::rand(&mut rng),
            u64::rand(&mut rng),
        ];
        let relaxed_naf = find_relaxed_naf(&num);

        let test = {
            let mut sum = BigInt::zero();
            let mut cur = BigInt::one();
            for v in relaxed_naf {
                sum += cur.clone() * v;
                cur *= 2;
            }
            sum
        };

        let test_expected = {
            let mut sum = BigInt::zero();
            let mut cur = BigInt::one();
            for v in num.iter() {
                sum += cur.clone() * v;
                cur <<= 64;
            }
            sum
        };

        assert_eq!(test, test_expected);
    }
}
