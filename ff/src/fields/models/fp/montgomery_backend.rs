use ark_std::{marker::PhantomData, Zero};

use super::{Fp, FpConfig};
use crate::{biginteger::arithmetic as fa, BigInt, BigInteger, PrimeField, SqrtPrecomputation};
use ark_ff_macros::unroll_for_loops;

/// A trait that specifies the constants and arithmetic procedures
/// for Montgomery arithmetic over the prime field defined by `MODULUS`.
///
/// # Note
/// Manual implementation of this trait is not recommended unless one wishes
/// to specialize arithmetic methods. Instead, the
/// [`MontConfig`][`ark_ff_macros::MontConfig`] derive macro should be used.
pub trait MontConfig<const N: usize>: 'static + Sync + Send + Sized {
    /// The modulus of the field.
    const MODULUS: BigInt<N>;

    /// Let `M` be the power of 2^64 nearest to `Self::MODULUS_BITS`. Then
    /// `R = M % Self::MODULUS`.
    const R: BigInt<N> = Self::MODULUS.montgomery_r();

    /// R2 = R^2 % Self::MODULUS
    const R2: BigInt<N> = Self::MODULUS.montgomery_r2();

    /// INV = -MODULUS^{-1} mod 2^64
    const INV: u64 = inv(&Self::MODULUS);

    /// A multiplicative generator of the field.
    /// `Self::GENERATOR` is an element having multiplicative order
    /// `Self::MODULUS - 1`.
    const GENERATOR: Fp<MontBackend<Self, N>, N>;

    /// Can we use the no-carry optimization for multiplication and squaring
    /// outlined [here](https://hackmd.io/@gnark/modular_multiplication)?
    ///
    /// This optimization applies if the most significant word of
    /// `Self::MODULUS` has (a) a zero MSB, and (b) at least one
    /// zero bit in the rest of the word.
    #[doc(hidden)]
    const CAN_USE_NO_CARRY_OPT: bool = can_use_no_carry_optimization(&Self::MODULUS);

    /// Can we use the no-carry optimization for multiplication and squaring
    /// outlined [here](https://hackmd.io/@gnark/modular_multiplication)?
    ///
    /// This optimization applies if the most significant word of
    /// `Self::MODULUS` has (a) the two MSBs are zero, and (b) at least one
    /// zero bit in the rest of the word.
    #[doc(hidden)]
    const CAN_USE_SQUARE_NO_CARRY_OPT: bool = can_use_square_no_carry_optimization(&Self::MODULUS);

    /// Can we use partial-reduce optimization, where the value is maintained in a partially
    /// reduced form, in the range [0, 2*Self::MODULUS) such that reduction is not needed after a
    /// multiplication.
    #[doc(hidden)]
    #[cfg(feature = "partial-reduce")]
    const CAN_USE_PARTIAL_REDUCE_OPT: bool = can_use_partial_reduce_opt(&Self::MODULUS);

    /// Defines the bound of the result of a multiplication operation, and the maximum value before
    /// reduction is applied to the result of addition and subtraction operations.
    /// If the partial-reduce optimization is not applied, this is Self::MODULUS. If the
    /// partial-reduce optimization is applied, this is Self::MODULUS times two.
    #[doc(hidden)]
    #[cfg(feature = "partial-reduce")]
    const REDUCTION_BOUND: BigInt<N> = match Self::CAN_USE_PARTIAL_REDUCE_OPT {
        true => Self::MODULUS.const_mul2(),
        false => Self::MODULUS,
    };

    /// 2^s root of unity computed by GENERATOR^t
    const TWO_ADIC_ROOT_OF_UNITY: Fp<MontBackend<Self, N>, N>;

    /// An integer `b` such that there exists a multiplicative subgroup
    /// of size `b^k` for some integer `k`.
    const SMALL_SUBGROUP_BASE: Option<u32> = None;

    /// The integer `k` such that there exists a multiplicative subgroup
    /// of size `Self::SMALL_SUBGROUP_BASE^k`.
    const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = None;

    /// GENERATOR^((MODULUS-1) / (2^s *
    /// SMALL_SUBGROUP_BASE^SMALL_SUBGROUP_BASE_ADICITY)).
    /// Used for mixed-radix FFT.
    const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<Fp<MontBackend<Self, N>, N>> = None;

    /// Precomputed material for use when computing square roots.
    /// The default is to use the standard Tonelli-Shanks algorithm.
    const SQRT_PRECOMP: Option<SqrtPrecomputation<Fp<MontBackend<Self, N>, N>>> =
        sqrt_precomputation::<N, Self>();

    /// (MODULUS + 1) / 4 when MODULUS % 4 == 3. Used for square root precomputations.
    #[doc(hidden)]
    const MODULUS_PLUS_ONE_DIV_FOUR: Option<BigInt<N>> = {
        match Self::MODULUS.mod_4() == 3 {
            true => {
                let (modulus_plus_one, carry) =
                    Self::MODULUS.const_add_with_carry(&BigInt::<N>::one());
                let mut result = modulus_plus_one.divide_by_2_round_down();
                // Since modulus_plus_one is even, dividing by 2 results in a MSB of 0.
                // Thus we can set MSB to `carry` to get the correct result of (MODULUS + 1) // 2:
                result.0[N - 1] |= (carry as u64) << 63;
                Some(result.divide_by_2_round_down())
            },
            false => None,
        }
    };

    /// Set a += b;
    fn add_assign(a: &mut Fp<MontBackend<Self, N>, N>, b: &Fp<MontBackend<Self, N>, N>) {
        // This cannot exceed the backing capacity.
        a.0.add_with_carry(&b.0);
        // However, it may need to be reduced
        a.subtract_modulus();
    }

    fn sub_assign(a: &mut Fp<MontBackend<Self, N>, N>, b: &Fp<MontBackend<Self, N>, N>) {
        // If `other` is larger than `self`, add the modulus to self first.
        if b.0 > a.0 {
            #[cfg(not(feature = "partial-reduce"))]
            { a.0.add_with_carry(&Self::MODULUS) };

            #[cfg(feature = "partial-reduce")]
            { a.0.add_with_carry(&Self::REDUCTION_BOUND) };
        }
        a.0.sub_with_borrow(&b.0);
    }

    fn double_in_place(a: &mut Fp<MontBackend<Self, N>, N>) {
        // This cannot exceed the backing capacity.
        a.0.mul2();
        // However, it may need to be reduced.
        a.subtract_modulus();
    }

    /// This modular multiplication algorithm uses Montgomery
    /// reduction for efficient implementation. It also additionally
    /// uses the "no-carry optimization" outlined
    /// [here](https://hackmd.io/@zkteam/modular_multiplication) if
    /// `Self::MODULUS` has (a) a non-zero MSB, and (b) at least one
    /// zero bit in the rest of the modulus.
    #[inline]
    #[unroll_for_loops(12)]
    fn mul_assign(a: &mut Fp<MontBackend<Self, N>, N>, b: &Fp<MontBackend<Self, N>, N>) {
        // No-carry optimisation applied to CIOS
        if Self::CAN_USE_NO_CARRY_OPT {
            if N <= 6
                && N > 1
                && cfg!(all(
                    feature = "asm",
                    inline_asm_stable,
                    target_feature = "bmi2",
                    target_feature = "adx",
                    target_arch = "x86_64"
                ))
            {
                #[cfg(all(feature = "asm", inline_asm_stable, target_feature = "bmi2", target_feature = "adx", target_arch = "x86_64"))]
                #[allow(unsafe_code, unused_mut)]
                // Tentatively avoid using assembly for `N == 1`.
                #[rustfmt::skip]
                match N {
                    2 => { ark_ff_asm::x86_64_asm_mul!(2, (a.0).0, (b.0).0); },
                    3 => { ark_ff_asm::x86_64_asm_mul!(3, (a.0).0, (b.0).0); },
                    4 => { ark_ff_asm::x86_64_asm_mul!(4, (a.0).0, (b.0).0); },
                    5 => { ark_ff_asm::x86_64_asm_mul!(5, (a.0).0, (b.0).0); },
                    6 => { ark_ff_asm::x86_64_asm_mul!(6, (a.0).0, (b.0).0); },
                    _ => unsafe { ark_std::hint::unreachable_unchecked() },
                };
            } else {
                let mut r = [0u64; N];
                let mut carry1 = 0u64;
                let mut carry2 = 0u64;

                for i in 0..N {
                    r[0] = fa::mac(r[0], (a.0).0[0], (b.0).0[i], &mut carry1);
                    let k = r[0].wrapping_mul(Self::INV);
                    fa::mac_discard(r[0], k, Self::MODULUS.0[0], &mut carry2);
                    for j in 1..N {
                        r[j] = fa::mac_with_carry(r[j], (a.0).0[j], (b.0).0[i], &mut carry1);
                        r[j - 1] = fa::mac_with_carry(r[j], k, Self::MODULUS.0[j], &mut carry2);
                    }
                    r[N - 1] = carry1 + carry2;
                }
                (a.0).0 = r;
            }
        } else {
            // Alternative implementation
            *a = a.mul_without_reduce(b);
        }
        #[cfg(not(feature = "partial-reduce"))]
        { a.subtract_modulus() };

        #[cfg(feature = "partial-reduce")]
        if !Self::CAN_USE_PARTIAL_REDUCE_OPT {
            a.subtract_modulus();
        }
    }

    #[inline]
    #[unroll_for_loops(12)]
    fn square_in_place(a: &mut Fp<MontBackend<Self, N>, N>) {
        if N == 1 {
            // We default to multiplying with `a` using the `Mul` impl
            // for the N == 1 case
            let temp = *a;
            Self::mul_assign(a, &temp);
            return;
        }

        // If we can use the NO_CARRY optimization and we are on a plaform with an assembly
        // implementation, use the assembly implementation.
        #[cfg(all(
            feature = "asm",
            inline_asm_stable,
            target_feature = "bmi2",
            target_feature = "adx",
            target_arch = "x86_64"
        ))]
        #[allow(unsafe_code, unused_mut)]
        {
            // Checking the modulus at compile time
            if N <= 6 && Self::CAN_USE_SQUARE_NO_CARRY_OPT {
                #[rustfmt::skip]
                match N {
                    2 => { ark_ff_asm::x86_64_asm_square!(2, (a.0).0); },
                    3 => { ark_ff_asm::x86_64_asm_square!(3, (a.0).0); },
                    4 => { ark_ff_asm::x86_64_asm_square!(4, (a.0).0); },
                    5 => { ark_ff_asm::x86_64_asm_square!(5, (a.0).0); },
                    6 => { ark_ff_asm::x86_64_asm_square!(6, (a.0).0); },
                    _ => unsafe { ark_std::hint::unreachable_unchecked() },
                };
                #[cfg(not(feature = "partial-reduce"))]
                { a.subtract_modulus() };

                #[cfg(feature = "partial-reduce")]
                if !Self::CAN_USE_PARTIAL_REDUCE_OPT {
                    a.subtract_modulus();
                }
                return;
            }
        }

        // If we can use the NO_CARRY optimization (but don't have an assembly implementation), use
        // an implementation written in Rust.
        // TODO(victor): It appears that this condition is slightly wrong since NO_CARRY requires
        // R > 2N for multiplication, but R > 4N for squaring.
        // https://hackmd.io/@gnark/modular_multiplication#Montgomery-squaring
        #[cfg(feature = "square-no-carry")]
        if Self::CAN_USE_SQUARE_NO_CARRY_OPT {
            //unsafe { std::arch::asm!("# begin rust no-carry implementation"); }
            let mut carry1: u64 = 0;
            let mut carry2: u64 = 0;
            let mut r = [0u64; N];
            // Buffer with three location to store word-level multiplication results.
            // One is used on each iteration to carry forward the upper word result.
            let mut p = [0u64; 3];

            for i in 0..N - 1 {
                // C, r[i] = r[i] + a[i] * a[i]
                r[i] = fa::mac(r[i], (a.0).0[i], (a.0).0[i], &mut carry1);

                // Incremental squaring operations.
                // j=i+1 case for the loop below.
                let (p1, p0, p1_prev) = ((i + 1) % 3, (i + 2) % 3, i % 3);
                // p1, p0 = p1_prev + a[i] * a[j]
                p[p0] = fa::mac(0, (a.0).0[i], (a.0).0[i + 1], &mut p[p1]);
                // C, r[i] = r[j] + 2*p0 + C
                r[i + 1] = adc_var!(&mut carry1, r[i + 1], p[p0], p[p0]);

                for j in i + 2..N {
                    let (p1, p0, p1_prev) = (j % 3, (j + 1) % 3, (j + 2) % 3);
                    // p1, p0 = a[i] * a[j]
                    p[p0] = fa::mac(p[p1_prev], (a.0).0[i], (a.0).0[j], &mut p[p1]);
                    // C, r[i] = r[j] + 2*p0 + 2*p1_prev
                    r[j] = adc_var!(&mut carry1, r[j], p[p0], p[p0]);
                }

                // Incremental reduction.
                // k = r[0] * q'[0]
                let k = r[0].wrapping_mul(Self::INV);
                // C, _ = r[0] + q[0]*k
                fa::mac_discard(r[0], k, Self::MODULUS.0[0], &mut carry2);
                for j in 1..N {
                    // C, r[j-1] = q[j]*k + r[j] + C
                    r[j - 1] = fa::mac_with_carry(r[j], k, Self::MODULUS.0[j], &mut carry2);
                }

                // Final carry word will not overflow due to the NO_CARRY rule.
                r[N - 1] = p[(N + 2) % 3] + p[(N + 2) % 3] + carry1 + carry2;
            }

            // i=N-1 case for the loop above.
            // C, r[i] = r[i] + a[i] * a[i]
            r[N - 1] = fa::mac(r[N - 1], (a.0).0[N - 1], (a.0).0[N - 1], &mut carry1);
            // k = r[0] * q'[0]
            let k = r[0].wrapping_mul(Self::INV);
            // C, _ = r[0] + q[0]*k
            fa::mac_discard(r[0], k, Self::MODULUS.0[0], &mut carry2);
            for j in 1..N {
                // C, r[j-1] = q[j]*k + r[j] + C
                r[j - 1] = fa::mac_with_carry(r[j], k, Self::MODULUS.0[j], &mut carry2);
            }

            // Final carry word will not overflow due to the NO_CARRY rule.
            r[N - 1] = carry1 + carry2;

            (a.0).0 = r;
            #[cfg(not(feature = "partial-reduce"))]
            { a.subtract_modulus() };

            #[cfg(feature = "partial-reduce")]
            if !Self::CAN_USE_PARTIAL_REDUCE_OPT {
                a.subtract_modulus();
            }
            //unsafe { std::arch::asm!("# end rust no-carry implementation"); }
            return;
        }

        //unsafe { std::arch::asm!("# begin rust square baseline implementation"); }
        let mut r = crate::const_helpers::MulBuffer::<N>::zeroed();

        let mut carry = 0;
        for i in 0..(N - 1) {
            for j in (i + 1)..N {
                r[i + j] = fa::mac_with_carry(r[i + j], (a.0).0[i], (a.0).0[j], &mut carry);
            }
            r.b1[i] = carry;
            carry = 0;
        }
        r.b1[N - 1] >>= 63;
        for i in 0..N {
            r[2 * (N - 1) - i] = (r[2 * (N - 1) - i] << 1) | (r[2 * (N - 1) - (i + 1)] >> 63);
        }
        for i in 3..N {
            r[N + 1 - i] = (r[N + 1 - i] << 1) | (r[N - i] >> 63);
        }
        r.b0[1] <<= 1;

        for i in 0..N {
            r[2 * i] = fa::mac_with_carry(r[2 * i], (a.0).0[i], (a.0).0[i], &mut carry);
            r[2 * i + 1] = fa::adc(r[2 * i + 1], 0, &mut carry);
        }
        // Montgomery reduction
        let mut carry2 = 0;
        for i in 0..N {
            let k = r[i].wrapping_mul(Self::INV);
            let mut carry = 0;
            fa::mac_discard(r[i], k, Self::MODULUS.0[0], &mut carry);
            for j in 1..N {
                r[j + i] = fa::mac_with_carry(r[j + i], k, Self::MODULUS.0[j], &mut carry);
            }
            r.b1[i] = fa::adc(r.b1[i], carry, &mut carry2);
        }
        (a.0).0.copy_from_slice(&r.b1);
        #[cfg(not(feature = "partial-reduce"))]
        { a.subtract_modulus() };

        #[cfg(feature = "partial-reduce")]
        if !Self::CAN_USE_PARTIAL_REDUCE_OPT {
            a.subtract_modulus();
        }
    }

    fn inverse(a: &Fp<MontBackend<Self, N>, N>) -> Option<Fp<MontBackend<Self, N>, N>> {
        if a.is_zero() {
            None
        } else {
            // Guajardo Kumar Paar Pelzl
            // Efficient Software-Implementation of Finite Fields with Applications to
            // Cryptography
            // Algorithm 16 (BEA for Inversion in Fp)

            let one = BigInt::from(1u64);

            let mut u = a.0;
            let mut v = Self::MODULUS;
            let mut b = Fp::new_unchecked(Self::R2); // Avoids unnecessary reduction step.
            let mut c = Fp::zero();

            while u != one && v != one {
                while u.is_even() {
                    u.div2();

                    if b.0.is_even() {
                        b.0.div2();
                    } else {
                        b.0.add_with_carry(&Self::MODULUS);
                        b.0.div2();
                    }
                }

                while v.is_even() {
                    v.div2();

                    if c.0.is_even() {
                        c.0.div2();
                    } else {
                        c.0.add_with_carry(&Self::MODULUS);
                        c.0.div2();
                    }
                }

                if v < u {
                    u.sub_with_borrow(&v);
                    b -= &c;
                } else {
                    v.sub_with_borrow(&u);
                    c -= &b;
                }
            }

            if u == one {
                Some(b)
            } else {
                Some(c)
            }
        }
    }

    fn from_bigint(r: BigInt<N>) -> Option<Fp<MontBackend<Self, N>, N>> {
        let mut r = Fp::new_unchecked(r);
        if r.is_zero() {
            Some(r)
        } else if r.is_less_than_modulus() {
            r *= &Fp::new_unchecked(Self::R2);
            Some(r)
        } else {
            None
        }
    }

    #[inline]
    #[unroll_for_loops(12)]
    #[allow(clippy::modulo_one)]
    fn into_bigint(a: Fp<MontBackend<Self, N>, N>) -> BigInt<N> {
        let mut tmp = a.0;
        let mut r = tmp.0;
        // Montgomery Reduction
        for i in 0..N {
            let k = r[i].wrapping_mul(Self::INV);
            let mut carry = 0;

            fa::mac_with_carry(r[i], k, Self::MODULUS.0[0], &mut carry);
            for j in 1..N {
                r[(j + i) % N] =
                    fa::mac_with_carry(r[(j + i) % N], k, Self::MODULUS.0[j], &mut carry);
            }
            r[i % N] = carry;
        }
        tmp.0 = r;
        // TODO(victor): This reduction may not be needed.
        #[cfg(feature = "partial-reduce")]
        if Self::CAN_USE_PARTIAL_REDUCE_OPT && tmp >= Self::MODULUS {
            tmp.sub_with_borrow(&Self::MODULUS);
        }
        tmp
    }

    #[unroll_for_loops(12)]
    fn sum_of_products(
        a: &[Fp<MontBackend<Self, N>, N>],
        b: &[Fp<MontBackend<Self, N>, N>],
    ) -> Fp<MontBackend<Self, N>, N> {
        assert_eq!(a.len(), b.len());
        // Adapted from https://github.com/zkcrypto/bls12_381/pull/84 by @str4d.

        // For a single `a x b` multiplication, operand scanning (schoolbook) takes each
        // limb of `a` in turn, and multiplies it by all of the limbs of `b` to compute
        // the result as a double-width intermediate representation, which is then fully
        // reduced at the end. Here however we have pairs of multiplications (a_i, b_i),
        // the results of which are summed.
        //
        // The intuition for this algorithm is two-fold:
        // - We can interleave the operand scanning for each pair, by processing the jth
        //   limb of each `a_i` together. As these have the same offset within the overall
        //   operand scanning flow, their results can be summed directly.
        // - We can interleave the multiplication and reduction steps, resulting in a
        //   single bitshift by the limb size after each iteration. This means we only
        //   need to store a single extra limb overall, instead of keeping around all the
        //   intermediate results and eventually having twice as many limbs.

        let modulus_size = Self::MODULUS.const_num_bits() as usize;
        // FIXME(victor): This is currently broken
        if true /* modulus_size > 64 * N - 1 */ {
            a.iter().zip(b).map(|(a, b)| *a * b).sum()
        } else {
            let chunk_size = 2 * (N * 64 - modulus_size) - 1;
            // chunk_size is at least 1, since MODULUS_BIT_SIZE is at most N * 64 - 1.
            a.chunks(chunk_size)
                .zip(b.chunks(chunk_size))
                .map(|(a, b)| {
                    // Algorithm 2, line 2
                    let result = (0..N).fold(BigInt::zero(), |mut result, j| {
                        // Algorithm 2, line 3
                        let (temp, end) = a.iter().zip(b).fold(
                            (result, 0),
                            |(mut temp, mut end), (Fp(a, _), Fp(b, _))| {
                                let mut carry = 0;
                                temp.0[0] = fa::mac(temp.0[0], a.0[j], b.0[0], &mut carry);
                                for k in 1..N {
                                    temp.0[k] =
                                        fa::mac_with_carry(temp.0[k], a.0[j], b.0[k], &mut carry);
                                }
                                end = fa::adc_no_carry(end, 0, &mut carry);
                                (temp, end)
                            },
                        );

                        let k = temp.0[0].wrapping_mul(Self::INV);
                        let mut carry = 0;
                        fa::mac_discard(temp.0[0], k, Self::MODULUS.0[0], &mut carry);
                        for i in 1..N {
                            result.0[i - 1] =
                                fa::mac_with_carry(temp.0[i], k, Self::MODULUS.0[i], &mut carry);
                        }
                        result.0[N - 1] = fa::adc_no_carry(end, 0, &mut carry);
                        result
                    });
                    let mut result = Fp::new_unchecked(result);
                    // TODO(victor): Possibly could use the partial-reduce rule to exclude this line.
                    result.subtract_modulus();
                    debug_assert_eq!(
                        a.iter().zip(b).map(|(a, b)| *a * b).sum::<Fp<_, N>>(),
                        result
                    );
                    result
                })
                .sum()
        }
    }
}

/// Compute -M^{-1} mod 2^64.
pub const fn inv<const N: usize>(m: &BigInt<N>) -> u64 {
    let mut inv = 1u64;
    crate::const_for!((_i in 0..63) {
        inv = inv.wrapping_mul(inv);
        inv = inv.wrapping_mul(m.0[0]);
    });
    inv.wrapping_neg()
}

#[inline]
pub const fn can_use_no_carry_optimization<const N: usize>(modulus: &BigInt<N>) -> bool {
    // Checking the modulus at compile time
    let first_bit_set = modulus.0[N - 1] >> 63 != 0;
    // N can be 1, hence we can run into a case with an unused mut.
    let mut all_bits_set = modulus.0[N - 1] >= ((!0u64) >> 1);
    // TODO(victor): I think this is wrong, but I'll need to prove it. The gnark article says that
    // there needs to be another zero in the most signigicant words, not just in the whole modulus.
    crate::const_for!((i in 1..N) {
        all_bits_set &= modulus.0[N - i - 1] == !0u64;
    });
    !(first_bit_set || all_bits_set)
}

#[inline]
pub const fn can_use_square_no_carry_optimization<const N: usize>(modulus: &BigInt<N>) -> bool {
    // Checking the modulus at compile time
    let first_two_bit_set = modulus.0[N - 1] >> 62 != 0;
    // N can be 1, hence we can run into a case with an unused mut.
    let mut all_bits_set = modulus.0[N - 1] >= ((!0u64) >> 2);
    // TODO(victor): I think this is wrong, but I'll need to prove it. The gnark article says that
    // there needs to be another zero in the most signigicant words, not just in the whole modulus.
    crate::const_for!((i in 1..N) {
        all_bits_set &= modulus.0[N - i - 1] == !0u64;
    });
    !(first_two_bit_set || all_bits_set)
}

#[inline]
pub const fn can_use_partial_reduce_opt<const N: usize>(modulus: &BigInt<N>) -> bool {
    // Since the partial-reduce optimization results in larger stored values, fields with modulus
    // close to the total bit-width of the BigInt have to choose whether to utilize partial-reduce
    // or no-carry for multiplication and squaring. This rule prioritizes utilizing the no-carry
    // optimization.
    //
    // More generally the requirement is that M > 4 * Self::MODULUS, where M is the nearest larger
    // power of 2^64 to Self::MODULUS (i.e. The first two bits of the modulus are zero). This
    // requirement ensure that the intermediate multiplication result of two multiplication results
    // in the range [0, 2*Self.MODULUS) can have the Montgomery reduction applied to it correctly
    // to get a value in the same range.
    can_use_square_no_carry_optimization(&(*modulus).const_mul2())
}

pub const fn sqrt_precomputation<const N: usize, T: MontConfig<N>>(
) -> Option<SqrtPrecomputation<Fp<MontBackend<T, N>, N>>> {
    match T::MODULUS.mod_4() {
        3 => match T::MODULUS_PLUS_ONE_DIV_FOUR.as_ref() {
            Some(BigInt(modulus_plus_one_div_four)) => Some(SqrtPrecomputation::Case3Mod4 {
                modulus_plus_one_div_four,
            }),
            None => None,
        },
        _ => Some(SqrtPrecomputation::TonelliShanks {
            two_adicity: <MontBackend<T, N>>::TWO_ADICITY,
            quadratic_nonresidue_to_trace: T::TWO_ADIC_ROOT_OF_UNITY,
            trace_of_modulus_minus_one_div_two:
                &<Fp<MontBackend<T, N>, N>>::TRACE_MINUS_ONE_DIV_TWO.0,
        }),
    }
}

/// Construct a [`Fp<MontBackend<T, N>, N>`] element from a literal string. This
/// should be used primarily for constructing constant field elements; in a
/// non-const context, [`Fp::from_str`](`ark_std::str::FromStr::from_str`) is
/// preferable.
///
/// # Panics
///
/// If the integer represented by the string cannot fit in the number
/// of limbs of the `Fp`, this macro results in a
/// * compile-time error if used in a const context
/// * run-time error otherwise.
///
/// # Usage
///
/// ```rust
/// # use ark_test_curves::{MontFp, One};
/// # use ark_test_curves::bls12_381 as ark_bls12_381;
/// # use ark_std::str::FromStr;
/// use ark_bls12_381::Fq;
/// const ONE: Fq = MontFp!("1");
/// const NEG_ONE: Fq = MontFp!("-1");
///
/// fn check_correctness() {
///     assert_eq!(ONE, Fq::one());
///     assert_eq!(Fq::from_str("1").unwrap(), ONE);
///     assert_eq!(NEG_ONE, -Fq::one());
/// }
/// ```
#[macro_export]
macro_rules! MontFp {
    ($c0:expr) => {{
        let (is_positive, limbs) = $crate::ark_ff_macros::to_sign_and_limbs!($c0);
        $crate::Fp::from_sign_and_limbs(is_positive, &limbs)
    }};
}

pub use ark_ff_macros::MontConfig;

pub use MontFp;

pub struct MontBackend<T: MontConfig<N>, const N: usize>(PhantomData<T>);

impl<T: MontConfig<N>, const N: usize> FpConfig<N> for MontBackend<T, N> {
    /// The modulus of the field.
    const MODULUS: crate::BigInt<N> = T::MODULUS;

    /// A multiplicative generator of the field.
    /// `Self::GENERATOR` is an element having multiplicative order
    /// `Self::MODULUS - 1`.
    const GENERATOR: Fp<Self, N> = T::GENERATOR;

    #[cfg(feature = "partial-reduce")]
    const REDUCTION_BOUND: crate::BigInt<N> = T::REDUCTION_BOUND;

    /// Additive identity of the field, i.e. the element `e`
    /// such that, for all elements `f` of the field, `e + f = f`.
    const ZERO: Fp<Self, N> = Fp::new_unchecked(BigInt([0u64; N]));

    /// Multiplicative identity of the field, i.e. the element `e`
    /// such that, for all elements `f` of the field, `e * f = f`.
    const ONE: Fp<Self, N> = Fp::new_unchecked(T::R);

    const TWO_ADICITY: u32 = Self::MODULUS.two_adic_valuation();
    const TWO_ADIC_ROOT_OF_UNITY: Fp<Self, N> = T::TWO_ADIC_ROOT_OF_UNITY;
    const SMALL_SUBGROUP_BASE: Option<u32> = T::SMALL_SUBGROUP_BASE;
    const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = T::SMALL_SUBGROUP_BASE_ADICITY;
    const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<Fp<Self, N>> = T::LARGE_SUBGROUP_ROOT_OF_UNITY;
    const SQRT_PRECOMP: Option<crate::SqrtPrecomputation<Fp<Self, N>>> = T::SQRT_PRECOMP;

    fn add_assign(a: &mut Fp<Self, N>, b: &Fp<Self, N>) {
        T::add_assign(a, b)
    }

    fn sub_assign(a: &mut Fp<Self, N>, b: &Fp<Self, N>) {
        T::sub_assign(a, b)
    }

    fn double_in_place(a: &mut Fp<Self, N>) {
        T::double_in_place(a)
    }

    /// This modular multiplication algorithm uses Montgomery
    /// reduction for efficient implementation. It also additionally
    /// uses the "no-carry optimization" outlined
    /// [here](https://hackmd.io/@gnark/modular_multiplication) if
    /// `P::MODULUS` has (a) a non-zero MSB, and (b) at least one
    /// zero bit in the rest of the modulus.
    #[inline]
    fn mul_assign(a: &mut Fp<Self, N>, b: &Fp<Self, N>) {
        T::mul_assign(a, b)
    }

    fn sum_of_products(a: &[Fp<Self, N>], b: &[Fp<Self, N>]) -> Fp<Self, N> {
        T::sum_of_products(a, b)
    }

    #[inline]
    #[allow(unused_braces, clippy::absurd_extreme_comparisons)]
    fn square_in_place(a: &mut Fp<Self, N>) {
        T::square_in_place(a)
    }

    fn inverse(a: &Fp<Self, N>) -> Option<Fp<Self, N>> {
        T::inverse(a)
    }

    fn from_bigint(r: BigInt<N>) -> Option<Fp<Self, N>> {
        T::from_bigint(r)
    }

    #[inline]
    #[allow(clippy::modulo_one)]
    fn into_bigint(a: Fp<Self, N>) -> BigInt<N> {
        T::into_bigint(a)
    }
}

impl<T: MontConfig<N>, const N: usize> Fp<MontBackend<T, N>, N> {
    #[doc(hidden)]
    pub const R2: BigInt<N> = T::R2;
    #[doc(hidden)]
    pub const INV: u64 = T::INV;

    /// Construct a new field element from its underlying
    /// [`struct@BigInt`] data type.
    #[inline]
    pub const fn new(element: BigInt<N>) -> Self {
        let mut r = Self(element, PhantomData);
        if r.const_is_zero() {
            r
        } else {
            r = r.mul(&Fp(T::R2, PhantomData));
            r
        }
    }

    /// Construct a new field element from its underlying
    /// [`struct@BigInt`] data type.
    ///
    /// Unlike [`Self::new`], this method does not perform Montgomery reduction.
    /// Thus, this method should be used only when constructing
    /// an element from an integer that has already been put in
    /// Montgomery form.
    #[inline]
    pub const fn new_unchecked(element: BigInt<N>) -> Self {
        Self(element, PhantomData)
    }

    const fn const_is_zero(&self) -> bool {
        self.0.const_is_zero()
    }

    #[doc(hidden)]
    const fn const_neg(self) -> Self {
        if !self.const_is_zero() {
            #[cfg(not(feature = "partial-reduce"))]
            { Self::new_unchecked(Self::sub_with_borrow(&T::MODULUS, &self.0)) }

            #[cfg(feature = "partial-reduce")]
            { Self::new_unchecked(Self::sub_with_borrow(&T::REDUCTION_BOUND, &self.0)) }
        } else {
            self
        }
    }

    /// Interpret a set of limbs (along with a sign) as a field element.
    /// For *internal* use only; please use the `ark_ff::MontFp` macro instead
    /// of this method
    #[doc(hidden)]
    pub const fn from_sign_and_limbs(is_positive: bool, limbs: &[u64]) -> Self {
        let mut repr = BigInt::<N>([0; N]);
        assert!(limbs.len() <= N);
        crate::const_for!((i in 0..(limbs.len())) {
            repr.0[i] = limbs[i];
        });
        let res = Self::new(repr);
        if is_positive {
            res
        } else {
            res.const_neg()
        }
    }

    const fn mul_without_reduce(mut self, other: &Self) -> Self {
        let (mut lo, mut hi) = ([0u64; N], [0u64; N]);
        crate::const_for!((i in 0..N) {
            let mut carry = 0;
            crate::const_for!((j in 0..N) {
                let k = i + j;
                if k >= N {
                    hi[k - N] = mac_with_carry!(hi[k - N], (self.0).0[i], (other.0).0[j], &mut carry);
                } else {
                    lo[k] = mac_with_carry!(lo[k], (self.0).0[i], (other.0).0[j], &mut carry);
                }
            });
            hi[i] = carry;
        });
        // Montgomery reduction
        let mut carry2 = 0;
        crate::const_for!((i in 0..N) {
            let tmp = lo[i].wrapping_mul(T::INV);
            let mut carry;
            mac!(lo[i], tmp, T::MODULUS.0[0], &mut carry);
            crate::const_for!((j in 1..N) {
                let k = i + j;
                if k >= N {
                    hi[k - N] = mac_with_carry!(hi[k - N], tmp, T::MODULUS.0[j], &mut carry);
                }  else {
                    lo[k] = mac_with_carry!(lo[k], tmp, T::MODULUS.0[j], &mut carry);
                }
            });
            hi[i] = adc!(hi[i], carry, &mut carry2);
        });

        crate::const_for!((i in 0..N) {
            (self.0).0[i] = hi[i];
        });
        self
    }

    const fn mul(mut self, other: &Self) -> Self {
        self = self.mul_without_reduce(other);
        #[cfg(not(feature = "partial-reduce"))]
        { self.const_reduce() }

        #[cfg(feature = "partial-reduce")]
        if T::CAN_USE_PARTIAL_REDUCE_OPT {
            self
        } else {
            self.const_reduce()
        }
    }

    const fn const_is_valid(&self) -> bool {
        crate::const_for!((i in 0..N) {
            if (self.0).0[(N - i - 1)] < T::MODULUS.0[(N - i - 1)] {
                return true
            } else if (self.0).0[(N - i - 1)] > T::MODULUS.0[(N - i - 1)] {
                return false
            }
        });
        false
    }

    #[cfg(feature = "partial-reduce")]
    const fn const_is_less_than_reduction_bound(&self) -> bool {
        crate::const_for!((i in 0..N) {
            if (self.0).0[(N - i - 1)] < T::REDUCTION_BOUND.0[(N - i - 1)] {
                return true
            } else if (self.0).0[(N - i - 1)] > T::REDUCTION_BOUND.0[(N - i - 1)] {
                return false
            }
        });
        false
    }

    #[inline]
    const fn const_reduce(mut self) -> Self {
        #[cfg(not(feature = "partial-reduce"))]
        if !self.const_is_valid() {
            self.0 = Self::sub_with_borrow(&self.0, &T::MODULUS);
        }

        #[cfg(feature = "partial-reduce")]
        if !self.const_is_less_than_reduction_bound() {
            self.0 = Self::sub_with_borrow(&self.0, &T::REDUCTION_BOUND);
        }

        self
    }

    const fn sub_with_borrow(a: &BigInt<N>, b: &BigInt<N>) -> BigInt<N> {
        a.const_sub_with_borrow(b).0
    }
}
