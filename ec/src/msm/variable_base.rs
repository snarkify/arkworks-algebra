use ark_ff::prelude::*;
use ark_std::vec::Vec;
use std::collections::HashMap;

use crate::{bls12::G1Projective, AffineCurve, ProjectiveCurve};

#[cfg(feature = "parallel")]
use rayon::prelude::*;
use crate::bn::G1Affine;

pub struct VariableBaseMSM;

impl VariableBaseMSM {
    fn sqrt(x: usize) -> usize {
        let mut z = (x + 1) / 2;
        let mut y = x;
        while z < y {
            y = z;
            z = (x / z + z) / 2;
        }
        y
    }
    fn zfill(v: &Vec<bool>, l: usize) -> Vec<bool> {
        let mut w = v.clone();
        for _ in v.len()..l {
            w.push(false);
        }
        w
    }
    fn pre_calculate<G: AffineCurve>(
        a: &[usize],
        vs: &[G::Projective],
    ) -> HashMap<Vec<usize>, G::Projective> {
        let mut hm: HashMap<Vec<usize>, G::Projective> = HashMap::new();
        hm.insert(vec![], G::Projective::zero());
        a.iter().fold(vec![vec![]], |mut acc, idx| {
            let delta = acc.clone().into_iter().map(|mut prev| {
                let mut v: <G as AffineCurve>::Projective = hm.get(&prev).unwrap().clone();
                v += vs[*idx];
                prev.push(*idx);
                hm.insert(prev.clone(), v);
                prev
            });
            acc.extend(delta);
            acc
        });
        hm
    }
    pub fn multiexp_bin<G: AffineCurve>(
        gs: Vec<G::Projective>,
        es: Vec<Vec<bool>>,
    ) -> Vec<G::Projective> {
        let size = ark_std::cmp::min(gs.len(), es.len());
        let es = &es[..size];
        let gs = &gs[..size];
        let mut b = ark_std::log2(size - ark_std::log2(size) as usize) as usize;
        b = if b > 0 { b } else { 1 };
        // println!("hehe, size={}, gs.len={}, es.len={} es[0].len={}, b={}", size,
        // gs.len(), es.len(),es[0].len(), b);
        let buckets: Vec<Vec<usize>> = (0..size)
            .step_by(b)
            .into_iter()
            .map(|i| (i..ark_std::cmp::min(i + b, size)).collect())
            .collect();

        // store the pre calculated hashmap on each bucket
        let cache: Vec<HashMap<Vec<usize>, G::Projective>> = buckets
            .clone()
            .into_iter()
            .map(|bk| Self::pre_calculate::<G>(&bk, &gs))
            .collect();

        let Gs: Vec<_> = ark_std::cfg_into_iter!(0..es[0].len())
            .map(|k| {
                let res = buckets.clone().into_iter().zip(&cache).fold(
                    G::Projective::zero(),
                    |mut acc: G::Projective, (bk, vs)| {
                        let mut tmp: Vec<_> = Vec::new();
                        for idx in bk {
                            if es[idx][k] {
                                tmp.push(idx);
                            }
                        }
                        if tmp.len() > 0 {
                            acc += vs.get(&tmp).unwrap();
                        }
                        acc
                    },
                );
                res
            })
            .collect();
        Gs
    }
    pub fn multiexp_affine<G: AffineCurve>(
        gs: Vec<G::Projective>,
        es: Vec<Vec<bool>>,
    ) -> Vec<Vec<G>> {
        let size = ark_std::cmp::min(gs.len(), es.len());
        let es = &es[..size];
        let gs = &gs[..size];
        let mut b = ark_std::log2(size - ark_std::log2(size) as usize) as usize;
        b = if b > 0 { b } else { 1 };
        // println!("hehe, size={}, gs.len={}, es.len={} es[0].len={}, b={}", size,
        // gs.len(), es.len(),es[0].len(), b);
        let buckets: Vec<Vec<usize>> = (0..size)
            .step_by(b)
            .into_iter()
            .map(|i| (i..ark_std::cmp::min(i + b, size)).collect())
            .collect();

        // store the pre calculated hashmap on each bucket
        let cache: Vec<HashMap<Vec<usize>, G::Projective>> = buckets
            .clone()
            .into_iter()
            .map(|bk| Self::pre_calculate::<G>(&bk, &gs))
            .collect();

        let Gs: Vec<_> = ark_std::cfg_into_iter!(0..es[0].len())
            .map(|k| {
                let pts: Vec<_>= buckets.clone().into_iter().zip(&cache).map(
                    |(bk, vs)| {
                        let mut tmp: Vec<_> = Vec::new();
                        for idx in bk {
                            if es[idx][k] {
                                tmp.push(idx);
                            }
                        }
                        let res:G::Projective;
                            if tmp.len() > 0 {
                                res = *vs.get(&tmp).unwrap()
                            } else {
                                res = G::Projective::zero()
                            }
                        res
                    }).filter(|x|!x.is_zero()).map(|x|x.into_affine()).collect();
                pts
            }).collect();
        Gs
    }

    pub fn pippenger_batch_affine<G: AffineCurve>(
        bases: &[G],
        scalars: &[<G::ScalarField as PrimeField>::BigInt],
    ) -> (Vec<Vec<G>>,usize) {
        let mut size = ark_std::cmp::min(bases.len(), scalars.len());
        let scalars = &scalars[..size];
        let bases = &bases[..size];
        let scalars_and_bases: Vec<_> = scalars
            .iter()
            .zip(bases)
            .filter(|(s, _)| !s.is_zero())
            .collect();
        size = scalars_and_bases.len();
        let num_bits = <G::ScalarField as PrimeField>::Params::MODULUS_BITS as usize;
        let s = Self::sqrt(num_bits / size) + 1;
        let t = (num_bits as f64 / s as f64).ceil() as usize;

        let gs_bin: Vec<Vec<_>> = ark_std::cfg_into_iter!(scalars_and_bases.clone())
            .map(|(_, g)| {
                let mut g0 = G::Projective::zero();
                let mut v = Vec::new();
                g0.add_assign_mixed(g);
                v.push(g0);
                for _ in 1..s {
                    let tmp = v[v.len() - 1];
                    v.push(tmp.double());
                }
                v
            })
            .collect();
        let gs: Vec<_> = gs_bin.into_iter().flatten().collect();

        let es_bin: Vec<Vec<Vec<bool>>> = ark_std::cfg_into_iter!(scalars_and_bases)
            .map(|(scalar, _)| {
                let mut res: Vec<Vec<bool>> = Vec::new();
                for _ in 0..s {
                    let tmp = Vec::new();
                    res.push(tmp);
                }
                let vs = Self::zfill(&scalar.to_bits_le(), s * t);
                for i in 0..t {
                    for j in 0..s {
                        res[j].push(vs[i * s + j]);
                    }
                }
                res
            })
            .collect();
        let es: Vec<_> = es_bin.into_iter().flatten().collect();
        let Gs: Vec<_> = Self::multiexp_affine::<G>(gs, es);
        (Gs, s)
    }


    pub fn pippenger_mul<G: AffineCurve>(
        bases: &[G],
        scalars: &[<G::ScalarField as PrimeField>::BigInt],
    ) -> G::Projective {
        let mut size = ark_std::cmp::min(bases.len(), scalars.len());
        let scalars = &scalars[..size];
        let bases = &bases[..size];
        let scalars_and_bases: Vec<_> = scalars
            .iter()
            .zip(bases)
            .filter(|(s, _)| !s.is_zero())
            .collect();
        size = scalars_and_bases.len();
        let num_bits = <G::ScalarField as PrimeField>::Params::MODULUS_BITS as usize;
        let s = Self::sqrt(num_bits / size) + 1;
        let t = (num_bits as f64 / s as f64).ceil() as usize;

        let gs_bin: Vec<Vec<_>> = ark_std::cfg_into_iter!(scalars_and_bases.clone())
            .map(|(_, g)| {
                let mut g0 = G::Projective::zero();
                let mut v = Vec::new();
                g0.add_assign_mixed(g);
                v.push(g0);
                for _ in 1..s {
                    let tmp = v[v.len() - 1];
                    v.push(tmp.double());
                }
                v
            })
            .collect();
        let gs: Vec<_> = gs_bin.into_iter().flatten().collect();

        let es_bin: Vec<Vec<Vec<bool>>> = ark_std::cfg_into_iter!(scalars_and_bases)
            .map(|(scalar, _)| {
                let mut res: Vec<Vec<bool>> = Vec::new();
                for _ in 0..s {
                    let tmp = Vec::new();
                    res.push(tmp);
                }
                let vs = Self::zfill(&scalar.to_bits_le(), s * t);
                for i in 0..t {
                    for j in 0..s {
                        res[j].push(vs[i * s + j]);
                    }
                }
                res
            })
            .collect();
        let es: Vec<_> = es_bin.into_iter().flatten().collect();
        let Gs: Vec<_> = Self::multiexp_bin::<G>(gs, es);
        let lowest = *Gs.first().unwrap();
        // We're traversing windows from high to low.
        lowest
            + &Gs[1..]
                .iter()
                .rev()
                .fold(G::Projective::zero(), |mut total, sum_i| {
                    total += sum_i;
                    for _ in 0..s {
                        total.double_in_place();
                    }
                    total
                })
    }

    pub fn multi_scalar_mul<G: AffineCurve>(
        bases: &[G],
        scalars: &[<G::ScalarField as PrimeField>::BigInt],
    ) -> G::Projective {
        let size = ark_std::cmp::min(bases.len(), scalars.len());
        let scalars = &scalars[..size];
        let bases = &bases[..size];
        let scalars_and_bases_iter = scalars.iter().zip(bases).filter(|(s, _)| !s.is_zero());

        let c = if size < 32 {
            3
        } else {
            super::ln_without_floats(size) + 2
        };

        let num_bits = <G::ScalarField as PrimeField>::Params::MODULUS_BITS as usize;
        let fr_one = G::ScalarField::one().into_repr();

        let zero = G::Projective::zero();
        let window_starts: Vec<_> = (0..num_bits).step_by(c).collect();

        // chao: res=sum_{i=0}^{N-1} e_i*g_i=\sum_{w=0}^{t-1}(\sum_{i=0}^{N-1}
        // s_i*g_i)*2^{cw} where lambda: max bit length of field; c: window
        // size, t=lambda/c s_i = \sum_{j=0}^{c=1} e_{i,j+cw}*2^j is the scalar
        // value of window_id=w this is special case of short version of
        // pippenger note, where s = c, and after flatten, choose b = c.

        // Each window is of size `c`.
        // We divide up the bits 0..num_bits into windows of size `c`, and
        // in parallel process each such window.
        let window_sums: Vec<_> = ark_std::cfg_into_iter!(window_starts)
            .map(|w_start| {
                let mut res = zero;
                // We don't need the "zero" bucket, so we only have 2^c - 1 buckets.
                let mut buckets = vec![zero; (1 << c) - 1];
                // This clone is cheap, because the iterator contains just a
                // pointer and an index into the original vectors.
                scalars_and_bases_iter.clone().for_each(|(&scalar, base)| {
                    if scalar == fr_one {
                        // We only process unit scalars once in the first window.
                        if w_start == 0 {
                            res.add_assign_mixed(base);
                        }
                    } else {
                        let mut scalar = scalar;

                        // We right-shift by w_start, thus getting rid of the
                        // lower bits.
                        scalar.divn(w_start as u32);

                        // We mod the remaining bits by 2^{window size}, thus taking `c` bits.
                        // notice that c < 64
                        let scalar = scalar.as_ref()[0] % (1 << c);

                        // If the scalar is non-zero, we update the corresponding
                        // bucket.
                        // (Recall that `buckets` doesn't have a zero bucket.)
                        if scalar != 0 {
                            buckets[(scalar - 1) as usize].add_assign_mixed(base);
                        }
                    }
                });

                // Compute sum_{i in 0..num_buckets} (sum_{j in i..num_buckets} bucket[j])
                // This is computed below for b buckets, using 2b curve additions.
                //
                // We could first normalize `buckets` and then use mixed-addition
                // here, but that's slower for the kinds of groups we care about
                // (Short Weierstrass curves and Twisted Edwards curves).
                // In the case of Short Weierstrass curves,
                // mixed addition saves ~4 field multiplications per addition.
                // However normalization (with the inversion batched) takes ~6
                // field multiplications per element,
                // hence batch normalization is a slowdown.

                // `running_sum` = sum_{j in i..num_buckets} bucket[j],
                // where we iterate backward from i = num_buckets to 0.
                let mut running_sum = G::Projective::zero();
                buckets.into_iter().rev().for_each(|b| {
                    running_sum += &b;
                    res += &running_sum; // chao: buckets[s] will be counted s
                                         // times. thus give us s*g results.
                });
                res
            })
            .collect();
        // We store the sum for the lowest window.
        let lowest = *window_sums.first().unwrap();

        // We're traversing windows from high to low.
        lowest
            + &window_sums[1..]
                .iter()
                .rev()
                .fold(zero, |mut total, sum_i| {
                    total += sum_i;
                    for _ in 0..c {
                        total.double_in_place();
                    }
                    total
                })
    }
}
