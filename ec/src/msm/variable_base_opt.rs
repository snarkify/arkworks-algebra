//use crate::{ark_std::string::ToString, msm::stop_measure};
use ark_ff::prelude::*;
use ark_std::vec::Vec;

use crate::{AffineCurve, ProjectiveCurve};

fn num_bits(value: usize) -> usize {
    (0usize.leading_zeros() - value.leading_zeros()) as usize
}

fn div_up(a: usize, b: usize) -> usize {
    (a + (b - 1)) / b
}

fn get_wnaf_size_bits(num_bits: usize, w: usize) -> usize {
    div_up(num_bits, w)
}

fn get_wnaf_size<C: AffineCurve>(w: usize) -> usize {
    let lambda = <C::ScalarField as PrimeField>::MODULUS_BIT_SIZE;
    get_wnaf_size_bits(lambda as usize, w)
}

fn get_num_rounds<C: AffineCurve>(c: usize) -> usize {
    get_wnaf_size::<C>(c + 1)
}

fn get_num_buckets(c: usize) -> usize {
    (1 << c) + 1
}

fn get_max_tree_size(num_points: usize, c: usize) -> usize {
    num_points * 2 + get_num_buckets(c)
}

fn get_num_tree_levels(num_points: usize) -> usize {
    1 + num_bits(num_points - 1)
}

/// Returns the signed digit representation of value with the specified window
/// size. The result is written to the wnaf slice with the specified stride.
fn get_wnaf<C: AffineCurve>(
    value: &<C::ScalarField as PrimeField>::BigInt,
    w: usize,
    num_rounds: usize,
    wnaf: &mut [u32],
    stride: usize,
) {
    assert!(w >= 2);
    assert!(w < 64);
    fn get_bits_at<C: AffineCurve>(
        v: &<C::ScalarField as PrimeField>::BigInt,
        pos: usize,
        num: usize,
    ) -> usize {
        let mut v = v.clone();
        v.divn(pos as u32);
        v.as_ref()[0] as usize % (1 << num) as usize
    }

    let mut borrow = 0;
    let max = 1 << (w - 1);
    for idx in 0..num_rounds {
        let b = get_bits_at::<C>(&value, idx * w, w) + borrow;
        if b >= max {
            // Set the highest bit to 1 to represent a negative value.
            // This way the lower bits directly represent the bucket index.
            wnaf[idx * stride] = (0x80000000 | ((1 << w) - b)) as u32;
            borrow = 1;
        } else {
            wnaf[idx * stride] = b as u32;
            borrow = 0;
        }
    }
    assert_eq!(borrow, 0);
}

/// Returns the best bucket width for the given number of points.
fn get_best_c(num_points: usize) -> usize {
    if num_points >= 262144 {
        15
    } else if num_points >= 65536 {
        12
    } else if num_points >= 16384 {
        11
    } else if num_points >= 8192 {
        10
    } else if num_points >= 1024 {
        9
    } else {
        7
    }
}

/// MultiExp
#[derive(Clone, Debug, Default)]
pub struct MultiExp<C: AffineCurve> {
    /// The bases
    bases: Vec<C>,
}

/// MultiExp context object
#[derive(Clone, Debug, Default)]
pub struct MultiExpContext<C: AffineCurve> {
    /// Memory to store the points in the addition tree
    points: Vec<C>,
    /// Memory to store wnafs
    wnafs: Vec<u32>,
    /// Memory split up between rounds
    rounds: SharedRoundData,
}

/// SharedRoundData
#[derive(Clone, Debug, Default)]
struct SharedRoundData {
    /// Memory to store bucket sizes
    bucket_sizes: Vec<usize>,
    /// Memory to store bucket offsets
    bucket_offsets: Vec<usize>,
    /// Memory to store the point data
    point_data: Vec<u32>,
    /// Memory to store the output indices
    output_indices: Vec<u32>,
    /// Memory to store the base positions (on the first level)
    base_positions: Vec<u32>,
    /// Memory to store the scatter maps
    scatter_map: Vec<ScatterData>,
}

/// RoundData
#[derive(Debug, Default)]
struct RoundData<'a> {
    /// Number of levels in the addition tree
    pub num_levels: usize,
    /// The length of each level in the addition tree
    pub level_sizes: Vec<usize>,
    /// The offset to each level in the addition tree
    pub level_offset: Vec<usize>,
    /// The size of each bucket
    pub bucket_sizes: &'a mut [usize],
    /// The offset of each bucket
    pub bucket_offsets: &'a mut [usize],
    /// The point to use for each coefficient
    pub point_data: &'a mut [u32],
    /// The output index in the point array for each pair addition
    pub output_indices: &'a mut [u32],
    /// The point to use on the first level in the addition tree
    pub base_positions: &'a mut [u32],
    /// List of points that are scattered to the addition tree
    pub scatter_map: &'a mut [ScatterData],
    /// The length of scatter_map
    pub scatter_map_len: usize,
}

/// ScatterData
#[derive(Default, Debug, Clone)]
struct ScatterData {
    /// The position in the addition tree to store the point
    pub position: u32,
    /// The point to write
    pub point_data: u32,
}

impl<C: AffineCurve> MultiExp<C> {
    /// Performs a multi-exponentiation operation.
    /// Set complete to true if the bases are not guaranteed linearly
    /// independent.

    /// Create a new MultiExp instance with the specified bases
    pub fn new(bases: &[C]) -> Self {
        Self {
            bases: bases.to_vec(),
        }
    }
    pub fn compute_msm_opt(
        bases: &[C],
        scalars: &[<C::ScalarField as PrimeField>::BigInt],
    ) -> C::Projective {
        let size = ark_std::cmp::min(bases.len(), scalars.len());
        let scalars = &scalars[..size];
        let bases = &bases[..size];
        let msm = MultiExp::new(bases);
        let mut ctx = MultiExpContext::default();
        let res = msm.evaluate(&mut ctx, scalars, false);
        res
    }

    pub fn evaluate(
        &self,
        ctx: &mut MultiExpContext<C>,
        coeffs: &[<C::ScalarField as PrimeField>::BigInt],
        complete: bool,
    ) -> <C as AffineCurve>::Projective {
        self.evaluate_with(ctx, coeffs, complete, get_best_c(coeffs.len()))
    }

    /// Performs a multi-exponentiation operation with the given bucket width.
    /// Set complete to true if the bases are not guaranteed linearly
    /// independent.
    pub fn evaluate_with(
        &self,
        ctx: &mut MultiExpContext<C>,
        coeffs: &[<C::ScalarField as PrimeField>::BigInt],
        complete: bool,
        c: usize,
    ) -> <C as AffineCurve>::Projective {
        assert!(c >= 4);

        // Allocate more memory if required
        ctx.allocate(coeffs.len(), c);

        // Get the data for each round
        let mut rounds = ctx.rounds.get_rounds::<C>(coeffs.len(), c);

        // Get the bases for the coefficients
        assert!(coeffs.len() == self.bases.len());
        //let start = super::start_measure("msm".to_string(), false);
        let bases = &self.bases[..coeffs.len()];
        if coeffs.len() >= 16 {
            let num_points = coeffs.len();
            let w = c + 1;
            let num_rounds = get_num_rounds::<C>(c);

            // Prepare WNAFs of all coefficients for all rounds
            calculate_wnafs::<C>(coeffs, &mut ctx.wnafs, c);
            // Sort WNAFs into buckets for all rounds
            sort::<C>(&mut ctx.wnafs[0..num_rounds * num_points], &mut rounds, c);
            // Calculate addition trees for all rounds
            create_addition_trees(&mut rounds);

            // Now process each round individually
            let mut partials = vec![C::Projective::zero(); num_rounds];
            for (round, acc) in rounds.iter().zip(partials.iter_mut()) {
                // Scatter the odd points in the odd length buckets to the addition tree
                do_point_scatter::<C>(round, bases, &mut ctx.points);
                // Do all bucket additions
                do_batch_additions::<C>(round, bases, &mut ctx.points, complete);
                // Get the final result of the round
                *acc = accumulate_buckets(round, &mut ctx.points, c);
            }
            let lowest = partials[0];
            let res = lowest
                + partials
                    .iter()
                    .skip(1)
                    .rev()
                    .fold(C::Projective::zero(), |mut total, sum_i| {
                        total += sum_i;
                        for _ in 0..w {
                            total.double_in_place();
                        }
                        total
                    });
            //stop_measure(start);
            res
        } else {
            // Just do a naive msm
            let mut acc = C::Projective::zero();
            for (idx, coeff) in coeffs.iter().enumerate() {
                acc += bases[idx].into_projective().mul(*coeff);
            }
            //stop_measure(start);
            acc
        }
    }
}

impl<C: AffineCurve> MultiExpContext<C> {
    /// Allocate memory for the evalution
    pub fn allocate(&mut self, num_points: usize, c: usize) {
        let num_buckets = get_num_buckets(c);
        let num_rounds = get_num_rounds::<C>(c);
        let tree_size = get_max_tree_size(num_points, c);
        let num_points_total = num_rounds * num_points;
        let num_buckets_total = num_rounds * num_buckets;
        let tree_size_total = num_rounds * tree_size;

        // Allocate memory when necessary
        if self.points.len() < tree_size {
            self.points.resize(tree_size, C::zero());
        }
        if self.wnafs.len() < num_points_total {
            self.wnafs.resize(num_points_total, 0u32);
        }
        if self.rounds.bucket_sizes.len() < num_buckets_total {
            self.rounds.bucket_sizes.resize(num_buckets_total, 0usize);
        }
        if self.rounds.bucket_offsets.len() < num_buckets_total {
            self.rounds.bucket_offsets.resize(num_buckets_total, 0usize);
        }
        if self.rounds.point_data.len() < num_points_total {
            self.rounds.point_data.resize(num_points_total, 0u32);
        }
        if self.rounds.output_indices.len() < tree_size_total / 2 {
            self.rounds.output_indices.resize(tree_size_total / 2, 0u32);
        }
        if self.rounds.base_positions.len() < num_points_total {
            self.rounds.base_positions.resize(num_points_total, 0u32);
        }
        if self.rounds.scatter_map.len() < num_buckets_total {
            self.rounds
                .scatter_map
                .resize(num_buckets_total, ScatterData::default());
        }
    }
}

impl SharedRoundData {
    fn get_rounds<C: AffineCurve>(&mut self, num_points: usize, c: usize) -> Vec<RoundData<'_>> {
        let num_buckets = get_num_buckets(c);
        let num_rounds = get_num_rounds::<C>(c);
        let tree_size = num_points * 2 + num_buckets;

        let mut bucket_sizes_rest = self.bucket_sizes.as_mut_slice();
        let mut bucket_offsets_rest = self.bucket_offsets.as_mut_slice();
        let mut point_data_rest = self.point_data.as_mut_slice();
        let mut output_indices_rest = self.output_indices.as_mut_slice();
        let mut base_positions_rest = self.base_positions.as_mut_slice();
        let mut scatter_map_rest = self.scatter_map.as_mut_slice();

        // Use the allocated memory above to init the memory used for each round.
        // This way the we don't need to reallocate memory for each msm with
        // a different configuration (different number of points or different bucket
        // width)
        let mut rounds: Vec<RoundData<'_>> = Vec::with_capacity(num_rounds);
        for _ in 0..num_rounds {
            let (bucket_sizes, rest) = bucket_sizes_rest.split_at_mut(num_buckets);
            bucket_sizes_rest = rest;
            let (bucket_offsets, rest) = bucket_offsets_rest.split_at_mut(num_buckets);
            bucket_offsets_rest = rest;
            let (point_data, rest) = point_data_rest.split_at_mut(num_points);
            point_data_rest = rest;
            let (output_indices, rest) = output_indices_rest.split_at_mut(tree_size / 2);
            output_indices_rest = rest;
            let (base_positions, rest) = base_positions_rest.split_at_mut(num_points);
            base_positions_rest = rest;
            let (scatter_map, rest) = scatter_map_rest.split_at_mut(num_buckets);
            scatter_map_rest = rest;

            rounds.push(RoundData {
                num_levels: 0,
                level_sizes: vec![],
                level_offset: vec![],
                bucket_sizes,
                bucket_offsets,
                point_data,
                output_indices,
                base_positions,
                scatter_map,
                scatter_map_len: 0,
            });
        }
        rounds
    }
}

fn calculate_wnafs<C: AffineCurve>(
    coeffs: &[<C::ScalarField as PrimeField>::BigInt],
    wnafs: &mut [u32],
    c: usize,
) {
    let num_points = coeffs.len();
    let num_rounds = get_num_rounds::<C>(c);
    let w = c + 1;

    //let start = super::start_measure("calculate wnafs".to_string(), false);
    for (idx, coeff) in coeffs.iter().enumerate() {
        get_wnaf::<C>(coeff, w, num_rounds, &mut wnafs[idx..], num_points);
    }
    //super::stop_measure(start);
}

fn radix_sort(wnafs: &mut [u32], round: &mut RoundData<'_>) {
    let bucket_sizes = &mut round.bucket_sizes;
    let bucket_offsets = &mut round.bucket_offsets;

    // Calculate bucket sizes, first resetting all sizes to 0
    bucket_sizes.fill_with(|| 0);
    for wnaf in wnafs.iter() {
        bucket_sizes[(wnaf & 0x7FFFFFFF) as usize] += 1;
    }

    // Calculate bucket offsets
    let mut offset = 0;
    let mut max_bucket_size = 0;
    bucket_offsets[0] = offset;
    offset += bucket_sizes[0];
    for (bucket_offset, bucket_size) in bucket_offsets
        .iter_mut()
        .skip(1)
        .zip(bucket_sizes.iter().skip(1))
    {
        *bucket_offset = offset;
        offset += bucket_size;
        max_bucket_size = max_bucket_size.max(*bucket_size);
    }
    // Number of levels we need in our addition tree
    round.num_levels = get_num_tree_levels(max_bucket_size);

    // Fill in point data grouped in buckets
    let point_data = &mut round.point_data;
    for (idx, wnaf) in wnafs.iter().enumerate() {
        let bucket_idx = (wnaf & 0x7FFFFFFF) as usize;
        point_data[bucket_offsets[bucket_idx]] = (wnaf & 0x80000000) | (idx as u32);
        bucket_offsets[bucket_idx] += 1;
    }
}

/// Sorts the points so they are grouped per bucket
fn sort<C: AffineCurve>(wnafs: &mut [u32], rounds: &mut [RoundData<'_>], c: usize) {
    let num_rounds = get_num_rounds::<C>(c);
    let num_points = wnafs.len() / num_rounds;

    // Sort per bucket for each round separately
    //let start = super::start_measure("radix sort".to_string(), false);
    for (round, wnafs) in rounds.chunks_mut(1).zip(wnafs.chunks_mut(num_points)) {
        radix_sort(wnafs, &mut round[0]);
    }
    //super::stop_measure(start);
}

/// Creates the addition tree.
/// When PREPROCESS is false we just calculate the size of each level.
/// All points in a bucket need to be added to each other. Because the affine
/// formulas are used we need to add points together in pairs. So we have to
/// make sure that on each level we have an even number of points for each
/// level. Odd points are added to lower levels where the length of the addition
/// results is odd (which then makes the length even).
fn process_addition_tree<const PREPROCESS: bool>(round: &mut RoundData<'_>) {
    let num_levels = round.num_levels;
    let bucket_sizes = &round.bucket_sizes;
    let point_data = &round.point_data;

    let mut level_sizes = vec![0usize; num_levels];
    let mut level_offset = vec![0usize; num_levels];
    let output_indices = &mut round.output_indices;
    let scatter_map = &mut round.scatter_map;
    let base_positions = &mut round.base_positions;
    let mut point_idx = bucket_sizes[0];

    if !PREPROCESS {
        // Set the offsets to the different levels in the tree
        level_offset[0] = 0;
        for idx in 1..level_offset.len() {
            level_offset[idx] = level_offset[idx - 1] + round.level_sizes[idx - 1];
        }
    }

    // The level where all bucket results will be stored
    let bucket_level = num_levels - 1;

    // Run over all buckets
    for bucket_size in bucket_sizes.iter().skip(1) {
        let mut size = *bucket_size;
        if size == 0 {
            level_sizes[bucket_level] += 1;
        } else if size == 1 {
            if !PREPROCESS {
                scatter_map[round.scatter_map_len] = ScatterData {
                    position: (level_offset[bucket_level] + level_sizes[bucket_level]) as u32,
                    point_data: point_data[point_idx],
                };
                round.scatter_map_len += 1;
                point_idx += 1;
            }
            level_sizes[bucket_level] += 1;
        } else {
            #[derive(Clone, Copy, PartialEq)]
            enum State {
                Even,
                OddPoint(usize),
                OddResult(usize),
            }
            let mut state = State::Even;
            let num_levels_bucket = get_num_tree_levels(size);

            let mut start_level_size = level_sizes[0];
            for level in 0..num_levels_bucket - 1 {
                let is_level_odd = size & 1;
                let first_level = level == 0;
                let last_level = level == num_levels_bucket - 2;

                // If this level has odd size we have to handle it
                if is_level_odd == 1 {
                    // If we already have a point saved from a previous odd level, use it
                    // to make the current level even
                    if state != State::Even {
                        if !PREPROCESS {
                            let pos = (level_offset[level] + level_sizes[level]) as u32;
                            match state {
                                State::OddPoint(point_idx) => {
                                    scatter_map[round.scatter_map_len] = ScatterData {
                                        position: pos,
                                        point_data: point_data[point_idx],
                                    };
                                    round.scatter_map_len += 1;
                                },
                                State::OddResult(output_idx) => {
                                    output_indices[output_idx] = pos;
                                },
                                _ => unreachable!(),
                            };
                        }
                        level_sizes[level] += 1;
                        size += 1;
                        state = State::Even;
                    } else {
                        // Not odd yet, so the state is now odd
                        // Store the point we have to add later
                        if !PREPROCESS {
                            if first_level {
                                state = State::OddPoint(point_idx + size - 1);
                            } else {
                                // std::println!("ops, something goes wrong");
                                // chao: else should never happen because we
                                // always make next level even after addition
                                state = State::OddResult(
                                    (level_offset[level] + level_sizes[level] + size) >> 1,
                                );
                            }
                        } else {
                            // Just mark it as odd, we won't use the actual value anywhere
                            state = State::OddPoint(0);
                        }
                        size -= 1;
                    }
                }

                // Write initial points on the first level
                if first_level {
                    if !PREPROCESS {
                        // Just write all points (except the odd size one)
                        let pos = level_offset[level] + level_sizes[level];
                        base_positions[pos..pos + size]
                            .copy_from_slice(&point_data[point_idx..point_idx + size]);
                        point_idx += size + is_level_odd;
                    }
                    level_sizes[level] += size;
                }

                // Write output indices
                // If the next level would be odd, we have to make it even
                // by writing the last result of this level to the next level that is odd
                // (unless we are writing the final result to the bucket level)
                let next_level_size = size >> 1;
                let next_level_odd = next_level_size & 1 == 1;
                let redirect =
                    if next_level_odd && state == State::Even && level < num_levels_bucket - 2 {
                        1usize
                    } else {
                        0usize
                    };
                // An addition works on two points and has one result, so this takes only half
                // the size chao: start_level_size is the sum of level_size up
                // to previous bucket's tree level_offset[level] is the starting
                // position of this level
                let sub_level_offset = (level_offset[level] + start_level_size) >> 1;
                // Cache the start position of the next level
                start_level_size = level_sizes[level + 1];
                if !PREPROCESS {
                    // Write the destination positions of the addition results in the tree
                    // chao: dst_pos is the 2*sub_level_offset of next_level
                    // output_indices: mapping current level index to next level index
                    let dst_pos = level_offset[level + 1] + level_sizes[level + 1];
                    for (idx, output_index) in output_indices
                        [sub_level_offset..sub_level_offset + next_level_size]
                        .iter_mut()
                        .enumerate()
                    {
                        *output_index = (dst_pos + idx) as u32;
                    }
                }
                if last_level {
                    // The result of the last addition for this bucket is written
                    // to the last level (so all bucket results are nicely after each other).
                    // Overwrite the output locations of the last result here.
                    if !PREPROCESS {
                        output_indices[sub_level_offset] =
                            (level_offset[bucket_level] + level_sizes[bucket_level]) as u32;
                    }
                    level_sizes[bucket_level] += 1;
                } else {
                    // Update the sizes
                    level_sizes[level + 1] += next_level_size - redirect;
                    size -= redirect;
                    // We have to redirect the last result to a lower level
                    // chao: this will never make middle levels odd size
                    if redirect == 1 {
                        state = State::OddResult(sub_level_offset + next_level_size - 1);
                    }
                }

                // We added pairs of points together so the next level has half the size
                // chao: size >> 1 here is equal to level_sizes[level+1], may not equal to
                // next_level_size
                size >>= 1;
            }
        }
    }

    // Store the tree level data
    round.level_sizes = level_sizes;
    round.level_offset = level_offset;
}

/// The affine formula is only efficient for independent point additions
/// (using the result of the addition requires an inversion which needs to be
/// avoided as much as possible). And so we try to add as many points together
/// on each level of the tree, writing the result of the addition to a lower
/// level. Each level thus contains independent point additions, with only
/// requiring a single inversion per level in the tree.
fn create_addition_trees(rounds: &mut [RoundData<'_>]) {
    //let start = super::start_measure("create addition trees".to_string(), false);
    for round in rounds.chunks_mut(1) {
        // Collect tree levels sizes
        process_addition_tree::<true>(&mut round[0]);
        // Construct the tree
        process_addition_tree::<false>(&mut round[0]);
    }
    //super::stop_measure(start);
}

/// Here we write the odd points in odd length buckets (the other points are
/// loaded on the fly). This will do random reads AND random writes, which is
/// normally terrible for performance. Luckily this doesn't really matter
/// because we only have to write at most num_buckets points.
fn do_point_scatter<C: AffineCurve>(round: &RoundData<'_>, bases: &[C], points: &mut [C]) {
    let scatter_map = &round.scatter_map[..round.scatter_map_len];
    //let start = super::start_measure("point scatter".to_string(), false);
    if !scatter_map.is_empty() {
        for scatter_data in scatter_map.iter() {
            let target_idx = scatter_data.position as usize;
            let negate = scatter_data.point_data & 0x80000000 != 0;
            let base_idx = (scatter_data.point_data & 0x7FFFFFFF) as usize;
            if negate {
                points[target_idx] = bases[base_idx].neg();
            } else {
                points[target_idx] = bases[base_idx];
            }
        }
    }
    //super::stop_measure(start);
}

/// Finally do all additions using the addition tree we've setup.
fn do_batch_additions<C: AffineCurve>(
    round: &RoundData<'_>,
    bases: &[C],
    points: &mut [C],
    complete: bool,
) {
    let num_levels = round.num_levels;
    let level_counter = &round.level_sizes;
    let level_offset = &round.level_offset;
    let output_indices = &round.output_indices;
    let base_positions = &round.base_positions;

    //let start = super::start_measure("batch additions".to_string(), false);
    for i in 0..num_levels - 1 {
        let start = level_offset[i];
        let num_points = level_counter[i];
        let points = &mut points[start..];
        let output_indices = &output_indices[start / 2..];
        let offset = start;
        if i == 0 {
            let base_positions = &base_positions[start..];
            if complete {
                C::batch_add::<true, true>(
                    points,
                    output_indices,
                    num_points,
                    offset,
                    bases,
                    base_positions,
                );
            } else {
                C::batch_add::<false, true>(
                    points,
                    output_indices,
                    num_points,
                    offset,
                    bases,
                    base_positions,
                );
            }
        } else {
            #[allow(collapsible-else-if)]
            if complete {
                C::batch_add::<true, false>(points, output_indices, num_points, offset, &[], &[]);
            } else {
                C::batch_add::<false, false>(points, output_indices, num_points, offset, &[], &[]);
            }
        }
    }
    //super::stop_measure(start);
}

/// Accumulate all bucket results to get the result of the round
fn accumulate_buckets<C: AffineCurve>(
    round: &RoundData<'_>,
    points: &mut [C],
    c: usize,
) -> C::Projective {
    let num_buckets = get_num_buckets(c);

    let num_levels = round.num_levels;
    let bucket_sizes = &round.bucket_sizes;
    let level_offset = &round.level_offset;

    //let start_time = super::start_measure("accumulate buckets".to_string(), false);
    let start = level_offset[num_levels - 1];
    let buckets = &mut points[start..(start + num_buckets)];
    let mut res = C::Projective::zero();
    let mut running_sum = C::Projective::zero();
    bucket_sizes[1..]
        .into_iter()
        .zip(buckets)
        .rev()
        .for_each(|(bz, b)| {
            if *bz > 0 {
                running_sum.add_assign_mixed(b);
            }
            res += &running_sum;
        });
    //super::stop_measure(start_time);
    res
}
