mod fixed_base;
mod variable_base;
mod variable_base_opt;
pub use fixed_base::*;
pub use variable_base::*;
pub use variable_base_opt::*;

/// The result of this function is only approximately `ln(a)`
/// [`Explanation of usage`]
///
/// [`Explanation of usage`]: https://github.com/scipr-lab/zexe/issues/79#issue-556220473
fn ln_without_floats(a: usize) -> usize {
    // log2(a) * ln(2)
    (ark_std::log2(a) * 69 / 100) as usize
}
