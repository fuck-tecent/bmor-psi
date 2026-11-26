# Vinogradov local plan

## Completed components

- `vaughan.lean`: Vaughan identity, exponential-sum decomposition, arithmetic
  Type-I support bounds, and the reindexings
  - `expSum_low_mu_mul_log_eq` (second Type-I term),
  - `expSum_mul_zeta_eq` (general `f * ζ * g` triple sum),
  - `expSum_low_mu_lowLambda_zeta_eq` (third Type-I term),
  - `expSum_high_mu_zeta_highLambda_eq` (Type-II term).
- `rational.lean`: geometric/Abel bounds, log-weighted bounds, rational and
  major-arc sine lower bounds, and the `Icc` geometric bounds.
- `type1_bound.lean`:
  - second Type-I term on major arcs: `2 U q log n`;
  - third Type-I term on major arcs (`q > U^2`): `2 U^2 q log n`;
  - combined Type-I major-arc bound: `6 U^2 q log n`
    (`norm_expSum_vaughan_typeI_le_majorArc`);
  - Type-II Cauchy–Schwarz reduction
    (`norm_expSum_high_mu_zeta_highLambda_sq_le`).
- `finite_large_sieve.lean`: the accepted finite `ZMod` large sieve
  `∑_r ‖∑_n a_n e(rn/Q)‖^2 ≤ (N+Q) ∑_n |a_n|^2` vendored locally.

## Type-II target

For `t = a/q + β` on a major arc, with `gcd(a,q) = 1`, the Type-II term is

```lean
expSum n (high U μ * ζ * high U Λ) t
  = ∑ d ∈ Icc (U+1) n, μ d *
      ∑ e ∈ Icc (U+1) (n/d), Λ e *
        ∑ m ∈ Icc 1 (n/(d*e)), E (d*e*m*t).
```

The goal is a bound `o(n / (log n)^A)`, eventually for `U ≈ n^{2/5}` and
`q ≤ Q ≈ n^{1/5}`.

## Large-sieve route

1. ~~Collapse the `(e, m)` sum into a single divisor sum.~~ Done:
   `inner_high_sum_collapse` proves
   `∑_e Λ e ∑_m E(d e m t) = ∑_{l ≤ n/d} c_U(l) E(l * d * t)`
   with `c_U(l) = ∑_{e | l, e > U} Λ(e)`, and
   `norm_expSum_high_mu_zeta_highLambda_sq_le'` states the squared-energy
   bound in this collapsed form.
2. Dyadically split `d ∈ [D, 2D)` so that the length `n/d` is comparable to
   `n/D` inside each block.  The refined squared bound now restricts to
   `d ≤ n/(U+1)` (`norm_expSum_high_mu_zeta_highLambda_sq_le_range`), removing
   the spurious factor `U`.
3. Apply Cauchy–Schwarz over `d` (done) and the finite large sieve to the
   Fourier transforms at `l * d * a/q`.  The fixed-length form is done:
   `largeSieve_frequency_energy` proves
   `∑_{d ≤ D} ‖∑_{l ≤ L} c_l e(l d a/q)‖²
      ≤ (D/q + 1)(L + q)∑|c_l|²`
   for `gcd(a,q) = 1`.  What remains is the varying length `n/d` and `β`.
4. Handle the `β` perturbation.  The sharp separated additive large sieve is
   now vendored (`separated_large_sieve.lean`), and
   `separated_frequency_energy` gives the fixed-length energy bound for any
   `δ`-separated frequency family.  Remaining: prove `CircleSeparated` for
   `x d = d (a/q + β)` on blocks of length `< q`, using `gcd(a,q) = 1` and
   `|β| ≤ 1/(2 q D)`.  Done: `circleSeparated_majorArc_shift` proves the
   separation, and `majorArc_block_energy` gives
   `∑_{d ≤ D} ‖∑_{n ≤ L} c_n e(n(d0+d)(a/q+β))‖²
      ≤ (L + 1 + 2q)∑|c_n|²`.

The technical bottleneck is step 2: the finite large sieve needs a fixed
coefficient length, so a smooth cutoff (or a dyadic block decomposition with
an error term) is required before the vendored theorem applies.

## Minor arcs

After the major arcs, the remaining `t` satisfy
`|sin (π d t)|` lower bounds for all small `d`; the plan is to use the
Weierstrass/Weyl or Vinogradov minor-arc machinery on the same Type-I/II
decomposition.  Nothing in this direction is formalized yet.

## Type-II block decomposition: the remaining arithmetic input

The short-block major-arc energy bound
`majorArc_block_energy` suggests the following route for the full Type-II
energy: split the inner length `n/d` into aligned blocks of length `B`
(e.g. `B = q`); each full block has fixed coefficients `c_U(l)`, so the
separated large sieve applies to the `d`-blocks.  The single partial block
for each `d` can be bounded trivially.

The resulting estimate is

```text
∑_{d ≤ n/U} |B_d|²
  ≲ (number of d-blocks) · (B + q) · ∑_{l in block} |c_U(l)|²
```

so everything reduces to the divisor-convolution moment

```text
∑_{l ∈ I} |c_U(l)|²,   c_U(l) = ∑_{e | l, e > U} Λ(e).
```

This moment is *not* a difficulty: `∑_{d | l} Λ(d) = log l`
(`ArithmeticFunction.vonMangoldt_sum`), so `‖c_U(l)‖ ≤ log n` and
`∑_{l ∈ I} ‖c_U(l)‖² ≤ |I| (log n)²`
(`norm_typeIICoeff_le`, `sum_normSq_typeIICoeff_le`).

What remains is purely combinatorial bookkeeping: aligned `l`-blocks of
length `B`, `d`-blocks of length `D ≤ q` (chosen for the separation
`|β| ≤ 1/(2qD)`), one partial `l`-block per `d`, and summing the block
estimates.

## Why naive `l`-block Cauchy–Schwarz is insufficient

The fixed-length block large sieve cannot be applied block-by-block to the
cutoff `l ≤ n/d` without losing the saving.  If one splits `l` into aligned
blocks and uses Cauchy–Schwarz over the blocks, a factor
`K_d ≈ n/(U B)` appears; combined with the block estimates this gives only
`n² (log n)^O(1)` for the squared Type-II term instead of `o(n²)`.
The large-sieve saving is cancelled by the block count.

The remaining viable routes are:

1. a smooth cutoff/Abel summation in `l` before applying the large sieve, so
   that the coefficient vector is fixed and only its Fourier transform
   varies slowly; or
2. a bilinear (Gallagher-type) large sieve for the `d, e, m` double sum,
   which handles the product condition `d e m ≤ n` without a varying cutoff.

The block decomposition lemmas
(`sum_range_mul_eq_sum_blocks`, `sum_range_eq_blocks_add_rem`,
`sum_Icc_eq_sum_range_shift`, `majorArc_block_energy_offset`) are in place for
either route.
