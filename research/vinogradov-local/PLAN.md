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
  - second Type-I term on major arcs: `2 U q log n` for `q > U`
    (`norm_expSum_low_mu_mul_log_le_majorArc`);
  - third Type-I term on major arcs: `2 U^2 q log n` for `q > U^2`
    (`norm_expSum_low_mu_lowLambda_zeta_le_majorArc`);
  - combined Type-I major-arc bound: `6 U^2 q log n`
    (`norm_expSum_vaughan_typeI_le_majorArc`);
  - **small-`q` versions for every `q >= 1`** (new):
    `2 U q log n + 2 n log n (1+log n)/q`,
    `2 U^2 q log n + 4 n log n (1+log n)/q`, and combined
    `6 U^2 q log n + 6 n log n (1+log n)/q`
    (`norm_expSum_low_mu_mul_log_le_majorArc_small_q`,
    `norm_expSum_low_mu_lowLambda_zeta_le_majorArc_small_q`,
    `norm_expSum_vaughan_typeI_le_majorArc_small_q`);
  - `double_sum_vonMangoldt_div_le` and harmonic-sum helpers for the
    multiples of `q`;
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


## Fixed-box estimate completed

`majorArc_box_energy` proves the fixed dyadic `(e,m)` box energy
`(3EM + 1 + 2q)(3EM + 1)(log n)²` over a short `d`-block.  The last Type-II
task is combinatorial: cover the region `{d > U, e > U, m ≥ 1, d e m ≤ n}`
by dyadic boxes fully contained in it (so the box sums are subsets of the
Type-II sum), then sum the bounds.  The boundary boxes need a standard
dyadic refinement (or a trivial estimate on the thin boundary).

## Dyadic containment and the top boundary

`box_product_le_of_dyadic` proves that `8DEM ≤ n` puts the box inside
`dem ≤ n`.  Thus the contained dyadic boxes cover `dem ≤ n/8`; the top
region `n/8 < dem ≤ n` is the remaining boundary.  The next step is the
standard dyadic refinement of this top region (or a direct bound on its
energy using the same fixed-box estimate with shorter `d`-ranges).

## The missing bilinear saving

The fixed-box estimate alone cannot finish Type-II: for large `EM` it is
`(EM+q)EM`, which loses the geometric cancellation in `m` and gives only
`n²`.  The correct reduction is the `e`-weighted Cauchy–Schwarz

`∑_d ‖∑_e Λ(e) G_e(d)‖²
   ≤ (∑_e Λ(e)) ∑_e Λ(e) ∑_d ‖G_e(d)‖²`.

Now `G_e(d) = ∑_m E(d e m t)` is a geometric sum at frequency `d (e t)`.
For fixed `e`, the modulus is `q / gcd(e,q)`, so the remaining task is the
gcd decomposition: apply the large sieve to each `e` class and sum over `e`
using divisor bounds.  This is the genuine bilinear/Gallagher step.

## Dispersion identity completed

`typeII_energy_dispersion` expands the Type-II energy into

`∑_{l1,l2} c(l1) \bar c(l2) ∑_{d} E(d(l1-l2)t)`.

The inner `d`-sum is geometric.  Remaining:

1. diagonal `l1=l2`;
2. resonant `q | (l1-l2)`;
3. non-resonant geometric bound;
4. sum over `l1,l2` using `|c(l)| ≤ log n` and divisor correlation bounds.

## Geometric `d`-sum bound

`norm_geometric_Icc_shift_le` bounds any interval geometric sum by `2q` when
`1/q ≤ |sin(πθ)|`.  Combined with `typeII_energy_dispersion`, the
non-resonant terms are ready.  Remaining: diagonal, resonant
`q | (l1-l2)`, and the `l1,l2` summation with the necessary large-sieve /
divisor-correlation saving.

## Diagonal bound completed

`diagonal_dispersion_le` gives the `l1 = l2` contribution
`n (log n)² (1 + log n)`, hence `o(n²)` after the outer factor `n/U`.
Remaining: off-diagonal, especially the resonant `q | (l1-l2)` case.

## Baseline and gap

`norm_typeIIFourier_le` gives the pointwise bound `(n/d) log n`; the trivial
energy is `(n²/U)(log n)²`, giving `n³/U²` after the outer factor — still
above `n²`.  The dispersion diagonal is much smaller (`n log³`).  The gap is
entirely in the off-diagonal (especially resonant `q | (l1-l2)`) terms and
requires the divisor-correlation/large-sieve input.

## Actual diagonal term done

`diagonal_dispersion_part_le` bounds the actual `l1 = l2` term by
`n (log n)² (1 + log n)`.  The off-diagonal remains the sole Type-II gap.

## Off-diagonal structure ready

`sum_diagonal_add_offdiag` and `norm_filtered_double_sum_le` provide the
diagonal/off-diagonal split and the filtered triangle bound.  Next:
instantiate with the non-resonance predicate `q ∤ (l1-l2)` and the geometric
`2q` bound; then handle the resonant correlation.

## Non-resonant off-diagonal done

`typeII_nonresonant_energy_le` gives the `2q (∑‖c‖)²` bound for
`q ∤ (l1-l2)`; the generalized sine lemma
`abs_sin_pi_mul_majorArc_ge_of_not_dvd` supplies the separation for all
`h ≤ M` (not just `h < q`).  The sole remaining off-diagonal input is the
resonant `q | (l1-l2)` correlation.

## Type-I small-q closed

`norm_expSum_vaughan_typeI_le_majorArc_small_q` gives the combined Type-I
major-arc bound for every `q >= 1`:

  6 U^2 q log n + 6 n log n (1 + log n) / q.

The small-`q` multiples of `q` are handled trivially; the integer
coefficient sum uses `∑_{e|k} Λ(e) = log k` to avoid divisor-counting
losses.  Remaining Type-I work is optimization for the eventual
major/minor-arc assembly, not coverage.

## Type-II non-resonant kernel closed

`typeIIKernel` and `norm_typeIIKernel_le` now give the actual `2q` kernel
bound, so `typeII_nonresonant_dispersion_energy_le` is unconditional
(with the explicit `2q (L log n)^2` form).  The dispersion energy is split
into non-resonant + resonant parts:
`typeII_dispersion_split_nonresonant` and
`typeII_energy_le_nonresonant_add_resonant`.

Remaining Type-II gap: the resonant `q | (l1-l2)` off-diagonal correlation.
The diagonal part is bounded by `diagonal_dispersion_part_le`.

## Type-I major/minor arcs formalized

`arcs.lean` defines `typeIMajorArcs`/`typeIMinorArcs`, proves both
measurable, and extracts the `a/q + β` representation.  `assembly.lean`
applies the combined Type-I bound on the major-arc union, including the
uniform `6 U² Q log n + 6 n log n (1 + log n)` form.  Next: the Type-I
minor-arc estimate, then the circle-method integral assembly.

## Farey approximation and minor-arc entry

`exists_farey_approx` gives the Dirichlet approximation with a reduced
denominator `q ≤ Q`; `exists_farey_approx_minor` additionally places the
approximation outside the major-arc radius when `α` is in the minor arcs.
Next: the Type-I minor-arc estimate in the regimes `q Q ≥ 16 U` and
`q Q < 16 U`, then the integral assembly.

## Type-II diagonal isolated

`typeII_resonant_split_diagonal` and
`typeII_energy_le_nonresonant_diagonal_add_resoff` reduce the Type-II
energy to

  non-resonant bound + diagonal bound + resonant off-diagonal.

The only remaining Type-II term is `typeIIResonantOffDiag`
(`q | (l1-l2)` with `l1 ≠ l2`).

## Type-I distance-to-integer form

`typeIDist` and `abs_sin_pi_mul_ge_two_mul_typeIDist` give the geometric
distance bound; `norm_expSum_low_mu_mul_log_le_dist` writes the Type-I
second term as `∑ log n / typeIDist (d α)`.  The next step is the
minor-arc estimate of this sum with the Farey approximation.
