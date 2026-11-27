# Local Vinogradov interface

This is a local, non-catalogue draft on branch `research/vinogradov-local`.

## What compiles

`bridge.lean` defines the exact polylog minor-arc target from the Vinogradov route
and proves it from a stronger, explicitly named analytic input:

```lean
VinogradovPolylogInput
```

The input states the standard polylog minor-arc saving for every fixed logarithmic
arc cutoff `B ≥ 4`. The bridge only chooses the target cutoff
`2 * Nat.ceil A + 16` and swaps the two conjuncts.

## What is still missing

`VinogradovPolylogInput` itself is not proved. It is the pointwise
Weyl/Vinogradov input; the accepted large-sieve and Vaughan modules currently in
open PRs provide L²/band estimates and the Vaughan decomposition, not this
pointwise estimate.

The accepted upstream material lives in:

- PR #2406 / #2421: arbitrary separated additive large sieve;
- PR #2430: Vaughan identity and Type-I elimination;
- PR #2363: deep Mangoldt swap.

The repository account used here has only `pull` permission, so those PRs cannot be
merged locally. Until they are merged, this branch is a local dependency map and
interface, not a claimable proof.

## First pointwise building block

`geometric.lean` proves the standard geometric-sum bound

```lean
‖∑ k ∈ Finset.range (n+1), E (k*t)‖ ≤ 1 / |sin (π*t)|
```

when `sin (π*t) ≠ 0`. This is the elementary oscillation estimate behind the
linear exponential-sum part of the minor-arc argument. It compiles with the pinned
Lean toolchain.

## Weighted Abel bound

`weighted.lean` upgrades the geometric estimate to weighted sums:

```lean
‖∑ k ∈ range (n+1), a k * E (k*t)‖
  ≤ (|a n| + ∑ k ∈ range n, |a k - a (k+1)|) / |sin (π*t)|
```

via summation by parts. The variation sum is the Abel budget that Vaughan's
Type-I/Type-II decomposition consumes. This file compiles with the pinned
toolchain.

## Type-I support bound

`type1.lean` proves the elementary Type-I estimate

```lean
‖∑ k ∈ range (N+1), low U f k * E (k*t)‖ ≤ (U+1) * C
```

whenever `|f k| ≤ C` for `k ≤ U`. For `U = n^(1/16)` and
`C = O(log n)`, this is `o(n)` without any prime-distribution input. The remaining
hard part is therefore the Type-II range, not the low Type-I terms.

## Residue-class decomposition

`residue.lean` proves the exact finite decomposition

```lean
S n u t =
  ∑ r ∈ range (min q (n+1)),
    E (r*t) *
      ∑ j ∈ range ((n-r)/q + 1),
        u (r + j*q) * E ((j*q)*t)
```

for `0 < q`. This is the entry point for rational frequencies `a/q + β`;
the next step is to combine it with the weighted Abel bound on each residue-class
subsequence.

## Rational-frequency bound

`rational.lean` combines the residue decomposition with the weighted Abel estimate.
For `t = a/q + β` and `sin (π q β) ≠ 0` it proves

```lean
‖S n u (a/q + β)‖
  ≤ ∑ r < min q (n+1),
      (a_r-variation + endpoint term) / |sin (π q β)|
```

where the numerator is exactly the Abel variation of the residue-class
subsequence `j ↦ u (r + j*q)`. This is the rational point estimate needed before
summing over Farey arcs.

## Vaughan decomposition

`vaughan.lean` contains the finite Vaughan identity (adapted from accepted
PR #2430, Apache-2.0) and proves the corresponding decomposition of the
exponential sum:

```lean
expSum n Λ t =
  expSum n (low U Λ) t +
  expSum n (low U μ * log) t -
  expSum n (low U μ * low U Λ * ζ) t +
  expSum n (high U μ * ζ * high U Λ) t
```

The last term is the Type-II coefficient; the first three are the Type-I terms
that the support/Abel estimates must bound.

## Arithmetic-function Type-I support bound

`vaughan.lean` also proves

```lean
‖expSum n (low U f) t‖ ≤ (U+1) * C
```

whenever `|f k| ≤ C` for `k ≤ U`. This is the Type-I support estimate in the
same `ArithmeticFunction` language as the Vaughan decomposition.

## First Type-I term

`vaughan.lean` now bounds the first Vaughan term:

```lean
‖expSum n (low U Λ) t‖ ≤ (U+1) * log n
```

for `1 ≤ n` and `U ≤ n`. Together with the support lemma, this makes the
Type-I `Λ` term `o(n)` once `U = o(n / log n)`.

## Total L1 bound

`vaughan.lean` also proves

```lean
‖expSum n f t‖ ≤ ∑ k ∈ range (n+1), |f k|
```

for every arithmetic function `f`. This is the crude L1 bridge that will be
used to turn support bounds on Type-I coefficients into exponential-sum bounds.

## Type-I pipeline for the second Vaughan term

`vaughan.lean` proves the divisor reindexing

```lean
expSum n (low U μ * log) t =
  ∑ d ∈ Icc 1 U, μ d * ∑ l ∈ Icc 1 (n/d), log l * E (d * l * t)
```

(`expSum_low_mu_mul_log_eq`).  The analytic pieces live in `rational.lean`:

- `norm_log_weighted_geometric_sum_le` / `norm_log_weighted_geometric_sum_Icc_le`:
  the log-weighted Abel bound `2 log N / |sin (π t)|` (the total variation of
  `log` telescopes);
- `abs_sin_pi_mul_div_ge`: `|sin (π r/q)| ≥ 2/q` for `1 ≤ r < q`, via Jordan's
  inequality;
- `abs_sin_pi_mul_majorArc_ge`: on a major arc `t = a/q + β` with
  `Nat.Coprime a q`, `U < q` and `|β| ≤ 1/(16 q U)`, one has
  `|sin (π d t)| ≥ 1/q` for every `1 ≤ d ≤ U`;
- `norm_type1_bilinear_log_le`: the bilinear Type-I estimate with the
  per-`d` weighted Abel bound.

Finally `type1_bound.lean` (importing `rational` and `vaughan`) assembles these:

```lean
‖expSum n (low U μ * log) (a/q + β)‖ ≤ 2 * U * q * log n
```

(`norm_expSum_low_mu_mul_log_le_majorArc`), whenever `gcd(a,q) = 1`, `U < q`
and `|β| ≤ 1/(16 q U)`.

To check the multi-file development, run `./check.sh` (it builds the two
dependency `.olean`s into `build/` and then checks `type1_bound.lean`).

## Triple reindexing: third Type-I term and Type-II term

`vaughan.lean` proves the general reindexing

```lean
expSum n (f * ζ * g) t =
  ∑ d ∈ Icc 1 n, f d *
    ∑ e ∈ Icc 1 (n/d), g e *
      ∑ m ∈ Icc 1 (n/(d*e)), E (d*e*m*t)
```

(`expSum_mul_zeta_eq`).  Support-restriction lemmas (`sum_Icc_eq_sum_Icc_min_of_eq_zero`
and `sum_Icc_eq_sum_Icc_succ_of_eq_zero`) turn this into the two remaining
Vaughan pieces:

- the third Type-I term
  `expSum n (low U μ * low U Λ * ζ) t`
  as a double Type-I sum over `d, e <= U` (`expSum_low_mu_lowLambda_zeta_eq`);
- the Type-II term
  `expSum n (high U μ * ζ * high U Λ) t`
  as a bilinear sum over `d, e > U` (`expSum_high_mu_zeta_highLambda_eq`).

Both inner sums are geometric sums in `m`, ready for the geometric/Abel
bounds.  The third term can be handled on major arcs with `q > U^2`, where
every product `d * e` is still below `q`; the Type-II term needs the large
sieve instead.

## Third Type-I term on major arcs

`type1_bound.lean` now also proves
`norm_expSum_low_mu_lowLambda_zeta_le_majorArc`: for a major arc
`t = a/q + β` with `gcd(a,q) = 1`, `q > U^2` and `|β| ≤ 1/(16 q U^2)`, the
third Vaughan term satisfies

```lean
‖expSum n (low U μ * low U Λ * ζ) (a/q + β)‖ ≤ 2 U^2 q log n.
```

Together with the first Type-I term `(U+1) log n` and the second Type-I term
`2 U q log n`, the whole Type-I part of Vaughan is `O(U^2 q log n)` on these
major arcs.  The remaining piece is the Type-II bilinear sum
`expSum_high_mu_zeta_highLambda_eq`, which needs the large sieve.

## Type-I milestone

`type1_bound.lean` assembles the three Type-I estimates into

```lean
‖expSum n Λ (a/q + β) - expSum n (high U μ * ζ * high U Λ) (a/q + β)‖
  ≤ 6 * U^2 * q * log n
```

(`norm_expSum_vaughan_typeI_le_majorArc`), under
`1 ≤ n`, `U ≤ n`, `gcd(a,q) = 1`, `1 ≤ U`, `U^2 < q` and
`|β| ≤ 1/(16 q U^2)`.

So on these major arcs the whole Type-I part of the Vaughan decomposition is
controlled; the only remaining Vaughan piece is the Type-II bilinear sum
`high U μ * ζ * high U Λ`, which requires the large sieve (and then the
minor-arc treatment and the final assembly).

## Type-II preparation

The accepted finite large sieve from PR #2641 is vendored locally as
`finite_large_sieve.lean` (module `finite_large_sieve`, built by `check.sh`).

`type1_bound.lean` now reduces the Type-II term by Cauchy–Schwarz:

```lean
‖expSum n (high U μ * ζ * high U Λ) t‖ ^ 2
  ≤ #(Icc (U+1) n) *
      ∑ d ∈ Icc (U+1) n,
        ‖∑ e ∈ Icc (U+1) (n/d), Λ e *
            ∑ m ∈ Icc 1 (n/(d*e)), E (d*e*m*t)‖ ^ 2
```

(`norm_expSum_high_mu_zeta_highLambda_sq_le`).  The remaining analytic task is
to bound the energy sum with the large sieve.  The technical obstruction is
that the inner length `n/d` depends on `d`; a dyadic decomposition (or smooth
cutoff) is needed before the finite large sieve can be applied uniformly.

## Collapsed Type-II inner sum

`vaughan.lean` now proves `inner_high_sum_collapse`: for `d > 0` and
`M = n/d`,

```lean
∑ e ∈ Icc (U+1) M, Λ e * ∑ m ∈ Icc 1 (M/e), E (d*e*m*t)
  = ∑ l ∈ Icc 1 M,
      (∑ e ∈ l.divisors.filter (fun e => U < e), Λ e) * E (d*l*t).
```

This turns the Type-II inner sum into a single Fourier transform of the
truncated divisor convolution `c_U(l) = ∑_{e | l, e > U} Λ(e)`.  Accordingly

- `expSum_high_mu_zeta_highLambda_eq'` is the collapsed Type-II identity;
- `norm_expSum_high_mu_zeta_highLambda_sq_le'` is the squared-energy bound
  with the collapsed inner sums.

The next step is the dyadic decomposition of `d` and the finite large sieve.

## Fixed-length frequency-energy large sieve

`rational.lean` now imports `finite_large_sieve` and proves
`largeSieve_frequency_energy`: for `gcd(a,q) = 1`,

```lean
∑ d ∈ range (D+1),
    ‖∑ l ∈ range (L+1), c l * E (l * (d * a/q))‖ ^ 2
  ≤ (D/q + 1) * (L + q) * ∑ l ∈ range (L+1), ‖c l‖ ^ 2.
```

The proof groups `d` by the residue `d * a mod q`, uses the fiber bound
`fiber_card_le` from the vendored finite large sieve, and then applies
`L_goldbach_finite_large_sieve`.  This is the core large-sieve input for the
Type-II energy at `β = 0`.

Remaining for Type-II:

- the inner length `n/d` varies with `d` (dyadic decomposition/smooth cutoff);
- the `β ≠ 0` perturbation (separated large sieve or Abel summation).

## Separated large sieve for major arcs

`separated_large_sieve.lean` vendors the accepted sharp separated additive
large sieve (upstream PR #2406, Apache-2.0), including
`separated_additive_sieve`.

`rational.lean` proves `separated_frequency_energy`: for a `δ`-separated
family `x : Fin (D+1) → ℝ`,

```lean
∑ d : Fin (D+1), ‖∑ n : Fin (L+1), c n * E (n * x d)‖ ^ 2
  ≤ (L + 1 + 1/δ) * ∑ n : Fin (L+1), ‖c n‖ ^ 2.
```

This is the fixed-length Type-II energy bound for arbitrary separated
frequencies, so it covers the `β ≠ 0` major-arc perturbation.  Remaining:

- prove `CircleSeparated` for `x d = d * (a/q + β)` on blocks of length
  `< q` (using `gcd(a,q) = 1` and `|β| ≤ 1/(2qD)`);
- combine with the varying length `n/d` (dyadic decomposition).

## Major-arc Type-II block energy

`rational.lean` now proves the major-arc separation and block-energy inputs:

- `abs_int_mul_rat_sub_ge`: for `1 ≤ |h| < q` and `gcd(a,q) = 1`, the
  distance of `h a/q` from any integer is at least `1/q`;
- `circleSeparated_majorArc_shift`: on a block of `D+1` consecutive
  frequencies `(d0+d)(a/q+β)`, if `D < q` and `|β| ≤ 1/(2qD)`, the points are
  `1/(2q)`-separated on the circle;
- `majorArc_block_energy`: consequently, for any coefficients `c`,

```lean
∑ d : Fin (D+1), ‖∑ n : Fin (L+1), c n * E (n (d0+d)(a/q+β))‖ ^ 2
  ≤ (L + 1 + 2q) * ∑ n, ‖c n‖ ^ 2.
```

This is the Type-II energy bound on a short major-arc block.  Remaining:
dyadic decomposition of the full `d`-range, the varying length `n/d`, and the
minor arcs.

## Refined Type-II energy range

The Type-II inner sum `typeIIInner n U t d` vanishes once `d > n/(U+1)`
(the `e`-range is empty).  Accordingly `type1_bound.lean` proves

```lean
‖expSum n (high U μ * ζ * high U Λ) t‖ ^ 2
  ≤ (n/(U+1)) *
      ∑ d ∈ Icc (U+1) (n/(U+1)), ‖typeIIInner n U t d‖ ^ 2
```

(`norm_expSum_high_mu_zeta_highLambda_sq_le_range`, via the generic
support-truncated Cauchy–Schwarz lemma `norm_sum_mu_mul_sq_le_of_support`).

This removes the earlier spurious factor `n` in place of `n/U`; only
`d ≤ n/(U+1)` can contribute to Type-II.

Remaining for the Type-II estimate: dyadic decomposition of the inner
length `n/d` and of the `d`-range, then the block large sieve.

## Type-II coefficient bound and collapsed energy

`type1_bound.lean` now defines the truncated divisor convolution and its
Fourier form:

```lean
typeIICoeff U l = ∑ e ∈ l.divisors.filter (U < e), Λ e
typeIIFourier n U t d = ∑ l ∈ Icc 1 (n/d), typeIICoeff U l * E (d*l*t)
```

The key point is that the coefficient moment is trivial, because
`∑_{d | l} Λ d = log l` (`ArithmeticFunction.vonMangoldt_sum`):

- `norm_typeIICoeff_le`: `‖typeIICoeff U l‖ ≤ log n` for `l ≤ n`;
- `sum_normSq_typeIICoeff_le`:
  `∑_{l ∈ s} ‖typeIICoeff U l‖² ≤ #s * (log n)²`;
- `typeIIInner_eq_typeIIFourier` identifies the `(e,m)` inner sum with the
  collapsed Fourier sum;
- `norm_expSum_high_mu_zeta_highLambda_sq_le_range'` is the refined squared
  energy bound with `typeIIFourier`.

So no divisor-moment estimate is needed; the remaining Type-II work is the
block decomposition (aligned `l`-blocks of length `B`, `d`-blocks below `q`,
one partial `l`-block per `d`).

### Status of the block route

The fixed-length block large sieve and the offset block bound
(`majorArc_block_energy_offset`) are in place, together with the range-block
lemmas.  A naive Cauchy–Schwarz over `l`-blocks loses a factor
`K_d ≈ n/(UB)`, cancelling the large-sieve saving (see `PLAN.md`).  The next
step is a smooth cutoff/Abel summation or a bilinear Gallagher-type large
sieve for the `d,e,m` double sum.

## Fixed-box Type-II energy (trilinear large sieve)

`type1_bound.lean` now has the fixed dyadic `(e,m)` box estimate:

- `box_e_m_reindex`: collapse
  `∑_{e∈[E,2E)} ∑_{m∈[M,2M)} Λ(e) e(dem t)` to a single divisor-convolution
  sum over `l = em ∈ [EM, 4EM)`;
- `typeIIBoxCoeff` and `norm_typeIIBoxCoeff_le` / interval energy bounds;
- `majorArc_coeff_interval_energy`: core fixed-interval block large sieve;
- `majorArc_box_energy`: for a dyadic `(e,m)` box with
  `4 E M - 1 ≤ n`,

```lean
∑ d in a short d-block,
  ‖∑ e∈[E,2E), m∈[M,2M), Λ e * E(d*e*m*t)‖²
  ≤ (3EM + 1 + 2q) * (3EM + 1) * (log n)².
```

This is the fixed-box trilinear large sieve.  The remaining Type-II step is
the dyadic covering of the region `d>U, e>U, m≥1, d e m ≤ n` by such boxes
(fully contained, so no extra terms are added) and the summation of the box
bounds.

### Dyadic containment

`box_product_le_of_dyadic`: if `8 D E M ≤ n`, then every
`d < 2D`, `e < 2E`, `m < 2M` satisfies `d e m ≤ n`, so the dyadic box is
contained in the Type-II region.

Boxes with `8DEM ≤ n` cover the sub-region `dem ≤ n/8`.  The remaining thin
top region `n/8 < dem ≤ n` needs the standard dyadic boundary refinement
(or a separate bound); this is the last combinatorial step for the global
Type-II estimate.

## Bilinear saving via `e`-weighted Cauchy–Schwarz

The fixed-box estimate `(EM+q)EM` treats the `(e,m)` coefficients as arbitrary
and loses the geometric cancellation in `m`; for large `EM` it only gives an
`n²`-type bound, not a power saving.  The correct bilinear step is

```lean
∑ d, ‖∑ e, Λ e * G_e(d)‖²
  ≤ (∑ e, Λ e) * ∑ e, Λ e * ∑ d, ‖G_e(d)‖²,
```

where `G_e(d) = ∑_m E(d*e*m*t)`.  This is
`sum_norm_mul_sq_le_sum_weight_mul_energy` plus
`norm_sum_mul_sq_le_sum_mul_sum_sq`.

For fixed `e`, `G_e(d)` is a geometric sum at frequency `d * (e t)`; the
`d`-energy is where the large sieve saves.  The frequency set has modulus
`q / gcd(e,q)`, so the remaining step is the standard gcd decomposition:
apply the separated/finite large sieve to each `e` class and sum over `e`
with the divisor bounds on `∑ Λ(e) / gcd(e,q)`.

## Dispersion/phase expansion of Type-II

`type1_bound.lean` now contains the dispersion identity

```lean
((∑ d ≤ n/(U+1), ‖typeIIFourier n U t d‖² : ℝ) : ℂ)
  = ∑ l1,l2 ≤ n/(U+1),
      typeIICoeff U l1 * star (typeIICoeff U l2) *
        ∑ d = U+1 .. min (n/(U+1)) (n/max l1 l2),
          E (d (l1-l2) t)
```

(`dispersion_identity`, specialized as `typeII_energy_dispersion`).
The inner sum over `d` is now a pure geometric sum with frequency
`(l1-l2)t`.  The next step is the standard dispersion analysis:

- `l1 = l2` (diagonal): length `≤ n/l1`;
- `q | (l1-l2)`: resonant geometric sums;
- `q ∤ (l1-l2)`: geometric sum bounded by `2/|sin (π (l1-l2) t)|`.

Together with `|typeIICoeff U l| ≤ log n` and divisor bounds on the
resonant correlations, this gives the Type-II dispersion estimate.

### Geometric inner `d`-sum bound

`norm_geometric_Icc_shift_le`: for any interval and any `θ` with
`1/q ≤ |sin (π θ)|`,

```lean
‖∑ d ∈ Icc A B, E (d * θ)‖ ≤ 2q.
```

Together with `typeII_energy_dispersion`, this gives the geometric bound for
each `(l1,l2)` pair in the non-resonant case.  The remaining dispersion work
is the diagonal, the resonant `q | (l1-l2)` case, and the summation over
`l1,l2` (the crude triangle bound still gives only `n²`; the resonant and
off-diagonal terms need the large sieve/divisor-correlation saving).

### Diagonal dispersion contribution

`diagonal_dispersion_le`:

```lean
∑ l ≤ n/(U+1), ‖typeIICoeff U l‖² * (n/l)
  ≤ n (log n)² (1 + log n).
```

This is the diagonal majorant in the dispersion expansion (the `l1 = l2`
term, whose geometric length is at most `n/l`).  So the diagonal part of the
Type-II energy is `n (log n)^3`, which after the outer factor `n/U` is
`n²/U (log n)^3 = o(n²)`.

The remaining off-diagonal part still needs the resonant `q | (l1-l2)` /
large-sieve saving; the crude `2q` triangle bound is not enough.

### Pointwise Type-II baseline

`norm_typeIIFourier_le`:

```lean
‖typeIIFourier n U t d‖ ≤ (n/d) * log n.
```

Consequently the trivial energy bound is

```text
∑_d ‖typeIIFourier d‖² ≤ n² (log n)² ∑_{d>U} 1/d² ≲ (n²/U)(log n)²,
```

and after the outer factor `n/U` this is `n³/U² (log n)² = n^{11/5}...`,
which is **not** enough.  The off-diagonal dispersion/large-sieve saving is
essential; the diagonal bound alone is `n (log n)^3`.

### Actual diagonal term bound

`diagonal_dispersion_part_le` bounds the **actual** `l1 = l2` term of the
dispersion expansion (not just its majorant):

```lean
‖∑ l, c(l) \bar c(l) * ∑_d E(0)‖
  ≤ n (log n)² (1 + log n).
```

Indeed `E(0) = 1`, so the inner `d`-sum is the interval length, which is at
most `n/l`; the rest is the previous diagonal majorant.

So the diagonal part of the Type-II energy is rigorously `n (log n)^3`, and
after the outer factor `n/U` it is `o(n²)`.  The remaining gap is entirely
the off-diagonal (resonant and non-resonant) part.

### Off-diagonal split and filtered triangle bound

- `sum_diagonal_add_offdiag`: any double sum splits into its diagonal plus
  the sum over `y ∈ s.erase x`;
- `norm_filtered_double_sum_le`: if the kernel is `≤ C` on the filtered
  pairs `p x y`, then

```lean
‖∑ x, ∑ y ∈ s.filter (p x), c x * star (c y) * G x y‖
  ≤ C * (∑ x, ‖c x‖) * (∑ y, ‖c y‖).
```

These are the bookkeeping tools for the non-resonant off-diagonal part.  The
resonant part still needs the divisor-correlation/large-sieve input.

### Generalized major-arc sine separation

`abs_sin_pi_mul_majorArc_ge_of_not_dvd`: for `1 ≤ h ≤ M`, `q ∤ h`, and
`|β| ≤ 1/(16 q M)`,

```lean
1/q ≤ |sin (π h (a/q + β))|.
```

This removes the earlier restriction `h < q`, covering all non-resonant
differences in the dispersion sum.

### Non-resonant off-diagonal

`typeIINonresonant q l1 l2 := ¬ (q : ℤ) ∣ (l1 : ℤ) - (l2 : ℤ)`, and

```lean
typeII_nonresonant_energy_le :
  ‖∑ x, ∑ y ∈ s.filter (typeIINonresonant q x), c x * star (c y) * G x y‖
    ≤ 2q (∑‖c‖)²
```

whenever the kernel is `≤ 2q` on non-resonant pairs.  Combined with the
geometric bound and the generalized sine separation, this gives the full
non-resonant off-diagonal estimate.  Only the resonant `q | (l1-l2)` part
remains.

### Type-I major arcs for all denominators `q`

The small-`q` gap (`q <= U` for the second term, `q <= U^2` for the third)
is now closed.  The key is a pointwise sine separation lemma plus a trivial
bound for the multiples of `q`:

- `abs_sin_pi_mul_majorArc_ge_pointwise`: for a single `h <= M` with
  `q ∤ h` and `|β| <= 1/(16 q M)`, `|sin (π h (a/q + β))| >= 1/q`;
- `norm_log_weighted_geometric_sum_Icc_le_trivial`: the log-weighted
  geometric sum is at most `N log N` (no oscillation needed);
- `sum_inv_Icc_le_one_add_log`, `sum_inv_multiples_eq`,
  `sum_inv_filter_le`: harmonic-sum bounds for the multiples of `q`;
- `double_sum_vonMangoldt_div_le`: in the double sum over `d,e <= U` with
  `q | de`, the von Mangoldt identity `∑_{e|k} Λ(e) = log k` removes the
  divisor-counting loss and gives the saving `1/q`.

Results:

```lean
-- second term, any q >= 1
norm_expSum_low_mu_mul_log_le_majorArc_small_q :
  |S_2| <= 2 U q log n + 2 n log n (1 + log n) / q

-- third term, any q >= 1
norm_expSum_low_mu_lowLambda_zeta_le_majorArc_small_q :
  |S_3| <= 2 U^2 q log n + 4 n log n (1 + log n) / q

-- combined Type-I, any q >= 1
norm_expSum_vaughan_typeI_le_majorArc_small_q :
  |S_I,full| <= 6 U^2 q log n + 6 n log n (1 + log n) / q
```

All assume `1 <= U <= n`, `gcd(a,q) = 1`, and `|β| <= 1/(16 q U^2)`.  Thus
the Type-I major-arc estimate no longer needs `U^2 < q`; the previous
`norm_expSum_vaughan_typeI_le_majorArc` is retained as the sharper
large-`q` form.

### Unconditional non-resonant Type-II kernel

The actual dispersion kernel is now defined and bounded pointwise:

```lean
typeIIKernel n U t l1 l2 =
  ∑ d ∈ Icc (U+1) (min (n/(U+1)) (n/max l1 l2)),
    E ((d * (l1-l2)) * t)

norm_typeIIKernel_le :
  q ∤ (l1-l2), |β| ≤ 1/(16 q L), L = n/(U+1)
    ⇒ ‖typeIIKernel n U (a/q+β) l1 l2‖ ≤ 2q
```

This removes the `hG` hypothesis from `typeII_nonresonant_energy_le`:
the non-resonant off-diagonal is now unconditional.

Results:

```lean
typeII_nonresonant_dispersion_energy_le :
  ‖non-resonant part of the dispersion energy‖
    ≤ 2q (∑_{l≤L} ‖c_U(l)‖)^2

typeII_nonresonant_dispersion_energy_le_log :
  ... ≤ 2q (L log n)^2

typeII_dispersion_split_nonresonant :
  energy = non-resonant part + resonant part

typeII_energy_le_nonresonant_add_resonant :
  ‖energy‖ ≤ 2q (∑‖c_U‖)^2 + ‖resonant part‖
```

The remaining Type-II gap is exactly the **resonant** part `q | (l1-l2)`
(the diagonal subpart is already bounded by `diagonal_dispersion_part_le`;
the resonant off-diagonal correlation is still open).

### Type-I major/minor arc infrastructure

New files:

- `arcs.lean`:
  - `typeIMajorArcs U Q = ⋃_{q≤Q} ⋃_{a≤q, (a,q)=1} Icc (a/q - r_q) (a/q + r_q)`,
    with `r_q = 1/(16 q U²)` (the Type-I major-arc width);
  - `typeIMinorArcs U Q = (typeIMajorArcs U Q)ᶜ`;
  - `measurableSet_typeIMajorArcs`, `measurableSet_typeIMinorArcs`;
  - `exists_majorArc_representation`: every major-arc point is
    `t = a/q + β` with `|β| ≤ 1/(16 q U²)`.
- `assembly.lean`:
  - `norm_expSum_vaughan_typeI_le_on_majorArc`: the combined Type-I bound
    on the major-arc union, with the representative `q ≤ Q`;
  - `norm_expSum_vaughan_typeI_le_on_majorArc_uniform`: a single uniform
    bound `6 U² Q log n + 6 n log n (1 + log n)` on all major arcs.

`check.sh` now builds `arcs.olean` and `assembly.olean` as well.  The
remaining Type-I work is the minor-arc estimate and the integral assembly;
the major-arc set and its pointwise estimate are now formalized.

### Farey/Dirichlet approximation and the minor-arc entry

`arcs.lean` now also contains:

- `exists_farey_approx`: for `α ∈ [0,1]` and `Q > 0`, there are
  `1 ≤ q ≤ Q`, `a ≤ q`, `gcd(a,q)=1`, with
  `|α - a/q| ≤ 1/(q Q)` (Dirichlet, reduced to lowest terms);
- `exists_farey_approx_minor`: if moreover `α` is in the minor arcs
  `(typeIMajorArcs U Q)ᶜ`, the same approximation can be chosen with
  `1/(16 q U²) < |α - a/q| ≤ 1/(q Q)`.  This is the entry point for the
  Type-I minor-arc estimate: the approximation is outside the major-arc
  radius (small-`q` multiples) but inside the Dirichlet radius.

The remaining Type-I minor-arc step is the actual estimate of the Type-I
sums in the two regimes `q Q ≥ 16 U` and `q Q < 16 U`; the Farey
approximation and the minor-arc entry are now formalized.

### Type-II diagonal isolated

The resonant part is now split into its diagonal and off-diagonal pieces:

- `typeIIPair n U t l1 l2 = c(l1) * conj c(l2) * typeIIKernel n U t l1 l2`;
- `typeIIDiagonal n U t = ∑_l typeIIPair n U t l l`;
- `typeIIResonantOffDiag n U q t`: resonant pairs with `l1 ≠ l2`;
- `typeII_resonant_split_diagonal`: resonant part = diagonal + resonant off-diagonal;
- `norm_typeIIDiagonal_le`: the diagonal is at most `n (log n)^2 (1 + log n)`;
- `typeII_energy_le_nonresonant_diagonal_add_resoff`:
  ```lean
  ‖energy‖ ≤ 2q (∑‖c_U‖)^2 + n (log n)^2 (1 + log n) + ‖resonant off-diagonal‖.
  ```

Thus the full Type-II dispersion energy is now reduced to the single
remaining term `typeIIResonantOffDiag` (`q | (l1-l2)`, `l1 ≠ l2`).  This is
the only remaining Type-II gap; everything else is unconditional.

### Distance-to-integer form for Type-I minor arcs

`rational.lean` now defines

```lean
typeIDist x = |x - round x|
```

and proves:

- `abs_sin_pi_mul_ge_two_mul_typeIDist`: `2 * typeIDist x ≤ |sin (π x)|`;
- `norm_geometric_sum_Icc_le_dist`: the geometric sum is at most
  `1 / typeIDist θ`.

`assembly.lean` derives the classical Type-I form

```lean
norm_expSum_low_mu_mul_log_le_dist :
  ‖S_2(t)‖ ≤ ∑_{d≤U} log n / typeIDist (d t).
```

The remaining Type-I minor-arc estimate is now a purely arithmetic bound on
`∑_{d≤U} 1 / typeIDist (d α)` using the Farey approximation
`exists_farey_approx_minor`.

### Unconditional reciprocal-distance form

`typeIDistRecip N θ = N` when `typeIDist θ = 0`, and
`min N (1/typeIDist θ)` otherwise.  Then

```lean
norm_log_weighted_geometric_sum_Icc_le_recip :
  ‖∑_{l≤N} log l · E(lθ)‖ ≤ log n · typeIDistRecip N θ

norm_expSum_low_mu_mul_log_le_recip :
  ‖S_2(t)‖ ≤ ∑_{d≤U} log n · typeIDistRecip (n/d) (d t).
```

This is the classical Type-I minor-arc form, unconditional even at
rational points: the zero-distance case is capped by the trivial length
`n/d`.  The remaining Type-I minor-arc estimate is the arithmetic bound on
this capped reciprocal sum using the Farey approximation.

### Third Type-I term in reciprocal-distance form

`norm_geometric_sum_Icc_le_recip` gives the no-log geometric bound
`‖∑_{m≤N} E(mθ)‖ ≤ typeIDistRecip N θ`.  Consequently

```lean
norm_expSum_low_mu_lowLambda_zeta_le_recip :
  ‖S_3(t)‖ ≤ ∑_{d≤U} ∑_{e≤U}
    Λ(e) · typeIDistRecip (n/(de)) (de · t).
```

All three Type-I terms now have unconditional reciprocal-distance forms:
the first term is `(U+1) log n`, the second and third are the capped
reciprocal sums above.  The remaining Type-I minor-arc estimate is the
arithmetic bound on these reciprocal sums.

### Type-I minor-arc second term for `Q ≥ 16U`

`exists_farey_approx` gives a reduced approximation `a/q` with
`|α - a/q| ≤ 1/(qQ)`.  When `Q ≥ 16U` this is inside the major-arc
radius `1/(16qU)`, so the second-term small-`q` estimate applies to
**every** `α ∈ [0,1]` (in particular on the minor arcs):

```lean
norm_expSum_low_mu_mul_log_le_of_large_Q :
  ∃ q ≤ Q, ‖S₂(α)‖ ≤ 2Uq log n + 2n log n (1+log n)/q

norm_expSum_low_mu_mul_log_le_uniform_of_large_Q :
  ‖S₂(α)‖ ≤ 2UQ log n + 2n log n (1+log n).
```

This is a genuine minor-arc Type-I estimate in the regime `Q ≥ 16U`.
The third term needs `Q ≥ 16U²` for the analogous argument (which makes
the minor arcs empty), so its small-`Q` treatment remains open.
