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
