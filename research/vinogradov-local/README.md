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
