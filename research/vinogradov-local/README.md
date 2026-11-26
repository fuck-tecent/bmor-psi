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
