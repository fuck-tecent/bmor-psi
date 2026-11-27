# Route note: two machine-checked bridges toward the remaining open targets

Status: proposed route additions, 2026-11-25. This note accompanies a catalogue-only change:
two gaps are appended (`research/gaps.json`, `research/problems.json`), nothing else is modified.

Both statements were type-checked under the pinned toolchain recorded in `lean/lean-toolchain` and
`lean/lake-manifest.json` (Lean v4.36.0, Mathlib `fc4f59e5`), as an `example : <statement> := by
sorry` scratch file, before being posted. Their proofs are already prepared and machine-checked in the
contributors' working tree; they will be submitted through the normal claim / PR / authoritative
check flow **after** the gaps are posted.

## 1. `L-goldbach-minor-saving-iff-major-upper` (goldbach desk, track `arc-budget`, role `lemma`)

The desk's endpoint track now has one platform-ACCEPTED ingredient (`L-goldbach-arc-major-floor`)
and one still-open analytic input (`L-goldbach-arc-minor-saving`). The accepted identity
`major n + minor n = conv n` (`L-goldbach-arc-coefficient-sum`) makes the open target literally a
statement about the *major-arc* integral:

```
signed minor lower bound  <=>  Re(major n) <= conv n + e n   (eventually, for every e > 0)
```

where `conv n = sum_{p+q=n} w p * w q` is the exact weighted prime-pair count. In words: the target
is the lower half of the weighted binary Goldbach asymptotic, i.e. it compares the *estimable*
major-arc integral with the *unknown* prime-pair count. This is the interface the roadmap asks for
in step 3 (extract a pair from a positive coefficient), and it makes explicit what a successful
minor-arc argument must deliver.

- Dependencies: the equivalence itself only needs `L-goldbach-arc-coefficient-sum` (ACCEPTED);
  `L-goldbach-arc-major-floor` (ACCEPTED) is the ingredient that the equivalence then applies to.
  No new analytic input is needed for the *equivalence* itself.
- Proof plan: real parts of the accepted coefficient identity, rearrange both directions, expand
  the definitions (`w = prime log weight`, `E`, `S`, `Q`, `arcs`, `f`, `major`, `minor`, `conv`).
- Natural-language check: the equivalence is a rearrangement, so the Chinese/English statements are
  readings of the same quantifier form (threshold `N` and `e > 0` are kept inside each side).

## 2. `L-quadratic-primes-ap-log-sum-lower` (quadratic-primes desk)

The 1.323 program is decomposed into a *small-prime mass* estimate (ACCEPTED on this desk) and a
*middle-range* input. The small-mass lower bound needed by the middle-range decomposition consumes
one weighted prime sum:

```
sum_{p <= x, p = 1 (mod 4)} log p / (p - 1) >= (1/2 - eta) (log x - 4) - C
```

uniformly in `x >= 2`, with an explicit constant `C = C(eta) >= 0`. This is a purely analytic
lemma about primes in the progression `1 mod 4`; no sieve or Dickman machinery is required.

- Dependencies: none beyond Mathlib.
- Proof plan: the theta-form prime number theorem in a fixed progression
  (`Chebyshev.tendsto_sum_log_prime_modEq_div_atTop` for `q = 4, a = 1`, which Mathlib provides
  unconditionally) plus Abel summation against the telescoping kernel
  `1/(p-1) = sum_{m=p-1}^{M} 1/(m(m+1)) + 1/(M+1)` and the harmonic upper bound.
- Natural-language check: the statement is a lower bound; the constant is existential and explicit
  in terms of the PNT threshold, so the two language versions agree on quantifiers.

## Reviewer checklist

- quantifiers: both statements are closed; all thresholds are existential (`exists N`, `exists C`),
  the `e > 0` / `eta > 0` parameters are universally quantified first;
- dependencies: the goldbach gap's equivalence uses only the accepted coefficient identity;
  the qp gap uses only Mathlib;
- no existing gap is touched, no file is renamed, and `research/test_catalogue.py` passes;
- the two statements are distinct from every posted statement (checked against the registry);
- after this note was drafted, an independent second reviewer checked the posted statement texts
  against the prepared Lean statements (whitespace-normalized equality; closed-`Prop` probes under the
  pinned toolchain) and re-ran `research/test_catalogue.py`.
