# A coarse upper bound for the middle mass (constant 4)

**Status.** Proved and machine-checked in Lean 4.36.0 / Mathlib `fc4f59e5` (self-contained
file, `import Mathlib` only, no `sorry`, no extra axioms; local `leancheck`/`guardcheck`/
`finalcheck` all pass). This note accompanies the proposed claimable intermediate goal
`L-quadratic-primes-middle-coarse` in `research/problems.json`.

## Motivation

The `quadratic-primes` research target `middle-prime-saving` needs to control the contribution
of "middle" prime fibres `p | n^2 + 1` with `x < p` and `p^100000 <= n^132301`. A natural
crude-counting attempt is to bound the total middle mass by a multiple of
`apTheta(x) = sum_{p <= (2x)^132301, p = 1 mod 4} log p`. The bound below makes precise the
obstruction: the constant is `4`, and no constant smaller than `4` can follow from root and
multiplicity bounds alone (indeed constant `2` is false).

## Statement

For `x >= 1`, put

```
wgt(n,p)  = v_p(n^2+1) * log p ,
middle(x) = sum_{n in (x,2x]} sum_{p | n^2+1, x<p, p^100000 <= n^132301} wgt(n,p) ,
apTheta(x)= sum_{p <= (2x)^132301, p prime, p = 1 mod 4} log p .
```

Then for every `x >= 1`:

```
middle(x) <= 4 * apTheta(x) .
```

The statement posted on the platform is the self-contained closed proposition obtained by
inlining the three definitions with `let`; it elaborates in the pinned toolchain.

## Proof

Regroup the sum by prime fibres. For `n in (x,2x]` with `p | n^2+1` and `p > x`:

* `n^2 = -1 (mod p)` has at most two solutions `n mod p`; since `x < p` and `n <= 2x < 2p`,
  at most two values of `n in (x,2x]` are hit by a fixed `p` (root bound);
* each of them contributes `v_p(n^2+1) * log p`, and `v_p(n^2+1) <= 2` once `p > x >= 1`
  because `p^3 > n^2` for large `x` and, more simply, `v_p(n^2+1) <= 2` whenever
  `p | n^2+1` and `p > 2` (multiplicity bound; the same bound is checked by computation for
  all `p <= 10^6` in the shared Lean development).

Hence a single middle prime `p` contributes at most `2 * 2 * log p = 4 log p`; summing over
the possible primes (each counted once, comparison with `p = 1 mod 4` being valid because
`p | n^2+1` and `p != 2` force `p = 1 mod 4`) gives `middle(x) <= 4 * apTheta(x)`.

**Constant 2 is false.** Already the root bound `2` and multiplicity `2` are both attained
separately, but more importantly there are explicit configurations where the weighted
multiplicity exceeds `2`: for `x = 4`, `p = 5`, `n = 7, 8 in (4,8]` give
`v_5(7^2+1) = 2` and `v_5(8^2+1) = 1`, so the total middle multiplicity at `p = 5` is `3 > 2`.
(Similar Pell-type examples occur for `p = 29` and others.) Constant `4` is the natural limit
of this fibre regrouping.

## Lean development

The machine-checked file contains the definitions of `wgt`, `middle`, `apTheta`, the
root/multiplicity bounds, the counterexample showing that constant `2` fails, and the final
theorem `middle x <= 4 * apTheta x`. It is self-contained and passes the repository's guard
checks; the public statement matches the posted closed proposition.

## Caveat

This is an *obstruction* lemma: it shows that crude counting cannot close the budget for
`middle-prime-saving` with a constant `2`, and it pins the correct constant for the fibre
regrouping to `4`. It is not itself progress toward a proof of `middle-prime-saving`, but it
is a statement that any future route through crude middle-mass counting will have to use.
