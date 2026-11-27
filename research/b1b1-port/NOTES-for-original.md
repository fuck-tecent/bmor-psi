# Notes to paste into the original session (branch `research/b1b1-arcsplit`)

## 1. There is an arithmetic error in M36.5 and M40

Both write `B₃ · n^(2/5) = n^(13/15)`.  Correct value:

```
2/3 + 2/5 = 10/15 + 6/15 = 16/15
```

`16/15 > 1`, so `m ≤ B₃ · n^(2/5)` is **weaker than `m ≤ n`** — the support bound is vacuous.

The Lean is fine: `le_mul_of_cofactor_le` (M39) correctly proves `m ≤ H * V₀`, and M40's
Cauchy–Schwarz lemmas are correct.  The error is only in the instantiation
`H = B₃ = n^(2/3)`, `V₀ = n^(2/5)`.

**These conclusions are therefore NOT established and should be struck or marked:**

- `‖S_res‖₂² = n^(13/15+o(1)) = o(n)`
- `|Jdeep(res,res)| = o(n)`
- `|Jdeep(main,res)| ≤ n^(14/15+o(1)) = o(n)`
- `Jdeep(τ₃,τ₃) = Jdeep(main,main) + o(n)`  ← the "outcome B reduction"

The `τ₃` residual is full-range; its `L²` mass is `≈ ∑|τ₃|² ≈ n log²n`, not `o(n)`.

## 2. Correct support table (`m ≤ H_i · V`, `V = n^(2/5)`)

| cell | `H_i` | `H_i · V` | short? |
|---|---|---|---|
| τ₁ | `n^(1/4)` | `n^(13/20)` | YES |
| τ₂ | `n^(1/3)` | `n^(11/15)` | YES |
| τ₃ | `n^(2/3)` | `n^(16/15)` | no |
| τ₄ | `n^(15/16)` | `n^(107/80)` | no |

The trick works for **τ₁ and τ₂**, fails for **τ₃** — opposite of M40.  Reason: it needs
`H_i · V < n`, and τ₃'s divisor band already reaches `n^(2/3)`.

For τ₃ the only short piece is `m/a ≤ n^(1/3−δ)`; the rest of the cofactor interval and the
whole gap band `a ∈ (n^(1/3), n^(2/5))` are full-range.

## 3. What I did instead, on a separate branch

Branch **`research/b1b1-exponent-fix`**, worktree
`~/github.com/fuck-tencent/goldback-vinogradov-fix`, based on `ff0b9136`.
I did not touch `research/b1b1-arcsplit`.

Added (all compile, no `sorry`, file now 2840 lines):

```lean
lowBandCoefficientBot / lowBandCoefficientTop (n V)      -- cofactor split of τ₁ at V
lowBandCoefficient_eq_bot_add_top                        -- exact identity
lowBandCoefficientBot_eq_zero (hm : B₁ n * V < m)        -- support
lowBandCoefficientBot_abs_le                             -- ≤ T * log m
integral_plainPolynomial_norm_sq (n) (a : ℕ → ℂ)         -- general Parseval
sum_bot_norm_sq_localize (hV : B₁ n * V ≤ n)             -- L² sum localises to m ≤ B₁V
integral_bot_norm_sq_le                                  -- ≤ T² * (B₁V + 1) * log²n
```

Combined with M40's `norm_deepSelf_le` / `norm_deepCross_le_sqrt`, the low-cofactor part of
**τ₁** is controlled by an explicit bound.

Two regimes (the lemma is parametric in `T`):

- crude `T ≤ B₁ = n^(1/4)` ⟹ `o(n)` when `V = n^(1/4−δ)`;
- divisor bound `T = n^o(1)` ⟹ `o(n)` when **`V = n^(3/4−δ)`**.

The second peels off all cofactors `≤ n^(3/4−δ)`, leaving
`a ∈ (n^(1/16), n^(1/4)]`, `m/a > n^(3/4−δ)`.  Since `Λ` lives on prime powers, `m/a` is
then essentially a **prime** — so b1-b1 becomes a "small divisor × large prime" Type-I
object.  That is a genuinely more concrete target than the original quadruple sum.

Still to do: instantiate `T ≤ B₁` (needs `a.divisors.card ≤ a`) and the divisor bound.

## 4. Answers to the two questions, after the correction

- **h33 reachable?** No.  Residual full-range; sup route uniformly dead
  (`|Jdeep| ≲ N²/U` would need `U = ω(N)`); one-sidedness only gives
  `Re Jdeep ≥ −∫_{Aᶜ}(Im T)²`, `T = S·e(−nt/2)`, still against `≈ n log²n`.
- **τ₃ cofactor interval + gap band resolvable?** Not by support/Cauchy–Schwarz.

## 5. Suggested action

1. Strike or annotate the four invalidated lines in M36.5 / M40.
2. Replace the support table with the corrected one.
3. Either merge `research/b1b1-exponent-fix`, or re-do the peeling for τ₁ on your branch
   using the lemmas above.
4. Do **not** build further on `Jdeep(τ₃,τ₃) = Jdeep(main,main) + o(n)`.
