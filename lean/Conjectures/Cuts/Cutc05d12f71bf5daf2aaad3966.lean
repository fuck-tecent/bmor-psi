import Mathlib

-- Cut of `L-goldbach-linnik-six-unconditional`.
--
-- The frozen task asks, for every sufficiently large even `N`, for primes `p, q` and six
-- positive binary exponents with `N = p + q + sum i, 2 ^ (a i + 1)`.
--
-- Two independent inputs are isolated.
--
-- (1) The analytic input `h1`: for some `c > 0` and all sufficiently large even `N`, at
-- least `c * N / log N ^ 2` pairs `(p, a)` have `p` prime, every exponent at most `N`, and
-- `N - (p + sum i, 2 ^ (a i + 1))` prime.  This is the positivity of the weighted
-- representation count supplied by the circle method (major-arc main term plus the
-- deep-minor saving); it is the true obstruction of the frozen task.
--
-- (2) The combinatorial input `h2`: a positive count of admissible pairs yields a witness
-- together with its exponent tuple.  It only reads one member of a finite set and
-- rewrites a natural-number equation, so it needs no analysis and is provable from
-- Mathlib alone.
--
-- The bridge below only takes the largest threshold and converts the analytic lower bound
-- into positivity of the count.
--
-- child 1 zh: 解析输入：存在 c > 0 与阈值，使每个充分大偶数的可容许 (p, a) 对数至少为 c·N/(log N)²；即圆法给出的加权表示数正性。
-- child 1 en: Analytic input: for some c > 0 and every sufficiently large even N, at least c·N/(log N)^2 admissible pairs (p, a) exist; this is the circle-method positivity of the weighted representation count.
-- child 2 zh: 组合提取：可容许对数为正时取出一个见证 (p, q, a) 并核对 N = p + q + Σ_i 2^(a_i+1)。
-- child 2 en: Combinatorial extraction: a positive admissible count yields a witness (p, q, a) with N = p + q + Σ_i 2^(a_i+1).

theorem Conjectures.Cuts.Cutc05d12f71bf5daf2aaad3966
    (h1 : ∃ (c : ℝ), 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      c * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 ≤
        ((((Finset.range (N + 1)).product
          (Fintype.piFinset fun _ : Fin 6 => Finset.range (N + 1))).filter
          (fun pa => Nat.Prime pa.1 ∧
            Nat.Prime (N - (pa.1 + ∑ i : Fin 6, 2 ^ (pa.2 i + 1))))).card : ℝ))
    (h2 : ∀ (N : ℕ), 0 < ((((Finset.range (N + 1)).product
        (Fintype.piFinset fun _ : Fin 6 => Finset.range (N + 1))).filter
        (fun pa => Nat.Prime pa.1 ∧
          Nat.Prime (N - (pa.1 + ∑ i : Fin 6, 2 ^ (pa.2 i + 1))))).card : ℝ) →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ ∃ a : Fin 6 → ℕ, N = p + q + ∑ i : Fin 6, 2 ^ (a i + 1)) :
    (∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → ∃ p q : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ ∃ a : Fin 6 → ℕ, N = p + q + ∑ i : Fin 6, 2 ^ (a i + 1)) := by
  classical
  obtain ⟨c, hc, N₀, hN⟩ := h1
  refine ⟨max N₀ 3, fun N hN' hEven => ?_⟩
  have hN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN'
  have h3 : 3 ≤ N := le_trans (le_max_right _ _) hN'
  have hbound := hN N hN₀ hEven
  have hlt : (1 : ℝ) < (N : ℝ) := by
    have h1N : 1 < N := by omega
    exact_mod_cast h1N
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hlt
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have hN0 : 0 < N := by omega
    exact_mod_cast hN0
  have hmain : 0 < c * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by positivity
  exact h2 N (lt_of_lt_of_le hmain hbound)
