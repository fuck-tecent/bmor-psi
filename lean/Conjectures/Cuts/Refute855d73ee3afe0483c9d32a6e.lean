import Mathlib

open Filter

theorem Conjectures.Cuts.Refute855d73ee3afe0483c9d32a6e :
    ¬ (∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∀ (x2 : ℕ), ∃ (x3 : ℕ), x2 < x3 ∧ x1 * ↑x3 ≤ ↑{x4 ∈ Finset.range ((2 : ℕ) * x3 + (1 : ℕ)) | x3 < x4 ∧ (50 : ℕ) * x4 < (51 : ℕ) * x3 ∧ Nat.Prime x4 ∧ Nat.Prime (x4 + (2 : ℕ))}.card) := by
  rintro ⟨c, hc, h⟩
  obtain ⟨T, hT⟩ := eventually_atTop.1
    (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num))
  obtain ⟨S, hS⟩ := eventually_atTop.1
    (Real.tendsto_log_atTop.eventually
      (eventually_gt_atTop (2 * (Real.log 4 + 1) / c)))
  let B : ℕ := ⌈max T S⌉₊
  obtain ⟨X, hBX, hX⟩ := h B
  have hX₀ : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  have hBX' : (B : ℝ) < X := by exact_mod_cast hBX
  have hB : max T S ≤ (B : ℝ) := Nat.le_ceil _
  have hLarge : max T S ≤ 2 * (X : ℝ) := by linarith
  have hLog := hS (2 * (X : ℝ)) ((le_max_right T S).trans hLarge)
  have hLog₀ : 0 < Real.log (2 * (X : ℝ)) := by
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    exact (div_pos (by linarith) hc).trans hLog
  have hPrime := hT (2 * (X : ℝ)) ((le_max_left T S).trans hLarge)
  have hFloor : ⌊2 * (X : ℝ)⌋₊ = 2 * X := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (Nat.floor_natCast (2 * X) : ⌊((2 * X : ℕ) : ℝ)⌋₊ = 2 * X)
  rw [hFloor] at hPrime
  let twins := (Finset.range (2 * X + 1)).filter
    (fun n => X < n ∧ 50 * n < 51 * X ∧ n.Prime ∧ (n + 2).Prime)
  have hSub : twins ⊆ Nat.primesLE (2 * X) := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hRange, _, _, hPrimeN, _⟩
    exact Nat.mem_primesLE.mpr
      ⟨Nat.lt_succ_iff.mp (Finset.mem_range.mp hRange), hPrimeN⟩
  have hCard : (twins.card : ℝ) ≤ (Nat.primeCounting (2 * X) : ℝ) := by
    exact_mod_cast (Nat.primesLE_card_eq_primeCounting (2 * X) ▸ Finset.card_le_card hSub)
  have hUpper : (c * (X : ℝ)) * Real.log (2 * (X : ℝ)) ≤
      (Real.log 4 + 1) * (2 * (X : ℝ)) :=
    (le_div_iff₀ hLog₀).mp (hX.trans (hCard.trans hPrime))
  have hStrict := (div_lt_iff₀ hc).mp hLog
  have hLower : (Real.log 4 + 1) * (2 * (X : ℝ)) <
      (c * (X : ℝ)) * Real.log (2 * (X : ℝ)) := by
    calc
      _ = (X : ℝ) * (2 * (Real.log 4 + 1)) := by ring
      _ < (X : ℝ) * (Real.log (2 * (X : ℝ)) * c) := mul_lt_mul_of_pos_left hStrict hX₀
      _ = _ := by ring
  exact (not_lt_of_ge hUpper) hLower
