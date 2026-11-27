import Mathlib

theorem Conjectures.JoshiAbc.CodifferentRounding :
    ∀ (n d : ℤ) (e : ℕ), 0 < e → ((n-d)+d)/(e:ℤ) = n/(e:ℤ) ∧ 0 ≤ (⌈(n:ℝ)/e⌉:ℝ)-(n:ℝ)/e ∧ (⌈(n:ℝ)/e⌉:ℝ)-(n:ℝ)/e < 1 := by
  intro n d e he
  refine ⟨by rw [sub_add_cancel], ?_, ?_⟩
  · exact sub_nonneg.mpr (Int.le_ceil ((n:ℝ)/e))
  · have h := Int.ceil_lt_add_one ((n:ℝ)/e)
    linarith
