import Mathlib

theorem PEqualNP.Outside.L_goldbach_reflected_long_complement_window : ∀ (n p d m D : ℕ), p < n → D < d → d*m = n-p → (n:ℝ)/3 ≤ p → (p:ℝ) ≤ 2*n/3 → D*m < n ∧ (n:ℝ)/3 ≤ d*m ∧ (d*m:ℝ) ≤ 2*n/3 := by
  intro n p d m D hpn hDd hdm h1 h2
  have hcast : (d:ℝ) * (m:ℝ) = (n:ℝ) - (p:ℝ) := by
    have h : ((d*m : ℕ) : ℝ) = (n:ℝ) - (p:ℝ) := by
      rw [hdm, Nat.cast_sub hpn.le]
    simpa using h
  have hn1 : 0 < n := by omega
  refine ⟨?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp only [mul_zero]
      omega
    · have hlt : D * m < d * m := Nat.mul_lt_mul_of_pos_right hDd hm
      have hle : d * m ≤ n := by rw [hdm]; exact Nat.sub_le n p
      omega
  · rw [hcast]; linarith
  · rw [hcast]; linarith