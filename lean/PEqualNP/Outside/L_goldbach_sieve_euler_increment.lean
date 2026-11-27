import Mathlib

theorem PEqualNP.Outside.L_goldbach_sieve_euler_increment :
    ∀ p : ℕ, p.Prime → 2<p → (((1+1/((p:ℝ)-2))^2-1)/(p:ℝ)) ≤ 9/(p:ℝ)^2 := by
  intro p hp hp2
  have hp3 : (3:ℝ) ≤ (p:ℝ) := by
    have h3 : 3 ≤ p := by
      rcases hp.eq_two_or_odd with h | h <;> omega
    exact_mod_cast h3
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have hd : (0:ℝ) < (p:ℝ) - 2 := by linarith
  have key : 0 ≤ 7*(p:ℝ)^2 - 33*(p:ℝ) + 36 := by
    nlinarith [sq_nonneg ((p:ℝ)-3), mul_nonneg (by linarith : (0:ℝ) ≤ (p:ℝ)-3) (by linarith : (0:ℝ) ≤ (p:ℝ)-3)]
  rw [div_le_div_iff₀ hp0 (by positivity)]
  field_simp
  nlinarith [key]
