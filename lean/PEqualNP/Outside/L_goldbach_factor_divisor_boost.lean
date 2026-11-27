import Mathlib

theorem PEqualNP.Outside.L_goldbach_factor_divisor_boost :
    let fac := fun p n : ℕ => if p ∣ n then (p:ℝ)/((p:ℝ)-1) else 1-1/((p:ℝ)-1)^2; ∀ p n, 2<p → p ∣ n → fac p n = (1-1/((p:ℝ)-1)^2)*(((p:ℝ)-1)/((p:ℝ)-2)) := by
  dsimp only
  intro p n hp hdvd
  rw [ite_eq_left hdvd]
  have hp_real : (2 : ℝ) < p := by exact_mod_cast hp
  have h₁ : (p : ℝ) - 1 ≠ 0 := by linarith
  have h₂ : (p : ℝ) - 2 ≠ 0 := by linarith
  field_simp
  ring
