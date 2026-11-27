import Mathlib
theorem PEqualNP.Outside.L_twin_primes_euler_factor : ∀ (p : ℕ) (u : ℝ), 2 < p → u ≠ (p:ℝ) → (1-u/((p:ℝ)-1))/(1-u/p) = 1-u/((p:ℝ)*((p:ℝ)-1)*(1-u/p)) := by
  intro p u hp hu
  have hp' : (2:ℝ) < p := by exact_mod_cast hp
  have hpn : (p:ℝ) ≠ 0 := by linarith
  have hpm : (p:ℝ)-1 ≠ 0 := by linarith
  have hpu : 1-u/(p:ℝ) ≠ 0 := by
    intro h
    apply hu
    field_simp at h
    linarith
  field_simp
  <;> ring

