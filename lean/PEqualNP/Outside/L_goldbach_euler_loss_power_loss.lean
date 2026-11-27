import Mathlib

theorem PEqualNP.Outside.L_goldbach_euler_loss_power_loss :
    ∀ (p X k : ℕ), Nat.Prime p → p^k≤X → (k:ℝ)*Real.log (p:ℝ)≤Real.log (X:ℝ) := by
  intro p X k hp hX
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
  have hxpos : (0:ℝ) < (p:ℝ)^k := pow_pos hp0 k
  have hle : (p:ℝ)^k ≤ (X:ℝ) := by exact_mod_cast hX
  have hlog : Real.log ((p:ℝ)^k) ≤ Real.log (X:ℝ) := Real.log_le_log hxpos hle
  rw [Real.log_pow] at hlog
  exact hlog
