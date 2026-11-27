import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

theorem PEqualNP.Outside.L_goldbach_factor_lower :
    let fac := fun p n : ℕ => if p ∣ n then (p:ℝ)/((p:ℝ)-1) else 1-1/((p:ℝ)-1)^2; ∀ p n : ℕ, 2<p → 0 < 1-1/((p:ℝ)-1)^2 ∧ 1-1/((p:ℝ)-1)^2 ≤ fac p n := by
  dsimp only
  intro p n hp
  have hp' : (2 : ℝ) < p := by exact_mod_cast hp
  have hd : 1 < (p : ℝ) - 1 := by linarith
  have hdpos : 0 < (p : ℝ) - 1 := zero_lt_one.trans hd
  have hs : 1 < ((p : ℝ) - 1) ^ 2 := by
    simpa using one_lt_pow₀ hd (by decide : 2 ≠ 0)
  have hspos := zero_lt_one.trans hs
  constructor
  · exact sub_pos.mpr ((div_lt_one hspos).mpr hs)
  · split_ifs with divides
    · calc
        _ ≤ 1 := sub_le_self _ (div_nonneg zero_le_one hspos.le)
        _ ≤ _ := (one_le_div hdpos).mpr (by linarith)
    · exact le_rfl
