import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Real.Sqrt

theorem PEqualNP.Outside.L_goldbach_ap_power_box_scale :
    ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, 2≤n → (Nat.sqrt n:ℝ)*(Nat.log 2 n:ℝ)*Real.log (n:ℝ) ≤ C*Real.sqrt (n:ℝ)*(Real.log (2*(n:ℝ)))^2 := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 / Real.log 2, by positivity, ?_⟩
  intro n hn
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hlog : Real.log (n:ℝ) ≤ Real.log (2*(n:ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have hbinary : (Nat.log 2 n : ℝ) ≤ Real.log (2*(n:ℝ)) / Real.log 2 := by
    apply (le_div_iff₀ htwo).2
    rw [← Real.log_pow]
    refine (Real.log_le_log (by positivity) ?_).trans hlog
    exact_mod_cast Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
  calc
    _ ≤ Real.sqrt (n:ℝ) * (Real.log (2*(n:ℝ)) / Real.log 2) * Real.log (2*(n:ℝ)) := by
      apply mul_le_mul _ hlog (Real.log_natCast_nonneg _) _
      · exact mul_le_mul Real.nat_sqrt_le_real_sqrt hbinary (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
      · exact mul_nonneg (Real.sqrt_nonneg _) ((Nat.cast_nonneg _).trans hbinary)
    _ = (1 / Real.log 2) * Real.sqrt (n:ℝ) * (Real.log (2*(n:ℝ)))^2 := by ring
