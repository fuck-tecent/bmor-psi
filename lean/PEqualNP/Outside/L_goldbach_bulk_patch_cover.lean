import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Basic

theorem PEqualNP.Outside.L_goldbach_bulk_patch_cover :
    ∃ J : Finset ℚ, (∀ r∈J, 0<r) ∧ ∀ t : ℝ, 1≤t → t≤2 → ∃ r∈J, 13*(r:ℝ)/12<t ∧ t<5*(r:ℝ)/4 := by
  refine ⟨{17/20, 19/20, 27/25, 61/50, 139/100, 79/50, 9/5}, ?_, ?_⟩
  · intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with h | h | h | h | h | h | h <;> subst h <;> norm_num
  · intro t h1 h2
    by_cases c1 : t < 17/16
    · refine ⟨17/20, by simp, ?_, ?_⟩ <;> push_cast <;> linarith
    by_cases c2 : t < 19/16
    · refine ⟨19/20, by simp, ?_, ?_⟩ <;> push_cast <;> linarith
    by_cases c3 : t < 27/20
    · refine ⟨27/25, by simp, ?_, ?_⟩ <;> push_cast <;> linarith
    by_cases c4 : t < 61/40
    · refine ⟨61/50, by simp, ?_, ?_⟩ <;> push_cast <;> linarith
    by_cases c5 : t < 139/80
    · refine ⟨139/100, by simp, ?_, ?_⟩ <;> push_cast <;> linarith
    by_cases c6 : t < 79/40
    · refine ⟨79/50, by simp, ?_, ?_⟩ <;> push_cast <;> linarith
    · refine ⟨9/5, by simp, ?_, ?_⟩ <;> push_cast <;> linarith
