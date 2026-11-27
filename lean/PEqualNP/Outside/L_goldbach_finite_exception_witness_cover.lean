import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

theorem PEqualNP.Outside.L_goldbach_finite_exception_witness_cover :
    ∀ (D U : Finset ℕ) (m R : ℕ → ℝ) (b : ℝ), 0 < b → (∀ n ∈ D, b ≤ m n) → (∀ n ∈ D, 0 ≤ R n) → (∀ n ∈ U, 0 < R n) → (∑ n ∈ D.filter (fun n => n ∉ U), (R n-m n)^2) < b^2 → ∀ n ∈ D, 0 < R n := by
  classical
  intro D U m R b hb hm hR hU hs n hn
  by_cases hu : n ∈ U
  · exact hU n hu
  · by_contra! hnpos
    have hz : R n = 0 := le_antisymm hnpos (hR n hn)
    have hterm : (R n - m n)^2 ≤
        ∑ k ∈ D.filter (fun k => k ∉ U), (R k - m k)^2 :=
      Finset.single_le_sum (f := fun k => (R k - m k)^2)
        (fun k _ => sq_nonneg _) (Finset.mem_filter.mpr ⟨hn, hu⟩)
    have hsq := mul_nonneg (sub_nonneg.mpr (hm n hn)) (show 0 ≤ m n + b by linarith [hm n hn])
    rw [hz] at hterm
    nlinarith
