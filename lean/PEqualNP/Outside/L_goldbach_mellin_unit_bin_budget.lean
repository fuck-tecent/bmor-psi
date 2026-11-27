import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

theorem PEqualNP.Outside.L_goldbach_mellin_unit_bin_budget :
    let Z := fun (m k : ℕ) (γ : Fin m → ℝ) => Finset.univ.filter (fun j => (k:ℝ) ≤ |γ j| ∧ |γ j| < (k+1:ℕ)); ∀ (m k a : ℕ) (γ : Fin m → ℝ) (W : ℝ → ℂ) (K : ℝ), 0≤K → (∀ t, ‖W t‖ ≤ K/(1+|t|)^a) → (∑ j ∈ Z m k γ, ‖W (γ j)‖) ≤ ((Z m k γ).card:ℝ)*K/((k+1:ℕ):ℝ)^a := by
  intro Z m k a γ W K hK hW
  have hZ : ∀ j ∈ Z m k γ, ‖W (γ j)‖ ≤ K / ((k + 1 : ℕ) : ℝ) ^ a := by
    intro j hj
    have hj' : (k : ℝ) ≤ |γ j| := by
      have := (Finset.mem_filter.mp hj).2
      exact this.1
    have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hle : ((k + 1 : ℕ) : ℝ) ≤ 1 + |γ j| := by
      push_cast
      linarith
    calc ‖W (γ j)‖ ≤ K / (1 + |γ j|) ^ a := hW _
      _ ≤ K / ((k + 1 : ℕ) : ℝ) ^ a := by
        apply div_le_div_of_nonneg_left hK (by positivity)
        exact pow_le_pow_left₀ hpos.le hle a
  calc ∑ j ∈ Z m k γ, ‖W (γ j)‖ ≤ ∑ j ∈ Z m k γ, K / ((k + 1 : ℕ) : ℝ) ^ a := Finset.sum_le_sum hZ
    _ = ((Z m k γ).card : ℝ) * K / ((k + 1 : ℕ) : ℝ) ^ a := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_div_assoc]
