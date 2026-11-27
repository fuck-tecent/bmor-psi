import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.ModEq

theorem PEqualNP.Outside.L_goldbach_finite_factor_window_switch :
    ∀ (n p a b : ℕ), Nat.Prime a → Nat.Prime b → 2 ≤ n-p → a*b=n-p → a ≤ b → a^2 ≤ n-p ∧ n-p ≤ b^2 ∧ p % a = n % a := by
  intro n p a b _ _ hgap hab hle
  have hpn : p ≤ n := by omega
  have hn : a * b + p = n := by rw [hab, Nat.sub_add_cancel hpn]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hab, pow_two]
    exact Nat.mul_le_mul_left a hle
  · rw [← hab, pow_two]
    exact Nat.mul_le_mul_right b hle
  · rw [← hn, Nat.add_mod]
    simp
