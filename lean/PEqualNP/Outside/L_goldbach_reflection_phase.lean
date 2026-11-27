import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Complex.Basic

theorem PEqualNP.Outside.L_goldbach_reflection_phase :
    ∀ (n : ℕ) (b : ℕ → ℂ) (z : ℂ), z ≠ 0 → (∑ k ∈ Finset.range (n+1), b (n-k)*z^k) = z^n * ∑ k ∈ Finset.range (n+1), b k*(z⁻¹)^k := by
  intro n b z hz
  calc
    _ = ∑ k ∈ Finset.range (n + 1), b k * z ^ (n - k) := by
      calc
        _ = ∑ k ∈ Finset.range (n + 1), b (n - k) * z ^ (n - (n - k)) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
          rw [Nat.sub_sub_self hkn]
        _ = _ := Finset.sum_range_reflect (fun k => b k * z ^ (n - k)) (n + 1)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hphase : z ^ n * (z⁻¹) ^ k = z ^ (n - k) := by
        calc
          _ = (z ^ (n - k) * z ^ k) * (z ^ k)⁻¹ := by
            rw [← pow_add, Nat.sub_add_cancel hkn, inv_pow]
          _ = _ := by rw [mul_assoc, mul_inv_cancel₀ (pow_ne_zero k hz), mul_one]
      rw [← hphase]
      ac_rfl
