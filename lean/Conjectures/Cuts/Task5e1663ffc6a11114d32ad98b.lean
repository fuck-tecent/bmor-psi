import Mathlib
import PEqualNP.Outside.L_twin_primes_window_bridge
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import Conjectures.TwinPrimes.EnergyBridgeV2

theorem Conjectures.Cuts.Task5e1663ffc6a11114d32ad98b : (∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∀ (x2 : ℕ), (∑ x3 ∈ Finset.range (x2 + (1 : ℕ)), ↑(ArithmeticFunction.moebius x3) * (ArithmeticFunction.vonMangoldt x3 * Real.log ↑x3) * if Nat.Prime (x3 + (2 : ℕ)) then Real.log (↑x3 + (2 : ℝ)) else (0 : ℝ)) ≤ x1 * ↑x2) := by
  refine ⟨1, one_pos, fun x2 => ?_⟩
  refine le_trans (Finset.sum_nonpos fun n _ => ?_)
    (by positivity : (0:ℝ) ≤ (1:ℝ) * ↑x2)
  have hw : (0:ℝ) ≤ if Nat.Prime (n + 2) then Real.log (↑n + 2) else 0 := by
    split_ifs
    · exact Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    · exact le_rfl
  by_cases hpp : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hpp
    have hmu : (↑(ArithmeticFunction.moebius (p ^ k)) : ℝ) ≤ 0 := by
      rw [ArithmeticFunction.moebius_apply_prime_pow hp hk.ne']
      split_ifs <;> norm_num
    have hL : (0:ℝ) ≤ ArithmeticFunction.vonMangoldt (p ^ k) * Real.log ↑(p ^ k) :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.log_natCast_nonneg _)
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hmu hL) hw
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
    simp
