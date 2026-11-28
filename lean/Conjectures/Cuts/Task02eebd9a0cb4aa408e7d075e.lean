import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

theorem Conjectures.Cuts.Task02eebd9a0cb4aa408e7d075e : (∀ (x1 : ℕ), (0 : ℝ) ≤ ↑(ArithmeticFunction.moebius x1) ^ (2 : ℕ) * (ArithmeticFunction.vonMangoldt x1 * Real.log ↑x1 + ∑ x2 ∈ x1.divisors, ArithmeticFunction.vonMangoldt x2 * ArithmeticFunction.vonMangoldt (x1 / x2)) * if Nat.Prime (x1 + (2 : ℕ)) then Real.log (↑x1 + (2 : ℝ)) else (0 : ℝ)) := by
  intro x1
  refine mul_nonneg (mul_nonneg (sq_nonneg _) ?_) ?_
  · apply add_nonneg
    · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.log_natCast_nonneg x1)
    · exact Finset.sum_nonneg fun d _ =>
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
  · split_ifs with h
    · exact Real.log_nonneg (by
        have h0 : (0 : ℝ) ≤ (x1 : ℝ) := Nat.cast_nonneg x1
        linarith)
    · exact le_refl 0
