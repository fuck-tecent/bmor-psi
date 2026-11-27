import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Positivity

/-- A single exceptional index would cost at least the square of the model
lower bound in the total squared error. -/
theorem PEqualNP.Outside.L_goldbach_exception_no_outlier :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0
    let conv := fun (u v : ℕ → ℝ) (n : ℕ) =>
      Finset.sum (Finset.range (n + 1)) (fun k => u k * v (n - k))
    let reps := fun n : ℕ =>
      (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))
    let D := fun X : ℕ => (Finset.Ico X (2 * X)).filter (fun n => 4 ≤ n ∧ Even n)
    let bad := fun X : ℕ => (D X).filter (fun n => (reps n).card = 0)
    ∀ (X : ℕ) (m : ℕ → ℝ) (b : ℝ), 0 ≤ b → (∀ n ∈ D X, b ≤ m n) →
      Finset.sum (D X) (fun n => (conv w w n - m n) ^ 2) < b ^ 2 → bad X = ∅ := by
  intro w conv reps D bad X m b hb hmodel herror
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  have hnD : n ∈ D X := (Finset.mem_filter.mp hn).1
  have hnone : reps n = ∅ := Finset.card_eq_zero.mp (Finset.mem_filter.mp hn).2
  have hconv : conv w w n = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hp : Nat.Prime k
    · have hq : ¬ Nat.Prime (n - k) := by
        intro hq
        have hrep : k ∈ reps n := Finset.mem_filter.mpr ⟨hk, hp, hq⟩
        simp only [hnone, Finset.notMem_empty] at hrep
      simp [w, hq]
    · simp [w, hp]
  have hcost : b ^ 2 ≤ (conv w w n - m n) ^ 2 := by
    rw [hconv, zero_sub, neg_sq]
    exact pow_le_pow_left₀ hb (hmodel n hnD) 2
  have hsingle : (conv w w n - m n) ^ 2 ≤
      Finset.sum (D X) (fun k => (conv w w k - m k) ^ 2) :=
    Finset.single_le_sum (f := fun k => (conv w w k - m k) ^ 2)
      (fun k _ => sq_nonneg _) hnD
  exact (not_lt_of_ge (hcost.trans hsingle)) herror
