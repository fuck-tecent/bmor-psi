import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Interval.Finset.Nat

/-- Every eligible even target lies in the half-open dyadic block indexed by
its integer base-two logarithm. -/
theorem PEqualNP.Outside.L_goldbach_exception_block_cover :
    let reps := fun n : ℕ =>
      (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))
    let D := fun X : ℕ => (Finset.Ico X (2 * X)).filter (fun n => 4 ≤ n ∧ Even n)
    let bad := fun X : ℕ => (D X).filter (fun n => (reps n).card = 0)
    ∀ K : ℕ, (∀ j : ℕ, K ≤ j → bad (2 ^ j) = ∅) →
      ∀ n : ℕ, 2 ^ K ≤ n → 4 ≤ n → Even n → (reps n).Nonempty := by
  intro reps D bad K hblocks n hKn hn₄ hEven
  let j := Nat.log 2 n
  have hn₀ : n ≠ 0 := by omega
  have hjK : K ≤ j := Nat.le_log_of_pow_le Nat.one_lt_two hKn
  have hlo : 2 ^ j ≤ n := Nat.pow_log_le_self 2 hn₀
  have hhi : n < 2 * 2 ^ j := by
    simpa only [j, Nat.succ_eq_add_one, pow_succ'] using
      Nat.lt_pow_succ_log_self Nat.one_lt_two n
  have hnBlock : n ∈ D (2 ^ j) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hlo, hhi⟩, hn₄, hEven⟩
  by_contra hnone
  have hreps : reps n = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
  have hbad : n ∈ bad (2 ^ j) :=
    Finset.mem_filter.mpr ⟨hnBlock, Finset.card_eq_zero.mpr hreps⟩
  rw [hblocks j hjK] at hbad
  exact Finset.notMem_empty n hbad
