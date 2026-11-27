import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Intervals

theorem PEqualNP.Outside.L_goldbach_bulk_overlap_floor :
    let J := fun x : ℕ => (Finset.range (2*x+1)).filter (fun n => Even n ∧ 13*x≤12*n ∧ 4*n≤5*x); let B := fun x : ℕ => (Finset.range (x+1)).filter (fun k => x≤2*k ∧ 3*k≤2*x); ∃ X : ℕ, ∀ x≥X, ∀ n ∈ J x, x ≤ 13*((B x).filter (fun p => p≤n ∧ n-p∈B x)).card := by
  intro J B
  refine ⟨200, fun x hx n hn => ?_⟩
  simp only [J, Finset.mem_filter, Finset.mem_range] at hn
  obtain ⟨hn1, _, hn2, hn3⟩ := hn
  have hsub : Finset.Icc (max ((x+1)/2) (n - 2*x/3)) (min (2*x/3) (n - (x+1)/2)) ⊆
      (B x).filter (fun p => p≤n ∧ n-p∈B x) := by
    intro p hp
    simp only [Finset.mem_Icc] at hp
    simp only [B, Finset.mem_filter, Finset.mem_range]
    omega
  have := Finset.card_le_card hsub
  rw [Nat.card_Icc] at this
  omega
