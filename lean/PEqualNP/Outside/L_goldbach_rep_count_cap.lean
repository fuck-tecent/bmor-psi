import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Prime.Defs

theorem PEqualNP.Outside.L_goldbach_rep_count_cap :
    ∀ n : ℕ, let reps := fun n : ℕ => (Finset.range (n+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n-p)); (reps n).card ≤ ((Finset.range (n+1)).filter Nat.Prime).card := by
  intro n
  apply Finset.card_le_card
  exact Finset.monotone_filter_right (Finset.range (n + 1)) fun _ _ hp => hp.1
