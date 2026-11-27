import Mathlib

theorem PEqualNP.Outside.L_goldbach_rep_odd_support :
    ∀ n : ℕ, Even n → 4<n → let reps := fun n : ℕ => (Finset.range (n+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n-p)); ∀ p ∈ reps n, Odd p ∧ Odd (n-p) := by
  intro n hn hfour reps p hmem
  dsimp [reps] at hmem
  obtain ⟨hbound, hp, hq⟩ := Finset.mem_filter.mp hmem
  have hle : p ≤ n := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hbound
  obtain ⟨k, hk⟩ := hn
  rcases hp.eq_two_or_odd with hp2 | hpodd <;>
    rcases hq.eq_two_or_odd with hq2 | hqodd
  all_goals rw [Nat.odd_iff, Nat.odd_iff]
  all_goals omega
