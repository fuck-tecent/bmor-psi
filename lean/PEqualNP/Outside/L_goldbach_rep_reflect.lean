import Mathlib

theorem PEqualNP.Outside.L_goldbach_rep_reflect :
    ∀ n p : ℕ, let reps := fun n : ℕ => (Finset.range (n+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n-p)); p ∈ reps n → n-p ∈ reps n := by
  intro n p
  dsimp only
  simp only [Finset.mem_filter, Finset.mem_range]
  rintro ⟨hpRange, hp, hComplement⟩
  have hle : p ≤ n := by omega
  exact ⟨by omega, hComplement, by rwa [Nat.sub_sub_self hle]⟩
