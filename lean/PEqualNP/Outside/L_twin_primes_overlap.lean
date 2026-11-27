import Mathlib
theorem PEqualNP.Outside.L_twin_primes_overlap : ∀ n m H : ℕ, n ≤ m → ((Finset.Ico n (n+H)) ∩ (Finset.Ico m (m+H))).card = H-(m-n) := by
  intro n m H h
  rw [Finset.Ico_inter_Ico]
  simp only [max_eq_right h, min_eq_left (Nat.add_le_add_right h H), Nat.card_Ico]
  omega

