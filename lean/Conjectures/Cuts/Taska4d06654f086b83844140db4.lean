import Mathlib

/-- Combinatorial extraction: a positive count of admissible pairs yields a witness.
Adapted from the accepted proof of `Conjectures.Cuts.Task1611ba2a96c98ad113eb01de`
(the `Fin 6` variant of the same extraction). -/
theorem Conjectures.Cuts.Taska4d06654f086b83844140db4 :
    ∀ (x1 : ℕ), (0 : ℝ) < ↑{x2 ∈ (Finset.range (x1 + (1 : ℕ))).product (Fintype.piFinset fun (x2 : Fin (13 : ℕ)) => Finset.range (x1 + (1 : ℕ))) | Nat.Prime x2.1 ∧ Nat.Prime (x1 - (x2.1 + ∑ x3 : Fin (13 : ℕ), (2 : ℕ) ^ (x2.2 x3 + (1 : ℕ))))}.card → ∃ (x3 : ℕ) (x4 : ℕ) (x5 : Fin (13 : ℕ) → ℕ), Nat.Prime x3 ∧ Nat.Prime x4 ∧ x1 = x3 + x4 + ∑ x6 : Fin (13 : ℕ), (2 : ℕ) ^ (x5 x6 + (1 : ℕ)) := by
  intro N h
  obtain ⟨⟨p, a⟩, hx⟩ := Finset.card_pos.mp (Nat.cast_pos.mp h)
  obtain ⟨_, hp, hq⟩ := Finset.mem_filter.mp hx
  change Nat.Prime (N - (p + ∑ i : Fin 13, 2 ^ (a i + 1))) at hq
  refine ⟨p, _, a, hp, hq, ?_⟩
  have hqpos := hq.pos
  omega
