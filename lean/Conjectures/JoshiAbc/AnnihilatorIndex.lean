import Mathlib

theorem Conjectures.JoshiAbc.AnnihilatorIndex :
    ∀ (p n : ℕ) [Fact p.Prime] (H : Submodule (ZMod p) (Fin n → ZMod p)),
      Nat.card H.dualAnnihilator = Nat.card ((Fin n → ZMod p) ⧸ H) := by
  intro p n _ H
  exact (Nat.card_congr (Subspace.quotEquivAnnihilator H).toEquiv).symm
