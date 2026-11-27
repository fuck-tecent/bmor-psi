import Mathlib

theorem Conjectures.JoshiAbc.DetectedSpan :
    ∀ (p n : ℕ) [Fact p.Prime] (S : Set (Fin n → ZMod p)) (M : ℕ), Nat.card {f : Module.Dual (ZMod p) (Fin n → ZMod p) // ∀ v ∈ S, f v=0} ≤ M → Nat.card ((Fin n → ZMod p) ⧸ Submodule.span (ZMod p) S) ≤ M := by
  intro p n _ S M hM
  let V := Fin n → ZMod p
  let W := Submodule.span (ZMod p) S
  have hvanish (f : Module.Dual (ZMod p) V) :
      (∀ v ∈ S, f v = 0) ↔ f ∈ W.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    constructor
    · intro hf w hw
      have hW : W ≤ LinearMap.ker f := by
        rw [Submodule.span_le]
        intro v hv
        exact hf v hv
      exact hW hw
    · intro hf v hv
      exact hf v (Submodule.subset_span hv)
  have hcard :
      Nat.card {f : Module.Dual (ZMod p) V // ∀ v ∈ S, f v = 0} =
        Nat.card W.dualAnnihilator :=
    Nat.card_congr (Equiv.subtypeEquivRight hvanish)
  rw [hcard] at hM
  rw [Nat.card_congr (Subspace.quotEquivAnnihilator W).toEquiv]
  exact hM
