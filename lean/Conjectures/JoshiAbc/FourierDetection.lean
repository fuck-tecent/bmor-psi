import Mathlib

theorem Conjectures.JoshiAbc.FourierDetection :
    ∀ (p n : ℕ) [Fact p.Prime] (S : Set (Fin n → ZMod p)), Submodule.span (ZMod p) S = ⊤ ↔ ∀ f : Module.Dual (ZMod p) (Fin n → ZMod p), f ≠ 0 → ∃ v ∈ S, f v ≠ 0 := by
  intro p n _ S
  constructor
  · intro hS f hf
    by_contra hcon
    have hmem : ∀ v ∈ S, f v = 0 := by
      intro v hv
      by_contra hv0
      exact hcon ⟨v, hv, hv0⟩
    have hle : Submodule.span (ZMod p) S ≤ LinearMap.ker f :=
      Submodule.span_le.2 hmem
    rw [hS] at hle
    exact hf (LinearMap.ker_eq_top.1 (top_le_iff.1 hle))
  · intro h
    by_contra hne
    have hlt : Submodule.span (ZMod p) S < ⊤ := lt_top_iff_ne_top.2 hne
    obtain ⟨f, hf0, hle⟩ :=
      Submodule.exists_le_ker_of_lt_top (Submodule.span (ZMod p) S) hlt
    obtain ⟨v, hvS, hv0⟩ := h f hf0
    exact hv0 (LinearMap.mem_ker.1 (hle (Submodule.subset_span hvS)))
