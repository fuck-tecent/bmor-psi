import Mathlib

theorem Conjectures.JoshiAbc.ThreeLift : ∀ (G : Type) [AddCommGroup G] (C L : AddSubgroup G), L ≤ C → (∀ x : G, ∃ y ∈ C, x-y ∈ L) → C=⊤ := by
  intro G _ C L hLC h
  rw [AddSubgroup.eq_top_iff']
  intro x
  obtain ⟨y, hy, hxy⟩ := h x
  have hmem : y + (x - y) ∈ C := C.add_mem hy (hLC hxy)
  simpa using hmem
