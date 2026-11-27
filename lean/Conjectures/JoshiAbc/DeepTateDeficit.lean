import Mathlib

private instance prime29 : Fact (Nat.Prime 29) := ⟨by norm_num⟩

theorem Conjectures.JoshiAbc.DeepTateDeficit :
    ∀ v : Fin 3 → (Fin 14 → ZMod 29), 29^11 ≤ Nat.card ((Fin 14 → ZMod 29) ⧸ Submodule.span (ZMod 29) (Set.range v)) := by
  intro v
  let W : Submodule (ZMod 29) (Fin 14 → ZMod 29) :=
    Submodule.span (ZMod 29) (Set.range v)
  have hW : Module.finrank (ZMod 29) W ≤ 3 := by
    have hW' := finrank_range_le_card (R := ZMod 29) v
    unfold Set.finrank at hW'
    simpa [W] using hW'
  have hsum := W.finrank_quotient_add_finrank
  have hV : Module.finrank (ZMod 29) (Fin 14 → ZMod 29) = 14 := by
    simp
  rw [hV] at hsum
  have hq : 11 ≤ Module.finrank (ZMod 29)
      ((Fin 14 → ZMod 29) ⧸ W) := by
    omega
  change 29 ^ 11 ≤ Nat.card ((Fin 14 → ZMod 29) ⧸ W)
  have hfinite : Module.Finite (ZMod 29) ((Fin 14 → ZMod 29) ⧸ W) :=
    Module.Finite.quotient (ZMod 29) W
  have hcard := @Module.natCard_eq_pow_finrank
    (ZMod 29) ((Fin 14 → ZMod 29) ⧸ W)
    inferInstance inferInstance inferInstance hfinite
  rw [hcard, Nat.card_zmod]
  exact Nat.pow_le_pow_right (by norm_num) hq
