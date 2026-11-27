import Mathlib

/-!
# Counting the characters that annihilate a subgroup

The complex characters of a finite additive group `G` which are trivial on a subgroup `H` are in
bijection with the complex characters of the quotient `G ⧸ H` (pull back along `QuotientAddGroup.mk'`,
descend along `QuotientAddGroup.lift`).  Finite abelian duality
(`AddChar.card_eq`) then identifies their number with `Nat.card (G ⧸ H)`, which is by definition
`H.index`.
-/

namespace Conjectures.JoshiAbc.FullAnnihilator_aux

variable {G : Type} [AddCommGroup G] (H : AddSubgroup G)

/-- A character of `G ⧸ H` pulls back to a character of `G` trivial on `H`. -/
def toSubtype (ψ : AddChar (G ⧸ H) ℂ) : {χ : AddChar G ℂ // ∀ h : H, χ h.val = 1} :=
  ⟨ψ.compAddMonoidHom (QuotientAddGroup.mk' H), fun h => by
    rw [AddChar.compAddMonoidHom_apply, QuotientAddGroup.mk'_apply,
      (QuotientAddGroup.eq_zero_iff (h : G)).mpr h.property, AddChar.map_zero_eq_one]⟩

/-- A character of `G` trivial on `H` descends to a character of `G ⧸ H`. -/
def ofSubtype (χ : {χ : AddChar G ℂ // ∀ h : H, χ h.val = 1}) : AddChar (G ⧸ H) ℂ :=
  AddChar.toAddMonoidHomEquiv.symm
    (QuotientAddGroup.lift H χ.val.toAddMonoidHom fun a ha => by
      have ha' : χ.val a = 1 := χ.property ⟨a, ha⟩
      simpa [AddChar.toAddMonoidHom_apply] using ha')

lemma ofSubtype_toSubtype (ψ : AddChar (G ⧸ H) ℂ) : ofSubtype H (toSubtype H ψ) = ψ := by
  apply AddChar.toAddMonoidHomEquiv.injective
  apply QuotientAddGroup.addMonoidHom_ext
  ext a
  simp [ofSubtype, toSubtype]

lemma toSubtype_ofSubtype (χ : {χ : AddChar G ℂ // ∀ h : H, χ h.val = 1}) :
    toSubtype H (ofSubtype H χ) = χ := by
  apply Subtype.ext
  ext a
  simp [toSubtype, ofSubtype]

/-- The characters of `G` annihilating `H` are exactly the characters of the quotient `G ⧸ H`. -/
def equiv : {χ : AddChar G ℂ // ∀ h : H, χ h.val = 1} ≃ AddChar (G ⧸ H) ℂ where
  toFun := ofSubtype H
  invFun := toSubtype H
  left_inv := toSubtype_ofSubtype H
  right_inv := ofSubtype_toSubtype H

end Conjectures.JoshiAbc.FullAnnihilator_aux

theorem Conjectures.JoshiAbc.FullAnnihilator :
    ∀ (G : Type) [AddCommGroup G] [Fintype G] (H : AddSubgroup G), Nat.card {χ : AddChar G ℂ // ∀ h : H, χ h.val=1} = H.index := by
  intro G _ _ H
  classical
  calc Nat.card {χ : AddChar G ℂ // ∀ h : H, χ h.val = 1}
      = Nat.card (AddChar (G ⧸ H) ℂ) :=
        Nat.card_congr (Conjectures.JoshiAbc.FullAnnihilator_aux.equiv H)
    _ = Fintype.card (AddChar (G ⧸ H) ℂ) := Nat.card_eq_fintype_card
    _ = Fintype.card (G ⧸ H) := AddChar.card_eq
    _ = Nat.card (G ⧸ H) := (Nat.card_eq_fintype_card).symm
    _ = H.index := rfl
