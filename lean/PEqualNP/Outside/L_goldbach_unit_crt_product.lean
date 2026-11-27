import Mathlib

namespace GoldbachUnitCRTProduct

open Finset

/-! ### Transport of `IsUnit` along a ring isomorphism -/

theorem isUnit_ringEquiv_iff {R S : Type*} [Semiring R] [Semiring S]
    (e : R ≃+* S) (x : R) : IsUnit (e x) ↔ IsUnit x := by
  constructor
  · intro h
    have h' : IsUnit (e.symm (e x)) := h.map e.symm.toRingHom
    rwa [RingEquiv.symm_apply_apply] at h'
  · intro h
    exact h.map e.toRingHom

/-! ### The two versions of the counting set -/

/-- The set from the task statement: residues `a` in `range q` that are coprime
to `q`, and such that `n - a` is coprime to `q` as well. -/
def U (q n : ℕ) : Finset ℕ :=
  (Finset.range q).filter fun a => Nat.Coprime a q ∧ Nat.Coprime (n + q - a) q

/-- The same condition, stated on `ZMod q`. -/
def good (q n : ℕ) [NeZero q] : Finset (ZMod q) :=
  Finset.univ.filter fun x => IsUnit x ∧ IsUnit ((n : ZMod q) - x)

/-! ### Translating `Nat.Coprime` to `IsUnit` -/

theorem natCast_sub_natCast (q n a : ℕ) (ha : a ≤ q) :
    ((n + q - a : ℕ) : ZMod q) = (n : ZMod q) - (a : ZMod q) := by
  have h1 : n + q - a = n + (q - a) := by omega
  rw [h1, Nat.cast_add, Nat.cast_sub ha, ZMod.natCast_self, zero_sub, sub_eq_add_neg]

theorem mem_U_iff (q n a : ℕ) :
    a ∈ U q n ↔ a < q ∧ IsUnit (a : ZMod q) ∧ IsUnit ((n : ZMod q) - (a : ZMod q)) := by
  simp only [U, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hlt, h1, h2⟩
    have ha : a ≤ q := le_of_lt hlt
    refine ⟨hlt, (ZMod.isUnit_iff_coprime a q).2 h1, ?_⟩
    rw [← natCast_sub_natCast q n a ha]
    exact (ZMod.isUnit_iff_coprime (n + q - a) q).2 h2
  · rintro ⟨hlt, h1, h2⟩
    have ha : a ≤ q := le_of_lt hlt
    refine ⟨hlt, (ZMod.isUnit_iff_coprime a q).1 h1, ?_⟩
    rw [← natCast_sub_natCast q n a ha] at h2
    exact (ZMod.isUnit_iff_coprime (n + q - a) q).1 h2

/-- `U q n` and `good q n` have the same cardinality: `a ↦ (a : ZMod q)` is a
bijection from `range q` onto `ZMod q`. -/
theorem card_U_eq_card_good (q n : ℕ) [NeZero q] : (U q n).card = (good q n).card := by
  refine Finset.card_bij (fun a (_ : a ∈ U q n) => (a : ZMod q)) ?_ ?_ ?_
  · intro a ha
    rw [mem_U_iff] at ha
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ha.2.1, ha.2.2⟩
  · intro a ha b hb hab
    rw [mem_U_iff] at ha hb
    rw [ZMod.natCast_eq_natCast_iff] at hab
    exact Nat.ModEq.eq_of_lt_of_lt hab ha.1 hb.1
  · intro y hy
    rw [good, Finset.mem_filter] at hy
    obtain ⟨-, hy1, hy2⟩ := hy
    refine ⟨y.val, ?_, ?_⟩
    · rw [mem_U_iff]
      have hyval : ((y.val : ℕ) : ZMod q) = y := ZMod.natCast_zmod_val y
      exact ⟨ZMod.val_lt y, by rwa [hyval], by rwa [hyval]⟩
    · exact ZMod.natCast_zmod_val y

/-! ### The Chinese remainder theorem, set-theoretically -/

theorem mem_good_crt (q r n : ℕ) [NeZero q] [NeZero r] [NeZero (q * r)]
    (h : Nat.Coprime q r) (x : ZMod (q * r)) :
    ZMod.chineseRemainder h x ∈ good q n ×ˢ good r n ↔ x ∈ good (q * r) n := by
  set e := ZMod.chineseRemainder h
  have hnat : e ((n : ℕ) : ZMod (q * r)) = (((n : ℕ) : ZMod q), ((n : ℕ) : ZMod r)) := by
    rw [map_natCast]
    rfl
  have hsub : e (((n : ℕ) : ZMod (q * r)) - x)
      = (((n : ℕ) : ZMod q) - (e x).1, ((n : ℕ) : ZMod r) - (e x).2) := by
    rw [map_sub, hnat]
    rfl
  simp only [Finset.mem_product, good, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨(isUnit_ringEquiv_iff e x).1 (Prod.isUnit_iff.2 ⟨h1, h3⟩), ?_⟩
    refine (isUnit_ringEquiv_iff e (((n : ℕ) : ZMod (q * r)) - x)).1 ?_
    rw [hsub]
    exact Prod.isUnit_iff.2 ⟨h2, h4⟩
  · rintro ⟨h1, h2⟩
    have h2' : IsUnit (e (((n : ℕ) : ZMod (q * r)) - x)) :=
      (isUnit_ringEquiv_iff e _).2 h2
    rw [hsub] at h2'
    have h1' := (isUnit_ringEquiv_iff e x).2 h1
    exact ⟨⟨(Prod.isUnit_iff.1 h1').1, (Prod.isUnit_iff.1 h2').1⟩,
      (Prod.isUnit_iff.1 h1').2, (Prod.isUnit_iff.1 h2').2⟩

theorem card_good_mul (q r n : ℕ) [NeZero q] [NeZero r] [NeZero (q * r)]
    (h : Nat.Coprime q r) :
    (good (q * r) n).card = (good q n).card * (good r n).card := by
  have hbij : (good (q * r) n).card = (good q n ×ˢ good r n).card := by
    refine Finset.card_bij' (fun x (_ : x ∈ good (q * r) n) => ZMod.chineseRemainder h x)
      (fun y (_ : y ∈ good q n ×ˢ good r n) => (ZMod.chineseRemainder h).symm y) ?_ ?_ ?_ ?_
    · intro x hx
      exact (mem_good_crt q r n h x).2 hx
    · intro y hy
      refine (mem_good_crt q r n h ((ZMod.chineseRemainder h).symm y)).1 ?_
      rwa [RingEquiv.apply_symm_apply]
    · intro x _
      exact RingEquiv.symm_apply_apply _ _
    · intro y _
      exact RingEquiv.apply_symm_apply _ _
  rw [hbij, Finset.card_product]

/-! ### The main statement -/

theorem U_card_mul (q r n : ℕ) (hq : 0 < q) (hr : 0 < r) (h : Nat.Coprime q r) :
    (U (q * r) n).card = (U q n).card * (U r n).card := by
  letI : NeZero q := ⟨hq.ne'⟩
  letI : NeZero r := ⟨hr.ne'⟩
  letI : NeZero (q * r) := ⟨(Nat.mul_pos hq hr).ne'⟩
  rw [card_U_eq_card_good (q * r) n, card_U_eq_card_good q n, card_U_eq_card_good r n,
    card_good_mul q r n h]

end GoldbachUnitCRTProduct

namespace PEqualNP.Outside

theorem L_goldbach_unit_crt_product :
    let U := fun q n : ℕ =>
      (Finset.range q).filter (fun a => Nat.Coprime a q ∧ Nat.Coprime (n + q - a) q)
    ∀ q r n : ℕ, 0 < q → 0 < r → Nat.Coprime q r →
      (U (q * r) n).card = (U q n).card * (U r n).card := by
  dsimp only
  intro q r n hq hr h
  exact GoldbachUnitCRTProduct.U_card_mul q r n hq hr h

end PEqualNP.Outside
