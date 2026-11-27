import Mathlib

namespace Conjectures.NoThreeInLine.FoldOptimalityAttained_aux

def hh (p : ℕ) : ℕ := (p - 1) / 2

def t0 (p : ℕ) : ZMod p := ((hh p : ℕ) : ZMod p)

def cI (p : ℕ) (z : ZMod p) : ℤ := if z.val > hh p then 1 else 0

def Xv (p : ℕ) (t : ZMod p) (w : ZMod p) : ℤ := ((w + t).val : ℤ)

def Yv (p : ℕ) (w : ZMod p) : ℤ := ((w⁻¹).val : ℤ)

def liftP (p : ℕ) (t : ZMod p) (x : ZMod p) (i j : Fin 2) : ℤ × ℤ :=
  (Xv p t x + (i.val : ℤ) * (p : ℤ), Yv p x + (j.val : ℤ) * (p : ℤ))

def det3i (P Q R : ℤ × ℤ) : ℤ :=
  (Q.1 - P.1) * (R.2 - P.2) - (Q.2 - P.2) * (R.1 - P.1)

def corner (p : ℕ) (x : ZMod p) : Fin 2 × Fin 2 :=
  (if x.val > hh p then 1 else 0, if (x⁻¹).val > hh p then 0 else 1)

def mask (p : ℕ) (x : ZMod p) : Finset (Fin 2 × Fin 2) :=
  Finset.univ.erase (corner p x)

def pts (p : ℕ) [NeZero p] (t : ZMod p) (R : ZMod p → Finset (Fin 2 × Fin 2)) : Finset (ℤ × ℤ) :=
  (Finset.univ.filter (fun x : ZMod p => x ≠ 0)).biUnion
    (fun x => (R x).image (fun ij => liftP p t x ij.1 ij.2))

theorem e0v : ((0 : Fin 2).val : ℤ) = 0 := rfl

theorem e1v : ((1 : Fin 2).val : ℤ) = 1 := rfl

theorem e0n : ((0 : Fin 2).val : ℕ) = 0 := rfl

theorem e1n : ((1 : Fin 2).val : ℕ) = 1 := rfl

theorem cast_p (p : ℕ) : ((p : ℤ) : ZMod p) = 0 := by
  simp [ZMod.natCast_self]

theorem cast_Xv (p : ℕ) [NeZero p] (t w : ZMod p) : ((Xv p t w : ℤ) : ZMod p) = w + t := by
  simp only [Xv, Int.cast_natCast]
  exact ZMod.natCast_zmod_val (w + t)

theorem cast_Yv (p : ℕ) [NeZero p] (w : ZMod p) : ((Yv p w : ℤ) : ZMod p) = w⁻¹ := by
  simp only [Yv, Int.cast_natCast]
  exact ZMod.natCast_zmod_val (w⁻¹)

theorem hh_two (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) : 2 * hh p + 1 = p := by
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  simp only [hh]
  omega

theorem val_add_t0 (p : ℕ) [NeZero p] (z : ZMod p) :
    (z + t0 p).val = (z.val + hh p) % p := by
  have h : z + t0 p = ((z.val + hh p : ℕ) : ZMod p) := by
    simp only [t0, Nat.cast_add, ZMod.natCast_zmod_val]
  rw [h, ZMod.val_natCast]

theorem Xv_eq (p : ℕ) [NeZero p] (hp : Nat.Prime p) (hp2 : p ≠ 2) (z : ZMod p) :
    Xv p (t0 p) z = (z.val : ℤ) + (hh p : ℤ) - (p : ℤ) * cI p z := by
  have h2 := hh_two p hp hp2
  have hz := ZMod.val_lt z
  have hv := val_add_t0 p z
  simp only [Xv, cI]
  rw [hv]
  by_cases h : z.val > hh p
  · rw [if_pos h]
    have h1 : p ≤ z.val + hh p := by omega
    have h3 : z.val + hh p < 2 * p := by omega
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
    rw [Nat.cast_sub h1]
    push_cast
    ring
  · rw [if_neg h]
    rw [Nat.mod_eq_of_lt (by omega)]
    push_cast
    ring

theorem val_neg (p : ℕ) [NeZero p] (z : ZMod p) (hz : z ≠ 0) : (-z).val = p - z.val := by
  have hlt := ZMod.val_lt z
  have hne : z.val ≠ 0 := by
    intro hc
    apply hz
    have h2 := ZMod.natCast_zmod_val z
    rw [hc, Nat.cast_zero] at h2
    exact h2.symm
  have key : (-z) = ((p - z.val : ℕ) : ZMod p) := by
    rw [Nat.cast_sub hlt.le]
    simp [ZMod.natCast_self, ZMod.natCast_zmod_val]
  rw [key, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (by omega)

theorem val_neg_z (p : ℕ) [NeZero p] (z : ZMod p) (hz : z ≠ 0) :
    ((-z).val : ℤ) = (p : ℤ) - (z.val : ℤ) := by
  have h := val_neg p z hz
  have hlt := ZMod.val_lt z
  rw [h, Nat.cast_sub hlt.le]

theorem val_ne_zero (p : ℕ) [NeZero p] (z : ZMod p) (hz : z ≠ 0) : z.val ≠ 0 := by
  intro hc
  apply hz
  have h2 := ZMod.natCast_zmod_val z
  rw [hc, Nat.cast_zero] at h2
  exact h2.symm

theorem cI_neg (p : ℕ) [NeZero p] (hp : Nat.Prime p) (hp2 : p ≠ 2) (z : ZMod p) (hz : z ≠ 0) :
    cI p (-z) = 1 - cI p z := by
  have h2 := hh_two p hp hp2
  have hv := val_neg p z hz
  have hzlt := ZMod.val_lt z
  have hz1 : 1 ≤ z.val := by
    have hne := val_ne_zero p z hz
    omega
  by_cases h : z.val > hh p
  · have hn : ¬ (p - z.val > hh p) := by omega
    simp [cI, hv, h, hn]
  · have hp' : p - z.val > hh p := by omega
    simp [cI, hv, h, hp']

theorem cI_cases (p : ℕ) (z : ZMod p) : cI p z = 0 ∨ cI p z = 1 := by
  by_cases h : z.val > hh p <;> simp [cI, h]

theorem cI_one (p : ℕ) (z : ZMod p) (h : cI p z = 1) : z.val > hh p := by
  by_contra hn
  simp only [cI, if_neg hn] at h
  exact absurd h (by norm_num)

theorem cI_zero (p : ℕ) (z : ZMod p) (h : cI p z = 0) : ¬ (z.val > hh p) := by
  intro hn
  simp only [cI, if_pos hn] at h
  exact absurd h (by norm_num)

theorem corner_fst_val (p : ℕ) (x : ZMod p) : ((corner p x).1.val : ℤ) = cI p x := by
  by_cases h : x.val > hh p <;> simp [corner, cI, h, e0n, e1n]

theorem corner_snd_val (p : ℕ) (x : ZMod p) : ((corner p x).2.val : ℤ) = 1 - cI p (x⁻¹) := by
  by_cases h : (x⁻¹).val > hh p <;> simp [corner, cI, h, e0n, e1n]

theorem corner_eq_iff (p : ℕ) (x : ZMod p) (i j : Fin 2) :
    (i, j) = corner p x ↔ ((i.val : ℤ) = cI p x ∧ (j.val : ℤ) = 1 - cI p (x⁻¹)) := by
  constructor
  · intro h
    have h1 : i = (corner p x).1 := congrArg Prod.fst h
    have h2 : j = (corner p x).2 := congrArg Prod.snd h
    refine ⟨?_, ?_⟩
    · rw [h1, corner_fst_val]
    · rw [h2, corner_snd_val]
  · intro h
    obtain ⟨h1, h2⟩ := h
    have f1 : i = (corner p x).1 := by
      apply Fin.ext
      have hc := corner_fst_val p x
      have hi := i.isLt
      have hj := (corner p x).1.isLt
      omega
    have f2 : j = (corner p x).2 := by
      apply Fin.ext
      have hc := corner_snd_val p x
      have hi := j.isLt
      have hj := (corner p x).2.isLt
      omega
    exact Prod.ext f1 f2

theorem mem_mask (p : ℕ) (x : ZMod p) (i j : Fin 2) (h : (i, j) ∈ mask p x) :
    (i, j) ≠ corner p x :=
  (Finset.mem_erase.mp h).1

theorem fin2_val_inj (p : ℕ) [NeZero p] (hp : Nat.Prime p) (a b : Fin 2)
    (h : ((a.val : ℕ) : ZMod p) = ((b.val : ℕ) : ZMod p)) : a = b := by
  have h2 := hp.two_le
  have hv : a.val % p = b.val % p := by
    rw [← ZMod.val_natCast p a.val, ← ZMod.val_natCast p b.val, h]
  have ha := a.isLt
  have hb := b.isLt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
  exact Fin.ext hv

theorem cast_fst (p : ℕ) [NeZero p] (t x : ZMod p) (i j : Fin 2) :
    (((liftP p t x i j).1 : ℤ) : ZMod p) = x + t := by
  have hpc := cast_p p
  simp only [liftP, Xv, Int.cast_add, Int.cast_mul, Int.cast_natCast, hpc, mul_zero, add_zero]
  exact ZMod.natCast_zmod_val (x + t)

theorem cast_snd (p : ℕ) [NeZero p] (t x : ZMod p) (i j : Fin 2) :
    (((liftP p t x i j).2 : ℤ) : ZMod p) = x⁻¹ := by
  have hpc := cast_p p
  simp only [liftP, Yv, Int.cast_add, Int.cast_mul, Int.cast_natCast, hpc, mul_zero, add_zero]
  exact ZMod.natCast_zmod_val (x⁻¹)

theorem cast_det3i (p : ℕ) [NeZero p] (t x y z : ZMod p) (i1 j1 i2 j2 i3 j3 : Fin 2) :
    ((det3i (liftP p t x i1 j1) (liftP p t y i2 j2) (liftP p t z i3 j3) : ℤ) : ZMod p)
      = (y - x) * (z⁻¹ - x⁻¹) - (y⁻¹ - x⁻¹) * (z - x) := by
  simp only [det3i, Int.cast_sub, Int.cast_mul, cast_fst, cast_snd]
  ring

theorem corner_det_ne : ∀ a b c : Fin 2 × Fin 2, a ≠ b → a ≠ c → b ≠ c →
    ((b.1.val : ℤ) - (a.1.val : ℤ)) * ((c.2.val : ℤ) - (a.2.val : ℤ))
      - ((b.2.val : ℤ) - (a.2.val : ℤ)) * ((c.1.val : ℤ) - (a.1.val : ℤ)) ≠ 0 := by
  decide

theorem det3i_same (p : ℕ) [NeZero p] (hp : Nat.Prime p) (t x : ZMod p)
    (i1 j1 i2 j2 i3 j3 : Fin 2)
    (h12 : (i1, j1) ≠ (i2, j2)) (h13 : (i1, j1) ≠ (i3, j3)) (h23 : (i2, j2) ≠ (i3, j3)) :
    det3i (liftP p t x i1 j1) (liftP p t x i2 j2) (liftP p t x i3 j3) ≠ 0 := by
  have hD : det3i (liftP p t x i1 j1) (liftP p t x i2 j2) (liftP p t x i3 j3)
      = (p : ℤ) * (p : ℤ) * (((i2.val : ℤ) - (i1.val : ℤ)) * ((j3.val : ℤ) - (j1.val : ℤ))
          - ((j2.val : ℤ) - (j1.val : ℤ)) * ((i3.val : ℤ) - (i1.val : ℤ))) := by
    simp only [det3i, liftP, Xv, Yv]
    ring
  rw [hD]
  have hne : (((i2.val : ℤ) - (i1.val : ℤ)) * ((j3.val : ℤ) - (j1.val : ℤ))
      - ((j2.val : ℤ) - (j1.val : ℤ)) * ((i3.val : ℤ) - (i1.val : ℤ))) ≠ 0 :=
    corner_det_ne (i1, j1) (i2, j2) (i3, j3) h12 h13 h23
  have hp0 : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  exact mul_ne_zero (mul_ne_zero hp0 hp0) hne

theorem det3i_three (p : ℕ) [NeZero p] (hp : Nat.Prime p) (t x y z : ZMod p)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (i1 j1 i2 j2 i3 j3 : Fin 2) :
    det3i (liftP p t x i1 j1) (liftP p t y i2 j2) (liftP p t z i3 j3) ≠ 0 := by
  haveI := Fact.mk hp
  intro hD
  have hz0 : ((det3i (liftP p t x i1 j1) (liftP p t y i2 j2) (liftP p t z i3 j3) : ℤ) : ZMod p) = 0 := by
    rw [hD]
    simp
  rw [cast_det3i] at hz0
  have hkey : x * y * z * ((y - x) * (z⁻¹ - x⁻¹) - (y⁻¹ - x⁻¹) * (z - x))
      = (y - x) * (x - z) * (y - z) := by
    field_simp
    ring
  rw [hz0, mul_zero] at hkey
  have hne : (y - x) * (x - z) * (y - z) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hxy)) (sub_ne_zero.mpr hxz))
      (sub_ne_zero.mpr hyz)
  exact hne hkey.symm

theorem det_expand (p : ℕ) (t x y : ZMod p) (i1 j1 i2 j2 i3 j3 : Fin 2) :
    det3i (liftP p t x i1 j1) (liftP p t x i2 j2) (liftP p t y i3 j3)
      = (p : ℤ) * (((i2.val : ℤ) - (i1.val : ℤ)) * (Yv p y - Yv p x)
          - ((j2.val : ℤ) - (j1.val : ℤ)) * (Xv p t y - Xv p t x)
          + (p : ℤ) * (((i2.val : ℤ) - (i1.val : ℤ)) * ((j3.val : ℤ) - (j1.val : ℤ))
              - ((j2.val : ℤ) - (j1.val : ℤ)) * ((i3.val : ℤ) - (i1.val : ℤ)))) := by
  simp only [det3i, liftP, Xv, Yv]
  ring

theorem det_expand_main (p : ℕ) (t x y : ZMod p) (i3 j3 : Fin 2) :
    det3i (liftP p t x 0 0) (liftP p t x 1 1) (liftP p t y i3 j3)
      = (p : ℤ) * ((Yv p y - Yv p x) - (Xv p t y - Xv p t x)
          + (p : ℤ) * ((j3.val : ℤ) - (i3.val : ℤ))) := by
  simp only [det3i, liftP, Xv, Yv, e0v, e1v]
  ring

theorem det_expand_anti (p : ℕ) (t x y : ZMod p) (i3 j3 : Fin 2) :
    det3i (liftP p t x 0 1) (liftP p t x 1 0) (liftP p t y i3 j3)
      = (p : ℤ) * ((Yv p y - Yv p x) + (Xv p t y - Xv p t x)
          + (p : ℤ) * ((j3.val : ℤ) + (i3.val : ℤ) - 1)) := by
  simp only [det3i, liftP, Xv, Yv, e0v, e1v]
  ring

theorem fin2_eq_zero (a : Fin 2) (h : (a.val : ℤ) = 0) : a = 0 := by
  apply Fin.ext
  have h2 := a.isLt
  have e := e0n
  omega

theorem fin2_eq_one (a : Fin 2) (h : (a.val : ℤ) = 1) : a = 1 := by
  apply Fin.ext
  have h2 := a.isLt
  have e := e1n
  omega

theorem pair_eq {α β : Type*} {a c : α} {b d : β} (h1 : a = c) (h2 : b = d) :
    (a, b) = (c, d) := by
  rw [h1, h2]

theorem det3i_swap12 (P Q R : ℤ × ℤ) : det3i Q P R = -det3i P Q R := by
  simp [det3i]
  ring

theorem det3i_swap23 (P Q R : ℤ × ℤ) : det3i P R Q = -det3i P Q R := by
  simp [det3i]
  ring

theorem det3i_cyc (P Q R : ℤ × ℤ) : det3i Q R P = det3i P Q R := by
  simp [det3i]
  ring

theorem ne_of_swap12 {P Q R : ℤ × ℤ} (h : det3i P Q R ≠ 0) : det3i Q P R ≠ 0 := by
  intro hD
  exact h (by rw [det3i_swap12, hD, neg_zero])

theorem ne_of_swap23 {P Q R : ℤ × ℤ} (h : det3i P R Q ≠ 0) : det3i P Q R ≠ 0 := by
  intro hD
  exact h (by rw [det3i_swap23, hD, neg_zero])

theorem ne_of_cyc {P Q R : ℤ × ℤ} (h : det3i Q R P ≠ 0) : det3i P Q R ≠ 0 := by
  intro hD
  exact h (by rw [det3i_cyc, hD])

theorem main_diag (p : ℕ) [NeZero p] (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (x y : ZMod p) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) (i3 j3 : Fin 2)
    (hmA : ((0 : Fin 2), (0 : Fin 2)) ∈ mask p x)
    (hmB : ((1 : Fin 2), (1 : Fin 2)) ∈ mask p x)
    (hm3 : (i3, j3) ∈ mask p y) :
    det3i (liftP p (t0 p) x 0 0) (liftP p (t0 p) x 1 1) (liftP p (t0 p) y i3 j3) ≠ 0 := by
  haveI := Fact.mk hp
  have hp0 : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hzinv : x⁻¹ ≠ 0 := inv_ne_zero hx
  intro hD
  have hE0 := det_expand_main p (t0 p) x y i3 j3
  rw [hD] at hE0
  have hE : (Yv p y - Yv p x) - (Xv p (t0 p) y - Xv p (t0 p) x)
      + (p : ℤ) * ((j3.val : ℤ) - (i3.val : ℤ)) = 0 := by
    rcases mul_eq_zero.mp hE0.symm with h | h
    · exact absurd h hp0
    · exact h
  have hz := congrArg (fun z : ℤ => (z : ZMod p)) hE
  simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast, cast_Yv, cast_Xv,
    cast_p, ZMod.natCast_self, Int.cast_zero, Nat.cast_zero, mul_zero, zero_mul, add_zero,
    sub_zero] at hz
  have hsub : (y + t0 p) - (x + t0 p) = y - x := by ring
  rw [hsub] at hz
  have hkey : (x - y) * (1 + x * y) = x * y * ((y⁻¹ - x⁻¹) - (y - x)) := by
    field_simp
    ring
  rw [hz, mul_zero] at hkey
  have hxy1 : x * y = -1 := by
    have hne : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have h2 := (mul_eq_zero.mp hkey).resolve_left hne
    linear_combination h2
  have hyeq : y = -(x⁻¹) := by
    calc y = 1 * y := (one_mul y).symm
      _ = (x⁻¹ * x) * y := by rw [inv_mul_cancel₀ hx]
      _ = x⁻¹ * (x * y) := by ring
      _ = x⁻¹ * (-1) := by rw [hxy1]
      _ = -(x⁻¹) := by ring
  have hyinv : y⁻¹ = -x := by rw [hyeq, inv_neg, inv_inv]
  have hA := mem_mask p x 0 0 hmA
  have hB := mem_mask p x 1 1 hmB
  have hA' : ¬ ((0 : ℤ) = cI p x ∧ (0 : ℤ) = 1 - cI p (x⁻¹)) := by
    intro hc
    refine hA ((corner_eq_iff p x 0 0).mpr ⟨?_, ?_⟩)
    · rw [e0v]; exact hc.1
    · rw [e0v]; exact hc.2
  have hB' : ¬ ((1 : ℤ) = cI p x ∧ (1 : ℤ) = 1 - cI p (x⁻¹)) := by
    intro hc
    refine hB ((corner_eq_iff p x 1 1).mpr ⟨?_, ?_⟩)
    · rw [e1v]; exact hc.1
    · rw [e1v]; exact hc.2
  have hceq : cI p x = cI p (x⁻¹) := by
    rcases cI_cases p x with h1 | h1 <;> rcases cI_cases p (x⁻¹) with h2 | h2
    · exact h1.trans h2.symm
    · exfalso
      refine hA' ⟨?_, ?_⟩ <;> omega
    · exfalso
      refine hB' ⟨?_, ?_⟩ <;> omega
    · exact h1.trans h2.symm
  have hYv : Yv p y = (p : ℤ) - (x.val : ℤ) := by
    simp only [Yv, hyinv]
    exact val_neg_z p x hx
  have hXv : Xv p (t0 p) y = ((p : ℤ) - ((x⁻¹).val : ℤ)) + (hh p : ℤ) - (p : ℤ) * cI p y := by
    rw [Xv_eq p hp hp2 y, hyeq]
    have hn := val_neg_z p (x⁻¹) hzinv
    linear_combination hn
  have hXv_x : Xv p (t0 p) x = (x.val : ℤ) + (hh p : ℤ) - (p : ℤ) * cI p x :=
    Xv_eq p hp hp2 x
  have hcIy : cI p y = 1 - cI p (x⁻¹) := by
    rw [hyeq]
    exact cI_neg p hp hp2 (x⁻¹) hzinv
  have hcomb : (Yv p y - Yv p x) - (Xv p (t0 p) y - Xv p (t0 p) x)
      = (p : ℤ) * (1 - cI p (x⁻¹) - cI p x) := by
    rw [hYv, hXv, hXv_x, hcIy]
    simp only [Yv]
    ring
  have hE2 : (1 - cI p (x⁻¹) - cI p x) + ((j3.val : ℤ) - (i3.val : ℤ)) = 0 := by
    have hfac : (p : ℤ) * ((1 - cI p (x⁻¹) - cI p x)
        + ((j3.val : ℤ) - (i3.val : ℤ))) = 0 := by
      rw [hcomb] at hE
      linear_combination hE
    exact (mul_eq_zero.mp hfac).resolve_left hp0
  have hfinal : (j3.val : ℤ) - (i3.val : ℤ) = cI p x + cI p (x⁻¹) - 1 := by omega
  have h3 := mem_mask p y i3 j3 hm3
  rcases cI_cases p x with hc | hc
  · have hci : cI p (x⁻¹) = 0 := by rw [← hceq]; exact hc
    have hi3 : (i3.val : ℤ) = 1 := by
      have g1 := i3.isLt
      have g2 := j3.isLt
      omega
    have hj3 : (j3.val : ℤ) = 0 := by
      have g1 := i3.isLt
      have g2 := j3.isLt
      omega
    have hcy : cI p y = 1 := by rw [hcIy, hci]; ring
    have hcyi : cI p (y⁻¹) = 1 := by
      rw [hyinv, cI_neg p hp hp2 x hx, hc]
      ring
    apply h3
    have g1 := cI_one p y hcy
    have g2 := cI_one p (y⁻¹) hcyi
    simp only [corner, if_pos g1, if_pos g2]
    exact pair_eq (fin2_eq_one i3 hi3) (fin2_eq_zero j3 hj3)
  · have hci : cI p (x⁻¹) = 1 := by rw [← hceq]; exact hc
    have hi3 : (i3.val : ℤ) = 0 := by
      have g1 := i3.isLt
      have g2 := j3.isLt
      omega
    have hj3 : (j3.val : ℤ) = 1 := by
      have g1 := i3.isLt
      have g2 := j3.isLt
      omega
    have hcy : cI p y = 0 := by rw [hcIy, hci]; ring
    have hcyi : cI p (y⁻¹) = 0 := by
      rw [hyinv, cI_neg p hp hp2 x hx, hc]
      ring
    apply h3
    have g1 := cI_zero p y hcy
    have g2 := cI_zero p (y⁻¹) hcyi
    simp only [corner, if_neg g1, if_neg g2]
    exact pair_eq (fin2_eq_zero i3 hi3) (fin2_eq_one j3 hj3)

theorem anti_diag (p : ℕ) [NeZero p] (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (x y : ZMod p) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) (i3 j3 : Fin 2)
    (hmA : ((0 : Fin 2), (1 : Fin 2)) ∈ mask p x)
    (hmB : ((1 : Fin 2), (0 : Fin 2)) ∈ mask p x)
    (hm3 : (i3, j3) ∈ mask p y) :
    det3i (liftP p (t0 p) x 0 1) (liftP p (t0 p) x 1 0) (liftP p (t0 p) y i3 j3) ≠ 0 := by
  haveI := Fact.mk hp
  have hp0 : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hzinv : x⁻¹ ≠ 0 := inv_ne_zero hx
  intro hD
  have hE0 := det_expand_anti p (t0 p) x y i3 j3
  rw [hD] at hE0
  have hE : (Yv p y - Yv p x) + (Xv p (t0 p) y - Xv p (t0 p) x)
      + (p : ℤ) * ((j3.val : ℤ) + (i3.val : ℤ) - 1) = 0 := by
    rcases mul_eq_zero.mp hE0.symm with h | h
    · exact absurd h hp0
    · exact h
  have hz := congrArg (fun z : ℤ => (z : ZMod p)) hE
  simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast, cast_Yv, cast_Xv,
    cast_p, ZMod.natCast_self, Int.cast_zero, Nat.cast_zero, mul_zero, zero_mul, add_zero,
    sub_zero] at hz
  have hsub : (y + t0 p) - (x + t0 p) = y - x := by ring
  rw [hsub] at hz
  have hkey : (x - y) * (1 - x * y) = x * y * ((y⁻¹ - x⁻¹) + (y - x)) := by
    field_simp
    ring
  rw [hz, mul_zero] at hkey
  have hxy1 : x * y = 1 := by
    have hne : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have h2 := (mul_eq_zero.mp hkey).resolve_left hne
    exact (sub_eq_zero.mp h2).symm
  have hyeq : y = x⁻¹ := by
    calc y = 1 * y := (one_mul y).symm
      _ = (x⁻¹ * x) * y := by rw [inv_mul_cancel₀ hx]
      _ = x⁻¹ * (x * y) := by ring
      _ = x⁻¹ * 1 := by rw [hxy1]
      _ = x⁻¹ := by ring
  have hyinv : y⁻¹ = x := by rw [hyeq, inv_inv]
  have hA := mem_mask p x 0 1 hmA
  have hB := mem_mask p x 1 0 hmB
  have hA' : ¬ ((0 : ℤ) = cI p x ∧ (1 : ℤ) = 1 - cI p (x⁻¹)) := by
    intro hc
    refine hA ((corner_eq_iff p x 0 1).mpr ⟨?_, ?_⟩)
    · rw [e0v]; exact hc.1
    · rw [e1v]; exact hc.2
  have hB' : ¬ ((1 : ℤ) = cI p x ∧ (0 : ℤ) = 1 - cI p (x⁻¹)) := by
    intro hc
    refine hB ((corner_eq_iff p x 1 0).mpr ⟨?_, ?_⟩)
    · rw [e1v]; exact hc.1
    · rw [e0v]; exact hc.2
  have hcne : cI p x ≠ cI p (x⁻¹) := by
    rcases cI_cases p x with h1 | h1 <;> rcases cI_cases p (x⁻¹) with h2 | h2
    · exfalso
      refine hA' ⟨?_, ?_⟩ <;> omega
    · rw [h1, h2]; norm_num
    · rw [h1, h2]; norm_num
    · exfalso
      refine hB' ⟨?_, ?_⟩ <;> omega
  have hYv : Yv p y = (x.val : ℤ) := by
    simp only [Yv, hyinv]
  have hXv : Xv p (t0 p) y = ((x⁻¹).val : ℤ) + (hh p : ℤ) - (p : ℤ) * cI p y := by
    rw [Xv_eq p hp hp2 y, hyeq]
  have hXv_x : Xv p (t0 p) x = (x.val : ℤ) + (hh p : ℤ) - (p : ℤ) * cI p x :=
    Xv_eq p hp hp2 x
  have hcIy : cI p y = cI p (x⁻¹) := by rw [hyeq]
  have hcomb : (Yv p y - Yv p x) + (Xv p (t0 p) y - Xv p (t0 p) x)
      = (p : ℤ) * (cI p x - cI p (x⁻¹)) := by
    rw [hYv, hXv, hXv_x, hcIy]
    simp only [Yv]
    ring
  have hE2 : (cI p x - cI p (x⁻¹)) + ((j3.val : ℤ) + (i3.val : ℤ) - 1) = 0 := by
    have hfac : (p : ℤ) * ((cI p x - cI p (x⁻¹))
        + ((j3.val : ℤ) + (i3.val : ℤ) - 1)) = 0 := by
      rw [hcomb] at hE
      linear_combination hE
    exact (mul_eq_zero.mp hfac).resolve_left hp0
  have hfinal : (j3.val : ℤ) + (i3.val : ℤ) - 1 = cI p (x⁻¹) - cI p x := by omega
  have h3 := mem_mask p y i3 j3 hm3
  rcases cI_cases p x with hc | hc
  · have hci : cI p (x⁻¹) = 1 := by
      rcases cI_cases p (x⁻¹) with h2 | h2
      · exfalso
        exact hcne (by omega)
      · exact h2
    have hi3 : (i3.val : ℤ) = 1 := by
      have g1 := i3.isLt
      have g2 := j3.isLt
      omega
    have hj3 : (j3.val : ℤ) = 1 := by
      have g1 := i3.isLt
      have g2 := j3.isLt
      omega
    have hcy : cI p y = 1 := by rw [hcIy]; exact hci
    have hcyi : cI p (y⁻¹) = 0 := by rw [hyinv]; exact hc
    apply h3
    have g1 := cI_one p y hcy
    have g2 := cI_zero p (y⁻¹) hcyi
    simp only [corner, if_pos g1, if_neg g2]
    exact pair_eq (fin2_eq_one i3 hi3) (fin2_eq_one j3 hj3)
  · have hci : cI p (x⁻¹) = 0 := by
      rcases cI_cases p (x⁻¹) with h2 | h2
      · exact h2
      · exfalso
        exact hcne (by omega)
    have hi3 : (i3.val : ℤ) = 0 := by
      have g1 := i3.isLt
      have g2 := j3.isLt
      omega
    have hj3 : (j3.val : ℤ) = 0 := by
      have g1 := i3.isLt
      have g2 := j3.isLt
      omega
    have hcy : cI p y = 0 := by rw [hcIy]; exact hci
    have hcyi : cI p (y⁻¹) = 1 := by rw [hyinv]; exact hc
    apply h3
    have g1 := cI_zero p y hcy
    have g2 := cI_one p (y⁻¹) hcyi
    simp only [corner, if_neg g1, if_pos g2]
    exact pair_eq (fin2_eq_zero i3 hi3) (fin2_eq_zero j3 hj3)

theorem two_one (p : ℕ) [NeZero p] (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (x y : ZMod p) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y)
    (i1 j1 i2 j2 i3 j3 : Fin 2)
    (hm1 : (i1, j1) ∈ mask p x) (hm2 : (i2, j2) ∈ mask p x) (hm3 : (i3, j3) ∈ mask p y)
    (h12 : (i1, j1) ≠ (i2, j2)) :
    det3i (liftP p (t0 p) x i1 j1) (liftP p (t0 p) x i2 j2) (liftP p (t0 p) y i3 j3) ≠ 0 := by
  haveI := Fact.mk hp
  have hp0 : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  intro hD
  have hE0 := det_expand p (t0 p) x y i1 j1 i2 j2 i3 j3
  rw [hD] at hE0
  have hE : ((i2.val : ℤ) - (i1.val : ℤ)) * (Yv p y - Yv p x)
      - ((j2.val : ℤ) - (j1.val : ℤ)) * (Xv p (t0 p) y - Xv p (t0 p) x)
      + (p : ℤ) * (((i2.val : ℤ) - (i1.val : ℤ)) * ((j3.val : ℤ) - (j1.val : ℤ))
          - ((j2.val : ℤ) - (j1.val : ℤ)) * ((i3.val : ℤ) - (i1.val : ℤ))) = 0 := by
    rcases mul_eq_zero.mp hE0.symm with h | h
    · exact absurd h hp0
    · exact h
  have hz := congrArg (fun z : ℤ => (z : ZMod p)) hE
  simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast, cast_Yv, cast_Xv,
    cast_p, ZMod.natCast_self, Int.cast_zero, Nat.cast_zero, mul_zero, zero_mul, add_zero,
    sub_zero] at hz
  have hsub : (y + t0 p) - (x + t0 p) = y - x := by ring
  rw [hsub] at hz
  have hkey : (x - y) * ((((i2.val : ℕ) : ZMod p) - ((i1.val : ℕ) : ZMod p))
      + (((j2.val : ℕ) : ZMod p) - ((j1.val : ℕ) : ZMod p)) * (x * y))
      = x * y * ((((i2.val : ℕ) : ZMod p) - ((i1.val : ℕ) : ZMod p)) * (y⁻¹ - x⁻¹)
          - (((j2.val : ℕ) : ZMod p) - ((j1.val : ℕ) : ZMod p)) * (y - x)) := by
    field_simp
    ring
  rw [hz, mul_zero] at hkey
  have hcon : (((i2.val : ℕ) : ZMod p) - ((i1.val : ℕ) : ZMod p))
      + (((j2.val : ℕ) : ZMod p) - ((j1.val : ℕ) : ZMod p)) * (x * y) = 0 :=
    (mul_eq_zero.mp hkey).resolve_left (sub_ne_zero.mpr hxy)
  have hxy0 : x * y ≠ 0 := mul_ne_zero hx hy
  have hi : i1 ≠ i2 := by
    intro hc
    have h1 : (((i2.val : ℕ) : ZMod p) - ((i1.val : ℕ) : ZMod p)) = 0 := by
      rw [hc]; ring
    rw [h1, zero_add] at hcon
    have h2 : (((j2.val : ℕ) : ZMod p) - ((j1.val : ℕ) : ZMod p)) = 0 := by
      rcases mul_eq_zero.mp hcon with h | h
      · exact h
      · exact absurd h hxy0
    have h3 := fin2_val_inj p hp j2 j1 (sub_eq_zero.mp h2)
    exact h12 (pair_eq hc h3.symm)
  have hj : j1 ≠ j2 := by
    intro hc
    have h1 : (((j2.val : ℕ) : ZMod p) - ((j1.val : ℕ) : ZMod p)) = 0 := by
      rw [hc]; ring
    rw [h1, zero_mul, add_zero] at hcon
    have h3 := fin2_val_inj p hp i2 i1 (sub_eq_zero.mp hcon)
    exact h12 (pair_eq h3.symm hc)
  have hc2 : ∀ a : Fin 2, a = 0 ∨ a = 1 := by
    intro a
    fin_cases a <;> tauto
  rcases hc2 i1 with rfl | rfl <;> rcases hc2 i2 with rfl | rfl <;>
    rcases hc2 j1 with rfl | rfl <;> rcases hc2 j2 with rfl | rfl <;>
    first
      | exact absurd rfl hi
      | exact absurd rfl hj
      | exact main_diag p hp hp2 x y hx hy hxy i3 j3 hm1 hm2 hm3 hD
      | exact anti_diag p hp hp2 x y hx hy hxy i3 j3 hm1 hm2 hm3 hD
      | exact ne_of_swap12 (main_diag p hp hp2 x y hx hy hxy i3 j3 hm2 hm1 hm3) hD
      | exact ne_of_swap12 (anti_diag p hp hp2 x y hx hy hxy i3 j3 hm2 hm1 hm3) hD

theorem mem_pts (p : ℕ) [NeZero p] (t : ZMod p) (R : ZMod p → Finset (Fin 2 × Fin 2))
    {a : ℤ × ℤ} (h : a ∈ pts p t R) :
    ∃ x : ZMod p, x ≠ 0 ∧ ∃ i j : Fin 2, (i, j) ∈ R x ∧ a = liftP p t x i j := by
  rw [pts, Finset.mem_biUnion] at h
  obtain ⟨x, hx, h⟩ := h
  rw [Finset.mem_filter] at hx
  obtain ⟨u, hx0⟩ := hx
  obtain ⟨ij, hij, h⟩ := Finset.mem_image.mp h
  exact ⟨x, hx0, ij.1, ij.2, hij, h.symm⟩

theorem no_three (p : ℕ) [NeZero p] (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    ∀ a ∈ pts p (t0 p) (mask p), ∀ b ∈ pts p (t0 p) (mask p), ∀ c ∈ pts p (t0 p) (mask p),
      a ≠ b → a ≠ c → b ≠ c → det3i a b c ≠ 0 := by
  intro a ha b hb c hc hab hac hbc
  obtain ⟨x, hx0, i1, j1, hm1, rfl⟩ := mem_pts p (t0 p) (mask p) ha
  obtain ⟨y, hy0, i2, j2, hm2, rfl⟩ := mem_pts p (t0 p) (mask p) hb
  obtain ⟨z, hz0, i3, j3, hm3, rfl⟩ := mem_pts p (t0 p) (mask p) hc
  by_cases hxy : x = y
  · by_cases hxz : x = z
    · have h12 : (i1, j1) ≠ (i2, j2) := by
        intro hc2
        apply hab
        rw [hxy]
        have e1 : i1 = i2 := congrArg Prod.fst hc2
        have e2 : j1 = j2 := congrArg Prod.snd hc2
        rw [e1, e2]
      have h13 : (i1, j1) ≠ (i3, j3) := by
        intro hc2
        apply hac
        rw [hxz]
        have e1 : i1 = i3 := congrArg Prod.fst hc2
        have e2 : j1 = j3 := congrArg Prod.snd hc2
        rw [e1, e2]
      have h23 : (i2, j2) ≠ (i3, j3) := by
        intro hc2
        apply hbc
        rw [← hxy, ← hxz]
        have e1 : i2 = i3 := congrArg Prod.fst hc2
        have e2 : j2 = j3 := congrArg Prod.snd hc2
        rw [e1, e2]
      have hmain := det3i_same p hp (t0 p) x i1 j1 i2 j2 i3 j3 h12 h13 h23
      rw [← hxy, ← hxz]
      exact hmain
    · have h12 : (i1, j1) ≠ (i2, j2) := by
        intro hc2
        apply hab
        rw [hxy]
        have e1 : i1 = i2 := congrArg Prod.fst hc2
        have e2 : j1 = j2 := congrArg Prod.snd hc2
        rw [e1, e2]
      have hm2' : (i2, j2) ∈ mask p x := by rw [hxy]; exact hm2
      have hmain := two_one p hp hp2 x z hx0 hz0 hxz i1 j1 i2 j2 i3 j3 hm1 hm2' hm3 h12
      rw [← hxy]
      exact hmain
  · by_cases hxz : x = z
    · have h13 : (i1, j1) ≠ (i3, j3) := by
        intro hc2
        apply hac
        rw [hxz]
        have e1 : i1 = i3 := congrArg Prod.fst hc2
        have e2 : j1 = j3 := congrArg Prod.snd hc2
        rw [e1, e2]
      have hm3' : (i3, j3) ∈ mask p x := by rw [hxz]; exact hm3
      have hmain := two_one p hp hp2 x y hx0 hy0 hxy i1 j1 i3 j3 i2 j2 hm1 hm3' hm2 h13
      have hmain2 := ne_of_swap23 hmain
      rw [← hxz]
      exact hmain2
    · by_cases hyz : y = z
      · have h23 : (i2, j2) ≠ (i3, j3) := by
          intro hc2
          apply hbc
          rw [hyz]
          have e1 : i2 = i3 := congrArg Prod.fst hc2
          have e2 : j2 = j3 := congrArg Prod.snd hc2
          rw [e1, e2]
        have hm3'' : (i3, j3) ∈ mask p y := by rw [hyz]; exact hm3
        have hmain := two_one p hp hp2 y x hy0 hx0 (Ne.symm hxy) i2 j2 i3 j3 i1 j1 hm2 hm3''
          hm1 h23
        have hmain2 := ne_of_cyc hmain
        rw [← hyz]
        exact hmain2
      · exact det3i_three p hp (t0 p) x y z hx0 hy0 hz0 hxy hxz hyz i1 j1 i2 j2 i3 j3

theorem mask_card (p : ℕ) (x : ZMod p) : (mask p x).card = 3 := by
  have h : (mask p x).card = (Finset.univ : Finset (Fin 2 × Fin 2)).card - 1 := by
    rw [mask]
    exact Finset.card_erase_of_mem (Finset.mem_univ (corner p x))
  rw [h]
  decide

theorem count (p : ℕ) [NeZero p] :
    (∑ x ∈ Finset.univ.filter (fun x : ZMod p => x ≠ 0), (mask p x).card) = 3 * (p - 1) := by
  have h : ∀ x ∈ Finset.univ.filter (fun x : ZMod p => x ≠ 0), (mask p x).card = 3 :=
    fun x _ => mask_card p x
  rw [Finset.sum_const_nat h]
  have hc : ((Finset.univ : Finset (ZMod p)).filter (fun x => x ≠ 0)).card = p - 1 := by
    have he : (Finset.univ : Finset (ZMod p)).filter (fun x => x ≠ 0)
        = Finset.univ.erase 0 := by
      ext x
      simp
    rw [he, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card]
  rw [hc, Nat.mul_comm]

end Conjectures.NoThreeInLine.FoldOptimalityAttained_aux

open Conjectures.NoThreeInLine.FoldOptimalityAttained_aux

theorem Conjectures.NoThreeInLine.FoldOptimalityAttained : ∀ (p : ℕ) [NeZero p] (hp : Nat.Prime p), p ≠ 2 → (let det3 : ℤ × ℤ → ℤ × ℤ → ℤ × ℤ → ℤ := fun P Q R => (Q.1 - P.1) * (R.2 - P.2) - (Q.2 - P.2) * (R.1 - P.1); let cap : ZMod p → ZMod p → ZMod p × ZMod p := fun t x => (x + t, x⁻¹); let lift : ZMod p → ZMod p → Fin 2 → Fin 2 → ℤ × ℤ := fun t x i j => (((cap t x).1.val : ℤ) + (i.val : ℤ) * (p : ℤ), ((cap t x).2.val : ℤ) + (j.val : ℤ) * (p : ℤ)); let Mask : Type := ZMod p → Finset (Fin 2 × Fin 2); let points : ZMod p → Mask → Finset (ℤ × ℤ) := fun t R => (Finset.univ.filter (fun x : ZMod p => x ≠ 0)).biUnion (fun x => (R x).image (fun ij => lift t x ij.1 ij.2)); let NoThreeCollinear : Finset (ℤ × ℤ) → Prop := fun S => ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c → det3 a b c ≠ 0; ∃ t : ZMod p, ∃ R : Mask, NoThreeCollinear (points t R) ∧ (∑ x ∈ Finset.univ.filter (fun x : ZMod p => x ≠ 0), (R x).card) = 3 * (p - 1)) := by
  intro p _ hp hp2
  refine ⟨t0 p, mask p, ?_, ?_⟩
  · exact no_three p hp hp2
  · exact count p
