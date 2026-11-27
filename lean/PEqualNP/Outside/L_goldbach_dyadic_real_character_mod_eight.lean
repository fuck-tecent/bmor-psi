import Mathlib

/- The iteration b ↦ t - 2b² gains a factor of two in the error at each step. -/
private theorem dyadicApproximation (t : ℤ) (k : ℕ) :
    ∃ b : ℤ, (2 : ℤ)^k ∣ t - (b + 2*b^2) := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨b, c, hc⟩ := ih
    let b' := t - 2*b^2
    refine ⟨b', -c * (b' + b), ?_⟩
    calc
      t - (b' + 2*b'^2) = -2 * (t - (b + 2*b^2)) * (b' + b) := by dsimp [b']; ring
      _ = 2^(k+1) * (-c * (b' + b)) := by rw [hc, pow_succ]; ring

/- Writing a = 1 + 8t reduces the search for a square root 1 + 4b to
   solving b + 2b² ≡ t. -/
private theorem squareOfOneModEight (a : ℤ) (ha : (a : ZMod 8) = 1) (k : ℕ) :
    ∃ y : ZMod (2^k), y^2 = a := by
  obtain ⟨t, ht⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 a 8).mp (by simpa using ha.symm)
  obtain ⟨b, c, hc⟩ := dyadicApproximation t k
  refine ⟨((1 + 4*b : ℤ) : ZMod (2^k)), ?_⟩
  rw [← Int.cast_pow, ZMod.intCast_eq_intCast_iff_dvd_sub]
  refine ⟨8*c, ?_⟩
  push_cast
  linear_combination ht + 8 * hc

theorem PEqualNP.Outside.L_goldbach_dyadic_real_character_mod_eight :
    ∀ (k : ℕ), 3 ≤ k → ∀ χ : DirichletCharacter ℂ (2^k), χ^2 = 1 → ∃ χ₈ : DirichletCharacter ℂ 8, ∀ a : ℕ, χ (a : ZMod (2^k)) = χ₈ (a : ZMod 8) := by
  intro k hk χ hχ
  have hd : 8 ∣ 2^k := pow_dvd_pow 2 hk
  have hf : χ.FactorsThrough 8 := by
    apply (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).2
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    have h8 : (((u : ZMod (2^k)).val : ℕ) : ZMod 8) = 1 := by
      rw [← ZMod.cast_natCast hd, ZMod.natCast_zmod_val, ← ZMod.unitsMap_val hd, hu]
      rfl
    obtain ⟨y, hy⟩ := squareOfOneModEight (u : ZMod (2^k)).val (by simpa using h8) k
    have hyu : y^2 = (u : ZMod (2^k)) := by simpa using hy
    have hyUnit : IsUnit y := (isUnit_pow_iff two_ne_zero).mp (hyu.symm ▸ u.isUnit)
    apply Units.ext
    rw [MulChar.coe_toUnitHom, Units.val_one, ← hyu, map_pow,
      ← MulChar.pow_apply' χ two_ne_zero, hχ, MulChar.one_apply hyUnit]
  obtain ⟨_, χ₈, heq⟩ := hf
  refine ⟨χ₈, fun a ↦ ?_⟩
  by_cases ha : IsUnit (a : ZMod (2^k))
  · rw [heq, ← ha.unit_spec, DirichletCharacter.changeLevel_eq_cast_of_dvd,
      ha.unit_spec, ZMod.cast_natCast hd]
  · have ha8 : ¬ IsUnit (a : ZMod 8) := by
      simpa only [ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_two (by omega : 0 < k),
        ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_two (by decide : 0 < 3)] using ha
    rw [χ.map_nonunit ha, χ₈.map_nonunit ha8]
