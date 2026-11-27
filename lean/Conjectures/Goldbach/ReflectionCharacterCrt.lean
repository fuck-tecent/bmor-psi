import Mathlib

private theorem localProduct {m d : ℕ} [NeZero m] [NeZero d] (h : m.Coprime d)
    (χ : DirichletCharacter ℂ m) (ξ : DirichletCharacter ℂ d) (y : ZMod (m*d)) :
    (χ.changeLevel (Nat.dvd_mul_right m d) * ξ.changeLevel (Nat.dvd_mul_left d m)) y =
      χ ((ZMod.chineseRemainder h y).1) * ξ ((ZMod.chineseRemainder h y).2) := by
  let e := ZMod.chineseRemainder h
  have fstEq (z : ZMod (m*d)) : (e z).1 = (ZMod.cast z : ZMod m) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z, map_natCast]
    rw [← ZMod.natCast_zmod_val z, ZMod.cast_natCast (Nat.dvd_mul_right m d)]
    simp
  have sndEq (z : ZMod (m*d)) : (e z).2 = (ZMod.cast z : ZMod d) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z, map_natCast]
    rw [← ZMod.natCast_zmod_val z, ZMod.cast_natCast (Nat.dvd_mul_left d m)]
    simp
  change _ = χ (e y).1 * ξ (e y).2
  by_cases hy : IsUnit y
  · obtain ⟨u,rfl⟩ := hy
    rw [MulChar.mul_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd,
      DirichletCharacter.changeLevel_eq_cast_of_dvd, fstEq, sndEq]
  · rw [MulChar.map_nonunit _ hy]
    by_cases hm : IsUnit (e y).1
    · have hd : ¬IsUnit (e y).2 := fun hh => hy (by simpa using (Prod.isUnit_iff.mpr ⟨hm,hh⟩).map e.symm)
      simp [MulChar.map_nonunit ξ hd]
    · simp [MulChar.map_nonunit χ hm]

set_option maxHeartbeats 1200000 in
theorem Conjectures.Goldbach.ReflectionCharacterCrt : let H := fun (m : ℕ) [NeZero m] (N : ℕ) (χ ψ : DirichletCharacter ℂ m) =>
  (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ ((N : ZMod m) - (x : ZMod m))) / (m.totient : ℂ)
∀ (m d : ℕ) [NeZero m] [NeZero d] (N : ℕ), m.Coprime d →
  ∀ (χ ψ : DirichletCharacter ℂ m) (ξ η : DirichletCharacter ℂ d),
    H (m*d) N
      (χ.changeLevel (Nat.dvd_mul_right m d) * ξ.changeLevel (Nat.dvd_mul_left d m))
      (ψ.changeLevel (Nat.dvd_mul_right m d) * η.changeLevel (Nat.dvd_mul_left d m)) =
      H m N χ ψ * H d N ξ η := by
  classical
  dsimp only
  intro m d _ _ N h χ ψ ξ η
  let e := ZMod.chineseRemainder h
  let u : (ZMod (m*d))ˣ ≃* (ZMod m)ˣ × (ZMod d)ˣ := (Units.mapEquiv e.toMulEquiv).trans MulEquiv.prodUnits
  let f := fun x : (ZMod m)ˣ => star (χ (x : ZMod m)) * ψ ((N : ZMod m) - (x : ZMod m))
  let g := fun x : (ZMod d)ˣ => star (ξ (x : ZMod d)) * η ((N : ZMod d) - (x : ZMod d))
  have sumEq : (∑ x : (ZMod (m*d))ˣ,
      star ((χ.changeLevel (Nat.dvd_mul_right m d) * ξ.changeLevel (Nat.dvd_mul_left d m)) (x : ZMod (m*d))) *
      ((ψ.changeLevel (Nat.dvd_mul_right m d) * η.changeLevel (Nat.dvd_mul_left d m)) ((N : ZMod (m*d)) - (x : ZMod (m*d))))) =
      (∑ x, f x) * (∑ y, g y) := by
    calc
      _ = ∑ x : (ZMod (m*d))ˣ, f (u x).1 * g (u x).2 := by
        apply Finset.sum_congr rfl
        intro x _
        rw [localProduct h χ ξ (x : ZMod (m*d)), localProduct h ψ η ((N : ZMod (m*d)) - (x : ZMod (m*d))), map_sub, map_natCast]
        change star (χ ((e (x : ZMod (m*d))).1) * ξ ((e (x : ZMod (m*d))).2)) *
          (ψ ((N : ZMod m) - (e (x : ZMod (m*d))).1) * η ((N : ZMod d) - (e (x : ZMod (m*d))).2)) =
          (star (χ ((e (x : ZMod (m*d))).1)) * ψ ((N : ZMod m) - (e (x : ZMod (m*d))).1)) *
          (star (ξ ((e (x : ZMod (m*d))).2)) * η ((N : ZMod d) - (e (x : ZMod (m*d))).2))
        rw [star_mul]
        ring
      _ = ∑ xy : (ZMod m)ˣ × (ZMod d)ˣ, f xy.1 * g xy.2 :=
        u.toEquiv.sum_comp (fun xy => f xy.1 * g xy.2)
      _ = _ := by rw [Fintype.sum_prod_type]; simp only [Finset.mul_sum, Finset.sum_mul]; exact Finset.sum_comm
  rw [sumEq, Nat.totient_mul h, Nat.cast_mul]
  change _ = (∑ x, f x) / _ * ((∑ y, g y) / _)
  exact (div_mul_div_comm _ _ _ _).symm
