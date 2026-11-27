import Mathlib

theorem PEqualNP.Outside.L_goldbach_characters_low_conductor_card :
    ∀ (n : ℕ) [NeZero n], 2<n → let odd := (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1); ∀ d : ℕ, d∣n → 2<d → 2*(odd.filter (fun χ => χ.conductor ∣ d)).card = d.totient := by
  classical
  intro n _ _
  dsimp only
  intro d hd hdgt
  have : NeZero d := ⟨by omega⟩
  let O := (Finset.univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ (-1) = -1)
  have parity (χ : DirichletCharacter ℂ d) :
      DirichletCharacter.changeLevel hd χ (-1) = χ (-1) := by
    simpa using χ.changeLevel_eq_cast_of_dvd' hd (a := (-1 : ℤ)) ⟨-1, 0, by ring⟩
  have image_eq : O.image (DirichletCharacter.changeLevel hd) =
      ((Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1)).filter
        (fun χ => χ.conductor ∣ d) := by
    ext χ
    simp only [O, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨ψ, hψ, rfl⟩
      exact ⟨(parity ψ).trans hψ, by
        rw [DirichletCharacter.conductor_changeLevel]
        exact ψ.conductor_dvd_level⟩
    · rintro ⟨hχ, hcond⟩
      have hfac := (χ.mem_conductorSet_iff_conductor_dvd hd).mpr hcond
      obtain ⟨_, ψ, heq⟩ := hfac
      exact ⟨ψ, (parity ψ).symm.trans (heq ▸ hχ), heq.symm⟩
  rw [← image_eq, Finset.card_image_of_injective _ (DirichletCharacter.changeLevel_injective hd)]
  have hne : (-1 : ZMod d) ≠ 1 := by
    rw [Ne, ZMod.neg_one_eq_one_iff]
    omega
  have hcount : 2 * (O.card : ℂ) = (d.totient : ℂ) := calc
    _ = ∑ χ ∈ O, (2 : ℂ) := by simp [mul_comm]
    _ = ∑ χ : DirichletCharacter ℂ d, (1 - χ (-1)) := by
      unfold O
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro χ _
      rcases χ.even_or_odd with h | h
      · rw [show χ (-1) = 1 from h]
        norm_num
      · rw [show χ (-1) = -1 from h]
        norm_num
    _ = _ := by
      rw [Finset.sum_sub_distrib, DirichletCharacter.sum_characters_eq_zero ℂ hne]
      simp [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  exact_mod_cast hcount
