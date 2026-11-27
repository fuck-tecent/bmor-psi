import Mathlib

theorem PEqualNP.Outside.L_goldbach_conductor_exception_small_level :
    ∀ (n : ℕ) [NeZero n], 2<n → let odd := (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1); ∀ d:ℕ, d∣n → d≤2 → (odd.filter (fun χ => χ.conductor ∣ d)).card=0 := by
  intro n _ hn
  dsimp only
  classical
  intro d hd hdt
  let odd := (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1)
  let bad := odd.filter (fun χ => χ.conductor ∣ d)
  change bad.card = 0
  rw [Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro χ hχ
  have hχodd := hχ
  intro hcdiv
  have hodd : χ (-1) = -1 := by simpa [odd] using hχodd
  have hcpos : 0 < χ.conductor := Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hdpos : 0 < d := by
    by_contra h
    have hzero : d = 0 := by omega
    subst d
    simp at hd
    exact (NeZero.ne n) hd
  have hcle : χ.conductor ≤ d := Nat.le_of_dvd hdpos hcdiv
  have hc_cases : χ.conductor = 1 ∨ χ.conductor = 2 := by omega
  have hunit : IsCoprime (-1 : ℤ) (n : ℤ) := ⟨-1, 0, by ring⟩
  have hprim : χ.primitiveCharacter (-1) = -1 := by
    have heq := χ.primitiveCharacter_apply_of_isCoprime hunit
    simpa using heq.trans (by simpa using hodd)
  rcases hc_cases with hc | hc
  · have hcast : ((-1 : ℤ) : ZMod χ.conductor) = 1 := by
      rw [hc]
      exact Subsingleton.elim _ _
    have hval := congrArg (fun x : ZMod χ.conductor => χ.primitiveCharacter x) hcast
    have hval' : χ.primitiveCharacter (-1) = χ.primitiveCharacter (1 : ℤ) := by simpa using hval
    have hne : (-1 : ℂ) ≠ 1 := by norm_num
    exact hne (hprim.symm.trans (hval'.trans (by simp)))
  · have hcast : ((-1 : ℤ) : ZMod χ.conductor) = 1 := by
      rw [hc]
      decide
    have hval := congrArg (fun x : ZMod χ.conductor => χ.primitiveCharacter x) hcast
    have hval' : χ.primitiveCharacter (-1) = χ.primitiveCharacter (1 : ℤ) := by simpa using hval
    have hne : (-1 : ℂ) ≠ 1 := by norm_num
    exact hne (hprim.symm.trans (hval'.trans (by simp)))
