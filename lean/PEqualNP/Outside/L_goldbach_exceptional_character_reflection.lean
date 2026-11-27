import Mathlib

theorem PEqualNP.Outside.L_goldbach_exceptional_character_reflection :
    ∀ (d n : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d), d ∣ n → χ^2 = 1 →
      (∑ a : (ZMod d)ˣ, χ (a : ZMod d) * χ ((n : ZMod d) - (a : ZMod d))) =
        (Nat.totient d : ℂ) * χ (-1) := by
  intro d n _ χ hdn hsq
  have hn : (n : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff n d).mpr hdn
  have hχa (a : (ZMod d)ˣ) : χ (a : ZMod d) * χ (a : ZMod d) = 1 := by
    have h := DFunLike.congr_fun hsq (a : ZMod d)
    simpa [pow_two, MonoidHom.mul_apply] using h
  calc
    (∑ a : (ZMod d)ˣ, χ (a : ZMod d) * χ ((n : ZMod d) - (a : ZMod d)))
        = ∑ _a : (ZMod d)ˣ, χ (-1) := by
          apply Finset.sum_congr rfl
          intro a _
          have hna : (n : ZMod d) - (a : ZMod d) = (-1 : ZMod d) * (a : ZMod d) := by
            rw [hn]
            ring
          rw [hna, map_mul]
          calc χ (a : ZMod d) * (χ (-1) * χ (a : ZMod d))
              = χ (-1) * (χ (a : ZMod d) * χ (a : ZMod d)) := by ring
            _ = χ (-1) * 1 := by rw [hχa a]
            _ = χ (-1) := by ring
    _ = (Nat.totient d : ℂ) * χ (-1) := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient]
          simp [nsmul_eq_mul]