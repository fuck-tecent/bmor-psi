import Mathlib

theorem PEqualNP.Outside.L_goldbach_minor_type_two_lcm_gcd_budget :
    ∀ (Y : ℕ),
      (∑ d ∈ Finset.Icc 1 Y, ∑ e ∈ Finset.Icc 1 Y, (1 : ℝ) / (Nat.lcm d e : ℝ)) ≤
        (1 + Real.log (max 1 Y)) ^ 3 := by
  intro Y
  let indices := Finset.Icc 1 Y
  let reciprocal (d : ℕ) : ℝ := 1 / (d : ℝ)
  let gcdCoordinates (pair : ℕ × ℕ) : ℕ × ℕ × ℕ :=
    (pair.1.gcd pair.2, pair.1 / pair.1.gcd pair.2, pair.2 / pair.1.gcd pair.2)
  let tripleWeight (triple : ℕ × ℕ × ℕ) : ℝ :=
    reciprocal triple.1 * (reciprocal triple.2.1 * reciprocal triple.2.2)
  have reconstruct : Function.LeftInverse
      (fun triple : ℕ × ℕ × ℕ => (triple.1 * triple.2.1, triple.1 * triple.2.2))
      gcdCoordinates := by
    rintro ⟨d, e⟩
    change (d.gcd e * (d / d.gcd e), d.gcd e * (e / d.gcd e)) = (d, e)
    rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left d e),
      Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)]
  have coordinatesInRange :
      (indices ×ˢ indices).image gcdCoordinates ⊆ indices ×ˢ (indices ×ˢ indices) := by
    intro triple membership
    obtain ⟨⟨d, e⟩, pairMembership, rfl⟩ := Finset.mem_image.mp membership
    obtain ⟨hd, he⟩ := Finset.mem_product.mp pairMembership
    obtain ⟨dPositive, dLe⟩ : 0 < d ∧ d ≤ Y := Finset.mem_Icc.mp hd
    obtain ⟨ePositive, eLe⟩ : 0 < e ∧ e ≤ Y := Finset.mem_Icc.mp he
    have gcdPositive : 0 < d.gcd e := Nat.gcd_pos_of_pos_left e dPositive
    have gcdLeD := Nat.gcd_le_left e dPositive
    have gcdLeE := Nat.gcd_le_right d ePositive
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨gcdPositive, gcdLeD.trans dLe⟩,
        Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨Nat.div_pos gcdLeD gcdPositive, (Nat.div_le_self d _).trans dLe⟩,
            Finset.mem_Icc.mpr ⟨Nat.div_pos gcdLeE gcdPositive, (Nat.div_le_self e _).trans eLe⟩⟩⟩
  have harmonicBound :
      (∑ d ∈ indices, reciprocal d) ≤ 1 + Real.log (max 1 Y) := by
    by_cases zero : Y = 0
    · subst Y
      norm_num [indices]
    · have oneLe : (1 : ℝ) ≤ Y := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr zero)
      rw [max_eq_right oneLe]
      simpa only [indices, reciprocal, one_div, harmonic_eq_sum_Icc, Rat.cast_sum,
        Rat.cast_inv, Rat.cast_natCast] using harmonic_le_one_add_log Y
  have harmonicNonnegative : 0 ≤ ∑ d ∈ indices, reciprocal d := by
    exact Finset.sum_nonneg fun d _ => by positivity
  change (∑ d ∈ indices, ∑ e ∈ indices, (1 : ℝ) / (Nat.lcm d e : ℝ)) ≤ _
  calc
    _ = ∑ pair ∈ indices ×ˢ indices, (1 : ℝ) / (Nat.lcm pair.1 pair.2 : ℝ) :=
      (Finset.sum_product _ _ _).symm
    _ ≤ ∑ triple ∈ indices ×ˢ (indices ×ˢ indices), tripleWeight triple := by
      apply Finset.sum_le_sum_of_injOn gcdCoordinates reconstruct.injective.injOn coordinatesInRange
      · rintro ⟨d, e⟩ membership
        have dPositive : 0 < d := (Finset.mem_Icc.mp (Finset.mem_product.mp membership).1).1
        have gcdPositive : 0 < d.gcd e := Nat.gcd_pos_of_pos_left e dPositive
        have lcmFactorization : d.lcm e = d.gcd e * (d / d.gcd e * (e / d.gcd e)) := by
          apply mul_right_cancel₀ gcdPositive.ne'
          calc
            d.lcm e * d.gcd e = d * e := Nat.lcm_mul_gcd d e
            _ = (d.gcd e * (d / d.gcd e)) * (d.gcd e * (e / d.gcd e)) := by
              rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left d e),
                Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)]
            _ = _ := by ac_rfl
        simp only [tripleWeight, reciprocal, gcdCoordinates, lcmFactorization, Nat.cast_mul,
          one_div_mul_one_div, le_refl]
      · intro triple _ _
        dsimp [tripleWeight, reciprocal]
        positivity
    _ = (∑ d ∈ indices, reciprocal d) ^ 3 := by
      simp only [Finset.sum_product, tripleWeight, ← Finset.mul_sum, ← Finset.sum_mul]
      ring
    _ ≤ (1 + Real.log (max 1 Y)) ^ 3 := pow_le_pow_left₀ harmonicNonnegative harmonicBound 3
