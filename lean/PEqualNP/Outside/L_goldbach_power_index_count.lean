import Mathlib

theorem PEqualNP.Outside.L_goldbach_power_index_count :
    ∀ X : ℕ, let T := (Finset.range (X+1)).filter (fun k => ArithmeticFunction.vonMangoldt k ≠ 0 ∧ ¬ Nat.Prime k); T.card ≤ (Nat.sqrt X+1)*(Nat.log 2 X+1) := by
  intro X
  dsimp only
  let T : Finset ℕ := (Finset.range (X + 1)).filter
      (fun k => ArithmeticFunction.vonMangoldt k ≠ 0 ∧ ¬ Nat.Prime k)
  let B : Finset (ℕ × ℕ) :=
      (Finset.range (Nat.sqrt X + 1)).product (Finset.range (Nat.log 2 X + 1))
  have hsub : T ⊆ B.image (fun z : ℕ × ℕ => z.1 ^ z.2) := by
    intro k hk
    have hkX : k ≤ X := by
      have := (Finset.mem_filter.mp hk).1
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp this)
    have hΛ : ArithmeticFunction.vonMangoldt k ≠ 0 := (Finset.mem_filter.mp hk).2.1
    have hknot : ¬ Nat.Prime k := (Finset.mem_filter.mp hk).2.2
    have hpp : IsPrimePow k := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
    rcases hpp with ⟨p, j, hp, hj, hpj⟩
    have hpN : Nat.Prime p := Nat.prime_iff.mpr hp
    have hj2 : 2 ≤ j := by
      by_contra h
      have hj1 : j = 1 := by omega
      subst j
      simp at hpj
      exact hknot (hpj ▸ hpN)
    have hp2 : p ^ 2 ≤ X := by
      calc
        p ^ 2 ≤ p ^ j := by
          exact pow_le_pow_right₀ (by exact_mod_cast (Nat.Prime.one_le hpN)) hj2
        _ = k := hpj
        _ ≤ X := hkX
    have hpsqrt : p ≤ Nat.sqrt X := (Nat.le_sqrt).mpr (by simpa [pow_two] using hp2)
    have h2j : 2 ^ j ≤ X := by
      calc
        2 ^ j ≤ p ^ j := Nat.pow_le_pow_left (Nat.Prime.two_le hpN) j
        _ = k := hpj
        _ ≤ X := hkX
    have hjlog : j ≤ Nat.log 2 X := Nat.le_log_of_pow_le (by omega) h2j
    apply Finset.mem_image.mpr
    refine ⟨(p, j), ?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hpsqrt),
         Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hjlog)⟩
    · exact hpj
  calc
    T.card ≤ (B.image (fun z : ℕ × ℕ => z.1 ^ z.2)).card := Finset.card_le_card hsub
    _ ≤ B.card := Finset.card_image_le
    _ = (Nat.sqrt X + 1) * (Nat.log 2 X + 1) := by
      simp [B]
