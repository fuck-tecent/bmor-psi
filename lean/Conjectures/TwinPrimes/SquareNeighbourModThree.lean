import Mathlib

theorem Conjectures.TwinPrimes.SquareNeighbourModThree :
    (∀ n : ℕ, 10 ≤ n → ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2) ≠ 0 → (¬ n.Prime ∨ ¬ (n+2).Prime) → (∃ p a : ℕ, p.Prime ∧ 3 ≤ a ∧ (p^a=n ∨ p^a=n+2)) ∨ (n.Prime ∧ ∃ p : ℕ, p.Prime ∧ p^2=n+2)) := by
  intro n hN hNonzero hBad
  obtain ⟨hL, hR⟩ := mul_ne_zero_iff.mp hNonzero
  obtain ⟨p, a, hp, ha, hPowL⟩ :=
    (isPrimePow_nat_iff n).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hL)
  obtain ⟨q, b, hq, hb, hPowR⟩ :=
    (isPrimePow_nat_iff (n+2)).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hR)
  by_cases haLarge : 3 ≤ a
  · exact Or.inl ⟨p, a, hp, haLarge, Or.inl hPowL⟩
  by_cases hbLarge : 3 ≤ b
  · exact Or.inl ⟨q, b, hq, hbLarge, Or.inr hPowR⟩
  by_cases hNPrime : n.Prime
  · have hNotPrime : ¬(n+2).Prime := hBad.resolve_left (fun h => h hNPrime)
    have hNotOne : b ≠ 1 := by
      intro h
      apply hNotPrime
      rwa [← hPowR, h, pow_one]
    have hTwo : b = 2 := by omega
    exact Or.inr ⟨hNPrime, q, hq, by simpa only [hTwo] using hPowR⟩
  · have hNotOne : a ≠ 1 := by
      intro h
      apply hNPrime
      rwa [← hPowL, h, pow_one]
    have hTwo : a = 2 := by omega
    have hSquare : p^2 = n := by simpa only [hTwo] using hPowL
    have hp3 : p ≠ 3 := by
      rintro rfl
      norm_num at hSquare
      omega
    have hNotZero : p % 3 ≠ 0 := by
      intro h
      exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.dvd_of_mod_eq_zero h)).symm
    have hRem : (p^2+2) % 3 = 0 := by
      rw [Nat.add_mod, pow_two, Nat.mul_mod p p 3]
      have hSmall := Nat.mod_lt p (by decide : 0 < 3)
      interval_cases (p % 3) <;> norm_num at *
    have hDiv : 3 ∣ q^b := by
      rw [hPowR, ← hSquare]
      exact Nat.dvd_of_mod_eq_zero hRem
    have hq3 : q = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp
      (Nat.prime_three.dvd_of_dvd_pow hDiv)).symm
    have hUpper := Nat.pow_le_pow_right hq.pos (show b ≤ 2 by omega)
    rw [hPowR, hq3] at hUpper
    norm_num at hUpper
    omega
