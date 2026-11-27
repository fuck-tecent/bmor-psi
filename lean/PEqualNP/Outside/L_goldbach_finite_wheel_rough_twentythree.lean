import Mathlib

set_option maxRecDepth 6000 in
theorem PEqualNP.Outside.L_goldbach_finite_wheel_rough_twentythree :
    ∀ n : ℕ, 210235 ≤ n → Even n → ∃ p : ℕ, Nat.Prime p ∧ p ≤ 210233 ∧ 2 ≤ n-p ∧ Nat.Coprime (n-p) 9699690 := by
  let row : Fin 4 → Fin 6 → ℕ := ![
    ![31, 61, 151, 181, 211, 331], ![7, 37, 67, 97, 127, 157],
    ![11, 41, 71, 101, 131, 191], ![17, 47, 107, 137, 167, 197]]
  let modulus : Fin 5 → ℕ := ![7, 11, 13, 17, 19]
  have hprime : ∀ g i, Nat.Prime (row g i) ∧ row g i ≤ 331 ∧ row g i % 2 = 1 := by
    decide
  -- The four rows represent the classes 1, 7, 11 and 17 modulo 30.
  have hrow : ∀ x : Fin 3, ∀ y : Fin 5, ∃ g, ∀ i,
      x.val ≠ row g i % 3 ∧ y.val ≠ row g i % 5 := by decide
  have hdistinct : ∀ g j i k, row g i % modulus j = row g k % modulus j → i = k := by
    decide
  intro n hn he
  obtain ⟨g, hg⟩ := hrow ⟨n % 3, Nat.mod_lt _ (by decide)⟩ ⟨n % 5, Nat.mod_lt _ (by decide)⟩
  -- Each remaining wheel prime rules out at most one of the six entries.
  have hgood : ∃ i, ∀ j, n % modulus j ≠ row g i % modulus j := by
    by_contra! h
    choose f hf using h
    have hinj : Function.Injective f := by
      intro i k hik
      apply hdistinct g (f i)
      calc
        row g i % modulus (f i) = n % modulus (f i) := (hf i).symm
        _ = row g k % modulus (f i) := by simpa only [hik] using hf k
    have hcard := Fintype.card_le_of_injective f hinj
    norm_num at hcard
  obtain ⟨i, hi⟩ := hgood
  obtain ⟨hp, hsmall, hodd⟩ := hprime g i
  refine ⟨row g i, hp, by omega, by omega, ?_⟩
  have cop (q : ℕ) (hq : q.Prime) (hne : n % q ≠ row g i % q) :
      Nat.Coprime (n - row g i) q := by
    apply (hq.coprime_iff_not_dvd.mpr _).symm
    intro hd
    exact hne ((Nat.modEq_iff_dvd' (by omega : row g i ≤ n)).mpr hd).symm
  have htwo : n % 2 ≠ row g i % 2 := by
    rw [Nat.even_iff.mp he, hodd]
    decide
  change Nat.Coprime _ (2 * 3 * 5 * 7 * 11 * 13 * 17 * 19)
  simp only [Nat.coprime_mul_iff_right]
  exact ⟨⟨⟨⟨⟨⟨⟨cop 2 (by decide) htwo, cop 3 (by decide) (hg i).1⟩,
    cop 5 (by decide) (hg i).2⟩, cop 7 (by decide) (hi 0)⟩,
    cop 11 (by decide) (hi 1)⟩, cop 13 (by decide) (hi 2)⟩,
    cop 17 (by decide) (hi 3)⟩, cop 19 (by decide) (hi 4)⟩
