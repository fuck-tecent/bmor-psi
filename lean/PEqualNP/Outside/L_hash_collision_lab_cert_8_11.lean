import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_8_11 :
    ∀ (q : ℕ) (b : Fin q → ℕ),
      (q * 165) + 330 * (∑ i, b i) ≤ (∑ i, Nat.choose (b i) 8) + q * 3630 := by
  intro q b
  -- The supporting line through the tight values at load 11 and 12.
  have hsmall : ∀ m : ℕ, m ≤ 11 → 165 + 330 * m ≤ Nat.choose m 8 + 3630 := by
    intro m hm
    rcases Nat.lt_or_ge m 11 with h | h
    · omega
    · have h11 : m = 11 := by omega
      subst h11
      norm_num [Nat.choose]
  have hpt : ∀ m : ℕ, 165 + 330 * m ≤ Nat.choose m 8 + 3630 := by
    intro m
    rcases Nat.lt_or_ge m 12 with hm | hm
    · exact hsmall m (by omega)
    · refine Nat.le_induction (by norm_num [Nat.choose] :
        165 + 330 * 12 ≤ Nat.choose 12 8 + 3630) ?step m hm
      intro n hn ih
      have h6 : 330 ≤ Nat.choose n 7 :=
        le_trans (by norm_num [Nat.choose] : 330 ≤ Nat.choose 11 7) (Nat.choose_le_choose 7 (by omega))
      have hrec : Nat.choose (n + 1) 8 = Nat.choose n 7 + Nat.choose n 8 := by
        simpa using Nat.choose_succ_succ n 7
      calc 165 + 330 * (n + 1) = (165 + 330 * n) + 330 := by ring
        _ ≤ (Nat.choose n 8 + 3630) + 330 := Nat.add_le_add_right ih 330
        _ ≤ (Nat.choose n 8 + 3630) + Nat.choose n 7 := Nat.add_le_add_left h6 _
        _ = Nat.choose (n + 1) 8 + 3630 := by rw [hrec]; ring
  have hsum : (∑ i : Fin q, (165 + 330 * b i))
      ≤ ∑ i : Fin q, (Nat.choose (b i) 8 + 3630) :=
    Finset.sum_le_sum fun i _ => hpt (b i)
  have hleft : (∑ i : Fin q, (165 + 330 * b i)) = q * 165 + 330 * (∑ i, b i) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    simp [Finset.sum_const, Finset.card_univ]
  have hright : (∑ i : Fin q, (Nat.choose (b i) 8 + 3630))
      = (∑ i, Nat.choose (b i) 8) + q * 3630 := by
    rw [Finset.sum_add_distrib]
    simp [Finset.sum_const, Finset.card_univ]
  calc (q * 165) + 330 * (∑ i, b i)
      = ∑ i : Fin q, (165 + 330 * b i) := hleft.symm
    _ ≤ ∑ i : Fin q, (Nat.choose (b i) 8 + 3630) := hsum
    _ = (∑ i, Nat.choose (b i) 8) + q * 3630 := hright
