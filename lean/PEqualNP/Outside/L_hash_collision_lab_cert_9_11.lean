import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_9_11 :
    ∀ (q : ℕ) (b : Fin q → ℕ),
      (q * 55) + 165 * (∑ i, b i) ≤ (∑ i, Nat.choose (b i) 9) + q * 1815 := by
  intro q b
  -- The supporting line through the tight values at load 11 and 12.
  have hsmall : ∀ m : ℕ, m ≤ 11 → 55 + 165 * m ≤ Nat.choose m 9 + 1815 := by
    intro m hm
    rcases Nat.lt_or_ge m 11 with h | h
    · omega
    · have h11 : m = 11 := by omega
      subst h11
      norm_num [Nat.choose]
  have hpt : ∀ m : ℕ, 55 + 165 * m ≤ Nat.choose m 9 + 1815 := by
    intro m
    rcases Nat.lt_or_ge m 12 with hm | hm
    · exact hsmall m (by omega)
    · refine Nat.le_induction (by norm_num [Nat.choose] :
        55 + 165 * 12 ≤ Nat.choose 12 9 + 1815) ?step m hm
      intro n hn ih
      have h6 : 165 ≤ Nat.choose n 8 :=
        le_trans (by norm_num [Nat.choose] : 165 ≤ Nat.choose 11 8) (Nat.choose_le_choose 8 (by omega))
      have hrec : Nat.choose (n + 1) 9 = Nat.choose n 8 + Nat.choose n 9 := by
        simpa using Nat.choose_succ_succ n 8
      calc 55 + 165 * (n + 1) = (55 + 165 * n) + 165 := by ring
        _ ≤ (Nat.choose n 9 + 1815) + 165 := Nat.add_le_add_right ih 165
        _ ≤ (Nat.choose n 9 + 1815) + Nat.choose n 8 := Nat.add_le_add_left h6 _
        _ = Nat.choose (n + 1) 9 + 1815 := by rw [hrec]; ring
  have hsum : (∑ i : Fin q, (55 + 165 * b i))
      ≤ ∑ i : Fin q, (Nat.choose (b i) 9 + 1815) :=
    Finset.sum_le_sum fun i _ => hpt (b i)
  have hleft : (∑ i : Fin q, (55 + 165 * b i)) = q * 55 + 165 * (∑ i, b i) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    simp [Finset.sum_const, Finset.card_univ]
  have hright : (∑ i : Fin q, (Nat.choose (b i) 9 + 1815))
      = (∑ i, Nat.choose (b i) 9) + q * 1815 := by
    rw [Finset.sum_add_distrib]
    simp [Finset.sum_const, Finset.card_univ]
  calc (q * 55) + 165 * (∑ i, b i)
      = ∑ i : Fin q, (55 + 165 * b i) := hleft.symm
    _ ≤ ∑ i : Fin q, (Nat.choose (b i) 9 + 1815) := hsum
    _ = (∑ i, Nat.choose (b i) 9) + q * 1815 := hright
