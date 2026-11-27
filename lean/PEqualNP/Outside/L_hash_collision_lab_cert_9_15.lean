import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_9_15 :
    ∀ (q : ℕ) (b : Fin q → ℕ),
      (q * 5005) + 6435 * (∑ i, b i) ≤ (∑ i, Nat.choose (b i) 9) + q * 96525 := by
  intro q b
  -- The supporting line through the tight values at load 15 and 16.
  have hsmall : ∀ m : ℕ, m ≤ 15 → 5005 + 6435 * m ≤ Nat.choose m 9 + 96525 := by
    intro m hm
    rcases Nat.lt_or_ge m 15 with h | h
    · omega
    · have h15 : m = 15 := by omega
      subst h15
      norm_num [Nat.choose]
  have hpt : ∀ m : ℕ, 5005 + 6435 * m ≤ Nat.choose m 9 + 96525 := by
    intro m
    rcases Nat.lt_or_ge m 16 with hm | hm
    · exact hsmall m (by omega)
    · refine Nat.le_induction (by norm_num [Nat.choose] :
        5005 + 6435 * 16 ≤ Nat.choose 16 9 + 96525) ?step m hm
      intro n hn ih
      have h6 : 6435 ≤ Nat.choose n 8 :=
        le_trans (by norm_num [Nat.choose] : 6435 ≤ Nat.choose 15 8) (Nat.choose_le_choose 8 (by omega))
      have hrec : Nat.choose (n + 1) 9 = Nat.choose n 8 + Nat.choose n 9 := by
        simpa using Nat.choose_succ_succ n 8
      calc 5005 + 6435 * (n + 1) = (5005 + 6435 * n) + 6435 := by ring
        _ ≤ (Nat.choose n 9 + 96525) + 6435 := Nat.add_le_add_right ih 6435
        _ ≤ (Nat.choose n 9 + 96525) + Nat.choose n 8 := Nat.add_le_add_left h6 _
        _ = Nat.choose (n + 1) 9 + 96525 := by rw [hrec]; ring
  have hsum : (∑ i : Fin q, (5005 + 6435 * b i))
      ≤ ∑ i : Fin q, (Nat.choose (b i) 9 + 96525) :=
    Finset.sum_le_sum fun i _ => hpt (b i)
  have hleft : (∑ i : Fin q, (5005 + 6435 * b i)) = q * 5005 + 6435 * (∑ i, b i) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    simp [Finset.sum_const, Finset.card_univ]
  have hright : (∑ i : Fin q, (Nat.choose (b i) 9 + 96525))
      = (∑ i, Nat.choose (b i) 9) + q * 96525 := by
    rw [Finset.sum_add_distrib]
    simp [Finset.sum_const, Finset.card_univ]
  calc (q * 5005) + 6435 * (∑ i, b i)
      = ∑ i : Fin q, (5005 + 6435 * b i) := hleft.symm
    _ ≤ ∑ i : Fin q, (Nat.choose (b i) 9 + 96525) := hsum
    _ = (∑ i, Nat.choose (b i) 9) + q * 96525 := hright
