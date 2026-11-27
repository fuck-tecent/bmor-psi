import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_8_15 :
    ∀ (q : ℕ) (b : Fin q → ℕ),
      (q * 6435) + 6435 * (∑ i, b i) ≤ (∑ i, Nat.choose (b i) 8) + q * 96525 := by
  intro q b
  -- Discrete supporting line for order 8, tight at loads 15 and 16.
  have hpt : ∀ m : ℕ, 6435 + 6435 * m ≤ Nat.choose m 8 + 96525 := by
    intro m
    rcases Nat.lt_or_ge m 15 with hm | hm
    · interval_cases m <;> norm_num [Nat.choose]
    · refine Nat.le_induction (by norm_num [Nat.choose] :
        6435 + 6435 * 15 ≤ Nat.choose 15 8 + 96525) ?step m hm
      intro n hn ih
      have h7 : 6435 ≤ Nat.choose n 7 :=
        le_trans (by norm_num [Nat.choose] : 6435 ≤ Nat.choose 15 7) (Nat.choose_le_choose 7 hn)
      have hrec : Nat.choose (n + 1) 8 = Nat.choose n 7 + Nat.choose n 8 := by
        simpa using Nat.choose_succ_succ n 7
      rw [hrec]
      calc 6435 + 6435 * (n + 1) = (6435 + 6435 * n) + 6435 := by ring
        _ ≤ (Nat.choose n 8 + 96525) + 6435 := Nat.add_le_add_right ih 6435
        _ ≤ (Nat.choose n 8 + 96525) + Nat.choose n 7 := Nat.add_le_add (le_refl _) h7
        _ = Nat.choose n 7 + Nat.choose n 8 + 96525 := by ring
  have hsum : (∑ i : Fin q, (6435 + 6435 * b i))
      ≤ ∑ i : Fin q, (Nat.choose (b i) 8 + 96525) :=
    Finset.sum_le_sum fun i _ => hpt (b i)
  have hleft : (∑ i : Fin q, (6435 + 6435 * b i)) = q * 6435 + 6435 * (∑ i, b i) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    simp [Finset.sum_const, Finset.card_univ]
  have hright : (∑ i : Fin q, (Nat.choose (b i) 8 + 96525))
      = (∑ i, Nat.choose (b i) 8) + q * 96525 := by
    rw [Finset.sum_add_distrib]
    simp [Finset.sum_const, Finset.card_univ]
  calc (q * 6435) + 6435 * (∑ i, b i)
      = ∑ i : Fin q, (6435 + 6435 * b i) := hleft.symm
    _ ≤ ∑ i : Fin q, (Nat.choose (b i) 8 + 96525) := hsum
    _ = (∑ i, Nat.choose (b i) 8) + q * 96525 := hright
