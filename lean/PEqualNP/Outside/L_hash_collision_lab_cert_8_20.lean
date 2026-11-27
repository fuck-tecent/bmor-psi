import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_8_20 :
    ∀ (q : ℕ) (b : Fin q → ℕ),
      (q * 125970) + 77520 * (∑ i, b i) ≤ (∑ i, Nat.choose (b i) 8) + q * 1550400 := by
  intro q b
  -- Discrete supporting line for order 8, tight at loads 20 and 21.
  have hpt : ∀ m : ℕ, 125970 + 77520 * m ≤ Nat.choose m 8 + 1550400 := by
    intro m
    rcases Nat.lt_or_ge m 20 with hm | hm
    · interval_cases m <;> norm_num [Nat.choose]
    · refine Nat.le_induction (by norm_num [Nat.choose] :
        125970 + 77520 * 20 ≤ Nat.choose 20 8 + 1550400) ?step m hm
      intro n hn ih
      have h7 : 77520 ≤ Nat.choose n 7 :=
        le_trans (by norm_num [Nat.choose] : 77520 ≤ Nat.choose 20 7) (Nat.choose_le_choose 7 hn)
      have hrec : Nat.choose (n + 1) 8 = Nat.choose n 7 + Nat.choose n 8 := by
        simpa using Nat.choose_succ_succ n 7
      rw [hrec]
      calc 125970 + 77520 * (n + 1) = (125970 + 77520 * n) + 77520 := by ring
        _ ≤ (Nat.choose n 8 + 1550400) + 77520 := Nat.add_le_add_right ih 77520
        _ ≤ (Nat.choose n 8 + 1550400) + Nat.choose n 7 := Nat.add_le_add (le_refl _) h7
        _ = Nat.choose n 7 + Nat.choose n 8 + 1550400 := by ring
  have hsum : (∑ i : Fin q, (125970 + 77520 * b i))
      ≤ ∑ i : Fin q, (Nat.choose (b i) 8 + 1550400) :=
    Finset.sum_le_sum fun i _ => hpt (b i)
  have hleft : (∑ i : Fin q, (125970 + 77520 * b i)) = q * 125970 + 77520 * (∑ i, b i) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    simp [Finset.sum_const, Finset.card_univ]
  have hright : (∑ i : Fin q, (Nat.choose (b i) 8 + 1550400))
      = (∑ i, Nat.choose (b i) 8) + q * 1550400 := by
    rw [Finset.sum_add_distrib]
    simp [Finset.sum_const, Finset.card_univ]
  calc (q * 125970) + 77520 * (∑ i, b i)
      = ∑ i : Fin q, (125970 + 77520 * b i) := hleft.symm
    _ ≤ ∑ i : Fin q, (Nat.choose (b i) 8 + 1550400) := hsum
    _ = (∑ i, Nat.choose (b i) 8) + q * 1550400 := hright
