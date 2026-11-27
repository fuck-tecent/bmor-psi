import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_9_17 :
    ∀ (q : ℕ) (b : Fin q → ℕ),
      (q * 24310) + 24310 * (∑ i, b i) ≤ (∑ i, Nat.choose (b i) 9) + q * 413270 := by
  intro q b
  -- Discrete supporting line for order 9, tight at loads 17 and 18.
  have hpt : ∀ m : ℕ, 24310 + 24310 * m ≤ Nat.choose m 9 + 413270 := by
    intro m
    rcases Nat.lt_or_ge m 17 with hm | hm
    · interval_cases m <;> norm_num [Nat.choose]
    · refine Nat.le_induction (by norm_num [Nat.choose] :
        24310 + 24310 * 17 ≤ Nat.choose 17 9 + 413270) ?step m hm
      intro n hn ih
      have h8 : 24310 ≤ Nat.choose n 8 :=
        le_trans (by norm_num [Nat.choose] : 24310 ≤ Nat.choose 17 8) (Nat.choose_le_choose 8 hn)
      have hrec : Nat.choose (n + 1) 9 = Nat.choose n 8 + Nat.choose n 9 := by
        simpa using Nat.choose_succ_succ n 8
      rw [hrec]
      calc 24310 + 24310 * (n + 1) = (24310 + 24310 * n) + 24310 := by ring
        _ ≤ (Nat.choose n 9 + 413270) + 24310 := Nat.add_le_add_right ih 24310
        _ ≤ (Nat.choose n 9 + 413270) + Nat.choose n 8 := Nat.add_le_add (le_refl _) h8
        _ = Nat.choose n 8 + Nat.choose n 9 + 413270 := by ring
  have hsum : (∑ i : Fin q, (24310 + 24310 * b i))
      ≤ ∑ i : Fin q, (Nat.choose (b i) 9 + 413270) :=
    Finset.sum_le_sum fun i _ => hpt (b i)
  have hleft : (∑ i : Fin q, (24310 + 24310 * b i)) = q * 24310 + 24310 * (∑ i, b i) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    simp [Finset.sum_const, Finset.card_univ]
  have hright : (∑ i : Fin q, (Nat.choose (b i) 9 + 413270))
      = (∑ i, Nat.choose (b i) 9) + q * 413270 := by
    rw [Finset.sum_add_distrib]
    simp [Finset.sum_const, Finset.card_univ]
  calc (q * 24310) + 24310 * (∑ i, b i)
      = ∑ i : Fin q, (24310 + 24310 * b i) := hleft.symm
    _ ≤ ∑ i : Fin q, (Nat.choose (b i) 9 + 413270) := hsum
    _ = (∑ i, Nat.choose (b i) 9) + q * 413270 := hright
