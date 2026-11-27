import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_757 :
    ∀ n : ℕ, 757 ∣ n ^ 2 + 1 ↔ n % 757 = 87 ∨ n % 757 = 670 := by
  intro n
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 757) = (n : ZMod 757) ^ 2 + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow]
  have hr : ((87 : ℕ) : ZMod 757) ^ 2 + 1 = 0 := by decide
  have hn : ((670 : ℕ) : ZMod 757) = -((87 : ℕ) : ZMod 757) := by decide
  have hq : Nat.Prime 757 := by norm_num
  have hroots : ∀ x : ZMod 757, x ^ 2 + 1 = 0 ↔
      x = ((87 : ℕ) : ZMod 757) ∨ x = ((670 : ℕ) : ZMod 757) := by
    intro x
    haveI : Fact (Nat.Prime 757) := ⟨hq⟩
    constructor
    · intro h
      have hz : (x - ((87 : ℕ) : ZMod 757)) * (x + ((87 : ℕ) : ZMod 757)) = 0 := by
        calc (x - ((87 : ℕ) : ZMod 757)) * (x + ((87 : ℕ) : ZMod 757))
            = x ^ 2 + 1 - (((87 : ℕ) : ZMod 757) ^ 2 + 1) := by ring
          _ = 0 := by rw [h, hr]; ring
      rcases mul_eq_zero.mp hz with h1 | h2
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (by rw [hn, eq_neg_of_add_eq_zero_left h2])
    · rintro (rfl | rfl)
      · exact hr
      · rw [hn, neg_sq]; exact hr
  have hmem : ∀ r : ℕ, r < 757 → ((n : ZMod 757) = ((r : ℕ) : ZMod 757) ↔ n % 757 = r) := by
    intro r hrlt
    rw [ZMod.natCast_eq_natCast_iff]
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt hrlt]
  have hd : 757 ∣ n ^ 2 + 1 ↔ ((n ^ 2 + 1 : ℕ) : ZMod 757) = 0 :=
    (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 757).symm
  rw [hd, hcast, hroots, hmem 87 (by decide), hmem 670 (by decide)]

