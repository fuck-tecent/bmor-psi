import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_769 :
    ∀ n : ℕ, 769 ∣ n ^ 2 + 1 ↔ n % 769 = 62 ∨ n % 769 = 707 := by
  intro n
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 769) = (n : ZMod 769) ^ 2 + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow]
  have hr : ((62 : ℕ) : ZMod 769) ^ 2 + 1 = 0 := by decide
  have hn : ((707 : ℕ) : ZMod 769) = -((62 : ℕ) : ZMod 769) := by decide
  have hq : Nat.Prime 769 := by norm_num
  have hroots : ∀ x : ZMod 769, x ^ 2 + 1 = 0 ↔
      x = ((62 : ℕ) : ZMod 769) ∨ x = ((707 : ℕ) : ZMod 769) := by
    intro x
    haveI : Fact (Nat.Prime 769) := ⟨hq⟩
    constructor
    · intro h
      have hz : (x - ((62 : ℕ) : ZMod 769)) * (x + ((62 : ℕ) : ZMod 769)) = 0 := by
        calc (x - ((62 : ℕ) : ZMod 769)) * (x + ((62 : ℕ) : ZMod 769))
            = x ^ 2 + 1 - (((62 : ℕ) : ZMod 769) ^ 2 + 1) := by ring
          _ = 0 := by rw [h, hr]; ring
      rcases mul_eq_zero.mp hz with h1 | h2
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (by rw [hn, eq_neg_of_add_eq_zero_left h2])
    · rintro (rfl | rfl)
      · exact hr
      · rw [hn, neg_sq]; exact hr
  have hmem : ∀ r : ℕ, r < 769 → ((n : ZMod 769) = ((r : ℕ) : ZMod 769) ↔ n % 769 = r) := by
    intro r hrlt
    rw [ZMod.natCast_eq_natCast_iff]
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt hrlt]
  have hd : 769 ∣ n ^ 2 + 1 ↔ ((n ^ 2 + 1 : ℕ) : ZMod 769) = 0 :=
    (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 769).symm
  rw [hd, hcast, hroots, hmem 62 (by decide), hmem 707 (by decide)]

