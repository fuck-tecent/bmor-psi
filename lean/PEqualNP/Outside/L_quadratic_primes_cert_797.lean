import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_797 :
    ∀ n : ℕ, 797 ∣ n ^ 2 + 1 ↔ n % 797 = 215 ∨ n % 797 = 582 := by
  intro n
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 797) = (n : ZMod 797) ^ 2 + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow]
  have hr : ((215 : ℕ) : ZMod 797) ^ 2 + 1 = 0 := by decide
  have hn : ((582 : ℕ) : ZMod 797) = -((215 : ℕ) : ZMod 797) := by decide
  have hq : Nat.Prime 797 := by norm_num
  have hroots : ∀ x : ZMod 797, x ^ 2 + 1 = 0 ↔
      x = ((215 : ℕ) : ZMod 797) ∨ x = ((582 : ℕ) : ZMod 797) := by
    intro x
    haveI : Fact (Nat.Prime 797) := ⟨hq⟩
    constructor
    · intro h
      have hz : (x - ((215 : ℕ) : ZMod 797)) * (x + ((215 : ℕ) : ZMod 797)) = 0 := by
        calc (x - ((215 : ℕ) : ZMod 797)) * (x + ((215 : ℕ) : ZMod 797))
            = x ^ 2 + 1 - (((215 : ℕ) : ZMod 797) ^ 2 + 1) := by ring
          _ = 0 := by rw [h, hr]; ring
      rcases mul_eq_zero.mp hz with h1 | h2
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (by rw [hn, eq_neg_of_add_eq_zero_left h2])
    · rintro (rfl | rfl)
      · exact hr
      · rw [hn, neg_sq]; exact hr
  have hmem : ∀ r : ℕ, r < 797 → ((n : ZMod 797) = ((r : ℕ) : ZMod 797) ↔ n % 797 = r) := by
    intro r hrlt
    rw [ZMod.natCast_eq_natCast_iff]
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt hrlt]
  have hd : 797 ∣ n ^ 2 + 1 ↔ ((n ^ 2 + 1 : ℕ) : ZMod 797) = 0 :=
    (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 797).symm
  rw [hd, hcast, hroots, hmem 215 (by decide), hmem 582 (by decide)]

