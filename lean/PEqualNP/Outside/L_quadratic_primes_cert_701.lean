import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_701 :
    ∀ n : ℕ, 701 ∣ n ^ 2 + 1 ↔ n % 701 = 135 ∨ n % 701 = 566 := by
  intro n
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 701) = (n : ZMod 701) ^ 2 + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow]
  have hr : ((135 : ℕ) : ZMod 701) ^ 2 + 1 = 0 := by decide
  have hn : ((566 : ℕ) : ZMod 701) = -((135 : ℕ) : ZMod 701) := by decide
  have hq : Nat.Prime 701 := by norm_num
  have hroots : ∀ x : ZMod 701, x ^ 2 + 1 = 0 ↔
      x = ((135 : ℕ) : ZMod 701) ∨ x = ((566 : ℕ) : ZMod 701) := by
    intro x
    haveI : Fact (Nat.Prime 701) := ⟨hq⟩
    constructor
    · intro h
      have hz : (x - ((135 : ℕ) : ZMod 701)) * (x + ((135 : ℕ) : ZMod 701)) = 0 := by
        calc (x - ((135 : ℕ) : ZMod 701)) * (x + ((135 : ℕ) : ZMod 701))
            = x ^ 2 + 1 - (((135 : ℕ) : ZMod 701) ^ 2 + 1) := by ring
          _ = 0 := by rw [h, hr]; ring
      rcases mul_eq_zero.mp hz with h1 | h2
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (by rw [hn, eq_neg_of_add_eq_zero_left h2])
    · rintro (rfl | rfl)
      · exact hr
      · rw [hn, neg_sq]; exact hr
  have hmem : ∀ r : ℕ, r < 701 → ((n : ZMod 701) = ((r : ℕ) : ZMod 701) ↔ n % 701 = r) := by
    intro r hrlt
    rw [ZMod.natCast_eq_natCast_iff]
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt hrlt]
  have hd : 701 ∣ n ^ 2 + 1 ↔ ((n ^ 2 + 1 : ℕ) : ZMod 701) = 0 :=
    (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 701).symm
  rw [hd, hcast, hroots, hmem 135 (by decide), hmem 566 (by decide)]

