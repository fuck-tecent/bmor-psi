import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1153 :
    ∀ n : ℕ, 1153 ∣ n ^ 2 + 1 ↔ n % 1153 = 140 ∨ n % 1153 = 1013 := by
  intro n
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1153) = (n : ZMod 1153) ^ 2 + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow]
  have hr : ((140 : ℕ) : ZMod 1153) ^ 2 + 1 = 0 := by decide
  have hn : ((1013 : ℕ) : ZMod 1153) = -((140 : ℕ) : ZMod 1153) := by decide
  have hq : Nat.Prime 1153 := by norm_num
  have hroots : ∀ x : ZMod 1153, x ^ 2 + 1 = 0 ↔
      x = ((140 : ℕ) : ZMod 1153) ∨ x = ((1013 : ℕ) : ZMod 1153) := by
    intro x
    haveI : Fact (Nat.Prime 1153) := ⟨hq⟩
    constructor
    · intro h
      have hz : (x - ((140 : ℕ) : ZMod 1153)) * (x + ((140 : ℕ) : ZMod 1153)) = 0 := by
        calc (x - ((140 : ℕ) : ZMod 1153)) * (x + ((140 : ℕ) : ZMod 1153))
            = x ^ 2 + 1 - (((140 : ℕ) : ZMod 1153) ^ 2 + 1) := by ring
          _ = 0 := by rw [h, hr]; ring
      rcases mul_eq_zero.mp hz with h1 | h2
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (by rw [hn, eq_neg_of_add_eq_zero_left h2])
    · rintro (rfl | rfl)
      · exact hr
      · rw [hn, neg_sq]; exact hr
  have hmem : ∀ r : ℕ, r < 1153 → ((n : ZMod 1153) = ((r : ℕ) : ZMod 1153) ↔ n % 1153 = r) := by
    intro r hrlt
    rw [ZMod.natCast_eq_natCast_iff]
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt hrlt]
  have hd : 1153 ∣ n ^ 2 + 1 ↔ ((n ^ 2 + 1 : ℕ) : ZMod 1153) = 0 :=
    (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1153).symm
  rw [hd, hcast, hroots, hmem 140 (by decide), hmem 1013 (by decide)]

