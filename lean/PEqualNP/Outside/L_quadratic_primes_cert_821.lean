import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_821 :
    ∀ n : ℕ, 821 ∣ n ^ 2 + 1 ↔ n % 821 = 295 ∨ n % 821 = 526 := by
  intro n
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 821) = (n : ZMod 821) ^ 2 + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow]
  have hr : ((295 : ℕ) : ZMod 821) ^ 2 + 1 = 0 := by decide
  have hn : ((526 : ℕ) : ZMod 821) = -((295 : ℕ) : ZMod 821) := by decide
  have hq : Nat.Prime 821 := by norm_num
  have hroots : ∀ x : ZMod 821, x ^ 2 + 1 = 0 ↔
      x = ((295 : ℕ) : ZMod 821) ∨ x = ((526 : ℕ) : ZMod 821) := by
    intro x
    haveI : Fact (Nat.Prime 821) := ⟨hq⟩
    constructor
    · intro h
      have hz : (x - ((295 : ℕ) : ZMod 821)) * (x + ((295 : ℕ) : ZMod 821)) = 0 := by
        calc (x - ((295 : ℕ) : ZMod 821)) * (x + ((295 : ℕ) : ZMod 821))
            = x ^ 2 + 1 - (((295 : ℕ) : ZMod 821) ^ 2 + 1) := by ring
          _ = 0 := by rw [h, hr]; ring
      rcases mul_eq_zero.mp hz with h1 | h2
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (by rw [hn, eq_neg_of_add_eq_zero_left h2])
    · rintro (rfl | rfl)
      · exact hr
      · rw [hn, neg_sq]; exact hr
  have hmem : ∀ r : ℕ, r < 821 → ((n : ZMod 821) = ((r : ℕ) : ZMod 821) ↔ n % 821 = r) := by
    intro r hrlt
    rw [ZMod.natCast_eq_natCast_iff]
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt hrlt]
  have hd : 821 ∣ n ^ 2 + 1 ↔ ((n ^ 2 + 1 : ℕ) : ZMod 821) = 0 :=
    (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 821).symm
  rw [hd, hcast, hroots, hmem 295 (by decide), hmem 526 (by decide)]

