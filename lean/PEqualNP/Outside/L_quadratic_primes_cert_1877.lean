import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1877 :
    ∀ n : ℕ, 1877 ∣ n ^ 2 + 1 ↔ n % 1877 = 137 ∨ n % 1877 = 1740 := by
  intro n
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1877) = (n : ZMod 1877) ^ 2 + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow]
  have hr : ((137 : ℕ) : ZMod 1877) ^ 2 + 1 = 0 := by decide
  have hn : ((1740 : ℕ) : ZMod 1877) = -((137 : ℕ) : ZMod 1877) := by decide
  have hq : Nat.Prime 1877 := by norm_num
  have hroots : ∀ x : ZMod 1877, x ^ 2 + 1 = 0 ↔
      x = ((137 : ℕ) : ZMod 1877) ∨ x = ((1740 : ℕ) : ZMod 1877) := by
    intro x
    haveI : Fact (Nat.Prime 1877) := ⟨hq⟩
    constructor
    · intro h
      have hz : (x - ((137 : ℕ) : ZMod 1877)) * (x + ((137 : ℕ) : ZMod 1877)) = 0 := by
        calc (x - ((137 : ℕ) : ZMod 1877)) * (x + ((137 : ℕ) : ZMod 1877))
            = x ^ 2 + 1 - (((137 : ℕ) : ZMod 1877) ^ 2 + 1) := by ring
          _ = 0 := by rw [h, hr]; ring
      rcases mul_eq_zero.mp hz with h1 | h2
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (by rw [hn, eq_neg_of_add_eq_zero_left h2])
    · rintro (rfl | rfl)
      · exact hr
      · rw [hn, neg_sq]; exact hr
  have hmem : ∀ r : ℕ, r < 1877 → ((n : ZMod 1877) = ((r : ℕ) : ZMod 1877) ↔ n % 1877 = r) := by
    intro r hrlt
    rw [ZMod.natCast_eq_natCast_iff]
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt hrlt]
  have hd : 1877 ∣ n ^ 2 + 1 ↔ ((n ^ 2 + 1 : ℕ) : ZMod 1877) = 0 :=
    (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1877).symm
  rw [hd, hcast, hroots, hmem 137 (by decide), hmem 1740 (by decide)]

