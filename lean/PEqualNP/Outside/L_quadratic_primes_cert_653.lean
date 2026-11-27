import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_653 :
    ∀ n : ℕ, 653 ∣ n ^ 2 + 1 ↔ n % 653 = 149 ∨ n % 653 = 504 := by
  intro n
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 653) = (n : ZMod 653) ^ 2 + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow]
  have hr : ((149 : ℕ) : ZMod 653) ^ 2 + 1 = 0 := by decide
  have hn : ((504 : ℕ) : ZMod 653) = -((149 : ℕ) : ZMod 653) := by decide
  have hq : Nat.Prime 653 := by norm_num
  have hroots : ∀ x : ZMod 653, x ^ 2 + 1 = 0 ↔
      x = ((149 : ℕ) : ZMod 653) ∨ x = ((504 : ℕ) : ZMod 653) := by
    intro x
    haveI : Fact (Nat.Prime 653) := ⟨hq⟩
    constructor
    · intro h
      have hz : (x - ((149 : ℕ) : ZMod 653)) * (x + ((149 : ℕ) : ZMod 653)) = 0 := by
        calc (x - ((149 : ℕ) : ZMod 653)) * (x + ((149 : ℕ) : ZMod 653))
            = x ^ 2 + 1 - (((149 : ℕ) : ZMod 653) ^ 2 + 1) := by ring
          _ = 0 := by rw [h, hr]; ring
      rcases mul_eq_zero.mp hz with h1 | h2
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (by rw [hn, eq_neg_of_add_eq_zero_left h2])
    · rintro (rfl | rfl)
      · exact hr
      · rw [hn, neg_sq]; exact hr
  have hmem : ∀ r : ℕ, r < 653 → ((n : ZMod 653) = ((r : ℕ) : ZMod 653) ↔ n % 653 = r) := by
    intro r hrlt
    rw [ZMod.natCast_eq_natCast_iff]
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt hrlt]
  have hd : 653 ∣ n ^ 2 + 1 ↔ ((n ^ 2 + 1 : ℕ) : ZMod 653) = 0 :=
    (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 653).symm
  rw [hd, hcast, hroots, hmem 149 (by decide), hmem 504 (by decide)]

