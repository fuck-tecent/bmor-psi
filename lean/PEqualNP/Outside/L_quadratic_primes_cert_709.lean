import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_709 :
    ∀ n : ℕ, 709 ∣ n ^ 2 + 1 ↔ n % 709 = 96 ∨ n % 709 = 613 := by
  intro n
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 709) = (n : ZMod 709) ^ 2 + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow]
  have hr : ((96 : ℕ) : ZMod 709) ^ 2 + 1 = 0 := by decide
  have hn : ((613 : ℕ) : ZMod 709) = -((96 : ℕ) : ZMod 709) := by decide
  have hq : Nat.Prime 709 := by norm_num
  have hroots : ∀ x : ZMod 709, x ^ 2 + 1 = 0 ↔
      x = ((96 : ℕ) : ZMod 709) ∨ x = ((613 : ℕ) : ZMod 709) := by
    intro x
    haveI : Fact (Nat.Prime 709) := ⟨hq⟩
    constructor
    · intro h
      have hz : (x - ((96 : ℕ) : ZMod 709)) * (x + ((96 : ℕ) : ZMod 709)) = 0 := by
        calc (x - ((96 : ℕ) : ZMod 709)) * (x + ((96 : ℕ) : ZMod 709))
            = x ^ 2 + 1 - (((96 : ℕ) : ZMod 709) ^ 2 + 1) := by ring
          _ = 0 := by rw [h, hr]; ring
      rcases mul_eq_zero.mp hz with h1 | h2
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (by rw [hn, eq_neg_of_add_eq_zero_left h2])
    · rintro (rfl | rfl)
      · exact hr
      · rw [hn, neg_sq]; exact hr
  have hmem : ∀ r : ℕ, r < 709 → ((n : ZMod 709) = ((r : ℕ) : ZMod 709) ↔ n % 709 = r) := by
    intro r hrlt
    rw [ZMod.natCast_eq_natCast_iff]
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt hrlt]
  have hd : 709 ∣ n ^ 2 + 1 ↔ ((n ^ 2 + 1 : ℕ) : ZMod 709) = 0 :=
    (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 709).symm
  rw [hd, hcast, hroots, hmem 96 (by decide), hmem 613 (by decide)]

