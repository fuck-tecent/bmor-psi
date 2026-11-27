import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1061 :
    ∀ n : ℕ, 1061 ∣ n ^ 2 + 1 ↔ n % 1061 = 103 ∨ n % 1061 = 958 := by
  intro n
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1061) = (n : ZMod 1061) ^ 2 + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow]
  have hr : ((103 : ℕ) : ZMod 1061) ^ 2 + 1 = 0 := by decide
  have hn : ((958 : ℕ) : ZMod 1061) = -((103 : ℕ) : ZMod 1061) := by decide
  have hq : Nat.Prime 1061 := by norm_num
  have hroots : ∀ x : ZMod 1061, x ^ 2 + 1 = 0 ↔
      x = ((103 : ℕ) : ZMod 1061) ∨ x = ((958 : ℕ) : ZMod 1061) := by
    intro x
    haveI : Fact (Nat.Prime 1061) := ⟨hq⟩
    constructor
    · intro h
      have hz : (x - ((103 : ℕ) : ZMod 1061)) * (x + ((103 : ℕ) : ZMod 1061)) = 0 := by
        calc (x - ((103 : ℕ) : ZMod 1061)) * (x + ((103 : ℕ) : ZMod 1061))
            = x ^ 2 + 1 - (((103 : ℕ) : ZMod 1061) ^ 2 + 1) := by ring
          _ = 0 := by rw [h, hr]; ring
      rcases mul_eq_zero.mp hz with h1 | h2
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (by rw [hn, eq_neg_of_add_eq_zero_left h2])
    · rintro (rfl | rfl)
      · exact hr
      · rw [hn, neg_sq]; exact hr
  have hmem : ∀ r : ℕ, r < 1061 → ((n : ZMod 1061) = ((r : ℕ) : ZMod 1061) ↔ n % 1061 = r) := by
    intro r hrlt
    rw [ZMod.natCast_eq_natCast_iff]
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt hrlt]
  have hd : 1061 ∣ n ^ 2 + 1 ↔ ((n ^ 2 + 1 : ℕ) : ZMod 1061) = 0 :=
    (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1061).symm
  rw [hd, hcast, hroots, hmem 103 (by decide), hmem 958 (by decide)]

