import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1193 :
    ∀ n : ℕ, 1193 ∣ n ^ 2 + 1 ↔ n % 1193 = 186 ∨ n % 1193 = 1007 := by
  intro n
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1193) = (n : ZMod 1193) ^ 2 + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow]
  have hr : ((186 : ℕ) : ZMod 1193) ^ 2 + 1 = 0 := by decide
  have hn : ((1007 : ℕ) : ZMod 1193) = -((186 : ℕ) : ZMod 1193) := by decide
  have hq : Nat.Prime 1193 := by norm_num
  have hroots : ∀ x : ZMod 1193, x ^ 2 + 1 = 0 ↔
      x = ((186 : ℕ) : ZMod 1193) ∨ x = ((1007 : ℕ) : ZMod 1193) := by
    intro x
    haveI : Fact (Nat.Prime 1193) := ⟨hq⟩
    constructor
    · intro h
      have hz : (x - ((186 : ℕ) : ZMod 1193)) * (x + ((186 : ℕ) : ZMod 1193)) = 0 := by
        calc (x - ((186 : ℕ) : ZMod 1193)) * (x + ((186 : ℕ) : ZMod 1193))
            = x ^ 2 + 1 - (((186 : ℕ) : ZMod 1193) ^ 2 + 1) := by ring
          _ = 0 := by rw [h, hr]; ring
      rcases mul_eq_zero.mp hz with h1 | h2
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (by rw [hn, eq_neg_of_add_eq_zero_left h2])
    · rintro (rfl | rfl)
      · exact hr
      · rw [hn, neg_sq]; exact hr
  have hmem : ∀ r : ℕ, r < 1193 → ((n : ZMod 1193) = ((r : ℕ) : ZMod 1193) ↔ n % 1193 = r) := by
    intro r hrlt
    rw [ZMod.natCast_eq_natCast_iff]
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt hrlt]
  have hd : 1193 ∣ n ^ 2 + 1 ↔ ((n ^ 2 + 1 : ℕ) : ZMod 1193) = 0 :=
    (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1193).symm
  rw [hd, hcast, hroots, hmem 186 (by decide), hmem 1007 (by decide)]

