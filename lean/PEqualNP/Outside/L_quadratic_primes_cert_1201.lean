import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1201 :
    ∀ n : ℕ, 1201 ∣ n ^ 2 + 1 ↔ n % 1201 = 49 ∨ n % 1201 = 1152 := by
  intro n
  have hcast : ((n ^ 2 + 1 : ℕ) : ZMod 1201) = (n : ZMod 1201) ^ 2 + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow]
  have hr : ((49 : ℕ) : ZMod 1201) ^ 2 + 1 = 0 := by decide
  have hn : ((1152 : ℕ) : ZMod 1201) = -((49 : ℕ) : ZMod 1201) := by decide
  have hq : Nat.Prime 1201 := by norm_num
  have hroots : ∀ x : ZMod 1201, x ^ 2 + 1 = 0 ↔
      x = ((49 : ℕ) : ZMod 1201) ∨ x = ((1152 : ℕ) : ZMod 1201) := by
    intro x
    haveI : Fact (Nat.Prime 1201) := ⟨hq⟩
    constructor
    · intro h
      have hz : (x - ((49 : ℕ) : ZMod 1201)) * (x + ((49 : ℕ) : ZMod 1201)) = 0 := by
        calc (x - ((49 : ℕ) : ZMod 1201)) * (x + ((49 : ℕ) : ZMod 1201))
            = x ^ 2 + 1 - (((49 : ℕ) : ZMod 1201) ^ 2 + 1) := by ring
          _ = 0 := by rw [h, hr]; ring
      rcases mul_eq_zero.mp hz with h1 | h2
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (by rw [hn, eq_neg_of_add_eq_zero_left h2])
    · rintro (rfl | rfl)
      · exact hr
      · rw [hn, neg_sq]; exact hr
  have hmem : ∀ r : ℕ, r < 1201 → ((n : ZMod 1201) = ((r : ℕ) : ZMod 1201) ↔ n % 1201 = r) := by
    intro r hrlt
    rw [ZMod.natCast_eq_natCast_iff]
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt hrlt]
  have hd : 1201 ∣ n ^ 2 + 1 ↔ ((n ^ 2 + 1 : ℕ) : ZMod 1201) = 0 :=
    (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 1201).symm
  rw [hd, hcast, hroots, hmem 49 (by decide), hmem 1152 (by decide)]

