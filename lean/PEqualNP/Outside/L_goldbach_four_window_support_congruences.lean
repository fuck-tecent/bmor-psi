import Mathlib

theorem PEqualNP.Outside.L_goldbach_four_window_support_congruences :
    ∀ (n j a b : ℕ), 0 < n → j ≤ 3 → (n:ℝ)/(3*2^j) ≤ a → (a:ℝ) ≤ 2*n/(3*2^j) → (n:ℝ)/(3*2^j) ≤ b → (b:ℝ) ≤ 2*n/(3*2^j) → (a % n = b % n ↔ a = b) ∧ (n ∣ a+b ↔ j = 0 ∧ a+b = n) := by
  intro n j a b hn hj ha₁ ha₂ _ hb₂
  have hden : 0 < (3 : ℝ) * 2 ^ j := by positivity
  have a_lo : n ≤ a * (3 * 2 ^ j) := by exact_mod_cast (div_le_iff₀ hden).mp ha₁
  have a_hi : a * (3 * 2 ^ j) ≤ 2 * n := by exact_mod_cast (le_div_iff₀ hden).mp ha₂
  have b_hi : b * (3 * 2 ^ j) ≤ 2 * n := by exact_mod_cast (le_div_iff₀ hden).mp hb₂
  have bounds : a < n ∧ b < n ∧ 0 < a + b ∧ a + b < 2 * n ∧ (0 < j → a + b < n) := by
    interval_cases j <;> norm_num at a_lo a_hi b_hi ⊢ <;> omega
  obtain ⟨ha, hb, hpos, htwo, hsmall⟩ := bounds
  constructor
  · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  · constructor
    · intro hdiv
      have hsum : a + b = n := Nat.eq_of_dvd_of_lt_two_mul (by omega) hdiv htwo
      refine ⟨?_, hsum⟩
      by_contra hj_ne
      exact (Nat.ne_of_lt (hsmall (Nat.pos_of_ne_zero hj_ne))) hsum
    · rintro ⟨_, hsum⟩
      rw [hsum]
