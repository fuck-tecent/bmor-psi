import Mathlib

/-- The complete list of sieve roots of `n ^ 2 + 1` modulo the prime `557`:
`n ^ 2 + 1` is divisible by `557` exactly when `n` is congruent to `118` or `439`
modulo `557`. -/
theorem PEqualNP.Outside.L_quadratic_primes_cert_557 :
    ∀ n : ℕ, 557 ∣ n ^ 2 + 1 ↔ n % 557 = 118 ∨ n % 557 = 439 := by
  have hroots : ∀ k : Fin 557, (k.val ^ 2 + 1) % 557 = 0 ↔ k.val = 118 ∨ k.val = 439 := by
    set_option maxRecDepth 100000 in
    decide
  intro n
  set r := n % 557 with hr
  have hrlt : r < 557 := by
    rw [hr]
    exact Nat.mod_lt _ (by norm_num)
  have key : (r ^ 2 + 1) % 557 = 0 ↔ r = 118 ∨ r = 439 := by
    simpa using hroots ⟨r, hrlt⟩
  have hmod : (n ^ 2 + 1) % 557 = (r ^ 2 + 1) % 557 := by
    have hn : Nat.ModEq 557 n r := by
      rw [Nat.ModEq, hr, Nat.mod_mod]
    exact Nat.ModEq.add_right 1 (Nat.ModEq.pow 2 hn)
  rw [Nat.dvd_iff_mod_eq_zero, hmod, key, hr]
