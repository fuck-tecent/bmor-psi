import Mathlib

theorem PEqualNP.Outside.L_goldbach_pp_true_nonprime :
    ∀ p a : ℕ, p.Prime → 2≤a → ¬ Nat.Prime (p^a) :=
  fun _ _ _ exponent_bound => Nat.Prime.not_prime_pow exponent_bound
