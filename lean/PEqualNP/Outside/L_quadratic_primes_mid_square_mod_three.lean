import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_mid_square_mod_three :
    ∀ n p:ℕ,n^2+1≠3*p^2 := by
  intro n p heq
  have hmod : (n ^ 2 + 1) % 3 = (3 * p ^ 2) % 3 :=
    congrArg (fun t : ℕ => t % 3) heq
  rw [Nat.mul_mod_right, Nat.add_mod, pow_two n, Nat.mul_mod n n] at hmod
  have hr : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hr with hr | hr | hr <;> norm_num [hr] at hmod
