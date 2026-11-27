import Mathlib

theorem PEqualNP.Outside.L_goldbach_pp_base_unique :
    ∀ p q a b : ℕ, p.Prime → q.Prime → 0<a → 0<b → p^a=q^b → p=q := by
  intro p q a b hp hq ha _hb hpow
  apply Nat.prime_eq_prime_of_dvd_pow (m := b) hp hq
  rw [← hpow]
  exact dvd_pow_self p (Nat.ne_of_gt ha)
