import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_reflected_root :
    ∀ q a:ℕ, a≤q → q∣a^2+1 → q∣(q-a)^2+1 := by
  intro q a haq h
  rw [← ZMod.natCast_eq_zero_iff] at h ⊢
  have hq0 : ((q : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff q q).mpr (dvd_refl q)
  push_cast at h ⊢
  have hsub : ((q - a : ℕ) : ZMod q) = - (a : ZMod q) := by
    rw [Nat.cast_sub haq, hq0]
    ring
  rw [hsub, neg_sq]
  exact h
