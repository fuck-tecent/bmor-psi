import Mathlib
theorem PEqualNP.Outside.L_twin_primes_unit_class : ∀ d : ℕ, Odd d → Nat.Coprime 2 d ∧ ∀ p : ℕ, d ∣ p+2 ↔ ((p:ZMod d) = -(2:ZMod d)) := by
  intro d hd
  refine ⟨Nat.coprime_two_left.mpr hd, ?_⟩
  intro p
  rw [← ZMod.natCast_eq_zero_iff (p+2) d]
  push_cast
  exact add_eq_zero_iff_eq_neg

