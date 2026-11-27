import Mathlib

theorem PEqualNP.Outside.L_twin_primes_shift_fourier_phase :
    ∀ (N : ℕ) [NeZero N] (f : ZMod N → ℂ) (k : ZMod N), ZMod.dft (fun n => f (n+2)) k = ZMod.stdAddChar (N:=N) (2*k) * ZMod.dft f k := by
  intro N _ f k
  rw [ZMod.dft_apply, ZMod.dft_apply, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight 2) _ _ fun j => ?_
  simp only [Equiv.coe_addRight, smul_eq_mul]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, show 2*k + -((j+2)*k) = -(j*k) by ring]
