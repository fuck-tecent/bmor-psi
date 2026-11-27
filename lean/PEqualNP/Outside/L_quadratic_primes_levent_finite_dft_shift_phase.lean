import Mathlib

open scoped BigOperators

/-
QP-0042 · Compute the finite Fourier phase for an arbitrary shift.

Shift the summation index by `h` (`Fintype.sum_equiv` along `Equiv.addRight h`), split the
standard additive character over `-(n * k) + h * k` with `AddChar.map_add_eq_mul`, and pull the
now-constant factor `ZMod.stdAddChar (h * k)` out of the sum with `Finset.sum_mul`.
-/

theorem PEqualNP.Outside.L_quadratic_primes_levent_finite_dft_shift_phase :
    ∀ (N : ℕ) [NeZero N] (f : ZMod N → ℂ) (h k : ZMod N),
      ZMod.dft (fun n => f (n + h)) k = ZMod.stdAddChar (h * k) * ZMod.dft f k := by
  intro N _ f h k
  rw [ZMod.dft_apply, ZMod.dft_apply]
  simp only [smul_eq_mul]
  have hsum : (∑ n : ZMod N, ZMod.stdAddChar (-(n * k)) * f (n + h))
      = ∑ n : ZMod N, ZMod.stdAddChar (-((n - h) * k)) * f n :=
    Fintype.sum_equiv (Equiv.addRight h) (fun n => ZMod.stdAddChar (-(n * k)) * f (n + h))
      (fun n => ZMod.stdAddChar (-((n - h) * k)) * f n) fun n => by simp
  have hchar (n : ZMod N) :
      ZMod.stdAddChar (-((n - h) * k)) * f n
        = ZMod.stdAddChar (-(n * k)) * f n * ZMod.stdAddChar (h * k) := by
    rw [show -((n - h) * k) = -(n * k) + h * k from by ring, AddChar.map_add_eq_mul]
    ring
  rw [hsum, Finset.sum_congr rfl fun n _ => hchar n, ← Finset.sum_mul, mul_comm]
