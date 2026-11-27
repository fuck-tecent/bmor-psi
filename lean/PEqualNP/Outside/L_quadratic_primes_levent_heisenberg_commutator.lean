import Mathlib

/-
QP-0048 · Compute the finite Heisenberg translation-modulation phase.

Translating a modulated function picks up the standard additive character at `a * b`: both sides
expand to products of `ZMod.stdAddChar`, the character turns the sum `b * n + a * b` into a
product (`AddChar.map_add_eq_mul`), and what is left is commutative arithmetic in `ℂ`.
-/

theorem PEqualNP.Outside.L_quadratic_primes_levent_heisenberg_commutator :
    ∀ (N : ℕ) [NeZero N] (a b : ZMod N) (f : ZMod N → ℂ),
      let T := fun (g : ZMod N → ℂ) n => g (n + a)
      let M := fun (g : ZMod N → ℂ) n => ZMod.stdAddChar (b * n) * g n
      ∀ n, T (M f) n = ZMod.stdAddChar (a * b) * M (T f) n := by
  intro N _ a b f T M n
  show ZMod.stdAddChar (b * (n + a)) * f (n + a)
      = ZMod.stdAddChar (a * b) * (ZMod.stdAddChar (b * n) * f (n + a))
  rw [mul_add, AddChar.map_add_eq_mul, ← mul_comm a b]
  ring
