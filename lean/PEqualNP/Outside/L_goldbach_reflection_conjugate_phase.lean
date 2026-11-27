import Mathlib

theorem PEqualNP.Outside.L_goldbach_reflection_conjugate_phase :
    ∀ (z : ℂ) (k : ℕ), ‖z‖=1 → (z⁻¹)^k=star (z^k) := by
  intro z k hz
  rw [star_pow]
  exact congrArg (fun w : ℂ => w ^ k) (Complex.inv_eq_conj hz)
