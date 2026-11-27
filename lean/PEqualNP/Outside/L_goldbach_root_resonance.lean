import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.Ring

theorem PEqualNP.Outside.L_goldbach_root_resonance :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
    let c := fun (M j k : ℕ) => E ((j:ℝ)*(k:ℝ)/(M:ℝ))
    ∀ M k, 0<M → (c M 1 k=1 ↔ M ∣ k) := by
  dsimp only
  intro M k hM
  have harg :
      (((2 * Real.pi * ((1 : ℕ) * (k : ℝ) / M) : ℝ) : ℂ) * Complex.I) =
        2 * Real.pi * Complex.I * k / M := by
    push_cast
    ring
  rw [harg]
  exact Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hM.ne'
