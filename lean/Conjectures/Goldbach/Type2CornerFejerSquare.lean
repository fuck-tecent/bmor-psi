import Mathlib

open scoped BigOperators

theorem Conjectures.Goldbach.Type2CornerFejerSquare :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
    ∀ (h : ℕ) (θ : ℝ),
      ((‖∑ j ∈ Finset.range h, E (2*(j:ℝ)*θ)‖^2 : ℝ) : ℂ)
        = ∑ i ∈ Finset.range h, ∑ j ∈ Finset.range h, E (2*((i:ℝ)-(j:ℝ))*θ) := by
  intro E h θ
  have hEmul : ∀ a b : ℝ, E a * E b = E (a + b) := by
    intro a b
    simp only [E, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hEconj : ∀ x : ℝ, star (E x) = E (-x) := by
    intro x
    simp only [E, Complex.star_def, Complex.exp_ofReal_mul_I, map_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    have h1 : (2:ℝ) * Real.pi * (-x) = -(2 * Real.pi * x) := by ring
    rw [h1, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have hnorm : ((‖∑ j ∈ Finset.range h, E (2*(j:ℝ)*θ)‖^2 : ℝ) : ℂ)
      = (∑ j ∈ Finset.range h, E (2*(j:ℝ)*θ)) * star (∑ j ∈ Finset.range h, E (2*(j:ℝ)*θ)) := by
    rw [Complex.star_def, Complex.mul_conj']
    push_cast
    ring
  rw [hnorm, star_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [hEconj, hEmul (2*(i:ℝ)*θ) (-(2*(j:ℝ)*θ))]
  congr 1
  ring
