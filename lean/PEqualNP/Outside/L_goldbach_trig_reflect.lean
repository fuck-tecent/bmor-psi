import Mathlib

theorem PEqualNP.Outside.L_goldbach_trig_reflect :
    let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
    let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) =>
      Finset.sum (Finset.range (n + 1)) (fun k => (w k : ℂ) * E ((k : ℝ) * t))
    ∀ n w t, S n w (-t) = star (S n w t) := by
  dsimp only
  intro n w t
  rw [star_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  change _ = (starRingEnd ℂ) _
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I,
    mul_neg, Complex.ofReal_neg, neg_mul]
