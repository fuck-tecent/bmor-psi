import Mathlib

namespace PEqualNP.Outside

/-- Cross-block mean square. Two amplitude blocks are paired at the same index. The interference
term left by the energy of their sum is the real part of twice the mixed block, and its square is
charged against four times the product of the two energies. Only an averaged budget is used, so
no single index has to be small. -/
theorem L_goldbach_cross_block_l2_tail :
    ∀ (m : ℕ) (a b : Fin m → ℂ),
      |∑ i, ((a i + b i) * star (a i + b i) - a i * star (a i) - b i * star (b i)).re| ^ 2 ≤
        4 * (∑ i, ‖a i‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) := by
  intro m a b
  set Y := ∑ i, (a i * star (b i)).re with hY
  set T := ∑ i, ‖a i‖ * ‖b i‖ with hT
  -- The three energies cancel down to the two mixed products.
  have hcross : ∀ i, (a i + b i) * star (a i + b i) - a i * star (a i) - b i * star (b i)
      = a i * star (b i) + b i * star (a i) := by
    intro i
    rw [star_add]
    ring
  -- The second mixed product is the conjugate of the first, so the two real parts agree.
  have hflip : ∀ i, b i * star (a i) = star (a i * star (b i)) := by
    intro i
    rw [star_mul, star_star]
  have hre : ∀ z : ℂ, (star z).re = z.re := fun z => Complex.conj_re z
  have hsum : ∑ i, ((a i + b i) * star (a i + b i) - a i * star (a i) - b i * star (b i)).re
      = 2 * Y := by
    rw [hY, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hcross, Complex.add_re, hflip, hre]
    ring
  -- Each mixed amplitude is bounded by the product of the two block norms.
  have hpoint : ∀ i, |(a i * star (b i)).re| ≤ ‖a i‖ * ‖b i‖ := by
    intro i
    calc |(a i * star (b i)).re| ≤ ‖a i * star (b i)‖ := Complex.abs_re_le_norm _
      _ ≤ ‖a i‖ * ‖star (b i)‖ := norm_mul_le _ _
      _ ≤ ‖a i‖ * ‖b i‖ := by rw [norm_star]
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have habs : |Y| ≤ T := (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => hpoint i)
  have h2 : Y ^ 2 ≤ T ^ 2 := sq_le_sq.mpr (by rw [abs_of_nonneg hT0]; exact habs)
  have hcs : T ^ 2 ≤ (∑ i, ‖a i‖ ^ 2) * ∑ i, ‖b i‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hL : |∑ i, ((a i + b i) * star (a i + b i) - a i * star (a i) - b i * star (b i)).re| ^ 2
      = 4 * Y ^ 2 := by
    rw [hsum, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    rw [← sq_abs Y]
    ring
  calc |∑ i, ((a i + b i) * star (a i + b i) - a i * star (a i) - b i * star (b i)).re| ^ 2
      _ = 4 * Y ^ 2 := hL
      _ ≤ 4 * T ^ 2 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 4 by norm_num)
      _ ≤ 4 * ((∑ i, ‖a i‖ ^ 2) * ∑ i, ‖b i‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (show (0 : ℝ) ≤ 4 by norm_num)
      _ = 4 * (∑ i, ‖a i‖ ^ 2) * ∑ i, ‖b i‖ ^ 2 := by ring

end PEqualNP.Outside
