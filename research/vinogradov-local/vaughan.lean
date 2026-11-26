import Mathlib

/-! Vaughan's identity, adapted locally from the accepted Goldbach proof
`L_goldbach_frontier_vaughan_type1_elimination` (PR #2430, Apache-2.0).
This local file isolates the finite identity before any analytic estimate. -/

open scoped BigOperators
open ArithmeticFunction
open scoped ArithmeticFunction zeta Moebius

namespace PEqualNP.Outside.Vaughan

noncomputable section

noncomputable def low (U : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun m => if m ≤ U then f m else 0, by simp⟩

noncomputable def high (U : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun m => if U < m then f m else 0, by simp⟩

private theorem low_add_high (U : ℕ) (f : ArithmeticFunction ℝ) :
    low U f + high U f = f := by
  ext m
  change (if m ≤ U then f m else 0) + (if U < m then f m else 0) = f m
  by_cases h : m ≤ U
  · simp [h, not_lt_of_ge h]
  · simp [h, lt_of_not_ge h]

theorem vaughan_identity (U : ℕ) :
    (Λ : ArithmeticFunction ℝ) =
      low U Λ + low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log -
        low U (μ : ArithmeticFunction ℝ) * low U Λ * (ζ : ArithmeticFunction ℝ) +
        high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) * high U Λ := by
  have hμ : (low U (μ : ArithmeticFunction ℝ) + high U (μ : ArithmeticFunction ℝ)) *
      (ζ : ArithmeticFunction ℝ) = 1 := by
    rw [low_add_high, coe_moebius_mul_coe_zeta]
  have hlog : (ζ : ArithmeticFunction ℝ) * (low U Λ + high U Λ) =
      ArithmeticFunction.log := by
    rw [low_add_high, zeta_mul_vonMangoldt]
  calc
    _ = low U Λ + high U Λ := (low_add_high U Λ).symm
    _ = low U Λ + (low U (μ : ArithmeticFunction ℝ) + high U (μ : ArithmeticFunction ℝ)) *
        (ζ : ArithmeticFunction ℝ) * high U Λ := by rw [hμ, one_mul]
    _ = _ := by rw [← hlog]; ring

noncomputable def E (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

noncomputable def expSum (n : ℕ) (f : ArithmeticFunction ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), (f k : ℂ) * E ((k : ℝ) * t)

lemma expSum_add (n : ℕ) (f g : ArithmeticFunction ℝ) (t : ℝ) :
    expSum n (f + g) t = expSum n f t + expSum n g t := by
  unfold expSum
  simp only [ArithmeticFunction.add_apply, Complex.ofReal_add, add_mul]
  rw [Finset.sum_add_distrib]

lemma expSum_sub (n : ℕ) (f g : ArithmeticFunction ℝ) (t : ℝ) :
    expSum n (f - g) t = expSum n f t - expSum n g t := by
  unfold expSum
  simp only [sub_apply, Complex.ofReal_sub, sub_mul]
  rw [Finset.sum_sub_distrib]

theorem expSum_vaughan (n U : ℕ) (t : ℝ) :
    expSum n Λ t =
      expSum n (low U Λ) t +
        expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) t -
        expSum n (low U (μ : ArithmeticFunction ℝ) * low U Λ * (ζ : ArithmeticFunction ℝ)) t +
        expSum n (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) * high U Λ) t := by
  have h : expSum n Λ t =
      expSum n (low U Λ + low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log -
        low U (μ : ArithmeticFunction ℝ) * low U Λ * (ζ : ArithmeticFunction ℝ) +
        high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) * high U Λ) t := by
    conv_lhs => rw [vaughan_identity U]
  rw [h]
  rw [expSum_add, expSum_sub, expSum_add]

end

end PEqualNP.Outside.Vaughan
