import Mathlib

/-!
# Logarithmic Möbius weight as a prime-power convolution

The identity `(μ * Λ)(n) = -μ(n) log n`, i.e. the divisor convolution identity for the
logarithmic derivative of the Möbius series.

Adapted from `PEqualNP.Outside.L_twin_primes_mangoldt_divisors` (use of
`ArithmeticFunction.sum_moebius_mul_log_eq`).
-/

namespace Conjectures.TwinPrimes.AdmissibleLongPrimePowerConvolution_aux

open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

/-- The arithmetic function `n ↦ -μ(n) log n`. -/
private noncomputable def logMoebius : ArithmeticFunction ℝ :=
  ⟨fun n => -((ArithmeticFunction.moebius n : ℝ) * Real.log n), by simp⟩

private theorem logMoebius_apply (n : ℕ) :
    logMoebius n = -((ArithmeticFunction.moebius n : ℝ) * Real.log n) := rfl

private theorem logMoebius_mul_zeta : logMoebius * ζ = ArithmeticFunction.vonMangoldt := by
  ext n
  have h := ArithmeticFunction.sum_moebius_mul_log_eq (n := n)
  change (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * Real.log d) =
    -ArithmeticFunction.vonMangoldt n at h
  rw [ArithmeticFunction.coe_mul_zeta_apply (f := logMoebius) (x := n)]
  simp only [logMoebius_apply, Finset.sum_neg_distrib]
  linarith

private theorem logMoebius_eq : logMoebius = ArithmeticFunction.vonMangoldt * μ := by
  have h := logMoebius_mul_zeta
  calc logMoebius = logMoebius * 1 := (mul_one logMoebius).symm
    _ = logMoebius * (ζ * μ) := by rw [ArithmeticFunction.coe_zeta_mul_coe_moebius]
    _ = (logMoebius * ζ) * μ := (mul_assoc _ _ _).symm
    _ = ArithmeticFunction.vonMangoldt * μ := by rw [h]

end Conjectures.TwinPrimes.AdmissibleLongPrimePowerConvolution_aux

theorem Conjectures.TwinPrimes.AdmissibleLongPrimePowerConvolution :
    ∀ d : ℕ, 0<d → (∑ k ∈ d.divisors, (ArithmeticFunction.moebius (d/k) : ℝ)*ArithmeticFunction.vonMangoldt k) = -(ArithmeticFunction.moebius d : ℝ)*Real.log d := by
  intro d _
  have h := Conjectures.TwinPrimes.AdmissibleLongPrimePowerConvolution_aux.logMoebius_eq
  have hd := congrFun (congrArg DFunLike.coe h) d
  rw [Conjectures.TwinPrimes.AdmissibleLongPrimePowerConvolution_aux.logMoebius_apply] at hd
  rw [ArithmeticFunction.mul_apply] at hd
  rw [← Nat.sum_divisorsAntidiagonal
    (fun k m => (ArithmeticFunction.moebius m : ℝ) * ArithmeticFunction.vonMangoldt k)]
  refine ?_
  have hd' : (∑ i ∈ d.divisorsAntidiagonal,
      (ArithmeticFunction.moebius i.2 : ℝ) * ArithmeticFunction.vonMangoldt i.1) =
      -(ArithmeticFunction.moebius d : ℝ) * Real.log d := by
    calc (∑ i ∈ d.divisorsAntidiagonal,
          (ArithmeticFunction.moebius i.2 : ℝ) * ArithmeticFunction.vonMangoldt i.1)
        = ∑ x ∈ d.divisorsAntidiagonal,
          ArithmeticFunction.vonMangoldt x.1 * (ArithmeticFunction.moebius x.2 : ℝ) :=
          Finset.sum_congr rfl fun x _ => mul_comm _ _
      _ = -((ArithmeticFunction.moebius d : ℝ) * Real.log d) := hd.symm
      _ = -(ArithmeticFunction.moebius d : ℝ) * Real.log d := by ring
  exact hd'
