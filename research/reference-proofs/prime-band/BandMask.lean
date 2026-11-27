import BandGeometry
import BandArithmetic

/-! Fourier coefficients of the actual catalogue minor-arc mask. -/

namespace GoldbachMinor

open Finset Set MeasureTheory
open scoped ComplexConjugate

noncomputable def mode (k : ℤ) (t : ℝ) : ℂ :=
  Complex.exp (((2*Real.pi*(k:ℝ)*t : ℝ):ℂ)*Complex.I)

theorem measurable_catalogue (Q n : ℕ) : MeasurableSet (catalogueArcs Q n) := by
  have eq : catalogueArcs Q n = ⋃ (q : ℕ) (a : ℕ)
      (_ : 1≤q ∧ q≤Q ∧ a≤q ∧ a.Coprime q),
      Icc ((a:ℝ)/q - (Q:ℝ)/(q*n)) ((a:ℝ)/q + (Q:ℝ)/(q*n)) := by
    ext t
    simp only [mem_iUnion, Set.mem_Icc, catalogueArcs, Set.mem_ofPred_eq, abs_le]
    constructor
    · rintro ⟨q,a,h₁,h₂,h₃,h₄,hl,hr⟩
      exact ⟨q,a,⟨h₁,h₂,h₃,h₄⟩,by linarith,by linarith⟩
    · rintro ⟨q,a,⟨h₁,h₂,h₃,h₄⟩,hl,hr⟩
      exact ⟨q,a,h₁,h₂,h₃,h₄,by linarith,by linarith⟩
  rw [eq]
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun _ => measurableSet_Icc

theorem integral_complement (A : Set ℝ) (hA : MeasurableSet A) (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ t in (0:ℝ)..1, Aᶜ.indicator f t) = (∫ t in (0:ℝ)..1, f t) -
      ∫ t in (0:ℝ)..1, A.indicator f t := by
  have hi : IntervalIntegrable (A.indicator f) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact (hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self).indicator hA
  rw [← intervalIntegral.integral_sub (hf.intervalIntegrable ..) hi]
  apply intervalIntegral.integral_congr
  intro t _
  by_cases ht : t ∈ A <;> simp [ht]

theorem mode_continuous (k : ℤ) : Continuous (mode k) := by unfold mode; fun_prop

private theorem mode_periodic (k : ℤ) : Function.Periodic (mode k) 1 := by
  intro t
  unfold mode
  calc
    _ = Complex.exp (((2*Real.pi*(k:ℝ)*t : ℝ):ℂ)*Complex.I) *
        Complex.exp ((k:ℂ)*(2*Real.pi*Complex.I)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    _ = _ := by rw [Complex.exp_int_mul_two_pi_mul_I, mul_one]

private theorem mode_neg (k : ℤ) (t : ℝ) : mode (-k) t = conj (mode k t) := by
  unfold mode
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

private theorem full_mode (k : ℕ) (hk : 0 < k) : (∫ t in (0:ℝ)..1, mode (k:ℤ) t) = 0 := by
  let c : ℂ := (k:ℂ)*(2*Real.pi*Complex.I)
  have hc : c ≠ 0 := by
    dsimp [c]; exact mul_ne_zero (by exact_mod_cast hk.ne') (mul_ne_zero (by exact_mod_cast (mul_ne_zero (by norm_num : (2:ℝ)≠0) Real.pi_ne_zero)) Complex.I_ne_zero)
  have he (t : ℝ) : mode (k:ℤ) t = Complex.exp (c*t) := by
    unfold mode c; congr 1; push_cast; ring
  simp_rw [he]
  rw [integral_exp_mul_complex hc]
  simp [c, Complex.exp_nat_mul_two_pi_mul_I]

private theorem ram_cast (q k : ℕ) : (ram q k : ℂ) = ∑ d ∈ q.divisors,
    (if d ∣ k then (d:ℂ) else 0) * (ArithmeticFunction.moebius (q/d):ℂ) := by
  unfold ram
  push_cast
  apply sum_congr rfl
  intro d _
  split_ifs <;> simp

private theorem major_pos_mode (Q n k : ℕ) (hscale : 2*Q^2<n) (hk : 0<k) :
    (∫ t in (0:ℝ)..1, (catalogueArcs Q n).indicator (mode (k:ℤ)) t) =
      (majorCoefficient Q n k:ℂ) := by
  rw [catalogue_major_periodic _ _ hscale _ (mode_continuous _) (mode_periodic _)]
  unfold majorCoefficient
  rw [Complex.ofReal_sum]
  apply sum_congr rfl
  intro q hq
  rw [Complex.ofReal_mul, ram_cast]
  simpa only [mode, Int.cast_natCast] using GoldbachRamanujan.arcs_at_denominator
    (Finset.mem_Icc.mp hq).1 hk ((Q:ℝ)/(q*n))

private theorem major_zero (Q n : ℕ) (hscale : 2*Q^2<n) :
    (∫ t in (0:ℝ)..1, (catalogueArcs Q n).indicator (mode 0) t) = (arcLength Q n:ℂ) := by
  rw [catalogue_major_periodic _ _ hscale _ (mode_continuous _) (mode_periodic _)]
  unfold arcLength
  rw [Complex.ofReal_sum]
  apply sum_congr rfl
  intro q _
  have hcard : ((range q).filter (·.Coprime q)).card = q.totient := by
    rw [Nat.totient_eq_card_coprime]; congr 1; ext a; simp only [mem_filter]; exact and_congr_right fun _ => Nat.coprime_comm
  have hint (a : ℕ) : (∫ t in ((a:ℝ)/q-(Q:ℝ)/(q*n))..((a:ℝ)/q+(Q:ℝ)/(q*n)), mode 0 t)
      = ((2*(Q:ℝ)/(q*n):ℝ):ℂ) := by
    simp [mode, intervalIntegral.integral_const, Complex.real_smul]
    ring
  simp_rw [hint]
  simp [hcard, nsmul_eq_mul]

/-- Fourier multiplier of the exact catalogue minor-arc mask, including the zero
mode and both signs of every integer frequency. -/
theorem minor_mode (Q n : ℕ) (hscale : 2*Q^2<n) (k : ℤ) :
    (∫ t in (0:ℝ)..1, (catalogueArcs Q n)ᶜ.indicator (mode k) t) =
      (minorCoefficient Q n k.natAbs:ℂ) := by
  have nat_mode (j : ℕ) : (∫ t in (0:ℝ)..1, (catalogueArcs Q n)ᶜ.indicator (mode (j:ℤ)) t) =
      (minorCoefficient Q n j:ℂ) := by
    rw [integral_complement _ (measurable_catalogue ..) _ (mode_continuous _)]
    rcases j with _ | j
    · rw [Nat.cast_zero,major_zero Q n hscale]
      simp [mode, minorCoefficient, intervalIntegral.integral_const]
    · rw [full_mode _ (Nat.succ_pos _), major_pos_mode _ _ _ hscale (Nat.succ_pos _)]
      simp [minorCoefficient]
  cases k with
  | ofNat j => exact nat_mode j
  | negSucc j =>
    change (∫ t in (0:ℝ)..1, (catalogueArcs Q n)ᶜ.indicator (mode (-((j+1:ℕ):ℤ))) t) = _
    have hm (t : ℝ) : (catalogueArcs Q n)ᶜ.indicator (mode (-((j+1:ℕ):ℤ))) t =
        conj ((catalogueArcs Q n)ᶜ.indicator (mode ((j+1:ℕ):ℤ)) t) := by
      by_cases h : t ∈ (catalogueArcs Q n)ᶜ
      · simp only [Set.indicator_of_mem h]; exact mode_neg _ t
      · simp only [Set.indicator_of_notMem h, map_zero]
    simp_rw [hm]
    rw [intervalIntegral.intervalIntegral_conj, nat_mode, Complex.conj_ofReal]
    rfl

end GoldbachMinor
