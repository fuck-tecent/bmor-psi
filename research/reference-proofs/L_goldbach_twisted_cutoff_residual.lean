import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.Tactic



namespace GoldbachReciprocalResidual

noncomputable def cutoff (c : ℝ) (n : ℕ) : ℂ :=
  if 1 ≤ n ∧ (n : ℝ) < c then ((Real.log c - Real.log n : ℝ) : ℂ) else 0

noncomputable def residual (c : ℝ) : ℕ → ℂ :=
  (Real.log c : ℂ) • LSeries.delta - (LSeries.convolution (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) (cutoff c))

private theorem cutoff_bounded {c : ℝ} (hc : 1 ≤ c) (n : ℕ) :
    ‖cutoff c n‖ ≤ Real.log c := by
  unfold cutoff
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    · linarith [Real.log_nonneg (show 1 ≤ (n : ℝ) by exact_mod_cast h.1)]
    · exact sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast Nat.zero_lt_of_lt h.1) h.2.le)
  · simpa using Real.log_nonneg hc

/-- The complementary Möbius convolution has a fixed, finite numerator.
    The identity holds on the half-plane of absolute convergence. -/
theorem twisted_residual {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {c : ℝ} (hc : 1 ≤ c) {s : ℂ} (hs : 1 < s.re) :
    LSeries ((fun n : ℕ => χ (n : ZMod N)) * residual c) s =
      (Real.log c : ℂ) - LSeries ((fun n : ℕ => χ (n : ZMod N)) * cutoff c) s / χ.LFunction s := by
  have hcSum : LSeriesSummable (cutoff c) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => cutoff_bounded hc n) hs
  have hmu := DirichletCharacter.LSeriesSummable_mul χ
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  have hcut := DirichletCharacter.LSeriesSummable_mul χ hcSum
  have hdelta : LSeriesSummable LSeries.delta s := by
    exact LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => by
      simp [LSeries.delta]; split_ifs <;> simp) hs
  have hpoint : (fun n : ℕ => χ (n : ZMod N)) * residual c =
      (Real.log c : ℂ) • LSeries.delta -
      (LSeries.convolution ((fun n : ℕ => χ (n : ZMod N)) * (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ))) ((fun n : ℕ => χ (n : ZMod N)) * cutoff c)) := by
    rw [DirichletCharacter.mul_convolution_distrib]
    unfold residual
    rw [mul_sub, mul_smul_comm, DirichletCharacter.mul_delta]
  rw [hpoint, LSeries_sub (hdelta.smul _) (hmu.convolution hcut),
      LSeries_smul, LSeries_delta, Pi.one_apply, mul_one,
      LSeries_convolution' hmu hcut, χ.LFunction_eq_LSeries hs]
  congr 1
  apply (eq_div_iff (DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hs)).2
  have h := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  calc
    _ = LSeries ((fun n : ℕ => χ (n : ZMod N)) * cutoff c) s *
        (LSeries (fun n : ℕ => χ (n : ZMod N)) s * LSeries ((fun n : ℕ => χ (n : ZMod N)) * (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ))) s) := by ring
    _ = _ := by rw [h, mul_one]

end GoldbachReciprocalResidual

theorem PEqualNP.Outside.L_goldbach_twisted_cutoff_residual :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (c : ℝ) (s : ℂ), 1 ≤ c → 1 < s.re → let w : ℕ → ℂ := fun n => if 1 ≤ n ∧ (n : ℝ) < c then ((Real.log c - Real.log (n : ℝ) : ℝ) : ℂ) else 0; let r : ℕ → ℂ := (Real.log c : ℂ) • LSeries.delta - LSeries.convolution (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) w; LSeries (fun n : ℕ => χ (n : ZMod N) * r n) s = (Real.log c : ℂ) - LSeries (fun n : ℕ => χ (n : ZMod N) * w n) s / χ.LFunction s := by
  intro N inst χ c s hc hs
  exact GoldbachReciprocalResidual.twisted_residual χ hc hs
