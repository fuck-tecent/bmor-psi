import Mathlib

open scoped BigOperators

namespace Conjectures.TwinPrimes.HarmonicKernelCofactorError_aux

/-- The single step of the comparison: for `0 < u`,
`1/(u+1) ≤ log ((u+1)/u) ≤ 1/u`. -/
lemma log_succ_ratio {u : ℕ} (hu : 0 < u) :
    ((u : ℝ) + 1)⁻¹ ≤ Real.log (((u : ℝ) + 1) / (u : ℝ)) ∧
      Real.log (((u : ℝ) + 1) / (u : ℝ)) ≤ (u : ℝ)⁻¹ := by
  have hx : (0 : ℝ) < ((u : ℝ) + 1) / (u : ℝ) := by
    have hu' : (0 : ℝ) < (u : ℝ) := Nat.cast_pos.mpr hu
    positivity
  have h1 : Real.log (((u : ℝ) + 1) / (u : ℝ)) ≤ ((u : ℝ) + 1) / (u : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hx
  have h2 : 1 - (((u : ℝ) + 1) / (u : ℝ))⁻¹ ≤ Real.log (((u : ℝ) + 1) / (u : ℝ)) :=
    Real.one_sub_inv_le_log_of_pos hx
  have e1 : ((u : ℝ) + 1) / (u : ℝ) - 1 = (u : ℝ)⁻¹ := by
    field_simp
    ring
  have e2 : 1 - (((u : ℝ) + 1) / (u : ℝ))⁻¹ = ((u : ℝ) + 1)⁻¹ := by
    field_simp
    ring
  exact ⟨by linarith, by linarith⟩

/-- Two-sided telescoping bound: the harmonic sum over `[l, u)` exceeds
`log (u/l)` by at most `1/l - 1/u`. -/
lemma harmonic_window_error :
    ∀ u : ℕ, ∀ l : ℕ, 0 < l → l ≤ u →
      0 ≤ (∑ x ∈ Finset.Ico l u, (x : ℝ)⁻¹) - Real.log ((u : ℝ) / (l : ℝ)) ∧
      (∑ x ∈ Finset.Ico l u, (x : ℝ)⁻¹) - Real.log ((u : ℝ) / (l : ℝ)) ≤
        (l : ℝ)⁻¹ - (u : ℝ)⁻¹ := by
  intro u
  induction u with
  | zero =>
    intro l hl hlu
    omega
  | succ u ih =>
    intro l hl hlu
    by_cases h : l = u + 1
    · subst h
      have hsum : (∑ x ∈ Finset.Ico (u + 1) (u + 1), (x : ℝ)⁻¹) = 0 := by
        simp
      have hlog : Real.log (((u + 1 : ℕ) : ℝ) / ((u + 1 : ℕ) : ℝ)) = 0 := by
        rw [div_self (by positivity), Real.log_one]
      rw [hsum, hlog]
      have hz : (((u + 1 : ℕ) : ℝ))⁻¹ - (((u + 1 : ℕ) : ℝ))⁻¹ = 0 := by ring
      exact ⟨by norm_num, by rw [hz]; norm_num⟩
    · have hlu' : l ≤ u := by omega
      have hu : 0 < u := by omega
      have hsum : (∑ x ∈ Finset.Ico l (u + 1), (x : ℝ)⁻¹) =
          (∑ x ∈ Finset.Ico l u, (x : ℝ)⁻¹) + (u : ℝ)⁻¹ :=
        Finset.sum_Ico_succ_top hlu' _
      have hlog : Real.log (((u + 1 : ℕ) : ℝ) / (l : ℝ)) =
          Real.log ((u : ℝ) / (l : ℝ)) + Real.log (((u : ℝ) + 1) / (u : ℝ)) := by
        have hl' : (l : ℝ) ≠ 0 := by positivity
        have hu' : (u : ℝ) ≠ 0 := by positivity
        rw [← Real.log_mul (div_ne_zero hu' hl') (div_ne_zero (by positivity) hu')]
        congr 1
        push_cast
        field_simp
      have hstep := log_succ_ratio hu
      have ih' := ih l hl hlu'
      rw [hsum, hlog]
      constructor
      · have hlow : (0 : ℝ) ≤ (u : ℝ)⁻¹ - Real.log (((u : ℝ) + 1) / (u : ℝ)) := by
          linarith [hstep.2]
        linarith [ih'.1]
      · have hupp : (u : ℝ)⁻¹ - Real.log (((u : ℝ) + 1) / (u : ℝ)) ≤
            (u : ℝ)⁻¹ - ((u : ℝ) + 1)⁻¹ := by linarith [hstep.1]
        have hcast : (((u + 1 : ℕ) : ℝ))⁻¹ = ((u : ℝ) + 1)⁻¹ := by
          push_cast
          ring_nf
        linarith [ih'.2]

end Conjectures.TwinPrimes.HarmonicKernelCofactorError_aux

theorem Conjectures.TwinPrimes.HarmonicKernelCofactorError :
    ∀ l u : ℕ, 0<l → l≤u → |(∑ x ∈ Finset.Ico l u, (x : ℝ)⁻¹) - Real.log ((u : ℝ)/l)| ≤ (l : ℝ)⁻¹ := by
  intro l u hl hlu
  have h := Conjectures.TwinPrimes.HarmonicKernelCofactorError_aux.harmonic_window_error u l hl hlu
  have hnonneg : (0 : ℝ) ≤ (l : ℝ)⁻¹ := by positivity
  have huinv : (0 : ℝ) ≤ (u : ℝ)⁻¹ := by positivity
  rw [abs_le]
  refine ⟨by linarith [h.1, hnonneg], ?_⟩
  linarith [h.2]
