import Mathlib

namespace Conjectures.TwinPrimes.IntegerScaleOrdinatePairKernel_aux

noncomputable def phi (θ : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((θ * Real.log t : ℝ) : ℂ))

lemma norm_phi (θ t : ℝ) : ‖phi θ t‖ = 1 := by
  unfold phi
  rw [mul_comm, Complex.norm_exp_ofReal_mul_I]

lemma continuousOn_phi (θ : ℝ) : ContinuousOn (phi θ) (Set.Ioi 0) := by
  have h1 : ContinuousOn (fun t : ℝ => θ * Real.log t) (Set.Ioi 0) :=
    continuousOn_const.mul
      (Real.continuousOn_log.mono (fun t ht => ne_of_gt (Set.mem_Ioi.mp ht)))
  have h2 : Continuous (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  exact h2.comp_continuousOn h1

lemma norm_phi_sub_le (θ : ℝ) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    ‖phi θ t - phi θ s‖ ≤ |θ| * ((t - s) / s) := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hlog : Real.log s ≤ Real.log t := Real.log_le_log hs hst
  have hdiff : Real.log t - Real.log s ≤ (t - s) / s := by
    have h := Real.log_le_sub_one_of_pos (div_pos ht hs)
    rw [Real.log_div ht.ne' hs.ne'] at h
    have h2 : (t - s) / s = t / s - 1 := by
      field_simp
    linarith
  have key : phi θ t - phi θ s =
      phi θ s * (Complex.exp (Complex.I * ((θ * (Real.log t - Real.log s) : ℝ) : ℂ)) - 1) := by
    unfold phi
    have h1 : Complex.I * ((θ * Real.log t : ℝ) : ℂ) =
        Complex.I * ((θ * Real.log s : ℝ) : ℂ) +
          Complex.I * ((θ * (Real.log t - Real.log s) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h1, Complex.exp_add]
    ring
  rw [key, norm_mul, norm_phi, one_mul]
  have hsin : ‖Complex.exp (Complex.I * ((θ * (Real.log t - Real.log s) : ℝ) : ℂ)) - 1‖ =
      ‖2 * Real.sin (θ * (Real.log t - Real.log s) / 2)‖ :=
    Complex.norm_exp_I_mul_ofReal_sub_one _
  rw [hsin, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have h3 : |Real.sin (θ * (Real.log t - Real.log s) / 2)| ≤
      |θ * (Real.log t - Real.log s) / 2| := Real.abs_sin_le_abs
  have h4 : |θ * (Real.log t - Real.log s) / 2| = |θ| * (Real.log t - Real.log s) / 2 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have hnn : 0 ≤ Real.log t - Real.log s := by linarith
    rw [abs_of_nonneg hnn]
  have h5 : |θ| * (Real.log t - Real.log s) ≤ |θ| * ((t - s) / s) :=
    mul_le_mul_of_nonneg_left hdiff (abs_nonneg θ)
  linarith

lemma cell_bound (θ : ℝ) {X u : ℝ} (hu : 0 < u) (hXu : u ≤ X) :
    ‖phi θ X - ∫ t in X..(X + 1), phi θ t‖ ≤ |θ| / u := by
  have hX : 0 < X := lt_of_lt_of_le hu hXu
  have hint : IntervalIntegrable (phi θ) MeasureTheory.volume X (X + 1) := by
    apply ContinuousOn.intervalIntegrable
    refine (continuousOn_phi θ).mono ?_
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    exact Set.mem_Ioi.mpr (lt_of_lt_of_le hX ht.1)
  have hEq : phi θ X - ∫ t in X..(X + 1), phi θ t =
      ∫ t in X..(X + 1), (phi θ X - phi θ t) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hint,
      intervalIntegral.integral_const]
    simp [add_sub_cancel_left]
  rw [hEq]
  have hbound : ∀ t ∈ Set.uIoc X (X + 1), ‖phi θ X - phi θ t‖ ≤ |θ| / u := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    have htX : X ≤ t := le_of_lt ht.1
    rw [norm_sub_rev]
    refine (norm_phi_sub_le θ hX htX).trans ?_
    have h1 : (t - X) / X ≤ 1 / u := by
      rw [div_le_div_iff₀ hX hu]
      calc (t - X) * u ≤ 1 * u :=
            mul_le_mul_of_nonneg_right (by linarith [ht.2]) (le_of_lt hu)
        _ ≤ 1 * X := by linarith
    calc |θ| * ((t - X) / X) ≤ |θ| * (1 / u) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg θ)
      _ = |θ| / u := by ring
  calc ‖∫ t in X..(X + 1), (phi θ X - phi θ t)‖
      ≤ (|θ| / u) * |X + 1 - X| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = |θ| / u := by rw [add_sub_cancel_left, abs_one, mul_one]

end Conjectures.TwinPrimes.IntegerScaleOrdinatePairKernel_aux

open Conjectures.TwinPrimes.IntegerScaleOrdinatePairKernel_aux

theorem Conjectures.TwinPrimes.IntegerScaleOrdinatePairKernel :
    ∀ (Y u v : ℕ) (θ : ℝ), 1≤Y → Y≤u → u≤v → v≤2*Y →
      ‖(∑ X ∈ Finset.Ico u v, Complex.exp (Complex.I * (θ * Real.log X : ℝ))) -
        ∫ t in (u:ℝ)..(v:ℝ), Complex.exp (Complex.I * (θ * Real.log t : ℝ))‖ ≤ 1+|θ| := by
  intro Y u v θ hY hu huv hvY
  have hu1 : 1 ≤ u := le_trans hY hu
  have huR : (0:ℝ) < (u:ℝ) := by exact_mod_cast hu1
  have hvU : v - u ≤ u := by omega
  have hsum : ∫ t in (u:ℝ)..(v:ℝ), phi θ t =
      ∑ X ∈ Finset.Ico u v, ∫ t in (X:ℝ)..((X + 1 : ℕ):ℝ), phi θ t := by
    symm
    refine intervalIntegral.sum_integral_adjacent_intervals_Ico huv ?_
    intro k hk
    rw [Set.mem_Ico] at hk
    have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast (lt_of_lt_of_le hu1 hk.1)
    apply ContinuousOn.intervalIntegrable
    refine (continuousOn_phi θ).mono ?_
    intro t ht
    have hle : (k:ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_succ k)
    rw [Set.uIcc_of_le hle] at ht
    exact Set.mem_Ioi.mpr (lt_of_lt_of_le hk0 ht.1)
  have hmain : ‖∑ X ∈ Finset.Ico u v,
      (phi θ (X:ℝ) - ∫ t in (X:ℝ)..((X + 1 : ℕ):ℝ), phi θ t)‖ ≤ |θ| := by
    calc ‖∑ X ∈ Finset.Ico u v,
          (phi θ (X:ℝ) - ∫ t in (X:ℝ)..((X + 1 : ℕ):ℝ), phi θ t)‖
        ≤ ∑ X ∈ Finset.Ico u v,
            ‖phi θ (X:ℝ) - ∫ t in (X:ℝ)..((X + 1 : ℕ):ℝ), phi θ t‖ := norm_sum_le _ _
      _ ≤ ∑ _X ∈ Finset.Ico u v, |θ| / (u:ℝ) := by
          refine Finset.sum_le_sum ?_
          intro k hk
          rw [Finset.mem_Ico] at hk
          have hku : (u:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk.1
          have h := cell_bound θ huR hku
          simpa [Nat.cast_add, Nat.cast_one] using h
      _ = ((Finset.Ico u v).card : ℝ) * (|θ| / (u:ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((v - u : ℕ) : ℝ) * (|θ| / (u:ℝ)) := by rw [Nat.card_Ico]
      _ ≤ (u:ℝ) * (|θ| / (u:ℝ)) := by
          have hcard : ((v - u : ℕ) : ℝ) ≤ (u : ℝ) := by exact_mod_cast hvU
          exact mul_le_mul_of_nonneg_right hcard
            (div_nonneg (abs_nonneg θ) (le_of_lt huR))
      _ = |θ| := by field_simp
  change ‖(∑ X ∈ Finset.Ico u v, phi θ (X:ℝ)) - ∫ t in (u:ℝ)..(v:ℝ), phi θ t‖ ≤ 1 + |θ|
  have hdiff : (∑ X ∈ Finset.Ico u v, phi θ (X:ℝ)) - ∫ t in (u:ℝ)..(v:ℝ), phi θ t =
      ∑ X ∈ Finset.Ico u v,
        (phi θ (X:ℝ) - ∫ t in (X:ℝ)..((X + 1 : ℕ):ℝ), phi θ t) := by
    rw [hsum, Finset.sum_sub_distrib]
  rw [hdiff]
  linarith
