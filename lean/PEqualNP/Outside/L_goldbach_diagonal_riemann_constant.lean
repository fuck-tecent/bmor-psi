import Mathlib

open MeasureTheory
open scoped BigOperators

private theorem right_endpoint_error (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      |(∑ k ∈ Finset.Icc 1 n, f ((k : ℝ)/n))/(n:ℝ) -
          (∫ x in (0:ℝ)..1, f x)| ≤ K/(n:ℝ) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).bddAbove_image
    hf.continuous_deriv_one.norm.continuousOn
  let K := max M 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hbound (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) : ‖deriv f x‖ ≤ K :=
    (hM ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  refine ⟨K, hK, ?_⟩
  intro n hn
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  let a (k : ℕ) : ℝ := (k:ℝ)/n
  have ha0 : a 0 = 0 := by simp [a]
  have han : a n = 1 := div_self hnR.ne'
  have hwidth (k : ℕ) : a (k+1) - a k = (n:ℝ)⁻¹ := by
    simp [a, Nat.cast_add, add_div, one_div]
  have ha_le (k : ℕ) : a k ≤ a (k+1) :=
    sub_nonneg.mp ((hwidth k).symm ▸ inv_nonneg.mpr hnR.le)
  have ha_mem (k : ℕ) (hk : k ≤ n) : a k ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · change 0 ≤ (k:ℝ)/(n:ℝ)
      positivity
    · change (k:ℝ)/(n:ℝ) ≤ 1
      rw [div_le_iff₀ hnR, one_mul]
      exact_mod_cast hk
  have hint :
      (∑ k ∈ Finset.range n, ∫ x in a k..a (k+1), f x) = ∫ x in (0:ℝ)..1, f x := by
    rw [intervalIntegral.sum_integral_adjacent_intervals
      (fun k _ => hf.continuous.intervalIntegrable (a k) (a (k+1))), ha0, han]
  have hshift :
      (∑ k ∈ Finset.Icc 1 n, f (a k)) = ∑ k ∈ Finset.range n, f (a (k+1)) := by
    refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      exact Finset.mem_range.mpr (by omega)
    · intro k hk l hl he
      simp only [Finset.mem_Icc] at hk hl
      omega
    · intro k hk
      have hkn := Finset.mem_range.mp hk
      exact ⟨k+1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro k hk
      have hk1 := (Finset.mem_Icc.mp hk).1
      rw [Nat.sub_add_cancel hk1]
  have hlocal (k : ℕ) (hk : k < n) :
      |f (a (k+1))/(n:ℝ) - (∫ x in a k..a (k+1), f x)| ≤ K/(n:ℝ)^2 := by
    have hrewrite : f (a (k+1))/(n:ℝ) - (∫ x in a k..a (k+1), f x) =
        ∫ x in a k..a (k+1), f (a (k+1)) - f x := by
      rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
        (hf.continuous.intervalIntegrable _ _), intervalIntegral.integral_const,
        smul_eq_mul, hwidth]
      simp only [div_eq_mul_inv]
      ring
    rw [← Real.norm_eq_abs, hrewrite]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := K*(n:ℝ)⁻¹) (fun x hx => ?_)).trans ?_
    · rw [Set.uIoc_of_le (ha_le k)] at hx
      have x_mem : x ∈ Set.Icc (0:ℝ) 1 :=
        ⟨(ha_mem k hk.le).1.trans hx.1.le, hx.2.trans (ha_mem (k+1) hk).2⟩
      calc
        ‖f (a (k+1)) - f x‖ ≤ K * ‖a (k+1) - x‖ :=
          (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_deriv_le
            (fun y _ => hf.differentiable (by norm_num) y) hbound x_mem (ha_mem (k+1) hk)
        _ ≤ _ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hx.2), ← hwidth k]
          exact mul_le_mul_of_nonneg_left (by linarith [hx.1]) hK.le
    · rw [hwidth, abs_of_nonneg (inv_nonneg.mpr hnR.le)]
      simp [div_eq_mul_inv, pow_two, mul_assoc]
  change |(∑ k ∈ Finset.Icc 1 n, f (a k))/(n:ℝ) - (∫ x in (0:ℝ)..1, f x)| ≤ K/(n:ℝ)
  rw [hshift, Finset.sum_div, ← hint, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.range n, |f (a (k+1))/(n:ℝ) - (∫ x in a k..a (k+1), f x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ Finset.range n, K/(n:ℝ)^2 :=
      Finset.sum_le_sum (fun k hk => hlocal k (Finset.mem_range.mp hk))
    _ = _ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

theorem PEqualNP.Outside.L_goldbach_diagonal_riemann_constant :
    let g := fun (φ : ℝ → ℝ) (n k : ℕ) => Real.log (k:ℝ)*(φ ((k:ℝ)/n))^2; let c := fun φ : ℝ → ℝ => intervalIntegral (fun u : ℝ => (φ u)^2) 0 1 MeasureTheory.volume; let b := fun φ : ℝ → ℝ => intervalIntegral (fun u : ℝ => (φ u)^2*Real.log u) 0 1 MeasureTheory.volume; ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → (∀ u : ℝ, u < 1/3 ∨ 2/3 < u → φ u=0) → ∃ K : ℝ, 0<K ∧ ∀ n : ℕ, 2≤n → |(∑ k ∈ Finset.Icc 1 n, g φ n k)/(n:ℝ) - (c φ*Real.log (n:ℝ)+b φ)| ≤ K*Real.log (2*(n:ℝ))/(n:ℝ) := by
  dsimp only
  intro φ hφ hsupp
  let f (u : ℝ) := (φ u)^2
  let q (u : ℝ) := f u * Real.log u
  have hf : ContDiff ℝ 1 f := hφ.pow 2
  have hq : ContDiff ℝ 1 q := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = 0
    · subst x
      refine (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [gt_mem_nhds (show (0:ℝ) < 1/3 by norm_num)] with y hy
      simp [q, f, hsupp y (Or.inl hy)]
    · exact hf.contDiffAt.mul (Real.contDiffAt_log.mpr hx)
  obtain ⟨C, hC, hCf⟩ := right_endpoint_error f hf
  obtain ⟨D, hD, hDq⟩ := right_endpoint_error q hq
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  refine ⟨C + D / Real.log 2, add_pos hC (div_pos hD hlog2), ?_⟩
  intro n hn
  have hn0 : 0 < n := by omega
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn0
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hlogn : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg hn1
  have hlogn' : Real.log (n:ℝ) ≤ Real.log (2*(n:ℝ)) :=
    Real.log_le_log hnR (by linarith)
  have hlog2' : Real.log (2:ℝ) ≤ Real.log (2*(n:ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hs :
      (∑ k ∈ Finset.Icc 1 n, Real.log (k:ℝ)*f ((k:ℝ)/n)) =
        Real.log (n:ℝ)*(∑ k ∈ Finset.Icc 1 n, f ((k:ℝ)/n)) +
          ∑ k ∈ Finset.Icc 1 n, q ((k:ℝ)/n) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hkR : (k:ℝ) ≠ 0 := by
      exact_mod_cast (show k ≠ 0 by have := (Finset.mem_Icc.mp hk).1; omega)
    dsimp [q]
    rw [Real.log_div hkR hnR.ne']
    ring
  let ef := (∑ k ∈ Finset.Icc 1 n, f ((k:ℝ)/n))/(n:ℝ) - (∫ u in (0:ℝ)..1, f u)
  let eq := (∑ k ∈ Finset.Icc 1 n, q ((k:ℝ)/n))/(n:ℝ) - (∫ u in (0:ℝ)..1, q u)
  have hef : |ef| ≤ C/(n:ℝ) := hCf n hn0
  have heq : |eq| ≤ D/(n:ℝ) := hDq n hn0
  change |(∑ k ∈ Finset.Icc 1 n, Real.log (k:ℝ)*f ((k:ℝ)/n))/(n:ℝ) -
      ((∫ u in (0:ℝ)..1, f u)*Real.log (n:ℝ)+(∫ u in (0:ℝ)..1, q u))| ≤ _
  calc
    _ = |Real.log (n:ℝ)*ef + eq| := by
      rw [hs]
      congr 1
      dsimp [ef, eq]
      simp only [div_eq_mul_inv]
      ring
    _ ≤ |Real.log (n:ℝ)*ef| + |eq| := abs_add_le _ _
    _ ≤ Real.log (n:ℝ)*(C/(n:ℝ)) + D/(n:ℝ) := by
      rw [abs_mul, abs_of_nonneg hlogn]
      exact add_le_add (mul_le_mul_of_nonneg_left hef hlogn) heq
    _ = (C*Real.log (n:ℝ)+D)/(n:ℝ) := by
      simp only [div_eq_mul_inv]
      ring
    _ ≤ (C*Real.log (2*(n:ℝ))+(D/Real.log 2)*Real.log (2*(n:ℝ)))/(n:ℝ) := by
      apply div_le_div_of_nonneg_right _ hnR.le
      apply add_le_add (mul_le_mul_of_nonneg_left hlogn' hC.le)
      calc
        D = (D/Real.log 2)*Real.log 2 := (div_mul_cancel₀ _ hlog2.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hlog2' (div_pos hD hlog2).le
    _ = _ := by rw [add_mul]

