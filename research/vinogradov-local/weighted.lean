import Mathlib
open scoped BigOperators
noncomputable def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

lemma z_ne_one (t : ℝ) (hsin : Real.sin (Real.pi * t) ≠ 0) : E t ≠ 1 := by
  intro h
  unfold E at h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨m, hm⟩ := h
  have hR : (m : ℂ) * (2 * Real.pi * Complex.I) =
      (((m : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hR] at hm
  have hm' : ((2 * Real.pi * t : ℝ) : ℂ) = (((m : ℝ) * (2 * Real.pi) : ℝ) : ℂ) :=
    mul_right_cancel₀ Complex.I_ne_zero hm
  have ht : t = (m : ℝ) := by
    have hreal : 2 * Real.pi * t = (m : ℝ) * (2 * Real.pi) := Complex.ofReal_injective hm'
    field_simp [Real.pi_ne_zero] at hreal
    linarith
  have hsin0 : Real.sin (Real.pi * t) = 0 := by
    rw [show Real.pi * t = (m : ℝ) * Real.pi by rw [ht]; ring]
    exact Real.sin_int_mul_pi m
  exact hsin hsin0

lemma norm_geometric_sum_le (n : ℕ) (t : ℝ) (hsin : Real.sin (Real.pi * t) ≠ 0) :
    ‖∑ k ∈ Finset.range (n + 1), E ((k : ℝ) * t)‖ ≤
      1 / |Real.sin (Real.pi * t)| := by
  classical
  let z := E t
  have hz : z ≠ 1 := z_ne_one t hsin
  have hsum : ∑ k ∈ Finset.range (n + 1), E ((k : ℝ) * t) =
      ∑ k ∈ Finset.range (n + 1), z ^ k := by
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [z]
    unfold E
    rw [show (((2 * Real.pi * ((k : ℝ) * t) : ℝ) : ℂ) * Complex.I) =
        (k : ℂ) * (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) by
      push_cast
      ring]
    rw [Complex.exp_nat_mul]
  rw [hsum, geom_sum_eq hz (n + 1), norm_div]
  have hnum : ‖z ^ (n + 1) - 1‖ ≤ 2 := by
    have hz1 : ‖z‖ = 1 := by
      dsimp only [z, E]
      simpa only [mul_comm] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * t)
    calc
      ‖z ^ (n + 1) - 1‖ ≤ ‖z ^ (n + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [norm_pow, hz1]; simp
      _ = 2 := by norm_num
  have hden : ‖z - 1‖ = 2 * |Real.sin (Real.pi * t)| := by
    dsimp only [z, E]
    rw [show (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) =
        Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) by rw [mul_comm]]
    rw [Complex.norm_exp_I_mul_ofReal_sub_one]
    have harg : 2 * Real.pi * t / 2 = Real.pi * t := by ring
    rw [harg]
    rw [Real.norm_eq_abs, abs_mul, abs_two]
  rw [hden]
  have hsinpos : 0 < |Real.sin (Real.pi * t)| := abs_pos.mpr hsin
  field_simp [hsinpos.ne']
  nlinarith


lemma norm_geom_prefix_le (k : ℕ) (t : ℝ) (hsin : Real.sin (Real.pi * t) ≠ 0) :
    ‖∑ j ∈ Finset.range k, E ((j : ℝ) * t)‖ ≤ 1 / |Real.sin (Real.pi * t)| := by
  rcases k with _ | m
  · simp
  · simpa [Nat.succ_eq_add_one] using norm_geometric_sum_le m t hsin

lemma norm_weighted_geometric_sum_le (n : ℕ) (a : ℕ → ℝ) (t : ℝ)
    (hsin : Real.sin (Real.pi * t) ≠ 0) :
    ‖∑ k ∈ Finset.range (n + 1), (a k : ℂ) * E ((k : ℝ) * t)‖ ≤
      (|a n| + ∑ k ∈ Finset.range n, |a k - a (k + 1)|) /
        |Real.sin (Real.pi * t)| := by
  classical
  let z := E t
  have hz : z ≠ 1 := z_ne_one t hsin
  have hterm : ∀ k : ℕ, E ((k : ℝ) * t) = z ^ k := by
    intro k
    dsimp only [z]
    unfold E
    rw [show (((2 * Real.pi * ((k : ℝ) * t) : ℝ) : ℂ) * Complex.I) =
        (k : ℂ) * (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) by
      push_cast
      ring]
    rw [Complex.exp_nat_mul]
  simp_rw [hterm]
  let G : ℕ → ℂ := fun k => ∑ j ∈ Finset.range k, z ^ j
  have hG (k : ℕ) : ‖G k‖ ≤ 1 / |Real.sin (Real.pi * t)| := by
    dsimp only [G]
    simpa only [← hterm] using norm_geom_prefix_le k t hsin
  have hparts := Finset.sum_range_by_parts (fun i : ℕ => (a i : ℂ)) (fun i : ℕ => z ^ i) (n + 1)
  simp only [Nat.add_sub_cancel] at hparts
  have hparts' : ∑ i ∈ Finset.range (n + 1), (a i : ℂ) * z ^ i =
      (a n : ℂ) * (∑ i ∈ Finset.range (n + 1), z ^ i) -
        ∑ i ∈ Finset.range n, ((a (i + 1) : ℂ) - (a i : ℂ)) *
          (∑ j ∈ Finset.range (i + 1), z ^ j) := by
    simpa only [smul_eq_mul] using hparts
  rw [hparts']
  have hbound := norm_sub_le ((a n : ℂ) * G (n + 1))
    (∑ i ∈ Finset.range n, ((a (i + 1) : ℂ) - (a i : ℂ)) * G (i + 1))
  have hsumBound :
      ‖∑ i ∈ Finset.range n, ((a (i + 1) : ℂ) - (a i : ℂ)) * G (i + 1)‖ ≤
        ∑ i ∈ Finset.range n, |a i - a (i + 1)| * (1 / |Real.sin (Real.pi * t)|) := by
    calc
      _ ≤ ∑ i ∈ Finset.range n,
          ‖((a (i + 1) : ℂ) - (a i : ℂ)) * G (i + 1)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range n,
          |a i - a (i + 1)| * (1 / |Real.sin (Real.pi * t)|) := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul]
        have hcoef : ‖((a (i + 1) : ℂ) - (a i : ℂ))‖ = |a i - a (i + 1)| := by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
        rw [hcoef]
        exact mul_le_mul_of_nonneg_left (hG (i + 1)) (abs_nonneg _)
  have hfirst : ‖(a n : ℂ) * G (n + 1)‖ = |a n| * ‖G (n + 1)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hBs : 0 ≤ 1 / |Real.sin (Real.pi * t)| := by positivity
  calc
    ‖(a n : ℂ) * G (n + 1) -
        ∑ i ∈ Finset.range n, ((a (i + 1) : ℂ) - (a i : ℂ)) * G (i + 1)‖
        ≤ ‖(a n : ℂ) * G (n + 1)‖ +
            ‖∑ i ∈ Finset.range n, ((a (i + 1) : ℂ) - (a i : ℂ)) * G (i + 1)‖ := hbound
    _ ≤ |a n| * (1 / |Real.sin (Real.pi * t)|) +
          ∑ i ∈ Finset.range n, |a i - a (i + 1)| * (1 / |Real.sin (Real.pi * t)|) := by
      apply add_le_add
      · rw [hfirst]
        exact mul_le_mul_of_nonneg_left (hG (n + 1)) (abs_nonneg _)
      · exact hsumBound
    _ = (|a n| + ∑ i ∈ Finset.range n, |a i - a (i + 1)|) /
          |Real.sin (Real.pi * t)| := by
      rw [div_eq_mul_inv, ← Finset.sum_mul]
      ring
