import Mathlib

namespace Conjectures.Goldbach.TypeIHyperbolaBound_aux

noncomputable def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

noncomputable def cap (H : ℕ) (x : ℝ) : ℝ :=
  if E x = 1 then (H : ℝ) else min (H : ℝ) (2 / ‖1 - E x‖)

theorem norm_E (y : ℝ) : ‖E y‖ = 1 := by
  unfold E
  exact Complex.norm_exp_ofReal_mul_I _

theorem E_nat_mul (x : ℝ) (k : ℕ) : E ((k : ℝ) * x) = (E x) ^ k := by
  unfold E
  have hexp : (((2 * Real.pi * ((k : ℝ) * x) : ℝ) : ℂ) * Complex.I)
      = ((k : ℂ) * (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)) := by
    push_cast
    ring
  rw [hexp, Complex.exp_nat_mul]

theorem sum_Icc_one_pow (z : ℂ) (M : ℕ) :
    (∑ k ∈ Finset.Icc 1 M, z ^ k) = z * ∑ i ∈ Finset.range M, z ^ i := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hset : Finset.Icc 1 (M + 1) = insert (M + 1) (Finset.Icc 1 M) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hset, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih,
      Finset.sum_range_succ, pow_succ']
    ring

theorem sum_ones (M : ℕ) : (∑ _ ∈ Finset.range M, (1 : ℝ)) = (M : ℝ) := by simp

theorem bound_aux (M : ℕ) (x : ℝ) :
    ‖∑ k ∈ Finset.Icc 1 M, E ((k : ℝ) * x)‖ ≤ cap M x := by
  have hz : ‖E x‖ = 1 := norm_E x
  have hsum : (∑ k ∈ Finset.Icc 1 M, E ((k : ℝ) * x))
      = E x * ∑ i ∈ Finset.range M, (E x) ^ i := by
    rw [← sum_Icc_one_pow (E x) M]
    exact Finset.sum_congr rfl (fun k _ => E_nat_mul x k)
  have h1 : ‖∑ k ∈ Finset.Icc 1 M, E ((k : ℝ) * x)‖ ≤ (M : ℝ) := by
    rw [hsum, norm_mul, hz, one_mul]
    calc ‖∑ i ∈ Finset.range M, (E x) ^ i‖
        ≤ ∑ i ∈ Finset.range M, ‖(E x) ^ i‖ := norm_sum_le _ _
      _ = ∑ i ∈ Finset.range M, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro _ _
          rw [norm_pow, hz, one_pow]
      _ = (M : ℝ) := sum_ones M
  have h2 : E x ≠ 1 → ‖∑ k ∈ Finset.Icc 1 M, E ((k : ℝ) * x)‖ ≤ 2 / ‖1 - E x‖ := by
    intro hne
    rw [hsum, norm_mul, hz, one_mul, geom_sum_eq hne M, norm_div]
    have hnum : ‖(E x) ^ M - 1‖ ≤ 2 := by
      calc ‖(E x) ^ M - 1‖ ≤ ‖(E x) ^ M‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hz, one_pow]; norm_num
    have hden : ‖E x - 1‖ = ‖1 - E x‖ := by
      rw [show (1 : ℂ) - E x = -(E x - 1) by ring, norm_neg]
    rw [hden]
    exact div_le_div_of_nonneg_right hnum (norm_nonneg _)
  unfold cap
  split_ifs with h
  · exact h1
  · exact le_min h1 (h2 h)

theorem main_bound (N D : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖∑ d ∈ Finset.Icc 1 D, a d * ∑ k ∈ Finset.Icc 1 (N / d), E ((d : ℝ) * (k : ℝ) * t)‖
      ≤ ∑ d ∈ Finset.Icc 1 D, ‖a d‖ * cap (N / d) ((d : ℝ) * t) := by
  have step : ∀ d : ℕ, ‖∑ k ∈ Finset.Icc 1 (N / d), E ((d : ℝ) * (k : ℝ) * t)‖
      ≤ cap (N / d) ((d : ℝ) * t) := by
    intro d
    have hrw : ∀ k : ℕ, E ((d : ℝ) * (k : ℝ) * t) = E ((k : ℝ) * ((d : ℝ) * t)) := by
      intro k
      congr 1
      ring
    rw [Finset.sum_congr rfl (fun k _ => hrw k)]
    exact bound_aux (N / d) ((d : ℝ) * t)
  calc ‖∑ d ∈ Finset.Icc 1 D, a d * ∑ k ∈ Finset.Icc 1 (N / d), E ((d : ℝ) * (k : ℝ) * t)‖
      ≤ ∑ d ∈ Finset.Icc 1 D,
          ‖a d * ∑ k ∈ Finset.Icc 1 (N / d), E ((d : ℝ) * (k : ℝ) * t)‖ := norm_sum_le _ _
    _ = ∑ d ∈ Finset.Icc 1 D,
          ‖a d‖ * ‖∑ k ∈ Finset.Icc 1 (N / d), E ((d : ℝ) * (k : ℝ) * t)‖ := by
        apply Finset.sum_congr rfl
        intro d _
        rw [norm_mul]
    _ ≤ ∑ d ∈ Finset.Icc 1 D, ‖a d‖ * cap (N / d) ((d : ℝ) * t) := by
        apply Finset.sum_le_sum
        intro d _
        exact mul_le_mul_of_nonneg_left (step d) (norm_nonneg _)

end Conjectures.Goldbach.TypeIHyperbolaBound_aux

theorem Conjectures.Goldbach.TypeIHyperbolaBound :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let cap (H : ℕ) (x : ℝ) := if E x = 1 then (H : ℝ) else min (H : ℝ) (2 / ‖1 - E x‖); ∀ (N D : ℕ) (a : ℕ → ℂ) (t : ℝ), ‖∑ d ∈ Finset.Icc 1 D, a d * ∑ k ∈ Finset.Icc 1 (N / d), E ((d : ℝ) * (k : ℝ) * t)‖ ≤ ∑ d ∈ Finset.Icc 1 D, ‖a d‖ * cap (N / d) ((d : ℝ) * t) :=
  Conjectures.Goldbach.TypeIHyperbolaBound_aux.main_bound
