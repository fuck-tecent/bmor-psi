import Mathlib

private theorem mean_minimizes {ι : Type*} (s : Finset ι) (a : ι → ℝ) (t : ℝ) :
    let μ := (∑ i ∈ s, a i) / (s.card : ℝ)
    (∑ i ∈ s, (a i - μ) ^ 2) ≤ ∑ i ∈ s, (a i - t) ^ 2 := by
  intro μ
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  have hcenter : (∑ i ∈ s, (a i - μ)) = 0 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, μ]
    field_simp [hcard]
    ring
  have hsplit : (∑ i ∈ s, (a i - t) ^ 2) =
      (∑ i ∈ s, (a i - μ) ^ 2) + (s.card : ℝ) * (μ - t) ^ 2 := by
    calc
      _ = ∑ i ∈ s, ((a i - μ) ^ 2 + (a i - μ) * (2 * (μ - t)) + (μ - t) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.sum_mul, hcenter, zero_mul, add_zero,
          Finset.sum_const, nsmul_eq_mul]
  rw [hsplit]
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

theorem PEqualNP.Outside.L_goldbach_theta_fiber_projection :
    ∀ (m r : ℕ) (c : Fin m → Fin r) (a : Fin m → ℝ) (b : Fin r → ℝ), let F := fun j => Finset.univ.filter (fun i => c i=j); let μ := fun j => (∑ i ∈ F j, a i)/((F j).card:ℝ); (∑ i, (a i-μ (c i))^2) ≤ ∑ i, (a i-b (c i))^2 := by
  intro m r c a b F μ
  have regroup (g : Fin r → ℝ) : (∑ i, (a i - g (c i)) ^ 2) =
      ∑ j, ∑ i ∈ F j, (a i - g j) ^ 2 := by
    calc
      _ = ∑ j, ∑ i ∈ F j, (a i - g (c i)) ^ 2 :=
        (Finset.sum_fiberwise Finset.univ c _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
  rw [regroup μ, regroup b]
  exact Finset.sum_le_sum (fun j _ => mean_minimizes (F j) a (b j))
