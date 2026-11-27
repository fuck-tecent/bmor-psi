import Mathlib

theorem PEqualNP.Outside.L_goldbach_theta_partition_refinement :
    ∀ (m r s : ℕ) (c : Fin m → Fin r) (h : Fin r → Fin s) (a : Fin m → ℝ), let B := fun (q : ℕ) (f : Fin m → Fin q) i => let F := Finset.univ.filter (fun k => f k=f i); (∑ k ∈ F, a k)/(F.card:ℝ); (∑ i, (a i-B s (h ∘ c) i)^2) - (∑ i, (a i-B r c i)^2) = ∑ i, (B r c i-B s (h ∘ c) i)^2 := by
  intro m r s c h a B
  let F (j : Fin r) := Finset.univ.filter (fun k => c k = j)
  let fine (j : Fin r) := (∑ i ∈ F j, a i) / ((F j).card : ℝ)
  let coarse (j : Fin r) :=
    let G := Finset.univ.filter (fun k => h (c k) = h j)
    (∑ i ∈ G, a i) / (G.card : ℝ)
  change (∑ i, (a i - coarse (c i)) ^ 2) - (∑ i, (a i - fine (c i)) ^ 2) =
    ∑ i, (fine (c i) - coarse (c i)) ^ 2
  have centered (j : Fin r) : (∑ i ∈ F j, (a i - fine j)) = 0 := by
    by_cases hj : (F j).Nonempty
    · have hc : ((F j).card : ℝ) ≠ 0 := by exact_mod_cast hj.card_pos.ne'
      simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, fine]
      field_simp [hc]
      ring
    · simp [Finset.not_nonempty_iff_eq_empty.mp hj]
  -- Both means are constant on each fine fiber, so its mixed term vanishes.
  have cross : (∑ i, (a i - fine (c i)) * (fine (c i) - coarse (c i))) = 0 := by
    rw [← Finset.sum_fiberwise Finset.univ c]
    apply Finset.sum_eq_zero
    intro j _
    calc
      _ = ∑ i ∈ F j, (a i - fine j) * (fine j - coarse j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
      _ = 0 := by rw [← Finset.sum_mul, centered, zero_mul]
  calc
    _ = (∑ i, (fine (c i) - coarse (c i)) ^ 2) +
        (∑ i, (a i - fine (c i)) * (fine (c i) - coarse (c i))) * 2 := by
      rw [← Finset.sum_sub_distrib, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [cross, zero_mul, add_zero]
