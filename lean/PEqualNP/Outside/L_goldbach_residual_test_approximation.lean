import Mathlib

theorem PEqualNP.Outside.L_goldbach_residual_test_approximation :
    let C := fun (x : ℕ) (a b : ℕ → ℝ) s => ∑ k ∈ (Finset.range (x+1)).filter (fun k => k ≤ s ∧ s-k ≤ x), a k*b (s-k); ∀ (x q c : ℕ) (a b g p : ℕ → ℝ) (δ : ℝ), let S := (Finset.range (2*x+1)).filter (fun s => s % q = c); (∀ s ∈ S, |g s-p s|≤δ) → 0≤δ → (∑ s ∈ S, p s*C x a b s)=0 → |∑ s ∈ S, g s*C x a b s| ≤ δ*(∑ i ∈ Finset.range (x+1), |a i|)*(∑ j ∈ Finset.range (x+1), |b j|) := by
  intro C x q c a b g p δ S hsup hδ hz
  let I := Finset.range (x+1)
  have hC (s : ℕ) : |C x a b s| ≤ ∑ i ∈ I, if i ≤ s ∧ s-i ≤ x then |a i| * |b (s-i)| else 0 := by
    rw [← Finset.sum_filter]
    simpa only [abs_mul] using
      (Finset.abs_sum_le_sum_abs (fun i => a i * b (s-i))
        (I.filter (fun i => i ≤ s ∧ s-i ≤ x)))
  have row (i : ℕ) : (∑ s ∈ S, if i ≤ s ∧ s-i ≤ x then |a i| * |b (s-i)| else 0) ≤
      |a i| * ∑ j ∈ I, |b j| := by
    let T := S.filter (fun s => i ≤ s ∧ s-i ≤ x)
    have sub : T.image (fun s => s-i) ⊆ I := by
      intro j hj
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hs).2.2)
    have inj : Set.InjOn (fun s : ℕ => s-i) (↑T : Set ℕ) := by
      intro s hs t ht heq
      change s-i = t-i at heq
      have hs' := (Finset.mem_filter.mp hs).2.1
      have ht' := (Finset.mem_filter.mp ht).2.1
      omega
    calc
      _ = |a i| * (∑ s ∈ T, |b (s-i)|) := by
        rw [Finset.mul_sum]
        exact (Finset.sum_filter _ _).symm
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [← Finset.sum_image inj (f := fun j => |b j|)]
        exact Finset.sum_le_sum_of_subset_of_nonneg sub (fun j _ _ => abs_nonneg _)
  have bound : (∑ s ∈ S, |C x a b s|) ≤ (∑ i ∈ I, |a i|) * ∑ j ∈ I, |b j| := by
    refine (Finset.sum_le_sum (fun s _ => hC s)).trans ?_
    rw [Finset.sum_comm, Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ => row i)
  have subtract : (∑ s ∈ S, (g s - p s)*C x a b s) = ∑ s ∈ S, g s*C x a b s := by
    simp only [sub_mul, Finset.sum_sub_distrib, hz, sub_zero]
  rw [← subtract, mul_assoc]
  calc
    _ ≤ ∑ s ∈ S, |(g s-p s)*C x a b s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ S, δ*|C x a b s| := Finset.sum_le_sum (fun s hs => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hsup s hs) (abs_nonneg _))
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left bound hδ
