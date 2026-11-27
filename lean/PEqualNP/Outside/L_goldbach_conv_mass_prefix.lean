import Mathlib

theorem PEqualNP.Outside.L_goldbach_conv_mass_prefix :
    let conv := fun (u v : ℕ → ℝ) (n : ℕ) =>
      Finset.sum (Finset.range (n+1)) (fun k => u k*v (n-k))
    ∀ (u v : ℕ → ℝ) (N : ℕ),
      Finset.sum (Finset.range (N+1)) (conv u v) =
        Finset.sum (Finset.range (N+1))
          (fun p => u p * Finset.sum (Finset.range (N-p+1)) v) := by
  change ∀ (u v : ℕ → ℝ) (N : ℕ),
    (∑ n ∈ Finset.range (N+1), ∑ k ∈ Finset.range (n+1), u k * v (n-k)) =
      ∑ p ∈ Finset.range (N+1), u p * ∑ j ∈ Finset.range (N-p+1), v j
  intro u v N
  calc
    (∑ n ∈ Finset.range (N+1), ∑ k ∈ Finset.range (n+1), u k * v (n-k)) =
        ∑ p ∈ Finset.range (N+1), ∑ n ∈ Finset.Ico p (N+1), u p * v (n-p) := by
      refine Finset.sum_comm'
        (s := Finset.range (N+1)) (t := fun n => Finset.range (n+1))
        (t' := Finset.range (N+1)) (s' := fun p => Finset.Ico p (N+1))
        (f := fun n p => u p * v (n-p)) ?_
      intro n p
      simp only [Finset.mem_range, Finset.mem_Ico]
      omega
    _ = ∑ p ∈ Finset.range (N+1), u p * ∑ j ∈ Finset.range (N-p+1), v j := by
      apply Finset.sum_congr rfl
      intro p hp
      simp only [Finset.mem_range] at hp
      rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
      have hlen : N + 1 - p = N - p + 1 := by omega
      rw [hlen]
      apply Finset.sum_congr rfl
      intro j _
      have hsub : p + j - p = j := by omega
      rw [hsub]
