import Mathlib

theorem PEqualNP.Outside.L_goldbach_central_support_weighted_witness :
  let S := fun (n : ℕ) => (Finset.range (n+1)).filter (fun k => n<3*k ∧ 3*k<2*n); ∀ n (w:ℕ→ℝ), (∀ k,¬Nat.Prime k → w k=0) → 0<(∑ k ∈ (S n).filter (fun k => 2*k≠n),w k*w (n-k)) → ∃ p∈S n, ∃ q∈S n,Nat.Prime p ∧ Nat.Prime q ∧ p≠q ∧ p+q=n := by
  classical
  dsimp only
  intro n w hsupport hpos
  by_contra hnone
  apply ne_of_gt hpos
  apply Finset.sum_eq_zero
  intro k hk
  obtain ⟨hmem, hoff⟩ := Finset.mem_filter.mp hk
  by_cases hp : Nat.Prime k
  · by_cases hq : Nat.Prime (n - k)
    · exfalso
      obtain ⟨hrange, hlo, hhi⟩ := Finset.mem_filter.mp hmem
      have hklt := Finset.mem_range.mp hrange
      apply hnone
      refine ⟨k, hmem, n - k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩,
        hp, hq, by omega, by omega⟩
      constructor <;> omega
    · simp [hsupport (n - k) hq]
  · simp [hsupport k hp]
