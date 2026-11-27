import Mathlib

theorem PEqualNP.Outside.L_goldbach_mellin_admissible_witness :
    let Adm := fun φ : ℝ → ℝ => (∀ j : ℕ, ContDiff ℝ j φ) ∧ (∀ u, 0≤φ u ∧ φ u≤1) ∧ (∀ u, φ (1-u)=φ u) ∧ (∀ u, u < 1/3 ∨ 2/3 < u → φ u=0) ∧ (∀ u, 5/12≤u → u≤7/12 → φ u=1); ∃ φ : ℝ → ℝ, Adm φ := by
  dsimp only
  let ψ : ContDiffBump (1/2 : ℝ) := ⟨1/12, 1/6, by norm_num, by norm_num⟩
  refine ⟨fun u => ψ u * ψ (1 - u), ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ψ.contDiff.mul (ψ.contDiff.comp (contDiff_const.sub contDiff_id))
  · intro u
    refine ⟨mul_nonneg ψ.nonneg ψ.nonneg, ?_⟩
    calc ψ u * ψ (1-u) ≤ 1 * 1 := mul_le_mul ψ.le_one ψ.le_one ψ.nonneg zero_le_one
      _ = 1 := by norm_num
  · intro u
    show ψ (1-u) * ψ (1-(1-u)) = ψ u * ψ (1-u)
    rw [show 1 - (1 - u) = u by ring, mul_comm]
  · intro u hu
    have hz : ψ u = 0 := by
      apply ψ.zero_of_le_dist
      rw [Real.dist_eq]
      rcases hu with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    show ψ u * ψ (1-u) = 0
    rw [hz, zero_mul]
  · intro u h1 h2
    have hmem : ∀ v : ℝ, |v - 1/2| ≤ 1/12 → ψ v = 1 := by
      intro v hv
      apply ψ.one_of_mem_closedBall
      rw [Metric.mem_closedBall, Real.dist_eq]
      exact hv
    show ψ u * ψ (1-u) = 1
    rw [hmem u (by rw [abs_le]; constructor <;> linarith),
      hmem (1-u) (by rw [abs_le]; constructor <;> linarith), mul_one]