import Mathlib

theorem PEqualNP.Outside.L_goldbach_window_square_lipschitz : ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → ∃ L : ℝ, 0≤L ∧ ∀ u ∈ Set.Icc (0:ℝ) 1, ∀ v ∈ Set.Icc (0:ℝ) 1, |φ u ^ 2 - φ v ^ 2| ≤ L*|u-v| := by
  intro φ hφ
  have hsq : ContDiff ℝ 1 (fun u : ℝ => φ u ^ 2) := hφ.pow 2
  obtain ⟨K, hK⟩ := (hsq.contDiffOn (s := Set.Icc (0 : ℝ) 1)).exists_lipschitzOnWith
    (by norm_num) (convex_Icc _ _) isCompact_Icc
  refine ⟨(K : ℝ), K.property, ?_⟩
  intro u hu v hv
  simpa only [Real.dist_eq] using hK.dist_le_mul u hu v hv
