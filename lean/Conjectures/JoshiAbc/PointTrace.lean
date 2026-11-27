import Mathlib

theorem Conjectures.JoshiAbc.PointTrace :
    let A : Matrix (Fin 2) (Fin 2) ℚ := !![0,5;1,0]
    A.trace = 0 ∧ A.det ≠ 0 := by
  simp only
  constructor
  · simp [Matrix.trace_fin_two]
  · rw [Matrix.det_fin_two_of]
    norm_num
