import Mathlib

namespace Conjectures.JoshiAbc

theorem MeanLinear :
    ∀ m : ℕ, 0 < m →
      ((Finset.Icc 1 m).sum (fun j => (j:ℝ)))/(m:ℝ) = ((2*(m:ℝ)+1)+1)/4 := by
  have hsum : ∀ m : ℕ, (Finset.Icc 1 m).sum (fun j => (j:ℝ)) = (m:ℝ)*((m:ℝ)+1)/2 := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (a := 1) (b := k) (by omega) (fun j : ℕ => (j:ℝ)), ih]
      push_cast
      ring
  intro m hm
  rw [hsum m]
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  field_simp
  ring

end Conjectures.JoshiAbc
