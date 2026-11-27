import Mathlib

namespace Conjectures.JoshiAbc.MeanSquare_aux

lemma sum_sq_Icc (m : ℕ) :
    ((Finset.Icc 1 m).sum (fun j => (j:ℝ)^2)) = (m:ℝ)*((m:ℝ)+1)*(2*(m:ℝ)+1)/6 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih]
    push_cast
    ring

end Conjectures.JoshiAbc.MeanSquare_aux

theorem Conjectures.JoshiAbc.MeanSquare :
∀ m : ℕ, 0 < m → ((Finset.Icc 1 m).sum (fun j => (j:ℝ)^2))/(m:ℝ) = (2*(m:ℝ)+1)*(2*(m:ℝ)+2)/12 := by
  intro m hm
  rw [Conjectures.JoshiAbc.MeanSquare_aux.sum_sq_Icc]
  have hm0 : (m:ℝ) ≠ 0 := by
    have hpos : (0:ℕ) < m := hm
    exact_mod_cast (ne_of_gt hpos)
  field_simp
  ring
