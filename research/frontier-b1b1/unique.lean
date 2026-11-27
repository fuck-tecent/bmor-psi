import Mathlib
open scoped BigOperators

noncomputable section
namespace B1B1

/-- At most one numerator per denominator: if `2H < n`, two arcs with the same
denominator `q` that both contain `t` have the same centre. -/
lemma arc_unique_per_denominator (n : ℕ) (H : ℝ) (hH : 0 ≤ H) (hn : 2*H < (n:ℝ))
    {q : ℕ} (hq : 0 < q) {a a' : ℕ} {t : ℝ}
    (h1 : |t - (a:ℝ)/(q:ℝ)| ≤ H/((q:ℝ)*(n:ℝ)))
    (h2 : |t - (a':ℝ)/(q:ℝ)| ≤ H/((q:ℝ)*(n:ℝ)))
    (hne : a ≠ a') : False := by
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  have hdist : |(a:ℝ)/(q:ℝ) - (a':ℝ)/(q:ℝ)| ≤ 2*H/((q:ℝ)*(n:ℝ)) := by
    calc |(a:ℝ)/(q:ℝ) - (a':ℝ)/(q:ℝ)|
        = |((a:ℝ)/(q:ℝ) - t) + (t - (a':ℝ)/(q:ℝ))| := by ring_nf
      _ ≤ |(a:ℝ)/(q:ℝ) - t| + |t - (a':ℝ)/(q:ℝ)| := abs_add_le _ _
      _ = |t - (a:ℝ)/(q:ℝ)| + |t - (a':ℝ)/(q:ℝ)| := by rw [abs_sub_comm]
      _ ≤ H/((q:ℝ)*(n:ℝ)) + H/((q:ℝ)*(n:ℝ)) := add_le_add h1 h2
      _ = 2*H/((q:ℝ)*(n:ℝ)) := by ring
  have hge : (1:ℝ)/(q:ℝ) ≤ |(a:ℝ)/(q:ℝ) - (a':ℝ)/(q:ℝ)| := by
    have habs : (1:ℤ) ≤ |(a:ℤ) - (a':ℤ)| := Int.one_le_abs (by omega)
    rw [show (a:ℝ)/(q:ℝ) - (a':ℝ)/(q:ℝ) = (((a:ℤ) - (a':ℤ) : ℤ) : ℝ)/(q:ℝ) by
      push_cast; ring]
    rw [abs_div, ← Int.cast_abs, abs_of_pos hqpos]
    exact div_le_div_of_nonneg_right (by exact_mod_cast habs) hqpos.le
  have hlt : 2*H/((q:ℝ)*(n:ℝ)) < (1:ℝ)/(q:ℝ) := by
    rw [div_lt_iff₀ (show (0:ℝ) < (q:ℝ)*(n:ℝ) by positivity)]
    have hval : (1:ℝ)/(q:ℝ) * ((q:ℝ)*(n:ℝ)) = (n:ℝ) := by field_simp
    rw [hval]
    exact hn
  linarith [hge, hdist, hlt]

end B1B1
