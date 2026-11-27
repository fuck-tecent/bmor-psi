import Mathlib
open scoped BigOperators

noncomputable section
namespace B1B1

/-- Farey spacing: distinct reduced fractions with denominators `q, q'` are at
distance at least `1/(q q')`. -/
lemma farey_spacing {q q' a a' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (hne : (a:ℝ)/(q:ℝ) ≠ (a':ℝ)/(q':ℝ)) :
    (1:ℝ)/((q:ℝ)*(q':ℝ)) ≤ |(a:ℝ)/(q:ℝ) - (a':ℝ)/(q':ℝ)| := by
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hq'pos : (0:ℝ) < (q':ℝ) := by exact_mod_cast hq'
  set n : ℤ := (a:ℤ) * (q':ℤ) - (a':ℤ) * (q:ℤ) with hn
  have hnne : n ≠ 0 := by
    intro h0
    apply hne
    have h1 : (a:ℤ) * (q':ℤ) = (a':ℤ) * (q:ℤ) := by
      have hcross : (a:ℤ) * (q':ℤ) - (a':ℤ) * (q:ℤ) = 0 := by rwa [← hn]
      omega
    have h2 : (a:ℝ) * (q':ℝ) = (a':ℝ) * (q:ℝ) := by exact_mod_cast h1
    rw [div_eq_div_iff (ne_of_gt hqpos) (ne_of_gt hq'pos)]
    exact h2
  have habs : (1:ℤ) ≤ |n| := Int.one_le_abs hnne
  have hkey : |(a:ℝ)/(q:ℝ) - (a':ℝ)/(q':ℝ)| = ((|n| : ℤ) : ℝ)/((q:ℝ)*(q':ℝ)) := by
    have hnum : (a:ℝ)/(q:ℝ) - (a':ℝ)/(q':ℝ) = ((n:ℤ) : ℝ)/((q:ℝ)*(q':ℝ)) := by
      rw [hn]
      push_cast
      field_simp
    rw [hnum, abs_div]
    rw [show |((n:ℤ) : ℝ)| = ((|n| : ℤ) : ℝ) by rw [Int.cast_abs]]
    rw [abs_of_pos (by positivity : (0:ℝ) < (q:ℝ)*(q':ℝ))]
  rw [hkey]
  exact div_le_div_of_nonneg_right (by exact_mod_cast habs) (by positivity)

end B1B1
