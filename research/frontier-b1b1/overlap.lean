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

/-- Two wide arcs that both meet `t` force `n ≤ 2 H q q'`. -/
lemma overlap_denominator_bound (n : ℕ) (hn : 0 < n) (H : ℝ) (hH : 0 ≤ H)
    {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') {a a' : ℕ}
    (hne : (a:ℝ)/(q:ℝ) ≠ (a':ℝ)/(q':ℝ)) (t : ℝ)
    (h1 : |t - (a:ℝ)/(q:ℝ)| ≤ H/((q:ℝ)*(n:ℝ)))
    (h2 : |t - (a':ℝ)/(q':ℝ)| ≤ H/((q':ℝ)*(n:ℝ))) :
    (n:ℝ) ≤ 2*H*(q:ℝ)*(q':ℝ) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hq'1 : (1:ℝ) ≤ (q':ℝ) := by exact_mod_cast hq'
  have hfar : (1:ℝ)/((q:ℝ)*(q':ℝ)) ≤ |(a:ℝ)/(q:ℝ) - (a':ℝ)/(q':ℝ)| :=
    farey_spacing hq hq' hne
  have htri : |(a:ℝ)/(q:ℝ) - (a':ℝ)/(q':ℝ)| ≤
      H/((q:ℝ)*(n:ℝ)) + H/((q':ℝ)*(n:ℝ)) := by
    calc |(a:ℝ)/(q:ℝ) - (a':ℝ)/(q':ℝ)|
        = |((a:ℝ)/(q:ℝ) - t) + (t - (a':ℝ)/(q':ℝ))| := by ring_nf
      _ ≤ |(a:ℝ)/(q:ℝ) - t| + |t - (a':ℝ)/(q':ℝ)| := abs_add_le _ _
      _ = |t - (a:ℝ)/(q:ℝ)| + |t - (a':ℝ)/(q':ℝ)| := by rw [abs_sub_comm]
      _ ≤ H/((q:ℝ)*(n:ℝ)) + H/((q':ℝ)*(n:ℝ)) := add_le_add h1 h2
  have hsum : (1:ℝ) ≤ H * ((q:ℝ) + (q':ℝ)) / (n:ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right (hfar.trans htri)
      (by positivity : (0:ℝ) ≤ (q:ℝ)*(q':ℝ))
    have hleft : (1:ℝ)/((q:ℝ)*(q':ℝ)) * ((q:ℝ)*(q':ℝ)) = 1 := by field_simp
    rw [hleft] at hmul
    have hright : (H/((q:ℝ)*(n:ℝ)) + H/((q':ℝ)*(n:ℝ))) * ((q:ℝ)*(q':ℝ))
        = H * ((q:ℝ) + (q':ℝ)) / (n:ℝ) := by
      field_simp
      ring
    rwa [hright] at hmul
  have hstep : H * ((q:ℝ) + (q':ℝ)) / (n:ℝ) ≤ 2*H*(q:ℝ)*(q':ℝ)/(n:ℝ) := by
    apply div_le_div_of_nonneg_right _ hnpos.le
    have hprod : (0:ℝ) ≤ ((q:ℝ) - 1) * ((q':ℝ) - 1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hprod, hH]
  have hfin : 1 ≤ 2*H*(q:ℝ)*(q':ℝ)/(n:ℝ) := le_trans hsum hstep
  rw [le_div_iff₀ hnpos] at hfin
  linarith

end B1B1
