import Mathlib
open scoped BigOperators

noncomputable section
namespace B1B1

def Qs (n : ℕ) : ℕ := (Nat.log 2 (n+2))^2
def Qcut (n : ℕ) : ℕ := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
def Hwide (n : ℕ) : ℕ := 256 * Qcut n * Qs n

/-- Radius-sum inequality: for `q, q' ≤ Q₁` the two semi-widths sum to less
than the Farey spacing, provided `512 Q₁² Q < n`. -/
lemma radius_sum_lt (n q q' : ℕ) (hn : 512 * (Qcut n)^2 * Qs n < n)
    (hqQ : q ≤ Qcut n) (hq'Q : q' ≤ Qcut n) :
    (Hwide n : ℝ) * ((q:ℝ) + (q':ℝ)) < (n:ℝ) := by
  have hH : (Hwide n : ℝ) = 256 * (Qcut n : ℝ) * (Qs n : ℝ) := by
    unfold Hwide
    push_cast
    ring
  have hsum : (q:ℝ) + (q':ℝ) ≤ 2 * (Qcut n : ℝ) := by
    have h1 : (q:ℝ) ≤ (Qcut n : ℝ) := by exact_mod_cast hqQ
    have h2 : (q':ℝ) ≤ (Qcut n : ℝ) := by exact_mod_cast hq'Q
    linarith
  have hbound : (Hwide n : ℝ) * ((q:ℝ) + (q':ℝ)) ≤
      256 * (Qcut n : ℝ) * (Qs n : ℝ) * (2 * (Qcut n : ℝ)) := by
    rw [hH]
    apply mul_le_mul_of_nonneg_left hsum
    positivity
  have hcast : (512 * (Qcut n)^2 * Qs n : ℕ) < n := hn
  have hcastR : (256 * (Qcut n : ℝ) * (Qs n : ℝ) * (2 * (Qcut n : ℝ))) < (n:ℝ) := by
    have : (256 * (Qcut n : ℝ) * (Qs n : ℝ) * (2 * (Qcut n : ℝ))) =
        ((512 * (Qcut n)^2 * Qs n : ℕ) : ℝ) := by push_cast; ring
    rw [this]
    exact_mod_cast hcast
  linarith

/-- The individual wide arcs are pairwise disjoint for large `n`. -/
lemma wideArcs_pieces_disjoint (n : ℕ) (hn : 512 * (Qcut n)^2 * Qs n < n)
    {q q' a a' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (hqQ : q ≤ Qcut n) (hq'Q : q' ≤ Qcut n)
    (hne : (a:ℝ)/(q:ℝ) ≠ (a':ℝ)/(q':ℝ)) :
    Disjoint {t : ℝ | |t - (a:ℝ)/(q:ℝ)| ≤ (Hwide n:ℝ)/((q:ℝ)*(n:ℝ))}
      {t : ℝ | |t - (a':ℝ)/(q':ℝ)| ≤ (Hwide n:ℝ)/((q':ℝ)*(n:ℝ))} := by
  rw [Set.disjoint_left]
  intro t h1 h2
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hq'pos : (0:ℝ) < (q':ℝ) := by exact_mod_cast hq'
  have hnpos : (0:ℝ) < (n:ℝ) := by
    have : (0:ℕ) < n := by omega
    exact_mod_cast this
  -- spacing lower bound from the cross-multiplication argument
  have hspacing : (1:ℝ)/((q:ℝ)*(q':ℝ)) ≤ |(a:ℝ)/(q:ℝ) - (a':ℝ)/(q':ℝ)| := by
    set z : ℤ := (a:ℤ) * (q':ℤ) - (a':ℤ) * (q:ℤ) with hz
    have hzne : z ≠ 0 := by
      intro h0
      apply hne
      have hcross : (a:ℤ) * (q':ℤ) - (a':ℤ) * (q:ℤ) = 0 := by rwa [← hz]
      have h1 : (a:ℤ) * (q':ℤ) = (a':ℤ) * (q:ℤ) := by omega
      have h2 : (a:ℝ) * (q':ℝ) = (a':ℝ) * (q:ℝ) := by exact_mod_cast h1
      rw [div_eq_div_iff (ne_of_gt hqpos) (ne_of_gt hq'pos)]
      exact h2
    have habs : (1:ℤ) ≤ |z| := Int.one_le_abs hzne
    have hkey : |(a:ℝ)/(q:ℝ) - (a':ℝ)/(q':ℝ)| = ((|z| : ℤ) : ℝ)/((q:ℝ)*(q':ℝ)) := by
      have hnum : (a:ℝ)/(q:ℝ) - (a':ℝ)/(q':ℝ) = ((z:ℤ) : ℝ)/((q:ℝ)*(q':ℝ)) := by
        rw [hz]; push_cast; field_simp
      rw [hnum, abs_div, ← Int.cast_abs, abs_of_pos (by positivity : (0:ℝ) < (q:ℝ)*(q':ℝ))]
    rw [hkey]
    exact div_le_div_of_nonneg_right (by exact_mod_cast habs) (by positivity)
  have htri : |(a:ℝ)/(q:ℝ) - (a':ℝ)/(q':ℝ)| ≤
      (Hwide n:ℝ)/((q:ℝ)*(n:ℝ)) + (Hwide n:ℝ)/((q':ℝ)*(n:ℝ)) := by
    calc |(a:ℝ)/(q:ℝ) - (a':ℝ)/(q':ℝ)|
        = |((a:ℝ)/(q:ℝ) - t) + (t - (a':ℝ)/(q':ℝ))| := by ring_nf
      _ ≤ |(a:ℝ)/(q:ℝ) - t| + |t - (a':ℝ)/(q':ℝ)| := abs_add_le _ _
      _ = |t - (a:ℝ)/(q:ℝ)| + |t - (a':ℝ)/(q':ℝ)| := by rw [abs_sub_comm]
      _ ≤ _ := add_le_add h1 h2
  have hlt : (Hwide n:ℝ)/((q:ℝ)*(n:ℝ)) + (Hwide n:ℝ)/((q':ℝ)*(n:ℝ)) <
      (1:ℝ)/((q:ℝ)*(q':ℝ)) := by
    have hsum := radius_sum_lt n q q' hn hqQ hq'Q
    have hden : (Hwide n:ℝ)/((q:ℝ)*(n:ℝ)) + (Hwide n:ℝ)/((q':ℝ)*(n:ℝ)) =
        (Hwide n:ℝ) * ((q:ℝ) + (q':ℝ)) / ((q:ℝ)*(q':ℝ)*(n:ℝ)) := by
      field_simp
      ring
    rw [hden]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have hpos : (0:ℝ) < (q:ℝ)*(q':ℝ) := by positivity
    have hsum' := mul_lt_mul_of_pos_right hsum hpos
    nlinarith [hsum']
  exact absurd (lt_of_le_of_lt hspacing (lt_of_le_of_lt htri hlt)) (lt_irrefl _)

end B1B1
