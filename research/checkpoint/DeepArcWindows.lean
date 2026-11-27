import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace GoldbachSupport

/-- A one-sided interval at a distinct reduced rational stays outside the
    closed major arc about `b/r`. The shift `h` is an arbitrary real number. -/
theorem deepArcWindow (a b q r : ℕ) (H n h : ℝ)
    (hq : 0 < (q : ℝ)) (hr : 0 < (r : ℝ)) (hn : 0 < n)
    (hne : a * r ≠ b * q) (hh : 0 ≤ h) (hwidth : h ≤ 1 / (6 * n))
    (hmask : (q : ℝ) * H + (q : ℝ) * r / 6 < n) :
    H / ((r : ℝ) * n) < |(a : ℝ) / q + h - (b : ℝ) / r| := by
  have hqr := mul_pos hq hr
  have hscale := mul_pos hqr hn
  have hcap : H / ((r : ℝ) * n) * ((q : ℝ) * r * n) = q * H := by
    field_simp [hr.ne', hn.ne']
  have hcenter : ((a : ℝ) / q + h - (b : ℝ) / r) * ((q : ℝ) * r * n) =
      ((a : ℝ) * r - (b : ℝ) * q) * n + h * ((q : ℝ) * r * n) := by
    field_simp [hq.ne', hr.ne']
    ring
  have hw := (le_div_iff₀ (show 0 < 6 * n by linarith)).mp hwidth
  have hwscaled := mul_le_mul_of_nonneg_right hw hqr.le
  have hshift : h * ((q : ℝ) * r * n) ≤ (q : ℝ) * r / 6 := by
    nlinarith only [hwscaled]
  apply lt_of_not_ge
  intro hbad
  obtain ⟨hl, hu⟩ := abs_le.mp hbad
  have hleft := mul_le_mul_of_nonneg_right hl hscale.le
  have hright := mul_le_mul_of_nonneg_right hu hscale.le
  rw [neg_mul, hcap, hcenter] at hleft
  rw [hcap, hcenter] at hright
  rcases Nat.lt_or_gt_of_ne hne with lt | gt
  · have hi : a * r + 1 ≤ b * q := lt
    have hi' : (a : ℝ) * r + 1 ≤ (b : ℝ) * q := by exact_mod_cast hi
    have hgap := mul_le_mul_of_nonneg_right hi' hn.le
    nlinarith only [hleft, hgap, hshift, hmask]
  · have hi : b * q + 1 ≤ a * r := gt
    have hi' : (b : ℝ) * q + 1 ≤ (a : ℝ) * r := by exact_mod_cast hi
    have hgap := mul_le_mul_of_nonneg_right hi' hn.le
    have hpositive := mul_nonneg hh hscale.le
    nlinarith only [hright, hgap, hpositive, hmask, hqr.le]

/-- With a reduced numerator, a denominator larger than `Q` excludes
    coincidences with every center in the frozen wide-arc mask. -/
theorem outsideWideArcs (a q Q H n : ℕ) (h : ℝ) (ha : Nat.Coprime a q)
    (hq : Q < q) (hn : 0 < n) (hh : 0 ≤ h) (hwidth : h ≤ 1 / (6 * (n : ℝ)))
    (hmask : (q : ℝ) * H + (q : ℝ) * Q / 6 < n) :
    (a : ℝ) / q + h ∉ {t : ℝ | ∃ r b : ℕ, 1 ≤ r ∧ r ≤ Q ∧ b ≤ r ∧
      Nat.Coprime b r ∧ |t - (b : ℝ) / r| ≤ (H : ℝ) / ((r : ℝ) * n)} := by
  rintro ⟨r, b, hr, hrQ, _, _, hnear⟩
  have hrpos : 0 < r := hr
  have hqpos : 0 < q := Nat.zero_lt_of_lt hq
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hqpos
  have hcross : a * r ≠ b * q := by
    intro heq
    have hd : q ∣ a * r := heq ▸ Nat.dvd_mul_left q b
    have hle := Nat.le_of_dvd hrpos (ha.symm.dvd_of_dvd_mul_left hd)
    exact (not_lt_of_ge hle) (lt_of_le_of_lt hrQ hq)
  have hrQ' : (r : ℝ) ≤ Q := by exact_mod_cast hrQ
  have hmask' : (q : ℝ) * H + (q : ℝ) * r / 6 < n := by
    linarith only [hmask, mul_le_mul_of_nonneg_left hrQ' hqr.le]
  exact (not_lt_of_ge hnear) (deepArcWindow a b q r H n h hqr (by exact_mod_cast hrpos)
    (by exact_mod_cast hn) hcross hh hwidth hmask')

/-- The two closed one-sided intervals of width `1/(6n)` do not meet
    if their denominator product is strictly below `6n`. -/
theorem deepArcWindowsDisjoint (a b q r : ℕ) (n u v : ℝ)
    (hq : 0 < (q : ℝ)) (hr : 0 < (r : ℝ)) (hn : 0 < n)
    (hne : a * r ≠ b * q) (hsize : (q : ℝ) * r < 6 * n)
    (hu : 0 ≤ u) (hU : u ≤ 1 / (6 * n)) (hv : 0 ≤ v) (hV : v ≤ 1 / (6 * n)) :
    (a : ℝ) / q + u ≠ (b : ℝ) / r + v := by
  intro heq
  rcases le_total v u with huv | hvu
  · have h := deepArcWindow a b q r 0 n (u - v) hq hr hn hne
      (sub_nonneg.mpr huv) (by linarith only [hU, hv]) (by linarith only [hsize])
    have hz : (a : ℝ) / q + (u - v) - (b : ℝ) / r = 0 := by linarith only [heq]
    simp [hz] at h
  · have hsize' : (r : ℝ) * q < 6 * n := by rwa [mul_comm]
    have h := deepArcWindow b a r q 0 n (v - u) hr hq hn (Ne.symm hne)
      (sub_nonneg.mpr hvu) (by linarith only [hV, hu]) (by linarith only [hsize'])
    have hz : (b : ℝ) / r + (v - u) - (a : ℝ) / q = 0 := by linarith only [heq]
    simp [hz] at h

end GoldbachSupport

#print axioms GoldbachSupport.deepArcWindow
#print axioms GoldbachSupport.outsideWideArcs
#print axioms GoldbachSupport.deepArcWindowsDisjoint
