import Mathlib

namespace PEqualNP.Outside.SquarePackingEleven

private noncomputable def a0 : ℝ := Real.sqrt (4 / 5)
private noncomputable def L0 : ℝ := 2 + 2 * a0

private lemma a0_nonneg : 0 ≤ a0 := Real.sqrt_nonneg _

private lemma a0_sq : a0 ^ 2 = 4 / 5 := by
  unfold a0
  exact Real.sq_sqrt (by norm_num)

private lemma a0_pos : 0 < a0 := by
  have hsq := a0_sq
  have hnn := a0_nonneg
  nlinarith only [hsq, hnn]

private lemma a0_lb : (8944 : ℝ) / 10000 ≤ a0 := by
  have hsq := a0_sq
  have hnn := a0_nonneg
  nlinarith only [hsq, hnn]

private lemma a0_ub_tight : a0 ≤ (8945 : ℝ) / 10000 := by
  have hsq := a0_sq
  have hnn := a0_nonneg
  nlinarith only [hsq, hnn]

private lemma a0_ub : a0 ≤ (179 : ℝ) / 200 := by
  linarith only [a0_ub_tight]

private lemma L0_pos : 0 < L0 := by
  unfold L0
  linarith only [a0_pos]

private def boxInside (r x y c s X Y : ℝ) : Prop :=
  |c * (X - x) + s * (Y - y)| < r ∧ |(-s) * (X - x) + c * (Y - y)| < r

private def ValidBox (r x y c s : ℝ) : Prop :=
  1 / 2 < r ∧ 0 ≤ c ∧ 0 ≤ s ∧ c ^ 2 + s ^ 2 = 1 ∧
  r * (c + s) ≤ x ∧ r * (c + s) ≤ L0 - x ∧
  r * (c + s) ≤ y ∧ r * (c + s) ≤ L0 - y

private lemma boxInside_translate (r x y c s X Y dx dy : ℝ) :
    boxInside r (x + dx) (y + dy) c s (X + dx) (Y + dy) ↔ boxInside r x y c s X Y := by
  unfold boxInside
  have h1 : X + dx - (x + dx) = X - x := by ring
  have h2 : Y + dy - (y + dy) = Y - y := by ring
  rw [h1, h2]

private lemma boxInside_reflectX (r x y c s X Y X0 : ℝ) :
    boxInside r (X0 - x) y s c (X0 - X) Y ↔ boxInside r x y c s X Y := by
  unfold boxInside
  have h1 : s * (X0 - X - (X0 - x)) + c * (Y - y) = (-s) * (X - x) + c * (Y - y) := by ring
  have h2 : (-c) * (X0 - X - (X0 - x)) + s * (Y - y) = c * (X - x) + s * (Y - y) := by ring
  rw [h1, h2, and_comm]

private lemma boxInside_reflectY (r x y c s X Y Y0 : ℝ) :
    boxInside r x (Y0 - y) s c X (Y0 - Y) ↔ boxInside r x y c s X Y := by
  unfold boxInside
  have h1 : s * (X - x) + c * (Y0 - Y - (Y0 - y)) = -((-s) * (X - x) + c * (Y - y)) := by ring
  have h2 : (-c) * (X - x) + s * (Y0 - Y - (Y0 - y)) = -(c * (X - x) + s * (Y - y)) := by ring
  rw [h1, h2, abs_neg, abs_neg, and_comm]

private lemma boxInside_swap (r x y c s X Y : ℝ) :
    boxInside r y x s c Y X ↔ boxInside r x y c s X Y := by
  unfold boxInside
  have h1 : s * (Y - y) + c * (X - x) = c * (X - x) + s * (Y - y) := by ring
  have h2 : (-c) * (Y - y) + s * (X - x) = -((-s) * (X - x) + c * (Y - y)) := by ring
  rw [h1, h2, abs_neg]

private lemma boxInside_rot90 (r x y c s X Y X0 dy : ℝ) :
    boxInside r (y - dy) (X0 - x) c s (Y - dy) (X0 - X) ↔ boxInside r x y c s X Y := by
  unfold boxInside
  have h1 : c * (Y - dy - (y - dy)) + s * (X0 - X - (X0 - x)) =
      (-s) * (X - x) + c * (Y - y) := by ring
  have h2 : (-s) * (Y - dy - (y - dy)) + c * (X0 - X - (X0 - x)) =
      -(c * (X - x) + s * (Y - y)) := by ring
  rw [h1, h2, abs_neg, and_comm]

private lemma boxInside_rot180 (r x y c s X Y X0 Y0 : ℝ) :
    boxInside r (X0 - x) (Y0 - y) c s (X0 - X) (Y0 - Y) ↔ boxInside r x y c s X Y := by
  unfold boxInside
  have h1 : c * (X0 - X - (X0 - x)) + s * (Y0 - Y - (Y0 - y)) =
      -(c * (X - x) + s * (Y - y)) := by ring
  have h2 : (-s) * (X0 - X - (X0 - x)) + c * (Y0 - Y - (Y0 - y)) =
      -((-s) * (X - x) + c * (Y - y)) := by ring
  rw [h1, h2, abs_neg, abs_neg]

private lemma boxInside_rot270 (r x y c s X Y Y0 : ℝ) :
    boxInside r (Y0 - y) x c s (Y0 - Y) X ↔ boxInside r x y c s X Y := by
  unfold boxInside
  have h1 : c * (Y0 - Y - (Y0 - y)) + s * (X - x) =
      -((-s) * (X - x) + c * (Y - y)) := by ring
  have h2 : (-s) * (Y0 - Y - (Y0 - y)) + c * (X - x) =
      c * (X - x) + s * (Y - y) := by ring
  rw [h1, h2, abs_neg, and_comm]

private lemma validBox_reflectX {r x y c s : ℝ} (h : ValidBox r x y c s) :
    ValidBox r (L0 - x) y s c := by
  rcases h with ⟨hr, hc, hs, hcs, hx1, hx2, hy1, hy2⟩
  refine ⟨hr, hs, hc, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

private lemma validBox_reflectY {r x y c s : ℝ} (h : ValidBox r x y c s) :
    ValidBox r x (L0 - y) s c := by
  rcases h with ⟨hr, hc, hs, hcs, hx1, hx2, hy1, hy2⟩
  refine ⟨hr, hs, hc, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

private lemma validBox_bounds {r x y c s : ℝ} (h : ValidBox r x y c s) :
    0 ≤ x ∧ x ≤ L0 ∧ 0 ≤ y ∧ y ≤ L0 := by
  rcases h with ⟨hr, hc, hs, hcs, hx1, hx2, hy1, hy2⟩
  have hcs_ge : 1 ≤ c + s := by nlinarith only [hc, hs, hcs]
  have hrc : 0 ≤ r * (c + s) := by nlinarith only [hr, hcs_ge]
  exact ⟨by linarith only [hx1, hrc], by linarith only [hx2, hrc],
         by linarith only [hy1, hrc], by linarith only [hy2, hrc]⟩

/-! ### Section 2: Purely Algebraic Nonavoidance Lemmas (Stromquist Lemmas 1, 2, 3, 4, 6) -/

private lemma lemma1_corner {r x y c s u v : ℝ}
    (hr : 1 / 2 < r) (hc : 0 ≤ c) (hs : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1)
    (hx1 : r * (c + s) ≤ x) (hx2 : x ≤ u) (hu : u ≤ 1)
    (hy1 : r * (c + s) ≤ y) (hy2 : y ≤ v) (hv : v ≤ 1) :
    boxInside r x y c s u v := by
  unfold boxInside
  have h1 : 0 ≤ c * (u - x) + s * (v - y) := by
    nlinarith only [hc, hs, hx2, hy2]
  have h2 : c * (u - x) + s * (v - y) < r := by
    have hsub : c * (u - x) + s * (v - y) ≤ (c + s) - r * (c + s) ^ 2 := by
      nlinarith only [hc, hs, hx1, hu, hy1, hv]
    have hpos : 0 ≤ ((c + s) - 1) ^ 2 := sq_nonneg _
    have hcs_sq : 1 ≤ (c + s) ^ 2 := by nlinarith only [hc, hs, hcs]
    nlinarith only [hr, hsub, hpos, hcs_sq]
  have h3 : (-s) * (u - x) + c * (v - y) < r := by
    have hsub : (-s) * (u - x) + c * (v - y) ≤ c * (1 - r * (c + s)) := by
      nlinarith only [hc, hs, hx2, hy1, hv]
    have hpos : 0 ≤ (1 - c) ^ 2 + c * s := by nlinarith only [hc, hs, sq_nonneg (1 - c)]
    have hmul : 0 < 1 + c * (c + s) := by nlinarith only [hc, hs]
    nlinarith only [hr, hcs, hsub, hpos, hmul]
  have h4 : -r < (-s) * (u - x) + c * (v - y) := by
    have hsub : s * (u - x) - c * (v - y) ≤ s * (1 - r * (c + s)) := by
      nlinarith only [hc, hs, hx1, hu, hy2]
    have hpos : 0 ≤ (1 - s) ^ 2 + c * s := by nlinarith only [hc, hs, sq_nonneg (1 - s)]
    have hmul : 0 < 1 + s * (c + s) := by nlinarith only [hc, hs]
    nlinarith only [hr, hcs, hsub, hpos, hmul]
  exact ⟨abs_lt.mpr ⟨by linarith only [hr, h1], h2⟩, abs_lt.mpr ⟨h4, h3⟩⟩

private def cross2 (x1 y1 x2 y2 x y : ℝ) : ℝ :=
  (x2 - x1) * (y - y1) - (y2 - y1) * (x - x1)

private lemma lemma2_triangle {r x y c s x1 y1 x2 y2 x3 y3 : ℝ}
    (hr : 1 / 2 < r) (hcs : c ^ 2 + s ^ 2 = 1)
    (hd12 : (x1 - x2) ^ 2 + (y1 - y2) ^ 2 ≤ 1)
    (hd23 : (x2 - x3) ^ 2 + (y2 - y3) ^ 2 ≤ 1)
    (hd31 : (x3 - x1) ^ 2 + (y3 - y1) ^ 2 ≤ 1)
    (hD : 0 < cross2 x1 y1 x2 y2 x3 y3)
    (he12 : 0 ≤ cross2 x1 y1 x2 y2 x y)
    (he23 : 0 ≤ cross2 x2 y2 x3 y3 x y)
    (he31 : 0 ≤ cross2 x3 y3 x1 y1 x y) :
    boxInside r x y c s x1 y1 ∨ boxInside r x y c s x2 y2 ∨ boxInside r x y c s x3 y3 := by
  by_contra hnone
  push Not at hnone
  rcases hnone with ⟨hn1, hn2, hn3⟩
  set w1 := cross2 x2 y2 x3 y3 x y
  set w2 := cross2 x3 y3 x1 y1 x y
  set w3 := cross2 x1 y1 x2 y2 x y
  have hwsum : w1 + w2 + w3 = cross2 x1 y1 x2 y2 x3 y3 := by
    simp only [w1, w2, w3, cross2]; ring
  set u1 := c * (x1 - x) + s * (y1 - y)
  set v1 := (-s) * (x1 - x) + c * (y1 - y)
  set u2 := c * (x2 - x) + s * (y2 - y)
  set v2 := (-s) * (x2 - x) + c * (y2 - y)
  set u3 := c * (x3 - x) + s * (y3 - y)
  set v3 := (-s) * (x3 - x) + c * (y3 - y)
  have husum : w1 * u1 + w2 * u2 + w3 * u3 = 0 := by
    simp only [w1, w2, w3, u1, u2, u3, cross2]; ring
  have hvsum : w1 * v1 + w2 * v2 + w3 * v3 = 0 := by
    simp only [w1, w2, w3, v1, v2, v3, cross2]; ring
  have hduv12 : (u1 - u2) ^ 2 + (v1 - v2) ^ 2 ≤ 1 := by
    have heq : (u1 - u2) ^ 2 + (v1 - v2) ^ 2 =
        (c ^ 2 + s ^ 2) * ((x1 - x2) ^ 2 + (y1 - y2) ^ 2) := by
      simp only [u1, u2, v1, v2]; ring
    rw [heq, hcs, one_mul]; exact hd12
  have hduv23 : (u2 - u3) ^ 2 + (v2 - v3) ^ 2 ≤ 1 := by
    have heq : (u2 - u3) ^ 2 + (v2 - v3) ^ 2 =
        (c ^ 2 + s ^ 2) * ((x2 - x3) ^ 2 + (y2 - y3) ^ 2) := by
      simp only [u2, u3, v2, v3]; ring
    rw [heq, hcs, one_mul]; exact hd23
  have hduv31 : (u3 - u1) ^ 2 + (v3 - v1) ^ 2 ≤ 1 := by
    have heq : (u3 - u1) ^ 2 + (v3 - v1) ^ 2 =
        (c ^ 2 + s ^ 2) * ((x3 - x1) ^ 2 + (y3 - y1) ^ 2) := by
      simp only [u3, u1, v3, v1]; ring
    rw [heq, hcs, one_mul]; exact hd31
  have hu12 : |u1 - u2| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith only [hduv12, sq_nonneg (v1 - v2)]
  have hu23 : |u2 - u3| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith only [hduv23, sq_nonneg (v2 - v3)]
  have hu31 : |u3 - u1| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith only [hduv31, sq_nonneg (v3 - v1)]
  have hv12 : |v1 - v2| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith only [hduv12, sq_nonneg (u1 - u2)]
  have hv23 : |v2 - v3| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith only [hduv23, sq_nonneg (u2 - u3)]
  have hv31 : |v3 - v1| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith only [hduv31, sq_nonneg (u3 - u1)]
  have hex_u : ∃ su : ℝ, (su = 1 ∨ su = -1) ∧ -r < su * u1 ∧ -r < su * u2 ∧ -r < su * u3 := by
    by_cases hneg : u1 ≤ -r ∨ u2 ≤ -r ∨ u3 ≤ -r
    · rcases abs_le.mp hu12 with ⟨ha12, hb12⟩
      rcases abs_le.mp hu23 with ⟨ha23, hb23⟩
      rcases abs_le.mp hu31 with ⟨ha31, hb31⟩
      refine ⟨-1, Or.inr rfl, ?_, ?_, ?_⟩ <;>
        rcases hneg with h | h | h <;> linarith only [hr, h, ha12, hb12, ha23, hb23, ha31, hb31]
    · push Not at hneg
      exact ⟨1, Or.inl rfl, by linarith only [hneg.1], by linarith only [hneg.2.1], by linarith only [hneg.2.2]⟩
  have hex_v : ∃ sv : ℝ, (sv = 1 ∨ sv = -1) ∧ -r < sv * v1 ∧ -r < sv * v2 ∧ -r < sv * v3 := by
    by_cases hneg : v1 ≤ -r ∨ v2 ≤ -r ∨ v3 ≤ -r
    · rcases abs_le.mp hv12 with ⟨ha12, hb12⟩
      rcases abs_le.mp hv23 with ⟨ha23, hb23⟩
      rcases abs_le.mp hv31 with ⟨ha31, hb31⟩
      refine ⟨-1, Or.inr rfl, ?_, ?_, ?_⟩ <;>
        rcases hneg with h | h | h <;> linarith only [hr, h, ha12, hb12, ha23, hb23, ha31, hb31]
    · push Not at hneg
      exact ⟨1, Or.inl rfl, by linarith only [hneg.1], by linarith only [hneg.2.1], by linarith only [hneg.2.2]⟩
  rcases hex_u with ⟨su, hsu, hsu1, hsu2, hsu3⟩
  rcases hex_v with ⟨sv, hsv, hsv1, hsv2, hsv3⟩
  have hpos_of_out : ∀ u v : ℝ, ¬ (|u| < r ∧ |v| < r) → -r < su * u → -r < sv * v →
      0 < su * u + sv * v := by
    intro u v hout hu_gt hv_gt
    have hge : r ≤ |u| ∨ r ≤ |v| := by
      by_contra hlt; push Not at hlt; exact hout hlt
    rcases hge with hge | hge
    · have : r ≤ su * u := by
        rcases hsu with rfl | rfl <;> rcases le_abs.mp hge with h | h <;> linarith only [hr, hu_gt, h]
      linarith only [hv_gt, this]
    · have : r ≤ sv * v := by
        rcases hsv with rfl | rfl <;> rcases le_abs.mp hge with h | h <;> linarith only [hr, hv_gt, h]
      linarith only [hu_gt, this]
  have hp1 : 0 < su * u1 + sv * v1 := hpos_of_out u1 v1 hn1 hsu1 hsv1
  have hp2 : 0 < su * u2 + sv * v2 := hpos_of_out u2 v2 hn2 hsu2 hsv2
  have hp3 : 0 < su * u3 + sv * v3 := hpos_of_out u3 v3 hn3 hsu3 hsv3
  have hcomb : w1 * (su * u1 + sv * v1) + w2 * (su * u2 + sv * v2) + w3 * (su * u3 + sv * v3) = 0 := by
    calc w1 * (su * u1 + sv * v1) + w2 * (su * u2 + sv * v2) + w3 * (su * u3 + sv * v3)
        = su * (w1 * u1 + w2 * u2 + w3 * u3) + sv * (w1 * v1 + w2 * v2 + w3 * v3) := by ring
      _ = 0 := by rw [husum, hvsum]; ring
  have hw1 : 0 ≤ w1 := he23
  have hw2 : 0 ≤ w2 := he31
  have hw3 : 0 ≤ w3 := he12
  have h1 : 0 ≤ w1 * (su * u1 + sv * v1) := mul_nonneg hw1 (le_of_lt hp1)
  have h2 : 0 ≤ w2 * (su * u2 + sv * v2) := mul_nonneg hw2 (le_of_lt hp2)
  have h3 : 0 ≤ w3 * (su * u3 + sv * v3) := mul_nonneg hw3 (le_of_lt hp3)
  have hor : 0 < w1 ∨ 0 < w2 ∨ 0 < w3 := by
    by_contra h; push Not at h; linarith only [hwsum, hD, h.1, h.2.1, h.2.2]
  rcases hor with hw | hw | hw
  · nlinarith only [hw, hp1, h2, h3, hcomb]
  · nlinarith only [hw, hp2, h1, h3, hcomb]
  · nlinarith only [hw, hp3, h1, h2, hcomb]

private lemma lemma3_rect {r x y c s w h : ℝ}
    (hr : 1 / 2 < r) (hc : 0 ≤ c) (hs : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1)
    (hx1 : 0 ≤ x) (hx2 : x ≤ w) (hw : w ≤ 9 / 10)
    (hy1 : r * (c + s) ≤ y) (hy2 : y ≤ h) (hh : h ≤ 9 / 10) :
    boxInside r x y c s 0 h ∨ boxInside r x y c s w h := by
  by_contra hnone
  push Not at hnone
  rcases hnone with ⟨hnL, hnR⟩
  have hc1 : c ≤ 1 := by nlinarith only [hc, hs, hcs]
  have hs1 : s ≤ 1 := by nlinarith only [hc, hs, hcs]
  have hcs_ge : 1 ≤ c + s := by nlinarith only [hc, hs, hcs]
  have hL : r ≤ c * x - s * (h - y) ∨ r ≤ s * x + c * (h - y) := by
    have hU_lt : c * (0 - x) + s * (h - y) < r := by
      have h1 : c * (0 - x) + s * (h - y) ≤ s * (1 - r * (c + s)) := by
        nlinarith only [hc, hs, hx1, hy1, hh]
      have h2 : 0 ≤ (1 - s) ^ 2 + c * s := by nlinarith only [hc, hs, sq_nonneg (1 - s)]
      have h3 : 0 < 1 + s * (c + s) := by nlinarith only [hc, hs]
      nlinarith only [hr, hcs, h1, h2, h3]
    have hV_gt : -r < (-s) * (0 - x) + c * (h - y) := by
      nlinarith only [hr, hc, hs, hx1, hy2]
    by_contra hboth
    push Not at hboth
    apply hnL
    exact ⟨abs_lt.mpr ⟨by linarith only [hboth.1], hU_lt⟩,
           abs_lt.mpr ⟨hV_gt, by linarith only [hboth.2]⟩⟩
  have hR : r ≤ c * (w - x) + s * (h - y) ∨ r ≤ s * (w - x) - c * (h - y) := by
    have hU_gt : -r < c * (w - x) + s * (h - y) := by
      nlinarith only [hr, hc, hs, hx2, hy2]
    have hV_lt : (-s) * (w - x) + c * (h - y) < r := by
      have h1 : (-s) * (w - x) + c * (h - y) ≤ c * (1 - r * (c + s)) := by
        nlinarith only [hc, hs, hx2, hy1, hh]
      have h2 : 0 ≤ (1 - c) ^ 2 + c * s := by nlinarith only [hc, hs, sq_nonneg (1 - c)]
      have h3 : 0 < 1 + c * (c + s) := by nlinarith only [hc, hs]
      nlinarith only [hr, hcs, h1, h2, h3]
    by_contra hboth
    push Not at hboth
    apply hnR
    exact ⟨abs_lt.mpr ⟨hU_gt, by linarith only [hboth.1]⟩,
           abs_lt.mpr ⟨by linarith only [hboth.2], hV_lt⟩⟩
  rcases hL with hL1 | hL2 <;> rcases hR with hR1 | hR4
  · nlinarith only [hr, hc, hc1, hw, hL1, hR1]
  · have hcx : r ≤ c * x := by nlinarith only [hs, hy2, hL1]
    have hsw : r ≤ s * (w - x) := by nlinarith only [hc, hy2, hR4]
    have hprod : r * (c + s) ≤ c * s * w := by nlinarith only [hc, hs, hcx, hsw]
    have h2cs : 2 * (c * s) ≤ c + s := by nlinarith only [hcs, hcs_ge, sq_nonneg (c - s)]
    have hcs_nn : 0 ≤ c * s := mul_nonneg hc hs
    nlinarith only [hr, hw, hcs_ge, hprod, h2cs, hcs_nn]
  · have hcomb : r * (c + s) ≤ c * s * w + h - y := by
      have hid : c * (s * x + c * (h - y)) + s * (c * (w - x) + s * (h - y)) =
          c * s * w + (c ^ 2 + s ^ 2) * (h - y) := by ring
      rw [hcs, one_mul] at hid
      nlinarith only [hc, hs, hL2, hR1, hid]
    have hbig : c + s < c * s * w + h := by nlinarith only [hr, hcs_ge, hy1, hcomb]
    set u := c + s
    have hu1 : 1 ≤ u := hcs_ge
    have hu_sq : u ^ 2 ≤ 2 := by
      have hid : u ^ 2 + (c - s) ^ 2 = 2 * (c ^ 2 + s ^ 2) := by simp only [u]; ring
      nlinarith only [hid, hcs, sq_nonneg (c - s)]
    have hu2 : u ≤ 3 / 2 := by nlinarith only [hu1, hu_sq]
    have hcs_eq : 2 * (c * s) = u ^ 2 - 1 := by
      have hid : u ^ 2 = c ^ 2 + s ^ 2 + 2 * (c * s) := by simp only [u]; ring
      linarith only [hid, hcs]
    have hcs_nn : 0 ≤ c * s := mul_nonneg hc hs
    have hbound : 20 * (c * s * w + h) ≤ 9 * (u ^ 2 + 1) := by
      nlinarith only [hw, hh, hcs_nn, hcs_eq]
    have hpoly : 20 * u - 9 * (u ^ 2 + 1) = 9 * (u - 1) * (3 / 2 - u) + (9 - 5 * u) / 2 := by ring
    nlinarith only [hu1, hu2, hbig, hbound, hpoly]
  · nlinarith only [hr, hs, hs1, hw, hL2, hR4]

private lemma lemma4_quad {r x y c s w b : ℝ}
    (hr : 1 / 2 < r) (hc : 0 ≤ c) (hs : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1)
    (hw0 : 0 < w) (hw1 : w ≤ 1) (hb0 : 1 / 2 ≤ b) (hb1 : b ≤ 1)
    (hdiag : w ^ 2 + (1 - b) ^ 2 ≤ 1)
    (hpoly : c * s * w + c ^ 2 + s ^ 2 * b ≤ c + s)
    (hx1 : 0 ≤ x) (hx2 : x ≤ w) (hy1 : r * (c + s) ≤ y) (hy2 : y ≤ 1)
    (htop : (1 - b) * x + w * y ≤ w) :
    boxInside r x y c s 0 1 ∨ boxInside r x y c s w b := by
  by_contra hnone
  push Not at hnone
  rcases hnone with ⟨hnL, hnR⟩
  have hc1 : c ≤ 1 := by nlinarith only [hc, hs, hcs]
  have hs1 : s ≤ 1 := by nlinarith only [hc, hs, hcs]
  have hcs_ge : 1 ≤ c + s := by nlinarith only [hc, hs, hcs]
  have hL : r ≤ c * x - s * (1 - y) ∨ r ≤ s * x + c * (1 - y) := by
    have hU_lt : c * (0 - x) + s * (1 - y) < r := by
      have h1 : c * (0 - x) + s * (1 - y) ≤ s * (1 - r * (c + s)) := by
        nlinarith only [hc, hs, hx1, hy1]
      have h2 : 0 ≤ (1 - s) ^ 2 + c * s := by nlinarith only [hc, hs, sq_nonneg (1 - s)]
      have h3 : 0 < 1 + s * (c + s) := by nlinarith only [hc, hs]
      nlinarith only [hr, hcs, h1, h2, h3]
    have hV_gt : -r < (-s) * (0 - x) + c * (1 - y) := by
      nlinarith only [hr, hc, hs, hx1, hy2]
    by_contra hboth
    push Not at hboth
    apply hnL
    exact ⟨abs_lt.mpr ⟨by linarith only [hboth.1], hU_lt⟩,
           abs_lt.mpr ⟨hV_gt, by linarith only [hboth.2]⟩⟩
  have hR : r ≤ c * (w - x) + s * (b - y) ∨ r ≤ s * (w - x) - c * (b - y) := by
    have hU_gt : -r < c * (w - x) + s * (b - y) := by
      nlinarith only [hr, hc, hs, hs1, hb0, hx2, hy2]
    have hV_lt : (-s) * (w - x) + c * (b - y) < r := by
      have h1 : (-s) * (w - x) + c * (b - y) ≤ c * (1 - r * (c + s)) := by
        nlinarith only [hc, hs, hb1, hx2, hy1]
      have h2 : 0 ≤ (1 - c) ^ 2 + c * s := by nlinarith only [hc, hs, sq_nonneg (1 - c)]
      have h3 : 0 < 1 + c * (c + s) := by nlinarith only [hc, hs]
      nlinarith only [hr, hcs, h1, h2, h3]
    by_contra hboth
    push Not at hboth
    apply hnR
    exact ⟨abs_lt.mpr ⟨hU_gt, by linarith only [hboth.1]⟩,
           abs_lt.mpr ⟨by linarith only [hboth.2], hV_lt⟩⟩
  rcases hL with hL1 | hL2 <;> rcases hR with hR1 | hR4
  · nlinarith only [hr, hc, hc1, hs, hw1, hb1, hL1, hR1]
  · set alpha := c * (1 - b) + s * w
    set beta := c * w - s * (1 - b)
    by_cases hbeta : beta ≤ 0
    · have hcw : c * w ≤ 1 / 2 := by nlinarith only [hs, hs1, hb0, hbeta]
      nlinarith only [hr, hc, hs, hx2, hy2, hL1, hcw]
    · push Not at hbeta
      have halpha : 0 ≤ alpha := by nlinarith only [hc, hs, hw0, hb1]
      have hab_sq : alpha ^ 2 + beta ^ 2 ≤ 1 := by
        have hid : alpha ^ 2 + beta ^ 2 = (c ^ 2 + s ^ 2) * (w ^ 2 + (1 - b) ^ 2) := by
          simp only [alpha, beta]; ring
        rw [hid, hcs, one_mul]; exact hdiag
      have halpha1 : alpha ≤ 1 := by nlinarith only [halpha, hab_sq, sq_nonneg beta]
      have hbeta1 : beta ≤ 1 := by nlinarith only [hbeta, hab_sq, sq_nonneg alpha]
      have h2ab : 2 * (alpha * beta) ≤ alpha + beta := by
        nlinarith only [halpha, hbeta, halpha1, hbeta1]
      have hcomb_eq : alpha * (c * x - s * (1 - y)) + beta * (s * (w - x) - c * (b - y)) =
          (c ^ 2 + s ^ 2) * ((1 - b) * x + w * y - w) + alpha * beta := by
        simp only [alpha, beta]; ring
      rw [hcs, one_mul] at hcomb_eq
      have hcomb_ge : (alpha + beta) * r ≤
          alpha * (c * x - s * (1 - y)) + beta * (s * (w - x) - c * (b - y)) := by
        nlinarith only [halpha, hbeta, hL1, hR4]
      nlinarith only [hr, halpha, hbeta, h2ab, htop, hcomb_eq, hcomb_ge]
  · have hid : c * (s * x + c * (1 - y)) + s * (c * (w - x) + s * (b - y)) =
        c * s * w + c ^ 2 + s ^ 2 * b - (c ^ 2 + s ^ 2) * y := by ring
    rw [hcs, one_mul] at hid
    have hge : r * (c + s) ≤ c * s * w + c ^ 2 + s ^ 2 * b - y := by
      nlinarith only [hc, hs, hL2, hR1, hid]
    nlinarith only [hr, hcs_ge, hy1, hpoly, hge]
  · have hsum : 1 < s * w + c * (1 - b) := by linarith only [hr, hL2, hR4]
    have hcs_ineq : (s * w + c * (1 - b)) ^ 2 ≤ (c ^ 2 + s ^ 2) * (w ^ 2 + (1 - b) ^ 2) := by
      nlinarith only [sq_nonneg (c * w - s * (1 - b))]
    rw [hcs, one_mul] at hcs_ineq
    nlinarith only [hsum, hcs_ineq, hdiag]

private lemma lemma4_poly_of_cubic {c s w b : ℝ}
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1)
    (hcub : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      0 ≤ -t ^ 3 + (1 + w) * t ^ 2 + (1 - 2 * b) * t + (1 - w)) :
    c * s * w + c ^ 2 + s ^ 2 * b ≤ c + s := by
  have h1c : 0 < 1 + c := by linarith only [hc]
  set t := s / (1 + c)
  have ht0 : 0 ≤ t := div_nonneg hs (le_of_lt h1c)
  have ht1 : t ≤ 1 := by
    rw [div_le_one h1c]
    nlinarith only [hc, hs, hcs]
  have hdenom : 0 < 1 + t ^ 2 := by positivity
  have hs_eq : s = t * (1 + c) := by
    simp only [t]; field_simp [h1c.ne']
  have h1c_eq : (1 + c) * (1 + t ^ 2) = 2 := by
    have h1 : t ^ 2 * (1 + c) ^ 2 = s ^ 2 := by rw [hs_eq]; ring
    have h2 : (1 + c) ^ 2 * (1 + t ^ 2) = 2 * (1 + c) := by
      have hid : (1 + c) ^ 2 + s ^ 2 = 2 * (1 + c) := by linarith only [hcs]
      linarith only [h1, hid]
    nlinarith only [h1c, h2]
  have hc_eq : c * (1 + t ^ 2) = 1 - t ^ 2 := by linarith only [h1c_eq]
  have hs_rat : s * (1 + t ^ 2) = 2 * t := by
    calc s * (1 + t ^ 2) = t * ((1 + c) * (1 + t ^ 2)) := by rw [hs_eq]; ring
      _ = 2 * t := by rw [h1c_eq]; ring
  have hid : ((c + s) - (c * s * w + c ^ 2 + s ^ 2 * b)) * (1 + t ^ 2) ^ 2 =
      2 * t * (-t ^ 3 + (1 + w) * t ^ 2 + (1 - 2 * b) * t + (1 - w)) := by
    have hmul : ((c + s) - (c * s * w + c ^ 2 + s ^ 2 * b)) * (1 + t ^ 2) ^ 2 =
        (c * (1 + t ^ 2) + s * (1 + t ^ 2)) * (1 + t ^ 2) -
        (c * (1 + t ^ 2)) * (s * (1 + t ^ 2)) * w -
        (c * (1 + t ^ 2)) ^ 2 - (s * (1 + t ^ 2)) ^ 2 * b := by ring
    rw [hmul, hc_eq, hs_rat]; ring
  have hp := hcub t ht0 ht1
  have hpos : 0 ≤ ((c + s) - (c * s * w + c ^ 2 + s ^ 2 * b)) * (1 + t ^ 2) ^ 2 := by
    rw [hid]; nlinarith only [ht0, hp]
  nlinarith only [hpos, sq_pos_of_pos hdenom]

private lemma lemma4_poly_a {c s w b : ℝ}
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1)
    (hw : w ≤ 179 / 200) (hb : b ≤ 9 / 10) :
    c * s * w + c ^ 2 + s ^ 2 * b ≤ c + s := by
  have hcs0 : 0 ≤ c * s := mul_nonneg hc hs
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  have hmon : c * s * w + c ^ 2 + s ^ 2 * b ≤ c * s * (179 / 200) + c ^ 2 + s ^ 2 * (9 / 10) := by
    nlinarith only [hcs0, hs2, hw, hb]
  have hbase : c * s * (179 / 200) + c ^ 2 + s ^ 2 * (9 / 10) ≤ c + s := by
    refine lemma4_poly_of_cubic hc hs hcs ?_
    intro t ht0 ht1
    have hid : -t ^ 3 + (1 + 179 / 200) * t ^ 2 + (1 - 2 * (9 / 10)) * t + (1 - 179 / 200) =
        (271 / 200 - t) * (t - 27 / 100) ^ 2 + 12441 / 2000000 * (1 - t) + 21641 / 2000000 * t := by
      ring
    rw [hid]
    have hterm : 0 ≤ (271 / 200 - t) * (t - 27 / 100) ^ 2 :=
      mul_nonneg (by linarith only [ht1]) (sq_nonneg _)
    linarith only [ht0, ht1, hterm]
  linarith only [hmon, hbase]

private lemma lemma4_poly_95 {c s w b : ℝ}
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1)
    (hw : w ≤ 19 / 20) (hb : b ≤ 39 / 50) :
    c * s * w + c ^ 2 + s ^ 2 * b ≤ c + s := by
  have hcs0 : 0 ≤ c * s := mul_nonneg hc hs
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  have hmon : c * s * w + c ^ 2 + s ^ 2 * b ≤ c * s * (19 / 20) + c ^ 2 + s ^ 2 * (39 / 50) := by
    nlinarith only [hcs0, hs2, hw, hb]
  have hbase : c * s * (19 / 20) + c ^ 2 + s ^ 2 * (39 / 50) ≤ c + s := by
    refine lemma4_poly_of_cubic hc hs hcs ?_
    intro t ht0 ht1
    have hid : -t ^ 3 + (1 + 19 / 20) * t ^ 2 + (1 - 2 * (39 / 50)) * t + (1 - 19 / 20) =
        (161 / 100 - t) * (t - 17 / 100) ^ 2 + 3471 / 1000000 * (1 - t) + 19771 / 1000000 * t := by
      ring
    rw [hid]
    have hterm : 0 ≤ (161 / 100 - t) * (t - 17 / 100) ^ 2 :=
      mul_nonneg (by linarith only [ht1]) (sq_nonneg _)
    linarith only [ht0, ht1, hterm]
  linarith only [hmon, hbase]

private lemma lemma6_U_bound {r x y c s : ℝ}
    (hr : 1 / 2 < r) (hc : 0 ≤ c) (hs : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1)
    (_hx1 : 0 ≤ x) (hx2 : x ≤ a0) (hy1 : r * (c + s) ≤ y) (hy2 : y ≤ 1)
    (hL2 : r ≤ s * x + c * (1 - y))
    (hR1 : r ≤ c * (a0 - x) + s * (1 - y)) :
    |c * (a0 / 2 - x) + s * (28 / 25 - y)| < r := by
  have ha_sq := a0_sq
  have ha_ub := a0_ub
  have ha_pos := a0_pos
  have hc1 : c ≤ 1 := by nlinarith only [hc, hs, hcs]
  have hs1 : s ≤ 1 := by nlinarith only [hc, hs, hcs]
  have hcs_ge : 1 ≤ c + s := by nlinarith only [hc, hs, hcs]
  have hlo : -r < c * (a0 / 2 - x) + s * (28 / 25 - y) := by
    have h1 : c * (x - a0 / 2) ≤ a0 / 2 := by nlinarith only [hc, hc1, hx2, ha_pos]
    have h2 : 0 ≤ s * (28 / 25 - y) := by nlinarith only [hs, hy2]
    linarith only [hr, ha_ub, h1, h2]
  have hcomb : r * (c + s) ≤ c * s * a0 + 1 - y := by
    have hid : c * (s * x + c * (1 - y)) + s * (c * (a0 - x) + s * (1 - y)) =
        c * s * a0 + (c ^ 2 + s ^ 2) * (1 - y) := by ring
    rw [hcs, one_mul] at hid
    nlinarith only [hc, hs, hL2, hR1, hid]
  have hfeas : c + s < c * s * a0 + 1 := by nlinarith only [hr, hcs_ge, hy1, hcomb]
  have hs_pos : 0 < s := by
    by_contra hle; push Not at hle
    have hs0 : s = 0 := le_antisymm hle hs
    rw [hs0] at hfeas hcs
    nlinarith only [hc, hcs, hfeas]
  have h1c : 0 < 1 + c := by linarith only [hc]
  set t := s / (1 + c)
  have ht0 : 0 < t := div_pos hs_pos h1c
  have ht1 : t ≤ 1 := by rw [div_le_one h1c]; nlinarith only [hc, hs, hcs]
  have hdenom : 0 < 1 + t ^ 2 := by positivity
  have hs_eq : s = t * (1 + c) := by simp only [t]; field_simp [h1c.ne']
  have h1c_eq : (1 + c) * (1 + t ^ 2) = 2 := by
    have h1 : t ^ 2 * (1 + c) ^ 2 = s ^ 2 := by rw [hs_eq]; ring
    have h2 : (1 + c) ^ 2 * (1 + t ^ 2) = 2 * (1 + c) := by
      have hid : (1 + c) ^ 2 + s ^ 2 = 2 * (1 + c) := by linarith only [hcs]
      linarith only [h1, hid]
    nlinarith only [h1c, h2]
  have hc_eq : c * (1 + t ^ 2) = 1 - t ^ 2 := by linarith only [h1c_eq]
  have hs_rat : s * (1 + t ^ 2) = 2 * t := by
    calc s * (1 + t ^ 2) = t * ((1 + c) * (1 + t ^ 2)) := by rw [hs_eq]; ring
      _ = 2 * t := by rw [h1c_eq]; ring
  have hFt_pos : 0 < -t ^ 2 + a0 * t + (a0 - 1) := by
    have hid : (c * s * a0 + 1 - (c + s)) * (1 + t ^ 2) ^ 2 =
        2 * t * (1 - t) * (-t ^ 2 + a0 * t + (a0 - 1)) := by
      have hmul : (c * s * a0 + 1 - (c + s)) * (1 + t ^ 2) ^ 2 =
          (c * (1 + t ^ 2)) * (s * (1 + t ^ 2)) * a0 + (1 + t ^ 2) ^ 2 -
          (c * (1 + t ^ 2) + s * (1 + t ^ 2)) * (1 + t ^ 2) := by ring
      rw [hmul, hc_eq, hs_rat]; ring
    have hpos : 0 < (c * s * a0 + 1 - (c + s)) * (1 + t ^ 2) ^ 2 :=
      mul_pos (by linarith only [hfeas]) (sq_pos_of_pos hdenom)
    rw [hid] at hpos
    by_contra hle; push Not at hle
    have hfac : 0 ≤ 2 * t * (1 - t) := by nlinarith only [ht0, ht1]
    nlinarith only [hpos, hfac, hle]
  have ht_hi : t ≤ 19 / 25 := by
    by_contra hgt; push Not at hgt
    have hF_ub : -t ^ 2 + a0 * t + (a0 - 1) ≤
        -t ^ 2 + (179 / 200) * t + (179 / 200 - 1) := by nlinarith only [ht0, ha_ub]
    have hF_id : -t ^ 2 + (179 / 200) * t + (179 / 200 - 1) =
        -(t - 19 / 25) ^ 2 - (5 / 8) * (t - 19 / 25) - 3 / 1250 := by ring
    nlinarith only [hFt_pos, hF_ub, hF_id, hgt, sq_nonneg (t - 19 / 25)]
  have hQ_nonneg : 0 ≤ -t ^ 3 + (1 + a0 / 2) * t ^ 2 + (1 - 2 * (28 / 25)) * t + (1 - a0 / 2) := by
    have h1mt2 : 0 ≤ 1 - t ^ 2 := by nlinarith only [ht0, ht1]
    have hmon : -t ^ 3 + (1 + 179 / 400) * t ^ 2 + (1 - 2 * (28 / 25)) * t + (1 - 179 / 400) ≤
        -t ^ 3 + (1 + a0 / 2) * t ^ 2 + (1 - 2 * (28 / 25)) * t + (1 - a0 / 2) := by
      have hdiff : (-t ^ 3 + (1 + a0 / 2) * t ^ 2 + (1 - 2 * (28 / 25)) * t + (1 - a0 / 2)) -
          (-t ^ 3 + (1 + 179 / 400) * t ^ 2 + (1 - 2 * (28 / 25)) * t + (1 - 179 / 400)) =
          (179 / 400 - a0 / 2) * (1 - t ^ 2) := by ring
      have hnn : 0 ≤ (179 / 400 - a0 / 2) * (1 - t ^ 2) := mul_nonneg (by linarith only [ha_ub]) h1mt2
      linarith only [hdiff, hnn]
    have hQ_id : -t ^ 3 + (1 + 179 / 400) * t ^ 2 + (1 - 2 * (28 / 25)) * t + (1 - 179 / 400) =
        9 / 1250 + (19 / 25 - t) * ((t - 11 / 32) ^ 2 + 15343 / 25600) := by ring
    have hprod : 0 ≤ (19 / 25 - t) * ((t - 11 / 32) ^ 2 + 15343 / 25600) :=
      mul_nonneg (by linarith only [ht_hi]) (by positivity)
    linarith only [hmon, hQ_id, hprod]
  have hpoly6 : c * s * (a0 / 2) + c ^ 2 + s ^ 2 * (28 / 25) ≤ c + s := by
    have hid : ((c + s) - (c * s * (a0 / 2) + c ^ 2 + s ^ 2 * (28 / 25))) * (1 + t ^ 2) ^ 2 =
        2 * t * (-t ^ 3 + (1 + a0 / 2) * t ^ 2 + (1 - 2 * (28 / 25)) * t + (1 - a0 / 2)) := by
      have hmul : ((c + s) - (c * s * (a0 / 2) + c ^ 2 + s ^ 2 * (28 / 25))) * (1 + t ^ 2) ^ 2 =
          (c * (1 + t ^ 2) + s * (1 + t ^ 2)) * (1 + t ^ 2) -
          (c * (1 + t ^ 2)) * (s * (1 + t ^ 2)) * (a0 / 2) -
          (c * (1 + t ^ 2)) ^ 2 - (s * (1 + t ^ 2)) ^ 2 * (28 / 25) := by ring
      rw [hmul, hc_eq, hs_rat]; ring
    have hnn : 0 ≤ ((c + s) - (c * s * (a0 / 2) + c ^ 2 + s ^ 2 * (28 / 25))) * (1 + t ^ 2) ^ 2 := by
      rw [hid]; nlinarith only [ht0, hQ_nonneg]
    nlinarith only [hnn, sq_pos_of_pos hdenom]
  have hhi : c * (a0 / 2 - x) + s * (28 / 25 - y) < r := by
    have hmul_id : s * (c * (a0 / 2 - x) + s * (28 / 25 - y)) + c * (s * x + c * (1 - y)) =
        c * s * (a0 / 2) + c ^ 2 + s ^ 2 * (28 / 25) - (c ^ 2 + s ^ 2) * y := by ring
    rw [hcs, one_mul] at hmul_id
    have hsU : s * (c * (a0 / 2 - x) + s * (28 / 25 - y)) < s * r := by
      nlinarith only [hr, hc, hcs_ge, hy1, hL2, hpoly6, hmul_id]
    nlinarith only [hs_pos, hsU]
  exact abs_lt.mpr ⟨hlo, hhi⟩

private lemma lemma6_pentagon {r x y c s : ℝ}
    (hr : 1 / 2 < r) (hc : 0 ≤ c) (hs : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1)
    (hx1 : 0 ≤ x) (hx2 : x ≤ a0) (hy1 : r * (c + s) ≤ y) (hy2 : y ≤ 1)
    (hn0 : ¬ boxInside r x y c s 0 1)
    (hna : ¬ boxInside r x y c s a0 1) :
    boxInside r x y c s (a0 / 2) (28 / 25) := by
  have ha_ub := a0_ub
  have hc1 : c ≤ 1 := by nlinarith only [hc, hs, hcs]
  have hs1 : s ≤ 1 := by nlinarith only [hc, hs, hcs]
  have hcs_ge : 1 ≤ c + s := by nlinarith only [hc, hs, hcs]
  have hL : r ≤ c * x - s * (1 - y) ∨ r ≤ s * x + c * (1 - y) := by
    have hU_lt : c * (0 - x) + s * (1 - y) < r := by
      have h1 : c * (0 - x) + s * (1 - y) ≤ s * (1 - r * (c + s)) := by nlinarith only [hc, hs, hx1, hy1]
      have h2 : 0 ≤ (1 - s) ^ 2 + c * s := by nlinarith only [hc, hs, sq_nonneg (1 - s)]
      have h3 : 0 < 1 + s * (c + s) := by nlinarith only [hc, hs]
      nlinarith only [hr, hcs, h1, h2, h3]
    have hV_gt : -r < (-s) * (0 - x) + c * (1 - y) := by nlinarith only [hr, hc, hs, hx1, hy2]
    by_contra hboth; push Not at hboth
    exact hn0 ⟨abs_lt.mpr ⟨by linarith only [hboth.1], hU_lt⟩,
               abs_lt.mpr ⟨hV_gt, by linarith only [hboth.2]⟩⟩
  have hR : r ≤ c * (a0 - x) + s * (1 - y) ∨ r ≤ s * (a0 - x) - c * (1 - y) := by
    have hU_gt : -r < c * (a0 - x) + s * (1 - y) := by nlinarith only [hr, hc, hs, hx2, hy2]
    have hV_lt : (-s) * (a0 - x) + c * (1 - y) < r := by
      have h1 : (-s) * (a0 - x) + c * (1 - y) ≤ c * (1 - r * (c + s)) := by nlinarith only [hc, hs, hx2, hy1]
      have h2 : 0 ≤ (1 - c) ^ 2 + c * s := by nlinarith only [hc, hs, sq_nonneg (1 - c)]
      have h3 : 0 < 1 + c * (c + s) := by nlinarith only [hc, hs]
      nlinarith only [hr, hcs, h1, h2, h3]
    by_contra hboth; push Not at hboth
    exact hna ⟨abs_lt.mpr ⟨hU_gt, by linarith only [hboth.1]⟩,
               abs_lt.mpr ⟨by linarith only [hboth.2], hV_lt⟩⟩
  have hL2R1 : r ≤ s * x + c * (1 - y) ∧ r ≤ c * (a0 - x) + s * (1 - y) := by
    rcases hL with hL1 | hL2 <;> rcases hR with hR1 | hR4
    · exfalso; nlinarith only [hr, hc, hc1, ha_ub, hL1, hR1]
    · exfalso
      have hcx : r ≤ c * x := by nlinarith only [hs, hy2, hL1]
      have hsw : r ≤ s * (a0 - x) := by nlinarith only [hc, hy2, hR4]
      have hprod : r * (c + s) ≤ c * s * a0 := by nlinarith only [hc, hs, hcx, hsw]
      have h2cs : 2 * (c * s) ≤ c + s := by nlinarith only [hcs, hcs_ge, sq_nonneg (c - s)]
      have hcs_nn : 0 ≤ c * s := mul_nonneg hc hs
      nlinarith only [hr, ha_ub, hcs_ge, hprod, h2cs, hcs_nn]
    · exact ⟨hL2, hR1⟩
    · exfalso; nlinarith only [hr, hs, hs1, ha_ub, hL2, hR4]
  rcases hL2R1 with ⟨hL2, hR1⟩
  have hU := lemma6_U_bound hr hc hs hcs hx1 hx2 hy1 hy2 hL2 hR1
  have hV_raw := lemma6_U_bound hr hs hc (by linarith only [hcs]) (by linarith only [hx2] : 0 ≤ a0 - x)
    (by linarith only [hx1] : a0 - x ≤ a0) (by linarith only [hy1] : r * (s + c) ≤ y) hy2
    (by linarith only [hR1] : r ≤ c * (a0 - x) + s * (1 - y))
    (by linarith only [hL2] : r ≤ s * (a0 - (a0 - x)) + c * (1 - y))
  have hV_eq : s * (a0 / 2 - (a0 - x)) + c * (28 / 25 - y) =
      (-s) * (a0 / 2 - x) + c * (28 / 25 - y) := by ring
  rw [hV_eq] at hV_raw
  exact ⟨hU, hV_raw⟩

/-! ### Section 3: Figure 13 (10-point piercing & extracting the special box hitting A1, A2, A3) -/

private noncomputable def fig13Pt : Fin 10 → ℝ × ℝ
  | ⟨0, _⟩ => (1, 1)
  | ⟨1, _⟩ => (1 + a0, 1)
  | ⟨2, _⟩ => (1 + 2 * a0, 1)
  | ⟨3, _⟩ => (1 - a0 / 2, 1 + a0)
  | ⟨4, _⟩ => (1 + a0 / 2, 1 + a0)
  | ⟨5, _⟩ => (1 + 3 * a0 / 2, 1 + a0)
  | ⟨6, _⟩ => (1 + 5 * a0 / 2, 1 + a0)
  | ⟨7, _⟩ => (1, 1 + 2 * a0)
  | ⟨8, _⟩ => (1 + a0, 1 + 2 * a0)
  | ⟨9, _⟩ => (1 + 2 * a0, 1 + 2 * a0)

private lemma fig13_reflectX (k : Fin 10) :
    ∃ j : Fin 10, (L0 - (fig13Pt k).1, (fig13Pt k).2) = fig13Pt j := by
  fin_cases k
  · exact ⟨⟨2, by decide⟩, by simp [fig13Pt, L0]; ring⟩
  · exact ⟨⟨1, by decide⟩, by simp [fig13Pt, L0]; ring⟩
  · exact ⟨⟨0, by decide⟩, by simp [fig13Pt, L0]; ring⟩
  · exact ⟨⟨6, by decide⟩, by simp [fig13Pt, L0]; ring⟩
  · exact ⟨⟨5, by decide⟩, by simp [fig13Pt, L0]; ring⟩
  · exact ⟨⟨4, by decide⟩, by simp [fig13Pt, L0]; ring⟩
  · exact ⟨⟨3, by decide⟩, by simp [fig13Pt, L0]; ring⟩
  · exact ⟨⟨9, by decide⟩, by simp [fig13Pt, L0]; ring⟩
  · exact ⟨⟨8, by decide⟩, by simp [fig13Pt, L0]; ring⟩
  · exact ⟨⟨7, by decide⟩, by simp [fig13Pt, L0]; ring⟩

private lemma fig13_reflectY (k : Fin 10) :
    ∃ j : Fin 10, ((fig13Pt k).1, L0 - (fig13Pt k).2) = fig13Pt j := by
  fin_cases k
  · exact ⟨⟨7, by decide⟩, by simp [fig13Pt, L0]; ring⟩
  · exact ⟨⟨8, by decide⟩, by simp [fig13Pt, L0]; ring⟩
  · exact ⟨⟨9, by decide⟩, by simp [fig13Pt, L0]; ring⟩
  · exact ⟨⟨3, by decide⟩, by simp [fig13Pt, L0]; ring⟩
  · exact ⟨⟨4, by decide⟩, by simp [fig13Pt, L0]; ring⟩
  · exact ⟨⟨5, by decide⟩, by simp [fig13Pt, L0]; ring⟩
  · exact ⟨⟨6, by decide⟩, by simp [fig13Pt, L0]; ring⟩
  · exact ⟨⟨0, by decide⟩, by simp [fig13Pt, L0]; ring⟩
  · exact ⟨⟨1, by decide⟩, by simp [fig13Pt, L0]; ring⟩
  · exact ⟨⟨2, by decide⟩, by simp [fig13Pt, L0]; ring⟩

private lemma fig13_quarter {r x y c s : ℝ}
    (hv : ValidBox r x y c s) (hx_le : x ≤ 1 + a0) (hy_le : y ≤ 1 + a0)
    (havoid : ∀ k : Fin 10, ¬ boxInside r x y c s (fig13Pt k).1 (fig13Pt k).2) :
    1 ≤ x ∧ y ≤ 1 := by
  have ha_sq := a0_sq
  have ha_pos := a0_pos
  have ha_ub := a0_ub
  rcases hv with ⟨hr, hc, hs, hcs, hx1, hx2, hy1, hy2⟩
  have h0 : ¬ boxInside r x y c s 1 1 := havoid ⟨0, by decide⟩
  have h1 : ¬ boxInside r x y c s (1 + a0) 1 := havoid ⟨1, by decide⟩
  have h3 : ¬ boxInside r x y c s (1 - a0 / 2) (1 + a0) := havoid ⟨3, by decide⟩
  have h4 : ¬ boxInside r x y c s (1 + a0 / 2) (1 + a0) := havoid ⟨4, by decide⟩
  have h5 : ¬ boxInside r x y c s (1 + 3 * a0 / 2) (1 + a0) := havoid ⟨5, by decide⟩
  by_cases hy : y ≤ 1
  · refine ⟨?_, hy⟩
    by_contra hx_lt
    push Not at hx_lt
    exact h0 (lemma1_corner hr hc hs hcs hx1 (le_of_lt hx_lt) (le_refl 1) hy1 hy (le_refl 1))
  · exfalso
    push Not at hy
    by_cases hside : 2 * x + y ≤ 3
    · have hq := lemma4_quad (x := y - 1) (y := x) (c := s) (s := c)
        (w := a0) (b := 1 - a0 / 2) hr hs hc (by linarith only [hcs]) ha_pos (by linarith only [ha_ub])
        (by linarith only [ha_ub]) (by linarith only [ha_pos]) (by nlinarith only [ha_sq])
        (lemma4_poly_a hs hc (by linarith only [hcs]) ha_ub (by linarith only [a0_lb]))
        (by linarith only [hy]) (by linarith only [hy_le]) (by linarith only [hx1])
        (by linarith only [hy, hside]) (by nlinarith only [ha_pos, hside])
      rcases hq with hq | hq
      · apply h0
        have heq := (boxInside_swap r x y c s 1 1).symm.trans
          ((boxInside_translate r y x s c 1 1 (-1) 0).symm)
        rw [show y + -1 = y - 1 by ring, show x + 0 = x by ring,
          show (1 : ℝ) + -1 = 0 by ring, show (1 : ℝ) + 0 = 1 by ring] at heq
        exact heq.mpr hq
      · apply h3
        have heq := (boxInside_swap r x y c s (1 - a0 / 2) (1 + a0)).symm.trans
          ((boxInside_translate r y x s c (1 + a0) (1 - a0 / 2) (-1) 0).symm)
        rw [show y + -1 = y - 1 by ring, show x + 0 = x by ring,
          show 1 + a0 + -1 = a0 by ring, show 1 - a0 / 2 + 0 = 1 - a0 / 2 by ring] at heq
        exact heq.mpr hq
    · push Not at hside
      by_cases htri1 : 2 * x - y ≤ 1
      · have ht := lemma2_triangle (x := x) (y := y) (x1 := 1 - a0 / 2) (y1 := 1 + a0)
          (x2 := 1) (y2 := 1) (x3 := 1 + a0 / 2) (y3 := 1 + a0) hr hcs
          (by nlinarith only [ha_sq]) (by nlinarith only [ha_sq]) (by nlinarith only [ha_sq])
          (by unfold cross2; nlinarith only [ha_sq])
          (by unfold cross2; nlinarith only [ha_pos, hside])
          (by unfold cross2; nlinarith only [ha_pos, htri1])
          (by unfold cross2; nlinarith only [ha_pos, hy_le])
        rcases ht with ht | ht | ht
        · exact h3 ht
        · exact h0 ht
        · exact h4 ht
      · push Not at htri1
        by_cases htri2 : 2 * x + y ≤ 3 + 2 * a0
        · have ht := lemma2_triangle (x := x) (y := y) (x1 := 1) (y1 := 1)
            (x2 := 1 + a0) (y2 := 1) (x3 := 1 + a0 / 2) (y3 := 1 + a0) hr hcs
            (by nlinarith only [ha_sq]) (by nlinarith only [ha_sq]) (by nlinarith only [ha_sq])
            (by unfold cross2; nlinarith only [ha_sq])
            (by unfold cross2; nlinarith only [ha_pos, hy])
            (by unfold cross2; nlinarith only [ha_pos, htri2])
            (by unfold cross2; nlinarith only [ha_pos, htri1])
          rcases ht with ht | ht | ht
          · exact h0 ht
          · exact h1 ht
          · exact h4 ht
        · push Not at htri2
          have ht := lemma2_triangle (x := x) (y := y) (x1 := 1 + a0 / 2) (y1 := 1 + a0)
            (x2 := 1 + a0) (y2 := 1) (x3 := 1 + 3 * a0 / 2) (y3 := 1 + a0) hr hcs
            (by nlinarith only [ha_sq]) (by nlinarith only [ha_sq]) (by nlinarith only [ha_sq])
            (by unfold cross2; nlinarith only [ha_sq])
            (by unfold cross2; nlinarith only [ha_pos, htri2])
            (by unfold cross2; nlinarith only [ha_pos, hx_le, hy])
            (by unfold cross2; nlinarith only [ha_pos, hy_le])
          rcases ht with ht | ht | ht
          · exact h4 ht
          · exact h1 ht
          · exact h5 ht

private lemma box_in_slot_hits_A123 {r x y c s : ℝ}
    (hv : ValidBox r x y c s)
    (hx_ge : 1 ≤ x) (hx_le : x ≤ 1 + a0) (hy_le : y ≤ 1)
    (hn0 : ¬ boxInside r x y c s 1 1)
    (hn1 : ¬ boxInside r x y c s (1 + a0) 1) :
    boxInside r x y c s 1 (9 / 10) ∧
    boxInside r x y c s (1 + a0) (9 / 10) ∧
    boxInside r x y c s (1 + a0 / 2) (28 / 25) := by
  have ha_sq := a0_sq
  have ha_pos := a0_pos
  have ha_ub := a0_ub
  rcases hv with ⟨hr, hc, hs, hcs, hx1, hx2, hy1, hy2⟩
  refine ⟨?_, ?_, ?_⟩
  · -- Hits A1 = (1, 9/10)
    by_cases hseg : (1 / 10 : ℝ) * (1 + a0 - x) + a0 * y ≤ a0
    · have hq := lemma4_quad (x := 1 + a0 - x) (y := y) (c := s) (s := c)
        (w := a0) (b := 9 / 10) hr hs hc (by linarith only [hcs]) ha_pos (by linarith only [ha_ub])
        (by norm_num) (by norm_num) (by nlinarith only [ha_sq])
        (lemma4_poly_a hs hc (by linarith only [hcs]) ha_ub (le_refl _))
        (by linarith only [hx_le]) (by linarith only [hx_ge]) (by linarith only [hy1])
        hy_le (by linarith only [hseg])
      rcases hq with hq | hq
      · exfalso
        apply hn1
        have heq := boxInside_reflectX r x y c s (1 + a0) 1 (1 + a0)
        rw [show 1 + a0 - (1 + a0) = 0 by ring] at heq
        exact heq.mp hq
      · have heq := boxInside_reflectX r x y c s 1 (9 / 10) (1 + a0)
        rw [show 1 + a0 - 1 = a0 by ring] at heq
        exact heq.mp hq
    · push Not at hseg
      have ht := lemma2_triangle (x := x) (y := y) (x1 := 1) (y1 := 9 / 10)
        (x2 := 1 + a0) (y2 := 1) (x3 := 1) (y3 := 1) hr hcs
        (by nlinarith only [ha_sq]) (by nlinarith only [ha_sq]) (by norm_num)
        (by unfold cross2; linarith only [ha_pos])
        (by unfold cross2; linarith only [hseg])
        (by unfold cross2; nlinarith only [ha_pos, hy_le])
        (by unfold cross2; linarith only [hx_ge])
      rcases ht with ht | ht | ht
      · exact ht
      · exact False.elim (hn1 ht)
      · exact False.elim (hn0 ht)
  · -- Hits A2 = (1 + a0, 9/10)
    by_cases hseg : (1 / 10 : ℝ) * (x - 1) + a0 * y ≤ a0
    · have hq := lemma4_quad (x := x - 1) (y := y) (c := c) (s := s)
        (w := a0) (b := 9 / 10) hr hc hs hcs ha_pos (by linarith only [ha_ub])
        (by norm_num) (by norm_num) (by nlinarith only [ha_sq])
        (lemma4_poly_a hc hs hcs ha_ub (le_refl _))
        (by linarith only [hx_ge]) (by linarith only [hx_le]) hy1 hy_le (by linarith only [hseg])
      rcases hq with hq | hq
      · exfalso
        apply hn0
        have heq := boxInside_translate r x y c s 1 1 (-1) 0
        rw [show x + -1 = x - 1 by ring, show y + 0 = y by ring,
          show (1 : ℝ) + -1 = 0 by ring, show (1 : ℝ) + 0 = 1 by ring] at heq
        exact heq.mp hq
      · have heq := boxInside_translate r x y c s (1 + a0) (9 / 10) (-1) 0
        rw [show x + -1 = x - 1 by ring, show y + 0 = y by ring,
          show 1 + a0 + -1 = a0 by ring, show (9 / 10 : ℝ) + 0 = 9 / 10 by ring] at heq
        exact heq.mp hq
    · push Not at hseg
      have ht := lemma2_triangle (x := x) (y := y) (x1 := 1) (y1 := 1)
        (x2 := 1 + a0) (y2 := 9 / 10) (x3 := 1 + a0) (y3 := 1) hr hcs
        (by nlinarith only [ha_sq]) (by norm_num) (by nlinarith only [ha_sq])
        (by unfold cross2; linarith only [ha_pos])
        (by unfold cross2; linarith only [hseg])
        (by unfold cross2; linarith only [hx_le])
        (by unfold cross2; nlinarith only [ha_pos, hy_le])
      rcases ht with ht | ht | ht
      · exact False.elim (hn0 ht)
      · exact ht
      · exact False.elim (hn1 ht)
  · -- Hits A3 = (1 + a0 / 2, 28 / 25) via translated Lemma 6
    have hn0' : ¬ boxInside r (x - 1) y c s 0 1 := by
      have heq := boxInside_translate r x y c s 1 1 (-1) 0
      rw [show x + -1 = x - 1 by ring, show y + 0 = y by ring,
        show (1 : ℝ) + -1 = 0 by ring, show (1 : ℝ) + 0 = 1 by ring] at heq
      rwa [heq]
    have hn1' : ¬ boxInside r (x - 1) y c s a0 1 := by
      have heq := boxInside_translate r x y c s (1 + a0) 1 (-1) 0
      rw [show x + -1 = x - 1 by ring, show y + 0 = y by ring,
        show 1 + a0 + -1 = a0 by ring, show (1 : ℝ) + 0 = 1 by ring] at heq
      rwa [heq]
    have h6 := lemma6_pentagon hr hc hs hcs (by linarith only [hx_ge]) (by linarith only [hx_le])
      hy1 hy_le hn0' hn1'
    have heq := boxInside_translate r x y c s (1 + a0 / 2) (28 / 25) (-1) 0
    rw [show x + -1 = x - 1 by ring, show y + 0 = y by ring,
      show 1 + a0 / 2 + -1 = a0 / 2 by ring, show (28 / 25 : ℝ) + 0 = 28 / 25 by ring] at heq
    exact heq.mp h6

/-! ### Section 4: Figure 14 (12-point universal piercing with corrected G = (39/50, 46/25)) -/

private noncomputable def fig14Pt : Fin 12 → ℝ × ℝ
  | ⟨0, _⟩  => (1, 9 / 10)                     -- A1
  | ⟨1, _⟩  => (1 + a0, 9 / 10)                -- A2
  | ⟨2, _⟩  => (1 + a0 / 2, 28 / 25)           -- A3
  | ⟨3, _⟩  => (1 + 2 * a0, 1)                 -- B
  | ⟨4, _⟩  => (11 / 10 + 2 * a0, 1 + a0)      -- C
  | ⟨5, _⟩  => (1 + 2 * a0, 1 + 2 * a0)        -- D
  | ⟨6, _⟩  => (1 + a0, 11 / 10 + 2 * a0)      -- E
  | ⟨7, _⟩  => (1, 1 + 2 * a0)                 -- F
  | ⟨8, _⟩  => (39 / 50, 46 / 25)              -- G
  | ⟨9, _⟩  => (3 / 2, 21 / 10)                -- H
  | ⟨10, _⟩ => (21 / 10, 21 / 10)              -- I
  | ⟨11, _⟩ => (21 / 10, 3 / 2)                -- J

private lemma fig14_tri_helper {r x y c s : ℝ}
    (hr : 1 / 2 < r) (hcs : c ^ 2 + s ^ 2 = 1)
    (k1 k2 k3 : Fin 12)
    (hd12 : ((fig14Pt k1).1 - (fig14Pt k2).1) ^ 2 + ((fig14Pt k1).2 - (fig14Pt k2).2) ^ 2 ≤ 1)
    (hd23 : ((fig14Pt k2).1 - (fig14Pt k3).1) ^ 2 + ((fig14Pt k2).2 - (fig14Pt k3).2) ^ 2 ≤ 1)
    (hd31 : ((fig14Pt k3).1 - (fig14Pt k1).1) ^ 2 + ((fig14Pt k3).2 - (fig14Pt k1).2) ^ 2 ≤ 1)
    (hD : 0 < cross2 (fig14Pt k1).1 (fig14Pt k1).2 (fig14Pt k2).1 (fig14Pt k2).2
      (fig14Pt k3).1 (fig14Pt k3).2)
    (he12 : 0 ≤ cross2 (fig14Pt k1).1 (fig14Pt k1).2 (fig14Pt k2).1 (fig14Pt k2).2 x y)
    (he23 : 0 ≤ cross2 (fig14Pt k2).1 (fig14Pt k2).2 (fig14Pt k3).1 (fig14Pt k3).2 x y)
    (he31 : 0 ≤ cross2 (fig14Pt k3).1 (fig14Pt k3).2 (fig14Pt k1).1 (fig14Pt k1).2 x y) :
    ∃ k : Fin 12, boxInside r x y c s (fig14Pt k).1 (fig14Pt k).2 := by
  rcases lemma2_triangle hr hcs hd12 hd23 hd31 hD he12 he23 he31 with h | h | h
  · exact ⟨k1, h⟩
  · exact ⟨k2, h⟩
  · exact ⟨k3, h⟩

-- Split Figure 14 interior triangulation into 3 fast sub-lemmas (north, southwest, east)
private lemma fig14_interior_north {r x y c s : ℝ}
    (hr : 1 / 2 < r) (hcs : c ^ 2 + s ^ 2 = 1)
    (hHI : (21 / 10 : ℝ) ≤ y)
    (ho4 : 0 ≤ (1 + 2 * a0 - (11 / 10 + 2 * a0)) * (y - (1 + a0)) -
               (1 + 2 * a0 - (1 + a0)) * (x - (11 / 10 + 2 * a0)))
    (ho5 : 0 ≤ (1 + a0 - (1 + 2 * a0)) * (y - (1 + 2 * a0)) -
               (11 / 10 + 2 * a0 - (1 + 2 * a0)) * (x - (1 + 2 * a0)))
    (ho6 : 0 ≤ (1 - (1 + a0)) * (y - (11 / 10 + 2 * a0)) -
               (1 + 2 * a0 - (11 / 10 + 2 * a0)) * (x - (1 + a0)))
    (ho7 : 0 ≤ (39 / 50 - 1) * (y - (1 + 2 * a0)) -
               (46 / 25 - (1 + 2 * a0)) * (x - 1)) :
    ∃ k : Fin 12, boxInside r x y c s (fig14Pt k).1 (fig14Pt k).2 := by
  have ha_sq := a0_sq
  have ha_lb := a0_lb
  have ha_ub := a0_ub_tight
  by_cases hFH : 0 ≤ (3 / 2 - 1) * (y - (1 + 2 * a0)) - (21 / 10 - (1 + 2 * a0)) * (x - 1)
  · by_cases hID : 0 ≤ (1 + 2 * a0 - 21 / 10) * (y - 21 / 10) - (1 + 2 * a0 - 21 / 10) * (x - 21 / 10)
    · by_cases hHE : 0 ≤ (1 + a0 - 3 / 2) * (y - 21 / 10) - (11 / 10 + 2 * a0 - 21 / 10) * (x - 3 / 2)
      · exact fig14_tri_helper hr hcs ⟨7, by decide⟩ ⟨9, by decide⟩ ⟨6, by decide⟩
          (by simp [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
          (by simp [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
          (by simp [fig14Pt]; nlinarith only [ha_sq])
          (by simp [fig14Pt, cross2]; nlinarith only [ha_sq, ha_lb, ha_ub])
          (by simp [fig14Pt, cross2]; linarith only [hFH])
          (by simp [fig14Pt, cross2]; linarith only [hHE])
          (by simp [fig14Pt, cross2]; linarith only [ho6])
      · push Not at hHE
        by_cases hIE : 0 ≤ (1 + a0 - 21 / 10) * (y - 21 / 10) - (11 / 10 + 2 * a0 - 21 / 10) * (x - 21 / 10)
        · exact fig14_tri_helper hr hcs ⟨6, by decide⟩ ⟨9, by decide⟩ ⟨10, by decide⟩
            (by simp [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
            (by simp [fig14Pt]; norm_num)
            (by simp [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
            (by simp [fig14Pt, cross2]; nlinarith only [ha_lb])
            (by simp [fig14Pt, cross2]; linarith only [hHE])
            (by simp [fig14Pt, cross2]; linarith only [hHI])
            (by simp [fig14Pt, cross2]; linarith only [hIE])
        · push Not at hIE
          exact fig14_tri_helper hr hcs ⟨6, by decide⟩ ⟨10, by decide⟩ ⟨5, by decide⟩
            (by simp [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
            (by simp [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
            (by simp [fig14Pt]; nlinarith only [ha_sq])
            (by simp [fig14Pt, cross2]; nlinarith only [ha_sq, ha_lb, ha_ub])
            (by simp [fig14Pt, cross2]; linarith only [hIE])
            (by simp [fig14Pt, cross2]; linarith only [hID])
            (by simp [fig14Pt, cross2]; linarith only [ho5])
    · push Not at hID
      have hx_ge : (21 / 10 : ℝ) ≤ x := by nlinarith only [ha_lb, hHI, hID]
      exact fig14_tri_helper hr hcs ⟨5, by decide⟩ ⟨10, by decide⟩ ⟨4, by decide⟩
        (by simp [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
        (by simp [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
        (by simp [fig14Pt]; nlinarith only [ha_sq])
        (by simp [fig14Pt, cross2]; nlinarith only [ha_sq, ha_lb, ha_ub])
        (by simp [fig14Pt, cross2]; linarith only [hID])
        (by simp [fig14Pt, cross2]; nlinarith only [ha_lb, ha_ub, hHI, hx_ge])
        (by simp [fig14Pt, cross2]; linarith only [ho4])
  · push Not at hFH
    have hx_le : x ≤ (3 / 2 : ℝ) := by nlinarith only [ha_lb, hHI, hFH]
    exact fig14_tri_helper hr hcs ⟨7, by decide⟩ ⟨8, by decide⟩ ⟨9, by decide⟩
      (by simp [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
      (by simp [fig14Pt]; norm_num)
      (by simp [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
      (by simp [fig14Pt, cross2]; nlinarith only [ha_lb])
      (by simp [fig14Pt, cross2]; linarith only [ho7])
      (by simp [fig14Pt, cross2]; linarith only [hHI, hx_le])
      (by simp [fig14Pt, cross2]; linarith only [hFH])

private lemma fig14_interior_east {r x y c s : ℝ}
    (hr : 1 / 2 < r) (hcs : c ^ 2 + s ^ 2 = 1)
    (hHI : y < (21 / 10 : ℝ)) (hJI : (21 / 10 : ℝ) < x)
    (ho2 : 0 ≤ (1 + 2 * a0 - (1 + a0)) * (y - 9 / 10) - (1 - 9 / 10) * (x - (1 + a0)))
    (ho3 : 0 ≤ (11 / 10 + 2 * a0 - (1 + 2 * a0)) * (y - 1) - (1 + a0 - 1) * (x - (1 + 2 * a0)))
    (ho4 : 0 ≤ (1 + 2 * a0 - (11 / 10 + 2 * a0)) * (y - (1 + a0)) -
               (1 + 2 * a0 - (1 + a0)) * (x - (11 / 10 + 2 * a0))) :
    ∃ k : Fin 12, boxInside r x y c s (fig14Pt k).1 (fig14Pt k).2 := by
  have ha_sq := a0_sq
  have ha_lb := a0_lb
  have ha_ub := a0_ub_tight
  by_cases hCI : 0 ≤ (21 / 10 - (11 / 10 + 2 * a0)) * (y - (1 + a0)) - (21 / 10 - (1 + a0)) * (x - (11 / 10 + 2 * a0))
  · by_cases hJC : 0 ≤ (11 / 10 + 2 * a0 - 21 / 10) * (y - 3 / 2) - (1 + a0 - 3 / 2) * (x - 21 / 10)
    · exact fig14_tri_helper hr hcs ⟨4, by decide⟩ ⟨10, by decide⟩ ⟨11, by decide⟩
        (by simp [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
        (by simp [fig14Pt]; norm_num)
        (by simp [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
        (by simp [fig14Pt, cross2]; nlinarith only [ha_lb])
        (by simp [fig14Pt, cross2]; linarith only [hCI])
        (by simp [fig14Pt, cross2]; linarith only [hJI])
        (by simp [fig14Pt, cross2]; linarith only [hJC])
    · push Not at hJC
      by_cases hJB : 0 ≤ (1 + 2 * a0 - 21 / 10) * (y - 3 / 2) - (1 - 3 / 2) * (x - 21 / 10)
      · exact fig14_tri_helper hr hcs ⟨4, by decide⟩ ⟨11, by decide⟩ ⟨3, by decide⟩
          (by simp [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
          (by simp [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
          (by simp [fig14Pt]; nlinarith only [ha_sq])
          (by simp [fig14Pt, cross2]; nlinarith only [ha_sq, ha_lb, ha_ub])
          (by simp [fig14Pt, cross2]; linarith only [hJC])
          (by simp [fig14Pt, cross2]; linarith only [hJB])
          (by simp [fig14Pt, cross2]; linarith only [ho3])
      · push Not at hJB
        have hy_lt : y < (3 / 2 : ℝ) := by nlinarith only [ha_lb, hJI, hJB]
        exact fig14_tri_helper hr hcs ⟨1, by decide⟩ ⟨3, by decide⟩ ⟨11, by decide⟩
          (by simp [fig14Pt]; nlinarith only [ha_sq])
          (by simp [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
          (by simp [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
          (by simp [fig14Pt, cross2]; nlinarith only [ha_sq, ha_lb, ha_ub])
          (by simp [fig14Pt, cross2]; linarith only [ho2])
          (by simp [fig14Pt, cross2]; linarith only [hJB])
          (by simp [fig14Pt, cross2]; nlinarith only [ha_lb, ha_ub, hJI, hy_lt])
  · push Not at hCI
    exact fig14_tri_helper hr hcs ⟨5, by decide⟩ ⟨10, by decide⟩ ⟨4, by decide⟩
      (by simp [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
      (by simp [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
      (by simp [fig14Pt]; nlinarith only [ha_sq])
      (by simp [fig14Pt, cross2]; nlinarith only [ha_sq, ha_lb, ha_ub])
      (by simp [fig14Pt, cross2]; nlinarith only [ha_lb, hHI, hJI])
      (by simp [fig14Pt, cross2]; linarith only [hCI])
      (by simp [fig14Pt, cross2]; linarith only [ho4])

private lemma fig14_interior_sw {r x y c s : ℝ}
    (hr : 1 / 2 < r) (hcs : c ^ 2 + s ^ 2 = 1)
    (hHI : y < (21 / 10 : ℝ)) (hJI : x ≤ (21 / 10 : ℝ))
    (ho1 : 0 ≤ (1 + a0 - 1) * (y - 9 / 10) - (9 / 10 - 9 / 10) * (x - 1))
    (ho2 : 0 ≤ (1 + 2 * a0 - (1 + a0)) * (y - 9 / 10) - (1 - 9 / 10) * (x - (1 + a0)))
    (ho7 : 0 ≤ (39 / 50 - 1) * (y - (1 + 2 * a0)) - (46 / 25 - (1 + 2 * a0)) * (x - 1))
    (ho8 : 0 ≤ (1 - 39 / 50) * (y - 46 / 25) - (9 / 10 - 46 / 25) * (x - 39 / 50)) :
    ∃ k : Fin 12, boxInside r x y c s (fig14Pt k).1 (fig14Pt k).2 := by
  have ha_sq := a0_sq
  have ha_lb := a0_lb
  have ha_ub := a0_ub_tight
  have hy_ge9 : (9 / 10 : ℝ) ≤ y := by nlinarith only [ha_lb, ho1]
  by_cases hHJ : (36 / 10 : ℝ) ≤ x + y
  · exact fig14_tri_helper hr hcs ⟨9, by decide⟩ ⟨11, by decide⟩ ⟨10, by decide⟩
      (by simp [fig14Pt]; norm_num) (by simp [fig14Pt]; norm_num) (by simp [fig14Pt]; norm_num)
      (by simp [fig14Pt, cross2]; norm_num)
      (by simp [fig14Pt, cross2]; linarith only [hHJ])
      (by simp [fig14Pt, cross2]; linarith only [hJI])
      (by simp [fig14Pt, cross2]; linarith only [hHI])
  · push Not at hHJ
    by_cases hGH : 0 ≤ (3 / 2 - 39 / 50) * (y - 46 / 25) - (21 / 10 - 46 / 25) * (x - 39 / 50)
    · have hx_lt : x < (3 / 2 : ℝ) := by linarith only [hHI, hGH]
      exact fig14_tri_helper hr hcs ⟨7, by decide⟩ ⟨8, by decide⟩ ⟨9, by decide⟩
        (by simp [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
        (by simp [fig14Pt]; norm_num)
        (by simp [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
        (by simp [fig14Pt, cross2]; nlinarith only [ha_lb])
        (by simp [fig14Pt, cross2]; linarith only [ho7])
        (by simp [fig14Pt, cross2]; linarith only [hGH])
        (by simp [fig14Pt, cross2]; nlinarith only [ha_lb, hHI, hx_lt])
    · push Not at hGH
      by_cases hA3H : 0 ≤ (3 / 2 - (1 + a0 / 2)) * (y - 28 / 25) - (21 / 10 - 28 / 25) * (x - (1 + a0 / 2))
      · by_cases hGA3 : 0 ≤ (1 + a0 / 2 - 39 / 50) * (y - 46 / 25) - (28 / 25 - 46 / 25) * (x - 39 / 50)
        · exact fig14_tri_helper hr hcs ⟨8, by decide⟩ ⟨2, by decide⟩ ⟨9, by decide⟩
            (by simp [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
            (by simp [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
            (by simp [fig14Pt]; norm_num)
            (by simp [fig14Pt, cross2]; nlinarith only [ha_lb])
            (by simp [fig14Pt, cross2]; linarith only [hGA3])
            (by simp [fig14Pt, cross2]; linarith only [hA3H])
            (by simp [fig14Pt, cross2]; linarith only [hGH])
        · push Not at hGA3
          by_cases hA1A3 : 0 ≤ (1 + a0 / 2 - 1) * (y - 9 / 10) - (28 / 25 - 9 / 10) * (x - 1)
          · exact fig14_tri_helper hr hcs ⟨8, by decide⟩ ⟨0, by decide⟩ ⟨2, by decide⟩
              (by simp [fig14Pt]; norm_num)
              (by simp [fig14Pt]; nlinarith only [ha_sq])
              (by simp [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
              (by simp [fig14Pt, cross2]; nlinarith only [ha_lb])
              (by simp [fig14Pt, cross2]; linarith only [ho8])
              (by simp [fig14Pt, cross2]; linarith only [hA1A3])
              (by simp [fig14Pt, cross2]; linarith only [hGA3])
          · push Not at hA1A3
            have hy_leA3 : y ≤ (28 / 25 : ℝ) := by
              -- From hA1A3 < 0 and hA3H >= 0, eliminate x - (1 + a0/2)!
              -- hA1A3: (a0/2)*(y - 28/25) < (11/50)*(x - (1 + a0/2))
              -- hA3H:  (49/50)*(x - (1 + a0/2)) <= (1/2 - a0/2)*(y - 28/25)
              have h1 : (a0 / 2) * (y - 28 / 25) < (11 / 50) * (x - (1 + a0 / 2)) := by
                linarith only [hA1A3]
              have h2 : (49 / 50) * (x - (1 + a0 / 2)) ≤ (1 / 2 - a0 / 2) * (y - 28 / 25) := by
                linarith only [hA3H]
              nlinarith only [ha_lb, ha_ub, h1, h2]
            have hx_leA3 : x ≤ 1 + a0 / 2 := by
              have h2 : (49 / 50) * (x - (1 + a0 / 2)) ≤ (1 / 2 - a0 / 2) * (y - 28 / 25) := by
                linarith only [hA3H]
              nlinarith only [ha_ub, hy_leA3, h2]
            exact fig14_tri_helper hr hcs ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩
              (by simp only [fig14Pt]; nlinarith only [ha_sq])
              (by simp only [fig14Pt]; nlinarith only [ha_sq])
              (by simp only [fig14Pt]; nlinarith only [ha_sq])
              (by simp only [fig14Pt, cross2]; linarith only [ha_lb])
              (by simp only [fig14Pt, cross2]; linarith only [ho1])
              (by simp only [fig14Pt, cross2]; nlinarith only [ha_lb, hy_leA3, hx_leA3])
              (by simp only [fig14Pt, cross2]; linarith only [hA1A3])
      · push Not at hA3H
        by_cases hA3J : 0 ≤ (21 / 10 - (1 + a0 / 2)) * (y - 28 / 25) - (3 / 2 - 28 / 25) * (x - (1 + a0 / 2))
        · exact fig14_tri_helper hr hcs ⟨2, by decide⟩ ⟨11, by decide⟩ ⟨9, by decide⟩
            (by simp only [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
            (by simp only [fig14Pt]; norm_num)
            (by simp only [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
            (by simp only [fig14Pt, cross2]; nlinarith only [ha_lb, ha_ub])
            (by simp only [fig14Pt, cross2]; linarith only [hA3J])
            (by simp only [fig14Pt, cross2]; linarith only [hHJ])
            (by simp only [fig14Pt, cross2]; linarith only [hA3H])
        · push Not at hA3J
          by_cases hA2A3 : 0 ≤ (1 + a0 / 2 - (1 + a0)) * (y - 9 / 10) - (28 / 25 - 9 / 10) * (x - (1 + a0))
          · have hA3A1 : 0 ≤ (1 - (1 + a0 / 2)) * (y - 28 / 25) -
                (9 / 10 - 28 / 25) * (x - (1 + a0 / 2)) := by
              have hid : (19 / 50 * a0 + 11 / 100) *
                  ((1 - (1 + a0 / 2)) * (y - 28 / 25) - (9 / 10 - 28 / 25) * (x - (1 + a0 / 2))) =
                  (11 / 50 * a0) * (-((3 / 2 - (1 + a0 / 2)) * (y - 28 / 25) -
                    (21 / 10 - 28 / 25) * (x - (1 + a0 / 2)))) +
                  (3 / 5 * a0 - 11 / 100) * ((1 + a0 / 2 - (1 + a0)) * (y - 9 / 10) -
                    (28 / 25 - 9 / 10) * (x - (1 + a0))) := by ring
              have h1 : 0 ≤ (11 / 50 * a0) * (-((3 / 2 - (1 + a0 / 2)) * (y - 28 / 25) -
                  (21 / 10 - 28 / 25) * (x - (1 + a0 / 2)))) :=
                mul_nonneg (by linarith only [ha_lb]) (by linarith only [hA3H])
              have h2 : 0 ≤ (3 / 5 * a0 - 11 / 100) * ((1 + a0 / 2 - (1 + a0)) * (y - 9 / 10) -
                  (28 / 25 - 9 / 10) * (x - (1 + a0))) :=
                mul_nonneg (by linarith only [ha_lb]) hA2A3
              have hD : 0 < 19 / 50 * a0 + 11 / 100 := by linarith only [ha_lb]
              nlinarith only [hid, h1, h2, hD]
            exact fig14_tri_helper hr hcs ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩
              (by simp only [fig14Pt]; nlinarith only [ha_sq])
              (by simp only [fig14Pt]; nlinarith only [ha_sq])
              (by simp only [fig14Pt]; nlinarith only [ha_sq])
              (by simp only [fig14Pt, cross2]; linarith only [ha_lb])
              (by simp only [fig14Pt, cross2]; linarith only [ho1])
              (by simp only [fig14Pt, cross2]; linarith only [hA2A3])
              (by simp only [fig14Pt, cross2]; linarith only [hA3A1])
          · push Not at hA2A3
            by_cases hA2J : 0 ≤ (21 / 10 - (1 + a0)) * (y - 9 / 10) - (3 / 2 - 9 / 10) * (x - (1 + a0))
            · exact fig14_tri_helper hr hcs ⟨2, by decide⟩ ⟨1, by decide⟩ ⟨11, by decide⟩
                (by simp [fig14Pt]; nlinarith only [ha_sq])
                (by simp [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
                (by simp [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
                (by simp [fig14Pt, cross2]; nlinarith only [ha_lb])
                (by simp [fig14Pt, cross2]; linarith only [hA2A3])
                (by simp [fig14Pt, cross2]; linarith only [hA2J])
                (by simp [fig14Pt, cross2]; linarith only [hA3J])
            · push Not at hA2J
              have hy_ltJ : y < (3 / 2 : ℝ) := by
                -- hA2J < 0: (11/10 - a0)*(y - 3/2) < (3/5)*(x - 21/10) <= 0
                have h1 : (11 / 10 - a0) * (y - 3 / 2) < (3 / 5) * (x - 21 / 10) := by
                  linarith only [hA2J]
                nlinarith only [ha_ub, hJI, h1]
              exact fig14_tri_helper hr hcs ⟨1, by decide⟩ ⟨3, by decide⟩ ⟨11, by decide⟩
                (by simp [fig14Pt]; nlinarith only [ha_sq])
                (by simp [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
                (by simp [fig14Pt]; nlinarith only [ha_sq, ha_lb, ha_ub])
                (by simp [fig14Pt, cross2]; nlinarith only [ha_sq, ha_lb, ha_ub])
                (by simp [fig14Pt, cross2]; linarith only [ho2])
                (by simp [fig14Pt, cross2]; nlinarith only [ha_lb, hJI, hy_ltJ])
                (by simp [fig14Pt, cross2]; linarith only [hA2J])

private lemma fig14_interior {r x y c s : ℝ}
    (hr : 1 / 2 < r) (hcs : c ^ 2 + s ^ 2 = 1)
    (ho1 : 0 ≤ cross2 (fig14Pt ⟨0, by decide⟩).1 (fig14Pt ⟨0, by decide⟩).2
                      (fig14Pt ⟨1, by decide⟩).1 (fig14Pt ⟨1, by decide⟩).2 x y)
    (ho2 : 0 ≤ cross2 (fig14Pt ⟨1, by decide⟩).1 (fig14Pt ⟨1, by decide⟩).2
                      (fig14Pt ⟨3, by decide⟩).1 (fig14Pt ⟨3, by decide⟩).2 x y)
    (ho3 : 0 ≤ cross2 (fig14Pt ⟨3, by decide⟩).1 (fig14Pt ⟨3, by decide⟩).2
                      (fig14Pt ⟨4, by decide⟩).1 (fig14Pt ⟨4, by decide⟩).2 x y)
    (ho4 : 0 ≤ cross2 (fig14Pt ⟨4, by decide⟩).1 (fig14Pt ⟨4, by decide⟩).2
                      (fig14Pt ⟨5, by decide⟩).1 (fig14Pt ⟨5, by decide⟩).2 x y)
    (ho5 : 0 ≤ cross2 (fig14Pt ⟨5, by decide⟩).1 (fig14Pt ⟨5, by decide⟩).2
                      (fig14Pt ⟨6, by decide⟩).1 (fig14Pt ⟨6, by decide⟩).2 x y)
    (ho6 : 0 ≤ cross2 (fig14Pt ⟨6, by decide⟩).1 (fig14Pt ⟨6, by decide⟩).2
                      (fig14Pt ⟨7, by decide⟩).1 (fig14Pt ⟨7, by decide⟩).2 x y)
    (ho7 : 0 ≤ cross2 (fig14Pt ⟨7, by decide⟩).1 (fig14Pt ⟨7, by decide⟩).2
                      (fig14Pt ⟨8, by decide⟩).1 (fig14Pt ⟨8, by decide⟩).2 x y)
    (ho8 : 0 ≤ cross2 (fig14Pt ⟨8, by decide⟩).1 (fig14Pt ⟨8, by decide⟩).2
                      (fig14Pt ⟨0, by decide⟩).1 (fig14Pt ⟨0, by decide⟩).2 x y) :
    ∃ k : Fin 12, boxInside r x y c s (fig14Pt k).1 (fig14Pt k).2 := by
  simp only [fig14Pt, cross2] at ho1 ho2 ho3 ho4 ho5 ho6 ho7 ho8
  by_cases hHI : (21 / 10 : ℝ) ≤ y
  · exact fig14_interior_north hr hcs hHI ho4 ho5 ho6 ho7
  · push Not at hHI
    by_cases hJI : x ≤ (21 / 10 : ℝ)
    · exact fig14_interior_sw hr hcs hHI hJI ho1 ho2 ho7 ho8
    · push Not at hJI
      exact fig14_interior_east hr hcs hHI hJI ho2 ho3 ho4

private lemma fig14_octagon_of_not_boundary {x y : ℝ}
    (hc1 : ¬ (x ≤ 1 ∧ y ≤ 9 / 10))
    (hc2 : ¬ (1 + 2 * a0 ≤ x ∧ y ≤ 1))
    (hc3 : ¬ (1 + 2 * a0 ≤ x ∧ 1 + 2 * a0 ≤ y))
    (hc4 : ¬ (x ≤ 1 ∧ 1 + 2 * a0 ≤ y))
    (hq1 : ¬ (1 ≤ x ∧ x ≤ 1 + a0 ∧ y ≤ 9 / 10))
    (hq2 : ¬ (1 + a0 ≤ x ∧ x ≤ 1 + 2 * a0 ∧
      cross2 (fig14Pt ⟨1, by decide⟩).1 (fig14Pt ⟨1, by decide⟩).2
             (fig14Pt ⟨3, by decide⟩).1 (fig14Pt ⟨3, by decide⟩).2 x y ≤ 0))
    (hq3 : ¬ (1 ≤ y ∧ y ≤ 1 + a0 ∧
      cross2 (fig14Pt ⟨3, by decide⟩).1 (fig14Pt ⟨3, by decide⟩).2
             (fig14Pt ⟨4, by decide⟩).1 (fig14Pt ⟨4, by decide⟩).2 x y ≤ 0))
    (hq4 : ¬ (1 + a0 ≤ y ∧ y ≤ 1 + 2 * a0 ∧
      cross2 (fig14Pt ⟨4, by decide⟩).1 (fig14Pt ⟨4, by decide⟩).2
             (fig14Pt ⟨5, by decide⟩).1 (fig14Pt ⟨5, by decide⟩).2 x y ≤ 0))
    (hq5 : ¬ (1 + a0 ≤ x ∧ x ≤ 1 + 2 * a0 ∧
      cross2 (fig14Pt ⟨5, by decide⟩).1 (fig14Pt ⟨5, by decide⟩).2
             (fig14Pt ⟨6, by decide⟩).1 (fig14Pt ⟨6, by decide⟩).2 x y ≤ 0))
    (hq6 : ¬ (1 ≤ x ∧ x ≤ 1 + a0 ∧
      cross2 (fig14Pt ⟨6, by decide⟩).1 (fig14Pt ⟨6, by decide⟩).2
             (fig14Pt ⟨7, by decide⟩).1 (fig14Pt ⟨7, by decide⟩).2 x y ≤ 0))
    (hq7 : ¬ (46 / 25 ≤ y ∧ y ≤ 1 + 2 * a0 ∧
      cross2 (fig14Pt ⟨7, by decide⟩).1 (fig14Pt ⟨7, by decide⟩).2
             (fig14Pt ⟨8, by decide⟩).1 (fig14Pt ⟨8, by decide⟩).2 x y ≤ 0))
    (hq8 : ¬ (9 / 10 ≤ y ∧ y ≤ 46 / 25 ∧
      cross2 (fig14Pt ⟨8, by decide⟩).1 (fig14Pt ⟨8, by decide⟩).2
             (fig14Pt ⟨0, by decide⟩).1 (fig14Pt ⟨0, by decide⟩).2 x y ≤ 0)) :
    0 ≤ cross2 (fig14Pt ⟨0, by decide⟩).1 (fig14Pt ⟨0, by decide⟩).2
               (fig14Pt ⟨1, by decide⟩).1 (fig14Pt ⟨1, by decide⟩).2 x y ∧
    0 ≤ cross2 (fig14Pt ⟨1, by decide⟩).1 (fig14Pt ⟨1, by decide⟩).2
               (fig14Pt ⟨3, by decide⟩).1 (fig14Pt ⟨3, by decide⟩).2 x y ∧
    0 ≤ cross2 (fig14Pt ⟨3, by decide⟩).1 (fig14Pt ⟨3, by decide⟩).2
               (fig14Pt ⟨4, by decide⟩).1 (fig14Pt ⟨4, by decide⟩).2 x y ∧
    0 ≤ cross2 (fig14Pt ⟨4, by decide⟩).1 (fig14Pt ⟨4, by decide⟩).2
               (fig14Pt ⟨5, by decide⟩).1 (fig14Pt ⟨5, by decide⟩).2 x y ∧
    0 ≤ cross2 (fig14Pt ⟨5, by decide⟩).1 (fig14Pt ⟨5, by decide⟩).2
               (fig14Pt ⟨6, by decide⟩).1 (fig14Pt ⟨6, by decide⟩).2 x y ∧
    0 ≤ cross2 (fig14Pt ⟨6, by decide⟩).1 (fig14Pt ⟨6, by decide⟩).2
               (fig14Pt ⟨7, by decide⟩).1 (fig14Pt ⟨7, by decide⟩).2 x y ∧
    0 ≤ cross2 (fig14Pt ⟨7, by decide⟩).1 (fig14Pt ⟨7, by decide⟩).2
               (fig14Pt ⟨8, by decide⟩).1 (fig14Pt ⟨8, by decide⟩).2 x y ∧
    0 ≤ cross2 (fig14Pt ⟨8, by decide⟩).1 (fig14Pt ⟨8, by decide⟩).2
               (fig14Pt ⟨0, by decide⟩).1 (fig14Pt ⟨0, by decide⟩).2 x y := by
  have ha_sq := a0_sq
  have ha_pos := a0_pos
  have ha_lb := a0_lb
  have ha_ub := a0_ub_tight
  simp only [fig14Pt, cross2] at hq2 hq3 hq4 hq5 hq6 hq7 hq8 ⊢
  have hy_gt9 : (9 / 10 : ℝ) < y := by
    by_contra hle; push Not at hle
    by_cases h1 : x ≤ 1
    · exact hc1 ⟨h1, hle⟩
    · by_cases h2 : x ≤ 1 + a0
      · exact hq1 ⟨by linarith only [h1], h2, hle⟩
      · by_cases h3 : x ≤ 1 + 2 * a0
        · exact hq2 ⟨by linarith only [h2], h3, by nlinarith only [ha_pos, hle, h2]⟩
        · exact hc2 ⟨by linarith only [h3], by linarith only [hle]⟩
  have hx_gt78 : (39 / 50 : ℝ) < x := by
    by_contra hle; push Not at hle
    by_cases h1 : y ≤ 46 / 25
    · exact hq8 ⟨by linarith only [hy_gt9], h1, by linarith only [hy_gt9, h1, hle]⟩
    · by_cases h2 : y ≤ 1 + 2 * a0
      · exact hq7 ⟨by linarith only [h1], h2, by nlinarith only [ha_lb, h1, h2, hle]⟩
      · exact hc4 ⟨by linarith only [hle], by linarith only [h2]⟩
  have hx_ltC : x < 11 / 10 + 2 * a0 := by
    by_contra hge; push Not at hge
    by_cases h1 : y ≤ 1
    · exact hc2 ⟨by linarith only [hge], h1⟩
    · by_cases h2 : y ≤ 1 + a0
      · exact hq3 ⟨by linarith only [h1], h2, by nlinarith only [ha_pos, h1, h2, hge]⟩
      · by_cases h3 : y ≤ 1 + 2 * a0
        · exact hq4 ⟨by linarith only [h2], h3, by nlinarith only [ha_pos, h2, h3, hge]⟩
        · exact hc3 ⟨by linarith only [hge], by linarith only [h3]⟩
  have hy_ltE : y < 11 / 10 + 2 * a0 := by
    by_contra hge; push Not at hge
    by_cases h1 : x ≤ 1
    · exact hc4 ⟨h1, by linarith only [hge]⟩
    · by_cases h2 : x ≤ 1 + a0
      · exact hq6 ⟨by linarith only [h1], h2, by nlinarith only [ha_pos, h1, h2, hge]⟩
      · by_cases h3 : x ≤ 1 + 2 * a0
        · exact hq5 ⟨by linarith only [h2], h3, by nlinarith only [ha_pos, h2, h3, hge]⟩
        · exact hc3 ⟨by linarith only [h3], by linarith only [hge]⟩
  refine ⟨by nlinarith only [ha_pos, hy_gt9], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_contra hneg; push Not at hneg
    have hx_gt : 1 + a0 < x := by nlinarith only [ha_pos, hy_gt9, hneg]
    by_cases hx_le : x ≤ 1 + 2 * a0
    · exact hq2 ⟨by linarith only [hx_gt], hx_le, by linarith only [hneg]⟩
    · push Not at hx_le
      by_cases hy_le : y ≤ 1
      · exact hc2 ⟨by linarith only [hx_le], hy_le⟩
      · push Not at hy_le
        exact hq3 ⟨by linarith only [hy_le], by nlinarith only [ha_lb, hx_ltC, hneg],
                   by nlinarith only [ha_pos, ha_sq, hx_le, hy_le, hneg]⟩
  · by_contra hneg; push Not at hneg
    have hy_lt : y < 1 + a0 := by nlinarith only [ha_pos, hx_ltC, hneg]
    by_cases hy_ge : 1 ≤ y
    · exact hq3 ⟨hy_ge, by linarith only [hy_lt], by linarith only [hneg]⟩
    · push Not at hy_ge
      by_cases hx_ge : 1 + 2 * a0 ≤ x
      · exact hc2 ⟨hx_ge, by linarith only [hy_ge]⟩
      · push Not at hx_ge
        exact hq2 ⟨by nlinarith only [ha_lb, hy_gt9, hneg], by linarith only [hx_ge],
                   by nlinarith only [ha_pos, ha_sq, hy_ge, hx_ge, hneg]⟩
  · by_contra hneg; push Not at hneg
    have hy_gt : 1 + a0 < y := by nlinarith only [ha_pos, hx_ltC, hneg]
    by_cases hy_le : y ≤ 1 + 2 * a0
    · exact hq4 ⟨by linarith only [hy_gt], hy_le, by linarith only [hneg]⟩
    · push Not at hy_le
      by_cases hx_ge : 1 + 2 * a0 ≤ x
      · exact hc3 ⟨hx_ge, by linarith only [hy_le]⟩
      · push Not at hx_ge
        exact hq5 ⟨by nlinarith only [ha_lb, hy_ltE, hneg], by linarith only [hx_ge],
                   by nlinarith only [ha_pos, ha_sq, hy_le, hx_ge, hneg]⟩
  · by_contra hneg; push Not at hneg
    have hx_gt : 1 + a0 < x := by nlinarith only [ha_pos, hy_ltE, hneg]
    by_cases hx_le : x ≤ 1 + 2 * a0
    · exact hq5 ⟨by linarith only [hx_gt], hx_le, by linarith only [hneg]⟩
    · push Not at hx_le
      by_cases hy_ge : 1 + 2 * a0 ≤ y
      · exact hc3 ⟨by linarith only [hx_le], hy_ge⟩
      · push Not at hy_ge
        exact hq4 ⟨by nlinarith only [ha_lb, hx_ltC, hneg], by linarith only [hy_ge],
                   by nlinarith only [ha_pos, ha_sq, hx_le, hy_ge, hneg]⟩
  · by_contra hneg; push Not at hneg
    have hx_lt : x < 1 + a0 := by nlinarith only [ha_pos, hy_ltE, hneg]
    by_cases hx_ge : 1 ≤ x
    · exact hq6 ⟨hx_ge, by linarith only [hx_lt], by linarith only [hneg]⟩
    · by_cases hy_ge : 1 + 2 * a0 ≤ y
      · exact hc4 ⟨by linarith only [hx_ge], hy_ge⟩
      · exact hq7 ⟨by nlinarith only [ha_lb, hx_gt78, hneg], by linarith only [hy_ge],
                   by nlinarith only [ha_sq, ha_lb, hx_ge, hy_ge, hneg]⟩
  · by_contra hneg; push Not at hneg
    have hy_gt : 46 / 25 < y := by nlinarith only [ha_lb, hx_gt78, hneg]
    by_cases hy_le : y ≤ 1 + 2 * a0
    · exact hq7 ⟨by linarith only [hy_gt], hy_le, by linarith only [hneg]⟩
    · by_cases hx_le : x ≤ 1
      · exact hc4 ⟨hx_le, by linarith only [hy_le]⟩
      · exact hq6 ⟨by linarith only [hx_le], by nlinarith only [ha_lb, hy_ltE, hneg],
                   by nlinarith only [ha_sq, ha_lb, hy_le, hx_le, hneg]⟩
  · by_contra hneg; push Not at hneg
    have hy_lt : y < 46 / 25 := by linarith only [hx_gt78, hneg]
    exact hq8 ⟨by linarith only [hy_gt9], by linarith only [hy_lt], by linarith only [hneg]⟩

private lemma fig14_cover {r x y c s : ℝ} (hv : ValidBox r x y c s) :
    ∃ k : Fin 12, boxInside r x y c s (fig14Pt k).1 (fig14Pt k).2 := by
  have ha_sq := a0_sq
  have ha_pos := a0_pos
  have ha_lb := a0_lb
  have ha_ub := a0_ub
  rcases hv with ⟨hr, hc, hs, hcs, hx1, hx2, hy1, hy2⟩
  -- 4 Corner rectangles
  by_cases hc1 : x ≤ 1 ∧ y ≤ 9 / 10
  · refine ⟨⟨0, by decide⟩, ?_⟩
    simpa [fig14Pt] using lemma1_corner hr hc hs hcs hx1 hc1.1 (le_refl 1) hy1 hc1.2 (by norm_num)
  by_cases hc2 : 1 + 2 * a0 ≤ x ∧ y ≤ 1
  · refine ⟨⟨3, by decide⟩, ?_⟩
    have h1 := lemma1_corner hr hs hc (by linarith only [hcs])
      (by linarith only [hx2] : r * (s + c) ≤ L0 - x)
      (by unfold L0; linarith only [hc2.1] : L0 - x ≤ 1) (le_refl 1)
      (by linarith only [hy1] : r * (s + c) ≤ y) hc2.2 (le_refl 1)
    have heq := boxInside_reflectX r x y c s (1 + 2 * a0) 1 L0
    rw [show L0 - (1 + 2 * a0) = 1 by unfold L0; ring] at heq
    simpa [fig14Pt] using heq.mp h1
  by_cases hc3 : 1 + 2 * a0 ≤ x ∧ 1 + 2 * a0 ≤ y
  · refine ⟨⟨5, by decide⟩, ?_⟩
    have h1 := lemma1_corner hr hc hs hcs hx2
      (by unfold L0; linarith only [hc3.1] : L0 - x ≤ 1) (le_refl 1)
      hy2 (by unfold L0; linarith only [hc3.2] : L0 - y ≤ 1) (le_refl 1)
    have heq := boxInside_rot180 r x y c s (1 + 2 * a0) (1 + 2 * a0) L0 L0
    rw [show L0 - (1 + 2 * a0) = 1 by unfold L0; ring] at heq
    simpa [fig14Pt] using heq.mp h1
  by_cases hc4 : x ≤ 1 ∧ 1 + 2 * a0 ≤ y
  · refine ⟨⟨7, by decide⟩, ?_⟩
    have h1 := lemma1_corner hr hs hc (by linarith only [hcs])
      (by linarith only [hx1] : r * (s + c) ≤ x) hc4.1 (le_refl 1)
      (by linarith only [hy2] : r * (s + c) ≤ L0 - y)
      (by unfold L0; linarith only [hc4.2] : L0 - y ≤ 1) (le_refl 1)
    have heq := boxInside_reflectY r x y c s 1 (1 + 2 * a0) L0
    rw [show L0 - (1 + 2 * a0) = 1 by unfold L0; ring] at heq
    simpa [fig14Pt] using heq.mp h1
  -- Q1: Bottom A1-A2
  by_cases hq1 : 1 ≤ x ∧ x ≤ 1 + a0 ∧ y ≤ 9 / 10
  · have h3 := lemma3_rect hr hc hs hcs (x := x - 1) (y := y) (w := a0) (h := 9 / 10)
      (by linarith only [hq1.1]) (by linarith only [hq1.2.1]) (by linarith only [ha_ub])
      hy1 hq1.2.2 (le_refl _)
    rcases h3 with h3 | h3
    · refine ⟨⟨0, by decide⟩, ?_⟩
      have heq := boxInside_translate r x y c s 1 (9 / 10) (-1) 0
      rw [show x + -1 = x - 1 by ring, show y + 0 = y by ring,
        show (1 : ℝ) + -1 = 0 by ring, show (9 / 10 : ℝ) + 0 = 9 / 10 by ring] at heq
      simpa [fig14Pt] using heq.mp h3
    · refine ⟨⟨1, by decide⟩, ?_⟩
      have heq := boxInside_translate r x y c s (1 + a0) (9 / 10) (-1) 0
      rw [show x + -1 = x - 1 by ring, show y + 0 = y by ring,
        show 1 + a0 + -1 = a0 by ring, show (9 / 10 : ℝ) + 0 = 9 / 10 by ring] at heq
      simpa [fig14Pt] using heq.mp h3
  -- Q2: Bottom A2-B
  by_cases hq2 : 1 + a0 ≤ x ∧ x ≤ 1 + 2 * a0 ∧
      cross2 (fig14Pt ⟨1, by decide⟩).1 (fig14Pt ⟨1, by decide⟩).2
             (fig14Pt ⟨3, by decide⟩).1 (fig14Pt ⟨3, by decide⟩).2 x y ≤ 0
  · have htop : (1 - 9 / 10 : ℝ) * (1 + 2 * a0 - x) + a0 * y ≤ a0 := by
      simp only [fig14Pt, cross2] at hq2; linarith only [hq2.2.2]
    have hy_le : y ≤ 1 := by nlinarith only [ha_pos, hq2.2.1, htop]
    have h4 := lemma4_quad (x := 1 + 2 * a0 - x) (y := y) (c := s) (s := c)
      (w := a0) (b := 9 / 10) hr hs hc (by linarith only [hcs]) ha_pos (by linarith only [ha_ub])
      (by norm_num) (by norm_num) (by nlinarith only [ha_sq])
      (lemma4_poly_a hs hc (by linarith only [hcs]) ha_ub (le_refl _))
      (by linarith only [hq2.2.1]) (by linarith only [hq2.1]) (by linarith only [hy1]) hy_le htop
    rcases h4 with h4 | h4
    · refine ⟨⟨3, by decide⟩, ?_⟩
      have heq := boxInside_reflectX r x y c s (1 + 2 * a0) 1 (1 + 2 * a0)
      rw [show 1 + 2 * a0 - (1 + 2 * a0) = 0 by ring] at heq
      simpa [fig14Pt] using heq.mp h4
    · refine ⟨⟨1, by decide⟩, ?_⟩
      have heq := boxInside_reflectX r x y c s (1 + a0) (9 / 10) (1 + 2 * a0)
      rw [show 1 + 2 * a0 - (1 + a0) = a0 by ring] at heq
      simpa [fig14Pt] using heq.mp h4
  -- Q3: Right B-C
  by_cases hq3 : 1 ≤ y ∧ y ≤ 1 + a0 ∧
      cross2 (fig14Pt ⟨3, by decide⟩).1 (fig14Pt ⟨3, by decide⟩).2
             (fig14Pt ⟨4, by decide⟩).1 (fig14Pt ⟨4, by decide⟩).2 x y ≤ 0
  · have htop : (1 - 9 / 10 : ℝ) * (y - 1) + a0 * (L0 - x) ≤ a0 := by
      simp only [fig14Pt, cross2] at hq3; unfold L0; linarith only [hq3.2.2]
    have hx_le : L0 - x ≤ 1 := by nlinarith only [ha_pos, hq3.1, htop]
    have h4 := lemma4_quad (x := y - 1) (y := L0 - x) (c := c) (s := s)
      (w := a0) (b := 9 / 10) hr hc hs hcs ha_pos (by linarith only [ha_ub])
      (by norm_num) (by norm_num) (by nlinarith only [ha_sq])
      (lemma4_poly_a hc hs hcs ha_ub (le_refl _))
      (by linarith only [hq3.1]) (by linarith only [hq3.2.1]) hx2 hx_le htop
    rcases h4 with h4 | h4
    · refine ⟨⟨3, by decide⟩, ?_⟩
      have heq := boxInside_rot90 r x y c s (1 + 2 * a0) 1 L0 1
      rw [show (1 : ℝ) - 1 = 0 by ring, show L0 - (1 + 2 * a0) = 1 by unfold L0; ring] at heq
      simpa [fig14Pt] using heq.mp h4
    · refine ⟨⟨4, by decide⟩, ?_⟩
      have heq := boxInside_rot90 r x y c s (11 / 10 + 2 * a0) (1 + a0) L0 1
      rw [show 1 + a0 - 1 = a0 by ring, show L0 - (11 / 10 + 2 * a0) = 9 / 10 by unfold L0; ring] at heq
      simpa [fig14Pt] using heq.mp h4
  -- Q4: Right C-D
  by_cases hq4 : 1 + a0 ≤ y ∧ y ≤ 1 + 2 * a0 ∧
      cross2 (fig14Pt ⟨4, by decide⟩).1 (fig14Pt ⟨4, by decide⟩).2
             (fig14Pt ⟨5, by decide⟩).1 (fig14Pt ⟨5, by decide⟩).2 x y ≤ 0
  · have htop : (1 - 9 / 10 : ℝ) * (1 + 2 * a0 - y) + a0 * (L0 - x) ≤ a0 := by
      simp only [fig14Pt, cross2] at hq4; unfold L0; linarith only [hq4.2.2]
    have hx_le : L0 - x ≤ 1 := by nlinarith only [ha_pos, hq4.2.1, htop]
    have h4 := lemma4_quad (x := 1 + 2 * a0 - y) (y := L0 - x) (c := s) (s := c)
      (w := a0) (b := 9 / 10) hr hs hc (by linarith only [hcs]) ha_pos (by linarith only [ha_ub])
      (by norm_num) (by norm_num) (by nlinarith only [ha_sq])
      (lemma4_poly_a hs hc (by linarith only [hcs]) ha_ub (le_refl _))
      (by linarith only [hq4.2.1]) (by linarith only [hq4.1]) (by linarith only [hx2]) hx_le htop
    rcases h4 with h4 | h4
    · refine ⟨⟨5, by decide⟩, ?_⟩
      have heq := (boxInside_swap r x y c s (1 + 2 * a0) (1 + 2 * a0)).symm.trans
        ((boxInside_rot180 r y x s c (1 + 2 * a0) (1 + 2 * a0) (1 + 2 * a0) L0).symm)
      rw [show 1 + 2 * a0 - (1 + 2 * a0) = 0 by ring,
        show L0 - (1 + 2 * a0) = 1 by unfold L0; ring] at heq
      simpa [fig14Pt] using heq.mpr h4
    · refine ⟨⟨4, by decide⟩, ?_⟩
      have heq := (boxInside_swap r x y c s (11 / 10 + 2 * a0) (1 + a0)).symm.trans
        ((boxInside_rot180 r y x s c (1 + a0) (11 / 10 + 2 * a0) (1 + 2 * a0) L0).symm)
      rw [show 1 + 2 * a0 - (1 + a0) = a0 by ring,
        show L0 - (11 / 10 + 2 * a0) = 9 / 10 by unfold L0; ring] at heq
      simpa [fig14Pt] using heq.mpr h4
  -- Q5: Top D-E
  by_cases hq5 : 1 + a0 ≤ x ∧ x ≤ 1 + 2 * a0 ∧
      cross2 (fig14Pt ⟨5, by decide⟩).1 (fig14Pt ⟨5, by decide⟩).2
             (fig14Pt ⟨6, by decide⟩).1 (fig14Pt ⟨6, by decide⟩).2 x y ≤ 0
  · have htop : (1 - 9 / 10 : ℝ) * (1 + 2 * a0 - x) + a0 * (L0 - y) ≤ a0 := by
      simp only [fig14Pt, cross2] at hq5; unfold L0; linarith only [hq5.2.2]
    have hy_le : L0 - y ≤ 1 := by nlinarith only [ha_pos, hq5.2.1, htop]
    have h4 := lemma4_quad (x := 1 + 2 * a0 - x) (y := L0 - y) (c := c) (s := s)
      (w := a0) (b := 9 / 10) hr hc hs hcs ha_pos (by linarith only [ha_ub])
      (by norm_num) (by norm_num) (by nlinarith only [ha_sq])
      (lemma4_poly_a hc hs hcs ha_ub (le_refl _))
      (by linarith only [hq5.2.1]) (by linarith only [hq5.1]) hy2 hy_le htop
    rcases h4 with h4 | h4
    · refine ⟨⟨5, by decide⟩, ?_⟩
      have heq := boxInside_rot180 r x y c s (1 + 2 * a0) (1 + 2 * a0) (1 + 2 * a0) L0
      rw [show 1 + 2 * a0 - (1 + 2 * a0) = 0 by ring,
        show L0 - (1 + 2 * a0) = 1 by unfold L0; ring] at heq
      simpa [fig14Pt] using heq.mp h4
    · refine ⟨⟨6, by decide⟩, ?_⟩
      have heq := boxInside_rot180 r x y c s (1 + a0) (11 / 10 + 2 * a0) (1 + 2 * a0) L0
      rw [show 1 + 2 * a0 - (1 + a0) = a0 by ring,
        show L0 - (11 / 10 + 2 * a0) = 9 / 10 by unfold L0; ring] at heq
      simpa [fig14Pt] using heq.mp h4
  -- Q6: Top E-F
  by_cases hq6 : 1 ≤ x ∧ x ≤ 1 + a0 ∧
      cross2 (fig14Pt ⟨6, by decide⟩).1 (fig14Pt ⟨6, by decide⟩).2
             (fig14Pt ⟨7, by decide⟩).1 (fig14Pt ⟨7, by decide⟩).2 x y ≤ 0
  · have htop : (1 - 9 / 10 : ℝ) * (x - 1) + a0 * (L0 - y) ≤ a0 := by
      simp only [fig14Pt, cross2] at hq6; unfold L0; linarith only [hq6.2.2]
    have hy_le : L0 - y ≤ 1 := by nlinarith only [ha_pos, hq6.1, htop]
    have h4 := lemma4_quad (x := x - 1) (y := L0 - y) (c := s) (s := c)
      (w := a0) (b := 9 / 10) hr hs hc (by linarith only [hcs]) ha_pos (by linarith only [ha_ub])
      (by norm_num) (by norm_num) (by nlinarith only [ha_sq])
      (lemma4_poly_a hs hc (by linarith only [hcs]) ha_ub (le_refl _))
      (by linarith only [hq6.1]) (by linarith only [hq6.2.1]) (by linarith only [hy2]) hy_le htop
    rcases h4 with h4 | h4
    · refine ⟨⟨7, by decide⟩, ?_⟩
      have heq := (boxInside_reflectY r x y c s 1 (1 + 2 * a0) L0).symm.trans
        ((boxInside_translate r x (L0 - y) s c 1 (L0 - (1 + 2 * a0)) (-1) 0).symm)
      rw [show x + -1 = x - 1 by ring, show L0 - y + 0 = L0 - y by ring,
        show (1 : ℝ) + -1 = 0 by ring, show L0 - (1 + 2 * a0) + 0 = 1 by unfold L0; ring] at heq
      simpa [fig14Pt] using heq.mpr h4
    · refine ⟨⟨6, by decide⟩, ?_⟩
      have heq := (boxInside_reflectY r x y c s (1 + a0) (11 / 10 + 2 * a0) L0).symm.trans
        ((boxInside_translate r x (L0 - y) s c (1 + a0) (L0 - (11 / 10 + 2 * a0)) (-1) 0).symm)
      rw [show x + -1 = x - 1 by ring, show L0 - y + 0 = L0 - y by ring,
        show 1 + a0 + -1 = a0 by ring,
        show L0 - (11 / 10 + 2 * a0) + 0 = 9 / 10 by unfold L0; ring] at heq
      simpa [fig14Pt] using heq.mpr h4
  -- Q7: Left F-G
  by_cases hq7 : 46 / 25 ≤ y ∧ y ≤ 1 + 2 * a0 ∧
      cross2 (fig14Pt ⟨7, by decide⟩).1 (fig14Pt ⟨7, by decide⟩).2
             (fig14Pt ⟨8, by decide⟩).1 (fig14Pt ⟨8, by decide⟩).2 x y ≤ 0
  · set wFG := 2 * a0 - 21 / 25
    have hw_pos : 0 < wFG := by simp only [wFG]; linarith only [ha_lb]
    have hw_ub : wFG ≤ 19 / 20 := by simp only [wFG]; linarith only [ha_ub]
    have htop : (1 - 39 / 50 : ℝ) * (1 + 2 * a0 - y) + wFG * x ≤ wFG := by
      simp only [fig14Pt, cross2] at hq7; simp only [wFG]; linarith only [hq7.2.2]
    have hx_le : x ≤ 1 := by nlinarith only [hw_pos, hq7.2.1, htop]
    have h4 := lemma4_quad (x := 1 + 2 * a0 - y) (y := x) (c := c) (s := s)
      (w := wFG) (b := 39 / 50) hr hc hs hcs hw_pos (by linarith only [hw_ub])
      (by norm_num) (by norm_num) (by nlinarith only [hw_pos, hw_ub])
      (lemma4_poly_95 hc hs hcs hw_ub (le_refl _))
      (by linarith only [hq7.2.1]) (by simp only [wFG]; linarith only [hq7.1]) hx1 hx_le htop
    rcases h4 with h4 | h4
    · refine ⟨⟨7, by decide⟩, ?_⟩
      have heq := boxInside_rot270 r x y c s 1 (1 + 2 * a0) (1 + 2 * a0)
      rw [show 1 + 2 * a0 - (1 + 2 * a0) = 0 by ring] at heq
      simpa [fig14Pt] using heq.mp h4
    · refine ⟨⟨8, by decide⟩, ?_⟩
      have heq := boxInside_rot270 r x y c s (39 / 50) (46 / 25) (1 + 2 * a0)
      rw [show 1 + 2 * a0 - 46 / 25 = wFG by simp only [wFG]; ring] at heq
      simpa [fig14Pt] using heq.mp h4
  -- Q8: Left G-A1
  by_cases hq8 : 9 / 10 ≤ y ∧ y ≤ 46 / 25 ∧
      cross2 (fig14Pt ⟨8, by decide⟩).1 (fig14Pt ⟨8, by decide⟩).2
             (fig14Pt ⟨0, by decide⟩).1 (fig14Pt ⟨0, by decide⟩).2 x y ≤ 0
  · have htop : (1 - 39 / 50 : ℝ) * (y - 9 / 10) + (47 / 50 : ℝ) * x ≤ 47 / 50 := by
      simp only [fig14Pt, cross2] at hq8; linarith only [hq8.2.2]
    have hx_le : x ≤ 1 := by linarith only [hq8.1, htop]
    have h4 := lemma4_quad (x := y - 9 / 10) (y := x) (c := s) (s := c)
      (w := 47 / 50) (b := 39 / 50) hr hs hc (by linarith only [hcs]) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (lemma4_poly_95 hs hc (by linarith only [hcs]) (by norm_num) (le_refl _))
      (by linarith only [hq8.1]) (by linarith only [hq8.2.1]) (by linarith only [hx1]) hx_le htop
    rcases h4 with h4 | h4
    · refine ⟨⟨0, by decide⟩, ?_⟩
      have heq := (boxInside_swap r x y c s 1 (9 / 10)).symm.trans
        ((boxInside_translate r y x s c (9 / 10) 1 (-9 / 10) 0).symm)
      rw [show y + -9 / 10 = y - 9 / 10 by ring, show x + 0 = x by ring,
        show (9 / 10 : ℝ) + -9 / 10 = 0 by ring, show (1 : ℝ) + 0 = 1 by ring] at heq
      simpa [fig14Pt] using heq.mpr h4
    · refine ⟨⟨8, by decide⟩, ?_⟩
      have heq := (boxInside_swap r x y c s (39 / 50) (46 / 25)).symm.trans
        ((boxInside_translate r y x s c (46 / 25) (39 / 50) (-9 / 10) 0).symm)
      rw [show y + -9 / 10 = y - 9 / 10 by ring, show x + 0 = x by ring,
        show (46 / 25 : ℝ) + -9 / 10 = 47 / 50 by ring,
        show (39 / 50 : ℝ) + 0 = 39 / 50 by ring] at heq
      simpa [fig14Pt] using heq.mpr h4
  -- Interior of convex octagon
  rcases fig14_octagon_of_not_boundary hc1 hc2 hc3 hc4 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 with
    ⟨ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8⟩
  exact fig14_interior hr hcs ho1 ho2 ho3 ho4 ho5 ho6 ho7 ho8

/-! ### Section 5: Scaling, Quadrant Normalization, Reflection, and Pigeonhole Closure -/

private lemma normalize_quadrant (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ∃ c s : ℝ, 0 ≤ c ∧ 0 ≤ s ∧ c ^ 2 + s ^ 2 = 1 ∧ c + s = |a| + |b| ∧
      ∀ r x y X Y : ℝ, boxInside r x y c s X Y ↔ boxInside r x y a b X Y := by
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · refine ⟨a, b, ha, hb, hab, ?_, fun _ _ _ _ _ => Iff.rfl⟩
      rw [abs_of_nonneg ha, abs_of_nonneg hb]
    · push Not at hb
      refine ⟨-b, a, by linarith only [hb], ha, by nlinarith only [hab], ?_, ?_⟩
      · rw [abs_of_nonneg ha, abs_of_neg hb]; ring
      · intro r x y X Y
        unfold boxInside
        have h2 : (-a) * (X - x) + (-b) * (Y - y) = -(a * (X - x) + b * (Y - y)) := by ring
        rw [h2, abs_neg, and_comm]
  · push Not at ha
    by_cases hb : 0 ≤ b
    · refine ⟨b, -a, hb, by linarith only [ha], by nlinarith only [hab], ?_, ?_⟩
      · rw [abs_of_neg ha, abs_of_nonneg hb]; ring
      · intro r x y X Y
        unfold boxInside
        have h1 : b * (X - x) + (-a) * (Y - y) = -((-b) * (X - x) + a * (Y - y)) := by ring
        have h2 : (-(-a)) * (X - x) + b * (Y - y) = a * (X - x) + b * (Y - y) := by ring
        rw [h1, h2, abs_neg, and_comm]
    · push Not at hb
      refine ⟨-a, -b, by linarith only [ha], by linarith only [hb], by nlinarith only [hab], ?_, ?_⟩
      · rw [abs_of_neg ha, abs_of_neg hb]
      · intro r x y X Y
        unfold boxInside
        have h1 : (-a) * (X - x) + (-b) * (Y - y) = -(a * (X - x) + b * (Y - y)) := by ring
        have h2 : (-(-b)) * (X - x) + (-a) * (Y - y) = -((-b) * (X - x) + a * (Y - y)) := by ring
        rw [h1, h2, abs_neg, abs_neg]

private lemma packing_contradiction (r : ℝ) (x y c s : Fin 11 → ℝ)
    (hvalid : ∀ i, ValidBox r (x i) (y i) (c i) (s i))
    (hdisj : ∀ i j, i ≠ j → ∀ X Y,
      boxInside r (x i) (y i) (c i) (s i) X Y → ¬ boxInside r (x j) (y j) (c j) (s j) X Y) :
    False := by
  have hex_i0 : ∃ i0 : Fin 11, ∀ k : Fin 10,
      ¬ boxInside r (x i0) (y i0) (c i0) (s i0) (fig13Pt k).1 (fig13Pt k).2 := by
    by_contra hall
    push Not at hall
    choose f hf using hall
    have hinj : Function.Injective f := by
      intro i j hij
      by_contra hne
      have hfj := hf j
      rw [← hij] at hfj
      exact hdisj i j hne (fig13Pt (f i)).1 (fig13Pt (f i)).2 (hf i) hfj
    have hcard := Fintype.card_le_of_injective f hinj
    simp at hcard
  rcases hex_i0 with ⟨i0, hi0⟩
  have hex_rx : ∃ x1 y1 c1 s1 : Fin 11 → ℝ,
      (∀ i, ValidBox r (x1 i) (y1 i) (c1 i) (s1 i)) ∧
      (∀ i j, i ≠ j → ∀ X Y,
        boxInside r (x1 i) (y1 i) (c1 i) (s1 i) X Y →
        ¬ boxInside r (x1 j) (y1 j) (c1 j) (s1 j) X Y) ∧
      x1 i0 ≤ 1 + a0 ∧
      (∀ k : Fin 10, ¬ boxInside r (x1 i0) (y1 i0) (c1 i0) (s1 i0) (fig13Pt k).1 (fig13Pt k).2) := by
    by_cases hxi : x i0 ≤ 1 + a0
    · exact ⟨x, y, c, s, hvalid, hdisj, hxi, hi0⟩
    · refine ⟨fun i => L0 - x i, y, s, c,
        fun i => validBox_reflectX (hvalid i), ?_, ?_, ?_⟩
      · intro i j hne X Y hbi hbj
        have h1 := (boxInside_reflectX r (x i) (y i) (c i) (s i) (L0 - X) Y L0).mp
          (by simpa [sub_sub_cancel] using hbi)
        have h2 := (boxInside_reflectX r (x j) (y j) (c j) (s j) (L0 - X) Y L0).mp
          (by simpa [sub_sub_cancel] using hbj)
        exact hdisj i j hne (L0 - X) Y h1 h2
      · unfold L0; linarith only [hxi]
      · intro k hk
        rcases fig13_reflectX k with ⟨j, hj⟩
        have h1 := (boxInside_reflectX r (x i0) (y i0) (c i0) (s i0)
          (L0 - (fig13Pt k).1) (fig13Pt k).2 L0).mp (by simpa [sub_sub_cancel] using hk)
        have hj1 : L0 - (fig13Pt k).1 = (fig13Pt j).1 := by simpa using congrArg Prod.fst hj
        have hj2 : (fig13Pt k).2 = (fig13Pt j).2 := by simpa using congrArg Prod.snd hj
        rw [hj1, hj2] at h1
        exact hi0 j h1
  rcases hex_rx with ⟨x1, y1, c1, s1, hv1, hd1, hx1_le, hi0_1⟩
  have hex_ry : ∃ x2 y2 c2 s2 : Fin 11 → ℝ,
      (∀ i, ValidBox r (x2 i) (y2 i) (c2 i) (s2 i)) ∧
      (∀ i j, i ≠ j → ∀ X Y,
        boxInside r (x2 i) (y2 i) (c2 i) (s2 i) X Y →
        ¬ boxInside r (x2 j) (y2 j) (c2 j) (s2 j) X Y) ∧
      x2 i0 ≤ 1 + a0 ∧ y2 i0 ≤ 1 + a0 ∧
      (∀ k : Fin 10, ¬ boxInside r (x2 i0) (y2 i0) (c2 i0) (s2 i0) (fig13Pt k).1 (fig13Pt k).2) := by
    by_cases hyi : y1 i0 ≤ 1 + a0
    · exact ⟨x1, y1, c1, s1, hv1, hd1, hx1_le, hyi, hi0_1⟩
    · refine ⟨x1, fun i => L0 - y1 i, s1, c1,
        fun i => validBox_reflectY (hv1 i), ?_, hx1_le, ?_, ?_⟩
      · intro i j hne X Y hbi hbj
        have h1 := (boxInside_reflectY r (x1 i) (y1 i) (c1 i) (s1 i) X (L0 - Y) L0).mp
          (by simpa [sub_sub_cancel] using hbi)
        have h2 := (boxInside_reflectY r (x1 j) (y1 j) (c1 j) (s1 j) X (L0 - Y) L0).mp
          (by simpa [sub_sub_cancel] using hbj)
        exact hd1 i j hne X (L0 - Y) h1 h2
      · unfold L0; linarith only [hyi]
      · intro k hk
        rcases fig13_reflectY k with ⟨j, hj⟩
        have h1 := (boxInside_reflectY r (x1 i0) (y1 i0) (c1 i0) (s1 i0)
          (fig13Pt k).1 (L0 - (fig13Pt k).2) L0).mp (by simpa [sub_sub_cancel] using hk)
        have hj1 : (fig13Pt k).1 = (fig13Pt j).1 := by simpa using congrArg Prod.fst hj
        have hj2 : L0 - (fig13Pt k).2 = (fig13Pt j).2 := by simpa using congrArg Prod.snd hj
        rw [hj1, hj2] at h1
        exact hi0_1 j h1
  rcases hex_ry with ⟨x2, y2, c2, s2, hv2, hd2, hx2_le, hy2_le, hi0_2⟩
  have hslot := fig13_quarter (hv2 i0) hx2_le hy2_le hi0_2
  have hA123 := box_in_slot_hits_A123 (hv2 i0) hslot.1 hx2_le hslot.2
    (hi0_2 ⟨0, by decide⟩) (hi0_2 ⟨1, by decide⟩)
  have hhit9 : ∀ i : {i : Fin 11 // i ≠ i0}, ∃ m : Fin 9,
      boxInside r (x2 i.1) (y2 i.1) (c2 i.1) (s2 i.1)
        (fig14Pt ⟨m.1 + 3, by omega⟩).1 (fig14Pt ⟨m.1 + 3, by omega⟩).2 := by
    intro ⟨i, hne⟩
    rcases fig14_cover (hv2 i) with ⟨k, hk⟩
    have hk0 : k.1 ≠ 0 := by
      intro h0
      have hk' : k = ⟨0, by decide⟩ := Fin.ext h0
      rw [hk'] at hk
      exact hd2 i0 i hne.symm 1 (9 / 10) hA123.1 hk
    have hk1 : k.1 ≠ 1 := by
      intro h1
      have hk' : k = ⟨1, by decide⟩ := Fin.ext h1
      rw [hk'] at hk
      exact hd2 i0 i hne.symm (1 + a0) (9 / 10) hA123.2.1 hk
    have hk2 : k.1 ≠ 2 := by
      intro h2
      have hk' : k = ⟨2, by decide⟩ := Fin.ext h2
      rw [hk'] at hk
      exact hd2 i0 i hne.symm (1 + a0 / 2) (28 / 25) hA123.2.2 hk
    refine ⟨⟨k.1 - 3, by omega⟩, ?_⟩
    have heq : (⟨k.1 - 3 + 3, by omega⟩ : Fin 12) = k := Fin.ext (by dsimp; omega)
    rw [heq]
    exact hk
  choose g hg using hhit9
  have hinj : Function.Injective g := by
    intro a b hab
    by_contra hne
    have hval : a.1 ≠ b.1 := fun h => hne (Subtype.ext h)
    have hgb := hg b
    rw [← hab] at hgb
    exact hd2 a.1 b.1 hval _ _ (hg a) hgb
  have hcard := Fintype.card_le_of_injective g hinj
  simp [Fintype.card_subtype_compl] at hcard

end PEqualNP.Outside.SquarePackingEleven

open PEqualNP.Outside.SquarePackingEleven in
theorem PEqualNP.Outside.L_square_packing_eleven_lower_bound :
    let inside := fun (x y a b X Y : ℝ) => |a*(X-x)+b*(Y-y)| < 1/2 ∧ |(-b)*(X-x)+a*(Y-y)| < 1/2;
    let fits := fun (n : ℕ) (s : ℝ) => 0 ≤ s ∧ ∃ x y a b : Fin n → ℝ, (∀ i, a i ^ 2 + b i ^ 2 = 1 ∧ |a i| + |b i| ≤ 2*x i ∧ |a i| + |b i| ≤ 2*(s-x i) ∧ |a i| + |b i| ≤ 2*y i ∧ |a i| + |b i| ≤ 2*(s-y i)) ∧ (∀ i j, i ≠ j → ∀ X Y : ℝ, inside (x i) (y i) (a i) (b i) X Y → ¬ inside (x j) (y j) (a j) (b j) X Y);
    ∀ s : ℝ, fits 11 s → 2 + 2*Real.sqrt (4/5) ≤ s := by
  intro inside fits s hfits
  by_contra hlt
  push Not at hlt
  rcases hfits with ⟨hs0, x, y, a, b, hbox, hdisj⟩
  have hs_pos : 0 < s := by
    have h0 := hbox ⟨0, by decide⟩
    have hnorm : 1 ≤ |a ⟨0, by decide⟩| + |b ⟨0, by decide⟩| := by
      have : (|a ⟨0, by decide⟩| + |b ⟨0, by decide⟩|) ^ 2 =
          a ⟨0, by decide⟩ ^ 2 + b ⟨0, by decide⟩ ^ 2 +
          2 * |a ⟨0, by decide⟩| * |b ⟨0, by decide⟩| := by
        have ha2 : |a ⟨0, by decide⟩| ^ 2 = a ⟨0, by decide⟩ ^ 2 := sq_abs _
        have hb2 : |b ⟨0, by decide⟩| ^ 2 = b ⟨0, by decide⟩ ^ 2 := sq_abs _
        nlinarith only [ha2, hb2]
      nlinarith only [this, h0.1, abs_nonneg (a ⟨0, by decide⟩), abs_nonneg (b ⟨0, by decide⟩)]
    linarith only [hnorm, h0.2.1, h0.2.2.1]
  have hnorm_quad : ∀ i : Fin 11,
      ∃ cs : ℝ × ℝ, 0 ≤ cs.1 ∧ 0 ≤ cs.2 ∧ cs.1 ^ 2 + cs.2 ^ 2 = 1 ∧
        cs.1 + cs.2 = |a i| + |b i| ∧
        ∀ r X Y, boxInside r (x i) (y i) cs.1 cs.2 X Y ↔ boxInside r (x i) (y i) (a i) (b i) X Y := by
    intro i
    rcases normalize_quadrant (a i) (b i) (hbox i).1 with ⟨c, s', hc, hs', hcs, hsum, hiff⟩
    exact ⟨(c, s'), hc, hs', hcs, hsum, fun r X Y => hiff r (x i) (y i) X Y⟩
  choose cs hcs_prop using hnorm_quad
  set lam := L0 / s
  have hL_eq : L0 = 2 + 2 * Real.sqrt (4 / 5) := rfl
  have hlam_gt : 1 < lam := by
    rw [show lam = L0 / s from rfl, one_lt_div hs_pos]
    rw [hL_eq]; exact hlt
  have hlam_pos : 0 < lam := by linarith only [hlam_gt]
  set r := lam / 2
  have hr : 1 / 2 < r := by simp only [r]; linarith only [hlam_gt]
  have hvalid : ∀ i : Fin 11, ValidBox r (lam * x i) (lam * y i) (cs i).1 (cs i).2 := by
    intro i
    rcases hbox i with ⟨_, hx1, hx2, hy1, hy2⟩
    rcases hcs_prop i with ⟨hc, hs', hcsq, hsum, _⟩
    have hlam_s : lam * s = L0 := div_mul_cancel₀ L0 hs_pos.ne'
    refine ⟨hr, hc, hs', hcsq, ?_, ?_, ?_, ?_⟩
    · have h1 : r * (|a i| + |b i|) ≤ r * (2 * x i) := by nlinarith only [hr, hx1]
      rw [← hsum] at h1
      have h2 : r * (2 * x i) = lam * x i := by simp only [r]; ring
      linarith only [h1, h2]
    · have h1 : r * (|a i| + |b i|) ≤ r * (2 * (s - x i)) := by nlinarith only [hr, hx2]
      rw [← hsum] at h1
      have h2 : r * (2 * (s - x i)) = L0 - lam * x i := by
        calc r * (2 * (s - x i)) = lam * s - lam * x i := by simp only [r]; ring
          _ = L0 - lam * x i := by rw [hlam_s]
      linarith only [h1, h2]
    · have h1 : r * (|a i| + |b i|) ≤ r * (2 * y i) := by nlinarith only [hr, hy1]
      rw [← hsum] at h1
      have h2 : r * (2 * y i) = lam * y i := by simp only [r]; ring
      linarith only [h1, h2]
    · have h1 : r * (|a i| + |b i|) ≤ r * (2 * (s - y i)) := by nlinarith only [hr, hy2]
      rw [← hsum] at h1
      have h2 : r * (2 * (s - y i)) = L0 - lam * y i := by
        calc r * (2 * (s - y i)) = lam * s - lam * y i := by simp only [r]; ring
          _ = L0 - lam * y i := by rw [hlam_s]
      linarith only [h1, h2]
  have hdisj' : ∀ i j : Fin 11, i ≠ j → ∀ X Y : ℝ,
      boxInside r (lam * x i) (lam * y i) (cs i).1 (cs i).2 X Y →
      ¬ boxInside r (lam * x j) (lam * y j) (cs j).1 (cs j).2 X Y := by
    intro i j hne X Y hbi hbj
    have hscale : ∀ k : Fin 11,
        boxInside r (lam * x k) (lam * y k) (cs k).1 (cs k).2 X Y →
        inside (x k) (y k) (a k) (b k) (X / lam) (Y / lam) := by
      intro k hk
      have h1 : boxInside (1 / 2) (x k) (y k) (cs k).1 (cs k).2 (X / lam) (Y / lam) := by
        rcases hk with ⟨hu, hv⟩
        have hX : X / lam - x k = (X - lam * x k) / lam := by field_simp [hlam_pos.ne']
        have hY : Y / lam - y k = (Y - lam * y k) / lam := by field_simp [hlam_pos.ne']
        refine ⟨?_, ?_⟩
        · have heq : (cs k).1 * (X / lam - x k) + (cs k).2 * (Y / lam - y k) =
              ((cs k).1 * (X - lam * x k) + (cs k).2 * (Y - lam * y k)) / lam := by
            rw [hX, hY]; ring
          rw [heq, abs_div, abs_of_pos hlam_pos, div_lt_iff₀ hlam_pos]
          simp only [r] at hu; linarith only [hu]
        · have heq : (-(cs k).2) * (X / lam - x k) + (cs k).1 * (Y / lam - y k) =
              ((-(cs k).2) * (X - lam * x k) + (cs k).1 * (Y - lam * y k)) / lam := by
            rw [hX, hY]; ring
          rw [heq, abs_div, abs_of_pos hlam_pos, div_lt_iff₀ hlam_pos]
          simp only [r] at hv; linarith only [hv]
      exact (hcs_prop k).2.2.2.2 (1 / 2) (X / lam) (Y / lam) |>.mp h1
    exact hdisj i j hne (X / lam) (Y / lam) (hscale i hbi) (hscale j hbj)
  exact packing_contradiction r (fun i => lam * x i) (fun i => lam * y i)
    (fun i => (cs i).1) (fun i => (cs i).2) hvalid hdisj'
