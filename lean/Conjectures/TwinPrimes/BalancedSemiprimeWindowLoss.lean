import Mathlib

open Finset Real

namespace Conjectures.TwinPrimes.BalancedSemiprimeWindowLoss_aux

open scoped Classical

def PP (X p : ℕ) : Prop :=
  ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ r < s ∧ Nat.sqrt X / 2 ≤ r ∧ r ≤ Nat.sqrt (2 * X + 2) ∧
    p + 2 = r * s

noncomputable def rr (X p : ℕ) : ℕ := if h : PP X p then Classical.choose h else 0

noncomputable def ss (X p : ℕ) : ℕ :=
  if h : PP X p then Classical.choose (Classical.choose_spec h) else 0

lemma rr_spec (X p : ℕ) (hp : PP X p) :
    (rr X p).Prime ∧ (ss X p).Prime ∧ rr X p < ss X p ∧ Nat.sqrt X / 2 ≤ rr X p ∧
      rr X p ≤ Nat.sqrt (2 * X + 2) ∧ p + 2 = rr X p * ss X p := by
  have e1 : rr X p = Classical.choose hp := by simp only [rr, dif_pos hp]
  have e2 : ss X p = Classical.choose (Classical.choose_spec hp) := by simp only [ss, dif_pos hp]
  rw [e1, e2]
  exact Classical.choose_spec (Classical.choose_spec hp)

theorem sqrt_bounds (X : ℕ) (hX : 100 ≤ X) :
    5 ≤ Nat.sqrt X / 2 ∧ Nat.sqrt (2 * X + 2) ≤ 8 * (Nat.sqrt X / 2) ∧ X < (Nat.sqrt X / 2) ^ 4 := by
  have hs10 : 10 ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by omega)
  have hdiv : 2 * (Nat.sqrt X / 2) + Nat.sqrt X % 2 = Nat.sqrt X := Nat.div_add_mod (Nat.sqrt X) 2
  have hmodlt : Nat.sqrt X % 2 < 2 := Nat.mod_lt _ (by omega)
  have hrm5 : 5 ≤ Nat.sqrt X / 2 := by omega
  have hstep : Nat.sqrt X + 1 ≤ 2 * (Nat.sqrt X / 2) + 2 := by omega
  have hlt : X < (Nat.sqrt X + 1) ^ 2 := by
    have h := Nat.lt_succ_sqrt' X
    rwa [Nat.succ_eq_add_one] at h
  have hsq : (Nat.sqrt X + 1) ^ 2 ≤ (2 * (Nat.sqrt X / 2) + 2) ^ 2 := Nat.pow_le_pow_left hstep 2
  have hXlt : X < (2 * (Nat.sqrt X / 2) + 2) * (2 * (Nat.sqrt X / 2) + 2) := by
    have h := lt_of_lt_of_le hlt hsq
    simpa [Nat.pow_two] using h
  refine ⟨hrm5, ?_, ?_⟩
  · have hb : 5 * 5 ≤ (Nat.sqrt X / 2) * (Nat.sqrt X / 2) := Nat.mul_self_le_mul_self hrm5
    have h1 : 2 * X + 2 ≤ 8 * ((Nat.sqrt X / 2) * (Nat.sqrt X / 2)) + 16 * (Nat.sqrt X / 2) + 8 := by
      have h2 : X + 1 ≤ (2 * (Nat.sqrt X / 2) + 2) * (2 * (Nat.sqrt X / 2) + 2) := by omega
      calc 2 * X + 2 = 2 * (X + 1) := by ring
        _ ≤ 2 * ((2 * (Nat.sqrt X / 2) + 2) * (2 * (Nat.sqrt X / 2) + 2)) :=
              Nat.mul_le_mul_left 2 h2
        _ = 8 * ((Nat.sqrt X / 2) * (Nat.sqrt X / 2)) + 16 * (Nat.sqrt X / 2) + 8 := by ring
    have h3 : 8 * ((Nat.sqrt X / 2) * (Nat.sqrt X / 2)) + 16 * (Nat.sqrt X / 2) + 8
        < 64 * ((Nat.sqrt X / 2) * (Nat.sqrt X / 2)) + 16 * (Nat.sqrt X / 2) + 1 := by
      have h4 : 8 ≤ 56 * ((Nat.sqrt X / 2) * (Nat.sqrt X / 2)) :=
        le_trans (by norm_num) (Nat.mul_le_mul_left 56 hb)
      omega
    have key : 2 * X + 2 < (8 * (Nat.sqrt X / 2) + 1) * (8 * (Nat.sqrt X / 2) + 1) := by
      calc 2 * X + 2 ≤ 8 * ((Nat.sqrt X / 2) * (Nat.sqrt X / 2)) + 16 * (Nat.sqrt X / 2) + 8 := h1
        _ < 64 * ((Nat.sqrt X / 2) * (Nat.sqrt X / 2)) + 16 * (Nat.sqrt X / 2) + 1 := h3
        _ = (8 * (Nat.sqrt X / 2) + 1) * (8 * (Nat.sqrt X / 2) + 1) := by ring
    have h5 : Nat.sqrt (2 * X + 2) < 8 * (Nat.sqrt X / 2) + 1 := Nat.sqrt_lt.mpr key
    omega
  · have hrm4 : 4 ≤ Nat.sqrt X / 2 := by omega
    have h16 : 4 * 4 ≤ (Nat.sqrt X / 2) * (Nat.sqrt X / 2) := Nat.mul_self_le_mul_self hrm4
    have h1 : 2 * (Nat.sqrt X / 2) + 2 ≤ 4 * (Nat.sqrt X / 2) := by omega
    have h2 : (2 * (Nat.sqrt X / 2) + 2) * (2 * (Nat.sqrt X / 2) + 2)
        ≤ (4 * (Nat.sqrt X / 2)) * (4 * (Nat.sqrt X / 2)) := Nat.mul_self_le_mul_self h1
    have h3 : (4 * (Nat.sqrt X / 2)) * (4 * (Nat.sqrt X / 2))
        ≤ ((Nat.sqrt X / 2) * (Nat.sqrt X / 2)) * ((Nat.sqrt X / 2) * (Nat.sqrt X / 2)) := by
      calc (4 * (Nat.sqrt X / 2)) * (4 * (Nat.sqrt X / 2))
          = 16 * ((Nat.sqrt X / 2) * (Nat.sqrt X / 2)) := by ring
        _ ≤ ((Nat.sqrt X / 2) * (Nat.sqrt X / 2)) * ((Nat.sqrt X / 2) * (Nat.sqrt X / 2)) :=
              Nat.mul_le_mul_right _ h16
    calc X < (2 * (Nat.sqrt X / 2) + 2) * (2 * (Nat.sqrt X / 2) + 2) := hXlt
      _ ≤ (4 * (Nat.sqrt X / 2)) * (4 * (Nat.sqrt X / 2)) := h2
      _ ≤ ((Nat.sqrt X / 2) * (Nat.sqrt X / 2)) * ((Nat.sqrt X / 2) * (Nat.sqrt X / 2)) := h3
      _ = (Nat.sqrt X / 2) ^ 4 := by ring


theorem div_bounds (X r : ℕ) (hX : 100 ≤ X) (hr1 : 1 ≤ r) (hr2 : r * r ≤ 2 * X + 2) :
    3 ≤ (X + 2) / r ∧ X ≤ 4 * ((X + 2) / r) ^ 2 := by
  have hr0 : 0 < r := hr1
  have hXX : 100 * X ≤ X * X := Nat.mul_le_mul_right X hX
  have h14 : 14 * X + 14 ≤ 100 * X := by omega
  have hsq : 9 * (2 * X + 2) ≤ (X + 2) * (X + 2) := by
    calc 9 * (2 * X + 2) = 14 * X + 14 + (4 * X + 4) := by ring
      _ ≤ 100 * X + (4 * X + 4) := Nat.add_le_add_right h14 _
      _ ≤ X * X + (4 * X + 4) := Nat.add_le_add_right hXX _
      _ = (X + 2) * (X + 2) := by ring
  have hY3 : 3 ≤ (X + 2) / r := by
    rw [Nat.le_div_iff_mul_le hr0]
    exact Nat.mul_self_le_mul_self_iff.mp
      (calc (3 * r) * (3 * r) = 9 * (r * r) := by ring
        _ ≤ 9 * (2 * X + 2) := Nat.mul_le_mul_left 9 hr2
        _ ≤ (X + 2) * (X + 2) := hsq)
  refine ⟨hY3, ?_⟩
  have hmod : r * ((X + 2) / r) + (X + 2) % r = X + 2 := Nat.div_add_mod (X + 2) r
  have hmodlt : (X + 2) % r < r := Nat.mod_lt _ hr0
  have hdiv2 : X + 2 < r * ((X + 2) / r + 1) := by
    have h1 : X + 2 < r * ((X + 2) / r) + r := by
      have h2 : r * ((X + 2) / r) + (X + 2) % r < r * ((X + 2) / r) + r :=
        Nat.add_lt_add_left hmodlt _
      rw [hmod] at h2
      exact h2
    calc X + 2 < r * ((X + 2) / r) + r := h1
      _ = r * ((X + 2) / r + 1) := by ring
  have hrlt : r < 2 * ((X + 2) / r + 1) := by
    have h : r * r < r * (2 * ((X + 2) / r + 1)) := by
      calc r * r ≤ 2 * X + 2 := hr2
        _ < 2 * (X + 2) := by omega
        _ ≤ 2 * (r * ((X + 2) / r + 1)) := Nat.mul_le_mul_left 2 (le_of_lt hdiv2)
        _ = r * (2 * ((X + 2) / r + 1)) := by ring
    exact Nat.lt_of_mul_lt_mul_left h
  have hX3 : X + 3 ≤ 2 * (((X + 2) / r + 1) * ((X + 2) / r + 1)) := by
    have h1 : X + 2 < 2 * (((X + 2) / r + 1) * ((X + 2) / r + 1)) := by
      calc X + 2 < r * ((X + 2) / r + 1) := hdiv2
        _ ≤ 2 * ((X + 2) / r + 1) * ((X + 2) / r + 1) :=
              Nat.mul_le_mul_right _ (le_of_lt hrlt)
        _ = 2 * (((X + 2) / r + 1) * ((X + 2) / r + 1)) := by ring
    omega
  have hY1 : 1 ≤ (X + 2) / r := le_trans (by omega) hY3
  have h2Y : 2 ≤ 2 * ((X + 2) / r) := by
    have h := Nat.mul_le_mul_left 2 hY1
    simpa using h
  have hkey1 : 4 * ((X + 2) / r) + 2 ≤ 6 * ((X + 2) / r) := by
    calc 4 * ((X + 2) / r) + 2 ≤ 4 * ((X + 2) / r) + 2 * ((X + 2) / r) :=
            Nat.add_le_add_left h2Y _
      _ = 6 * ((X + 2) / r) := by ring
  have hYsq : 3 * ((X + 2) / r) ≤ ((X + 2) / r) * ((X + 2) / r) :=
    Nat.mul_le_mul_right _ hY3
  have hkey : 4 * ((X + 2) / r) + 2 ≤ 2 * (((X + 2) / r) * ((X + 2) / r)) := by
    calc 4 * ((X + 2) / r) + 2 ≤ 6 * ((X + 2) / r) := hkey1
      _ = 2 * (3 * ((X + 2) / r)) := by ring
      _ ≤ 2 * (((X + 2) / r) * ((X + 2) / r)) := Nat.mul_le_mul_left 2 hYsq
  have hfin : 2 * (((X + 2) / r + 1) * ((X + 2) / r + 1))
      ≤ 4 * (((X + 2) / r) * ((X + 2) / r)) := by
    have hid : 2 * (((X + 2) / r + 1) * ((X + 2) / r + 1))
        = 2 * (((X + 2) / r) * ((X + 2) / r)) + (4 * ((X + 2) / r) + 2) := by ring
    rw [hid]
    calc 2 * (((X + 2) / r) * ((X + 2) / r)) + (4 * ((X + 2) / r) + 2)
        ≤ 2 * (((X + 2) / r) * ((X + 2) / r)) + 2 * (((X + 2) / r) * ((X + 2) / r)) :=
          Nat.add_le_add_left hkey _
      _ = 4 * (((X + 2) / r) * ((X + 2) / r)) := by ring
  have hcomb : X ≤ 4 * (((X + 2) / r) * ((X + 2) / r)) :=
    le_trans (Nat.le_add_right X 3) (le_trans hX3 hfin)
  rw [Nat.pow_two]
  exact hcomb


theorem s_window (X r s p : ℕ) (hX : 100 ≤ X) (hr1 : 1 ≤ r) (hr2 : r * r ≤ 2 * X + 2)
    (hpX : X < p) (hp50 : 50 * p < 51 * X) (hrs : p + 2 = r * s) :
    (X + 2) / r < s ∧ s ≤ 2 * ((X + 2) / r) := by
  have hr0 : 0 < r := hr1
  have hmul : r * ((X + 2) / r) ≤ X + 2 := Nat.mul_div_le (X + 2) r
  have hrs' : X + 2 < r * s := by
    calc X + 2 < p + 2 := by omega
      _ = r * s := hrs
  have hlow : (X + 2) / r < s := Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt hmul hrs')
  refine ⟨hlow, ?_⟩
  have hXX : 100 * X ≤ X * X := Nat.mul_le_mul_right X hX
  have h1 : 50 * X + 50 ≤ 100 * X := by omega
  have hbig : 50 * X + 50 ≤ X * X := le_trans h1 hXX
  have h25 : (5 * r) * (5 * r) ≤ X * X := by
    calc (5 * r) * (5 * r) = 25 * (r * r) := by ring
      _ ≤ 25 * (2 * X + 2) := Nat.mul_le_mul_left 25 hr2
      _ = 50 * X + 50 := by ring
      _ ≤ X * X := hbig
  have h5r : 5 * r ≤ X := Nat.mul_self_le_mul_self_iff.mp h25
  have h100r : 100 * r ≤ 20 * X := by
    calc 100 * r = 20 * (5 * r) := by ring
      _ ≤ 20 * X := Nat.mul_le_mul_left 20 h5r
  have hpr : p + 2 * r ≤ 2 * X + 4 := by omega
  have hmod : r * ((X + 2) / r) + (X + 2) % r = X + 2 := Nat.div_add_mod (X + 2) r
  have hmodlt : (X + 2) % r < r := Nat.mod_lt _ hr0
  have hkey : r * s ≤ 2 * (r * ((X + 2) / r)) := by omega
  have hkey' : r * s ≤ r * (2 * ((X + 2) / r)) := by
    calc r * s ≤ 2 * (r * ((X + 2) / r)) := hkey
      _ = r * (2 * ((X + 2) / r)) := by ring
  exact (Nat.mul_le_mul_left_iff hr0).mp hkey'


theorem log_lower_third (X Y : ℕ) (hX : 64 ≤ X) (hY : 1 ≤ Y) (h : X ≤ 4 * Y ^ 2) :
    Real.log X / 3 ≤ Real.log Y := by
  have hX' : (64 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hY' : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have h' : (X : ℝ) ≤ 4 * (Y : ℝ) ^ 2 := by exact_mod_cast h
  have hX0 : (0 : ℝ) < (X : ℝ) := by linarith
  have hY0 : (0 : ℝ) < (Y : ℝ) := by linarith
  have hY2 : ((Y : ℝ) ^ 2) ≠ 0 := ne_of_gt (pow_pos hY0 2)
  have hstep1 : Real.log (X : ℝ) ≤ Real.log 4 + 2 * Real.log (Y : ℝ) := by
    have h1 : Real.log (X : ℝ) ≤ Real.log (4 * (Y : ℝ) ^ 2) := Real.log_le_log hX0 h'
    have h2 : Real.log (4 * (Y : ℝ) ^ 2) = Real.log 4 + 2 * Real.log (Y : ℝ) := by
      rw [Real.log_mul (x := (4 : ℝ)) (y := (Y : ℝ) ^ 2) (by norm_num) hY2, Real.log_pow]
      push_cast
      ring
    linarith
  have hstep2 : 3 * Real.log 4 ≤ Real.log (X : ℝ) := by
    have h3 : Real.log 64 ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) hX'
    have h4 : Real.log 64 = 3 * Real.log 4 := by
      have h64 : (64 : ℝ) = 4 ^ 3 := by norm_num
      rw [h64, Real.log_pow]
      push_cast
      ring
    linarith
  linarith


theorem log_lower_quarter (X r : ℕ) (hX : 1 ≤ X) (hr : 1 ≤ r) (h : X < r ^ 4) :
    Real.log X / 4 ≤ Real.log r := by
  have hX' : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hr' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h' : (X : ℝ) < (r : ℝ) ^ 4 := by exact_mod_cast h
  have hX0 : (0 : ℝ) < (X : ℝ) := by linarith
  have hr0 : (0 : ℝ) < (r : ℝ) := by linarith
  have hr2 : ((r : ℝ) ^ 2) ≠ 0 := ne_of_gt (pow_pos hr0 2)
  have h1 : Real.log (X : ℝ) ≤ Real.log ((r : ℝ) ^ 4) := Real.log_le_log hX0 h'.le
  have h2 : Real.log ((r : ℝ) ^ 4) = 4 * Real.log (r : ℝ) := by
    have he : (r : ℝ) ^ 4 = (r : ℝ) ^ 2 * (r : ℝ) ^ 2 := by ring
    rw [he, Real.log_mul (x := (r : ℝ) ^ 2) (y := (r : ℝ) ^ 2) hr2 hr2, Real.log_pow]
    push_cast
    ring
  linarith


theorem weight_bound (X p : ℕ) (hX : 100 ≤ X) (hp1 : 1 ≤ p) (hp2 : p ≤ 2 * X) :
    Real.log (p : ℝ) * Real.log ((p : ℝ) + 2) ≤ 4 * (Real.log X) ^ 2 := by
  have hX' : (100 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hp1' : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
  have hp2' : (p : ℝ) ≤ 2 * (X : ℝ) := by exact_mod_cast hp2
  have hX0 : (0 : ℝ) < (X : ℝ) := by linarith
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hq0 : (0 : ℝ) < (p : ℝ) + 2 := by linarith
  have hL4 : Real.log 4 ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) (by linarith)
  have hLp : Real.log (p : ℝ) ≤ Real.log (4 * (X : ℝ)) :=
    Real.log_le_log hp0 (by linarith)
  have hLq : Real.log ((p : ℝ) + 2) ≤ Real.log (4 * (X : ℝ)) :=
    Real.log_le_log hq0 (by linarith)
  have hL4X : Real.log (4 * (X : ℝ)) = Real.log 4 + Real.log (X : ℝ) :=
    Real.log_mul (x := (4 : ℝ)) (y := (X : ℝ)) (by norm_num) (by linarith)
  have hLX0 : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by linarith)
  have hLq0 : 0 ≤ Real.log ((p : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hLp' : Real.log (p : ℝ) ≤ 2 * Real.log (X : ℝ) := by linarith
  have hLq' : Real.log ((p : ℝ) + 2) ≤ 2 * Real.log (X : ℝ) := by linarith
  have hmul1 : Real.log (p : ℝ) * Real.log ((p : ℝ) + 2)
      ≤ 2 * Real.log (X : ℝ) * Real.log ((p : ℝ) + 2) :=
    mul_le_mul_of_nonneg_right hLp' hLq0
  have hmul2 : 2 * Real.log (X : ℝ) * Real.log ((p : ℝ) + 2)
      ≤ 2 * Real.log (X : ℝ) * (2 * Real.log (X : ℝ)) :=
    mul_le_mul_of_nonneg_left hLq' (by linarith)
  calc Real.log (p : ℝ) * Real.log ((p : ℝ) + 2)
      ≤ 2 * Real.log (X : ℝ) * Real.log ((p : ℝ) + 2) := hmul1
    _ ≤ 2 * Real.log (X : ℝ) * (2 * Real.log (X : ℝ)) := hmul2
    _ = 4 * (Real.log X) ^ 2 := by ring

theorem log_four_le : Real.log 4 ≤ 3 := by
  have h := Real.log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num)
  norm_num at h
  exact h


theorem recip_sum_bound (X N rmin : ℕ) (R : Finset ℕ)
    (hR : ∀ r ∈ R, rmin ≤ r ∧ r ≤ N ∧ r.Prime)
    (hrmin : 5 ≤ rmin) (hN : N ≤ 8 * rmin) (hX : 100 ≤ X) (hr4 : X < rmin ^ 4) :
    ∑ r ∈ R, (1 : ℝ) / ((r : ℕ) : ℝ) ≤ 96 / Real.log X := by
  have hrmin' : (5 : ℝ) ≤ (rmin : ℝ) := by exact_mod_cast hrmin
  have hN' : (N : ℝ) ≤ 8 * (rmin : ℝ) := by exact_mod_cast hN
  have hX' : (100 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < (X : ℝ) := by linarith
  have hLX : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  have hrmin0 : (0 : ℝ) < (rmin : ℝ) := by linarith
  have hLrmin : 0 < Real.log (rmin : ℝ) := Real.log_pos (by linarith)
  have hD : (0 : ℝ) < (rmin : ℝ) * Real.log (rmin : ℝ) := mul_pos hrmin0 hLrmin
  have hlogX : Real.log (X : ℝ) ≤ 4 * Real.log (rmin : ℝ) := by
    have h1 : (X : ℝ) < (rmin : ℝ) ^ 4 := by exact_mod_cast hr4
    have h2 : Real.log (X : ℝ) ≤ Real.log ((rmin : ℝ) ^ 4) := Real.log_le_log hX0 h1.le
    have h3 : Real.log ((rmin : ℝ) ^ 4) = 4 * Real.log (rmin : ℝ) := by
      rw [Real.log_pow]
      push_cast
      ring
    linarith
  have hpt : ∀ r ∈ R, (1 : ℝ) / (r : ℝ)
      ≤ Real.log (r : ℝ) / ((rmin : ℝ) * Real.log (rmin : ℝ)) := by
    intro r hr
    obtain ⟨hr1, hr2, hr3⟩ := hR r hr
    have hrr : (rmin : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    have hr0 : (0 : ℝ) < (r : ℝ) := by linarith
    have hLr : 0 < Real.log (r : ℝ) := Real.log_pos (by linarith)
    have hLmono : Real.log (rmin : ℝ) ≤ Real.log (r : ℝ) := Real.log_le_log hrmin0 hrr
    have hcross : (rmin : ℝ) * Real.log (rmin : ℝ) ≤ (r : ℝ) * Real.log (r : ℝ) := by
      have t1 : (r : ℝ) * Real.log (rmin : ℝ) ≤ (r : ℝ) * Real.log (r : ℝ) :=
        mul_le_mul_of_nonneg_left hLmono hr0.le
      have t2 : (rmin : ℝ) * Real.log (rmin : ℝ) ≤ (r : ℝ) * Real.log (rmin : ℝ) :=
        mul_le_mul_of_nonneg_right hrr hLrmin.le
      linarith
    exact (div_le_div_iff₀ hr0 hD).mpr (by linarith)
  have hsumA : ∑ r ∈ R, (1 : ℝ) / (r : ℝ)
      ≤ ∑ r ∈ R, Real.log (r : ℝ) / ((rmin : ℝ) * Real.log (rmin : ℝ)) :=
    Finset.sum_le_sum hpt
  have hsumB : ∑ r ∈ R, Real.log (r : ℝ) / ((rmin : ℝ) * Real.log (rmin : ℝ))
      = (∑ r ∈ R, Real.log (r : ℝ)) / ((rmin : ℝ) * Real.log (rmin : ℝ)) :=
    (Finset.sum_div R (fun r => Real.log (r : ℝ))
      ((rmin : ℝ) * Real.log (rmin : ℝ))).symm
  have hsub : R ⊆ Nat.primesLE N := by
    intro r hr
    obtain ⟨hr1, hr2, hr3⟩ := hR r hr
    exact Nat.mem_primesLE.mpr ⟨hr2, hr3⟩
  have hsumC : (∑ r ∈ R, Real.log (r : ℝ)) ≤ ∑ r ∈ Nat.primesLE N, Real.log (r : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Real.log_natCast_nonneg i)
  have hsumD : (∑ r ∈ Nat.primesLE N, Real.log (r : ℝ)) ≤ Real.log 4 * (N : ℝ) := by
    have h1 : (∑ r ∈ Nat.primesLE N, Real.log (r : ℝ)) = Chebyshev.theta ((N : ℕ) : ℝ) :=
      (Chebyshev.theta_eq_sum_primesLE_log N).symm
    have h2 : Chebyshev.theta ((N : ℕ) : ℝ) ≤ Real.log 4 * ((N : ℕ) : ℝ) :=
      Chebyshev.theta_le_log4_mul_x (by positivity)
    rw [h1]
    exact h2
  have hL4 : Real.log 4 ≤ 3 := log_four_le
  have hNn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have e1 : Real.log 4 * (N : ℝ) ≤ 24 * (rmin : ℝ) := by
    have t1 : Real.log 4 * (N : ℝ) ≤ 3 * (N : ℝ) := mul_le_mul_of_nonneg_right hL4 hNn
    have t2 : (3 : ℝ) * (N : ℝ) ≤ 3 * (8 * (rmin : ℝ)) :=
      mul_le_mul_of_nonneg_left hN' (by norm_num)
    linarith
  have e2 : Real.log 4 * (N : ℝ) * Real.log (X : ℝ) ≤ 24 * (rmin : ℝ) * Real.log (X : ℝ) :=
    mul_le_mul_of_nonneg_right e1 hLX.le
  have e3 : 24 * (rmin : ℝ) * Real.log (X : ℝ)
      ≤ 24 * (rmin : ℝ) * (4 * Real.log (rmin : ℝ)) :=
    mul_le_mul_of_nonneg_left hlogX (by linarith)
  have e4 : Real.log 4 * (N : ℝ) * Real.log (X : ℝ)
      ≤ 96 * ((rmin : ℝ) * Real.log (rmin : ℝ)) := by linarith
  have hfin : Real.log 4 * (N : ℝ) / ((rmin : ℝ) * Real.log (rmin : ℝ))
      ≤ 96 / Real.log (X : ℝ) :=
    (div_le_div_iff₀ hD hLX).mpr (by linarith)
  calc ∑ r ∈ R, (1 : ℝ) / ((r : ℕ) : ℝ)
      ≤ ∑ r ∈ R, Real.log (r : ℝ) / ((rmin : ℝ) * Real.log (rmin : ℝ)) := hsumA
    _ = (∑ r ∈ R, Real.log (r : ℝ)) / ((rmin : ℝ) * Real.log (rmin : ℝ)) := hsumB
    _ ≤ (Real.log 4 * (N : ℝ)) / ((rmin : ℝ) * Real.log (rmin : ℝ)) :=
      div_le_div_of_nonneg_right (by linarith) hD.le
    _ ≤ 96 / Real.log (X : ℝ) := hfin


end Conjectures.TwinPrimes.BalancedSemiprimeWindowLoss_aux

open Conjectures.TwinPrimes.BalancedSemiprimeWindowLoss_aux

theorem Conjectures.TwinPrimes.BalancedSemiprimeWindowLoss :
    let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let S := fun (X : ℕ) => @Finset.filter ℕ (fun p => p.Prime ∧ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ r < s ∧ Nat.sqrt X/2 ≤ r ∧ r ≤ Nat.sqrt (2*X+2) ∧ p+2=r*s) (fun _ => Classical.propDecidable _) (w X); (∃ C : ℝ, 0 < C ∧ ∀ (Y r : ℕ), 3 ≤ Y → r.Prime → 2 < r → ((((Finset.Ioc Y (2*Y)).filter (fun s => s.Prime ∧ (r*s-2).Prime)).card:ℕ):ℝ) ≤ C*(Y:ℝ)/(Real.log Y)^2) → (∃ K : ℝ, 0 < K ∧ ∀ X : ℕ, 100 ≤ X → (S X).sum (fun p => Real.log p * Real.log (p+2)) ≤ K*(X:ℝ)/Real.log X) := by
  intro w S
  rintro ⟨C, hCpos, hC⟩
  refine ⟨6912 * C, by positivity, ?_⟩
  intro X hX
  haveI : DecidablePred (fun q : ℕ => q.Prime ∧ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ r < s ∧
      Nat.sqrt X / 2 ≤ r ∧ r ≤ Nat.sqrt (2 * X + 2) ∧ q + 2 = r * s) :=
    fun _ => Classical.propDecidable _
  have hSX : S X = (w X).filter (fun q : ℕ => q.Prime ∧ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ r < s ∧
      Nat.sqrt X / 2 ≤ r ∧ r ≤ Nat.sqrt (2 * X + 2) ∧ q + 2 = r * s) :=
    Finset.filter_congr_decidable (w X) _ (fun _ => Classical.propDecidable _)
  have hPP : ∀ p ∈ S X, PP X p := by
    intro p hp
    rw [hSX] at hp
    exact (Finset.mem_filter.mp hp).2.2
  have hwin : ∀ p ∈ S X, X < p ∧ 50 * p < 51 * X ∧ p < 2 * X + 1 ∧ p.Prime := by
    intro p hp
    rw [hSX] at hp
    have h1 := Finset.mem_filter.mp hp
    have h2 := Finset.mem_filter.mp h1.1
    exact ⟨h2.2.1, h2.2.2, Finset.mem_range.mp h2.1, h1.2.1⟩
  obtain ⟨hrmin5, hNle, hr4⟩ := sqrt_bounds X hX
  set R := (Finset.Icc (Nat.sqrt X / 2) (Nat.sqrt (2 * X + 2))).filter (fun r => r.Prime) with hR
  set Yr := fun r => (X + 2) / r with hYr
  have hrmem : ∀ r ∈ R, Nat.sqrt X / 2 ≤ r ∧ r ≤ Nat.sqrt (2 * X + 2) ∧ r.Prime := by
    intro r hr
    rw [hR, Finset.mem_filter, Finset.mem_Icc] at hr
    exact ⟨hr.1.1, hr.1.2, hr.2⟩
  have hr1 : ∀ r ∈ R, 1 ≤ r := fun r hr => by
    have h := (hrmem r hr).1
    omega
  have hr2 : ∀ r ∈ R, 2 < r := fun r hr => by
    have h := (hrmem r hr).1
    omega
  have hrr2 : ∀ r ∈ R, r * r ≤ 2 * X + 2 := fun r hr => by
    have h := (hrmem r hr).2.1
    have h2 := Nat.sqrt_le (2 * X + 2)
    exact le_trans (Nat.mul_le_mul h h) h2
  have hdiv : ∀ r ∈ R, 3 ≤ Yr r ∧ X ≤ 4 * (Yr r) ^ 2 := fun r hr => by
    have h := div_bounds X r hX (hr1 r hr) (hrr2 r hr)
    simpa [hYr] using h
  have hlogY : ∀ r ∈ R, Real.log X / 3 ≤ Real.log ((Yr r : ℕ) : ℝ) := fun r hr => by
    have h := (hdiv r hr).2
    have h3 := (hdiv r hr).1
    have h4 := log_lower_third X (Yr r) (by omega) (by omega) h
    simpa [hYr] using h4
  have hlogX : (0 : ℝ) < Real.log X := Real.log_pos (by norm_cast; omega)
  have hYle : ∀ r ∈ R, ((Yr r : ℕ) : ℝ) ≤ ((X : ℝ) + 2) / ((r : ℕ) : ℝ) := by
    intro r hr
    have h1 : Yr r * r ≤ X + 2 := by
      simp only [hYr]
      exact Nat.div_mul_le_self _ _
    have h2 : (0 : ℝ) < ((r : ℕ) : ℝ) := by
      have h3 := hr1 r hr
      exact_mod_cast (show (0 : ℕ) < r by omega)
    have h3 : ((Yr r : ℕ) : ℝ) * ((r : ℕ) : ℝ) ≤ ((X : ℝ) + 2) := by
      have h4 : (((Yr r * r : ℕ) : ℝ)) ≤ ((X + 2 : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h4 ⊢
      linarith
    rw [le_div_iff₀ h2]
    linarith
  have hfib : ∀ r ∈ R, ((((S X).filter (fun p => rr X p = r)).card : ℕ) : ℝ) ≤
      C * ((Yr r : ℕ) : ℝ) / (Real.log ((Yr r : ℕ) : ℝ)) ^ 2 := by
    intro r hr
    have hA : ((S X).filter (fun p => rr X p = r)).card ≤
        ((Finset.Ioc (Yr r) (2 * (Yr r))).filter (fun s => s.Prime ∧ (r * s - 2).Prime)).card := by
      have hinj : (((S X).filter (fun p => rr X p = r) : Finset ℕ) : Set ℕ).InjOn (ss X) := by
        intro a ha b hb hab
        have ha' := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
        have hb' := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
        have hsa := rr_spec X a (hPP a ha'.1)
        have hsb := rr_spec X b (hPP b hb'.1)
        have h1 : a + 2 = r * ss X a := by rw [← ha'.2]; exact hsa.2.2.2.2.2
        have h2 : b + 2 = r * ss X a := by
          calc b + 2 = rr X b * ss X b := hsb.2.2.2.2.2
            _ = r * ss X b := by rw [hb'.2]
            _ = r * ss X a := by rw [hab]
        omega
      have hsub : ((S X).filter (fun p => rr X p = r)).image (ss X) ⊆
          (Finset.Ioc (Yr r) (2 * (Yr r))).filter (fun s => s.Prime ∧ (r * s - 2).Prime) := by
        intro y hy
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
        have ha' := Finset.mem_filter.mp ha
        have hma := hwin a ha'.1
        have hsa := rr_spec X a (hPP a ha'.1)
        have h1 : a + 2 = r * ss X a := by rw [← ha'.2]; exact hsa.2.2.2.2.2
        have hsw := s_window X r (ss X a) a hX (hr1 r hr) (hrr2 r hr) hma.1 hma.2.1 h1
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        refine ⟨⟨hsw.1, hsw.2⟩, hsa.2.1, ?_⟩
        have hkey : r * ss X a - 2 = a := by omega
        rw [hkey]
        exact hma.2.2.2
      calc ((S X).filter (fun p => rr X p = r)).card
          = (((S X).filter (fun p => rr X p = r)).image (ss X)).card :=
            (Finset.card_image_of_injOn hinj).symm
        _ ≤ ((Finset.Ioc (Yr r) (2 * (Yr r))).filter
              (fun s => s.Prime ∧ (r * s - 2).Prime)).card := Finset.card_le_card hsub
    calc ((((S X).filter (fun p => rr X p = r)).card : ℕ) : ℝ)
        ≤ ((((Finset.Ioc (Yr r) (2 * (Yr r))).filter
              (fun s => s.Prime ∧ (r * s - 2).Prime)).card : ℕ) : ℝ) := by exact_mod_cast hA
      _ ≤ C * ((Yr r : ℕ) : ℝ) / (Real.log ((Yr r : ℕ) : ℝ)) ^ 2 :=
            hC (Yr r) r (by simpa [hYr] using (hdiv r hr).1) (hrmem r hr).2.2 (hr2 r hr)
  have hcardsum : ((S X).card : ℕ) =
      ∑ r ∈ R, (((S X).filter (fun p => rr X p = r)).card : ℕ) := by
    refine Finset.card_eq_sum_card_fiberwise (f := rr X) (s := S X) (t := R) ?_
    intro p hp
    have hsa := rr_spec X p (hPP p (Finset.mem_coe.mp hp))
    refine Finset.mem_coe.mpr ?_
    rw [hR, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hsa.2.2.2.1, hsa.2.2.2.2.1⟩, hsa.1⟩
  have hcard : ((S X).card : ℝ) ≤ ∑ r ∈ R, C * ((Yr r : ℕ) : ℝ) / (Real.log ((Yr r : ℕ) : ℝ)) ^ 2 := by
    have hcast : ((S X).card : ℝ) =
        ∑ r ∈ R, ((((S X).filter (fun p => rr X p = r)).card : ℕ) : ℝ) := by
      rw [hcardsum]; push_cast; rfl
    rw [hcast]
    exact Finset.sum_le_sum (fun r hr => hfib r hr)
  have hrecip : ∑ r ∈ R, (1 : ℝ) / ((r : ℕ) : ℝ) ≤ 96 / Real.log X := by
    refine recip_sum_bound X (Nat.sqrt (2 * X + 2)) (Nat.sqrt X / 2) R (fun r hr => ?_)
      hrmin5 hNle hX hr4
    exact ⟨(hrmem r hr).1, (hrmem r hr).2.1, (hrmem r hr).2.2⟩
  have hsumY : ∑ r ∈ R, ((Yr r : ℕ) : ℝ) ≤ 192 * (X : ℝ) / Real.log X := by
    calc ∑ r ∈ R, ((Yr r : ℕ) : ℝ) ≤ ∑ r ∈ R, ((X : ℝ) + 2) / ((r : ℕ) : ℝ) :=
          Finset.sum_le_sum (fun r hr => hYle r hr)
      _ = ((X : ℝ) + 2) * ∑ r ∈ R, (1 : ℝ) / ((r : ℕ) : ℝ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun r _ => by ring)
      _ ≤ ((X : ℝ) + 2) * (96 / Real.log X) := by
          exact mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ ≤ 192 * (X : ℝ) / Real.log X := by
          have hX2 : ((X : ℝ) + 2) ≤ 2 * (X : ℝ) := by norm_cast; omega
          have : (192 : ℝ) * (X : ℝ) / Real.log X = (2 * (X : ℝ)) * (96 / Real.log X) := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_right hX2 (by positivity)
  have hcard3 : ((S X).card : ℝ) ≤ 1728 * C * (X : ℝ) / (Real.log X) ^ 3 := by
    have h1 : ∑ r ∈ R, C * ((Yr r : ℕ) : ℝ) / (Real.log ((Yr r : ℕ) : ℝ)) ^ 2 ≤
        ∑ r ∈ R, (C * ((Yr r : ℕ) : ℝ)) * (9 / (Real.log X) ^ 2) := by
      refine Finset.sum_le_sum (fun r hr => ?_)
      have hY := hlogY r hr
      have hsq : (Real.log X) ^ 2 ≤ 9 * (Real.log ((Yr r : ℕ) : ℝ)) ^ 2 := by
        nlinarith [hY, hlogX]
      have hnn : (0 : ℝ) ≤ C * ((Yr r : ℕ) : ℝ) := by positivity
      have hpos : (0 : ℝ) < (Real.log ((Yr r : ℕ) : ℝ)) ^ 2 := by
        have : (0 : ℝ) < Real.log ((Yr r : ℕ) : ℝ) := by
          have := div_pos hlogX (by norm_num : (0 : ℝ) < 3)
          linarith
        positivity
      have hpos2 : (0 : ℝ) < (Real.log X) ^ 2 := by positivity
      have hrw : (C * ((Yr r : ℕ) : ℝ)) * (9 / (Real.log X) ^ 2) =
          9 * (C * ((Yr r : ℕ) : ℝ)) / (Real.log X) ^ 2 := by ring
      rw [hrw, div_le_div_iff₀ hpos hpos2]
      have h5 : C * ((Yr r : ℕ) : ℝ) * (Real.log X) ^ 2 ≤
          C * ((Yr r : ℕ) : ℝ) * (9 * (Real.log ((Yr r : ℕ) : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hnn
      nlinarith [h5]
    calc ((S X).card : ℝ) ≤ ∑ r ∈ R, C * ((Yr r : ℕ) : ℝ) / (Real.log ((Yr r : ℕ) : ℝ)) ^ 2 := hcard
      _ ≤ ∑ r ∈ R, (C * ((Yr r : ℕ) : ℝ)) * (9 / (Real.log X) ^ 2) := h1
      _ = (C * (9 / (Real.log X) ^ 2)) * ∑ r ∈ R, ((Yr r : ℕ) : ℝ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun r _ => by ring)
      _ ≤ (C * (9 / (Real.log X) ^ 2)) * (192 * (X : ℝ) / Real.log X) := by
          exact mul_le_mul_of_nonneg_left hsumY (by positivity)
      _ = 1728 * C * (X : ℝ) / (Real.log X) ^ 3 := by
          have : Real.log X ≠ 0 := ne_of_gt hlogX
          field_simp
          ring
  calc (S X).sum (fun p => Real.log p * Real.log (p + 2))
      ≤ (S X).sum (fun _ => 4 * (Real.log X) ^ 2) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        obtain ⟨h1, h2, h3, h4⟩ := hwin p hp
        exact weight_bound X p hX (by omega) (by omega)
    _ = 4 * (Real.log X) ^ 2 * ((S X).card : ℝ) := by
        rw [Finset.sum_const]
        simp only [nsmul_eq_mul]
        ring
    _ ≤ 4 * (Real.log X) ^ 2 * (1728 * C * (X : ℝ) / (Real.log X) ^ 3) := by
        exact mul_le_mul_of_nonneg_left hcard3 (by positivity)
    _ = 6912 * C * (X : ℝ) / Real.log X := by
        have : Real.log X ≠ 0 := ne_of_gt hlogX
        field_simp
        ring
