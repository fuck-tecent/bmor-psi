import Mathlib

open Finset

theorem PEqualNP.Outside.L_quadratic_primes_levent_weighted_error_sum :
    ∃ C : ℝ, 0<C ∧ ∀ x : ℕ, 2≤x → (∑ q ∈ Finset.Icc 1 (Nat.sqrt x), Real.sqrt x*Real.log (4*(q : ℝ)*x)^2/q) ≤ C*Real.sqrt x*Real.log (4*(x : ℝ))^3 := by
  refine ⟨8, by norm_num, ?_⟩
  intro x hx
  set m := Nat.sqrt x with hm
  have hx2 : (2:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hxpos : (0:ℝ) < (x:ℝ) := by linarith
  have hsx : (0:ℝ) ≤ Real.sqrt (x:ℝ) := Real.sqrt_nonneg _
  have hl4xpos : (1:ℝ) < 4*(x:ℝ) := by linarith
  have hl4x : (0:ℝ) < Real.log (4*(x:ℝ)) := Real.log_pos hl4xpos
  have hlogx : (0:ℝ) ≤ Real.log (x:ℝ) := Real.log_nonneg (by linarith)
  have hterm : ∀ q ∈ Finset.Icc 1 m,
      Real.sqrt x*Real.log (4*(q : ℝ)*x)^2/q
        ≤ Real.sqrt x*(4*Real.log (4*(x : ℝ))^2)/q := by
    intro q hq
    obtain ⟨hq1, hqm⟩ := Finset.mem_Icc.mp hq
    have hq1r : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hqle : (q:ℝ) ≤ Real.sqrt (x:ℝ) := by
      have h1 : (q:ℝ) ≤ (m:ℝ) := by exact_mod_cast hqm
      have h2 : (m:ℝ) ≤ Real.sqrt (x:ℝ) := Real.nat_sqrt_le_real_sqrt
      linarith
    have hargpos : (0:ℝ) < 4*(q:ℝ)*(x:ℝ) := by positivity
    have hle : 4*(q:ℝ)*(x:ℝ) ≤ 4*Real.sqrt (x:ℝ)*(x:ℝ) := by
      have : 4*(q:ℝ) ≤ 4*Real.sqrt (x:ℝ) := by linarith
      nlinarith [this, hxpos.le]
    have hlog1 : Real.log (4*(q:ℝ)*(x:ℝ)) ≤ Real.log (4*Real.sqrt (x:ℝ)*(x:ℝ)) :=
      Real.log_le_log hargpos hle
    have hlog2 : Real.log (4*Real.sqrt (x:ℝ)*(x:ℝ)) ≤ 2*Real.log (4*(x:ℝ)) := by
      rw [show (4:ℝ)*Real.sqrt (x:ℝ)*(x:ℝ) = (4*(x:ℝ))*Real.sqrt (x:ℝ) by ring]
      rw [Real.log_mul (by positivity) (ne_of_gt (Real.sqrt_pos.mpr hxpos))]
      rw [Real.log_sqrt hxpos.le]
      have hlog4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      have : Real.log (x:ℝ)/2 ≤ Real.log (4*(x:ℝ)) := by
        rw [Real.log_mul (by norm_num) (ne_of_gt hxpos)]
        linarith
      linarith
    have hlogbound : Real.log (4*(q:ℝ)*(x:ℝ)) ≤ 2*Real.log (4*(x:ℝ)) := hlog1.trans hlog2
    have hlogqnn : (0:ℝ) ≤ Real.log (4*(q:ℝ)*(x:ℝ)) := by
      apply Real.log_nonneg
      have hq1' : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
      nlinarith [hq1', hx2]
    have hsq : Real.log (4*(q:ℝ)*(x:ℝ))^2 ≤ (2*Real.log (4*(x:ℝ)))^2 := by
      have h2nn : (0:ℝ) ≤ 2*Real.log (4*(x:ℝ)) := by linarith
      nlinarith [hlogbound, hlogqnn, h2nn]
    have hsq2 : Real.log (4*(q:ℝ)*(x:ℝ))^2 ≤ 4*Real.log (4*(x:ℝ))^2 := by
      have hsq' : (2*Real.log (4*(x:ℝ)))^2 = 4*Real.log (4*(x:ℝ))^2 := by ring
      calc Real.log (4*(q:ℝ)*(x:ℝ))^2 ≤ (2*Real.log (4*(x:ℝ)))^2 := hsq
        _ = 4*Real.log (4*(x:ℝ))^2 := hsq'
    rw [div_le_div_iff_of_pos_right hq1r]
    exact mul_le_mul_of_nonneg_left hsq2 hsx
  have hstep1 : (∑ q ∈ Finset.Icc 1 m, Real.sqrt x*Real.log (4*(q : ℝ)*x)^2/q)
      ≤ ∑ q ∈ Finset.Icc 1 m, Real.sqrt x*(4*Real.log (4*(x : ℝ))^2)/q :=
    Finset.sum_le_sum hterm
  have hstep2 : (∑ q ∈ Finset.Icc 1 m, Real.sqrt x*(4*Real.log (4*(x : ℝ))^2)/q)
      = Real.sqrt x*(4*Real.log (4*(x : ℝ))^2) * (∑ q ∈ Finset.Icc 1 m, (1:ℝ)/(q:ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [one_div, div_eq_mul_inv]
  have hharm : (∑ q ∈ Finset.Icc 1 m, (1:ℝ)/(q:ℝ)) ≤ 1 + Real.log (x:ℝ) := by
    have hcast : (harmonic m : ℝ) = ∑ q ∈ Finset.Icc 1 m, (1:ℝ)/(q:ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      apply Finset.sum_congr rfl
      intro q _
      rw [one_div]
    rw [← hcast]
    have h1 : (harmonic m : ℝ) ≤ 1 + Real.log (m:ℝ) := harmonic_le_one_add_log m
    have hmpos : 0 < m := Nat.sqrt_pos.mpr (by omega)
    have h2 : Real.log (m:ℝ) ≤ Real.log (x:ℝ) := by
      apply Real.log_le_log (by exact_mod_cast hmpos)
      exact_mod_cast Nat.sqrt_le_self x
    linarith
  have hstep3 : Real.sqrt x*(4*Real.log (4*(x : ℝ))^2) * (∑ q ∈ Finset.Icc 1 m, (1:ℝ)/(q:ℝ))
      ≤ Real.sqrt x*(4*Real.log (4*(x : ℝ))^2) * (1 + Real.log (x:ℝ)) := by
    apply mul_le_mul_of_nonneg_left hharm
    positivity
  have hkey : 1 + Real.log (x:ℝ) ≤ 2*Real.log (4*(x:ℝ)) := by
    have hlog4big : (1:ℝ) ≤ 2*Real.log 4 := by
      rw [Real.log_four_eq]; nlinarith [Real.log_two_gt_d9]
    rw [Real.log_mul (by norm_num) (ne_of_gt hxpos)]
    nlinarith [hlog4big, hlogx]
  have hstep4 : Real.sqrt x*(4*Real.log (4*(x : ℝ))^2) * (1 + Real.log (x:ℝ))
      ≤ Real.sqrt x*(4*Real.log (4*(x : ℝ))^2) * (2*Real.log (4*(x:ℝ))) :=
    mul_le_mul_of_nonneg_left hkey (by positivity)
  have hfinal : Real.sqrt x*(4*Real.log (4*(x : ℝ))^2) * (2*Real.log (4*(x:ℝ)))
      = 8*Real.sqrt x*Real.log (4*(x : ℝ))^3 := by ring
  linarith [hstep1, hstep2, hstep3, hstep4, hfinal]
