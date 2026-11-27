import Mathlib
import Conjectures.TwinPrimes.CofactorTwoLinearSieve
import PEqualNP.Outside.L_goldbach_coset_logrange_ap

namespace Conjectures.TwinPrimes.PrimeSquareMinusTwoUpperSieve_aux

noncomputable section

namespace AP


/-! ### Definitions -/

private noncomputable def th (a n : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range (n+1)).filter (fun k => k % 8 = a),
    (if k.Prime then Real.log (k:ℝ) else 0)

private noncomputable def g (n : ℕ) : ℝ :=
  if n ≤ 1 then 1 else 1 / ((n:ℝ) * Real.log (n:ℝ))

private def u (i : ℕ) : ℝ := if i = 0 then 0 else 1

private noncomputable def E (a n : ℕ) : ℝ := th a n - (n:ℝ)/4

private noncomputable def e (a i : ℕ) : ℝ :=
  if i.Prime ∧ i % 8 = a then Real.log (i:ℝ) else 0

/-! ### Elementary facts about `g` -/

private lemma g_of_two {n : ℕ} (hn : 2 ≤ n) : g n = 1 / ((n:ℝ) * Real.log (n:ℝ)) := by
  unfold g; split_ifs with h; omega; rfl

private lemma g_one : g 1 = 1 := by simp [g]

private lemma g_zero : g 0 = 1 := by simp [g]

private lemma u_one : u 1 = 1 := by simp [u]

private lemma u_of_pos {i : ℕ} (hi : i ≠ 0) : u i = 1 := by simp [u, hi]

private lemma g_antitone_of_two {n : ℕ} (hn : 2 ≤ n) : g (n+1) ≤ g n := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hL0 : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hL1 : 0 < Real.log ((n+1:ℕ):ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n+1))
  have h1 : (n:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.le_succ n
  have h2 : Real.log (n:ℝ) ≤ Real.log ((n+1:ℕ):ℝ) := Real.log_le_log hn0 h1
  have hmono : (n:ℝ) * Real.log (n:ℝ) ≤ ((n+1:ℕ):ℝ) * Real.log ((n+1:ℕ):ℝ) :=
    mul_le_mul h1 h2 hL0.le (by positivity)
  rw [g_of_two (by omega), g_of_two hn]
  exact one_div_le_one_div_of_le (by positivity) hmono

private lemma g_antitone (i : ℕ) : g (i+1) ≤ g i := by
  rcases i with _ | _ | i
  · rw [g_zero, g_one]
  · have h : (1:ℝ) ≤ (2:ℝ) * Real.log 2 := by linarith [Real.log_two_gt_d9]
    rw [g_one, g_of_two (by norm_num)]
    exact (div_le_one (by positivity)).mpr h
  · exact g_antitone_of_two (by omega)

private lemma log_succ_sub_log_le (i : ℕ) (hi : 1 ≤ i) :
    Real.log ((i+1:ℕ):ℝ) - Real.log (i:ℝ) ≤ 1/(i:ℝ) := by
  have hcast : ((i+1:ℕ):ℝ) = (i:ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hi0 : (0:ℝ) < (i:ℝ) := by exact_mod_cast (by omega : 0 < i)
  have hx : (0:ℝ) < ((i:ℝ)+1)/(i:ℝ) := by positivity
  have h := Real.log_le_sub_one_of_pos hx
  rw [Real.log_div (by positivity) hi0.ne'] at h
  have h2 : ((i:ℝ)+1)/(i:ℝ) - 1 = 1/(i:ℝ) := by field_simp; ring
  linarith

private lemma log_succ_sub_log_ge (i : ℕ) (hi : 1 ≤ i) :
    1 ≤ ((i+1:ℕ):ℝ) * (Real.log ((i+1:ℕ):ℝ) - Real.log (i:ℝ)) := by
  have hcast : ((i+1:ℕ):ℝ) = (i:ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hi0 : (0:ℝ) < (i:ℝ) := by exact_mod_cast (by omega : 0 < i)
  have hx : (0:ℝ) < ((i:ℝ)+1)/(i:ℝ) := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hx
  have hinv : (((i:ℝ)+1)/(i:ℝ))⁻¹ = (i:ℝ)/((i:ℝ)+1) := by rw [inv_div]
  rw [hinv, Real.log_div (by positivity) hi0.ne'] at h
  have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ (i:ℝ)+1)
  have h3 : ((i:ℝ)+1) * (1 - (i:ℝ)/((i:ℝ)+1)) = 1 := by field_simp; ring
  linarith

private lemma log_succ_le_two_log (i : ℕ) (hi : 2 ≤ i) :
    Real.log ((i+1:ℕ):ℝ) ≤ 2 * Real.log (i:ℝ) := by
  have hcast : ((i+1:ℕ):ℝ) = (i:ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have h := log_succ_sub_log_le i (by omega)
  rw [hcast] at h
  have hiR : (2:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi
  have hlog2 : (1:ℝ)/2 ≤ Real.log (i:ℝ) := by
    have h1 := Real.log_two_gt_d9
    have h2 := Real.log_le_log (by norm_num : (0:ℝ) < 2) hiR
    linarith
  have h3 : (1:ℝ)/(i:ℝ) ≤ 1/2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hiR
  linarith

private lemma two_le_log {n : ℕ} (hn : 9 ≤ n) : 2 ≤ Real.log (n:ℝ) := by
  have h1 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
    have h : (2:ℝ) = ((2:ℕ):ℝ) * 1 := by norm_num
    rw [h, Real.exp_nat_mul]
  have h3 : (9:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have h4 : Real.exp 2 ≤ (n:ℝ) := by
    rw [h2]; nlinarith [Real.exp_nonneg 1]
  rw [← Real.log_exp 2]
  exact Real.log_le_log (Real.exp_pos 2) h4

private lemma eight_le_cube_of_two_le {L : ℝ} (h : 2 ≤ L) : 8 ≤ L^3 := by
  have h2 : 4 ≤ L^2 := by nlinarith
  have h3 : L^3 = L^2 * L := by ring
  rw [h3]; nlinarith

private lemma one_le_cube_of_two_le {L : ℝ} (h : 2 ≤ L) : 1 ≤ L^3 := by
  have := eight_le_cube_of_two_le h; linarith

private lemma one_le_log_of_three {i : ℕ} (hi : 3 ≤ i) : 1 ≤ Real.log (i:ℝ) := by
  have h3 : (3:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi
  have hexp := Real.exp_one_lt_d9
  have h := Real.log_le_log (Real.exp_pos 1) (by linarith : Real.exp 1 ≤ (i:ℝ))
  rw [Real.log_exp] at h
  exact h

private lemma g_ge_loglog {i : ℕ} (hi : 2 ≤ i) :
    Real.log (Real.log ((i+1:ℕ):ℝ)) - Real.log (Real.log (i:ℝ)) ≤ g i := by
  have hcast : ((i+1:ℕ):ℝ) = (i:ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hi0 : (0:ℝ) < (i:ℝ) := by exact_mod_cast (by omega : 0 < i)
  have hL0 : 0 < Real.log (i:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < i))
  have hL1 : 0 < Real.log ((i:ℝ)+1) := Real.log_pos (by linarith)
  have hd1 := log_succ_sub_log_le i (by omega)
  rw [hcast] at hd1
  have hlog : Real.log (Real.log ((i:ℝ)+1)) - Real.log (Real.log (i:ℝ)) =
      Real.log (1 + (Real.log ((i:ℝ)+1) - Real.log (i:ℝ)) / Real.log (i:ℝ)) := by
    rw [(Real.log_div hL1.ne' hL0.ne').symm]
    congr 1
    field_simp; ring
  have hd0 : 0 ≤ Real.log ((i:ℝ)+1) - Real.log (i:ℝ) := by
    have h := Real.log_le_log hi0 (by linarith : (i:ℝ) ≤ (i:ℝ)+1); linarith
  have ht0 : 0 ≤ (Real.log ((i:ℝ)+1) - Real.log (i:ℝ)) / Real.log (i:ℝ) := by positivity
  have hstep := Real.log_le_sub_one_of_pos
    (by linarith : (0:ℝ) < 1 + (Real.log ((i:ℝ)+1) - Real.log (i:ℝ)) / Real.log (i:ℝ))
  have hdiv : (Real.log ((i:ℝ)+1) - Real.log (i:ℝ)) / Real.log (i:ℝ) ≤
      1 / ((i:ℝ) * Real.log (i:ℝ)) := by
    rw [div_le_div_iff₀ hL0 (by positivity)]
    have h := mul_le_mul_of_nonneg_right hd1 (by positivity : (0:ℝ) ≤ (i:ℝ) * Real.log (i:ℝ))
    have h2 : (1/(i:ℝ)) * ((i:ℝ) * Real.log (i:ℝ)) = Real.log (i:ℝ) := by field_simp
    linarith
  rw [g_of_two hi, hlog]
  linarith

private lemma g_sub_le {i : ℕ} (hi : 2 ≤ i) :
    g i - g (i+1) ≤ 2 / ((i:ℝ)^2 * Real.log (i:ℝ)) := by
  have hcast : ((i+1:ℕ):ℝ) = (i:ℝ) + 1 := by push_cast; ring
  have hi0 : (0:ℝ) < (i:ℝ) := by exact_mod_cast (by omega : 0 < i)
  have hL0 : 0 < Real.log (i:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < i))
  have hL1 : 0 < Real.log ((i:ℝ)+1) := Real.log_pos (by linarith)
  have hL1ge : 1 ≤ Real.log ((i:ℝ)+1) := by
    have h := one_le_log_of_three (i := i+1) (by omega)
    rwa [hcast] at h
  have hd := log_succ_sub_log_le i (by omega)
  rw [hcast] at hd
  have hmul : (i:ℝ) * (Real.log ((i:ℝ)+1) - Real.log (i:ℝ)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hd hi0.le
    have h2 : (i:ℝ) * (1/(i:ℝ)) = 1 := by field_simp
    linarith
  have hkey : (i:ℝ) * (((i:ℝ)+1) * Real.log ((i:ℝ)+1) - (i:ℝ) * Real.log (i:ℝ)) ≤
      2 * ((i:ℝ)+1) * Real.log ((i:ℝ)+1) := by
    have h1 : (i:ℝ) * (((i:ℝ)+1) * Real.log ((i:ℝ)+1) - (i:ℝ) * Real.log (i:ℝ)) =
        (i:ℝ) * Real.log ((i:ℝ)+1) +
          (i:ℝ) * ((i:ℝ) * (Real.log ((i:ℝ)+1) - Real.log (i:ℝ))) := by ring
    have h2 := mul_le_mul_of_nonneg_left hmul hi0.le
    have h3 : (i:ℝ) * Real.log ((i:ℝ)+1) + (i:ℝ) ≤
        2 * ((i:ℝ)+1) * Real.log ((i:ℝ)+1) := by nlinarith
    linarith
  rw [g_of_two hi, g_of_two (by omega), hcast]
  have hpos3 : (0:ℝ) < (i:ℝ)^2 * Real.log (i:ℝ) := by positivity
  calc 1 / ((i:ℝ) * Real.log (i:ℝ)) - 1 / (((i:ℝ)+1) * Real.log ((i:ℝ)+1))
      = (((i:ℝ)+1) * Real.log ((i:ℝ)+1) - (i:ℝ) * Real.log (i:ℝ)) /
          ((i:ℝ) * Real.log (i:ℝ) * (((i:ℝ)+1) * Real.log ((i:ℝ)+1))) := by
        field_simp
    _ ≤ 2 / ((i:ℝ)^2 * Real.log (i:ℝ)) := by
        rw [div_le_div_iff₀ (by positivity) hpos3]
        have h := mul_le_mul_of_nonneg_left hkey (by positivity : (0:ℝ) ≤ (i:ℝ) * Real.log (i:ℝ))
        have hl : (i:ℝ) * Real.log (i:ℝ) * ((i:ℝ) * (((i:ℝ)+1) * Real.log ((i:ℝ)+1) -
            (i:ℝ) * Real.log (i:ℝ))) =
            (((i:ℝ)+1) * Real.log ((i:ℝ)+1) - (i:ℝ) * Real.log (i:ℝ)) *
              ((i:ℝ)^2 * Real.log (i:ℝ)) := by ring
        have hr : (i:ℝ) * Real.log (i:ℝ) * (2 * ((i:ℝ)+1) * Real.log ((i:ℝ)+1)) =
            2 * ((i:ℝ) * Real.log (i:ℝ) * (((i:ℝ)+1) * Real.log ((i:ℝ)+1))) := by ring
        linarith

private lemma tele_bound {i : ℕ} (hi : 2 ≤ i) :
    1 / ((i:ℝ) * (Real.log (i:ℝ))^2) ≤
      4 * (1 / Real.log (i:ℝ) - 1 / Real.log ((i+1:ℕ):ℝ)) := by
  have hcast : ((i+1:ℕ):ℝ) = (i:ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hi0 : (0:ℝ) < (i:ℝ) := by exact_mod_cast (by omega : 0 < i)
  have hL0 : 0 < Real.log (i:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < i))
  have hL1 : 0 < Real.log ((i:ℝ)+1) := Real.log_pos (by linarith)
  have hd := log_succ_sub_log_ge i (by omega)
  rw [hcast] at hd
  have hL1' := log_succ_le_two_log i hi
  rw [hcast] at hL1'
  have hnn : 0 ≤ Real.log ((i:ℝ)+1) - Real.log (i:ℝ) := by
    have h := Real.log_le_log hi0 (by linarith : (i:ℝ) ≤ (i:ℝ)+1); linarith
  have h1 : 1 ≤ (2:ℝ) * (i:ℝ) * (Real.log ((i:ℝ)+1) - Real.log (i:ℝ)) := by
    have h2 : ((i:ℝ)+1) ≤ 2 * (i:ℝ) := by
      have h' : (1:ℝ) ≤ (i:ℝ) := by exact_mod_cast (by omega)
      linarith
    have h3 : 0 ≤ (2 * (i:ℝ) - ((i:ℝ)+1)) * (Real.log ((i:ℝ)+1) - Real.log (i:ℝ)) :=
      mul_nonneg (by linarith) hnn
    nlinarith
  have hkey : Real.log ((i:ℝ)+1) ≤
      4 * (i:ℝ) * Real.log (i:ℝ) * (Real.log ((i:ℝ)+1) - Real.log (i:ℝ)) := by
    have h4 := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ 2 * Real.log (i:ℝ))
    have h5 : (2:ℝ) * Real.log (i:ℝ) * (2 * (i:ℝ) * (Real.log ((i:ℝ)+1) - Real.log (i:ℝ))) =
        4 * (i:ℝ) * Real.log (i:ℝ) * (Real.log ((i:ℝ)+1) - Real.log (i:ℝ)) := by ring
    linarith
  rw [div_sub_div (1:ℝ) (1:ℝ) hL0.ne' hL1.ne', ← mul_div_assoc]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h5 := mul_le_mul_of_nonneg_left hkey hL0.le
  have h6 : Real.log (i:ℝ) * (4 * (i:ℝ) * Real.log (i:ℝ) * (Real.log ((i:ℝ)+1) - Real.log (i:ℝ))) =
      4 * (Real.log ((i:ℝ)+1) - Real.log (i:ℝ)) * ((i:ℝ) * (Real.log (i:ℝ))^2) := by ring
  linarith

private lemma tail_term {C : ℝ} (hC : 0 ≤ C) {i : ℕ} (hi : 3 ≤ i) :
    C * (i:ℝ) / (Real.log (i:ℝ))^2 * (g i - g (i+1)) ≤
      8 * C * (1 / Real.log (i:ℝ) - 1 / Real.log ((i+1:ℕ):ℝ)) := by
  have hcast : ((i+1:ℕ):ℝ) = (i:ℝ) + 1 := by push_cast; ring
  have hi0 : (0:ℝ) < (i:ℝ) := by exact_mod_cast (by omega : 0 < i)
  have hL0 : 0 < Real.log (i:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < i))
  have hL0ge : 1 ≤ Real.log (i:ℝ) := one_le_log_of_three hi
  have hgs := g_sub_le (by omega : 2 ≤ i)
  have h1 := mul_le_mul_of_nonneg_left hgs (by positivity : (0:ℝ) ≤ C * (i:ℝ) / (Real.log (i:ℝ))^2)
  have h2 : C * (i:ℝ) / (Real.log (i:ℝ))^2 * (2 / ((i:ℝ)^2 * Real.log (i:ℝ))) =
      2 * C / ((i:ℝ) * (Real.log (i:ℝ))^3) := by field_simp
  have h3 : (2:ℝ) * C / ((i:ℝ) * (Real.log (i:ℝ))^3) ≤
      2 * C / ((i:ℝ) * (Real.log (i:ℝ))^2) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have : (Real.log (i:ℝ))^2 ≤ (Real.log (i:ℝ))^3 := by nlinarith
    nlinarith
  have h5 := tele_bound (by omega : 2 ≤ i)
  rw [hcast] at h5
  have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : (0:ℝ) ≤ 2 * C)
  have h7 : (2:ℝ) * C * (4 * (1 / Real.log (i:ℝ) - 1 / Real.log ((i:ℝ)+1))) =
      8 * C * (1 / Real.log (i:ℝ) - 1 / Real.log ((i:ℝ)+1)) := by ring
  have h8 : (2:ℝ) * C / ((i:ℝ) * (Real.log (i:ℝ))^2) =
      2 * C * (1 / ((i:ℝ) * (Real.log (i:ℝ))^2)) := by field_simp
  rw [hcast]
  linarith

/-! ### Abel summation -/

private lemma sum_e_eq_th (a N : ℕ) : ∑ i ∈ Finset.range (N+1), e a i = th a N := by
  unfold th
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hm : i % 8 = a
  · by_cases hp : i.Prime <;> simp [e, hm, hp]
  · simp [e, hm]

private lemma abel (a N : ℕ) :
    ∑ i ∈ Finset.range (N+1), g i * e a i =
      g N * th a N - ∑ i ∈ Finset.range N, (g (i+1) - g i) * th a i := by
  have h := Finset.sum_range_by_parts (M := ℝ) (R := ℝ) g (e a) (N + 1)
  rw [Nat.add_sub_cancel] at h
  simp only [smul_eq_mul] at h
  rw [h]
  simp only [sum_e_eq_th]

private lemma lhs_eq (a N : ℕ) (ha : a = 1 ∨ a = 3 ∨ a = 5 ∨ a = 7) :
    ∑ i ∈ Finset.range (N+1), g i * e a i =
      ∑ p ∈ (Finset.range (N+1)).filter (fun p => Nat.Prime p ∧ p % 8 = a), (1:ℝ)/(p:ℝ) := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i.Prime ∧ i % 8 = a
  · obtain ⟨hp, hm⟩ := h
    have hi3 : 3 ≤ i := by
      have h2 : i ≠ 2 := by
        intro h2; rw [h2] at hm; omega
      have := Nat.Prime.two_le hp; omega
    have hne : ¬ (i ≤ 1) := by omega
    have hlog : Real.log (i:ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < i))).ne'
    have hi : (i:ℝ) ≠ 0 := by exact_mod_cast (by omega : i ≠ 0)
    simp [e, hp, hm, g, hne]
    field_simp
  · simp [e, h]

private lemma sum_u (n : ℕ) (hn : 1 ≤ n) : ∑ i ∈ Finset.range n, u i = (n:ℝ) - 1 := by
  have h : ∀ i, u i = 1 - (if i = 0 then (1:ℝ) else 0) := by
    intro i; by_cases hi : i = 0 <;> simp [u, hi]
  simp_rw [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Finset.sum_ite_eq']
  have hmem : 0 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  rw [ite_eq_left_iff.mpr (fun h => absurd hmem h)]
  ring

private lemma main_part (N : ℕ) :
    (N:ℝ) * g N - ∑ i ∈ Finset.range N, (g (i+1) - g i) * (i:ℝ) =
      ∑ i ∈ Finset.range (N+1), g i * u i := by
  have h := Finset.sum_range_by_parts (M := ℝ) (R := ℝ) g u (N + 1)
  rw [Nat.add_sub_cancel] at h
  simp only [smul_eq_mul] at h
  rw [h]
  have h1 : ∑ i ∈ Finset.range (N+1), u i = (N:ℝ) := by
    rw [sum_u (N+1) (by omega)]; push_cast; ring
  have h2 : ∀ i, ∑ j ∈ Finset.range (i+1), u j = (i:ℝ) := by
    intro i; rw [sum_u (i+1) (by omega)]; push_cast; ring
  simp only [h1, h2]
  ring

private lemma main_lower {N : ℕ} (hN : 2 ≤ N) :
    Real.log (Real.log (N:ℝ)) ≤ ∑ i ∈ Finset.range (N+1), g i * u i := by
  have hf : ∀ i ∈ Finset.range (N+1),
      Real.log (Real.log ((i+1:ℕ):ℝ)) - Real.log (Real.log (i:ℝ)) ≤ g i * u i := by
    intro i _
    by_cases h0 : i = 0
    · subst h0; simp [u, g, Real.log_one, Real.log_zero]
    · rw [u_of_pos h0, mul_one]
      by_cases h1 : i = 1
      · subst h1
        have h11 : ((1+1:ℕ):ℝ) = (2:ℝ) := by push_cast; ring
        have hlog1 : Real.log (Real.log ((1:ℕ):ℝ)) = 0 := by
          rw [Nat.cast_one, Real.log_one, Real.log_zero]
        rw [h11, hlog1, sub_zero, g_one]
        have hpos : 0 < Real.log (2:ℝ) := by linarith [Real.log_two_gt_d9]
        have hle : Real.log (2:ℝ) ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
        have : Real.log (Real.log (2:ℝ)) ≤ 0 := by
          calc Real.log (Real.log (2:ℝ)) ≤ Real.log 1 := Real.log_le_log hpos hle
            _ = 0 := Real.log_one
        linarith
      · exact g_ge_loglog (by omega)
  have h1 : ∑ i ∈ Finset.range (N+1),
      (Real.log (Real.log ((i+1:ℕ):ℝ)) - Real.log (Real.log (i:ℝ))) =
      Real.log (Real.log ((N+1:ℕ):ℝ)) - Real.log (Real.log ((0:ℕ):ℝ)) :=
    Finset.sum_range_sub (fun i => Real.log (Real.log (i:ℝ))) (N+1)
  have hlog0 : Real.log (Real.log ((0:ℕ):ℝ)) = 0 := by
    rw [Nat.cast_zero, Real.log_zero, Real.log_zero]
  calc Real.log (Real.log (N:ℝ)) ≤ Real.log (Real.log ((N+1:ℕ):ℝ)) :=
        Real.log_le_log (Real.log_pos (by exact_mod_cast (by omega : 1 < N)))
          (Real.log_le_log (by exact_mod_cast (by omega : 0 < N)) (by exact_mod_cast Nat.le_succ N))
    _ ≤ Real.log (Real.log ((N+1:ℕ):ℝ)) - Real.log (Real.log ((0:ℕ):ℝ)) := by
        rw [hlog0]; linarith
    _ = ∑ i ∈ Finset.range (N+1),
          (Real.log (Real.log ((i+1:ℕ):ℝ)) - Real.log (Real.log (i:ℝ))) := h1.symm
    _ ≤ ∑ i ∈ Finset.range (N+1), g i * u i := Finset.sum_le_sum hf

/-! ### The arithmetic-progression input -/

private lemma ap_bound (a : ℕ) (ha : a = 1 ∨ a = 3 ∨ a = 5 ∨ a = 7) :
    ∃ C : ℝ, 0 < C ∧ ∃ X0 : ℕ, 9 ≤ X0 ∧ ∀ n : ℕ, X0 ≤ n →
      |th a n - (n:ℝ)/4| ≤ C * (n:ℝ) / (Real.log (n:ℝ))^2 := by
  obtain ⟨C, hC, X, hX⟩ := PEqualNP.Outside.L_goldbach_coset_logrange_ap 3 2
  refine ⟨C, hC, max X 9, le_max_right _ _, ?_⟩
  intro n hn
  have hn9 : 9 ≤ n := le_trans (le_max_right _ _) hn
  have hnX : X ≤ n := le_trans (le_max_left _ _) hn
  have hlog2 := two_le_log hn9
  have h8 : (8:ℝ) ≤ (Real.log (n:ℝ))^3 := eight_le_cube_of_two_le hlog2
  have htot : (8:ℕ).totient = 4 := by decide
  have h := hX n hnX 8 (by norm_num) h8 a (by omega)
    (by rcases ha with rfl | rfl | rfl | rfl <;> decide)
  rw [htot] at h
  exact h

/-! ### The theorem -/

theorem ap_recip_lower (a : ℕ) (ha : a = 1 ∨ a = 3 ∨ a = 5 ∨ a = 7) :
    ∃ K : ℝ, ∀ y : ℕ, 3 ≤ y →
      (1/4 : ℝ) * Real.log (Real.log (y : ℝ)) ≤
        K + ∑ p ∈ (Finset.range (y + 1)).filter (fun p => Nat.Prime p ∧ p % 8 = a),
          (1 : ℝ) / (p : ℝ) := by
  obtain ⟨C, hC, X0, hX0, hAP⟩ := ap_bound a ha
  let M0 : ℝ := (X0:ℝ) + 1
  refine ⟨max ((1/4) * Real.log (Real.log (X0:ℝ))) (M0 + 5 * C), ?_⟩
  intro y hy
  have hS0 : 0 ≤ ∑ p ∈ (Finset.range (y + 1)).filter (fun p => Nat.Prime p ∧ p % 8 = a),
      (1:ℝ) / (p:ℝ) := Finset.sum_nonneg (fun p _ => by positivity)
  by_cases hyX : X0 ≤ y
  · -- the large range: Abel summation
    have hy9 : 9 ≤ y := le_trans hX0 hyX
    have hS : (∑ p ∈ (Finset.range (y+1)).filter (fun p => Nat.Prime p ∧ p % 8 = a),
        (1:ℝ)/(p:ℝ)) =
        (1/4) * (∑ i ∈ Finset.range (y+1), g i * u i) + g y * E a y -
          ∑ i ∈ Finset.range y, (g (i+1) - g i) * E a i := by
      rw [← lhs_eq a y ha, abel a y]
      have hsplit : (∑ i ∈ Finset.range y, (g (i+1) - g i) * th a i) =
          (1/4) * (∑ i ∈ Finset.range y, (g (i+1) - g i) * (i:ℝ)) +
            ∑ i ∈ Finset.range y, (g (i+1) - g i) * E a i := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hE : th a i = (i:ℝ)/4 + E a i := by unfold E; ring
        rw [hE]; ring
      have hth : th a y = (y:ℝ)/4 + E a y := by unfold E; ring
      rw [hsplit, hth]
      linear_combination (1/4) * main_part y
    have hM : Real.log (Real.log (y:ℝ)) ≤ ∑ i ∈ Finset.range (y+1), g i * u i :=
      main_lower (by omega)
    -- the last term
    have hEy : |E a y| ≤ C * (y:ℝ) / (Real.log (y:ℝ))^2 := hAP y hyX
    have hgy : g y = 1 / ((y:ℝ) * Real.log (y:ℝ)) := g_of_two (by omega)
    have hgypos : 0 < g y := by
      rw [hgy]
      have := two_le_log hy9
      positivity
    have hbound : g y * |E a y| ≤ C := by
      calc g y * |E a y| ≤ g y * (C * (y:ℝ) / (Real.log (y:ℝ))^2) :=
            mul_le_mul_of_nonneg_left hEy hgypos.le
        _ = C / (Real.log (y:ℝ))^3 := by rw [hgy]; field_simp
        _ ≤ C := div_le_self hC.le (one_le_cube_of_two_le (two_le_log hy9))
    have hterm1 : -(C) ≤ g y * E a y := by
      have h1 : |g y * E a y| ≤ C := by rw [abs_mul, abs_of_pos hgypos]; exact hbound
      have h2 := neg_abs_le (g y * E a y)
      linarith
    -- the sum over i < y
    have hneg : (∑ i ∈ Finset.range y, (g i - g (i+1)) * E a i) =
        -(∑ i ∈ Finset.range y, (g (i+1) - g i) * E a i) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hsplit2 : (∑ i ∈ Finset.range y, (g i - g (i+1)) * E a i) =
        (∑ i ∈ Finset.range X0, (g i - g (i+1)) * E a i) +
          (∑ i ∈ Finset.Ico X0 y, (g i - g (i+1)) * E a i) := by
      rw [← Nat.Ico_zero_eq_range, ← Nat.Ico_zero_eq_range,
        ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le X0) hyX,
        Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive _ _ _)]
    have hhead : -(M0) ≤ ∑ i ∈ Finset.range X0, (g i - g (i+1)) * E a i := by
      have hper : ∀ i ∈ Finset.range X0, -(M0) * (g i - g (i+1)) ≤
          (g i - g (i+1)) * E a i := by
        intro i hi
        have hiX : i < X0 := Finset.mem_range.mp hi
        have hnn : 0 ≤ g i - g (i+1) := sub_nonneg.mpr (g_antitone i)
        have hE : -(M0) ≤ E a i := by
          have hthnn : 0 ≤ th a i := by
            unfold th
            refine Finset.sum_nonneg fun k _ => ?_
            by_cases hk : k.Prime
            · simp [hk]; exact Real.log_nonneg (by exact_mod_cast Nat.Prime.one_le hk)
            · simp [hk]
          have h1 : (i:ℝ)/4 ≤ M0 := by
            have h2 : (i:ℝ) ≤ (X0:ℝ) := by exact_mod_cast (le_of_lt hiX)
            have h3 : (0:ℝ) ≤ (X0:ℝ) := Nat.cast_nonneg X0
            dsimp [M0]; linarith
          unfold E; linarith
        have := mul_le_mul_of_nonneg_left hE hnn
        linarith
      have h1 : (-(M0)) * (∑ i ∈ Finset.range X0, (g i - g (i+1))) ≤
          ∑ i ∈ Finset.range X0, (g i - g (i+1)) * E a i := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum hper
      rw [Finset.sum_range_sub'] at h1
      have hgX0 : 0 ≤ g X0 := by rw [g_of_two (by omega)]; positivity
      have hM0 : 0 ≤ M0 := by dsimp [M0]; positivity
      have h2 : g 0 - g X0 ≤ 1 := by rw [g_zero]; linarith
      nlinarith
    have htel : (∑ i ∈ Finset.Ico X0 y,
        (1 / Real.log (i:ℝ) - 1 / Real.log ((i+1:ℕ):ℝ))) =
        1 / Real.log (X0:ℝ) - 1 / Real.log (y:ℝ) := by
      rw [Finset.sum_Ico_eq_sum_range]
      have h : ∀ k ∈ Finset.range (y - X0),
          (1 / Real.log ((X0 + k : ℕ):ℝ) - 1 / Real.log ((X0 + k + 1 : ℕ):ℝ)) =
          (1 / Real.log ((X0 + k : ℕ):ℝ) - 1 / Real.log ((X0 + (k+1) : ℕ):ℝ)) := by
        intro k _
        have hk : X0 + k + 1 = X0 + (k + 1) := by omega
        rw [hk]
      rw [Finset.sum_congr rfl h, Finset.sum_range_sub']
      have h1 : X0 + (y - X0) = y := Nat.add_sub_of_le hyX
      rw [h1]
      simp
    have htail : -(4 * C) ≤ ∑ i ∈ Finset.Ico X0 y, (g i - g (i+1)) * E a i := by
      have hper : ∀ i ∈ Finset.Ico X0 y,
          (-(8 * C)) * (1 / Real.log (i:ℝ) - 1 / Real.log ((i+1:ℕ):ℝ)) ≤
            (g i - g (i+1)) * E a i := by
        intro i hi
        have hiX : X0 ≤ i := (Finset.mem_Ico.mp hi).1
        have hi3 : 3 ≤ i := by omega
        have hEi : |E a i| ≤ C * (i:ℝ) / (Real.log (i:ℝ))^2 := hAP i hiX
        have hnn : 0 ≤ g i - g (i+1) := sub_nonneg.mpr (g_antitone i)
        have hstep : -(g i - g (i+1)) * |E a i| ≤ (g i - g (i+1)) * E a i := by
          have h := mul_le_mul_of_nonneg_left (neg_abs_le (E a i)) hnn
          linarith
        have h2 : (g i - g (i+1)) * |E a i| ≤
            C * (i:ℝ) / (Real.log (i:ℝ))^2 * (g i - g (i+1)) := by
          have h := mul_le_mul_of_nonneg_left hEi hnn
          linarith
        have h3 := tail_term hC.le hi3
        linarith
      have hsum : (-(8 * C)) * (∑ i ∈ Finset.Ico X0 y,
          (1 / Real.log (i:ℝ) - 1 / Real.log ((i+1:ℕ):ℝ))) ≤
          ∑ i ∈ Finset.Ico X0 y, (g i - g (i+1)) * E a i := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum hper
      rw [htel] at hsum
      have hX0log : 2 ≤ Real.log (X0:ℝ) := two_le_log hX0
      have h1 : 1 / Real.log (X0:ℝ) ≤ 1/2 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hX0log
      have h2 : 0 < 1 / Real.log (y:ℝ) := by
        have := two_le_log hy9; positivity
      have h3 : 1 / Real.log (X0:ℝ) - 1 / Real.log (y:ℝ) ≤ 1/2 := by linarith
      have h4 := mul_le_mul_of_nonpos_left h3 (by linarith : (-(8*C) : ℝ) ≤ 0)
      linarith
    have hterm2 : -(M0 + 4 * C) ≤ ∑ i ∈ Finset.range y, (g i - g (i+1)) * E a i := by
      rw [hsplit2]; linarith
    have h3 : -(M0 + 4 * C) ≤ -(∑ i ∈ Finset.range y, (g (i+1) - g i) * E a i) := by
      rw [← hneg]; exact hterm2
    have h4 : (1/4) * Real.log (Real.log (y:ℝ)) ≤
        (1/4) * (∑ i ∈ Finset.range (y+1), g i * u i) :=
      mul_le_mul_of_nonneg_left hM (by norm_num)
    have hfinal : (1/4) * Real.log (Real.log (y:ℝ)) ≤
        (M0 + 5 * C) + ∑ p ∈ (Finset.range (y+1)).filter (fun p => Nat.Prime p ∧ p % 8 = a),
          (1:ℝ)/(p:ℝ) := by
      linarith [hS]
    linarith [le_max_right ((1/4) * Real.log (Real.log (X0:ℝ))) (M0 + 5 * C)]
  · have hlog : Real.log (Real.log (y:ℝ)) ≤ Real.log (Real.log (X0:ℝ)) := by
      apply Real.log_le_log
      · exact Real.log_pos (by exact_mod_cast (by omega : 1 < y))
      · exact Real.log_le_log (by exact_mod_cast (by omega : 0 < y))
          (by exact_mod_cast (by omega : y ≤ X0))
    linarith [le_max_left ((1/4) * Real.log (Real.log (X0:ℝ))) (M0 + 5 * C)]


end AP

open scoped BigOperators
open Finset
open Conjectures.TwinPrimes.CofactorTwoLinearSieve_aux.OAI.Problem337

/-- Residue classes removed by the sieve for `r * (r^2 - 2)`. -/
def SqRoot (d : ℕ) :=
  {x : ZMod d // x * (x ^ 2 - 2) = 0}

/-- Local number of roots of `x * (x^2 - 2)` modulo `d`. -/
def sqRootCount (d : ℕ) : ℕ :=
  Nat.card (SqRoot d)

instance sqRootFintype (d : ℕ) [NeZero d] : Fintype (SqRoot d) :=
  inferInstanceAs (Fintype {x : ZMod d // x * (x ^ 2 - 2) = 0})

instance sqRootNonempty (d : ℕ) : Nonempty (SqRoot d) :=
  ⟨⟨0, by simp⟩⟩

/-- The Chinese remainder theorem separates the local root conditions. -/
def sqRootEquiv (a b : ℕ) (hab : a.Coprime b) :
    SqRoot (a * b) ≃ SqRoot a × SqRoot b := by
  let e := ZMod.chineseRemainder hab
  apply (Equiv.subtypeEquiv e.toEquiv ?_).trans Equiv.subtypeProdEquivProd
  intro x
  change x * ((x : ZMod (a * b)) ^ 2 - 2) = 0 ↔
    (e x).1 * ((e x).1 ^ 2 - 2) = 0 ∧ (e x).2 * ((e x).2 ^ 2 - 2) = 0
  have h := e.injective.eq_iff (a := x * ((x : ZMod (a * b)) ^ 2 - 2)) (b := 0)
  rw [map_mul, map_sub, map_pow, map_ofNat, map_zero] at h
  constructor
  · intro hx
    have hz : (e x) * ((e x) ^ 2 - 2) = 0 := h.mpr hx
    constructor
    · have h1 := congrArg Prod.fst hz
      simpa using h1
    · have h2 := congrArg Prod.snd hz
      simpa using h2
  · rintro ⟨h1, h2⟩
    apply h.mp
    ext
    · simpa using h1
    · simpa using h2

theorem sqRootCount_mul (a b : ℕ) (hab : a.Coprime b) :
    sqRootCount (a * b) = sqRootCount a * sqRootCount b := by
  unfold sqRootCount
  rw [Nat.card_congr (sqRootEquiv a b hab), Nat.card_prod]

@[simp] theorem sqRootCount_one : sqRootCount 1 = 1 := by
  unfold sqRootCount SqRoot
  have e : {x : ZMod 1 // x * (x ^ 2 - 2) = 0} ≃ ZMod 1 :=
    Equiv.subtypeUnivEquiv (fun x => Subsingleton.elim _ _)
  rw [Nat.card_congr e, Nat.card_zmod]

theorem sqRootCount_pos (d : ℕ) [NeZero d] : 0 < sqRootCount d := Nat.card_pos

private lemma zmod_two_eq_zero_iff (p : ℕ) : (2 : ZMod p) = 0 ↔ p ∣ 2 := by
  constructor
  · intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by simpa using h
    exact (ZMod.natCast_eq_zero_iff 2 p).mp h'
  · intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff 2 p).mpr h
    simpa using h'

private lemma prime_eq_two_of_two_dvd {p : ℕ} (hp : p.Prime) (hd : 2 ∣ p) : p = 2 := by
  rcases hp.eq_one_or_self_of_dvd 2 hd with h | h
  · omega
  · exact h.symm

/-- At an odd prime the roots are zero and the two square roots of two, when they exist. -/
theorem sqRootCount_prime (p : ℕ) (hp : p.Prime) :
    sqRootCount p = if p = 2 then 1 else (if p % 8 = 1 ∨ p % 8 = 7 then 3 else 1) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard0 : sqRootCount p =
      (Finset.univ.filter (fun x : ZMod p => x * (x ^ 2 - 2) = 0)).card := by
    unfold sqRootCount SqRoot
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard0]
  by_cases h2 : p = 2
  · subst h2
    have hz : (2 : ZMod 2) = 0 := by
      have hz' : ((2 : ℕ) : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff 2 2).mpr (dvd_refl 2)
      simpa using hz'
    have hfilter : (Finset.univ.filter (fun x : ZMod 2 => x * (x ^ 2 - 2) = 0)) = {0} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [hz, sub_zero]
      constructor
      · intro h
        rcases mul_eq_zero.mp h with h0 | h0
        · exact h0
        · exact sq_eq_zero_iff.mp h0
      · rintro rfl
        rw [zero_mul]
    rw [hfilter]
    norm_num
  · have hodd : ¬ (2 ∣ p) := fun hd => h2 (prime_eq_two_of_two_dvd hp hd)
    have htwo : (2 : ZMod p) ≠ 0 := by
      intro h
      have hd : p ∣ 2 := (zmod_two_eq_zero_iff p).mp h
      have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
      have := hp.two_le
      exact h2 (by omega)
    have hsplit : (Finset.univ.filter (fun x : ZMod p => x * (x ^ 2 - 2) = 0)) =
        insert 0 (Finset.univ.filter (fun x : ZMod p => x ^ 2 = 2)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro h
        rcases mul_eq_zero.mp h with h0 | h0
        · exact Or.inl h0
        · exact Or.inr (sub_eq_zero.mp h0)
      · rintro (rfl | h)
        · rw [zero_mul]
        · exact mul_eq_zero.mpr (Or.inr (sub_eq_zero.mpr h))
    have h0notmem : (0 : ZMod p) ∉ (Finset.univ.filter (fun x : ZMod p => x ^ 2 = 2)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro h
      have h' : (0 : ZMod p) ^ 2 = (2 : ZMod p) := h
      have h'' : (0 : ZMod p) = (2 : ZMod p) := by simpa using h'
      exact htwo h''.symm
    have hcount : (Finset.univ.filter (fun x : ZMod p => x * (x ^ 2 - 2) = 0)).card =
        1 + (Finset.univ.filter (fun x : ZMod p => x ^ 2 = 2)).card := by
      rw [hsplit, Finset.card_insert_of_notMem h0notmem]
      omega
    rw [hcount]
    have hmododd : p % 8 % 2 = 1 := by omega
    have hmodlt : p % 8 < 8 := Nat.mod_lt p (by norm_num)
    have hres : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
    have hisq : IsSquare (2 : ZMod p) ↔ p % 8 ≠ 3 ∧ p % 8 ≠ 5 := by
      have h := FiniteField.isSquare_two_iff (F := ZMod p)
      rwa [ZMod.card p] at h
    by_cases hsq2 : IsSquare (2 : ZMod p)
    · have hmod : p % 8 ≠ 3 ∧ p % 8 ≠ 5 := hisq.mp hsq2
      have hfinal : p % 8 = 1 ∨ p % 8 = 7 := by omega
      rw [if_neg h2, if_pos hfinal]
      obtain ⟨r, hr0⟩ := hsq2
      have hr : r ^ 2 = 2 := by rw [sq]; exact hr0.symm
      have hrne : r ≠ 0 := by
        intro h
        have h1 : (0 : ZMod p) ^ 2 = (2 : ZMod p) := by rw [← h]; exact hr
        have h2' : (0 : ZMod p) = (2 : ZMod p) := by simpa using h1
        exact htwo h2'.symm
      have hreq : (Finset.univ.filter (fun x : ZMod p => x ^ 2 = 2)) = {r, -r} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · intro hx
          have hfac : (x - r) * (x + r) = 0 := by
            calc (x - r) * (x + r) = x ^ 2 - r ^ 2 := by ring
              _ = 0 := by rw [hx, hr]; ring
          rcases mul_eq_zero.mp hfac with h1 | h1
          · exact Or.inl (sub_eq_zero.mp h1)
          · exact Or.inr (eq_neg_of_add_eq_zero_left h1)
        · rintro (rfl | rfl)
          · exact hr
          · rw [neg_sq]; exact hr
      rw [hreq]
      have hne : r ≠ -r := by
        intro h
        have hsum : (2 : ZMod p) * r = 0 := by
          have h1 : r + r = -r + r := congrArg (fun t => t + r) h
          have h2 : r + r = 0 := by rw [h1, neg_add_cancel]
          linear_combination h2
        rcases mul_eq_zero.mp hsum with h1 | h1
        · exact htwo h1
        · exact hrne h1
      rw [Finset.card_pair hne]
    · have hmod : ¬ (p % 8 ≠ 3 ∧ p % 8 ≠ 5) := fun hh => hsq2 (hisq.mpr hh)
      have hfinal : ¬ (p % 8 = 1 ∨ p % 8 = 7) := by omega
      rw [if_neg h2, if_neg hfinal]
      have hemp : (Finset.univ.filter (fun x : ZMod p => x ^ 2 = 2)) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        exact hsq2 ⟨x, by rw [← sq]; exact hx.symm⟩
      rw [hemp]
      norm_num


theorem sqRootCount_prime_le_three (p : ℕ) (hp : p.Prime) : sqRootCount p ≤ 3 := by
  rw [sqRootCount_prime p hp]
  split_ifs <;> omega

theorem sqRootCount_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    sqRootCount (∏ p ∈ s, p) = ∏ p ∈ s, sqRootCount p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      have hpp := hs p (Finset.mem_insert_self p s)
      have hsp : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
      have hcop : p.Coprime (∏ q ∈ s, q) := by
        apply Nat.Coprime.prod_right
        intro q hq
        apply (Nat.coprime_primes hpp (hsp q hq)).mpr
        intro heq
        exact hp (heq ▸ hq)
      rw [Finset.prod_insert hp, sqRootCount_mul p _ hcop, ih hsp, Finset.prod_insert hp]

theorem sqRootCount_squarefree (d : ℕ) (hd : Squarefree d) :
    sqRootCount d = ∏ p ∈ d.primeFactors, sqRootCount p := by
  calc
    sqRootCount d = sqRootCount (∏ p ∈ d.primeFactors, p) := by
          rw [Nat.prod_primeFactors_of_squarefree hd]
    _ = ∏ p ∈ d.primeFactors, sqRootCount p :=
      sqRootCount_prod_primes d.primeFactors (fun p hp => (Nat.mem_primeFactors.mp hp).1)

theorem sqRootCount_le_three_pow (d : ℕ) (hd : Squarefree d) :
    sqRootCount d ≤ 3 ^ d.primeFactors.card := by
  rw [sqRootCount_squarefree d hd]
  calc
    _ ≤ ∏ _p ∈ d.primeFactors, 3 := by
      apply Finset.prod_le_prod
      intro p hp
      exact sqRootCount_prime_le_three p (Nat.mem_primeFactors.mp hp).1
    _ = 3 ^ d.primeFactors.card := by
      rw [Finset.prod_const]

/-- Reduction modulo the least common multiple embeds the roots. -/
def sqRootLCMEmbedding (a b : ℕ) :
    SqRoot (a.lcm b) ↪ SqRoot a × SqRoot b := by
  let e : ZMod (a.lcm b) →+* ZMod a × ZMod b :=
    ZMod.castHom (dvd_refl (a.lcm b)) _
  have einj : Function.Injective e := ZMod.castHom_injective _
  have he (x : SqRoot (a.lcm b)) :
      (e x.val).1 * ((e x.val).1 ^ 2 - 2) = 0 ∧
        (e x.val).2 * ((e x.val).2 ^ 2 - 2) = 0 := by
    have h := congrArg e x.property
    have h' : (e x.val) * ((e x.val) ^ 2 - 2) = 0 := by
      rw [map_mul, map_sub, map_pow, map_ofNat, map_zero] at h
      exact h
    exact ⟨by have h1 := congrArg Prod.fst h'; simpa using h1,
      by have h2 := congrArg Prod.snd h'; simpa using h2⟩
  refine ⟨fun x => (⟨(e x.val).1, (he x).1⟩, ⟨(e x.val).2, (he x).2⟩), ?_⟩
  intro x y hxy
  apply Subtype.ext
  apply einj
  apply Prod.ext
  · exact congrArg (fun z : SqRoot a × SqRoot b => z.1.val) hxy
  · exact congrArg (fun z : SqRoot a × SqRoot b => z.2.val) hxy

theorem sqRootCount_lcm_le (a b : ℕ) [NeZero a] [NeZero b] :
    sqRootCount (a.lcm b) ≤ sqRootCount a * sqRootCount b := by
  unfold sqRootCount
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective (sqRootLCMEmbedding a b)
    (sqRootLCMEmbedding a b).injective

/-- The exact finite local root density, normalized as an arithmetic function. -/
def sqDensity : ArithmeticFunction ℝ where
  toFun d := (sqRootCount d : ℝ) / (d : ℝ)
  map_zero' := by simp

@[simp] theorem sqDensity_apply (d : ℕ) :
    sqDensity d = (sqRootCount d : ℝ) / (d : ℝ) := rfl

theorem sqDensity_isMultiplicative : sqDensity.IsMultiplicative := by
  constructor
  · simp
  · intro a b hab
    simp only [sqDensity_apply, sqRootCount_mul a b hab, Nat.cast_mul, mul_div_mul_comm]

theorem sqDensity_prime (p : ℕ) (hp : p.Prime) :
    sqDensity p = ((if p = 2 then 1 else (if p % 8 = 1 ∨ p % 8 = 7 then 3 else 1) : ℕ) : ℝ) /
      (p : ℝ) := by
  rw [sqDensity_apply, sqRootCount_prime p hp]

theorem sqDensity_prime_pos (p : ℕ) (hp : p.Prime) : 0 < sqDensity p := by
  rw [sqDensity_apply]
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h := sqRootCount_pos p
  have hd : (0 : ℝ) < p := by exact_mod_cast hp.pos
  positivity

theorem sqDensity_prime_lt_one (p : ℕ) (hp : p.Prime) : sqDensity p < 1 := by
  rw [sqDensity_apply, div_lt_one (by exact_mod_cast hp.pos)]
  have h := sqRootCount_prime p hp
  have hlt : sqRootCount p < p := by
    by_cases h2 : p = 2
    · have h1 : sqRootCount p = 1 := by rw [h, if_pos h2]
      rw [h1, h2]
      decide
    · by_cases h8 : p % 8 = 1 ∨ p % 8 = 7
      · have h3 : sqRootCount p = 3 := by rw [h, if_neg h2, if_pos h8]
        rw [h3]
        by_contra hle
        have hsmall : p = 2 ∨ p = 3 := by
          have := hp.two_le
          omega
        rcases hsmall with rfl | rfl
        · revert h8; decide
        · revert h8; decide
      · have h1 : sqRootCount p = 1 := by rw [h, if_neg h2, if_neg h8]
        rw [h1]
        exact hp.one_lt
  exact_mod_cast hlt

/-- The multiplicity-preserving sieve for the quadratic square-minus-two sequence. -/
def sqSieve (U y : ℕ) : BoundingSieve :=
  PrimePairSieve.imageSieve (Finset.Ioc U (2 * U)) (fun r => r * (r ^ 2 - 2))
    (primorial y) (squarefree_primorial y) sqDensity sqDensity_isMultiplicative
    (fun p hp _ => sqDensity_prime_pos p hp)
    (fun p hp _ => sqDensity_prime_lt_one p hp)

theorem sqSieve_multSum (U y d : ℕ) :
    (sqSieve U y).multSum d =
      (((Finset.Ioc U (2 * U)).filter (fun r => d ∣ r * (r ^ 2 - 2))).card : ℝ) :=
  PrimePairSieve.imageSieve_multSum (Finset.Ioc U (2 * U)) (fun r => r * (r ^ 2 - 2))
    (primorial y) (squarefree_primorial y) sqDensity sqDensity_isMultiplicative
    (fun p hp _ => sqDensity_prime_pos p hp) (fun p hp _ => sqDensity_prime_lt_one p hp) d

theorem sqSieve_siftedSum (U y : ℕ) :
    (sqSieve U y).siftedSum =
      (((Finset.Ioc U (2 * U)).filter
        (fun r => (primorial y).Coprime (r * (r ^ 2 - 2)))).card : ℝ) :=
  PrimePairSieve.imageSieve_siftedSum (Finset.Ioc U (2 * U)) (fun r => r * (r ^ 2 - 2))
    (primorial y) (squarefree_primorial y) sqDensity sqDensity_isMultiplicative
    (fun p hp _ => sqDensity_prime_pos p hp) (fun p hp _ => sqDensity_prime_lt_one p hp)

theorem sqSieve_totalMass (U y : ℕ) : (sqSieve U y).totalMass = (U : ℝ) := by
  have h : (sqSieve U y).totalMass = (((Finset.Ioc U (2 * U)).card : ℕ) : ℝ) := rfl
  rw [h, Nat.card_Ioc]
  have : 2 * U - U = U := by omega
  rw [this]

theorem sqSieve_rem (U y d : ℕ) :
    (sqSieve U y).rem d =
      (((Finset.Ioc U (2 * U)).filter (fun r => d ∣ r * (r ^ 2 - 2))).card : ℝ) -
        sqDensity d * (U : ℝ) := by
  have hm := sqSieve_multSum U y d
  have ht := sqSieve_totalMass U y
  have hnu : (sqSieve U y).nu d = sqDensity d := rfl
  unfold BoundingSieve.rem
  rw [hm, ht, hnu]

/-- Divisibility by the polynomial value is a residue condition. -/
theorem dvd_iff_sqRoot (d r : ℕ) [NeZero d] (hr : 2 ≤ r) :
    d ∣ r * (r ^ 2 - 2) ↔ (r : ZMod d) * ((r : ZMod d) ^ 2 - 2) = 0 := by
  have hcast : ((r * (r ^ 2 - 2) : ℕ) : ZMod d) = (r : ZMod d) * ((r : ZMod d) ^ 2 - 2) := by
    rw [Nat.cast_mul, Nat.cast_sub (by nlinarith), Nat.cast_pow, Nat.cast_ofNat]
  rw [← hcast, ZMod.natCast_eq_zero_iff]

theorem sqSieve_rem_bound (U y d : ℕ) [NeZero d] (hU : 1 ≤ U) :
    |(sqSieve U y).rem d| ≤ sqRootCount d := by
  classical
  rw [sqSieve_rem]
  have hI : Finset.Ioc U (2 * U) = Finset.Ico (U + 1) ((U + 1) + U) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have hfilt : (Finset.Ioc U (2 * U)).filter (fun r => d ∣ r * (r ^ 2 - 2)) =
      (Finset.Ico (U + 1) ((U + 1) + U)).filter
        (fun r : ℕ => (r : ZMod d) * ((r : ZMod d) ^ 2 - 2) = 0) := by
    rw [← hI]
    apply Finset.filter_congr
    intro r hr
    have hr2 : 2 ≤ r := by have := (Finset.mem_Ioc.mp hr).1; omega
    exact dvd_iff_sqRoot d r hr2
  have hcard : (((Finset.Ioc U (2 * U)).filter (fun r => d ∣ r * (r ^ 2 - 2))).card : ℝ) =
      (((Finset.Ico (U + 1) ((U + 1) + U)).filter
        (fun r : ℕ => (r : ZMod d) * ((r : ZMod d) ^ 2 - 2) = 0)).card : ℝ) := by
    rw [hfilt]
  rw [hcard]
  have hcount : sqRootCount d =
      (Finset.univ.filter (fun x : ZMod d => x * (x ^ 2 - 2) = 0)).card := by
    unfold sqRootCount SqRoot
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hz := zmod_predicate_Ico_discrepancy d
    (fun x : ZMod d => x * (x ^ 2 - 2) = 0) (U + 1) U
  have hgoal :
      (((Finset.Ico (U + 1) ((U + 1) + U)).filter
        (fun r : ℕ => (r : ZMod d) * ((r : ZMod d) ^ 2 - 2) = 0)).card : ℝ) -
          sqDensity d * (U : ℝ) =
      (((Finset.Ico (U + 1) ((U + 1) + U)).filter
        (fun r : ℕ => (r : ZMod d) * ((r : ZMod d) ^ 2 - 2) = 0)).card : ℝ) -
          (U : ℝ) * (sqRootCount d : ℝ) / (d : ℝ) := by
    rw [sqDensity_apply]
    ring
  rw [hgoal, hcount]
  exact hz

/-- The factorizable remainder envelope with base three. -/
theorem sqSieve_rem_lcm_bound (U y : ℕ) (hU : 1 ≤ U)
    (a : ℕ) (ha : a ∈ (primorial y).divisors) (b : ℕ) (hb : b ∈ (primorial y).divisors) :
    |(sqSieve U y).rem (Nat.lcm a b)| ≤
      (3 : ℝ) ^ a.primeFactors.card * (3 : ℝ) ^ b.primeFactors.card := by
  let : NeZero a := ⟨(Nat.pos_of_mem_divisors ha).ne'⟩
  let : NeZero b := ⟨(Nat.pos_of_mem_divisors hb).ne'⟩
  let : NeZero (Nat.lcm a b) := ⟨Nat.lcm_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  have ha2 := sqRootCount_le_three_pow a
    ((squarefree_primorial y).squarefree_of_dvd (Nat.dvd_of_mem_divisors ha))
  have hb2 := sqRootCount_le_three_pow b
    ((squarefree_primorial y).squarefree_of_dvd (Nat.dvd_of_mem_divisors hb))
  calc
    _ ≤ (sqRootCount (Nat.lcm a b) : ℝ) := sqSieve_rem_bound U y _ hU
    _ ≤ (sqRootCount a : ℝ) * sqRootCount b := by
      exact_mod_cast sqRootCount_lcm_le a b
    _ ≤ _ := by exact_mod_cast Nat.mul_le_mul ha2 hb2


/-- The optimal weights have a logarithmically bounded weighted mass with base three. -/
theorem optimalWeight_primeFactor_mass_le_three (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    (∑ d ∈ s.prodPrimes.divisors, |SelbergOptimal.optimalWeight s z d| *
      (3 : ℝ) ^ d.primeFactors.card) ≤ (z : ℝ) * (1 + Real.log z) ^ 3 := by
  calc
    _ ≤ ∑ d ∈ s.prodPrimes.divisors,
        if d ≤ z then (3 : ℝ) ^ d.primeFactors.card else 0 := by
      apply sum_le_sum
      intro d hd
      by_cases hdz : d ≤ z
      · rw [ite_eq_left hdz]
        have hw : |SelbergOptimal.optimalWeight s z d| ≤ 1 := by
          rw [SelbergOptimal.optimalWeight_formula s z d (Nat.dvd_of_mem_divisors hd)]
          convert SelbergOptimal.abs_normalized_complement_le_one s hz
            (Nat.dvd_of_mem_divisors hd) using 1
          unfold SelbergOptimal.complementNormalizer
          congr 1
          ring
        simpa using mul_le_mul_of_nonneg_right hw
          (by positivity : 0 ≤ (3 : ℝ) ^ d.primeFactors.card)
      · rw [ite_eq_right hdz, SelbergOptimal.optimalWeight_eq_zero_of_lt s (lt_of_not_ge hdz)]
        simp
    _ = ∑ d ∈ s.prodPrimes.divisors.filter (fun d => d ≤ z),
        (3 : ℝ) ^ d.primeFactors.card := (sum_filter _ _).symm
    _ ≤ _ := SelbergError.sum_squarefree_pow_le _ 3 z
      (fun d hd => s.squarefree_of_mem_divisors_prodPrimes (mem_filter.mp hd).1)
      (by
        intro d hd
        obtain ⟨hdP, hdz⟩ := mem_filter.mp hd
        exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdP, hdz⟩)

/-- A dimension-three local remainder envelope gives an explicit logarithmic error. -/
theorem errSum_optimalWeight_le_log_three (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z)
    (hrem : ∀ a ∈ s.prodPrimes.divisors, ∀ b ∈ s.prodPrimes.divisors,
      |s.rem (Nat.lcm a b)| ≤
        (3 : ℝ) ^ a.primeFactors.card * (3 : ℝ) ^ b.primeFactors.card) :
    s.errSum (BoundingSieve.lambdaSquared (SelbergOptimal.optimalWeight s z)) ≤
      (z : ℝ) ^ 2 * (1 + Real.log z) ^ 6 := by
  calc
    _ ≤ (∑ d ∈ s.prodPrimes.divisors, |SelbergOptimal.optimalWeight s z d| *
        (3 : ℝ) ^ d.primeFactors.card) ^ 2 :=
      SelbergError.errSum_lambdaSquared_le_sq s (SelbergOptimal.optimalWeight s z)
        (fun d => (3 : ℝ) ^ d.primeFactors.card) hrem
    _ ≤ ((z : ℝ) * (1 + Real.log z) ^ 3) ^ 2 :=
      pow_le_pow_left₀ (sum_nonneg (by intros; positivity))
        (optimalWeight_primeFactor_mass_le_three s hz) 2
    _ = _ := by ring

/-- Fully optimized finite Selberg inequality with explicit logarithmic error, base three. -/
theorem siftedSum_le_log_error_three (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z)
    (hrem : ∀ a ∈ s.prodPrimes.divisors, ∀ b ∈ s.prodPrimes.divisors,
      |s.rem (Nat.lcm a b)| ≤
        (3 : ℝ) ^ a.primeFactors.card * (3 : ℝ) ^ b.primeFactors.card) :
    s.siftedSum ≤ s.totalMass / SelbergOptimal.normalizer s z +
      (z : ℝ) ^ 2 * (1 + Real.log z) ^ 6 :=
  (SelbergOptimal.siftedSum_le s hz).trans
    (add_le_add le_rfl (errSum_optimalWeight_le_log_three s hz hrem))

/-- The sifted count for the quadratic sequence is bounded by the Selberg main term. -/
theorem sq_sifted_le (U y z : ℕ) (hU : 1 ≤ U) (hz : 1 ≤ z) :
    (((Finset.Ioc U (2 * U)).filter
        (fun r => (primorial y).Coprime (r * (r ^ 2 - 2)))).card : ℝ) ≤
      (U : ℝ) / SelbergOptimal.normalizer (sqSieve U y) z +
        (z : ℝ) ^ 2 * (1 + Real.log z) ^ 6 := by
  have he := siftedSum_le_log_error_three (sqSieve U y) hz
    (fun a ha b hb => sqSieve_rem_lcm_bound U y hU a ha b hb)
  rwa [sqSieve_siftedSum, sqSieve_totalMass] at he


/-- The local sieve weight. -/
def wgt (p : ℕ) : ℝ := sqDensity p * (1 - sqDensity p)⁻¹

/-- The finite Euler product of local factors. -/
def mass (y : ℕ) : ℝ := ∏ p ∈ y.primesLE, (1 + wgt p)

def index (t : Finset ℕ) : ℕ := ∏ p ∈ t, p

def weight (t : Finset ℕ) : ℝ := ∏ p ∈ t, wgt p

theorem sqDensity_bounds (p : ℕ) (hp : p.Prime) :
    0 < sqDensity p ∧ sqDensity p < 1 :=
  ⟨sqDensity_prime_pos p hp, sqDensity_prime_lt_one p hp⟩

theorem wgt_pos (p : ℕ) (hp : p.Prime) : 0 < wgt p := by
  have h := sqDensity_bounds p hp
  exact mul_pos h.1 (inv_pos.mpr (by linarith [h.2]))

theorem wgt_ratio (p : ℕ) (hp : p.Prime) : wgt p / (1 + wgt p) = sqDensity p := by
  have h := (sqDensity_bounds p hp).2
  have hpos := wgt_pos p hp
  unfold wgt at *
  field_simp
  ring

theorem wgt_le (p : ℕ) (hp : p.Prime) : wgt p / (1 + wgt p) ≤ 3 / (p : ℝ) := by
  rw [wgt_ratio p hp, sqDensity_apply]
  have h := sqRootCount_prime_le_three p hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) hpR.le

/-- The Selberg normalizer is a sum over subsets of the sieving primes. -/
theorem normalizer_eq_powerset (U y z : ℕ) :
    SelbergOptimal.normalizer (sqSieve U y) z =
      ∑ t ∈ y.primesLE.powerset, if index t ≤ z then weight t else 0 := by
  classical
  let P := primorial y
  have prime (t : Finset ℕ) (ht : t ∈ y.primesLE.powerset) : ∀ p ∈ t, p.Prime :=
    fun p hp => Nat.prime_of_mem_primesLE ((Finset.mem_powerset.mp ht) hp)
  have hfac (t : Finset ℕ) (ht : t ∈ y.primesLE.powerset) :
      (index t).primeFactors = t := Nat.primeFactors_prod (prime t ht)
  have hmap : P.divisors = y.primesLE.powerset.image index := by
    ext d
    constructor
    · intro hd
      have hsq := (squarefree_primorial y).squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
      have hmono := Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) (primorial_ne_zero y)
      rw [primeFactors_primorial] at hmono
      exact Finset.mem_image.mpr ⟨d.primeFactors, Finset.mem_powerset.mpr hmono,
        Nat.prod_primeFactors_of_squarefree hsq⟩
    · rintro hd
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hd
      exact Nat.mem_divisors.mpr ⟨Finset.prod_dvd_prod_of_subset _ _ _
        (Finset.mem_powerset.mp ht), primorial_ne_zero y⟩
  unfold SelbergOptimal.normalizer
  change (∑ d ∈ P.divisors, if d ≤ z then (sqSieve U y).selbergTerms d else 0) = _
  rw [hmap, Finset.sum_image (fun a ha b hb hh =>
    (hfac a ha).symm.trans ((congrArg Nat.primeFactors hh).trans (hfac b hb)))]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [BoundingSieve.selbergTerms_apply]
  have hnu : ∀ d, (sqSieve U y).nu d = sqDensity d := fun d => rfl
  simp only [hnu]
  split_ifs
  · rw [hfac t ht, index, (sqDensity_isMultiplicative).map_prod_of_prime t (prime t ht)]
    unfold weight wgt
    rw [Finset.prod_mul_distrib]
  · rfl

/-- The truncated normalizer retains half of the Euler product at cutoff `y^12`. -/
theorem mass_le_two_mul_normalizer (U y : ℕ) (hy : 2 ≤ y) :
    mass y ≤ 2 * SelbergOptimal.normalizer (sqSieve U y) (y ^ 12) := by
  classical
  let T := y.primesLE.powerset
  let W := weight
  have wp (t : Finset ℕ) (ht : t ∈ T) : 0 ≤ W t :=
    Finset.prod_nonneg fun p hp =>
      (wgt_pos p (Nat.prime_of_mem_primesLE ((Finset.mem_powerset.mp ht) hp))).le
  have total : (∑ t ∈ T, W t) = mass y := by
    unfold mass
    exact (Finset.prod_one_add _).symm
  have heavy_point (t : Finset ℕ) (ht : t ∈ T) :
      (if y ^ 12 < index t then W t else 0) * (12 * Real.log y) ≤ W t * Real.log (index t) := by
    have hip : 0 < index t := Finset.prod_pos fun p hp =>
      (Nat.prime_of_mem_primesLE ((Finset.mem_powerset.mp ht) hp)).pos
    split
    · rename_i hl
      apply mul_le_mul_of_nonneg_left _ (wp t ht)
      have hlog := Real.log_le_log (show (0 : ℝ) < ((y ^ 12 : ℕ) : ℝ) by positivity)
        (show ((y ^ 12 : ℕ) : ℝ) ≤ index t by exact_mod_cast hl.le)
      simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using hlog
    · rw [zero_mul]
      exact mul_nonneg (wp t ht) (Real.log_nonneg (by exact_mod_cast hip))
  have mean := Conjectures.TwinPrimes.CofactorTwoLinearSieve_aux.CentralSelberg.powerset_moment
    y.primesLE wgt (fun p => Real.log (p : ℝ))
    (fun p hp => (wgt_pos p (Nat.prime_of_mem_primesLE hp)).le)
  have hsumlog (t : Finset ℕ) (ht : t ∈ T) :
      Real.log (index t) = ∑ p ∈ t, Real.log (p : ℝ) := by
    unfold index
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    exact_mod_cast (Nat.prime_of_mem_primesLE ((Finset.mem_powerset.mp ht) hp)).ne_zero
  have bound : (∑ p ∈ y.primesLE, wgt p / (1 + wgt p) * Real.log p) ≤ 6 * Real.log y := by
    calc
      _ ≤ ∑ p ∈ y.primesLE, 3 * (Real.log p / p) := by
        refine sum_le_sum fun p hp => ?_
        have hpP := Nat.prime_of_mem_primesLE hp
        have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpP.one_le)
        have hw := wgt_le p hpP
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hpP.pos
        calc
          wgt p / (1 + wgt p) * Real.log p ≤ (3 / (p : ℝ)) * Real.log p :=
            mul_le_mul_of_nonneg_right hw hlog
          _ = 3 * (Real.log p / p) := by ring
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        have hwh :=
          Conjectures.TwinPrimes.CofactorTwoLinearSieve_aux.CentralSelberg.weighted_harmonic
            y (by omega)
        linarith
  have hmass : 0 ≤ mass y := by
    unfold mass
    exact Finset.prod_nonneg (fun p hp => by
      linarith [wgt_pos p (Nat.prime_of_mem_primesLE hp)])
  have moment : (∑ t ∈ T, W t * Real.log (index t)) ≤ mass y * (6 * Real.log y) := by
    calc
      _ = ∑ t ∈ y.primesLE.powerset, (∏ p ∈ t, wgt p) * (∑ p ∈ t, Real.log p) :=
        sum_congr rfl (fun t ht => by rw [hsumlog t ht]; rfl)
      _ = _ := mean
      _ ≤ _ := mul_le_mul_of_nonneg_left bound hmass
  have hdiff : (∑ t ∈ T, if y ^ 12 < index t then W t else 0) =
      mass y - SelbergOptimal.normalizer (sqSieve U y) (y ^ 12) := by
    rw [← total, normalizer_eq_powerset U y (y ^ 12), ← Finset.sum_sub_distrib]
    apply sum_congr rfl
    intro t _
    by_cases h : index t ≤ y ^ 12
    · rw [if_neg (not_lt.mpr h), if_pos h]
      dsimp [W]
      ring
    · rw [if_pos (lt_of_not_ge h), if_neg h]
      dsimp [W]
      ring
  have hh := (sum_le_sum heavy_point).trans moment
  rw [← Finset.sum_mul, hdiff] at hh
  have hl : 0 < Real.log y := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  change mass y ≤ 2 * SelbergOptimal.normalizer (sqSieve U y) (y ^ 12)
  apply (le_of_mul_le_mul_right (a := Real.log y) ?_ hl)
  linarith only [hh]


/-- The Euler product dominates the exponential of the summed local densities. -/
theorem mass_ge_exp_sum (y : ℕ) :
    Real.exp (∑ p ∈ y.primesLE, sqDensity p) ≤ mass y := by
  unfold mass
  rw [Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro p _
    positivity
  · intro p hp
    have hpP := Nat.prime_of_mem_primesLE hp
    have h := sqDensity_bounds p hpP
    have hne : 1 - sqDensity p ≠ 0 := by linarith [h.2]
    have h1 : 1 + wgt p = (1 - sqDensity p)⁻¹ := by
      unfold wgt
      field_simp
      ring
    rw [h1]
    have h2 : 1 - sqDensity p ≤ Real.exp (-(sqDensity p)) := by
      have := Real.add_one_le_exp (-(sqDensity p))
      linarith
    have h3 : (Real.exp (-(sqDensity p)))⁻¹ ≤ (1 - sqDensity p)⁻¹ :=
      inv_anti₀ (by linarith [h.2]) h2
    rw [Real.exp_neg, inv_inv] at h3
    exact h3

/-- The harmonic sum of the local densities splits over the residue classes mod eight. -/
theorem sum_sqDensity_split (y : ℕ) :
    (∑ p ∈ y.primesLE, sqDensity p) =
      (if 2 ∈ y.primesLE then (1 : ℝ) / 2 else 0) +
        3 * (∑ p ∈ y.primesLE.filter (fun p => p % 8 = 1), (1 : ℝ) / (p : ℝ)) +
        3 * (∑ p ∈ y.primesLE.filter (fun p => p % 8 = 7), (1 : ℝ) / (p : ℝ)) +
        (∑ p ∈ y.primesLE.filter (fun p => p % 8 = 3), (1 : ℝ) / (p : ℝ)) +
        (∑ p ∈ y.primesLE.filter (fun p => p % 8 = 5), (1 : ℝ) / (p : ℝ)) := by
  classical
  have key (p : ℕ) (hp : p ∈ y.primesLE) : sqDensity p =
      (if p = 2 then (1 : ℝ) / 2 else 0) +
        3 * (if p % 8 = 1 then (1 : ℝ) / (p : ℝ) else 0) +
        3 * (if p % 8 = 7 then (1 : ℝ) / (p : ℝ) else 0) +
        (if p % 8 = 3 then (1 : ℝ) / (p : ℝ) else 0) +
        (if p % 8 = 5 then (1 : ℝ) / (p : ℝ) else 0) := by
    have hpP := Nat.prime_of_mem_primesLE hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpP.pos
    rw [sqDensity_prime p hpP]
    by_cases h2 : p = 2
    · subst h2
      have hmod : (2 : ℕ) % 8 = 2 := by norm_num
      simp [hmod, hpR.ne']
    · have hodd : ¬ (2 ∣ p) := by
        intro hd
        rcases hpP.eq_one_or_self_of_dvd 2 hd with h | h
        · omega
        · exact h2 h.symm
      have hmododd : p % 8 % 2 = 1 := by omega
      have hmodlt : p % 8 < 8 := Nat.mod_lt p (by norm_num)
      have hres : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
      rcases hres with h1 | h3 | h5 | h7
      · rw [h1]; simp [h2, hpR.ne'] <;> ring
      · rw [h3]; simp [h2, hpR.ne'] <;> ring
      · rw [h5]; simp [h2, hpR.ne'] <;> ring
      · rw [h7]; simp [h2, hpR.ne'] <;> ring
  have e2 : (∑ p ∈ y.primesLE, (if p = 2 then (1 : ℝ) / 2 else 0)) =
      if 2 ∈ y.primesLE then (1 : ℝ) / 2 else 0 := by
    by_cases h : 2 ∈ y.primesLE
    · rw [if_pos h]; simp [h]
    · rw [if_neg h]; simp [h]
  have eclass (a : ℕ) :
      (∑ p ∈ y.primesLE, (if p % 8 = a then (1 : ℝ) / (p : ℝ) else 0)) =
        ∑ p ∈ y.primesLE.filter (fun p => p % 8 = a), (1 : ℝ) / (p : ℝ) :=
    (Finset.sum_filter (fun p => p % 8 = a) (fun p => (1 : ℝ) / (p : ℝ))).symm
  calc
    (∑ p ∈ y.primesLE, sqDensity p) =
        ∑ p ∈ y.primesLE, ((if p = 2 then (1 : ℝ) / 2 else 0) +
          3 * (if p % 8 = 1 then (1 : ℝ) / (p : ℝ) else 0) +
          3 * (if p % 8 = 7 then (1 : ℝ) / (p : ℝ) else 0) +
          (if p % 8 = 3 then (1 : ℝ) / (p : ℝ) else 0) +
          (if p % 8 = 5 then (1 : ℝ) / (p : ℝ) else 0)) :=
      Finset.sum_congr rfl (fun p hp => key p hp)
    _ = (∑ p ∈ y.primesLE, (if p = 2 then (1 : ℝ) / 2 else 0)) +
          3 * (∑ p ∈ y.primesLE, (if p % 8 = 1 then (1 : ℝ) / (p : ℝ) else 0)) +
          3 * (∑ p ∈ y.primesLE, (if p % 8 = 7 then (1 : ℝ) / (p : ℝ) else 0)) +
          (∑ p ∈ y.primesLE, (if p % 8 = 3 then (1 : ℝ) / (p : ℝ) else 0)) +
          (∑ p ∈ y.primesLE, (if p % 8 = 5 then (1 : ℝ) / (p : ℝ) else 0)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = (if 2 ∈ y.primesLE then (1 : ℝ) / 2 else 0) +
          3 * (∑ p ∈ y.primesLE.filter (fun p => p % 8 = 1), (1 : ℝ) / (p : ℝ)) +
          3 * (∑ p ∈ y.primesLE.filter (fun p => p % 8 = 7), (1 : ℝ) / (p : ℝ)) +
          (∑ p ∈ y.primesLE.filter (fun p => p % 8 = 3), (1 : ℝ) / (p : ℝ)) +
          (∑ p ∈ y.primesLE.filter (fun p => p % 8 = 5), (1 : ℝ) / (p : ℝ)) := by
        rw [e2, eclass 1, eclass 7, eclass 3, eclass 5]

/-- Under the arithmetic-progression harmonic input, the Euler product is at least
a constant times the square of the logarithm. -/
theorem mass_lower (hAP : ∀ a : ℕ, (a = 1 ∨ a = 3 ∨ a = 5 ∨ a = 7) →
      ∃ K : ℝ, ∀ y : ℕ, 3 ≤ y →
        (1 / 4 : ℝ) * Real.log (Real.log (y : ℝ)) ≤
          K + ∑ p ∈ (Finset.range (y + 1)).filter (fun p => Nat.Prime p ∧ p % 8 = a),
            (1 : ℝ) / (p : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : ℕ, 5 ≤ y → c * (Real.log (y : ℝ)) ^ 2 ≤ mass y := by
  obtain ⟨K1, hK1⟩ := hAP 1 (Or.inl rfl)
  obtain ⟨K3, hK3⟩ := hAP 3 (Or.inr (Or.inl rfl))
  obtain ⟨K5, hK5⟩ := hAP 5 (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨K7, hK7⟩ := hAP 7 (Or.inr (Or.inr (Or.inr rfl)))
  let L1 : ℝ := max K1 0
  let L3 : ℝ := max K3 0
  let L5 : ℝ := max K5 0
  let L7 : ℝ := max K7 0
  have hL1 : 0 ≤ L1 := le_max_right _ _
  have hL3 : 0 ≤ L3 := le_max_right _ _
  have hL5 : 0 ≤ L5 := le_max_right _ _
  have hL7 : 0 ≤ L7 := le_max_right _ _
  refine ⟨Real.exp (-(8 * (L1 + L3 + L5 + L7))), Real.exp_pos _, ?_⟩
  intro y hy
  have hy3 : 3 ≤ y := by omega
  have hfilter (a : ℕ) :
      (Finset.range (y + 1)).filter (fun p => Nat.Prime p ∧ p % 8 = a) =
        y.primesLE.filter (fun p => p % 8 = a) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_primesLE]
    constructor
    · rintro ⟨hpy, hpp, hmod⟩
      exact ⟨⟨by omega, hpp⟩, hmod⟩
    · rintro ⟨⟨hpy, hpp⟩, hmod⟩
      exact ⟨by omega, hpp, hmod⟩
  have h1 : (1 / 4 : ℝ) * Real.log (Real.log (y : ℝ)) ≤
      L1 + ∑ p ∈ y.primesLE.filter (fun p => p % 8 = 1), (1 : ℝ) / (p : ℝ) := by
    have h := hK1 y hy3
    rw [hfilter 1] at h
    exact h.trans (add_le_add_left (le_max_left K1 0) _)
  have h3 : (1 / 4 : ℝ) * Real.log (Real.log (y : ℝ)) ≤
      L3 + ∑ p ∈ y.primesLE.filter (fun p => p % 8 = 3), (1 : ℝ) / (p : ℝ) := by
    have h := hK3 y hy3
    rw [hfilter 3] at h
    exact h.trans (add_le_add_left (le_max_left K3 0) _)
  have h5 : (1 / 4 : ℝ) * Real.log (Real.log (y : ℝ)) ≤
      L5 + ∑ p ∈ y.primesLE.filter (fun p => p % 8 = 5), (1 : ℝ) / (p : ℝ) := by
    have h := hK5 y hy3
    rw [hfilter 5] at h
    exact h.trans (add_le_add_left (le_max_left K5 0) _)
  have h7 : (1 / 4 : ℝ) * Real.log (Real.log (y : ℝ)) ≤
      L7 + ∑ p ∈ y.primesLE.filter (fun p => p % 8 = 7), (1 : ℝ) / (p : ℝ) := by
    have h := hK7 y hy3
    rw [hfilter 7] at h
    exact h.trans (add_le_add_left (le_max_left K7 0) _)
  have hsplit := sum_sqDensity_split y
  have hmem2 : 2 ∈ y.primesLE := Nat.mem_primesLE.mpr ⟨by omega, Nat.prime_two⟩
  rw [if_pos hmem2] at hsplit
  have hsum : 2 * Real.log (Real.log (y : ℝ)) ≤
      8 * (L1 + L3 + L5 + L7) + ∑ p ∈ y.primesLE, sqDensity p := by
    have h1' := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 3)
    have h7' := mul_le_mul_of_nonneg_left h7 (by norm_num : (0 : ℝ) ≤ 3)
    linarith
  have hmass := mass_ge_exp_sum y
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hexp : Real.exp (2 * Real.log (Real.log (y : ℝ))) = (Real.log (y : ℝ)) ^ 2 := by
    rw [show (2 : ℝ) * Real.log (Real.log (y : ℝ)) =
      Real.log ((Real.log (y : ℝ)) ^ 2) by rw [Real.log_pow]; ring]
    exact Real.exp_log (by positivity)
  have hmono : Real.exp (2 * Real.log (Real.log (y : ℝ))) ≤
      Real.exp (8 * (L1 + L3 + L5 + L7) + ∑ p ∈ y.primesLE, sqDensity p) :=
    Real.exp_le_exp.mpr (by linarith)
  have hexp2 : Real.exp (8 * (L1 + L3 + L5 + L7) + ∑ p ∈ y.primesLE, sqDensity p) =
      Real.exp (8 * (L1 + L3 + L5 + L7)) * Real.exp (∑ p ∈ y.primesLE, sqDensity p) :=
    Real.exp_add _ _
  have hmono' : (Real.log (y : ℝ)) ^ 2 ≤
      Real.exp (8 * (L1 + L3 + L5 + L7) + ∑ p ∈ y.primesLE, sqDensity p) := by
    rw [← hexp]
    exact hmono
  calc
    Real.exp (-(8 * (L1 + L3 + L5 + L7))) * (Real.log (y : ℝ)) ^ 2
        ≤ Real.exp (-(8 * (L1 + L3 + L5 + L7))) *
            Real.exp (8 * (L1 + L3 + L5 + L7) + ∑ p ∈ y.primesLE, sqDensity p) :=
          mul_le_mul_of_nonneg_left hmono' (Real.exp_pos _).le
    _ = Real.exp (∑ p ∈ y.primesLE, sqDensity p) := by
          rw [← Real.exp_add]
          congr 1
          ring
    _ ≤ mass y := hmass


/-- The truncated normalizer is at least a constant times `(log y)^2`. -/
theorem normalizer_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ (U y : ℕ), 5 ≤ y →
      c * (Real.log (y : ℝ)) ^ 2 ≤ SelbergOptimal.normalizer (sqSieve U y) (y ^ 12) := by
  obtain ⟨c, hc, hmass⟩ := mass_lower (fun a ha => AP.ap_recip_lower a ha)
  refine ⟨c / 2, by linarith, ?_⟩
  intro U y hy
  have h1 := mass_le_two_mul_normalizer U y (by omega)
  have h2 := hmass y hy
  linarith

open Filter Topology

set_option maxRecDepth 2000000 in
/-- A choice of the sieving level for which the error term is negligible. -/
theorem scales :
    ∀ᶠ U : ℕ in atTop, ∃ y : ℕ, 5 ≤ y ∧ y ≤ U ∧
       Real.log (U:ℝ) ≤ 64*Real.log ((y:ℝ)+1) ∧
       (((y^12:ℕ):ℝ)^2*(1+Real.log ((y^12:ℕ):ℝ))^6) * (Real.log (U:ℝ))^2 ≤ 64*(U:ℝ) := by
  have hs := (isLittleO_log_rpow_rpow_atTop (8:ℝ) (by norm_num : (0:ℝ)<1/2)).bound
    (by norm_num : (0:ℝ)<1)
  have hs' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hs
  have hl := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
  filter_upwards [hs', hl, eventually_ge_atTop (5^64:ℕ)] with U hU hlog hU64
  change 1 ≤ Real.log (U:ℝ) at hlog
  have hU0 : 0 < (U:ℝ) := by exact_mod_cast (show 0<U by omega)
  have hU1 : 1 ≤ (U:ℝ) := by linarith [show (5:ℝ)^64 ≤ U by exact_mod_cast hU64]
  have hbig : (Real.log U)^8 ≤ Real.sqrt U := by
    have hr : (U:ℝ)^(1/2:ℝ) = Real.sqrt U := (Real.sqrt_eq_rpow _).symm
    simpa only [Real.norm_eq_abs, Real.rpow_natCast_mul, Real.rpow_ofNat,
      abs_of_nonneg (by positivity : 0≤(Real.log U)^8),
      abs_of_nonneg (Real.rpow_nonneg hU0.le _), one_mul, hr,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hU
  let u : ℝ := (U:ℝ)^(1/64:ℝ)
  let y := ⌊u⌋₊
  have hu : 0≤u := Real.rpow_nonneg hU0.le _
  have hu64 : u^64 = U := by
    rw [show u^64 = (U:ℝ)^((1/64:ℝ)*64) from (Real.rpow_mul_natCast hU0.le _ _).symm]
    norm_num
  have hy5 : 5≤y := by
    apply (Nat.le_floor_iff hu).mpr
    by_contra! h
    have hp : u ^ (64 : ℕ) < (5 : ℝ) ^ (64 : ℕ) := pow_lt_pow_left₀ h hu (by norm_num)
    rw [hu64] at hp
    exact (not_lt_of_ge (show (5:ℝ)^64 ≤ U by exact_mod_cast hU64)) hp
  have hyU : y ≤ U := by
    have h1 : (y:ℝ) ≤ u := Nat.floor_le hu
    have h2 : u ≤ (U:ℝ) := by
      have hx := Real.rpow_le_rpow_of_exponent_le hU1 (show (1/64:ℝ) ≤ 1 by norm_num)
      simpa [u] using hx
    exact_mod_cast h1.trans h2
  have hyp : (0:ℝ)<y := by exact_mod_cast (show 0<y by omega)
  have hyr : (1:ℝ)≤y := by exact_mod_cast (show 1≤y by omega)
  have hlow := pow_le_pow_left₀ hyp.le (Nat.floor_le hu : (y:ℝ) ≤ u) 64
  have hhigh := pow_le_pow_left₀ hu (Nat.lt_floor_add_one u).le 64
  rw [hu64] at hlow hhigh
  have hylog : Real.log (U:ℝ) ≤ 64*Real.log ((y:ℝ)+1) := by
    have hh := Real.log_le_log hU0 hhigh
    simpa only [Real.log_pow, Nat.cast_ofNat, y] using hh
  have hy32 : (y:ℝ)^32 ≤ Real.sqrt U := by
    apply (Real.le_sqrt (by positivity) hU0.le).mpr
    convert hlow using 1 <;> ring
  have hy24a : (y:ℝ)^(24:ℕ) ≤ (y:ℝ)^(32:ℕ) := pow_le_pow_right₀ hyr (by norm_num)
  have hy24 : (y:ℝ)^24 ≤ Real.sqrt U := hy24a.trans hy32
  have hly : Real.log ((y^12:ℕ):ℝ) ≤ Real.log U := by
    apply Real.log_le_log (by positivity)
    rw [Nat.cast_pow]
    exact (pow_le_pow_right₀ hyr (by norm_num : 12≤64)).trans hlow
  have hp6 : (1+Real.log ((y^12:ℕ):ℝ))^6 ≤ (2*Real.log U)^6 :=
    pow_le_pow_left₀ (by have := Real.log_nonneg (show (1:ℝ)≤((y^12:ℕ):ℝ) by
      exact_mod_cast (Nat.one_le_pow _ _ (by omega : 1≤y))); linarith) (by linarith) _
  rw [Nat.cast_pow] at hp6
  have hsqr := Real.sq_sqrt hU0.le
  have hmain : Real.sqrt U*(Real.log U)^8 ≤ U := by
    nlinarith [mul_le_mul_of_nonneg_left hbig (Real.sqrt_nonneg U)]
  have h24 : ((y:ℝ)^12)^2 = (y:ℝ)^24 := by ring
  refine ⟨y, hy5, hyU, hylog, ?_⟩
  rw [Nat.cast_pow]
  calc
    _ ≤ ((y:ℝ)^24*(2*Real.log U)^6)*(Real.log U)^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      rw [h24]
      exact mul_le_mul (le_refl _) hp6 (by positivity) (by positivity)
    _ ≤ (Real.sqrt U*(2*Real.log U)^6)*(Real.log U)^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right hy24 (by positivity)
    _ = 64*(Real.sqrt U*(Real.log U)^8) := by ring
    _ ≤ 64*(U:ℝ) := by linarith

/-- Both factors of a prime pair avoid every prime up to the sieving level. -/
theorem prime_pair_coprime (U y r : ℕ) (hyU : y ≤ U) (hrI : r ∈ Finset.Ioc U (2 * U))
    (hrP : r.Prime) (hrQ : (r ^ 2 - 2).Prime) :
    (primorial y).Coprime (r * (r ^ 2 - 2)) := by
  have hrU : U < r := (Finset.mem_Ioc.mp hrI).1
  have hry : ¬ (r ∣ primorial y) := by
    intro hd
    have hmem : r ∈ (primorial y).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hrP, hd, primorial_ne_zero y⟩
    rw [primeFactors_primorial] at hmem
    have := (Nat.mem_primesLE.mp hmem).1
    omega
  have hq : y < r ^ 2 - 2 := by
    have hr2 : 2 ≤ r := hrP.two_le
    have hsq : 2 ≤ r ^ 2 := by nlinarith
    have hsub : r ^ 2 - 2 + 2 = r ^ 2 := Nat.sub_add_cancel hsq
    have hle : r ≤ r ^ 2 - 2 := by nlinarith
    omega
  have hqy : ¬ ((r ^ 2 - 2) ∣ primorial y) := by
    intro hd
    have hmem : r ^ 2 - 2 ∈ (primorial y).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hrQ, hd, primorial_ne_zero y⟩
    rw [primeFactors_primorial] at hmem
    have := (Nat.mem_primesLE.mp hmem).1
    omega
  exact ((hrP.coprime_iff_not_dvd.mpr hry).symm).mul_right
    ((hrQ.coprime_iff_not_dvd.mpr hqy).symm)

/-- The upper bound for prime pairs `r, r^2 - 2`. -/
theorem prime_square_minus_two_upper :
    ∃ C : ℝ, 0<C ∧ ∀ U : ℕ, 3≤U →
      (((Finset.Ioc U (2*U)).filter fun r => r.Prime ∧ (r^2-2).Prime).card : ℝ) ≤
        C*U/(Real.log U)^2 := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp scales
  obtain ⟨c, hc, hnorm⟩ := normalizer_lower
  refine ⟨16384 / c + 64 + (Real.log ((max X 3 : ℕ) : ℝ))^2, by positivity, ?_⟩
  intro U hU
  have hU1 : 1 ≤ U := by omega
  have hUpos : 0 < U := by omega
  have hlogUpos : 0 < Real.log U := Real.log_pos (by exact_mod_cast (show 1 < U by omega))
  have hcardIoc : (Finset.Ioc U (2 * U)).card = U := by
    rw [Nat.card_Ioc]
    omega
  rw [le_div_iff₀ (pow_pos hlogUpos 2)]
  by_cases hcase : U < max X 3
  · have hcardT : ((((Finset.Ioc U (2*U)).filter
        (fun r => r.Prime ∧ (r^2-2).Prime)).card : ℕ) : ℝ) ≤ (U : ℝ) := by
      have h1 : ((Finset.Ioc U (2*U)).filter
          (fun r => r.Prime ∧ (r^2-2).Prime)).card ≤ (Finset.Ioc U (2*U)).card := by
        apply Finset.card_le_card
        intro r hr
        exact (Finset.mem_filter.mp hr).1
      rw [hcardIoc] at h1
      exact_mod_cast h1
    have hmono : Real.log U ≤ Real.log ((max X 3 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast hUpos) (by exact_mod_cast (le_of_lt hcase))
    have hsq : (Real.log U)^2 ≤ (Real.log ((max X 3 : ℕ) : ℝ))^2 :=
      pow_le_pow_left₀ hlogUpos.le hmono 2
    calc _ ≤ (U:ℝ) * (Real.log U)^2 :=
          mul_le_mul_of_nonneg_right hcardT (sq_nonneg (Real.log U))
      _ ≤ (U:ℝ) * (Real.log ((max X 3 : ℕ) : ℝ))^2 :=
          mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg U)
      _ ≤ (16384 / c + 64 + (Real.log ((max X 3 : ℕ) : ℝ))^2) * (U:ℝ) := by
          calc (U:ℝ) * (Real.log ((max X 3 : ℕ) : ℝ))^2
              ≤ (U:ℝ) * (Real.log ((max X 3 : ℕ) : ℝ))^2 + (16384 / c + 64) * (U:ℝ) :=
                le_add_of_nonneg_right (by positivity)
            _ = (16384 / c + 64 + (Real.log ((max X 3 : ℕ) : ℝ))^2) * (U:ℝ) := by ring
  · have hcase' : max X 3 ≤ U := by omega
    obtain ⟨y, hy5, hyU, hlog, herr⟩ := hX U ((le_max_left X 3).trans hcase')
    have hzpos : 1 ≤ y ^ 12 := Nat.one_le_pow _ _ (by omega)
    set N := SelbergOptimal.normalizer (sqSieve U y) (y ^ 12)
    have hN : c * (Real.log (y : ℝ)) ^ 2 ≤ N := hnorm U y hy5
    have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN
    have hyle : Real.log ((y : ℝ) + 1) ≤ 2 * Real.log (y : ℝ) := by
      have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast (show 2 ≤ y by omega)
      have h1 : ((y : ℝ) + 1) ≤ (y : ℝ) ^ 2 := by nlinarith
      have h2 := Real.log_le_log (by positivity) h1
      rw [Real.log_pow, Nat.cast_ofNat] at h2
      exact h2
    have hsq1 : (Real.log U)^2 ≤ (64 * Real.log ((y : ℝ) + 1))^2 :=
      pow_le_pow_left₀ hlogUpos.le hlog 2
    have hsq2 : (Real.log ((y : ℝ) + 1))^2 ≤ 4 * (Real.log (y : ℝ))^2 := by
      nlinarith [hyle]
    have hDen : (Real.log U)^2 ≤ (16384 / c) * N := by
      calc (Real.log U)^2 ≤ (64 * Real.log ((y : ℝ) + 1))^2 := hsq1
        _ = 4096 * (Real.log ((y : ℝ) + 1))^2 := by ring
        _ ≤ 4096 * (4 * (Real.log (y : ℝ))^2) := mul_le_mul_of_nonneg_left hsq2 (by norm_num)
        _ = (16384 / c) * (c * (Real.log (y : ℝ))^2) := by field_simp; ring
        _ ≤ (16384 / c) * N := mul_le_mul_of_nonneg_left hN (by positivity)
    have hfirst : ((U : ℝ) / N) * (Real.log U)^2 ≤ (16384 / c) * (U : ℝ) := by
      calc _ ≤ ((U : ℝ) / N) * ((16384 / c) * N) :=
            mul_le_mul_of_nonneg_left hDen (by positivity)
        _ = _ := by field_simp
    have hsub : (Finset.Ioc U (2 * U)).filter (fun r => r.Prime ∧ (r ^ 2 - 2).Prime) ⊆
        (Finset.Ioc U (2 * U)).filter
          (fun r => (primorial y).Coprime (r * (r ^ 2 - 2))) := by
      intro r hr
      obtain ⟨hrI, hrP, hrQ⟩ := Finset.mem_filter.mp hr
      exact Finset.mem_filter.mpr ⟨hrI, prime_pair_coprime U y r hyU hrI hrP hrQ⟩
    have hcardle : ((((Finset.Ioc U (2 * U)).filter
        (fun r => r.Prime ∧ (r ^ 2 - 2).Prime)).card : ℕ) : ℝ) ≤
        (U : ℝ) / N + ((y ^ 12 : ℕ) : ℝ) ^ 2 * (1 + Real.log ((y ^ 12 : ℕ) : ℝ)) ^ 6 := by
      calc _ ≤ ((((Finset.Ioc U (2 * U)).filter
              (fun r => (primorial y).Coprime (r * (r ^ 2 - 2)))).card : ℕ) : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ _ := sq_sifted_le U y (y ^ 12) hU1 hzpos
    have hmul := mul_le_mul_of_nonneg_right hcardle (sq_nonneg (Real.log U))
    calc _ ≤ ((U : ℝ) / N + ((y ^ 12 : ℕ) : ℝ) ^ 2 * (1 + Real.log ((y ^ 12 : ℕ) : ℝ)) ^ 6) *
          (Real.log U)^2 := hmul
      _ = ((U : ℝ) / N) * (Real.log U)^2 +
          ((y ^ 12 : ℕ) : ℝ) ^ 2 * (1 + Real.log ((y ^ 12 : ℕ) : ℝ)) ^ 6 * (Real.log U)^2 := by ring
      _ ≤ (16384 / c) * (U : ℝ) + 64 * (U : ℝ) := add_le_add hfirst herr
      _ ≤ (16384 / c + 64 + (Real.log ((max X 3 : ℕ) : ℝ))^2) * (U : ℝ) := by
          calc (16384 / c) * (U : ℝ) + 64 * (U : ℝ) = (16384 / c + 64) * (U : ℝ) := by ring
            _ ≤ (16384 / c + 64) * (U : ℝ) +
                  (Real.log ((max X 3 : ℕ) : ℝ))^2 * (U : ℝ) :=
                le_add_of_nonneg_right
                  (mul_nonneg (sq_nonneg (Real.log ((max X 3 : ℕ) : ℝ))) (Nat.cast_nonneg U))
            _ = (16384 / c + 64 + (Real.log ((max X 3 : ℕ) : ℝ))^2) * (U : ℝ) := by ring

end
end Conjectures.TwinPrimes.PrimeSquareMinusTwoUpperSieve_aux

theorem Conjectures.TwinPrimes.PrimeSquareMinusTwoUpperSieve :
  ∃ C : ℝ, 0<C ∧ ∀ U : ℕ, 3≤U → (((Finset.Ioc U (2*U)).filter fun r => r.Prime ∧ (r^2-2).Prime).card : ℝ) ≤ C*U/(Real.log U)^2 :=
  Conjectures.TwinPrimes.PrimeSquareMinusTwoUpperSieve_aux.prime_square_minus_two_upper
