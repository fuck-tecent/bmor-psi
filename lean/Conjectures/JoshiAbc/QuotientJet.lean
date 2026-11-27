import Mathlib

open Filter

namespace Conjectures.JoshiAbc.QuotientJet_aux

lemma pow_zpow_int {K : Type} [GroupWithZero K] (r : K) (k : ℕ) (m : ℤ) :
    (r ^ k) ^ m = r ^ ((k : ℤ) * m) := by
  rw [← zpow_natCast, zpow_mul]

lemma expo14 (n : ℤ) : ((14 : ℕ) : ℤ) * (n * (n + 1) / 2) = 7 * n * (n + 1) := by
  have h := Int.ediv_mul_cancel (Int.two_dvd_mul_add_one n)
  have h14 : ((14 : ℕ) : ℤ) = 14 := by norm_num
  rw [h14]
  linarith [h]

lemma term1 {K : Type} [NontriviallyNormedField K] (r z : K) (hr : r ≠ 0) (n : ℤ) :
    (r ^ 14) ^ (n * (n + 1) / 2) * (r * z) ^ (2 * n + 1)
      = r ^ (7 * n * (n + 1) + (2 * n + 1)) * z ^ (2 * n + 1) := by
  have e1 : (r ^ 14) ^ (n * (n + 1) / 2) = r ^ (7 * n * (n + 1)) := by
    rw [pow_zpow_int, expo14]
  rw [mul_zpow, e1]
  have e3 := zpow_add₀ hr (7 * n * (n + 1)) (2 * n + 1)
  rw [e3]
  ring

lemma term2 {K : Type} [NontriviallyNormedField K] (r z : K) (hr : r ≠ 0) (n : ℤ) :
    (r ^ 14) ^ (n * (n + 1) / 2) * (r ^ 2 * z) ^ (2 * n + 1)
      = r ^ (7 * n * (n + 1) + 2 * (2 * n + 1)) * z ^ (2 * n + 1) := by
  have e1 : (r ^ 14) ^ (n * (n + 1) / 2) = r ^ (7 * n * (n + 1)) := by
    rw [pow_zpow_int, expo14]
  have e2 : (r ^ 2) ^ (2 * n + 1) = r ^ (2 * (2 * n + 1)) := by
    rw [pow_zpow_int, show ((2 : ℕ) : ℤ) = (2 : ℤ) by norm_num]
  rw [mul_zpow, e1, e2]
  have e3 := zpow_add₀ hr (7 * n * (n + 1)) (2 * (2 * n + 1))
  rw [e3]
  ring

lemma e1_ge_sq (n : ℤ) : n ^ 2 + (-2) ≤ 7 * n * (n + 1) + (2 * n + 1) := by
  have h : 7 * n * (n + 1) + (2 * n + 1) - (n ^ 2 + (-2)) = 3 * ((2 * n + 1) * (n + 1)) := by
    ring
  have hsplit : n ≤ -1 ∨ 0 ≤ n := by omega
  have hnn : 0 ≤ 3 * ((2 * n + 1) * (n + 1)) := by
    rcases hsplit with hn | hn
    · have ha : 2 * n + 1 ≤ 0 := by omega
      have hb : n + 1 ≤ 0 := by omega
      exact mul_nonneg (by norm_num) (mul_nonneg_of_nonpos_of_nonpos ha hb)
    · have ha : 0 ≤ 2 * n + 1 := by omega
      have hb : 0 ≤ n + 1 := by omega
      exact mul_nonneg (by norm_num) (mul_nonneg ha hb)
  linarith [h]

lemma e2_ge_sq (n : ℤ) : n ^ 2 + (-3) ≤ 7 * n * (n + 1) + 2 * (2 * n + 1) := by
  have h : 7 * n * (n + 1) + 2 * (2 * n + 1) - (n ^ 2 + (-3)) = (6 * n + 5) * (n + 1) := by
    ring
  have hsplit : n ≤ -1 ∨ 0 ≤ n := by omega
  have hnn : 0 ≤ (6 * n + 5) * (n + 1) := by
    rcases hsplit with hn | hn
    · have ha : 6 * n + 5 ≤ 0 := by omega
      have hb : n + 1 ≤ 0 := by omega
      exact mul_nonneg_of_nonpos_of_nonpos ha hb
    · have ha : 0 ≤ 6 * n + 5 := by omega
      have hb : 0 ≤ n + 1 := by omega
      exact mul_nonneg ha hb
  linarith [h]

lemma e1_ge_11 (n : ℤ) (h1 : n ≠ -1) (h2 : n ≠ 0) :
    11 ≤ 7 * n * (n + 1) + (2 * n + 1) := by
  have hsplit : n ≤ -2 ∨ 1 ≤ n := by omega
  have h : 7 * n * (n + 1) + (2 * n + 1) - 11 = (n + 2) * (7 * n - 5) := by ring
  have hnn : 0 ≤ (n + 2) * (7 * n - 5) := by
    rcases hsplit with hn | hn
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    · exact mul_nonneg (by omega) (by omega)
  linarith [h]

lemma e2_ge_8 (n : ℤ) (h1 : n ≠ -1) (h2 : n ≠ 0) :
    8 ≤ 7 * n * (n + 1) + 2 * (2 * n + 1) := by
  have hsplit : n ≤ -2 ∨ 1 ≤ n := by omega
  have h : 7 * n * (n + 1) + 2 * (2 * n + 1) - 8 = (n + 2) * (7 * n - 3) := by ring
  have hnn : 0 ≤ (n + 2) * (7 * n - 3) := by
    rcases hsplit with hn | hn
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    · exact mul_nonneg (by omega) (by omega)
  linarith [h]

lemma zpn_cast (a : ℝ) (n : ℕ) : a ^ ((n : ℕ) : ℤ) = a ^ n := by
  rw [zpow_natCast]

lemma tendsto_zpow_sq (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Tendsto (fun n : ℤ => ρ ^ (n ^ 2)) cofinite (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
    (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1) ε hε
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset (Finset.finite_toSet (Finset.Icc (-(N : ℤ)) (N : ℤ))) ?_
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  by_contra hcon
  simp only [Finset.mem_coe, Finset.mem_Icc] at hcon
  have hN0 : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg N
  have hNle : (N : ℤ) ≤ n ^ 2 := by
    rcases not_and_or.mp hcon with h | h
    · have ha : (0 : ℤ) ≤ -n - 1 := by omega
      have hb : (0 : ℤ) ≤ -n := by omega
      nlinarith [mul_nonneg ha hb]
    · have ha : (0 : ℤ) ≤ n - 1 := by omega
      have hb : (0 : ℤ) ≤ n := by omega
      nlinarith [mul_nonneg ha hb]
  have hpos : 0 < ρ ^ (n ^ 2) := zpow_pos hρ0 _
  have hle : ρ ^ (n ^ 2) ≤ ρ ^ ((N : ℕ) : ℤ) :=
    zpow_le_zpow_right_of_le_one₀ hρ0 hρ1.le hNle
  rw [zpn_cast] at hle
  have hNd := hN N le_rfl
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (pow_pos hρ0 N)] at hNd
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hpos] at hn
  exact absurd (lt_of_le_of_lt hle hNd) hn

lemma summable_of_sq_bound {K : Type} [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] (t : ℤ → K) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (c : ℤ)
    (h : ∀ n : ℤ, ‖t n‖ ≤ ρ ^ (n ^ 2 + c)) : Summable t := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) h ?_
  have hmain : Tendsto (fun n : ℤ => ρ ^ c * ρ ^ (n ^ 2)) cofinite (nhds 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_zpow_sq ρ hρ0 hρ1)
  refine hmain.congr' ?_
  filter_upwards with n
  rw [zpow_add₀ (ne_of_gt hρ0), mul_comm]

lemma tsum_split {K : Type} [NontriviallyNormedField K] (t : ℤ → K) (ht : Summable t)
    (a b : ℤ) (hab : a ≠ b) (hg : Summable (fun n => if n = a then 0 else t n)) :
    ∑' n, t n = t a + t b + ∑' n, (if n = a ∨ n = b then 0 else t n) := by
  have e1 : ∑' n, t n = t a + ∑' n, (if n = a then 0 else t n) := ht.tsum_eq_add_tsum_ite a
  have e2 : ∑' n, (if n = a then 0 else t n)
      = (if b = a then (0 : K) else t b) + ∑' n, (if n = b then 0 else (if n = a then 0 else t n)) :=
    hg.tsum_eq_add_tsum_ite b
  have e3 : ∑' n, (if n = b then 0 else (if n = a then 0 else t n))
      = ∑' n, (if n = a ∨ n = b then 0 else t n) := by
    refine tsum_congr fun n => ?_
    by_cases h1 : n = b <;> by_cases h2 : n = a <;> simp [h1, h2]
  rw [e1, e2, e3, if_neg (Ne.symm hab)]
  ring

lemma norm_tsum_ite_le {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K]
    (t : ℤ → K) (a b : ℤ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ n, n ≠ a → n ≠ b → ‖t n‖ ≤ C) :
    ‖∑' n : ℤ, (if n = a ∨ n = b then (0 : K) else t n)‖ ≤ C := by
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC ?_
  intro n
  by_cases h1 : n = a ∨ n = b
  · rw [if_pos h1, norm_zero]
    exact hC
  · rw [if_neg h1]
    exact h n (fun h2 => h1 (Or.inl h2)) (fun h2 => h1 (Or.inr h2))

end Conjectures.JoshiAbc.QuotientJet_aux

open Conjectures.JoshiAbc.QuotientJet_aux

theorem Conjectures.JoshiAbc.QuotientJet :
∀ (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K], let theta := fun (q u : K) => ∑' n : ℤ, q^(n*(n+1)/2) * u^(2*n+1); ∀ (r z : K), r^14=(29:K) → 0 < ‖r‖ → ‖r‖ < 1 → z^7=1 → ‖z‖=1 → ‖1+z^2‖=1 → ‖theta (r^14) (r*z) / theta (r^14) (r^2*z) - (r+z^2*r^3)‖ ≤ ‖r‖^4 := by
  intro K _ _ _ _
  simp only []
  intro r z _ hr0 hr1 _ hz _
  have hr : r ≠ 0 := by
    intro h
    rw [h, norm_zero] at hr0
    exact lt_irrefl 0 hr0
  have hzne : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    exact zero_ne_one hz
  have hrz : r * z ≠ 0 := mul_ne_zero hr hzne
  have hr2z : r ^ 2 * z ≠ 0 := mul_ne_zero (pow_ne_zero 2 hr) hzne
  have hle1 : ‖r‖ ≤ 1 := le_of_lt hr1
  set A := ∑' n : ℤ, (r ^ 14) ^ (n * (n + 1) / 2) * (r * z) ^ (2 * n + 1) with hAdef
  set B := ∑' n : ℤ, (r ^ 14) ^ (n * (n + 1) / 2) * (r ^ 2 * z) ^ (2 * n + 1) with hBdef
  set R1 := ∑' n : ℤ, (if n = -1 ∨ n = 0 then (0 : K) else
    (r ^ 14) ^ (n * (n + 1) / 2) * (r * z) ^ (2 * n + 1)) with hR1def
  set R2 := ∑' n : ℤ, (if n = -1 ∨ n = 0 then (0 : K) else
    (r ^ 14) ^ (n * (n + 1) / 2) * (r ^ 2 * z) ^ (2 * n + 1)) with hR2def
  set U := 1 + r ^ 2 * z ^ 2 + r * z * R1 with hUdef
  set V := 1 + r ^ 4 * z ^ 2 + r ^ 2 * z * R2 with hVdef
  set W := U - (1 + r ^ 2 * z ^ 2) * V with hWdef
  have hs1 : Summable (fun n : ℤ => (r ^ 14) ^ (n * (n + 1) / 2) * (r * z) ^ (2 * n + 1)) := by
    refine summable_of_sq_bound _ ‖r‖ hr0 hr1 (-2) ?_
    intro n
    rw [term1 r z hr n, norm_mul, norm_zpow, norm_zpow, hz, one_zpow, mul_one]
    exact zpow_le_zpow_right_of_le_one₀ hr0 hle1 (e1_ge_sq n)
  have hs2 : Summable (fun n : ℤ => (r ^ 14) ^ (n * (n + 1) / 2) * (r ^ 2 * z) ^ (2 * n + 1)) := by
    refine summable_of_sq_bound _ ‖r‖ hr0 hr1 (-3) ?_
    intro n
    rw [term2 r z hr n, norm_mul, norm_zpow, norm_zpow, hz, one_zpow, mul_one]
    exact zpow_le_zpow_right_of_le_one₀ hr0 hle1 (e2_ge_sq n)
  have hg1 : Summable (fun n : ℤ => if n = -1 then (0 : K) else
      (r ^ 14) ^ (n * (n + 1) / 2) * (r * z) ^ (2 * n + 1)) := by
    refine summable_of_sq_bound _ ‖r‖ hr0 hr1 (-2) ?_
    intro n
    by_cases h : n = -1
    · rw [if_pos h, norm_zero]
      exact zpow_nonneg (norm_nonneg r) _
    · rw [if_neg h]
      rw [term1 r z hr n, norm_mul, norm_zpow, norm_zpow, hz, one_zpow, mul_one]
      exact zpow_le_zpow_right_of_le_one₀ hr0 hle1 (e1_ge_sq n)
  have hg2 : Summable (fun n : ℤ => if n = -1 then (0 : K) else
      (r ^ 14) ^ (n * (n + 1) / 2) * (r ^ 2 * z) ^ (2 * n + 1)) := by
    refine summable_of_sq_bound _ ‖r‖ hr0 hr1 (-3) ?_
    intro n
    by_cases h : n = -1
    · rw [if_pos h, norm_zero]
      exact zpow_nonneg (norm_nonneg r) _
    · rw [if_neg h]
      rw [term2 r z hr n, norm_mul, norm_zpow, norm_zpow, hz, one_zpow, mul_one]
      exact zpow_le_zpow_right_of_le_one₀ hr0 hle1 (e2_ge_sq n)
  have ht1a : (r ^ 14) ^ ((-1 : ℤ) * ((-1 : ℤ) + 1) / 2) * (r * z) ^ (2 * (-1 : ℤ) + 1)
      = (r * z)⁻¹ := by
    rw [show ((-1 : ℤ) * ((-1 : ℤ) + 1) / 2) = 0 by norm_num, zpow_zero, one_mul,
      show (2 * (-1 : ℤ) + 1) = -1 by norm_num, zpow_neg_one]
  have ht1b : (r ^ 14) ^ ((0 : ℤ) * ((0 : ℤ) + 1) / 2) * (r * z) ^ (2 * (0 : ℤ) + 1) = r * z := by
    rw [show ((0 : ℤ) * ((0 : ℤ) + 1) / 2) = 0 by norm_num, zpow_zero, one_mul,
      show (2 * (0 : ℤ) + 1) = 1 by norm_num, zpow_one]
  have ht2a : (r ^ 14) ^ ((-1 : ℤ) * ((-1 : ℤ) + 1) / 2) * (r ^ 2 * z) ^ (2 * (-1 : ℤ) + 1)
      = (r ^ 2 * z)⁻¹ := by
    rw [show ((-1 : ℤ) * ((-1 : ℤ) + 1) / 2) = 0 by norm_num, zpow_zero, one_mul,
      show (2 * (-1 : ℤ) + 1) = -1 by norm_num, zpow_neg_one]
  have ht2b : (r ^ 14) ^ ((0 : ℤ) * ((0 : ℤ) + 1) / 2) * (r ^ 2 * z) ^ (2 * (0 : ℤ) + 1)
      = r ^ 2 * z := by
    rw [show ((0 : ℤ) * ((0 : ℤ) + 1) / 2) = 0 by norm_num, zpow_zero, one_mul,
      show (2 * (0 : ℤ) + 1) = 1 by norm_num, zpow_one]
  have hsp1 : A = (r * z)⁻¹ + r * z + R1 := by
    have h := tsum_split (fun n : ℤ => (r ^ 14) ^ (n * (n + 1) / 2) * (r * z) ^ (2 * n + 1))
      hs1 (-1) 0 (by norm_num) hg1
    rw [hAdef, hR1def, h, ht1a, ht1b]
  have hsp2 : B = (r ^ 2 * z)⁻¹ + r ^ 2 * z + R2 := by
    have h := tsum_split (fun n : ℤ => (r ^ 14) ^ (n * (n + 1) / 2) * (r ^ 2 * z) ^ (2 * n + 1))
      hs2 (-1) 0 (by norm_num) hg2
    rw [hBdef, hR2def, h, ht2a, ht2b]
  have hR1n : ‖R1‖ ≤ ‖r‖ ^ (11 : ℕ) := by
    rw [hR1def]
    refine norm_tsum_ite_le _ (-1) 0 _ (pow_nonneg (norm_nonneg r) 11) ?_
    intro n h1 h2
    rw [term1 r z hr n, norm_mul, norm_zpow, norm_zpow, hz, one_zpow, mul_one,
      ← zpn_cast ‖r‖ 11]
    exact zpow_le_zpow_right_of_le_one₀ hr0 hle1 (e1_ge_11 n h1 h2)
  have hR2n : ‖R2‖ ≤ ‖r‖ ^ (8 : ℕ) := by
    rw [hR2def]
    refine norm_tsum_ite_le _ (-1) 0 _ (pow_nonneg (norm_nonneg r) 8) ?_
    intro n h1 h2
    rw [term2 r z hr n, norm_mul, norm_zpow, norm_zpow, hz, one_zpow, mul_one,
      ← zpn_cast ‖r‖ 8]
    exact zpow_le_zpow_right_of_le_one₀ hr0 hle1 (e2_ge_8 n h1 h2)
  have hρ4lt : ‖r‖ ^ (4 : ℕ) < 1 := pow_lt_one₀ hr0.le hr1 (by norm_num)
  have hρ2lt : ‖r‖ ^ (2 : ℕ) < 1 := pow_lt_one₀ hr0.le hr1 (by norm_num)
  have hδ1 : ‖r * z * R1‖ ≤ ‖r‖ ^ (4 : ℕ) := by
    have hnorm : ‖r * z * R1‖ = ‖r‖ * ‖R1‖ := by rw [norm_mul, norm_mul, hz, mul_one]
    have hle : ‖R1‖ ≤ ‖r‖ ^ (3 : ℕ) :=
      le_trans hR1n (pow_le_pow_of_le_one hr0.le hle1 (by norm_num))
    rw [hnorm]
    calc ‖r‖ * ‖R1‖ ≤ ‖r‖ * ‖r‖ ^ (3 : ℕ) := mul_le_mul_of_nonneg_left hle hr0.le
      _ = ‖r‖ ^ (4 : ℕ) := by ring
  have hδ2 : ‖r ^ 2 * z * R2‖ ≤ ‖r‖ ^ (4 : ℕ) := by
    have hnorm : ‖r ^ 2 * z * R2‖ = ‖r‖ ^ 2 * ‖R2‖ := by
      rw [norm_mul, norm_mul, norm_pow, hz, mul_one]
    have hle : ‖R2‖ ≤ ‖r‖ ^ (2 : ℕ) :=
      le_trans hR2n (pow_le_pow_of_le_one hr0.le hle1 (by norm_num))
    rw [hnorm]
    calc ‖r‖ ^ 2 * ‖R2‖ ≤ ‖r‖ ^ 2 * ‖r‖ ^ (2 : ℕ) :=
            mul_le_mul_of_nonneg_left hle (pow_nonneg (norm_nonneg r) 2)
      _ = ‖r‖ ^ (4 : ℕ) := by ring
  have hρ2 : ‖r ^ 2 * z ^ 2‖ = ‖r‖ ^ 2 := by
    rw [norm_mul, norm_pow, norm_pow, hz, one_pow, mul_one]
  have h1r2z2 : ‖1 + r ^ 2 * z ^ 2‖ = 1 := by
    have hne : ‖(1 : K)‖ ≠ ‖r ^ 2 * z ^ 2‖ := by
      rw [norm_one, hρ2]
      exact (ne_of_lt hρ2lt).symm
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one, hρ2,
      max_eq_left (le_of_lt hρ2lt)]
  have h4z2 : ‖r ^ 4 * z ^ 2‖ = ‖r‖ ^ (4 : ℕ) := by
    rw [norm_mul, norm_pow, norm_pow, hz, one_pow, mul_one]
  have hsum2 : ‖r ^ 4 * z ^ 2 + r ^ 2 * z * R2‖ ≤ ‖r‖ ^ (4 : ℕ) := by
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ ?_)
    · rw [h4z2]
    · exact hδ2
  have hVn : ‖V‖ = 1 := by
    have hVeq : V = 1 + (r ^ 4 * z ^ 2 + r ^ 2 * z * R2) := by
      rw [hVdef]
      ring
    have hne : ‖(1 : K)‖ ≠ ‖r ^ 4 * z ^ 2 + r ^ 2 * z * R2‖ := by
      rw [norm_one]
      exact (ne_of_lt (lt_of_le_of_lt hsum2 hρ4lt)).symm
    rw [hVeq, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one,
      max_eq_left (le_of_lt (lt_of_le_of_lt hsum2 hρ4lt))]
  have hVne : V ≠ 0 := by
    intro h
    rw [h, norm_zero] at hVn
    exact zero_ne_one hVn
  have hWn : ‖W‖ ≤ ‖r‖ ^ (4 : ℕ) := by
    have hWeq : W = r * z * R1 - (1 + r ^ 2 * z ^ 2) * (r ^ 4 * z ^ 2 + r ^ 2 * z * R2) := by
      rw [hWdef, hUdef, hVdef]
      ring
    rw [hWeq]
    have h1 : ‖r * z * R1 - (1 + r ^ 2 * z ^ 2) * (r ^ 4 * z ^ 2 + r ^ 2 * z * R2)‖
        ≤ max ‖r * z * R1‖ ‖(1 + r ^ 2 * z ^ 2) * (r ^ 4 * z ^ 2 + r ^ 2 * z * R2)‖ := by
      rw [sub_eq_add_neg]
      refine le_trans (IsUltrametricDist.norm_add_le_max _ _) ?_
      rw [norm_neg]
    refine le_trans h1 (max_le hδ1 ?_)
    rw [norm_mul, h1r2z2, one_mul]
    exact hsum2
  have hAeq : A = U / (r * z) := by
    rw [hUdef, hsp1]
    field_simp <;> ring
  have hBeq : B = V / (r ^ 2 * z) := by
    rw [hVdef, hsp2]
    field_simp <;> ring
  have hkey : A / B - (r + z ^ 2 * r ^ 3) = r * W / V := by
    rw [hAeq, hBeq, hWdef]
    field_simp <;> ring
  rw [hkey, norm_div, norm_mul, hVn, div_one]
  calc ‖r‖ * ‖W‖ ≤ ‖r‖ * ‖r‖ ^ (4 : ℕ) := mul_le_mul_of_nonneg_left hWn hr0.le
    _ ≤ 1 * ‖r‖ ^ (4 : ℕ) := mul_le_mul_of_nonneg_right hle1 (pow_nonneg (norm_nonneg r) 4)
    _ = ‖r‖ ^ 4 := one_mul _
