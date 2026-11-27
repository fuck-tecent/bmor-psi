import Mathlib

namespace Conjectures.JoshiAbc.SingleJet_aux

lemma tail_le {E ι : Type*} [NormedAddCommGroup E] [CompleteSpace E] [IsUltrametricDist E]
    (f : ι → E) (s : Finset ι) (C : ℝ) (hC : 0 ≤ C) (hf : Summable f)
    (h : ∀ i, i ∉ s → ‖f i‖ ≤ C) : ‖∑' i, f i - ∑ i ∈ s, f i‖ ≤ C := by
  have hs := hf.sum_add_tsum_compl (s := s)
  have heq : (∑' i, f i) - ∑ i ∈ s, f i = ∑' x : ↑(s : Set ι)ᶜ, f x := by
    rw [← hs]
    abel
  rw [heq]
  apply IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC
  intro i
  apply h i
  change (i : ι) ∉ s
  exact i.property

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

lemma exp14 (n : ℤ) : (14:ℤ) * (n*(n+1)/2) = 7*n*(n+1) := by
  have h : (2:ℤ) ∣ n*(n+1) := Even.two_dvd (Int.even_mul_succ_self n)
  obtain ⟨k, hk⟩ := h
  have h2 : n*(n+1)/2 = k := by omega
  rw [h2]
  nlinarith [hk]

lemma zpow_nat_mul (a : ℝ) (m : ℕ) (t : ℤ) : (a^m)^t = a^((m:ℤ)*t) := by
  rw [← zpow_natCast, ← zpow_mul]

lemma norm_psi1 (r z : K) (hz : ‖z‖ = 1) (n : ℤ) :
    ‖(r^14)^(n*(n+1)/2) * z^(2*n+2)‖ = ‖r‖^(7*n*(n+1)) := by
  rw [norm_mul, norm_zpow, norm_zpow, norm_pow, hz]
  simp only [one_zpow, mul_one]
  rw [zpow_nat_mul]
  congr 1
  exact exp14 n

lemma norm_psi2 (r z : K) (hr : 0 < ‖r‖) (hz : ‖z‖ = 1) (n : ℤ) :
    ‖(r^14)^(n*(n+1)/2) * (r^2*z)^(2*n+2)‖ = ‖r‖^(7*n*(n+1)+4*n+4) := by
  have hne : ‖r‖ ≠ 0 := ne_of_gt hr
  rw [norm_mul, norm_zpow, norm_zpow, norm_pow, norm_mul, norm_pow, hz]
  simp only [mul_one]
  rw [zpow_nat_mul, zpow_nat_mul, ← zpow_add₀ hne]
  congr 1
  push_cast
  rw [exp14]
  ring

lemma exp1_tail (n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ -1) : (14:ℤ) ≤ 7*n*(n+1) := by
  have key : (0:ℤ) ≤ (n+2)*(n-1) := by
    rcases lt_or_ge n (-1) with hn | hn
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    · exact mul_nonneg (by omega) (by omega)
  nlinarith [key]

lemma exp2_tail (n : ℤ) (h1 : n ≠ -1) : (4:ℤ) ≤ 7*n*(n+1)+4*n+4 := by
  have key : (0:ℤ) ≤ n*(7*n+11) := by
    rcases lt_or_ge n (-1) with hn | hn
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    · exact mul_nonneg (by omega) (by omega)
  nlinarith [key]

lemma exp1_pos (n : ℕ) : (n:ℤ) ≤ 7*(n:ℤ)*((n:ℤ)+1) := by
  have key : (0:ℤ) ≤ (n:ℤ)*(7*(n:ℤ)+6) := mul_nonneg (by omega) (by omega)
  nlinarith [key]

lemma exp1_neg (n : ℕ) : (n:ℤ) ≤ 7*(-((n:ℤ)+1))*(-((n:ℤ)+1)+1) := by
  have key : (0:ℤ) ≤ (n:ℤ)*(7*(n:ℤ)+6) := mul_nonneg (by omega) (by omega)
  nlinarith [key]

lemma exp2_pos (n : ℕ) : (n:ℤ) ≤ 7*(n:ℤ)*((n:ℤ)+1)+4*(n:ℤ)+4 := by
  have key : (0:ℤ) ≤ (n:ℤ)*(7*(n:ℤ)+10) := mul_nonneg (by omega) (by omega)
  nlinarith [key]

lemma exp2_neg (n : ℕ) : (n:ℤ) ≤ 7*(-((n:ℤ)+1))*(-((n:ℤ)+1)+1)+4*(-((n:ℤ)+1))+4 := by
  have key : (0:ℤ) ≤ (n:ℤ)*(7*(n:ℤ)+2) := mul_nonneg (by omega) (by omega)
  nlinarith [key]

lemma summable_psi1 (r z : K) (hr : 0 < ‖r‖) (hrlt : ‖r‖ < 1) (hz : ‖z‖ = 1) :
    Summable (fun n : ℤ => (r^14)^(n*(n+1)/2) * z^(2*n+2)) := by
  have hgeom : Summable (fun n : ℕ => ‖r‖^n) :=
    summable_geometric_of_lt_one (norm_nonneg r) hrlt
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · apply Summable.of_norm_bounded hgeom
    intro n
    show ‖(r^14)^((n:ℤ)*((n:ℤ)+1)/2) * z^(2*(n:ℤ)+2)‖ ≤ ‖r‖^n
    rw [norm_psi1 r z hz (n:ℤ), ← zpow_natCast]
    exact zpow_le_zpow_right_of_le_one₀ hr hrlt.le (exp1_pos n)
  · apply Summable.of_norm_bounded hgeom
    intro n
    show ‖(r^14)^((-((n:ℤ)+1))*((-((n:ℤ)+1))+1)/2) * z^(2*(-((n:ℤ)+1))+2)‖ ≤ ‖r‖^n
    rw [norm_psi1 r z hz (-((n:ℤ)+1)), ← zpow_natCast]
    exact zpow_le_zpow_right_of_le_one₀ hr hrlt.le (exp1_neg n)

lemma summable_psi2 (r z : K) (hr : 0 < ‖r‖) (hrlt : ‖r‖ < 1) (hz : ‖z‖ = 1) :
    Summable (fun n : ℤ => (r^14)^(n*(n+1)/2) * (r^2*z)^(2*n+2)) := by
  have hgeom : Summable (fun n : ℕ => ‖r‖^n) :=
    summable_geometric_of_lt_one (norm_nonneg r) hrlt
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · apply Summable.of_norm_bounded hgeom
    intro n
    show ‖(r^14)^((n:ℤ)*((n:ℤ)+1)/2) * (r^2*z)^(2*(n:ℤ)+2)‖ ≤ ‖r‖^n
    rw [norm_psi2 r z hr hz (n:ℤ), ← zpow_natCast]
    exact zpow_le_zpow_right_of_le_one₀ hr hrlt.le (exp2_pos n)
  · apply Summable.of_norm_bounded hgeom
    intro n
    show ‖(r^14)^((-((n:ℤ)+1))*((-((n:ℤ)+1))+1)/2) * (r^2*z)^(2*(-((n:ℤ)+1))+2)‖ ≤ ‖r‖^n
    rw [norm_psi2 r z hr hz (-((n:ℤ)+1)), ← zpow_natCast]
    exact zpow_le_zpow_right_of_le_one₀ hr hrlt.le (exp2_neg n)

end Conjectures.JoshiAbc.SingleJet_aux

open Conjectures.JoshiAbc.SingleJet_aux

theorem Conjectures.JoshiAbc.SingleJet :
    ∀ (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K], let theta := fun (q u : K) => ∑' n : ℤ, q^(n*(n+1)/2) * u^(2*n+1); ∀ (r z : K), r^14=(29:K) → 0 < ‖r‖ → ‖r‖ < 1 → z^7=1 → ‖z‖=1 → ‖1+z^2‖=1 → ‖theta (r^14) z / theta (r^14) (r^2*z) - (1+z^2)*r^2‖ ≤ ‖r‖^4 := by
  intro K i1 i2 i3 i4 theta r z h29 hrpos hrlt hz7 hzn hu
  show ‖(∑' n : ℤ, (r^14)^(n*(n+1)/2) * z^(2*n+1)) /
      (∑' n : ℤ, (r^14)^(n*(n+1)/2) * (r^2*z)^(2*n+1)) - (1+z^2)*r^2‖ ≤ ‖r‖^4
  have hr0 : r ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hrpos)
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hzn]; exact one_ne_zero)
  have hr2z0 : r^2*z ≠ 0 := mul_ne_zero (pow_ne_zero 2 hr0) hz0
  have hr2 : ‖r‖^2 < 1 := by
    have h : (‖r‖ - 1) * (‖r‖ + 1) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
    nlinarith [h]
  have hr4 : ‖r‖^4 < 1 := by
    have h : (‖r‖^2 - 1) * (‖r‖^2 + 1) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) (by positivity)
    nlinarith [h]
  have hr14 : ‖r‖^14 ≤ ‖r‖^4 := by
    have h : ‖r‖^10 ≤ 1 := pow_le_one₀ (norm_nonneg r) hrlt.le
    calc ‖r‖^14 = ‖r‖^4 * ‖r‖^10 := by ring
      _ ≤ ‖r‖^4 * 1 := mul_le_mul_of_nonneg_left h (pow_nonneg (norm_nonneg r) 4)
      _ = ‖r‖^4 := by ring
  have hr6 : ‖r‖^6 ≤ ‖r‖^4 := by
    have h : ‖r‖^2 ≤ 1 := pow_le_one₀ (norm_nonneg r) hrlt.le
    calc ‖r‖^6 = ‖r‖^4 * ‖r‖^2 := by ring
      _ ≤ ‖r‖^4 * 1 := mul_le_mul_of_nonneg_left h (pow_nonneg (norm_nonneg r) 4)
      _ = ‖r‖^4 := by ring
  have hS1 : Summable (fun n : ℤ => (r^14)^(n*(n+1)/2) * z^(2*n+2)) :=
    summable_psi1 r z hrpos hrlt hzn
  have hS2 : Summable (fun n : ℤ => (r^14)^(n*(n+1)/2) * (r^2*z)^(2*n+2)) :=
    summable_psi2 r z hrpos hrlt hzn
  set A : K := ∑' n : ℤ, (r^14)^(n*(n+1)/2) * z^(2*n+1) with hA_def
  set B : K := ∑' n : ℤ, (r^14)^(n*(n+1)/2) * (r^2*z)^(2*n+1) with hB_def
  set P : K := ∑' n : ℤ, (r^14)^(n*(n+1)/2) * z^(2*n+2) with hP_def
  set Q : K := ∑' n : ℤ, (r^14)^(n*(n+1)/2) * (r^2*z)^(2*n+2) with hQ_def
  have hT1 : ‖P - (1+z^2)‖ ≤ ‖r‖^14 := by
    have hb : ∀ i : ℤ, i ∉ ({0,-1} : Finset ℤ) →
        ‖(r^14)^(i*(i+1)/2) * z^(2*i+2)‖ ≤ ‖r‖^14 := by
      intro i hi
      have hi' : i ≠ 0 ∧ i ≠ -1 := by simpa using hi
      rw [norm_psi1 r z hzn i, ← zpow_natCast]
      exact zpow_le_zpow_right_of_le_one₀ hrpos hrlt.le (exp1_tail i hi'.1 hi'.2)
    have hhead : (∑ i ∈ ({0,-1} : Finset ℤ), (r^14)^(i*(i+1)/2) * z^(2*i+2)) = 1 + z^2 := by
      rw [Finset.sum_pair (by norm_num : (0:ℤ) ≠ -1)]
      simp <;> ring
    rw [hP_def, ← hhead]
    exact tail_le _ _ _ (pow_nonneg (norm_nonneg r) 14) hS1 hb
  have hT2 : ‖Q - 1‖ ≤ ‖r‖^4 := by
    have hb : ∀ i : ℤ, i ∉ ({-1} : Finset ℤ) →
        ‖(r^14)^(i*(i+1)/2) * (r^2*z)^(2*i+2)‖ ≤ ‖r‖^4 := by
      intro i hi
      have hi' : i ≠ -1 := by simpa using hi
      rw [norm_psi2 r z hrpos hzn i, ← zpow_natCast]
      exact zpow_le_zpow_right_of_le_one₀ hrpos hrlt.le (exp2_tail i hi')
    have hhead : (∑ i ∈ ({-1} : Finset ℤ), (r^14)^(i*(i+1)/2) * (r^2*z)^(2*i+2)) = 1 := by
      rw [Finset.sum_singleton]
      simp
    rw [hQ_def, ← hhead]
    exact tail_le _ _ _ (pow_nonneg (norm_nonneg r) 4) hS2 hb
  have hzA : z * A = P := by
    rw [hA_def, hP_def, ← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    have hzp : ∀ m : ℤ, z^(m+1) = z^m * z := by
      intro m
      rw [zpow_add₀ hz0, zpow_one]
    have hz : z^(2*n+1) * z = z^(2*n+2) := by
      have hthis := hzp (2*n+1)
      rw [show (2:ℤ)*n+1+1 = 2*n+2 by ring] at hthis
      exact hthis.symm
    show z * ((r^14)^(n*(n+1)/2) * z^(2*n+1)) = (r^14)^(n*(n+1)/2) * z^(2*n+2)
    calc z * ((r^14)^(n*(n+1)/2) * z^(2*n+1))
        = (r^14)^(n*(n+1)/2) * (z^(2*n+1) * z) := by ring
      _ = (r^14)^(n*(n+1)/2) * z^(2*n+2) := by rw [hz]
  have hzB : (r^2*z) * B = Q := by
    rw [hB_def, hQ_def, ← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    have hzp : ∀ m : ℤ, (r^2*z)^(m+1) = (r^2*z)^m * (r^2*z) := by
      intro m
      rw [zpow_add₀ hr2z0, zpow_one]
    have hz : (r^2*z)^(2*n+1) * (r^2*z) = (r^2*z)^(2*n+2) := by
      have hthis := hzp (2*n+1)
      rw [show (2:ℤ)*n+1+1 = 2*n+2 by ring] at hthis
      exact hthis.symm
    show (r^2*z) * ((r^14)^(n*(n+1)/2) * (r^2*z)^(2*n+1)) =
      (r^14)^(n*(n+1)/2) * (r^2*z)^(2*n+2)
    calc (r^2*z) * ((r^14)^(n*(n+1)/2) * (r^2*z)^(2*n+1))
        = (r^14)^(n*(n+1)/2) * ((r^2*z)^(2*n+1) * (r^2*z)) := by ring
      _ = (r^14)^(n*(n+1)/2) * (r^2*z)^(2*n+2) := by rw [hz]
  have hAdiv : A = P / z := (eq_div_iff hz0).mpr (by rw [mul_comm]; exact hzA)
  have hBdiv : B = Q / (r^2*z) := (eq_div_iff hr2z0).mpr (by rw [mul_comm]; exact hzB)
  have hQ1 : ‖Q‖ = 1 := by
    have h2 : ‖Q - 1‖ < 1 := lt_of_le_of_lt hT2 hr4
    have hu1 : ‖(1:K) + (Q-1)‖ ≤ max ‖(1:K)‖ ‖Q-1‖ := by
      exact IsUltrametricDist.norm_add_le_max _ _
    have hl1 : (1:ℝ) ≤ max ‖(1:K) + (Q-1)‖ ‖Q-1‖ := by
      have h := IsUltrametricDist.norm_add_le_max ((1:K)+(Q-1)) (-(Q-1))
      have e1 : ((1:K)+(Q-1)) + (-(Q-1)) = 1 := by ring
      rw [e1, norm_neg, norm_one] at h
      exact h
    have hupp : ‖(1:K) + (Q-1)‖ ≤ 1 := by
      refine le_trans hu1 ?_
      rw [norm_one]
      exact (max_eq_left (le_of_lt h2)).le
    have hlow : (1:ℝ) ≤ ‖(1:K) + (Q-1)‖ := by
      rcases le_max_iff.mp hl1 with h | h
      · exact h
      · linarith
    have e2 : Q = 1 + (Q-1) := by ring
    rw [e2]
    exact le_antisymm hupp hlow
  have hQne : Q ≠ 0 := norm_ne_zero_iff.mp (by rw [hQ1]; exact one_ne_zero)
  have hkey : A / B - (1+z^2)*r^2 = r^2 * (P - (1+z^2)*Q) / Q := by
    rw [hAdiv, hBdiv]
    field_simp [hz0, hr2z0, hQne]
  rw [hkey, norm_div, norm_mul, norm_pow, hQ1, div_one]
  have hPQ : P - (1+z^2)*Q = (P - (1+z^2)) - (1+z^2)*(Q-1) := by ring
  rw [hPQ]
  have hbd : ‖(P - (1+z^2)) - (1+z^2)*(Q-1)‖ ≤ ‖r‖^4 := by
    have h := IsUltrametricDist.norm_add_le_max (P - (1+z^2)) (-((1+z^2)*(Q-1)))
    have e1 : (P - (1+z^2)) + (-((1+z^2)*(Q-1))) = (P - (1+z^2)) - (1+z^2)*(Q-1) := by ring
    rw [e1, norm_neg] at h
    refine le_trans h (max_le ?_ ?_)
    · exact le_trans hT1 hr14
    · rw [norm_mul, hu, one_mul]
      exact hT2
  calc ‖r‖^2 * ‖(P - (1+z^2)) - (1+z^2)*(Q-1)‖ ≤ ‖r‖^2 * ‖r‖^4 :=
        mul_le_mul_of_nonneg_left hbd (pow_nonneg (norm_nonneg r) 2)
    _ = ‖r‖^6 := by ring
    _ ≤ ‖r‖^4 := hr6
