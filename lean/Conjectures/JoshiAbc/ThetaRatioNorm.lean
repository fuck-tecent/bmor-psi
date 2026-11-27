import Mathlib

open Filter Topology Set

namespace Conjectures.JoshiAbc.ThetaRatioNorm_aux

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

theorem two_mul_half (n : ℤ) : 2 * (n * (n + 1) / 2) = n * (n + 1) := by
  have h : (2:ℤ) ∣ n * (n + 1) := even_iff_two_dvd.mp (Int.even_mul_succ_self n)
  omega

theorem prod_nonneg (n : ℤ) : 0 ≤ n * (n + 1) := by
  rcases le_or_gt n (-1) with hn | hn
  · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  · exact mul_nonneg (by omega) (by omega)

theorem half_nonneg (n : ℤ) : 0 ≤ n * (n + 1) / 2 := by
  have h1 := two_mul_half n
  have h2 := prod_nonneg n
  omega

theorem half_ge_one (n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ -1) : 1 ≤ n * (n + 1) / 2 := by
  have hh := two_mul_half n
  have h2 : 2 ≤ n * (n + 1) := by
    rcases le_or_gt n 0 with hn | hn
    · have hk : 0 ≤ (n - 1) * (n + 2) := mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
      nlinarith [hk]
    · have hk : 0 ≤ (n - 1) * (n + 2) := mul_nonneg (by omega) (by omega)
      nlinarith [hk]
  omega

theorem half_nat_ge (n : ℕ) : (n : ℤ) ≤ (n : ℤ) * ((n : ℤ) + 1) / 2 := by
  have hh := two_mul_half (n : ℤ)
  have h2 : 2 * (n : ℤ) ≤ (n : ℤ) * ((n : ℤ) + 1) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · have hk : 0 ≤ ((n : ℤ) - 1) * (n : ℤ) := mul_nonneg (by omega) (by omega)
      nlinarith [hk]
  omega

theorem half_neg_ge (n : ℕ) : (n : ℤ) ≤ (-((n : ℤ) + 1)) * (-((n : ℤ) + 1) + 1) / 2 := by
  have hh := two_mul_half (-((n : ℤ) + 1))
  have h2 : 2 * (n : ℤ) ≤ (-((n : ℤ) + 1)) * (-((n : ℤ) + 1) + 1) := by
    have h3 : (-((n : ℤ) + 1)) * (-((n : ℤ) + 1) + 1) = ((n : ℤ) + 1) * (n : ℤ) := by ring
    rw [h3]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · have hk : 0 ≤ ((n : ℤ) - 1) * (n : ℤ) := mul_nonneg (by omega) (by omega)
      nlinarith [hk]
  omega

theorem Enum_ge_one (n l : ℤ) (hl : 1 ≤ l) (h0 : n ≠ 0) (h1 : n ≠ -1) :
    1 ≤ 2 * l * (n * (n + 1) / 2) := by
  have h := half_ge_one n h0 h1
  have h2 : (1:ℤ) * (n * (n + 1) / 2) ≤ 2 * l * (n * (n + 1) / 2) :=
    mul_le_mul_of_nonneg_right (by omega) (half_nonneg n)
  omega

theorem Enum_nat (n : ℕ) (l : ℤ) (hl : 1 ≤ l) :
    (n : ℤ) ≤ 2 * l * ((n : ℤ) * ((n : ℤ) + 1) / 2) := by
  have h := half_nat_ge n
  have h2 : (1:ℤ) * ((n : ℤ) * ((n : ℤ) + 1) / 2) ≤ 2 * l * ((n : ℤ) * ((n : ℤ) + 1) / 2) :=
    mul_le_mul_of_nonneg_right (by omega) (half_nonneg (n : ℤ))
  omega

theorem Enum_neg (n : ℕ) (l : ℤ) (hl : 1 ≤ l) :
    (n : ℤ) ≤ 2 * l * ((-((n : ℤ) + 1)) * (-((n : ℤ) + 1) + 1) / 2) := by
  have h := half_neg_ge n
  have h2 : (1:ℤ) * ((-((n : ℤ) + 1)) * (-((n : ℤ) + 1) + 1) / 2)
      ≤ 2 * l * ((-((n : ℤ) + 1)) * (-((n : ℤ) + 1) + 1) / 2) :=
    mul_le_mul_of_nonneg_right (by omega) (half_nonneg (-((n : ℤ) + 1)))
  omega

theorem E_ge (n l j : ℤ) (hj : 1 ≤ j) (hjl : j < l) (hn : n ≠ -1) :
    2 - j ≤ 2 * l * (n * (n + 1) / 2) + j * (2 * n + 1) := by
  have hh := two_mul_half n
  have hrw : 2 * l * (n * (n + 1) / 2) = l * (n * (n + 1)) := by
    calc 2 * l * (n * (n + 1) / 2) = l * (2 * (n * (n + 1) / 2)) := by ring
      _ = l * (n * (n + 1)) := by rw [hh]
  rw [hrw]
  have hkey : 2 ≤ l * (n * (n + 1)) + j * (2 * n + 1) + j := by
    have hfact : l * (n * (n + 1)) + j * (2 * n + 1) + j = (n + 1) * (l * n + 2 * j) := by ring
    rw [hfact]
    rcases le_or_gt n (-1) with h | h
    · have hA : (1:ℤ) ≤ -(n + 1) := by omega
      have hB : (2:ℤ) ≤ -(l * n + 2 * j) := by
        have h1 : l * n ≤ l * (-2) := mul_le_mul_of_nonneg_left (by omega) (by omega)
        omega
      calc (2:ℤ) = 1 * 2 := by ring
        _ ≤ (-(n + 1)) * (-(l * n + 2 * j)) := mul_le_mul hA hB (by norm_num) (by omega)
        _ = (n + 1) * (l * n + 2 * j) := by ring
    · have hA : (1:ℤ) ≤ n + 1 := by omega
      have hB : (2:ℤ) ≤ l * n + 2 * j := by
        have h1 : 0 ≤ l * n := mul_nonneg (by omega) (by omega)
        omega
      calc (2:ℤ) = 1 * 2 := by ring
        _ ≤ (n + 1) * (l * n + 2 * j) := mul_le_mul hA hB (by norm_num) (by omega)
  omega

theorem E_nat (n : ℕ) (l j : ℤ) (hj : 1 ≤ j) (hjl : j < l) :
    (n : ℤ) ≤ 2 * l * ((n : ℤ) * ((n : ℤ) + 1) / 2) + j * (2 * (n : ℤ) + 1) := by
  have h1 := Enum_nat n l (by omega)
  have h2 : 0 ≤ j * (2 * (n : ℤ) + 1) := mul_nonneg (by omega) (by omega)
  omega

theorem E_neg (n : ℕ) (l j : ℤ) (hj : 1 ≤ j) (hjl : j < l) :
    (n : ℤ) - (j + 1) ≤ 2 * l * ((-((n : ℤ) + 1)) * (-((n : ℤ) + 1) + 1) / 2)
      + j * (2 * (-((n : ℤ) + 1)) + 1) := by
  have hh := two_mul_half (-((n : ℤ) + 1))
  have hrw : 2 * l * ((-((n : ℤ) + 1)) * (-((n : ℤ) + 1) + 1) / 2)
      = l * ((-((n : ℤ) + 1)) * (-((n : ℤ) + 1) + 1)) := by
    calc 2 * l * ((-((n : ℤ) + 1)) * (-((n : ℤ) + 1) + 1) / 2)
        = l * (2 * ((-((n : ℤ) + 1)) * (-((n : ℤ) + 1) + 1) / 2)) := by ring
      _ = l * ((-((n : ℤ) + 1)) * (-((n : ℤ) + 1) + 1)) := by rw [hh]
  rw [hrw]
  have h1 : (-((n : ℤ) + 1)) * (-((n : ℤ) + 1) + 1) = ((n : ℤ) + 1) * (n : ℤ) := by ring
  have h2 : 2 * (-((n : ℤ) + 1)) + 1 = -(2 * (n : ℤ) + 1) := by ring
  rw [h1, h2]
  have hk : 0 ≤ (n : ℤ) * ((n : ℤ) - 1) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · exact mul_nonneg (by omega) (by omega)
  have hk2 : 0 ≤ j * ((n : ℤ) * ((n : ℤ) - 1)) := mul_nonneg (by omega) hk
  have h3 : (j + 1) * (((n : ℤ) + 1) * (n : ℤ)) ≤ l * (((n : ℤ) + 1) * (n : ℤ)) :=
    mul_le_mul_of_nonneg_right (by omega) (mul_nonneg (by omega) (by omega))
  nlinarith [hk2, h3, mul_self_nonneg (n : ℤ)]

theorem norm_term_num (r z : K) (l : ℕ) (hr : ‖r‖ ≠ 0) (hz : ‖z‖ = 1) (n : ℤ) :
    ‖(r^(2*l))^(n*(n+1)/2) * z^(2*n+1)‖ = ‖r‖ ^ ((2*(l:ℤ))*(n*(n+1)/2)) := by
  have h1 : ‖(r^(2*l))^(n*(n+1)/2)‖ = ‖r‖ ^ (((2*l : ℕ) : ℤ) * (n*(n+1)/2)) := by
    rw [norm_zpow, norm_pow, ← zpow_natCast, ← zpow_mul]
  have h2 : ‖z^(2*n+1)‖ = (1:ℝ) := by simp [norm_zpow, hz]
  rw [norm_mul, h1, h2, mul_one]
  congr 1 <;> push_cast <;> ring

theorem norm_term_den (r z : K) (l j : ℕ) (hr : ‖r‖ ≠ 0) (hz : ‖z‖ = 1) (n : ℤ) :
    ‖(r^(2*l))^(n*(n+1)/2) * (r^j * z)^(2*n+1)‖
      = ‖r‖ ^ ((2*(l:ℤ))*(n*(n+1)/2) + (j:ℤ)*(2*n+1)) := by
  have h1 : ‖(r^(2*l))^(n*(n+1)/2)‖ = ‖r‖ ^ (((2*l : ℕ) : ℤ) * (n*(n+1)/2)) := by
    rw [norm_zpow, norm_pow, ← zpow_natCast, ← zpow_mul]
  have h2 : ‖(r^j * z)^(2*n+1)‖ = ‖r‖ ^ (((j : ℕ) : ℤ) * (2*n+1)) := by
    rw [norm_zpow, norm_mul, norm_pow, hz, mul_one, ← zpow_natCast, ← zpow_mul]
  rw [norm_mul, h1, h2, ← zpow_add₀ hr]
  congr 1 <;> push_cast <;> ring

theorem tail_bound (f : ℤ → K) (s : Finset ℤ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ n : ℤ, n ∉ s → ‖f n‖ ≤ C) :
    ‖∑' x : {y : ℤ // y ∈ ((↑s : Set ℤ))ᶜ}, f ↑x‖ ≤ C := by
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC ?_
  rintro ⟨y, hy⟩
  exact h y (by simpa using hy)

theorem tail_eq (f : ℤ → K) (hf : Summable f) (s : Finset ℤ) :
    ∑' n : ℤ, f n = (∑ x ∈ s, f x) + ∑' x : {y : ℤ // y ∈ ((↑s : Set ℤ))ᶜ}, f ↑x :=
  (hf.sum_add_tsum_compl (s := s)).symm

theorem norm_tsum_eq_of_head (f : ℤ → K) (s : Finset ℤ) (a : K) (C B : ℝ) (hC : 0 ≤ C)
    (hf : Summable f) (hb : ∀ n : ℤ, n ∉ s → ‖f n‖ ≤ C)
    (hsum : (∑ x ∈ s, f x) = a) (hB : ‖a‖ = B) (hlt : C < B) :
    ‖∑' n : ℤ, f n‖ = B := by
  have htail := tail_bound f s C hC hb
  have hne : ‖a‖ ≠ ‖∑' x : {y : ℤ // y ∈ ((↑s : Set ℤ))ᶜ}, f ↑x‖ := by
    intro hcon
    have h1 : ‖a‖ ≤ C := hcon.symm ▸ htail
    have h2 : B ≤ C := by rw [← hB]; exact h1
    exact (not_le_of_gt hlt) h2
  have hsplit := tail_eq f hf s
  rw [hsplit, hsum, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, hB,
    max_eq_left (le_of_lt (lt_of_le_of_lt htail hlt))]

end Conjectures.JoshiAbc.ThetaRatioNorm_aux

open Conjectures.JoshiAbc.ThetaRatioNorm_aux

theorem Conjectures.JoshiAbc.ThetaRatioNorm :
    ∀ (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K], let theta := fun (q u : K) => ∑' n : ℤ, q^(n*(n+1)/2) * u^(2*n+1); ∀ (r z : K) (l j : ℕ), 0 < ‖r‖ → ‖r‖ < 1 → ‖z‖=1 → ‖z+z⁻¹‖=1 → 0 < j → j < l → ‖theta (r^(2*l)) z / theta (r^(2*l)) (r^j*z)‖ = ‖r‖^j := by
  intro K _ _ _
  show ∀ (r z : K) (l j : ℕ), 0 < ‖r‖ → ‖r‖ < 1 → ‖z‖=1 → ‖z+z⁻¹‖=1 → 0 < j → j < l →
    ‖(∑' n : ℤ, (r^(2*l))^(n*(n+1)/2) * z^(2*n+1)) /
      (∑' n : ℤ, (r^(2*l))^(n*(n+1)/2) * (r^j*z)^(2*n+1))‖ = ‖r‖^j
  intro r z l j hr0 hr1 hz hzz hj0 hjl
  have hrne : (‖r‖:ℝ) ≠ 0 := ne_of_gt hr0
  have hlj : (1:ℤ) ≤ (l:ℤ) := by omega
  have hj1 : (1:ℤ) ≤ (j:ℤ) := by omega
  have hjlt : ((j:ℤ)) < (l:ℤ) := by omega
  have hnum_sum : Summable (fun n : ℤ => (r^(2*l))^(n*(n+1)/2) * z^(2*n+1)) := by
    apply Summable.of_nat_of_neg_add_one
    · refine (summable_geometric_of_lt_one hr0.le hr1).of_norm_bounded ?_
      intro n
      rw [norm_term_num r z l hrne hz (n:ℤ)]
      have hb := Enum_nat n (l:ℤ) hlj
      have h := zpow_le_zpow_right_of_le_one₀ hr0 hr1.le hb
      rwa [zpow_natCast] at h
    · refine (summable_geometric_of_lt_one hr0.le hr1).of_norm_bounded ?_
      intro n
      rw [norm_term_num r z l hrne hz]
      have hb := Enum_neg n (l:ℤ) hlj
      have h := zpow_le_zpow_right_of_le_one₀ hr0 hr1.le hb
      rwa [zpow_natCast] at h
  have hden_sum : Summable (fun n : ℤ => (r^(2*l))^(n*(n+1)/2) * (r^j*z)^(2*n+1)) := by
    apply Summable.of_nat_of_neg_add_one
    · refine (summable_geometric_of_lt_one hr0.le hr1).of_norm_bounded ?_
      intro n
      rw [norm_term_den r z l j hrne hz (n:ℤ)]
      have hb := E_nat n (l:ℤ) (j:ℤ) hj1 hjlt
      have h := zpow_le_zpow_right_of_le_one₀ hr0 hr1.le hb
      rwa [zpow_natCast] at h
    · refine (Summable.mul_left (‖r‖ ^ (-((j:ℤ) + 1)))
        (summable_geometric_of_lt_one hr0.le hr1)).of_norm_bounded ?_
      intro n
      rw [norm_term_den r z l j hrne hz]
      have hb := E_neg n (l:ℤ) (j:ℤ) hj1 hjlt
      have h1 := zpow_le_zpow_right_of_le_one₀ hr0 hr1.le hb
      have h2 : ‖r‖ ^ ((n:ℤ) - ((j:ℤ) + 1))
          = ‖r‖ ^ (-((j:ℤ) + 1)) * ‖r‖ ^ ((n:ℕ):ℤ) := by
        rw [show ((n:ℤ) - ((j:ℤ) + 1)) = (-((j:ℤ) + 1)) + ((n:ℕ):ℤ) by ring,
          zpow_add₀ hrne]
      rw [h2, zpow_natCast] at h1
      exact h1
  have hb1 : ∀ n : ℤ, n ∉ ({0, -1} : Finset ℤ) →
      ‖(r^(2*l))^(n*(n+1)/2) * z^(2*n+1)‖ ≤ ‖r‖ := by
    intro n hn
    have hn' : n ≠ 0 ∧ n ≠ -1 := by simpa using hn
    rw [norm_term_num r z l hrne hz n]
    have hb := Enum_ge_one n (l:ℤ) hlj hn'.1 hn'.2
    have h := zpow_le_zpow_right_of_le_one₀ hr0 hr1.le hb
    simpa using h
  have hhead1 : (∑ x ∈ ({0, -1} : Finset ℤ),
      ((r^(2*l))^(x*(x+1)/2) * z^(2*x+1))) = z + z⁻¹ := by
    have e0 : ((0:ℤ)*(0+1)/2) = 0 := by norm_num
    have e1 : ((-1:ℤ)*((-1:ℤ)+1)/2) = 0 := by norm_num
    have e2 : (2*(0:ℤ)+1) = 1 := by norm_num
    have e3 : (2*(-1:ℤ)+1) = -1 := by norm_num
    rw [Finset.sum_insert (by simp), Finset.sum_singleton, e0, e2, e1, e3]
    simp [zpow_neg]
  have hnum : ‖∑' n : ℤ, (r^(2*l))^(n*(n+1)/2) * z^(2*n+1)‖ = 1 :=
    norm_tsum_eq_of_head (fun n : ℤ => (r^(2*l))^(n*(n+1)/2) * z^(2*n+1))
      ({0, -1} : Finset ℤ) (z + z⁻¹) ‖r‖ 1 hr0.le hnum_sum hb1 hhead1 hzz hr1
  have hb2 : ∀ n : ℤ, n ∉ ({-1} : Finset ℤ) →
      ‖(r^(2*l))^(n*(n+1)/2) * (r^j*z)^(2*n+1)‖ ≤ ‖r‖^(2 - (j:ℤ)) := by
    intro n hn
    have hn1 : n ≠ -1 := by simpa using hn
    rw [norm_term_den r z l j hrne hz n]
    exact zpow_le_zpow_right_of_le_one₀ hr0 hr1.le (E_ge n (l:ℤ) (j:ℤ) hj1 hjlt hn1)
  have hhead2 : (∑ x ∈ ({-1} : Finset ℤ),
      ((r^(2*l))^(x*(x+1)/2) * (r^j*z)^(2*x+1)))
      = (r^(2*l))^(((-1:ℤ)*((-1:ℤ)+1)/2)) * (r^j*z)^(2*(-1:ℤ)+1) :=
    Finset.sum_singleton _ _
  have hheadnorm2 : ‖(r^(2*l))^(((-1:ℤ)*((-1:ℤ)+1)/2)) * (r^j*z)^(2*(-1:ℤ)+1)‖
      = ‖r‖^(-(j:ℤ)) := by
    have e1 : ((-1:ℤ)*((-1:ℤ)+1)/2) = 0 := by norm_num
    have e3 : (2*(-1:ℤ)+1) = -1 := by norm_num
    rw [norm_term_den r z l j hrne hz (-1), e1, e3]
    simp
  have hden : ‖∑' n : ℤ, (r^(2*l))^(n*(n+1)/2) * (r^j*z)^(2*n+1)‖ = ‖r‖^(-(j:ℤ)) :=
    norm_tsum_eq_of_head (fun n : ℤ => (r^(2*l))^(n*(n+1)/2) * (r^j*z)^(2*n+1))
      ({-1} : Finset ℤ) ((r^(2*l))^(((-1:ℤ)*((-1:ℤ)+1)/2)) * (r^j*z)^(2*(-1:ℤ)+1))
      (‖r‖^(2 - (j:ℤ))) (‖r‖^(-(j:ℤ))) (zpow_nonneg hr0.le _) hden_sum hb2 hhead2
      hheadnorm2 (zpow_lt_zpow_right_of_lt_one₀ hr0 hr1 (by omega))
  rw [norm_div, hnum, hden, ← zpow_natCast, div_eq_iff (ne_of_gt (zpow_pos hr0 _)), mul_comm]
  have hkey : ‖r‖^(-(j:ℤ)) * ‖r‖^((j:ℤ)) = 1 := by
    rw [← zpow_add₀ hrne]
    simp
  exact hkey.symm
