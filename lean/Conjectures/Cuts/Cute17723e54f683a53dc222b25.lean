import Mathlib

open Finset

-- child 1 zh: 起点为零的短窗下界，窗长只需达到较小的 817/1000 指数。
-- child 1 en: The shorter-scale bound at exponent 817/1000 for windows starting at zero.
-- child 2 zh: 起点为正的移动窗下界，使用 697/800 的窗长指数。
-- child 2 en: The moving-window bound at exponent 697/800 for positive window starts.
theorem Conjectures.Cuts.Cute17723e54f683a53dc222b25 (atZero : (let C₀ : ℝ := ∏' p : ℕ, if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ)-1)^2 else 1; ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N A H : ℕ, N₀ ≤ N → Even N → 2*A ≤ N → A+H ≤ N → (N : ℝ)^(817/1000 : ℝ) ≤ (H : ℝ) → A = 0 → let S := (Finset.Icc A (A+H)).filter (fun p => Nat.Prime p ∧ (Nat.Prime (N-p) ∨ ((N-p).minFac.Prime ∧ Nat.Prime ((N-p)/(N-p).minFac)))); let D : ℝ := ∏ p ∈ N.primeFactors.filter (fun p => 2 < p), ((p : ℝ)-1)/((p : ℝ)-2); c*C₀*D*(H : ℝ)/(Real.log (N : ℝ))^2 ≤ (S.card : ℝ))) (atPositive : (let C₀ : ℝ := ∏' p : ℕ, if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ)-1)^2 else 1; ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N A H : ℕ, N₀ ≤ N → Even N → 2*A ≤ N → A+H ≤ N → (N : ℝ)^(817/1000 : ℝ) ≤ (H : ℝ) → (0 < A ∧ (N : ℝ)^(697/800 : ℝ) ≤ (H : ℝ)) → let S := (Finset.Icc A (A+H)).filter (fun p => Nat.Prime p ∧ (Nat.Prime (N-p) ∨ ((N-p).minFac.Prime ∧ Nat.Prime ((N-p)/(N-p).minFac)))); let D : ℝ := ∏ p ∈ N.primeFactors.filter (fun p => 2 < p), ((p : ℝ)-1)/((p : ℝ)-2); c*C₀*D*(H : ℝ)/(Real.log (N : ℝ))^2 ≤ (S.card : ℝ))) : (let C₀ : ℝ := ∏' p : ℕ, if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ)-1)^2 else 1; ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N A H : ℕ, N₀ ≤ N → Even N → 2*A ≤ N → A+H ≤ N → (N : ℝ)^(817/1000 : ℝ) ≤ (H : ℝ) → (A=0 ∨ (N : ℝ)^(697/800 : ℝ) ≤ (H : ℝ)) → let S := (Finset.Icc A (A+H)).filter (fun p => Nat.Prime p ∧ (Nat.Prime (N-p) ∨ ((N-p).minFac.Prime ∧ Nat.Prime ((N-p)/(N-p).minFac)))); let D : ℝ := ∏ p ∈ N.primeFactors.filter (fun p => 2 < p), ((p : ℝ)-1)/((p : ℝ)-2); c*C₀*D*(H : ℝ)/(Real.log (N : ℝ))^2 ≤ (S.card : ℝ)) := by
  intro C₀
  obtain ⟨c₀, hc₀, N₀, h₀⟩ := atZero
  obtain ⟨c₁, hc₁, N₁, h₁⟩ := atPositive
  refine ⟨min c₀ c₁, lt_min hc₀ hc₁, max N₀ N₁, ?_⟩
  intro N A H hN hn hleft hright hsize hcase S D
  have hC₀ : 0 ≤ C₀ := by
    change 0 ≤ ∏' p : ℕ, if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1)^2 else 1
    apply tprod_nonneg
    intro p
    split_ifs with hp
    · have hpR : (2 : ℝ) < p := by exact_mod_cast hp.2
      have hp₁ : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
      have hpSq : (1 : ℝ) ≤ ((p : ℝ) - 1)^2 := by
        simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hp₁ 2
      exact sub_nonneg.mpr ((div_le_one (by positivity : 0 < ((p : ℝ) - 1)^2)).2 hpSq)
    · norm_num
  have hD : 0 ≤ D := by
    change 0 ≤ ∏ p ∈ N.primeFactors.filter (fun p => 2 < p),
      (((p : ℝ) - 1) / ((p : ℝ) - 2))
    apply prod_nonneg
    intro p hp
    have hpR : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
    exact div_nonneg (by linarith) (le_of_lt (sub_pos.mpr hpR))
  have lower_bound_mono {a b : ℝ} (hab : a ≤ b) :
      a * C₀ * D * (H : ℝ) / (Real.log (N : ℝ))^2 ≤
        b * C₀ * D * (H : ℝ) / (Real.log (N : ℝ))^2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hab hC₀) hD)
      (Nat.cast_nonneg H)
  by_cases hA : A = 0
  · exact (lower_bound_mono (min_le_left _ _)).trans
      (h₀ N A H ((le_max_left _ _).trans hN) hn hleft hright hsize hA)
  · have hLarge := hcase.resolve_left hA
    exact (lower_bound_mono (min_le_right _ _)).trans
      (h₁ N A H ((le_max_right _ _).trans hN) hn hleft hright hsize ⟨by omega, hLarge⟩)
