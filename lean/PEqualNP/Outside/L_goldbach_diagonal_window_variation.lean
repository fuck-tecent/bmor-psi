import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_diagonal_window_variation :
    let g := fun (φ : ℝ → ℝ) (n k : ℕ) => Real.log (k:ℝ)*(φ ((k:ℝ)/n))^2; ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → (∀ u : ℝ, u < 1/3 ∨ 2/3 < u → φ u=0) → ∃ K : ℝ, 0<K ∧ ∀ n : ℕ, 2≤n → (∑ k ∈ Finset.range n, |g φ n (k+1)-g φ n k|) ≤ K*Real.log (2*(n:ℝ)) := by
  dsimp only
  intro φ hφ _hsupport
  let F : ℝ → ℝ := fun u => (φ u) ^ 2
  have hF : ContDiff ℝ 1 F := hφ.pow 2
  obtain ⟨A, hA⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
      hF.continuous.continuousOn
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
      hF.continuous_deriv_one.continuousOn
  let M := max A 0
  let C := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  have hC : 0 ≤ C := le_max_right _ _
  refine ⟨M + C + 1, by linarith, ?_⟩
  intro n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let v : ℕ → ℝ := fun k => (k : ℝ) / n
  let L : ℕ → ℝ := fun k => Real.log (k : ℝ)
  change (∑ k ∈ Finset.range n, |L (k + 1) * F (v (k + 1)) - L k * F (v k)|) ≤
    (M + C + 1) * Real.log (2 * (n : ℝ))
  have hv (k : ℕ) (hk : k ≤ n) : v k ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨div_nonneg (Nat.cast_nonneg _) hnR.le,
      (div_le_one hnR).mpr (by exact_mod_cast hk)⟩
  have hlog (k : ℕ) : 0 ≤ L (k + 1) - L k := by
    apply sub_nonneg.mpr
    by_cases hk : k = 0
    · subst k
      simp [L]
    · exact Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hk))
        (by exact_mod_cast Nat.le_succ k)
  have hterm (k : ℕ) (hk : k < n) :
      |L (k + 1) * F (v (k + 1)) - L k * F (v k)| ≤
        L n * (C / n) + (L (k + 1) - L k) * M := by
    have hd : v (k + 1) - v k = (1 : ℝ) / n := by
      dsimp only [v]
      push_cast
      rw [← sub_div, add_sub_cancel_left]
    have hlip : |F (v (k + 1)) - F (v k)| ≤ C / n := by
      have hm := Convex.norm_image_sub_le_of_norm_deriv_le (C := C)
        (fun u _ => hF.differentiable (by norm_num) u)
        (fun u hu => (hB u hu).trans (le_max_left B 0))
        (convex_Icc (0 : ℝ) 1) (hv k hk.le) (hv (k + 1) hk)
      simpa only [Real.norm_eq_abs, hd, div_eq_mul_inv, one_mul,
        abs_of_nonneg (inv_nonneg.mpr hnR.le)] using hm
    have hMk : |F (v k)| ≤ M := by
      simpa only [Real.norm_eq_abs] using (hA (v k) (hv k hk.le)).trans (le_max_left A 0)
    have hLmax : L (k + 1) ≤ L n := Real.log_le_log (by positivity) (by exact_mod_cast hk)
    have hLpos : 0 ≤ L (k + 1) := Real.log_nonneg (by exact_mod_cast Nat.succ_pos k)
    rw [show L (k + 1) * F (v (k + 1)) - L k * F (v k) =
      L (k + 1) * (F (v (k + 1)) - F (v k)) + (L (k + 1) - L k) * F (v k) by ring]
    calc
      _ ≤ _ := abs_add_le _ _
      _ = L (k + 1) * |F (v (k + 1)) - F (v k)| + (L (k + 1) - L k) * |F (v k)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hLpos, abs_of_nonneg (hlog k)]
      _ ≤ _ := add_le_add
        (mul_le_mul hLmax hlip (abs_nonneg _) (hLpos.trans hLmax))
        (mul_le_mul_of_nonneg_left hMk (hlog k))
  calc
    _ ≤ ∑ k ∈ Finset.range n, (L n * (C / n) + (L (k + 1) - L k) * M) :=
      Finset.sum_le_sum (fun k hk => hterm k (Finset.mem_range.mp hk))
    _ = (n : ℝ) * (L n * (C / n)) + L n * M := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← Finset.sum_mul, Finset.sum_range_sub]
      simp [L]
    _ = (M + C) * L n := by
      field_simp [hnR.ne'] <;> ring
    _ ≤ _ := by
      have hLn : L n ≤ Real.log (2 * (n : ℝ)) :=
        Real.log_le_log hnR (by linarith)
      have hp : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by
        have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
        linarith)
      exact (mul_le_mul_of_nonneg_left hLn (add_nonneg hM hC)).trans
        (mul_le_mul_of_nonneg_right (by linarith) hp)
