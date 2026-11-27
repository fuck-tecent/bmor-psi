import Mathlib

theorem PEqualNP.Outside.L_goldbach_coset_primepower_ap_budget :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q = r); let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; ∃ C : ℝ, 0<C ∧ ∀ n q r : ℕ, 2≤n → 0<q → r<q → let d := (∑ k ∈ F n q r, ArithmeticFunction.vonMangoldt k)-A n q r; 0≤d ∧ d ≤ C*Real.sqrt (n:ℝ)*(Real.log (2*(n:ℝ)))^2 := by
  dsimp only
  refine ⟨2, by norm_num, ?_⟩
  intro n q r hn _ _
  let R (k : ℕ) := ArithmeticFunction.vonMangoldt k - (if k.Prime then Real.log (k:ℝ) else 0)
  let F := (Finset.range (n+1)).filter (fun k => k % q = r)
  change 0 ≤ (∑ k ∈ F, ArithmeticFunction.vonMangoldt k) - _ ∧ _ ≤ _
  rw [← Finset.sum_sub_distrib]
  change 0 ≤ ∑ k ∈ F, R k ∧ (∑ k ∈ F, R k) ≤ _
  have hR (k : ℕ) : 0 ≤ R k := by
    by_cases hp : k.Prime
    · simp [R, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simpa [R, hp] using (ArithmeticFunction.vonMangoldt_nonneg (n := k))
  refine ⟨Finset.sum_nonneg (fun k _ => hR k), ?_⟩
  have htotal : (∑ k ∈ Finset.range (n+1), R k) = Chebyshev.psi n - Chebyshev.theta n := by
    simp only [R, Finset.sum_sub_distrib, Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc,
      Finset.sum_filter, Nat.floor_natCast, Nat.range_succ_eq_Icc_zero]
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hlog : Real.log (n:ℝ) ≤ Real.log (2*(n:ℝ)) := Real.log_le_log (by linarith) (by linarith)
  have hone : 1 ≤ Real.log (2*(n:ℝ)) := (Real.le_log_iff_exp_le (by linarith)).2 (by linarith [Real.exp_one_lt_three])
  calc
    (∑ k ∈ F, R k) ≤ ∑ k ∈ Finset.range (n+1), R k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun k _ _ => hR k)
    _ = Chebyshev.psi n - Chebyshev.theta n := htotal
    _ ≤ 2*Real.sqrt n*Real.log n := Chebyshev.psi_sub_theta_le (by linarith)
    _ ≤ 2*Real.sqrt n*(Real.log (2*(n:ℝ)))^2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hlog.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hone) (le_trans zero_le_one hone)])
