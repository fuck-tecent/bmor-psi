import Mathlib

open ArithmeticFunction

private theorem residual_mass (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), if k.Prime then 0 else vonMangoldt k) =
      Chebyshev.psi n - Chebyshev.theta n := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, Finset.sum_filter]
  simp_rw [ite_not]
  symm
  apply Finset.sum_subset
  · intro k hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Ioc.mp hk).2)
  · intro k hkr hki
    have hk : k = 0 := by
      have hkn := Finset.mem_range.mp hkr
      simp only [Finset.mem_Ioc] at hki
      omega
    subst k
    simp

theorem PEqualNP.Outside.L_goldbach_coset_primepower_ap_energy :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q=r); let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; ∃ C : ℝ, 0<C ∧ ∀ n q : ℕ, 2≤n → 0<q → (∑ r ∈ Finset.range q, ((∑ k ∈ F n q r, ArithmeticFunction.vonMangoldt k)-A n q r)^2) ≤ C*(n:ℝ)*(Real.log (2*(n:ℝ)))^4 := by
  intro F w A
  obtain ⟨K, hK⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let B := max K 1
  have hB : 0 < B := zero_lt_one.trans_le (le_max_right K 1)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨B ^ 2 / (Real.log 2) ^ 4, by positivity, ?_⟩
  intro n q hn hq
  let residual (k : ℕ) : ℝ := if k.Prime then 0 else vonMangoldt k
  let mass (r : ℕ) : ℝ := ∑ k ∈ F n q r, residual k
  have hmass (r : ℕ) : 0 ≤ mass r := by
    apply Finset.sum_nonneg
    intro k _
    by_cases hp : k.Prime <;> simp [residual, hp]
  have hdiff (r : ℕ) : (∑ k ∈ F n q r, vonMangoldt k) - A n q r = mass r := by
    change (∑ k ∈ F n q r, vonMangoldt k) - (∑ k ∈ F n q r, w k) = _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hp : k.Prime <;> simp [residual, w, hp, vonMangoldt_apply_prime]
  -- Every index contributes to precisely one residue class.
  have htotal : (∑ r ∈ Finset.range q, mass r) = Chebyshev.psi n - Chebyshev.theta n := by
    rw [← residual_mass]
    exact Finset.sum_fiberwise_of_maps_to (fun k _ => Finset.mem_range.mpr (Nat.mod_lt k hq)) residual
  have hsum : (∑ r ∈ Finset.range q, mass r) ≤ B * Real.sqrt n := by
    rw [htotal]
    exact (hK n).trans (mul_le_mul_of_nonneg_right (le_max_left K 1) (Real.sqrt_nonneg _))
  have hlog_le : Real.log 2 ≤ Real.log (2 * (n : ℝ)) := by
    apply Real.log_le_log (by norm_num)
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  simp_rw [hdiff]
  calc
    _ ≤ (∑ r ∈ Finset.range q, mass r) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun r _ => hmass r)
    _ ≤ (B * Real.sqrt n) ^ 2 :=
      pow_le_pow_left₀ (Finset.sum_nonneg (fun r _ => hmass r)) hsum 2
    _ = B ^ 2 * n := by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    _ = (B ^ 2 / (Real.log 2) ^ 4) * n * (Real.log 2) ^ 4 := by
      field_simp [hlog.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog.le hlog_le 4) (by positivity)
