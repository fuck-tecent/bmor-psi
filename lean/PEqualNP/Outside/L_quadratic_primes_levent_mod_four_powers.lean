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


theorem PEqualNP.Outside.L_quadratic_primes_levent_mod_four_powers :
    let psi := fun (q a x : ℕ) => ∑ n ∈ (Finset.Icc 1 x).filter (fun n => n % q=a % q), ArithmeticFunction.vonMangoldt n; let cheb := fun x : ℕ => ∑ p ∈ (Finset.Icc 1 x).filter (fun p => p.Prime ∧ p % 4=1), Real.log (p : ℝ); ∃ C : ℝ, 0<C ∧ ∀ x : ℕ, 2≤x → 0 ≤ psi 4 1 x - cheb x ∧ psi 4 1 x - cheb x ≤ C * Real.sqrt x * Real.log (2*(x : ℝ))^2 := by
  intro psi cheb
  obtain ⟨K, hK⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let B := max K 1
  have hB : 0 < B := zero_lt_one.trans_le (le_max_right K 1)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨B / (Real.log 2) ^ 2, by positivity, ?_⟩
  intro x hx
  let s := (Finset.Icc 1 x).filter (fun n => n % 4 = 1)
  let residual (n : ℕ) : ℝ := if n.Prime then 0 else vonMangoldt n
  have hnonneg (n : ℕ) : 0 ≤ residual n := by
    by_cases hp : n.Prime <;> simp [residual, hp]
  have hsplit : psi 4 1 x - cheb x = ∑ n ∈ s, residual n := by
    change (∑ n ∈ s, vonMangoldt n) - (∑ n ∈ (Finset.Icc 1 x).filter (fun n => n.Prime ∧ n % 4 = 1), Real.log (n : ℝ)) = _
    rw [show (Finset.Icc 1 x).filter (fun n => n.Prime ∧ n % 4 = 1) = s.filter (fun n => n.Prime) by ext n; simp [s, and_comm, and_left_comm]]
    have hfilter : (∑ n ∈ s.filter (fun n => n.Prime), Real.log (n : ℝ)) =
        ∑ n ∈ s, if n.Prime then Real.log (n : ℝ) else 0 := Finset.sum_filter (fun n : ℕ => n.Prime) (fun n : ℕ => Real.log (n : ℝ))
    rw [hfilter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : n.Prime <;> simp [residual, hp, vonMangoldt_apply_prime]
  have hsubset : s ⊆ Finset.range (x+1) := by
    intro n hn
    have hnle := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hnle)
  have hmass : (∑ n ∈ s, residual n) ≤ Chebyshev.psi x - Chebyshev.theta x := by
    rw [← residual_mass]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun n _ _ => hnonneg n)
  have hupper : (∑ n ∈ s, residual n) ≤ B * Real.sqrt x :=
    hmass.trans ((hK x).trans (mul_le_mul_of_nonneg_right (le_max_left K 1) (Real.sqrt_nonneg _)))
  have hlog_le : Real.log 2 ≤ Real.log (2 * (x : ℝ)) := by
    apply Real.log_le_log (by norm_num)
    have hx' : (2 : ℝ) ≤ x := by exact_mod_cast hx
    linarith
  rw [hsplit]
  constructor
  · exact Finset.sum_nonneg (fun n _ => hnonneg n)
  · calc
      _ ≤ B * Real.sqrt x := hupper
      _ = (B / (Real.log 2) ^ 2) * Real.sqrt x * (Real.log 2) ^ 2 := by field_simp [hlog.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog.le hlog_le 2) (by positivity)
