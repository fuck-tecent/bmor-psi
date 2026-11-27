import Mathlib

private theorem no_middle_cubes :
    let block := fun x : ℕ => Finset.Ioc x (2*x); ∀ x n p : ℕ, 5≤x → n ∈ block x → x<p → ¬ p^3 ∣ n^2+1 := by
  intro block x n p hx hn hp
  have hn_upper : n ≤ 2 * x := (Finset.mem_Ioc.mp hn).2
  have hcube : (x + 1) ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp 3
  have hsquare : n ^ 2 ≤ (2 * x) ^ 2 := Nat.pow_le_pow_left hn_upper 2
  have hlarge : (2 * x) ^ 2 + 1 < (x + 1) ^ 3 := by
    have hxsq : 5 * x ≤ x ^ 2 := by nlinarith
    have hxcube : 5 * x ^ 2 ≤ x ^ 3 := by nlinarith [sq_nonneg (x : ℤ)]
    nlinarith
  intro hdvd
  have hle : p ^ 3 ≤ n ^ 2 + 1 := Nat.le_of_dvd (by positivity) hdvd
  omega

theorem PEqualNP.Outside.L_quadratic_primes_levent_middle_square_weight :
    let block := fun x : ℕ => Finset.Ioc x (2*x); let band := fun a x n : ℕ => (n^2+a).primeFactors.filter (fun p => x<p ∧ p^100000 ≤ n^132301); ∀ x n : ℕ, 5≤x → n ∈ block x → (∑ p ∈ band 1 x n, (((n^2+1).factorization p - 1 : ℕ) : ℝ)*Real.log (p : ℝ)) = ∑ p ∈ (band 1 x n).filter (fun p => p^2 ∣ n^2+1), Real.log (p : ℝ) := by
  intro block band x n hx hn
  conv_rhs => rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  have hband := Finset.mem_filter.mp hp
  have hprime := Nat.prime_of_mem_primeFactors hband.1
  have hdiv := Nat.dvd_of_mem_primeFactors hband.1
  have hm : n ^ 2 + 1 ≠ 0 := by positivity
  have hvalpos : 1 ≤ (n ^ 2 + 1).factorization p := by
    apply (hprime.pow_dvd_iff_le_factorization hm).mp
    simpa using hdiv
  have hnocube : ¬ p ^ 3 ∣ n ^ 2 + 1 := no_middle_cubes x n p hx hn hband.2.1
  have hvalbound : (n ^ 2 + 1).factorization p < 3 := by
    by_contra hnlt
    exact hnocube ((hprime.pow_dvd_iff_le_factorization hm).mpr (by omega))
  by_cases hsquare : p ^ 2 ∣ n ^ 2 + 1
  · have hv : (n ^ 2 + 1).factorization p = 2 := by
      have := (hprime.pow_dvd_iff_le_factorization hm).mp hsquare
      omega
    simp [hsquare, hv]
  · have hv : (n ^ 2 + 1).factorization p = 1 := by
      have hnot : ¬ 2 ≤ (n ^ 2 + 1).factorization p := fun h => hsquare ((hprime.pow_dvd_iff_le_factorization hm).mpr h)
      omega
    simp [hsquare, hv]
