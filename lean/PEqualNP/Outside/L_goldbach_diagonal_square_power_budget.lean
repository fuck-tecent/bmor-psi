import Mathlib

private noncomputable def primeGap (k : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt k - (if k.Prime then Real.log (k:ℝ) else 0)

private lemma primeGap_eq (k : ℕ) :
    primeGap k = if ¬k.Prime then ArithmeticFunction.vonMangoldt k else 0 := by
  by_cases hp : k.Prime <;> simp [primeGap, hp, ArithmeticFunction.vonMangoldt_apply_prime]

private lemma primeGap_nonneg (k : ℕ) : 0 ≤ primeGap k := by
  rw [primeGap_eq]
  split <;> first | exact le_rfl | exact ArithmeticFunction.vonMangoldt_nonneg

private lemma totalGap (n : ℕ) (hn : 2 ≤ n) :
    (∑ k ∈ Finset.range (n+1), primeGap k) ≤ 2*Real.sqrt (n:ℝ)*(Real.log (2*(n:ℝ)))^2 := by
  have hsum : (∑ k ∈ Finset.range (n+1), primeGap k) = Chebyshev.psi n - Chebyshev.theta n := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, Finset.sum_filter]
    simp_rw [← primeGap_eq]
    symm
    apply Finset.sum_subset
    · intro k hk
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Ioc.mp hk).2)
    · intro k hk hnot
      have hk' := Finset.mem_range.mp hk
      have hzero : k = 0 := by
        by_contra h
        exact hnot (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero h, by omega⟩)
      simp [hzero, primeGap]
  rw [hsum]
  have hn' : 2 ≤ (n:ℝ) := by exact_mod_cast hn
  have hlog : 1 ≤ Real.log (2*(n:ℝ)) := (Real.le_log_iff_exp_le (by positivity)).2
    (by linarith [Real.exp_one_lt_three])
  have hlog' : Real.log (n:ℝ) ≤ Real.log (2*(n:ℝ)) := Real.log_le_log (by positivity) (by linarith)
  exact (Chebyshev.psi_sub_theta_le (by linarith : 1 ≤ (n:ℝ))).trans
    (mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg (sub_nonneg.mpr hlog) (le_trans zero_le_one hlog)])
      (by positivity))

theorem PEqualNP.Outside.L_goldbach_diagonal_square_power_budget :
    let p := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let D := fun (φ : ℝ → ℝ) (n : ℕ) => (∑ k ∈ (Finset.range (n+1)).filter (fun k => k.Coprime n), (ArithmeticFunction.vonMangoldt k)^2*(φ ((k:ℝ)/n))^2)/(n:ℝ); ∃ K : ℝ, 0<K ∧ ∀ (n : ℕ) (φ : ℝ → ℝ), 2≤n → (∀ u, |φ u|≤1) → (∀ u : ℝ, u < 1/3 ∨ 2/3 < u → φ u=0) → |D φ n - (∑ k ∈ Finset.range (n+1), (p k)^2*(φ ((k:ℝ)/n))^2)/(n:ℝ)| ≤ K*(Real.log (2*(n:ℝ)))^3/Real.sqrt (n:ℝ) := by
  intro p D
  refine ⟨3, by norm_num, ?_⟩
  intro n φ hn hφ _
  let I := Finset.range (n+1)
  let L := Real.log (2*(n:ℝ))
  let u (k : ℕ) := (φ ((k:ℝ)/n))^2
  let loss (k : ℕ) := if k ∈ n.primeFactors then Real.log (k:ℝ) else 0
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hL : 1 ≤ L := (Real.le_log_iff_exp_le (by positivity)).2 (by linarith [Real.exp_one_lt_three])
  have hlog : Real.log (n:ℝ) ≤ L := Real.log_le_log hn0 (by linarith)
  have hpow (k : ℕ) : 0 ≤ u k ∧ u k ≤ 1 := by
    have hh := sq_le_sq₀ (abs_nonneg (φ ((k:ℝ)/n))) zero_le_one |>.2 (hφ _)
    exact ⟨sq_nonneg _, by simpa [u, sq_abs] using hh⟩
  have hΛ {k : ℕ} (hk : k ∈ I) : ArithmeticFunction.vonMangoldt k ≤ L := by
    by_cases hzero : k=0
    · simp [hzero]; linarith
    · have hkn := Finset.mem_range.mp hk
      exact ArithmeticFunction.vonMangoldt_le_log.trans ((Real.log_le_log
        (by exact_mod_cast Nat.pos_of_ne_zero hzero) (by exact_mod_cast (show k ≤ n by omega))).trans hlog)
  have point (k : ℕ) (hk : k ∈ I) :
      |(if k.Coprime n then (ArithmeticFunction.vonMangoldt k)^2 * u k else 0) - (p k)^2 * u k|
        ≤ (primeGap k + loss k)*L := by
    have hnon : 0 ≤ ArithmeticFunction.vonMangoldt k := ArithmeticFunction.vonMangoldt_nonneg
    have sqBound : (ArithmeticFunction.vonMangoldt k)^2 * u k ≤ ArithmeticFunction.vonMangoldt k * L :=
      (mul_le_of_le_one_right (sq_nonneg _) (hpow k).2).trans (by
        rw [sq]; exact mul_le_mul_of_nonneg_left (hΛ hk) hnon)
    by_cases hp : k.Prime
    · rw [ArithmeticFunction.vonMangoldt_apply_prime hp] at hnon sqBound ⊢
      have hgap : primeGap k = 0 := by simp [primeGap, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
      by_cases hc : k.Coprime n
      · have hmem : k ∉ n.primeFactors := by simp [Nat.mem_primeFactors, (hp.coprime_iff_not_dvd.mp hc)]
        simp only [ite_eq_left hc, p, ite_eq_left hp, hgap, loss, ite_eq_right hmem, sub_self, abs_zero, add_zero, zero_mul, le_refl]
      · have hmem : k ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp,
          by simpa [hp.coprime_iff_not_dvd] using hc, by omega⟩
        simpa only [ite_eq_right hc, p, ite_eq_left hp, hgap, loss, ite_eq_left hmem, zero_sub, abs_neg, zero_add, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hpow k).1)] using sqBound
    · have hmem : k ∉ n.primeFactors := fun h => hp (Nat.prime_of_mem_primeFactors h)
      have hgap : primeGap k = ArithmeticFunction.vonMangoldt k := by simp [primeGap, hp]
      by_cases hc : k.Coprime n
      · simpa only [ite_eq_left hc, p, ite_eq_right hp, hgap, loss, ite_eq_right hmem, zero_pow (by decide : 2 ≠ 0), zero_mul, sub_zero, add_zero, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hpow k).1)] using sqBound
      · simpa only [ite_eq_right hc, p, ite_eq_right hp, hgap, loss, ite_eq_right hmem, zero_pow (by decide : 2 ≠ 0), zero_mul, sub_zero, abs_zero, add_zero] using mul_nonneg hnon (zero_le_one.trans hL)
  have lost : (∑ k ∈ I, loss k) ≤ L := by
    rw [show (∑ k ∈ I, loss k) = ∑ k ∈ I.filter (· ∈ n.primeFactors), Real.log (k:ℝ) from
      (Finset.sum_filter _ _).symm]
    calc
      _ ≤ ∑ k ∈ n.primeFactors, Real.log (k:ℝ) := Finset.sum_le_sum_of_subset_of_nonneg
        (fun k hk => (Finset.mem_filter.mp hk).2) (fun k hk _ => Real.log_nonneg
          (by exact_mod_cast (Nat.prime_of_mem_primeFactors hk).one_le))
      _ ≤ Real.log (n:ℝ) := by
        rw [← Real.log_prod (s := n.primeFactors) (f := fun k : ℕ => (k:ℝ))
          (fun k hk => (by exact_mod_cast (Nat.prime_of_mem_primeFactors hk).ne_zero : (k:ℝ) ≠ 0)), ← Nat.cast_prod]
        exact Real.log_le_log (by exact_mod_cast Finset.prod_pos (fun k hk => (Nat.prime_of_mem_primeFactors hk).pos))
          (by exact_mod_cast Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n))
      _ ≤ L := hlog
  have hsum := (Finset.abs_sum_le_sum_abs _ I).trans (Finset.sum_le_sum point)
  rw [← Finset.sum_mul, Finset.sum_add_distrib] at hsum
  have root : 1 ≤ Real.sqrt (n:ℝ) := (Real.one_le_sqrt).2 (by linarith)
  have hdom : L ≤ Real.sqrt (n:ℝ)*L^2 := by
    calc
      _ ≤ L^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hL) (zero_le_one.trans hL)]
      _ ≤ _ := le_mul_of_one_le_left (sq_nonneg _) root
  have mass := totalGap n hn
  change (∑ k ∈ I, primeGap k) ≤ 2*Real.sqrt (n:ℝ)*L^2 at mass
  have rhs : ((∑ k ∈ I, primeGap k)+(∑ k ∈ I, loss k))*L ≤ 3*Real.sqrt (n:ℝ)*L^3 := by
    calc
      _ ≤ (2*Real.sqrt (n:ℝ)*L^2 + Real.sqrt (n:ℝ)*L^2)*L :=
        mul_le_mul_of_nonneg_right (add_le_add mass (lost.trans hdom)) (zero_le_one.trans hL)
      _ = _ := by ring
  have bound := hsum.trans rhs
  change |(∑ k ∈ I.filter (fun k => k.Coprime n), (ArithmeticFunction.vonMangoldt k)^2*u k)/(n:ℝ)
    - (∑ k ∈ I, (p k)^2*u k)/(n:ℝ)| ≤ 3*L^3/Real.sqrt (n:ℝ)
  rw [← sub_div, abs_div, abs_of_pos hn0, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine (div_le_div_of_nonneg_right bound hn0.le).trans_eq ?_
  field_simp [hn0.ne', (Real.sqrt_pos.mpr hn0).ne']
  nlinarith [Real.sq_sqrt hn0.le, congrArg (fun z : ℝ => 3*L^3*z) (Real.sq_sqrt hn0.le)]
