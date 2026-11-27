import Mathlib

open Filter Topology

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

private lemma slowLog :
    ∀ᶠ n : ℕ in Filter.atTop, 4096*(Real.log (n:ℝ))^11 ≤ Real.sqrt (n:ℝ) := by
  have bound := ((isLittleO_log_rpow_rpow_atTop 11 (by norm_num : (0:ℝ) < 1/2)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound (show (0:ℝ) < 1/4096 by norm_num)
  filter_upwards [bound, Filter.eventually_ge_atTop 1] with n h hn
  have hr : (0:ℝ) ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  have he : Real.log (n:ℝ)^(11:ℝ) = Real.log (n:ℝ)^11 := Real.rpow_natCast _ 11
  simp only [Function.comp_apply, Real.norm_eq_abs, he, abs_of_nonneg (pow_nonneg hr 11),
    ← Real.sqrt_eq_rpow, abs_of_nonneg (Real.sqrt_nonneg _)] at h
  linarith

theorem PEqualNP.Outside.L_goldbach_coset_sparse_power_block :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q=r); let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; let Q := fun n : ℕ => n/(Nat.log 2 n)^8; ∃ X : ℕ, ∀ n≥X, (∑ q ∈ Finset.Ioc (Q n) (2*Q n), ∑ r ∈ Finset.range q, ((∑ k ∈ F n q r, ArithmeticFunction.vonMangoldt k)-A n q r)^2) ≤ (n:ℝ)*(Q n:ℝ) := by
  intro F w A Q
  obtain ⟨X,hX⟩ := Filter.eventually_atTop.mp slowLog
  refine ⟨max X 2, ?_⟩
  intro n hn
  have htwo : 2 ≤ n := (le_max_right _ _).trans hn
  have small := hX n ((le_max_left _ _).trans hn)
  let M := (Nat.log 2 n)^8
  let L := Real.log (n:ℝ)
  have hnat : (2:ℝ) ≤ n := by exact_mod_cast htwo
  have hL : 0 ≤ L := Real.log_natCast_nonneg n
  have hmult : Real.log (2*(n:ℝ)) ≤ 2*L := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    have hlog := Real.log_le_log (by norm_num : (0:ℝ)<2) hnat
    dsimp [L]; linarith
  have hp : 0 < M := pow_pos (Nat.log_pos (by decide) htwo) _
  have base : ((Nat.log 2 n):ℝ) ≤ 2*L := by
    refine (Real.natLog_le_logb n 2).trans ?_
    change L / Real.log 2 ≤ 2*L
    apply (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).2
    nlinarith [mul_nonneg hL (sub_nonneg.mpr (show (1:ℝ)/2 ≤ Real.log 2 by linarith [Real.log_two_gt_d9]))]
  have hM : (M:ℝ) ≤ (2*L)^8 := by
    dsimp only [M]
    push_cast
    exact pow_le_pow_left₀ (by positivity) base _
  have gap (k : ℕ) (hk : k ∈ Finset.range (n+1)) : primeGap k ≤ L := by
    rw [primeGap_eq]
    split
    · by_cases hz : k = 0
      · simpa [hz] using hL
      · exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log
          (by exact_mod_cast Nat.pos_of_ne_zero hz) (by exact_mod_cast (show k ≤ n by have := Finset.mem_range.mp hk; omega)))
    · exact hL
  have forQ (q : ℕ) (hq : q ∈ Finset.Ioc (Q n) (2*Q n)) :
      (∑ r ∈ Finset.range q, ((∑ k ∈ F n q r, ArithmeticFunction.vonMangoldt k)-A n q r)^2) ≤ (n:ℝ) := by
    have hq' : n / M < q := (Finset.mem_Ioc.mp hq).1
    have pos : 0 < q := lt_of_le_of_lt (Nat.zero_le _) hq'
    have hlen : n+1 ≤ q*M := (Nat.div_lt_iff_lt_mul hp).1 hq'
    have hdiv : (n+1)/q ≤ M := by
      calc
        _ ≤ (q*M)/q := Nat.div_le_div_right hlen
        _ = M := Nat.mul_div_cancel_left _ pos
    let d (r : ℕ) := ∑ k ∈ F n q r, primeGap k
    have heq (r : ℕ) : (∑ k ∈ F n q r, ArithmeticFunction.vonMangoldt k)-A n q r=d r := by
      dsimp only [d, A, w, primeGap]; rw [Finset.sum_sub_distrib]
    have maxD (r : ℕ) (hr : r ∈ Finset.range q) : d r ≤ (2*(2*L)^8)*L := by
      have hr' := Finset.mem_range.mp hr
      have cnt := Nat.count_modEq_card (n+1) pos r
      rw [Nat.count_eq_card_filter_range] at cnt
      simp only [Nat.ModEq, Nat.mod_eq_of_lt hr'] at cnt
      have car : (F n q r).card ≤ 2*M := by
        change ((Finset.range (n+1)).filter (fun k => k % q = r)).card ≤ _
        split at cnt <;> omega
      calc
        _ ≤ ∑ _k ∈ F n q r, L := Finset.sum_le_sum fun k hk => gap k (Finset.mem_filter.mp hk).1
        _ ≤ _ := by
          simp only [Finset.sum_const,nsmul_eq_mul]
          apply mul_le_mul_of_nonneg_right _ hL
          exact (show ((F n q r).card:ℝ) ≤ 2*(M:ℝ) by exact_mod_cast car).trans (by linarith)
    have mass : (∑ r ∈ Finset.range q, d r) ≤ 2*Real.sqrt (n:ℝ)*(2*L)^2 := by
      have sumEq : (∑ r ∈ Finset.range q, d r) = ∑ k ∈ Finset.range (n+1), primeGap k :=
        Finset.sum_fiberwise_of_maps_to (fun k _ => Finset.mem_range.mpr (Nat.mod_lt k pos)) _
      rw [sumEq]
      refine (totalGap n htwo).trans ?_
      gcongr
      exact Real.log_nonneg (by linarith)
    simp_rw [heq]
    calc
      _ ≤ ∑ r ∈ Finset.range q, (2*(2*L)^8*L)*d r := Finset.sum_le_sum fun r hr => by
        rw [sq]; exact mul_le_mul_of_nonneg_right (maxD r hr) (Finset.sum_nonneg fun k _ => primeGap_nonneg k)
      _ ≤ (2*(2*L)^8*L)*(2*Real.sqrt (n:ℝ)*(2*L)^2) := by
        rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left mass (by positivity)
      _ = Real.sqrt (n:ℝ)*(4096*L^11) := by ring
      _ ≤ _ := by
        calc
          _ ≤ (Real.sqrt (n:ℝ))^2 := by rw [sq]; exact mul_le_mul_of_nonneg_left small (Real.sqrt_nonneg _)
          _ = _ := Real.sq_sqrt (by positivity)
  refine (Finset.sum_le_sum forQ).trans_eq ?_
  simp [Nat.card_Ioc, two_mul, mul_comm]
