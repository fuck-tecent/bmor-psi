import Mathlib
/- Weighted prime sum from the Goldbach project, revision 5a7853e, adapted there from
PrimeNumberTheoremAnd, IEANTN/Mertens.lean, c39a751132c88b6e8080b74c74023fd95b3d8be0 (Apache-2.0).
The reciprocal sum and prime product arguments are excerpted from Sushaan Kandukoori,
erdos-straus-lean, revision f6c99eaaca6ec7a7226a7a16bef1cd2b09e36660 (Apache-2.0). -/
namespace WeightedTorusJets.Mertens
open Real Finset Filter Asymptotics Topology
open ArithmeticFunction hiding log
theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)

lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]

theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]

noncomputable abbrev E₁Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x

theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring

theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring

noncomputable abbrev E₁p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x

theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

noncomputable abbrev E₁ : ℝ := ∑' p : ℕ, if p.Prime then (log p) / (p*(p-1)) else 0

lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl

theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

theorem E₁.nonneg : E₁ ≥ 0 :=
  tsum_nonneg E₁.summand_nonneg

theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem prime_log_div_bounded_error :
    ∃ C > 0, ∀ x : ℝ, 1 ≤ x →
      |∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p - log x| ≤ C := by
  refine ⟨log 4 + 6 + E₁, by positivity [E₁.nonneg], fun x hx => ?_⟩
  rw [Nat.primesLE_eq_filter_Ioc_zero]
  change |E₁p x| ≤ log 4 + 6 + E₁
  have hlog : 0 ≤ log 4 := by positivity
  exact abs_le.mpr
    ⟨by linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx],
     by linarith [E₁Λ.le hx, E₁p.le_E₁Λ x, E₁.nonneg]⟩

end WeightedTorusJets.Mertens
namespace ErdosStraus.PrimeEstimates.Mertens

open Finset Real

/-- The set of primes `p ≤ x`. -/
def primesUpTo (x : ℕ) : Finset ℕ :=
  (range (x + 1)).filter Nat.Prime

@[simp]
theorem mem_primesUpTo {p x : ℕ} : p ∈ primesUpTo x ↔ p.Prime ∧ p ≤ x := by
  simp [primesUpTo, and_comm]

theorem primesUpTo_eq_empty_of_le_one {x : ℕ} (hx : x ≤ 1) : primesUpTo x = ∅ := by
  ext p
  simp only [mem_primesUpTo, Finset.notMem_empty, iff_false]
  intro hp'
  have hp2 := hp'.1.two_le
  omega

/-- The sum `∑_{p ≤ x} 1/p`. -/
noncomputable def primeReciprocalSum (x : ℕ) : ℝ :=
  (primesUpTo x).sum fun p => 1 / (p : ℝ)

/-- The Euler product `∏_{p ≤ x} (1 - 1/p)`. -/
noncomputable def primeProduct (x : ℕ) : ℝ :=
  (primesUpTo x).prod fun p => 1 - 1 / (p : ℝ)

theorem primeFactor_pos {p : ℕ} (hp : p.Prime) :
    0 < 1 - 1 / (p : ℝ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact sub_pos.mpr ((div_lt_one (zero_lt_one.trans hp1)).mpr hp1)

theorem primeProduct_pos (x : ℕ) : 0 < primeProduct x := by
  unfold primeProduct
  exact Finset.prod_pos fun p hp => primeFactor_pos (mem_primesUpTo.mp hp).1

theorem log_primeProduct (x : ℕ) :
    log (primeProduct x) =
      (primesUpTo x).sum (fun p => log (1 - 1 / (p : ℝ))) := by
  unfold primeProduct
  rw [Real.log_prod]
  intro p hp
  exact (primeFactor_pos (mem_primesUpTo.mp hp).1).ne'

theorem abs_log_one_sub_add_le {t : ℝ} (ht0 : 0 < t) (htle : t ≤ 1 / 2) :
    |log (1 - t) + t| ≤ 2 * t ^ 2 := by
  have hpos : 0 < 1 - t := by linarith
  have hne : 1 - t ≠ 0 := ne_of_gt hpos
  have hub : log (1 - t) ≤ -t := by
    have h := Real.log_le_sub_one_of_pos hpos
    linarith
  have hlb : -t - 2 * t ^ 2 ≤ log (1 - t) := by
    have hrec2 : 1 / (1 - t) ≤ 1 + 2 * t := by
      rw [div_le_iff₀ hpos]
      nlinarith
    have hmul : t / (1 - t) ≤ t * (1 + 2 * t) := by
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left hrec2 (le_of_lt ht0)
    calc
      -t - 2 * t ^ 2 = -(t * (1 + 2 * t)) := by ring
      _ ≤ -(t / (1 - t)) := neg_le_neg hmul
      _ = 1 - (1 - t)⁻¹ := by field_simp [hne]; ring
      _ ≤ log (1 - t) := Real.one_sub_inv_le_log_of_pos hpos
  rw [abs_le]
  constructor <;> nlinarith

theorem abs_log_primeFactor_add_le {p : ℕ} (hp : p.Prime) :
    |log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)| ≤ 2 / (p : ℝ) ^ 2 := by
  have ht0 : 0 < 1 / (p : ℝ) := by
    exact div_pos one_pos (by exact_mod_cast hp.pos)
  have htle : 1 / (p : ℝ) ≤ 1 / 2 := by
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      (by exact_mod_cast hp.two_le)
  simpa only [div_pow, one_pow, mul_one_div] using
    abs_log_one_sub_add_le ht0 htle

end ErdosStraus.PrimeEstimates.Mertens
namespace ErdosStraus.PrimeEstimates
open Finset
theorem sum_Ico_weight_differences (u : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    (∑ k ∈ Ico m n, (u k - u (k + 1))) = u m - u n := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih => rw [Finset.sum_Ico_succ_top hmn, ih]; ring

theorem sum_Ioc_eq_prefix_sub (c : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    (∑ j ∈ Ioc m n, c j) =
      (∑ j ∈ Icc 0 n, c j) - (∑ j ∈ Icc 0 m, c j) := by
  have hsplit : (∑ j ∈ Icc 0 n, c j) =
      (∑ j ∈ Icc 0 m, c j) + (∑ j ∈ Ioc m n, c j) := by
    rw [← Finset.add_sum_Ioc_eq_sum_Icc (f := c) (Nat.zero_le n),
      ← Finset.add_sum_Ioc_eq_sum_Icc (f := c) (Nat.zero_le m),
      ← Finset.sum_Ioc_consecutive c (Nat.zero_le m) hmn]
    ring
  linarith
end ErdosStraus.PrimeEstimates
namespace ErdosStraus.PrimeEstimates.Mertens

open Filter MeasureTheory Real Set
open scoped Topology

theorem hasDerivAt_neg_inv_log {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t : ℝ => -(log t)⁻¹) (x⁻¹ / (log x) ^ 2) x := by
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hl0 : log x ≠ 0 := (log_pos hx).ne'
  refine ((Real.hasDerivAt_log hx0).inv hl0).neg.congr_deriv ?_
  simp [div_eq_mul_inv]

theorem inv_log_tendsto_zero :
    Tendsto (fun t : ℝ => -(log t)⁻¹) atTop (𝓝 0) := by
  simpa using Real.tendsto_log_atTop.inv_tendsto_atTop.neg

theorem integrableOn_inv_div_log_sq_Ioi {x : ℝ} (hx : 1 < x) :
    IntegrableOn (fun t : ℝ => t⁻¹ / (log t) ^ 2) (Ioi x) := by
  apply integrableOn_Ioi_deriv_of_nonneg' (g := fun t : ℝ => -(log t)⁻¹)
    (l := 0) (fun t ht => hasDerivAt_neg_inv_log (hx.trans_le ht))
    (fun t ht => div_nonneg (inv_nonneg.mpr (zero_lt_one.trans (hx.trans ht)).le)
      (sq_nonneg _)) inv_log_tendsto_zero

theorem integral_inv_div_log_sq_Ioi {x : ℝ} (hx : 1 < x) :
    (∫ t in Ioi x, t⁻¹ / (log t) ^ 2) = 1 / log x := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (g := fun t : ℝ => -(log t)⁻¹)
    (l := 0) (fun t ht => hasDerivAt_neg_inv_log (hx.trans_le ht))
    (fun t ht => div_nonneg (inv_nonneg.mpr (zero_lt_one.trans (hx.trans ht)).le)
      (sq_nonneg _)) inv_log_tendsto_zero
  simpa using h

theorem integral_interval_sub_Ioi {f : ℝ → ℝ} {a x : ℝ}
    (hf : IntegrableOn f (Ioi a)) (hx : a ≤ x) :
    (∫ t in a..x, f t) - (∫ t in Ioi a, f t) = -(∫ t in Ioi x, f t) := by
  have hdisj : Disjoint (Ioc a x) (Ioi x) := by
    apply Set.disjoint_left.mpr
    intro t ht ht'
    exact (not_lt_of_ge ht.2) ht'
  have h := setIntegral_union hdisj measurableSet_Ioi
    (hf.mono_set Ioc_subset_Ioi_self) (hf.mono_set (Ioi_subset_Ioi hx))
  rw [Ioc_union_Ioi_eq_Ioi hx] at h
  rw [intervalIntegral.integral_of_le hx]
  linarith

end ErdosStraus.PrimeEstimates.Mertens
namespace ErdosStraus.PrimeEstimates.Mertens

open Finset Real
open scoped BigOperators
theorem mertensFirst :
    ∃ C > 0, ∀ x : ℝ, 2 ≤ x →
      |(∑ p ∈ primesUpTo ⌊x⌋₊, log p / p) - log x| ≤ C := by
  obtain ⟨C,hC,hh⟩ := WeightedTorusJets.Mertens.prime_log_div_bounded_error
  refine ⟨C,hC, fun x hx => ?_⟩
  have heq : primesUpTo ⌊x⌋₊ = Nat.primesLE ⌊x⌋₊ := by
    ext q
    simp [Nat.mem_primesLE, and_comm]
  rw [heq]
  exact hh x (by linarith)
/-- `B₁(x) = ∑_{p ≤ x} log p / p`. -/
noncomputable def primeLogReciprocal (x : ℝ) : ℝ := ∑ p ∈ primesUpTo ⌊x⌋₊, log p / p

/-- The remainder `R(x) = B₁(x) - log x` in Mertens' first theorem. -/
noncomputable def mertensRemainder (x : ℝ) : ℝ := primeLogReciprocal x - log x

/-- `R(x) = B₁(x) - log x` is bounded on `[2, ∞)`. -/
theorem mertensRemainder_bound :
    ∃ C > 0, ∀ x : ℝ, 2 ≤ x → |mertensRemainder x| ≤ C :=
  mertensFirst

/-- Express `B₁(x)` as a sum over primes up to the given bound. -/
theorem primeLogReciprocal_eq_sum_Icc (x : ℝ) :
    primeLogReciprocal x =
      ∑ n ∈ Icc 0 ⌊x⌋₊, if n.Prime then log (n : ℝ) / n else 0 := by
  rw [primeLogReciprocal, primesUpTo, sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext n
  simp only [mem_range, mem_Icc]
  omega

theorem measurable_primeLogReciprocal : Measurable primeLogReciprocal :=
  (measurable_of_countable
    (fun N : ℕ => ∑ p ∈ primesUpTo N, log (p : ℝ) / p)).comp Nat.measurable_floor

theorem measurable_mertensRemainder : Measurable mertensRemainder :=
  measurable_primeLogReciprocal.sub measurable_log

end ErdosStraus.PrimeEstimates.Mertens

/-! ## Mertens' second theorem

Abel summation against `B₁` gives
`∑_{p ≤ x} 1/p = B₁(x)/log x + ∫_2^x B₁(t)/(t (log t)²) dt`.
Writing `B₁(t) = log t + R(t)` with `R` bounded, the error integral converges
with tail `O(1/log x)`, so `∑_{p ≤ x} 1/p = log log x + B + O(1/log x)`.
-/

namespace ErdosStraus.PrimeEstimates.Mertens

open Filter Finset MeasureTheory Real
open scoped BigOperators

/-- A function dominated by `C / (t (log t)²)` has tail integral at most `C / log x`. -/
theorem norm_integral_Ioi_le_div_log {f : ℝ → ℝ} {x C : ℝ} (hx : 1 < x)
    (hbound : ∀ t ∈ Set.Ioi x, ‖f t‖ ≤ C * (t⁻¹ / (log t) ^ 2)) :
    ‖∫ t in Set.Ioi x, f t‖ ≤ C / log x := by
  have hk : IntegrableOn (fun t : ℝ => t⁻¹ / (log t) ^ 2) (Set.Ioi x) volume :=
    integrableOn_inv_div_log_sq_Ioi hx
  have hCk : IntegrableOn (fun t : ℝ => C * (t⁻¹ / (log t) ^ 2)) (Set.Ioi x) volume :=
    hk.const_mul C
  calc
    ‖∫ t in Set.Ioi x, f t‖ ≤ ∫ t in Set.Ioi x, C * (t⁻¹ / (log t) ^ 2) := by
      apply MeasureTheory.norm_integral_le_of_norm_le hCk
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hbound t ht
    _ = C * ∫ t in Set.Ioi x, t⁻¹ / (log t) ^ 2 := by rw [integral_const_mul]
    _ = C / log x := by rw [integral_inv_div_log_sq_Ioi hx]; ring

/-- `(1 / log t)' = -1 / (t (log t)²)`. -/
theorem hasDerivAt_inv_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun u : ℝ => (log u)⁻¹) (-(t⁻¹ / (log t) ^ 2)) t := by
  convert (hasDerivAt_neg_inv_log ht).neg using 1 <;> first | rfl | (ext u; simp)
/-- Abel summation against `B₁`:
`∑_{p ≤ x} 1/p = B₁(x)/log x + ∫_2^x B₁(t)/(t (log t)²) dt`. -/
theorem primeReciprocalSum_abel {x : ℝ} (hx : 2 ≤ x) :
    primeReciprocalSum ⌊x⌋₊ =
      primeLogReciprocal x / log x +
        ∫ t in (2 : ℝ)..x, primeLogReciprocal t / (t * (log t) ^ 2) := by
  let c : ℕ → ℝ := fun n => if n.Prime then log (n : ℝ) / n else 0
  let f : ℝ → ℝ := fun u => (log u)⁻¹
  have hderiv : ∀ t : ℝ, 1 < t → deriv f t = -(t⁻¹ / (log t) ^ 2) :=
    fun t ht => (hasDerivAt_inv_log ht).deriv
  have hf : ∀ t ∈ Set.Icc 2 x, DifferentiableAt ℝ f t :=
    fun t ht => (hasDerivAt_inv_log (by linarith [ht.1])).differentiableAt
  have hfi : IntegrableOn (deriv f) (Set.Icc 2 x) := by
    have hc : ContinuousOn (fun t : ℝ => -(t⁻¹ / (log t) ^ 2)) (Set.Icc 2 x) := by
      have hlog : ContinuousOn log (Set.Icc 2 x) := fun t ht =>
        (Real.continuousAt_log (by linarith [ht.1])).continuousWithinAt
      refine (((continuousOn_id' _).inv₀ fun t ht => ?_).div (hlog.pow 2) fun t ht => ?_).neg
      · exact (show (0 : ℝ) < t by linarith [ht.1]).ne'
      · exact pow_ne_zero 2 (log_pos (by linarith [ht.1])).ne'
    exact hc.integrableOn_Icc.congr_fun
      (fun t ht => (hderiv t (by linarith [ht.1])).symm) measurableSet_Icc
  have h := sum_mul_eq_sub_sub_integral_mul c (by norm_num : (0 : ℝ) ≤ 2) hx hf hfi
  have hfloor : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx
  simp only [Nat.floor_ofNat] at h
  rw [sum_Ioc_eq_prefix_sub (fun n => f n * c n) hfloor] at h
  have hinit : (∑ n ∈ Icc (0 : ℕ) 2, f n * c n) = f 2 * ∑ n ∈ Icc (0 : ℕ) 2, c n := by
    norm_num [c, Finset.sum_Icc_succ_top]
  have hB : ∀ t : ℝ, (∑ n ∈ Icc 0 ⌊t⌋₊, c n) = primeLogReciprocal t :=
    fun t => (primeLogReciprocal_eq_sum_Icc t).symm
  have hsum : (∑ n ∈ Icc 0 ⌊x⌋₊, f n * c n) = primeReciprocalSum ⌊x⌋₊ := by
    unfold primeReciprocalSum primesUpTo
    have hset : range (⌊x⌋₊ + 1) = Icc 0 ⌊x⌋₊ := by
      ext n
      simp only [mem_range, mem_Icc]
      omega
    rw [hset, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hp : n.Prime
    · have hl : log (n : ℝ) ≠ 0 := (log_pos (by exact_mod_cast hp.one_lt)).ne'
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      simp only [c, f, hp, if_true]
      field_simp
    · simp [c, hp]
  rw [hinit, hsum] at h
  simp_rw [hB] at h
  rw [← intervalIntegral.integral_of_le hx] at h
  have hint : -(∫ t in (2 : ℝ)..x, deriv f t * primeLogReciprocal t) =
      ∫ t in (2 : ℝ)..x, primeLogReciprocal t / (t * (log t) ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht1 : 1 < t := by linarith [ht.1]
    have ht0 : t ≠ 0 := by linarith
    have hl0 : log t ≠ 0 := (log_pos ht1).ne'
    simp only [hderiv t ht1]
    field_simp
  have hfx : f x * primeLogReciprocal x = primeLogReciprocal x / log x := by
    simp only [f]; ring
  linarith

/-- The integrand `R(t) / (t (log t)²)` of the remainder in Mertens' second theorem. -/
noncomputable def mertensKernel (t : ℝ) : ℝ := mertensRemainder t * (t⁻¹ / (log t) ^ 2)

theorem measurable_mertensKernel : Measurable mertensKernel :=
  measurable_mertensRemainder.mul (measurable_inv.div (measurable_log.pow_const 2))

/-- `|R(t) / (t (log t)²)| ≤ C / (t (log t)²)` whenever `|R(t)| ≤ C`. -/
theorem norm_mertensKernel_le {C t : ℝ} (ht : 0 ≤ t) (hR : |mertensRemainder t| ≤ C) :
    ‖mertensKernel t‖ ≤ C * (t⁻¹ / (log t) ^ 2) := by
  have hpos : 0 ≤ t⁻¹ / (log t) ^ 2 := by positivity
  rw [Real.norm_eq_abs, mertensKernel, abs_mul, abs_of_nonneg hpos]
  exact mul_le_mul_of_nonneg_right hR hpos

/-- The error integral `∫_2^∞ R(t) / (t (log t)²) dt` converges. -/
theorem integrableOn_mertensKernel : IntegrableOn mertensKernel (Set.Ioi 2) := by
  obtain ⟨C, _, hR⟩ := mertensRemainder_bound
  have hg : IntegrableOn (fun t : ℝ => C * (t⁻¹ / (log t) ^ 2)) (Set.Ioi 2) :=
    (integrableOn_inv_div_log_sq_Ioi (by norm_num)).const_mul C
  refine hg.mono' measurable_mertensKernel.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht2 : (2 : ℝ) ≤ t := le_of_lt ht
  exact norm_mertensKernel_le (by linarith) (hR t ht2)

/-- The constant `B` in `∑_{p ≤ x} 1/p = log log x + B + O(1/log x)`. -/
noncomputable def mertensSecondConstant : ℝ :=
  1 - log (log 2) + ∫ t in Set.Ioi (2 : ℝ), mertensKernel t

/-- The remainder in Mertens' second theorem:
`∑_{p ≤ x} 1/p - log log x - B = R(x)/log x - ∫_x^∞ R(t)/(t (log t)²) dt`. -/
theorem mertensSecond_error_eq {x : ℝ} (hx : 2 ≤ x) :
    primeReciprocalSum ⌊x⌋₊ - (log (log x) + mertensSecondConstant) =
      mertensRemainder x / log x - ∫ t in Set.Ioi x, mertensKernel t := by
  have hlx : 0 < log x := log_pos (by linarith)
  have hlog : ContinuousOn log (Set.Icc 2 x) := fun t ht =>
    (Real.continuousAt_log (by linarith [ht.1])).continuousWithinAt
  have hK : IntervalIntegrable mertensKernel volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mpr
      (integrableOn_mertensKernel.mono_set Set.Ioc_subset_Ioi_self)
  have hL : IntervalIntegrable (fun t : ℝ => t⁻¹ / log t) volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    refine ((continuousOn_id' _).inv₀ fun t ht => ?_).div hlog fun t ht => ?_
    · exact (show (0 : ℝ) < t by linarith [ht.1]).ne'
    · exact (log_pos (by linarith [ht.1])).ne'
  have hsplit : (∫ t in (2 : ℝ)..x, primeLogReciprocal t / (t * (log t) ^ 2)) =
      (∫ t in (2 : ℝ)..x, t⁻¹ / log t) + ∫ t in (2 : ℝ)..x, mertensKernel t := by
    rw [← intervalIntegral.integral_add hL hK]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl0 : log t ≠ 0 := (log_pos (by linarith [ht.1])).ne'
    simp only [mertensKernel, mertensRemainder]
    field_simp
    ring
  have hloglog : (∫ t in (2 : ℝ)..x, t⁻¹ / log t) = log (log x) - log (log 2) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hL
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl0 : log t ≠ 0 := (log_pos (by linarith [ht.1])).ne'
    exact (Real.hasDerivAt_log ht0).log hl0
  have htail := integral_interval_sub_Ioi integrableOn_mertensKernel hx
  have hBx : primeLogReciprocal x / log x = 1 + mertensRemainder x / log x := by
    unfold mertensRemainder
    field_simp
    ring
  rw [primeReciprocalSum_abel hx, hsplit, hloglog, hBx]
  unfold mertensSecondConstant
  linarith

/-- Mertens' second theorem: `∑_{p ≤ x} 1/p = log log x + B + O(1/log x)`. -/
theorem mertensSecond :
    ∃ C > 0, ∀ x : ℝ, 2 ≤ x →
      |primeReciprocalSum ⌊x⌋₊ - (log (log x) + mertensSecondConstant)| ≤ C / log x := by
  obtain ⟨C, hC, hR⟩ := mertensRemainder_bound
  refine ⟨2 * C, by positivity, fun x hx => ?_⟩
  have hlx : 0 < log x := log_pos (by linarith)
  rw [mertensSecond_error_eq hx]
  have h1 : |mertensRemainder x / log x| ≤ C / log x := by
    rw [abs_div, abs_of_pos hlx]
    exact div_le_div_of_nonneg_right (hR x hx) hlx.le
  have h2 : ‖∫ t in Set.Ioi x, mertensKernel t‖ ≤ C / log x :=
    norm_integral_Ioi_le_div_log (by linarith) fun t ht =>
      norm_mertensKernel_le (by linarith [ht.out]) (hR t (hx.trans ht.out.le))
  rw [Real.norm_eq_abs] at h2
  calc
    _ ≤ |mertensRemainder x / log x| + |∫ t in Set.Ioi x, mertensKernel t| := abs_sub _ _
    _ ≤ C / log x + C / log x := add_le_add h1 h2
    _ = 2 * C / log x := by ring

end ErdosStraus.PrimeEstimates.Mertens



/- The dyadic order decomposition follows Heath-Brown and Puchta, equation (26).
   We establish the cumulative estimate using the common product of Mersenne numbers. -/
namespace Goldbach.OrderTail
open Finset Real ErdosStraus.PrimeEstimates.Mertens

def common (k : ℕ) := ∏ i ∈ range k, (2^(i+1)-1:ℕ)

theorem common_pos (k : ℕ) : 0 < common k := by
  apply Finset.prod_pos
  intro i _
  have h : 1 < (2:ℕ)^(i+1) := Nat.one_lt_pow (by omega) (by decide)
  omega

theorem common_bound (k : ℕ) : common k ≤ 2^(k^2) := by
  calc common k ≤ ∏ _i ∈ range k, (2:ℕ)^k := by
        apply prod_le_prod
        intro i hi
        exact (Nat.sub_le ..).trans (Nat.pow_le_pow_right (by decide) (mem_range.mp hi))
    _ = _ := by simp [← pow_mul,sq]

noncomputable def ord (d : ℕ) := orderOf (2 : ZMod d)

theorem dvd_common {d k : ℕ} (ho : 0 < ord d) (hk : ord d ≤ k) : d ∣ common k := by
  have h : ((2^(ord d):ℕ) : ZMod d) = (1:ℕ) := by
    simpa only [ord,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using (pow_orderOf_eq_one (2:ZMod d))
  have hdiv : d ∣ 2^ord d - 1 :=
    ((ZMod.natCast_eq_natCast_iff _ _ d).mp h).symm.dvd'
  exact hdiv.trans (by
    have hmem : ord d-1 ∈ range k := mem_range.mpr (by omega)
    have hh := dvd_prod_of_mem (fun i => (2^(i+1)-1:ℕ)) hmem
    change (2^(ord d-1+1)-1 : ℕ) ∣ common k at hh
    rwa [show ord d-1+1=ord d by omega] at hh)

theorem factor_count (k : ℕ) : (common k).primeFactors.card ≤ k^2 := by
  have h : (2:ℕ)^(common k).primeFactors.card ≤ ∏ p ∈ (common k).primeFactors, p := by
    simpa using prod_le_prod (s:=(common k).primeFactors) (f:=fun _ => (2:ℕ)) (g:=id)
      (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (h.trans ((Nat.le_of_dvd (common_pos k) (Nat.prod_primeFactors_dvd _)).trans (common_bound k)))

theorem reciprocal_divisors (s : Finset ℕ) (m : ℕ) (hm : 0 < m)
    (hs : ∀ d ∈ s, Squarefree d ∧ d ∣ m) :
    (∑ d ∈ s, 1/(d:ℝ)) ≤ ∏ p ∈ m.primeFactors, (1+1/(p:ℝ)) := by
  let f := fun (a : Finset ℕ) => ∏ p ∈ a, (1/(p:ℝ))
  have eqv (d : ℕ) (hd : d ∈ s) : f d.primeFactors = 1/(d:ℝ) := by
    simp only [f,one_div,prod_inv_distrib]
    congr 1
    have hh := congrArg (fun v : ℕ => (v:ℝ)) (Nat.prod_primeFactors_of_squarefree (hs d hd).1)
    push_cast at hh
    exact hh
  have inj : Set.InjOn Nat.primeFactors s := by
    intro a ha b hb hab
    simpa only [Nat.prod_primeFactors_of_squarefree (hs a ha).1,
      Nat.prod_primeFactors_of_squarefree (hs b hb).1] using congrArg (fun t : Finset ℕ => ∏ p ∈ t,p) hab
  have sub : s.image Nat.primeFactors ⊆ m.primeFactors.powerset := by
    intro v hv
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hv
    exact mem_powerset.mpr (Nat.primeFactors_mono (hs d hd).2 hm.ne')
  rw [prod_one_add]
  calc (∑ d ∈ s, 1/(d:ℝ)) = ∑ a ∈ s.image Nat.primeFactors, f a := by
        rw [sum_image inj]
        exact sum_congr rfl (fun d hd => (eqv d hd).symm)
    _ ≤ ∑ a ∈ m.primeFactors.powerset, f a := sum_le_sum_of_subset_of_nonneg sub (fun a _ _ => by dsimp [f]; positivity)

theorem euler_bound : ∃ A : ℝ, 0 < A ∧ ∀ k : ℕ, 2 ≤ k →
    (∏ p ∈ (common k).primeFactors, (1+1/(p:ℝ))) ≤ A * log (2*(k:ℝ)) := by
  obtain ⟨C,hC,hrec⟩ := mertensSecond
  let B := mertensSecondConstant + C/log 2 + 1
  refine ⟨2*exp B, by positivity, ?_⟩
  intro k hk
  let S := (common k).primeFactors
  let x := (k:ℝ)^2
  have hx : 2≤x := by
    dsimp [x]
    have h : (2:ℝ) ≤ k := by exact_mod_cast hk
    nlinarith only [h,sq_nonneg ((k:ℝ)-2)]
  have hxlog : 0 < log x := log_pos (by linarith)
  have hxceil : ⌊x⌋₊=k^2 := by dsimp [x]; exact_mod_cast Nat.floor_natCast (k^2)
  have hrs := (abs_le.mp (hrec x hx)).2
  rw [hxceil] at hrs
  have hCdiv : C / log x ≤ C / log 2 :=
    div_le_div_of_nonneg_left hC.le (log_pos (by norm_num)) (log_le_log (by norm_num) hx)
  have small : (∑ p ∈ S.filter (fun p => p≤k^2), 1/(p:ℝ)) ≤ primeReciprocalSum (k^2) := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hmem,hle⟩ := mem_filter.mp hp
      exact mem_primesUpTo.mpr ⟨Nat.prime_of_mem_primeFactors hmem, hle⟩
    · intro _ _ _; positivity
  have hcount : ((S.filter (fun p => ¬p≤k^2)).card:ℝ) ≤ x := by
    dsimp only [x]
    exact_mod_cast ((card_filter_le S (fun p => ¬p≤k^2)).trans (factor_count k))
  have big : (∑ p ∈ S.filter (fun p => ¬p≤k^2), 1/(p:ℝ)) ≤ 1 := by
    calc _ ≤ ∑ _p ∈ S.filter (fun p => ¬p≤k^2), (1:ℝ)/x := by
             apply sum_le_sum
             intro p hp
             have hl : k^2 ≤ p := by have h := (mem_filter.mp hp).2; omega
             exact one_div_le_one_div_of_le (by linarith) (by dsimp only [x]; exact_mod_cast hl)
         _ ≤ 1 := by simp only [sum_const,nsmul_eq_mul,mul_one_div]; exact (div_le_one (by linarith)).mpr hcount
  have hsum : (∑ p ∈ S, 1/(p:ℝ)) ≤ log (log x) + B := by
    have hsplit := sum_filter_add_sum_filter_not S (fun p => p≤k^2) (fun p => 1/(p:ℝ))
    dsimp only [B]
    linarith only [hsplit,small,big,hrs,hCdiv]
  have hxid : log x ≤ 2*log (2*(k:ℝ)) := by
    rw [show log x = 2 * log (k:ℝ) by simp [x,log_pow]]
    have h : 0 < (k:ℝ) := by exact_mod_cast (show 0<k by omega)
    gcongr
    linarith
  calc _ ≤ ∏ p ∈ S, exp (1/(p:ℝ)) := by
             apply prod_le_prod₀
             · intro _ _; positivity
             · intro p _; linarith only [Real.add_one_le_exp (1/(p:ℝ))]
       _ = exp (∑ p ∈ S, 1/(p:ℝ)) := (Real.exp_sum ..).symm
       _ ≤ exp (log (log x) + B) := exp_le_exp.mpr hsum
       _ ≤ _ := by rw [exp_add,exp_log hxlog]; nlinarith only [mul_le_mul_of_nonneg_right hxid (exp_pos B).le]


theorem tail : ∃ C : ℝ, 0<C ∧ ∀ T D : ℕ, 2≤T →
    (∑ d ∈ (Finset.Icc 3 D).filter (fun d => Odd d ∧ (∀ p ∈ d.primeFactors, d.factorization p ≤ 1) ∧ T < orderOf (2 : ZMod d)),
      1/((d:ℝ)*(orderOf (2 : ZMod d):ℝ))) ≤ C*Real.log (2*(T:ℝ))/(T:ℝ) := by
  classical
  obtain ⟨A,hA,hEuler⟩ := euler_bound
  let w (d : ℕ) := 1/((d:ℝ)*(ord d:ℝ))
  have window (t : ℕ) (ht : 2≤t) (s : Finset ℕ)
      (hs : ∀ d ∈ s, Squarefree d ∧ t < ord d ∧ ord d ≤ 2*t) :
      (∑ d ∈ s, w d) ≤ A*log (2*(2*(t:ℝ)))/t := by
    have hrec := reciprocal_divisors s (common (2*t)) (common_pos _) (fun d hd =>
      ⟨(hs d hd).1, dvd_common (by have h := (hs d hd).2.1; omega) (hs d hd).2.2⟩)
    have hh := hrec.trans (hEuler (2*t) (by omega))
    push_cast at hh
    calc _ ≤ ∑ d ∈ s, (1/(d:ℝ))/(t:ℝ) := by
               apply sum_le_sum
               intro d hd
               dsimp only [w]
               rw [← div_div]
               apply div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast (show 0<t by omega))
               exact_mod_cast (hs d hd).2.1.le
         _ ≤ _ := by rw [← sum_div]; exact div_le_div_of_nonneg_right hh (Nat.cast_nonneg _)
  have iter (j t : ℕ) (ht : 2≤t) (s : Finset ℕ)
      (hs : ∀ d ∈ s, Squarefree d ∧ t < ord d ∧ ord d ≤ 2^j*t) :
      (∑ d ∈ s, w d) ≤ (6*A)*log (2*(t:ℝ))/t := by
    induction j generalizing s t with
    | zero =>
      have emp : s=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro d hd
        obtain ⟨_,a,b⟩ := hs d hd
        simp only [pow_zero,one_mul] at b
        omega
      rw [emp,sum_empty]
      have h : 0 < (t:ℝ) := by exact_mod_cast (show 0<t by omega)
      exact div_nonneg (mul_nonneg (by positivity) (log_nonneg (by linarith [show (2:ℝ)≤t by exact_mod_cast ht]))) h.le
    | succ j ih =>
      let P := fun d => ord d ≤ 2*t
      have hlow := window t ht (s.filter P) (fun d hd =>
        ⟨(hs d (mem_filter.mp hd).1).1,(hs d (mem_filter.mp hd).1).2.1,(mem_filter.mp hd).2⟩)
      have hhigh := ih (2*t) (by omega) (s.filter (fun d => ¬P d)) (by
        intro d hd
        obtain ⟨hmem,hh⟩ := mem_filter.mp hd
        obtain ⟨hsq,_,hle⟩ := hs d hmem
        exact ⟨hsq,lt_of_not_ge hh,by simpa only [pow_succ,mul_assoc] using hle⟩)
      have hsplit := sum_filter_add_sum_filter_not s P w
      have htr : (2:ℝ)≤t := by exact_mod_cast ht
      have htpos : (0:ℝ)<t := by linarith
      have hlog : 2 * log 2 ≤ log (2*(t:ℝ)) := by
        rw [log_mul (by norm_num) htpos.ne']
        linarith only [log_le_log (by norm_num : (0:ℝ)<2) htr]
      have hlog' : log (2*(2*(t:ℝ))) = log 2 + log (2*t) := log_mul (by norm_num) (by positivity)
      push_cast at hhigh
      rw [le_div_iff₀ htpos] at hlow ⊢
      rw [le_div_iff₀ (by positivity : 0 < 2*(t:ℝ))] at hhigh
      rw [hlog'] at hlow hhigh
      rw [← hsplit,add_mul]
      nlinarith only [hlow,hhigh,mul_le_mul_of_nonneg_left hlog hA.le]
  refine ⟨6*A,by positivity,?_⟩
  intro t D ht
  let s := (Icc 3 D).filter (fun d => Odd d ∧ (∀ p ∈ d.primeFactors, d.factorization p ≤ 1) ∧ t < ord d)
  let J := s.sup ord
  change (∑ d ∈ s, w d) ≤ _
  apply iter J t ht s
  intro d hd
  obtain ⟨hmem,_,hsq,hord⟩ := mem_filter.mp hd
  have hd0 : d ≠ 0 := by have h := (mem_Icc.mp hmem).1; omega
  refine ⟨Nat.squarefree_of_factorization_le_one hd0 (fun p => ?_),hord,?_⟩
  · by_cases hp : p ∈ d.primeFactors
    · exact hsq p hp
    · have hzero : d.factorization p = 0 := by
        simpa only [← Finsupp.notMem_support_iff,Nat.support_factorization] using hp
      omega
  · have hb : ord d ≤ J := Finset.le_sup hd
    exact hb.trans ((Nat.le_of_lt (show J < 2^J from Nat.lt_two_pow_self)).trans (Nat.le_mul_of_pos_right _ (by omega)))

end Goldbach.OrderTail

theorem Conjectures.Goldbach.BinaryShiftOrderTail :
    ∃ C : ℝ, 0<C ∧ ∀ T D : ℕ, 2≤T → (∑ d ∈ (Finset.Icc 3 D).filter (fun d => Odd d ∧ (∀ p ∈ d.primeFactors, d.factorization p ≤ 1) ∧ T < orderOf (2 : ZMod d)), 1/((d:ℝ)*(orderOf (2 : ZMod d):ℝ))) ≤ C*Real.log (2*(T:ℝ))/(T:ℝ) := Goldbach.OrderTail.tail
