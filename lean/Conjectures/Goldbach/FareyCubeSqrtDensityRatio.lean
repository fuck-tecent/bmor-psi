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

namespace GoldbachLateDensity
open Finset Real Filter
open ErdosStraus.PrimeEstimates.Mertens
open scoped Topology BigOperators
noncomputable section

def low (n : ℕ) : ℝ := (n:ℝ)^(1/3:ℝ)
def high (n : ℕ) : ℝ := (n:ℝ)^(1/2:ℝ)
def strip (n : ℕ) := primesUpTo ⌊high n⌋₊ \ primesUpTo ⌊low n⌋₊
def good (n : ℕ) := (strip n).filter fun p => ¬p∣n
def mass (s : Finset ℕ) : ℝ := ∑ p ∈ s, 1/(p:ℝ)
def tail (n : ℕ) : ℝ := ∏ p ∈ good n, (1-2/(p:ℝ))

lemma endpoints (n : ℕ) (hn : 64≤n) : 4 ≤ low n ∧ low n ≤ high n := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (by omega : 1≤n)
  constructor
  · rw [low,one_div,Real.le_rpow_inv_iff_of_pos (by norm_num) (by positivity) (by norm_num)]
    rw [show (3:ℝ)=((3:ℕ):ℝ) by norm_num,Real.rpow_natCast]
    norm_num
    exact_mod_cast hn
  · exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)

lemma strip_mem {n p : ℕ} (hp : p ∈ strip n) :
    p.Prime ∧ low n < p ∧ p ≤ ⌊high n⌋₊ := by
  obtain ⟨h,nl⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hpp,hh⟩ := mem_primesUpTo.mp h
  exact ⟨hpp,(Nat.floor_lt (by unfold low; positivity)).mp (by
    by_contra! hle; exact nl (mem_primesUpTo.mpr ⟨hpp,hle⟩)),hh⟩

lemma strip_mass (n : ℕ) (hn : 64≤n) :
    mass (strip n) = primeReciprocalSum ⌊high n⌋₊ - primeReciprocalSum ⌊low n⌋₊ := by
  have hsub : primesUpTo ⌊low n⌋₊ ⊆ primesUpTo ⌊high n⌋₊ := fun p hp =>
    mem_primesUpTo.mpr ⟨(mem_primesUpTo.mp hp).1,(mem_primesUpTo.mp hp).2.trans
      (Nat.floor_mono (endpoints n hn).2)⟩
  apply eq_sub_of_add_eq
  exact Finset.sum_sdiff hsub

theorem strip_mass_error : ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, 64≤n →
    |mass (strip n) - log (3/2:ℝ)| ≤ C / log n := by
  obtain ⟨C,hC,h⟩ := mertensSecond
  refine ⟨5*C,by positivity,?_⟩
  intro n hn
  obtain ⟨hl,hhl⟩ := endpoints n hn
  have h0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hlog : 0<log (n:ℝ) := log_pos (by exact_mod_cast (by omega : 1<n))
  have hu := abs_le.mp (h (high n) (by linarith))
  have hd := abs_le.mp (h (low n) (by linarith))
  have ha : log (high n) = (1/2:ℝ)*log n := log_rpow h0 _
  have hb : log (low n) = (1/3:ℝ)*log n := log_rpow h0 _
  have hdiff : log (log (high n)) - log (log (low n)) = log (3/2:ℝ) := by
    rw [ha,hb,← log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  rw [ha] at hu
  rw [hb] at hd
  rw [strip_mass n hn,← hdiff,ha,hb]
  have hu' : C/((1/2:ℝ)*log n) = 2*C/log n := by ring
  have hd' : C/((1/3:ℝ)*log n) = 3*C/log n := by ring
  rw [hu'] at hu
  rw [hd'] at hd
  rw [show 5*C/log (n:ℝ) = 2*C/log n + 3*C/log n by ring]
  rw [abs_le]
  constructor <;> linarith only [hu.1,hu.2,hd.1,hd.2]

theorem mass_limit : Tendsto (fun n => mass (strip n)) atTop (𝓝 (log (3/2:ℝ))) := by
  obtain ⟨C,_,h⟩ := strip_mass_error
  have hl := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have ht : Tendsto (fun n : ℕ => C/log (n:ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hl
  rw [Metric.tendsto_nhds] at ht ⊢
  intro ε hε
  filter_upwards [ht ε hε,eventually_ge_atTop 64] with n hne hn
  rw [Real.dist_eq] at hne ⊢
  exact (h n hn).trans_lt ((le_abs_self _).trans_lt (by simpa using hne))

/-- A product of divisors in the strip contains at most three distinct primes.
The estimate is uniform in the factorisation of the target integer. -/
lemma excluded_card (n : ℕ) (hn : 64≤n) :
    ((strip n).filter (fun p => p∣n)).card ≤ 3 := by
  let D := (strip n).filter (fun p => p∣n)
  have hpos : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hlog : 0<log (n:ℝ) := log_pos (by exact_mod_cast (by omega : 1<n))
  have hp (p : ℕ) (hp : p ∈ D) := strip_mem (mem_filter.mp hp).1
  have hsub : D ⊆ n.primeFactors := by
    intro p hp'
    exact Nat.mem_primeFactors.mpr ⟨(hp p hp').1,(mem_filter.mp hp').2,by omega⟩
  have hdvd : (∏ p ∈ D, p) ∣ n :=
    (Finset.prod_dvd_prod_of_subset D n.primeFactors id hsub).trans (Nat.prod_primeFactors_dvd n)
  have hle : (∏ p ∈ D, (p:ℝ)) ≤ n := by
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd (by omega : 0<n) hdvd
  have hprod := log_le_log (Finset.prod_pos (fun p h => by exact_mod_cast (hp p h).1.pos)) hle
  rw [Real.log_prod (fun p h => by exact_mod_cast (hp p h).1.ne_zero)] at hprod
  have hsum : (D.card:ℝ) * ((1/3:ℝ)*log n) ≤ log n := by
    apply le_trans _ hprod
    rw [← nsmul_eq_mul,← sum_const]
    apply sum_le_sum
    intro p h
    rw [← Real.log_rpow hpos]
    exact log_le_log (Real.rpow_pos_of_pos hpos _) (hp p h).2.1.le
  change D.card ≤ 3
  have : (D.card:ℝ) * log n ≤ 3*log n := by linarith
  exact_mod_cast (le_of_mul_le_mul_right this hlog)

lemma lost_mass (n : ℕ) (hn : 64≤n) : 0 ≤ mass (strip n)-mass (good n) ∧
    mass (strip n)-mass (good n) ≤ 3/low n := by
  let D := (strip n).filter fun p => p∣n
  have hd : mass D + mass (good n) = mass (strip n) := by
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hl := (endpoints n hn).1
  have hd0 : 0 ≤ mass D := sum_nonneg fun p _ => by positivity
  have hdb : mass D ≤ 3/low n := by
    calc
      _ ≤ ∑ _p ∈ D, (1/low n) := sum_le_sum fun p hp =>
        one_div_le_one_div_of_le (by linarith) (strip_mem (mem_filter.mp hp).1).2.1.le
      _ = D.card * (1/low n) := by simp
      _ ≤ 3/low n := by
        rw [show (3:ℝ)/low n = 3*(1/low n) by ring]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast excluded_card n hn)
          (one_div_nonneg.mpr (by linarith))
  constructor <;> linarith

lemma low_tendsto : Tendsto low atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : 0<(1/3:ℝ))).comp (tendsto_natCast_atTop_atTop (R:=ℝ))

theorem good_limit : Tendsto (fun n => mass (good n)) atTop (𝓝 (log (3/2:ℝ))) := by
  have ht : Tendsto (fun n : ℕ => 3/low n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop low_tendsto
  have hlost : Tendsto (fun n => mass (strip n)-mass (good n)) atTop (𝓝 0) :=
    squeeze_zero' ((eventually_ge_atTop 64).mono (fun n hn => (lost_mass n hn).1))
      ((eventually_ge_atTop 64).mono (fun n hn => (lost_mass n hn).2)) ht
  simpa only [sub_zero,sub_sub_cancel,Pi.sub_apply] using mass_limit.sub hlost

lemma log_tail_error (n : ℕ) (hn : 64≤n) :
    |log (tail n) + 2*mass (good n)| ≤ (8/low n)*mass (good n) := by
  have hL := (endpoints n hn).1
  have hp (p : ℕ) (h : p ∈ good n) : low n < p := (strip_mem (mem_filter.mp h).1).2.1
  have ht (p : ℕ) (h : p ∈ good n) : 2/(p:ℝ) ≤ 1/2 := by
    have h4 : (4:ℝ)≤p := hL.trans (hp p h).le
    apply (div_le_iff₀ (by linarith : (0:ℝ)<p)).mpr
    linarith
  have hprod (p : ℕ) (h : p ∈ good n) : 1-2/(p:ℝ)≠0 := by linarith [ht p h]
  rw [tail,Real.log_prod hprod,mass,mul_sum,← sum_add_distrib,mul_sum]
  refine (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum ?_)
  intro p h
  have hpp : (0:ℝ)<p := by linarith [hp p h]
  have hsmall := abs_log_one_sub_add_le (div_pos (by norm_num : (0:ℝ)<2) hpp) (ht p h)
  calc
    _ = |log (1-2/(p:ℝ)) + 2/(p:ℝ)| := by rw [mul_one_div]
    _ ≤ _ := hsmall
    _ = (8*(1/(p:ℝ)))*(1/(p:ℝ)) := by ring
    _ ≤ _ := by
      rw [show (8:ℝ)/low n = 8*(1/low n) by ring]
      gcongr
      exact (hp p h).le

lemma tail_pos (n : ℕ) (hn : 64 ≤ n) : 0 < tail n := by
  apply Finset.prod_pos
  intro p hp
  have hbig := (strip_mem (mem_filter.mp hp).1).2.1
  have hL := (endpoints n hn).1
  exact sub_pos.mpr ((div_lt_one (by linarith)).mpr (by linarith))

theorem tail_limit : Tendsto tail atTop (𝓝 (4/9:ℝ)) := by
  have h0 : Tendsto (fun n : ℕ => 8/low n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop low_tendsto
  have hupper : Tendsto (fun n => (8/low n)*mass (good n)) atTop (𝓝 0) := by
    simpa only [zero_mul] using h0.mul good_limit
  have hd : Tendsto (fun n => log (tail n)+2*mass (good n)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds] at hupper ⊢
    intro ε he
    filter_upwards [hupper ε he,eventually_ge_atTop 64] with n h hn
    simp only [Real.dist_eq,sub_zero] at h ⊢
    exact (log_tail_error n hn).trans_lt ((le_abs_self _).trans_lt h)
  have hm : Tendsto (fun n => 2*mass (good n)) atTop (𝓝 (2*log (3/2:ℝ))) :=
    tendsto_const_nhds.mul good_limit
  have hl : Tendsto (fun n => log (tail n)) atTop (𝓝 (-(2*log (3/2:ℝ)))) := by
    simpa only [Pi.sub_apply,add_sub_cancel_right,zero_sub] using hd.sub hm
  have heq : exp (-(2*log (3/2:ℝ))) = 4/9 := by
    rw [exp_neg,show 2*log (3/2:ℝ)=log (3/2:ℝ)+log (3/2:ℝ) by ring, exp_add,
      exp_log (by norm_num : 0 < (3/2:ℝ))]
    norm_num
  rw [← heq]
  apply (Real.continuous_exp.continuousAt.tendsto.comp hl).congr'
  filter_upwards [eventually_ge_atTop 64] with n hn
  exact exp_log (tail_pos n hn)

def factors (n z : ℕ) := (primesUpTo z).filter fun p => ¬p∣n
def vol (n z : ℕ) : ℝ := ((Icc ((n+2)/3) ((2*n)/3)).card:ℝ)*n.totient/n *
  ∏ p ∈ factors n z, (1-2/(p:ℝ))

lemma vol_pos (n z : ℕ) (hn : 64≤n) (he : Even n) : 0 < vol n z := by
  have hI : 0 < (Icc ((n+2)/3) ((2*n)/3)).card :=
    Finset.card_pos.mpr ⟨(n+2)/3, mem_Icc.mpr ⟨le_rfl,by omega⟩⟩
  have hphi := Nat.totient_pos.mpr (by omega : 0<n)
  apply mul_pos (div_pos (mul_pos (by exact_mod_cast hI) (by exact_mod_cast hphi))
    (by exact_mod_cast (by omega : 0<n)))
  apply Finset.prod_pos
  intro p hp
  obtain ⟨hprod,hnd⟩ := mem_filter.mp hp
  have hp2 := (mem_primesUpTo.mp hprod).1.two_le
  have hne : p≠2 := fun hh => hnd (hh ▸ even_iff_two_dvd.mp he)
  have hr : (2:ℝ)<p := by exact_mod_cast (by omega : 2<p)
  exact sub_pos.mpr ((div_lt_one (by linarith)).mpr hr)

lemma volume_ratio (n : ℕ) (hn : 64≤n) (he : Even n) :
    vol n ⌊low n⌋₊ / vol n n.sqrt = (tail n)⁻¹ := by
  have hs : ⌊high n⌋₊ = n.sqrt := by
    change ⌊(n:ℝ)^(1/2:ℝ)⌋₊ = _
    rw [←sqrt_eq_rpow,nat_floor_real_sqrt_eq_nat_sqrt]
  have hsub : factors n ⌊low n⌋₊ ⊆ factors n ⌊high n⌋₊ := by
    intro p hp
    obtain ⟨hh,hnd⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_primesUpTo.mpr ⟨(mem_primesUpTo.mp hh).1,
      (mem_primesUpTo.mp hh).2.trans (Nat.floor_mono (endpoints n hn).2)⟩,hnd⟩
  have hset : factors n ⌊high n⌋₊ \ factors n ⌊low n⌋₊ = good n := by
    ext p
    simp only [factors,good,strip,Finset.mem_sdiff,mem_filter]
    exact ⟨fun ⟨⟨hh,hnd⟩,hl⟩ => ⟨⟨hh,fun h => hl ⟨h,hnd⟩⟩,hnd⟩,
      fun ⟨⟨hh,hl⟩,hnd⟩ => ⟨⟨hh,hnd⟩,fun h => hl h.1⟩⟩
  have hfac : vol n ⌊high n⌋₊ = tail n*vol n ⌊low n⌋₊ := by
    have hprod := Finset.prod_sdiff (f:=fun p : ℕ => 1-2/(p:ℝ)) hsub
    rw [hset] at hprod
    unfold vol tail
    rw [←hprod]
    ring
  rw [← hs,hfac]
  field_simp [(vol_pos n ⌊low n⌋₊ hn he).ne',(tail_pos n hn).ne']

theorem sharp_ratio (ε : ℝ) (hε : 0<ε) : ∃ N : ℕ, 64≤N ∧ ∀ n : ℕ, N≤n →
    Even n → |vol n ⌊low n⌋₊/vol n n.sqrt-9/4| ≤ ε := by
  have hi : Tendsto (fun n => (tail n)⁻¹) atTop (𝓝 (9/4:ℝ)) := by
    convert tail_limit.inv₀ (by norm_num : (4/9:ℝ)≠0) using 1 <;> norm_num
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp hi) ε hε)
  refine ⟨max 64 N,le_max_left ..,?_⟩
  intro n hn he
  rw [volume_ratio n ((le_max_left ..).trans hn) he]
  exact (hN n ((le_max_right ..).trans hn)).le

end
end GoldbachLateDensity

theorem Conjectures.Goldbach.FareyCubeSqrtDensityRatio :
    let I := fun n : ℕ => Finset.Icc ((n+2)/3) ((2*n)/3); let P := fun z : ℕ => (Finset.Icc 2 z).filter Nat.Prime; let V := fun n z : ℕ => ((I n).card:ℝ)*(n.totient:ℝ)/n * ∏ p ∈ (P z).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ)); let Z₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 64 ≤ N ∧ ∀ n : ℕ, N ≤ n → Even n → |V n (Z₁ n) / V n n.sqrt - 9/4| ≤ ε := by
  have hP (z : ℕ) : (Finset.Icc 2 z).filter Nat.Prime =
      ErdosStraus.PrimeEstimates.Mertens.primesUpTo z := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_Icc,ErdosStraus.PrimeEstimates.Mertens.mem_primesUpTo]
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨h.1.two_le,h.2⟩,h.1⟩⟩
  dsimp only
  simp only [hP]
  exact GoldbachLateDensity.sharp_ratio
