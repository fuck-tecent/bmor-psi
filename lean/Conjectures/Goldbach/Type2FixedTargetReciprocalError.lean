import Mathlib

/-!
# Transition band (2,2) for the Goldbach deep minor arcs

The quantitative reduction is `GoldbachTransitionSquare.full_to_fixed_target_discrepancy`.
For distinct large primes p and q with |p-q| above the cutoff, `reciprocalTotal`
uses the unique possible short cofactors of a representation a*p + b*q = n.
`wideFar` integrates the same prime pairs on the prescribed wide arcs.
The open estimate is that their difference is o(n) along all even n.
-/

open Finset MeasureTheory

namespace GoldbachTransitionSquare
noncomputable section

/- The divisor hyperbola identity and bound for the truncated Möbius coefficient
   below are from goldbach-proofs #2492 (27164850faea517a013e2c44c55f834e86db01be),
   adapted there from xuanyou-li's #2489, Apache-2.0. -/
theorem finite_divisor_hyperbola {R : Type*} [AddCommMonoid R] (limit : ℕ)
    (term : ℕ → ℕ → R) :
    (∑ m ∈ Icc 1 limit, ∑ a ∈ m.divisors, term a (m / a)) =
      ∑ a ∈ Icc 1 limit, ∑ b ∈ Icc 1 (limit / a), term a b := by
  classical
  have divisorFilter (m : ℕ) (membership : m ∈ Icc 1 limit) :
      m.divisors = (Icc 1 limit).filter (fun a => a ∣ m) := by
    obtain ⟨positive, bounded⟩ := mem_Icc.mp membership
    ext a
    rw [mem_filter, mem_Icc]
    constructor
    · intro divisor
      have divides := Nat.dvd_of_mem_divisors divisor
      exact ⟨⟨Nat.pos_of_mem_divisors divisor, (Nat.le_of_dvd positive divides).trans bounded⟩,
        divides⟩
    · rintro ⟨_, divides⟩
      exact Nat.mem_divisors.mpr ⟨divides, (show 0 < m from positive).ne'⟩
  calc
    _ = ∑ m ∈ Icc 1 limit, ∑ a ∈ Icc 1 limit, if a ∣ m then term a (m / a) else 0 := by
      refine sum_congr rfl fun m membership => ?_
      rw [divisorFilter m membership, sum_filter]
    _ = _ := by
      rw [sum_comm]
      refine sum_congr rfl fun a membership => ?_
      have aPositive : 0 < a := (mem_Icc.mp membership).1
      let multiply : ℕ ↪ ℕ := ⟨fun b => a * b,
        fun _ _ equal => mul_left_cancel₀ aPositive.ne' equal⟩
      have multiples : (Icc 1 limit).filter (fun m => a ∣ m) =
          (Icc 1 (limit / a)).map multiply := by
        ext m
        simp only [mem_filter, mem_map]
        constructor
        · rintro ⟨inInterval, divides⟩
          obtain ⟨b, rfl⟩ := divides
          obtain ⟨mPositive, mBounded⟩ := mem_Icc.mp inInterval
          have bPositive : 0 < b := by
            by_contra! bZero
            have bEqualsZero : b = 0 := Nat.eq_zero_of_le_zero bZero
            simp [bEqualsZero] at mPositive
          have bBounded : b ≤ limit / a :=
            (Nat.le_div_iff_mul_le aPositive).mpr (by simpa only [mul_comm] using mBounded)
          exact ⟨b, mem_Icc.mpr ⟨bPositive, bBounded⟩, rfl⟩
        · rintro ⟨b, bInInterval, rfl⟩
          obtain ⟨bPositive, bBounded⟩ := mem_Icc.mp bInInterval
          change a * b ∈ Icc 1 limit ∧ a ∣ a * b
          have mBounded : a * b ≤ limit := by
            simpa only [mul_comm] using (Nat.le_div_iff_mul_le aPositive).mp bBounded
          exact ⟨mem_Icc.mpr ⟨Nat.mul_pos aPositive bPositive, mBounded⟩, dvd_mul_right a b⟩
      rw [← sum_filter, multiples, sum_map]
      refine sum_congr rfl fun b _ => ?_
      change term a ((a * b) / a) = term a b
      rw [Nat.mul_div_cancel_left _ aPositive]

def lowMoebiusWeight (U a : ℕ) : ℝ := ∑ d ∈ a.divisors.filter (fun d => U < d), ((ArithmeticFunction.moebius d : ℤ) : ℝ)

theorem abs_lowMoebiusWeight_le (U a : ℕ) : |lowMoebiusWeight U a| ≤ (a.divisors.card : ℝ) := by
  have bound : ‖lowMoebiusWeight U a‖ ≤ (a.divisors.card : ℝ) := by
    unfold lowMoebiusWeight
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ d ∈ a.divisors.filter (fun d => U < d), (1 : ℝ) := by
        refine sum_le_sum fun d _ => ?_
        rw [Real.norm_eq_abs]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
      _ ≤ ∑ d ∈ a.divisors, (1 : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => zero_le_one)
      _ = _ := by simp
  simpa only [Real.norm_eq_abs] using bound


def properWeight (b : ℕ) : ℝ :=
  if b.Prime then 0 else ArithmeticFunction.vonMangoldt b

theorem properWeight_nonneg (b : ℕ) : 0 ≤ properWeight b := by
  unfold properWeight
  split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]

theorem properWeight_sum_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ b ∈ Icc 1 n, properWeight b ≤ 2 * Real.sqrt n * Real.log n := by
  have eqn : ∑ b ∈ Icc 0 n, properWeight b = Chebyshev.psi n - Chebyshev.theta n := by
    rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast,
      sum_filter, ← sum_sub_distrib]
    refine sum_congr rfl fun b _ => ?_
    by_cases h : b.Prime
    · simp [properWeight, h, ArithmeticFunction.vonMangoldt_apply_prime h]
    · simp [properWeight, h]
  refine le_trans (sum_le_sum_of_subset_of_nonneg (t := Icc 0 n)
    (fun b hb => mem_Icc.mpr ⟨Nat.zero_le b, (mem_Icc.mp hb).2⟩)
    (fun b _ _ => properWeight_nonneg b)) ?_
  rw [eqn]
  exact Chebyshev.psi_sub_theta_le (by exact_mod_cast hn)

/-- In the transition band, the total weight of the nonprime cofactors
    can be bounded without any information about primes in progressions. -/
theorem properWeight_hyperbola_le (n B : ℕ) (hn : 1 ≤ n) :
    (∑ m ∈ Icc 1 n, ∑ a ∈ m.divisors,
      if a ≤ B then properWeight (m / a) else 0) ≤
      (B : ℝ) * (2 * Real.sqrt n * Real.log n) := by
  rw [finite_divisor_hyperbola n (fun a b => if a ≤ B then properWeight b else 0)]
  let cap := 2 * Real.sqrt n * Real.log n
  have hcap : 0 ≤ cap := by
    dsimp [cap]
    have : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    positivity
  calc
    _ ≤ ∑ a ∈ Icc 1 n, if a ≤ B then cap else 0 := by
      refine sum_le_sum fun a _ => ?_
      by_cases h : a ≤ B
      · simp only [ite_eq_left h]
        refine le_trans (sum_le_sum_of_subset_of_nonneg (t := Icc 1 n)
          (fun b hb => mem_Icc.mpr ⟨(mem_Icc.mp hb).1,
          (mem_Icc.mp hb).2.trans (Nat.div_le_self n a)⟩)
          (fun b _ _ => properWeight_nonneg b)) (properWeight_sum_le n hn)
      · simp [h]
    _ ≤ ∑ a ∈ Icc 1 B, cap := by
      rw [← sum_filter]
      exact sum_le_sum_of_subset_of_nonneg
        (fun a ha => mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp ha).1).1, (mem_filter.mp ha).2⟩)
        (fun _ _ _ => hcap)
    _ = _ := by simp [cap]

def band (U L B : ℕ) (weight : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ a ∈ m.divisors.filter (fun a => L < a ∧ a ≤ B ∧ U < m / a),
    lowMoebiusWeight U a * weight (m / a)

theorem band_add (U L B m : ℕ) (v w : ℕ → ℝ) :
    band U L B (fun b => v b + w b) m = band U L B v m + band U L B w m := by
  simp only [band, mul_add, sum_add_distrib]

def primeWeight (b : ℕ) : ℝ := if b.Prime then Real.log b else 0

theorem band_prime_split (U L B m : ℕ) :
    band U L B ArithmeticFunction.vonMangoldt m =
    band U L B primeWeight m + band U L B properWeight m := by
  rw [← band_add]
  congr 1
  funext b
  by_cases hb : b.Prime <;> simp [primeWeight, properWeight, hb, ArithmeticFunction.vonMangoldt_apply_prime]

theorem band_proper_l1 (n U L B : ℕ) (hn : 1 ≤ n) {T : ℝ} (hT : 0 ≤ T)
    (hdiv : ∀ a ≤ n, (a.divisors.card : ℝ) ≤ T) :
    ∑ m ∈ Icc 1 n, |band U L B properWeight m| ≤
    T * ((B : ℝ) * (2 * Real.sqrt n * Real.log n)) := by
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (properWeight_hyperbola_le n B hn) hT)
  rw [mul_sum]
  refine sum_le_sum fun m hm => ?_
  rw [← Real.norm_eq_abs, band]
  refine (norm_sum_le _ _).trans ?_
  rw [sum_filter, mul_sum]
  refine sum_le_sum fun a ha => ?_
  have h := (abs_lowMoebiusWeight_le U a).trans
    (hdiv a ((Nat.le_of_dvd (mem_Icc.mp hm).1 (Nat.dvd_of_mem_divisors ha)).trans
      (mem_Icc.mp hm).2))
  by_cases hc : L < a ∧ a ≤ B ∧ U < m / a
  · simp only [ite_eq_left hc, ite_eq_left hc.2.1, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (properWeight_nonneg _)]
    exact mul_le_mul_of_nonneg_right h (properWeight_nonneg _)
  · simp only [ite_eq_right hc]
    split_ifs
    · exact mul_nonneg hT (properWeight_nonneg _)
    · simp

theorem band_uniform_bound (n U L B m : ℕ) (hm : m ≤ n) (hn : 1 ≤ n)
    {T : ℝ} (hdiv : ∀ a ≤ n, (a.divisors.card : ℝ) ≤ T)
    {w : ℕ → ℝ} (hw : ∀ b, |w b| ≤ ArithmeticFunction.vonMangoldt b) :
    |band U L B w m| ≤ T ^ 2 * Real.log n := by
  have hT := (Nat.cast_nonneg _).trans (hdiv m hm)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  rw [← Real.norm_eq_abs, band]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _a ∈ m.divisors.filter (fun a => L < a ∧ a ≤ B ∧ U < m / a),
          T * Real.log n := by
      refine sum_le_sum fun a ha => ?_
      have ha' := (mem_filter.mp ha).1
      have hm' := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisors ha')
      have hle := Nat.le_of_dvd hm' (Nat.dvd_of_mem_divisors ha')
      have hquot := Nat.div_pos hle (Nat.pos_of_mem_divisors ha')
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul ((abs_lowMoebiusWeight_le U a).trans (hdiv a (hle.trans hm)))
        (((hw _).trans ArithmeticFunction.vonMangoldt_le_log).trans (Real.log_le_log
          (by exact_mod_cast hquot) (by exact_mod_cast (Nat.div_le_self m a).trans hm)))
        (abs_nonneg _) hT
    _ ≤ ∑ _a ∈ m.divisors, T * Real.log n :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => mul_nonneg hT hlog)
    _ ≤ _ := by
      simp only [sum_const, nsmul_eq_mul]
      calc
        _ ≤ T * (T * Real.log n) := mul_le_mul_of_nonneg_right (hdiv m hm) (mul_nonneg hT hlog)
        _ = _ := by ring

theorem abs_properWeight_le (b : ℕ) :
    |properWeight b| ≤ ArithmeticFunction.vonMangoldt b := by
  rw [abs_of_nonneg (properWeight_nonneg b)]
  unfold properWeight
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact le_rfl

theorem band_proper_l2 (n U L B : ℕ) (hn : 1 ≤ n) {T : ℝ} (hT : 0 ≤ T)
    (hdiv : ∀ a ≤ n, (a.divisors.card : ℝ) ≤ T) :
    ∑ m ∈ range (n+1), (band U L B properWeight m)^2 ≤
      (T^2 * Real.log n) * (T * ((B:ℝ) * (2 * Real.sqrt n * Real.log n))) := by
  have parts : range (n+1) = insert 0 (Icc 1 n) := by
    ext m; simp only [mem_range, mem_insert, mem_Icc]; omega
  rw [parts, sum_insert (by simp)]
  simp only [band, Nat.divisors_zero, filter_empty, sum_empty, zero_pow (by decide : 2 ≠ 0),
    zero_add]
  change (∑ m ∈ Icc 1 n, (band U L B properWeight m)^2) ≤ _
  have hl := Real.log_nonneg (show (1:ℝ) ≤ n by exact_mod_cast hn)
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (band_proper_l1 n U L B hn hT hdiv)
    (mul_nonneg (sq_nonneg T) hl))
  rw [mul_sum]
  refine sum_le_sum fun m hm => ?_
  rw [← sq_abs, sq]
  exact mul_le_mul_of_nonneg_right
    (band_uniform_bound n U L B m (mem_Icc.mp hm).2 hn hdiv abs_properWeight_le) (abs_nonneg _)

theorem band_l2 (n U L B : ℕ) (hn : 1 ≤ n) {T : ℝ}
    (hdiv : ∀ a ≤ n, (a.divisors.card : ℝ) ≤ T)
    {w : ℕ → ℝ} (hw : ∀ b, |w b| ≤ ArithmeticFunction.vonMangoldt b) :
    ∑ m ∈ range (n+1), (band U L B w m)^2 ≤ (n+1 : ℕ) * (T^2 * Real.log n)^2 := by
  calc
    _ ≤ ∑ _m ∈ range (n+1), (T^2 * Real.log n)^2 := by
      refine sum_le_sum fun m hm => ?_
      rw [← sq_abs (band U L B w m)]
      exact pow_le_pow_left₀ (abs_nonneg _) (band_uniform_bound n U L B m
        (Nat.le_of_lt_succ (mem_range.mp hm)) hn hdiv hw) 2
    _ = _ := by simp

def smallPrimeWeight (n b : ℕ) : ℝ := if b ≤ n.sqrt then primeWeight b else 0
def largePrimeWeight (n b : ℕ) : ℝ := if n.sqrt < b then primeWeight b else 0

theorem primeWeight_split (n b : ℕ) :
    primeWeight b = smallPrimeWeight n b + largePrimeWeight n b := by
  by_cases h : b ≤ n.sqrt <;> simp [smallPrimeWeight, largePrimeWeight, h, lt_iff_not_ge]

theorem abs_primeWeight_le (b : ℕ) :
    |primeWeight b| ≤ ArithmeticFunction.vonMangoldt b := by
  by_cases hb : b.Prime
  · simp [primeWeight, hb, ArithmeticFunction.vonMangoldt_apply_prime hb, abs_of_nonneg
      (Real.log_nonneg (show (1:ℝ) ≤ b by exact_mod_cast hb.one_le))]
  · simpa [primeWeight, hb] using (ArithmeticFunction.vonMangoldt_nonneg (n := b))

theorem abs_smallPrimeWeight_le (n b : ℕ) :
    |smallPrimeWeight n b| ≤ ArithmeticFunction.vonMangoldt b := by
  unfold smallPrimeWeight
  split_ifs
  · exact abs_primeWeight_le b
  · simpa using (ArithmeticFunction.vonMangoldt_nonneg (n := b))

theorem band_smallPrime_eq_zero (n U L B m : ℕ) (hm : B * n.sqrt < m) :
    band U L B (smallPrimeWeight n) m = 0 := by
  apply sum_eq_zero
  intro a ha
  obtain ⟨hdiv, _, hab, _⟩ := mem_filter.mp ha
  have hlarge : ¬ m / a ≤ n.sqrt := by
    intro h
    have hprod := Nat.mul_le_mul hab h
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hdiv)] at hprod
    omega
  simp [smallPrimeWeight, hlarge]

theorem band_smallPrime_l2 (n U L B : ℕ) (hn : 1 ≤ n) {T : ℝ}
    (hdiv : ∀ a ≤ n, (a.divisors.card : ℝ) ≤ T) :
    ∑ m ∈ range (n+1), (band U L B (smallPrimeWeight n) m)^2 ≤
      ((B * n.sqrt + 1 : ℕ) : ℝ) * (T^2 * Real.log n)^2 := by
  let A := (T^2 * Real.log n)^2
  calc
    _ ≤ ∑ m ∈ range (n+1), if m ≤ B * n.sqrt then A else 0 := by
      refine sum_le_sum fun m hm => ?_
      by_cases h : m ≤ B * n.sqrt
      · simp only [ite_eq_left h, A]
        rw [← sq_abs (band U L B (smallPrimeWeight n) m)]
        exact pow_le_pow_left₀ (abs_nonneg _) (band_uniform_bound n U L B m
          (Nat.le_of_lt_succ (mem_range.mp hm)) hn hdiv (abs_smallPrimeWeight_le n)) 2
      · simp [h, band_smallPrime_eq_zero n U L B m (Nat.lt_of_not_ge h)]
    _ ≤ ∑ _m ∈ range (B * n.sqrt + 1), A := by
      rw [← sum_filter]
      exact sum_le_sum_of_subset_of_nonneg
        (fun m hm => mem_range.mpr (by have := (mem_filter.mp hm).2; omega))
        (fun _ _ _ => sq_nonneg _)
    _ = _ := by simp [A]

/-- The remaining prime cofactor identifies its short divisor uniquely. -/
theorem unique_large_prime_cofactor {m n a c : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (ha : a ∣ m) (hc : c ∣ m) (hp : (m/a).Prime) (hq : (m/c).Prime)
    (hpl : n.sqrt < m/a) (hql : n.sqrt < m/c) : a = c := by
  have hsame : m/a = m/c := by
    by_contra h
    have hprod := Nat.Prime.dvd_mul_of_dvd_ne h hp hq
      (Nat.div_dvd_of_dvd ha) (Nat.div_dvd_of_dvd hc)
    have hlow := Nat.mul_le_mul hpl hql
    have hhigh := (Nat.le_of_dvd hm hprod).trans hmn
    have hs := Nat.lt_succ_sqrt n
    nlinarith
  have e1 := Nat.mul_div_cancel' ha
  have e2 := Nat.mul_div_cancel' hc
  rw [← hsame] at e2
  exact Nat.eq_of_mul_eq_mul_right hp.pos (e1.trans e2.symm)

end
end GoldbachTransitionSquare

/- Continuous Parseval from Clrs17, goldbach-proofs #138, 5ab2bcbb94ec2a8224686cc2cf35f1736f882a64 (Apache-2.0). -/

open scoped BigOperators ComplexConjugate

private noncomputable def parsevalPhase (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

namespace GoldbachTransitionFourier

theorem continuous_parseval :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); ∀ n w, intervalIntegral (fun t => ‖S n w t‖^2) (0:ℝ) 1 MeasureTheory.volume = Finset.sum (Finset.range (n+1)) (fun k => (w k)^2) := by
  dsimp only
  intro n w
  let T := Finset.range (n + 1)
  let S : ℝ → ℂ := fun t => ∑ k ∈ T, (w k : ℂ) * parsevalPhase ((k : ℝ) * t)
  let z : ℝ → ℂ := fun t => ∑ k ∈ T, ∑ j ∈ T,
    ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t)
  change intervalIntegral (fun t => ‖S t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume = _
  have hphase_mul : ∀ x y : ℝ, parsevalPhase (x + y) = parsevalPhase x * parsevalPhase y := by
    intro x y
    unfold parsevalPhase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hphase_cont : Continuous parsevalPhase := by
    unfold parsevalPhase
    fun_prop
  have hphase_exp : ∀ m : ℤ, Complex.exp (2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I) = 1 := by
    intro m
    have h : 2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I =
        (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
  have hphase_one : ∀ m : ℤ, parsevalPhase (m : ℝ) = 1 := by
    intro m
    unfold parsevalPhase
    have h : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) =
        2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, hphase_exp m]
  have hphase_conj : ∀ x : ℝ, conj (parsevalPhase x) = parsevalPhase (-x) := by
    intro x
    unfold parsevalPhase
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have horth : ∀ m : ℤ, intervalIntegral (fun t : ℝ => parsevalPhase ((m : ℝ) * t))
      (0 : ℝ) 1 MeasureTheory.volume = if m = 0 then 1 else 0 := by
    intro m
    have hrewrite : intervalIntegral (fun t : ℝ => parsevalPhase ((m : ℝ) * t))
        (0 : ℝ) 1 MeasureTheory.volume =
        ∫ t in (0 : ℝ)..1, Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) * (t : ℂ)) := by
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      unfold parsevalPhase
      congr 1
      push_cast
      ring
    rw [hrewrite]
    by_cases hm : m = 0
    · subst hm
      simp
    · have hmr : (m : ℝ) ≠ 0 := by
        intro hzero
        exact hm (by exact_mod_cast hzero)
      have h1 : (2 * Real.pi * (m : ℝ)) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hmr
      have hc : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) ≠ 0 := by
        have h2 : ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) ≠ 0 := by
          simpa [Complex.ofReal_eq_zero] using h1
        exact mul_ne_zero h2 Complex.I_ne_zero
      have hval : Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ)) * Complex.I) = 1 := by
        have hone := hphase_one m
        simpa only [parsevalPhase] using hone
      rw [integral_exp_mul_complex hc]
      simp [hphase_exp m, hm]
  have hint_single : ∀ (c : ℂ) (a : ℝ),
      IntervalIntegrable (fun t : ℝ => c * parsevalPhase (a * t)) MeasureTheory.volume (0 : ℝ) 1 := by
    intro c a
    exact (continuous_const.mul (hphase_cont.comp (by fun_prop))).intervalIntegrable (0 : ℝ) 1
  have hpoint : ∀ t : ℝ, (Complex.normSq (S t) : ℂ) = z t := by
    intro t
    rw [Complex.normSq_eq_conj_mul_self]
    dsimp only [S, z]
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    simp only [map_mul, Complex.conj_ofReal, hphase_conj]
    have hmul : parsevalPhase (-((k : ℝ) * t)) * parsevalPhase ((j : ℝ) * t) =
        parsevalPhase (((j : ℝ) - (k : ℝ)) * t) := by
      rw [← hphase_mul]
      congr 1
      ring
    calc
      ((w k : ℂ) * parsevalPhase (-((k : ℝ) * t))) *
          ((w j : ℂ) * parsevalPhase ((j : ℝ) * t)) =
          ((w k : ℂ) * (w j : ℂ)) *
            (parsevalPhase (-((k : ℝ) * t)) * parsevalPhase ((j : ℝ) * t)) := by ring
      _ = ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t) := by
        rw [hmul]
  have hint_z : IntervalIntegrable z MeasureTheory.volume (0 : ℝ) 1 := by
    dsimp only [z]
    exact (continuous_finsetSum _ (fun k _ => continuous_finsetSum _
      (fun j _ => continuous_const.mul (hphase_cont.comp (by fun_prop))))).intervalIntegrable (0 : ℝ) 1
  have hmain : intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume =
      ((∑ k ∈ T, (w k) ^ 2 : ℝ) : ℂ) := by
    dsimp only [z]
    have houter (k : ℕ) (hk : k ∈ T) : IntervalIntegrable (fun t : ℝ => ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
        MeasureTheory.volume (0 : ℝ) 1 := by
      exact (continuous_finsetSum _ (fun j _ => continuous_const.mul
        (hphase_cont.comp (by fun_prop)))).intervalIntegrable (0 : ℝ) 1
    rw [intervalIntegral.integral_finsetSum houter]
    have hstep : ∀ k ∈ T, intervalIntegral (fun t : ℝ => ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
        (0 : ℝ) 1 MeasureTheory.volume = ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * (if ((j : ℤ) - (k : ℤ)) = 0 then 1 else 0) := by
      intro k hk
      rw [intervalIntegral.integral_finsetSum (fun j _ =>
        hint_single ((w k : ℂ) * (w j : ℂ)) (((j : ℝ) - (k : ℝ))))]
      apply Finset.sum_congr rfl
      intro j hj
      rw [intervalIntegral.integral_const_mul]
      congr 1
      have hm : ((j : ℝ) - (k : ℝ)) = (((j : ℤ) - (k : ℤ) : ℤ) : ℝ) := by
        push_cast
        ring
      simp_rw [hm]
      rw [horth]
    calc
      (∑ k ∈ T, intervalIntegral (fun t : ℝ => ∑ j ∈ T,
          ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
          (0 : ℝ) 1 MeasureTheory.volume) =
          ∑ k ∈ T, ∑ j ∈ T, ((w k : ℂ) * (w j : ℂ)) *
            (if ((j : ℤ) - (k : ℤ)) = 0 then 1 else 0) := Finset.sum_congr rfl hstep
      _ = ((∑ k ∈ T, (w k) ^ 2 : ℝ) : ℂ) := by
        push_cast
        simp only [sub_eq_zero, Int.ofNat_inj]
        apply Finset.sum_congr rfl
        intro k hk
        simp [hk, pow_two]
  have hre : intervalIntegral (fun t => (z t).re) (0 : ℝ) 1 MeasureTheory.volume =
      (intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume).re := by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc,
      intervalIntegral.intervalIntegral_eq_integral_uIoc]
    simp only [show (0 : ℝ) ≤ 1 by norm_num, ite_true, one_smul]
    exact integral_re hint_z.def'
  calc
    intervalIntegral (fun t => ‖S t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume =
        intervalIntegral (fun t => (z t).re) (0 : ℝ) 1 MeasureTheory.volume := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hp := congrArg Complex.re (hpoint t)
      simpa only [Complex.ofReal_re, Complex.normSq_eq_norm_sq] using hp
    _ = (intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume).re := hre
    _ = ∑ k ∈ T, (w k) ^ 2 := by rw [hmain]; exact Complex.ofReal_re _

end GoldbachTransitionFourier

namespace GoldbachTransitionSquare
noncomputable section

def phase (t : ℝ) : ℂ := Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
def fourierSum (n : ℕ) (w : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n+1), (w k : ℂ) * phase (k*t)
def pairIntegral (s : Set ℝ) (n : ℕ) (u v : ℕ → ℝ) : ℂ :=
  ∫ t in (0:ℝ)..1, s.indicator (fun x => fourierSum n u x * fourierSum n v x *
    phase (-(n:ℝ)*x)) t

theorem norm_phase (t : ℝ) : ‖phase t‖ = 1 := by simp [phase, Complex.norm_exp]

theorem continuous_fourierSum (n : ℕ) (w : ℕ → ℝ) : Continuous (fourierSum n w) := by
  unfold fourierSum phase
  fun_prop

theorem fourierSum_add (n : ℕ) (u v : ℕ → ℝ) (t : ℝ) :
    fourierSum n (fun k => u k + v k) t = fourierSum n u t + fourierSum n v t := by
  simp [fourierSum, add_mul, sum_add_distrib]

theorem fourierSum_sub (n : ℕ) (u v : ℕ → ℝ) (t : ℝ) :
    fourierSum n (fun k => u k - v k) t = fourierSum n u t - fourierSum n v t := by
  simp [fourierSum, sub_mul, sum_sub_distrib]

theorem integrable_pair (s : Set ℝ) (hs : MeasurableSet s) (n : ℕ) (u v : ℕ → ℝ) :
    IntervalIntegrable (s.indicator (fun x => fourierSum n u x * fourierSum n v x *
      phase (-(n:ℝ)*x))) volume 0 1 := by
  have hf : Continuous (fun x => fourierSum n u x * fourierSum n v x * phase (-(n:ℝ)*x)) := by
    apply Continuous.mul ((continuous_fourierSum n u).mul (continuous_fourierSum n v))
    unfold phase; fun_prop
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
    (hf.intervalIntegrable 0 1)).indicator hs

theorem pairIntegral_sub_squares (s : Set ℝ) (hs : MeasurableSet s) (n : ℕ)
    (u v : ℕ → ℝ) :
    pairIntegral s n u u - pairIntegral s n v v =
      pairIntegral s n (fun k => u k - v k) (fun k => u k + v k) := by
  unfold pairIntegral
  rw [← intervalIntegral.integral_sub (integrable_pair s hs n u u) (integrable_pair s hs n v v)]
  apply intervalIntegral.integral_congr
  intro x _
  by_cases hx : x ∈ s
  · simp only [Set.indicator_of_mem hx, fourierSum_sub, fourierSum_add]
    ring
  · simp [Set.indicator_of_notMem hx]

end
end GoldbachTransitionSquare

open MeasureTheory
/- Scaled Young inequality from goldbach-proofs #2492, cited above. -/
namespace GoldbachTransitionFourier

theorem scaled_young {s x y : ℝ} (sPositive : 0 < s) :
    x * y ≤ (1 / 2) * (s * x ^ 2 + s⁻¹ * y ^ 2) := by
  have multiplied : (2 * x * y - s * x ^ 2) * s ≤ y ^ 2 := by
    nlinarith only [sq_nonneg (s * x - y)]
  have divided := (le_div_iff₀ sPositive).mpr multiplied
  rw [inv_mul_eq_div]
  linarith only [divided]

theorem norm_indicator_product_le {f g : ℝ → ℂ} {s : Set ℝ} {scale : ℝ}
    (scalePositive : 0 < scale) (sMeasurable : MeasurableSet s) (fMeasurable : Measurable f)
    (gMeasurable : Measurable g)
    (fSquareIntegrable : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume 0 1)
    (gSquareIntegrable : IntervalIntegrable (fun t => ‖g t‖ ^ 2) volume 0 1) :
    ‖∫ t in (0 : ℝ)..1, s.indicator (fun x => f x * g x) t‖ ≤
      (1 / 2) * (scale * (∫ t in (0 : ℝ)..1, ‖f t‖ ^ 2) +
        scale⁻¹ * (∫ t in (0 : ℝ)..1, ‖g t‖ ^ 2)) := by
  let product := s.indicator (fun t => f t * g t)
  let bound (t : ℝ) := (1 / 2) * (scale * ‖f t‖ ^ 2 + scale⁻¹ * ‖g t‖ ^ 2)
  have productMeasurable : Measurable product := (fMeasurable.mul gMeasurable).indicator sMeasurable
  have firstIntegrable : IntervalIntegrable (fun t => scale * ‖f t‖ ^ 2) volume 0 1 :=
    fSquareIntegrable.const_mul scale
  have secondIntegrable : IntervalIntegrable (fun t => scale⁻¹ * ‖g t‖ ^ 2) volume 0 1 :=
    gSquareIntegrable.const_mul scale⁻¹
  have sumIntegrable : IntervalIntegrable (fun t => scale * ‖f t‖ ^ 2 + scale⁻¹ * ‖g t‖ ^ 2) volume 0 1 :=
    firstIntegrable.add secondIntegrable
  have boundIntegrable : IntervalIntegrable bound volume 0 1 := sumIntegrable.const_mul (1 / 2)
  have pointwise (t : ℝ) : ‖product t‖ ≤ bound t := by
    unfold product bound
    by_cases member : t ∈ s
    · rw [Set.indicator_of_mem member, norm_mul]
      exact scaled_young scalePositive
    · rw [Set.indicator_of_notMem member, norm_zero]
      positivity
  have productIntegrable : IntervalIntegrable product volume 0 1 := boundIntegrable.mono_fun'
    productMeasurable.aestronglyMeasurable (Filter.Eventually.of_forall pointwise)
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, ‖product t‖ := intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, bound t := intervalIntegral.integral_mono_on zero_le_one productIntegrable.norm
      boundIntegrable (fun t _ => pointwise t)
    _ = _ := by
      unfold bound
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add firstIntegrable secondIntegrable,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]


end GoldbachTransitionFourier
namespace GoldbachTransitionSquare
noncomputable section
open MeasureTheory GoldbachTransitionFourier

theorem pairIntegral_le_energy (s : Set ℝ) (hs : MeasurableSet s) (n : ℕ)
    (u v : ℕ → ℝ) {scale : ℝ} (hscale : 0 < scale) :
    ‖pairIntegral s n u v‖ ≤ (1/2) * (scale * (∑ k ∈ range (n+1), (u k)^2)
      + scale⁻¹ * (∑ k ∈ range (n+1), (v k)^2)) := by
  let f := fourierSum n u
  let g := fun x : ℝ => fourierSum n v x * phase (-(n:ℝ)*x)
  have hf : Continuous f := continuous_fourierSum n u
  have hg : Continuous g := by
    apply Continuous.mul (continuous_fourierSum n v)
    unfold phase; fun_prop
  have normg (x : ℝ) : ‖g x‖ = ‖fourierSum n v x‖ := by simp [g, norm_mul, norm_phase]
  have eqn : pairIntegral s n u v = ∫ t in (0:ℝ)..1, s.indicator (fun x => f x * g x) t := by
    simp only [pairIntegral, f, g, mul_assoc]
  rw [eqn]
  apply (norm_indicator_product_le hscale hs hf.measurable hg.measurable
    ((hf.norm.pow 2).intervalIntegrable 0 1) ((hg.norm.pow 2).intervalIntegrable 0 1)).trans_eq
  simp only [normg]
  have hu : (∫ t in (0:ℝ)..1, ‖f t‖^2) = ∑ k ∈ range (n+1), (u k)^2 := continuous_parseval n u
  have hv : (∫ t in (0:ℝ)..1, ‖fourierSum n v t‖^2) = ∑ k ∈ range (n+1), (v k)^2 :=
    continuous_parseval n v
  rw [hu, hv]

end
end GoldbachTransitionSquare

namespace GoldbachTransitionSquare
noncomputable section

theorem abs_largePrimeWeight_le (n b : ℕ) :
    |largePrimeWeight n b| ≤ ArithmeticFunction.vonMangoldt b := by
  unfold largePrimeWeight
  split_ifs
  · exact abs_primeWeight_le b
  · simp

def full (n U L B : ℕ) := band U L B ArithmeticFunction.vonMangoldt
def core (n U L B : ℕ) := band U L B (largePrimeWeight n)

theorem full_sub_core (n U L B m : ℕ) :
    full n U L B m - core n U L B m =
    band U L B properWeight m + band U L B (smallPrimeWeight n) m := by
  have hp : primeWeight = fun b => smallPrimeWeight n b + largePrimeWeight n b :=
    funext (primeWeight_split n)
  rw [full, core, band_prime_split, hp, band_add]
  ring

theorem full_sub_core_energy (n U L B : ℕ) (hn : 1 ≤ n) {T : ℝ} (hT : 0 ≤ T)
    (hdiv : ∀ a ≤ n, (a.divisors.card : ℝ) ≤ T) :
    ∑ m ∈ range (n+1), (full n U L B m - core n U L B m)^2 ≤
      2 * ((T^2 * Real.log n) * (T * ((B:ℝ) * (2 * Real.sqrt n * Real.log n))) +
      ((B * n.sqrt + 1 : ℕ) : ℝ) * (T^2 * Real.log n)^2) := by
  let A := band U L B properWeight
  let C := band U L B (smallPrimeWeight n)
  calc
    _ ≤ ∑ m ∈ range (n+1), 2 * ((A m)^2 + (C m)^2) := by
      refine sum_le_sum fun m _ => ?_
      rw [full_sub_core]
      change (A m + C m)^2 ≤ _
      nlinarith only [sq_nonneg (A m - C m)]
    _ = 2 * (∑ m ∈ range (n+1), (A m)^2 + ∑ m ∈ range (n+1), (C m)^2) := by
      rw [← mul_sum, sum_add_distrib]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (band_proper_l2 n U L B hn hT hdiv) (band_smallPrime_l2 n U L B hn hdiv))
      (by norm_num)

theorem full_add_core_energy (n U L B : ℕ) (hn : 1 ≤ n) {T : ℝ}
    (hdiv : ∀ a ≤ n, (a.divisors.card : ℝ) ≤ T) :
    ∑ m ∈ range (n+1), (full n U L B m + core n U L B m)^2 ≤
    ((n+1 : ℕ) : ℝ) * (2 * (T^2 * Real.log n))^2 := by
  let A := T^2 * Real.log n
  calc
    _ ≤ ∑ _m ∈ range (n+1), (2*A)^2 := by
      refine sum_le_sum fun m hm => ?_
      have hm' := Nat.le_of_lt_succ (mem_range.mp hm)
      have h1 := band_uniform_bound n U L B m hm' hn hdiv
        (w:=ArithmeticFunction.vonMangoldt) (fun b => (abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg).le)
      have h2 := band_uniform_bound n U L B m hm' hn hdiv (abs_largePrimeWeight_le n)
      rw [← sq_abs (full n U L B m + core n U L B m)]
      apply pow_le_pow_left₀ (abs_nonneg _)
      exact (abs_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by dsimp [A]; ring))
    _ = _ := by simp [A]

theorem masked_square_reduction (s : Set ℝ) (hs : MeasurableSet s)
    (n U L B : ℕ) (hn : 1 ≤ n) {T scale : ℝ} (hT : 0 ≤ T)
    (hdiv : ∀ a ≤ n, (a.divisors.card : ℝ) ≤ T) (hscl : 0 < scale) :
    let F := full n U L B
    let P := core n U L B
    let A := T^2 * Real.log n
    ‖pairIntegral s n F F - pairIntegral s n P P‖ ≤
      (1/2) * (scale * (2 * (A * (T * ((B:ℝ) * (2 * Real.sqrt n * Real.log n))) +
        ((B * n.sqrt + 1 : ℕ) : ℝ) * A^2)) + scale⁻¹ * (((n+1:ℕ):ℝ) * (2*A)^2)) := by
  dsimp only
  rw [pairIntegral_sub_squares s hs]
  apply (pairIntegral_le_energy _ hs _ _ _ hscl).trans
  exact mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left (full_sub_core_energy _ _ _ _ hn hT hdiv) hscl.le)
    (mul_le_mul_of_nonneg_left (full_add_core_energy _ _ _ _ hn hdiv) (inv_nonneg.mpr hscl.le)))
    (by norm_num)

end
end GoldbachTransitionSquare

namespace GoldbachTransitionSquare
open Filter Topology
/- Divisor growth bound adapted from #2468 and #2492, cited above. -/
theorem divisorPower (K : ℕ) (hK : 0<K) :
    ∃ C : ℝ,1≤C ∧ ∀ n : ℕ, 0<n → (n.divisors.card:ℝ)^K ≤ C*n := by
  have hl := (isLittleO_pow_const_const_pow_of_one_lt (R:=ℝ) K (by norm_num : (1:ℝ)<2)).bound (by norm_num : (0:ℝ)<1)
  obtain ⟨E,hE⟩ := eventually_atTop.mp hl
  let c : ℝ := (2:ℝ)^K*((E:ℝ)+1)^K
  have hc : 1≤c := by
    dsimp [c]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) E]))
  have small (e : ℕ) : ((e:ℝ)+1)^K ≤ c*(2:ℝ)^e := by
    by_cases he : e<E
    · have hle : ((e:ℝ)+1)^K ≤ ((E:ℝ)+1)^K := pow_le_pow_left₀ (by positivity) (by exact_mod_cast (show e+1≤E+1 by omega)) _
      have h2 : (1:ℝ)≤2^K := one_le_pow₀ (by norm_num)
      have h3 : (1:ℝ)≤2^e := one_le_pow₀ (by norm_num)
      exact hle.trans ((le_mul_of_one_le_left (by positivity) h2).trans (le_mul_of_one_le_right (by positivity) h3))
    · have hs := hE (e+1) (by omega)
      simp only [Function.comp_apply,Real.norm_eq_abs,Nat.cast_add,Nat.cast_one,abs_of_nonneg (pow_nonneg (by positivity : 0≤(e:ℝ)+1) K),abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) (e+1)),one_mul,pow_succ] at hs
      rw [abs_of_nonneg (by positivity)] at hs
      have hK1 : (2:ℝ)≤2^K := by simpa using (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hK)
      have hE1 : (1:ℝ)≤((E:ℝ)+1)^K := one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) E])
      have hc2 : (2:ℝ)≤c := hK1.trans (le_mul_of_one_le_right (by positivity) hE1)
      exact hs.trans (by nlinarith [mul_le_mul_of_nonneg_right hc2 (by positivity : 0≤(2:ℝ)^e)])
  let P : ℕ := 2^K
  refine ⟨c^P,one_le_pow₀ hc,?_⟩
  intro n hn
  have hprod : (∏ p ∈ n.primeFactors,(p:ℝ)^(n.factorization p))=n := by
    exact_mod_cast (by simpa [Finsupp.prod,Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hn.ne' :
      (∏ p ∈ n.primeFactors,p^(n.factorization p))=n)
  have hlocal (p : ℕ) (hp : p∈n.primeFactors) :
      ((n.factorization p:ℝ)+1)^K ≤ (if p<P then c else 1)*(p:ℝ)^(n.factorization p) := by
    have h2 : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    split_ifs with h
    · exact (small _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) h2 _) (by linarith))
    · rw [one_mul]
      have he : ∀ e : ℕ,(e:ℝ)+1 ≤ (2:ℝ)^e := by
        intro e; induction e with
        | zero => norm_num
        | succ e ih => push_cast; rw [pow_succ]; linarith [show (0:ℝ)≤e by positivity]
      calc
        _ ≤ ((2:ℝ)^n.factorization p)^K := pow_le_pow_left₀ (by positivity) (he _) _
        _ = ((2:ℝ)^K)^n.factorization p := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
        _ ≤ _ := pow_le_pow_left₀ (by positivity) (by exact_mod_cast (show 2^K≤p by omega)) _
  have hcount : ((n.primeFactors.filter (·<P)).card)≤P := by
    have : n.primeFactors.filter (·<P)⊆range P := fun _ h => mem_range.mpr (mem_filter.mp h).2
    simpa using card_le_card this
  have hfactor : (∏ p ∈ n.primeFactors, if p<P then c else 1)≤c^P := by
    rw [←prod_filter,prod_const]; exact pow_le_pow_right₀ hc hcount
  rw [Nat.card_divisors hn.ne',Nat.cast_prod,←prod_pow]
  simp only [Nat.cast_add,Nat.cast_one]
  calc
    _ ≤ ∏ p ∈ n.primeFactors, (if p<P then c else 1)*(p:ℝ)^(n.factorization p) :=
      prod_le_prod₀ (fun _ _ => by positivity) hlocal
    _ ≤ _ := by rw [prod_mul_distrib,hprod]; exact mul_le_mul_of_nonneg_right hfactor (by positivity)
private theorem divisor_envelope : ∃ C : ℝ, 1 ≤ C ∧ ∀ n m : ℕ, m ≤ n →
    (m.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (1 / 128 : ℝ) := by
  obtain ⟨C, CLower, estimate⟩ := divisorPower 128 (by decide)
  let p : ℝ := 1 / 128
  have CNonnegative : 0 ≤ C := zero_le_one.trans CLower
  refine ⟨C ^ p, Real.one_le_rpow CLower (by norm_num [p]), fun n m upper => ?_⟩
  by_cases mPositive : 0 < m
  · have mReal : (m : ℝ) ≤ n := by exact_mod_cast upper
    have standard := (estimate m mPositive).trans (mul_le_mul_of_nonneg_left mReal CNonnegative)
    have powered := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg m.divisors.card) 128) standard
      (show 0 ≤ p by norm_num [p])
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg m.divisors.card),
      Real.mul_rpow CNonnegative (Nat.cast_nonneg n)] at powered
    norm_num [p] at powered ⊢
    exact powered
  · have mZero : m = 0 := by omega
    subst m
    simp only [Nat.divisors_zero, Finset.card_empty, Nat.cast_zero]
    positivity

end GoldbachTransitionSquare

namespace GoldbachTransitionSquare
noncomputable section
open MeasureTheory Filter Topology

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 2048 in
private theorem numerical_error {D X A T logN B rootN n : ℝ}
    (hD : 1 ≤ D) (hX : 1 ≤ X) (hA0 : 0 ≤ A) (hT0 : 0 ≤ T)
    (hl0 : 0 ≤ logN) (hB0 : 0 ≤ B) (hr0 : 0 ≤ rootN)
    (hA : A ≤ D^3 * X^3) (hT : T ≤ D*X) (hl : logN ≤ D*X)
    (hB : B ≤ X^43) (hr : rootN ≤ X^64) (hn : n ≤ X^128) :
    (1/2 : ℝ) * (X^10 * (2 * (A * (T * (B * (2 * rootN * logN))) +
        (B * rootN + 1) * A^2)) + (X^10)⁻¹ * ((n+1) * (2*A)^2)) ≤
    8 * D^6 * X^124 := by
  have hX0 := zero_le_one.trans hX
  have hD0 := zero_le_one.trans hD
  have hb : B * rootN + 1 ≤ 2 * X^107 := by
    calc
      _ ≤ X^43 * X^64 + 1 := add_le_add (mul_le_mul hB hr hr0 (pow_nonneg hX0 43)) le_rfl
      _ ≤ X^107 + X^107 := by rw [← pow_add]; exact add_le_add le_rfl (one_le_pow₀ hX)
      _ = _ := by ring
  have hs : n + 1 ≤ 2 * X^128 := by linarith [one_le_pow₀ hX (n:=128)]
  have ha : A * (T * (B * (2 * rootN * logN))) ≤ 2 * D^6 * X^113 := by
    calc
      _ ≤ (D^3 * X^3) * ((D*X) * (X^43 * (2 * X^64 * (D*X)))) := by gcongr
      _ = 2 * D^5 * X^112 := by ring
      _ ≤ _ := by gcongr <;> norm_num
  have hc : (B * rootN + 1) * A^2 ≤ 2 * D^6 * X^113 := by
    calc
      _ ≤ (2 * X^107) * (D^3 * X^3)^2 := by gcongr
      _ = _ := by ring
  have hd : (n+1) * (2*A)^2 ≤ 8 * D^6 * X^134 := by
    calc
      _ ≤ (2 * X^128) * (2*(D^3 * X^3))^2 := by gcongr
      _ = _ := by ring
  have left : X^10 * (2 * (A * (T * (B * (2 * rootN * logN))) + (B * rootN + 1) * A^2)) ≤
      8 * D^6 * X^124 := by
    calc
      _ ≤ X^10 * (2 * (2 * D^6 * X^113 + 2 * D^6 * X^113)) := by gcongr
      _ = 8 * D^6 * X^123 := by ring
      _ ≤ _ := by gcongr <;> norm_num
  have right : (X^10)⁻¹ * ((n+1) * (2*A)^2) ≤ 8 * D^6 * X^124 := by
    rw [← div_eq_inv_mul, div_le_iff₀ (by positivity : 0 < X^10)]
    exact hd.trans_eq (by ring)
  linarith

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 2048 in
theorem transition_power_saving :
    ∃ K : ℝ, 0 < K ∧ ∀ (n U L B : ℕ), 1 ≤ n → (B:ℝ) ≤ (n:ℝ)^(1/3:ℝ) →
    ∀ s : Set ℝ, MeasurableSet s →
    let F := full n U L B
    let P := core n U L B
    ‖pairIntegral s n F F - pairIntegral s n P P‖ ≤ K * (n:ℝ)^(124/128:ℝ) := by
  obtain ⟨C, hC, hdiv⟩ := divisor_envelope
  let D := max C 128
  have hD : 1 ≤ D := hC.trans (le_max_left ..)
  refine ⟨8 * D^6, by positivity, ?_⟩
  intro n U L B hn hB s hs
  dsimp only
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  let X := (n:ℝ)^(1/128:ℝ)
  have hX : 1 ≤ X := Real.one_le_rpow hnR (by norm_num)
  have posX : 0 < X := zero_lt_one.trans_le hX
  have hpow (k : ℕ) : X^k = (n:ℝ)^((k:ℝ)/128) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    ring
  have hlog := Real.log_le_rpow_div (x:=(n:ℝ)) (Nat.cast_nonneg _) (by norm_num : (0:ℝ)<1/128)
  have hl : Real.log n ≤ D*X := by
    calc
      _ ≤ X / (1/128:ℝ) := hlog
      _ = 128 * X := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) posX.le
  have hB' : (B:ℝ) ≤ X^43 := by
    rw [hpow]; exact hB.trans (Real.rpow_le_rpow_of_exponent_le hnR (by norm_num))
  have hsqrt : Real.sqrt n = X^64 := by rw [hpow, Real.sqrt_eq_rpow]; norm_num
  have hn' : (n:ℝ) = X^128 := by rw [hpow]; norm_num
  have hlog0 := Real.log_nonneg hnR
  have hD0 := zero_le_one.trans hD
  let T := D*X
  have hT : 0 ≤ T := mul_nonneg hD0 posX.le
  have hdiv' (m : ℕ) (hm : m ≤ n) : (m.divisors.card:ℝ) ≤ T :=
    (hdiv n m hm).trans (mul_le_mul_of_nonneg_right (le_max_left ..) posX.le)
  have h := masked_square_reduction s hs n U L B hn hT hdiv' (pow_pos posX 10)
  dsimp only at h
  push_cast at h
  have hroot : (n.sqrt:ℝ) ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
  have hA : T^2 * Real.log n ≤ D^3 * X^3 := by
    calc
      _ ≤ (D*X)^2 * (D*X) := mul_le_mul_of_nonneg_left hl (sq_nonneg _)
      _ = _ := by ring
  refine h.trans (le_trans ?_ ((numerical_error hD hX (mul_nonneg (sq_nonneg T) hlog0)
    hT hlog0 (Nat.cast_nonneg B) (Real.sqrt_nonneg _) hA (le_refl T) hl hB'
    hsqrt.le hn'.le).trans_eq ?_))
  · gcongr
  · rw [hpow]; norm_num
end
end GoldbachTransitionSquare

namespace GoldbachTransitionSquare

/-- A term of the additive convolution, with short factors a,b and complementary
    factors p,q. The counting lemma does not need primality of p or q. -/
structure Representation where
  a : ℕ
  b : ℕ
  p : ℕ
  q : ℕ
deriving DecidableEq

private def Representation.code (r : Representation) : ℕ × ℕ × ℤ :=
  (r.a, r.b, (r.p:ℤ) - r.q)

private theorem Representation.eq_of_code {n : ℕ} {r u : Representation}
    (ha : 0 < r.a) (hr : r.a*r.p + r.b*r.q = n)
    (hu : u.a*u.p + u.b*u.q = n) (hcode : r.code = u.code) : r = u := by
  rcases r with ⟨a,b,p,q⟩
  rcases u with ⟨a',b',p',q'⟩
  simp only [Representation.code, Prod.mk.injEq] at hcode
  obtain ⟨rfl,rfl,hd⟩ := hcode
  change a*p+b*q=n at hr
  change a*p'+b*q'=n at hu
  have eqZ : (a:ℤ)*p+b*q = a*p'+b*q' := by exact_mod_cast hr.trans hu.symm
  have hmul : ((a:ℤ)+b)*((p:ℤ)-p') = 0 := by linear_combination eqZ + (b:ℤ)*hd
  have hab : 0 < (a:ℤ)+b := by exact_mod_cast (show 0 < a+b by change 0 < a at ha; omega)
  have hp : p=p' := by have := (mul_eq_zero.mp hmul).resolve_left hab.ne'; omega
  have hq : q=q' := by omega
  cases hp; cases hq; rfl

/-- Close cofactor pairs have at most one solution for each (a,b,p-q). -/
theorem representation_card_near {n B D : ℕ} (s : Finset Representation)
    (hrep : ∀ r ∈ s, 0 < r.a ∧ r.a ≤ B ∧ 0 < r.b ∧ r.b ≤ B ∧
      r.a*r.p+r.b*r.q=n ∧ |(r.p:ℤ)-r.q| ≤ D) :
    s.card ≤ B^2 * (2*D+1) := by
  let box := (Icc 1 B) ×ˢ ((Icc 1 B) ×ˢ (Icc (-(D:ℤ)) (D:ℤ)))
  have hcard : s.card ≤ box.card := by
    apply card_le_card_of_injOn Representation.code
    · intro r hr
      obtain ⟨ha,ha',hb,hb',_,hd⟩ := hrep r hr
      exact mem_product.mpr ⟨mem_Icc.mpr ⟨ha,ha'⟩, mem_product.mpr ⟨mem_Icc.mpr ⟨hb,hb'⟩,
        mem_Icc.mpr (abs_le.mp hd)⟩⟩
    · intro r hr u hu he
      exact Representation.eq_of_code (hrep r hr).1 (hrep r hr).2.2.2.2.1
        (hrep u hu).2.2.2.2.1 he
  refine hcard.trans_eq ?_
  have hd : (Icc (-(D:ℤ)) (D:ℤ)).card = 2*D+1 := by rw [Int.card_Icc]; omega
  simp [box, hd, Nat.card_Icc, pow_two, Nat.mul_assoc]
end GoldbachTransitionSquare
namespace GoldbachTransitionSquare
noncomputable section
open Filter Topology MeasureTheory

def wide (n B H : ℕ) : Set ℝ := {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ B ∧ a ≤ q ∧
  Nat.Coprime a q ∧ |t - (a:ℝ)/q| ≤ (H:ℝ)/((q:ℝ)*n)}

theorem wide_measurable (n B H : ℕ) : MeasurableSet (wide n B H) := by
  unfold wide
  simp only [Set.ofPred_exists]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  by_cases condition : 1 ≤ q ∧ q ≤ B ∧ a ≤ q ∧ a.Coprime q
  · obtain ⟨qPositive, qBound, aBound, coprime⟩ := condition
    simp only [qPositive, qBound, aBound, true_and]
    have equality : {x : ℝ | a.Coprime q ∧ |x - (a : ℝ) / q| ≤ (H : ℝ) / ((q : ℝ) * n)} =
        {x : ℝ | |x - (a : ℝ) / q| ≤ (H : ℝ) / ((q : ℝ) * n)} := by
      ext x
      exact ⟨And.right, And.intro coprime⟩
    rw [equality]
    exact measurableSet_le (f := fun t : ℝ => |t - (a : ℝ) / q|)
      (g := fun _ : ℝ => (H : ℝ) / ((q : ℝ) * n)) (by fun_prop) measurable_const
  · have empty : {t : ℝ | 1 ≤ q ∧ q ≤ B ∧ a ≤ q ∧ a.Coprime q ∧
        |t - (a : ℝ) / q| ≤ (H : ℝ) / ((q : ℝ) * n)} = ∅ := by
      ext t
      simp
      tauto
    rw [empty]
    exact MeasurableSet.empty

def cutoffU (n : ℕ) := ⌊(n:ℝ)^(1/16:ℝ)⌋₊
def cutoffL (n : ℕ) := ⌊(n:ℝ)^(1/4:ℝ)⌋₊
def cutoffB (n : ℕ) := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
def deep (n : ℕ) := (wide n (cutoffB n) (256 * cutoffB n * (Nat.log 2 (n+2))^2))ᶜ
def fullValue (n : ℕ) : ℂ :=
  let F := full n (cutoffU n) (cutoffL n) (cutoffB n)
  pairIntegral (deep n) n F F
def coreValue (n : ℕ) : ℂ :=
  let P := core n (cutoffU n) (cutoffL n) (cutoffB n)
  pairIntegral (deep n) n P P

theorem error_eventually (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ‖fullValue n - coreValue n‖ ≤ e * (n:ℝ) := by
  obtain ⟨K, _, hK⟩ := transition_power_saving
  have hh : Tendsto (fun n : ℕ => K * (n:ℝ)^(-(1/32):ℝ)) atTop (𝓝 0) := by
    have limit : Tendsto (fun n : ℕ => (n:ℝ)^(-(1/32):ℝ)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/32)).comp
        (tendsto_natCast_atTop_atTop (R:=ℝ))
    simpa only [mul_zero] using (tendsto_const_nhds (x:=K)).mul limit
  filter_upwards [eventually_ge_atTop 1, hh.eventually_lt_const he] with n hn hsmall
  have hpos : 0 < (n:ℝ) := by exact_mod_cast hn
  have hbound := hK n (cutoffU n) (cutoffL n) (cutoffB n) hn
    (Nat.floor_le (by positivity)) (deep n) (wide_measurable ..).compl
  refine hbound.trans ?_
  calc
    K * (n:ℝ)^(124/128:ℝ) = (K*(n:ℝ)^(-(1/32):ℝ)) * (n:ℝ) := by
      rw [mul_assoc, show (124/128:ℝ) = -(1/32:ℝ)+1 by norm_num,
        Real.rpow_add hpos, Real.rpow_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall.le hpos.le

def smallEven (f : ℕ → ℂ) : Prop :=
  ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖f n‖ ≤ e*(n:ℝ)

theorem smallEven_transfer {f g : ℕ → ℂ}
    (herr : ∀ e : ℝ, 0 < e → ∀ᶠ n : ℕ in atTop, ‖f n - g n‖ ≤ e*(n:ℝ)) :
    smallEven g → smallEven f := by
  intro hg e he
  have hhalf := half_pos he
  obtain ⟨N,hN⟩ := hg (e/2) hhalf
  obtain ⟨M,hM⟩ := eventually_atTop.mp (herr (e/2) hhalf)
  refine ⟨max M N, fun n hn hEven => ?_⟩
  have h1 := hM n ((le_max_left ..).trans hn)
  have h2 := hN n ((le_max_right ..).trans hn) hEven
  have h3 := norm_add_le (f n - g n) (g n)
  rw [sub_add_cancel] at h3
  linarith

theorem full_iff_large_prime_cofactors : smallEven fullValue ↔ smallEven coreValue := by
  constructor
  · apply smallEven_transfer
    intro e he
    filter_upwards [error_eventually e he] with n hn
    simpa only [norm_sub_rev (coreValue n) (fullValue n)] using hn
  · exact smallEven_transfer error_eventually

end
end GoldbachTransitionSquare

namespace GoldbachTransitionSquare
theorem frozen_iff_core : (
let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let Λ := ArithmeticFunction.vonMangoldt; let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊; let B₁ := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊; let B₂ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let τ₂ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₁ n < a ∧ a ≤ B₂ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let Jdeep := fun (n : ℕ) (u v : ℕ → ℝ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖Jdeep n (τ₂ n) (τ₂ n)‖ ≤ e * (n : ℝ)
) ↔ smallEven coreValue := full_iff_large_prime_cofactors
end GoldbachTransitionSquare

/- Generic Fourier sampling estimate from goldbach-proofs #2492, cited above. -/
section

open Finset MeasureTheory
open scoped ComplexConjugate

namespace DyadicMixedB4Fourier

noncomputable section

def frequency (k : ℤ) : ℂ := (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)

def mode (k : ℤ) (t : ℝ) : ℂ := Complex.exp (frequency k * (t : ℂ))

theorem continuous_mode (k : ℤ) : Continuous (mode k) := by
  unfold mode
  fun_prop

theorem periodic_mode (k : ℤ) : Function.Periodic (mode k) 1 := by
  intro t
  unfold mode
  rw [Complex.ofReal_add, Complex.ofReal_one, mul_add, Complex.exp_add]
  have onePhase : Complex.exp (frequency k * 1) = 1 := by
    simp [frequency, Complex.exp_int_mul_two_pi_mul_I]
  rw [onePhase, mul_one]

theorem hasDerivAt_mode (k : ℤ) (t : ℝ) :
    HasDerivAt (mode k) (frequency k * mode k t) t := by
  have linear : HasDerivAt (fun z : ℂ => frequency k * z) (frequency k) (t : ℂ) := by
    simpa only [mul_one, id_eq] using (hasDerivAt_id (t : ℂ)).const_mul (frequency k)
  change HasDerivAt (fun x : ℝ => Complex.exp (frequency k * (x : ℂ)))
    (frequency k * Complex.exp (frequency k * (t : ℂ))) t
  rw [mul_comm (frequency k)]
  exact linear.cexp.comp_ofReal (z := t)

theorem mode_integral (k : ℤ) :
    (∫ t in (0 : ℝ)..1, mode k t) = if k = 0 then 1 else 0 := by
  by_cases zero : k = 0
  · simp [zero, mode, frequency]
  · have kNonzero : (k : ℂ) ≠ 0 := Int.cast_ne_zero.mpr zero
    have piNonzero : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have frequencyNonzero : frequency k ≠ 0 := by
      exact mul_ne_zero kNonzero (mul_ne_zero (mul_ne_zero (by norm_num) piNonzero) Complex.I_ne_zero)
    change (∫ t in (0 : ℝ)..1, Complex.exp (frequency k * (t : ℂ))) = _
    rw [ite_eq_right zero, integral_exp_mul_complex frequencyNonzero]
    simp [frequency, Complex.exp_int_mul_two_pi_mul_I]

theorem mode_mul_conj (j k : ℤ) (t : ℝ) :
    mode j t * star (mode k t) = mode (j - k) t := by
  change Complex.exp (frequency j * (t : ℂ)) *
    conj (Complex.exp (frequency k * (t : ℂ))) = _
  rw [← Complex.exp_conj, ← Complex.exp_add]
  unfold mode frequency
  congr 1
  have conjTwo : (starRingEnd ℂ) 2 = 2 := by
    simpa only [Nat.cast_ofNat] using (map_natCast (starRingEnd ℂ) 2)
  simp [map_mul, Complex.conj_I, Int.cast_sub, conjTwo]
  ring

theorem parseval_finite_modes (limit : ℕ) (coefficient : ℕ → ℂ) :
    (∫ t in (0 : ℝ)..1,
      ((‖∑ j ∈ range limit, coefficient j * mode (j : ℤ) t‖ ^ 2 : ℝ) : ℂ)) =
      ∑ j ∈ range limit, ((‖coefficient j‖ ^ 2 : ℝ) : ℂ) := by
  let entry (j k : ℕ) (t : ℝ) : ℂ :=
    coefficient j * star (coefficient k) * mode ((j : ℤ) - (k : ℤ)) t
  have entryContinuous (j k : ℕ) : Continuous (entry j k) :=
    continuous_const.mul (continuous_mode ((j : ℤ) - (k : ℤ)))
  calc
    _ = ∫ t in (0 : ℝ)..1, ∑ j ∈ range limit, ∑ k ∈ range limit, entry j k t := by
      apply intervalIntegral.integral_congr
      intro t _
      change ((‖∑ j ∈ range limit, coefficient j * mode (j : ℤ) t‖ ^ 2 : ℝ) : ℂ) = _
      rw [Complex.ofReal_pow, ← Complex.mul_conj']
      change (∑ j ∈ range limit, coefficient j * mode (j : ℤ) t) *
          star (∑ j ∈ range limit, coefficient j * mode (j : ℤ) t) = _
      rw [star_sum, sum_mul_sum]
      refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
      rw [star_mul]
      calc
        _ = coefficient j * star (coefficient k) *
            (mode (j : ℤ) t * star (mode (k : ℤ) t)) := by ac_rfl
        _ = _ := by rw [mode_mul_conj]
    _ = ∑ j ∈ range limit, ∑ k ∈ range limit, ∫ t in (0 : ℝ)..1, entry j k t := by
      rw [intervalIntegral.integral_finsetSum]
      · refine sum_congr rfl fun j _ => ?_
        rw [intervalIntegral.integral_finsetSum]
        exact fun k _ => (entryContinuous j k).intervalIntegrable _ _
      · intro j _
        exact (continuous_finsetSum _ fun k _ => entryContinuous j k).intervalIntegrable _ _
    _ = _ := by
      refine sum_congr rfl fun j jMember => ?_
      rw [sum_eq_single_of_mem j jMember]
      · simp [entry, intervalIntegral.integral_const_mul, mode_integral, Complex.mul_conj']
      · intro k _ different
        have frequencyNonzero : (j : ℤ) - (k : ℤ) ≠ 0 := by omega
        simp [entry, intervalIntegral.integral_const_mul, mode_integral, frequencyNonzero]

theorem periodic_mode_sum (limit : ℕ) (coefficient : ℕ → ℂ) :
    Function.Periodic (fun t => ∑ j ∈ range limit, coefficient j * mode (j : ℤ) t) 1 := by
  intro t
  refine sum_congr rfl fun j _ => ?_
  rw [periodic_mode]

theorem hasDerivAt_mode_sum (limit : ℕ) (coefficient : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (fun x => ∑ j ∈ range limit, coefficient j * mode (j : ℤ) x)
      (∑ j ∈ range limit, (coefficient j * frequency (j : ℤ)) * mode (j : ℤ) t) t := by
  apply HasDerivAt.fun_sum
  intro j _
  simpa only [mul_assoc] using (hasDerivAt_mode (j : ℤ) t).const_mul (coefficient j)


end
end DyadicMixedB4Fourier

end

section

open Finset MeasureTheory Set

namespace DyadicMixedB4Sampling

theorem sample_mul_length_le_integrals {f gradient : ℝ → ℝ} {a b centre : ℝ}
    (derivative : ∀ x, HasDerivAt f (gradient x) x) (gradientContinuous : Continuous gradient)
    (centreLower : a ≤ centre) (centreUpper : centre ≤ b) :
    (b - a) * f centre ≤ (∫ x in a..b, f x) + (b - a) * ∫ x in a..b, |gradient x| := by
  have fDifferentiable : Differentiable ℝ f := fun x => (derivative x).differentiableAt
  have fContinuous : Continuous f := fDifferentiable.continuous
  let variation : ℝ := ∫ x in a..b, |gradient x|
  have difference {x y : ℝ} (left : a ≤ x) (ordered : x ≤ y) (right : y ≤ b) :
      |f y - f x| ≤ variation := by
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => derivative z)
      (gradientContinuous.intervalIntegrable x y)]
    exact (intervalIntegral.abs_integral_le_integral_abs ordered).trans
      (intervalIntegral.integral_mono_interval left ordered right
        (Filter.Eventually.of_forall fun z => abs_nonneg (gradient z))
        (gradientContinuous.abs.intervalIntegrable a b))
  have pointwise (x : ℝ) (membership : x ∈ Icc a b) : f centre ≤ f x + variation := by
    have absoluteDifference : |f centre - f x| ≤ variation := by
      rcases le_total x centre with ordered | ordered
      · exact difference membership.1 ordered centreUpper
      · rw [abs_sub_comm]
        exact difference centreLower ordered membership.2
    linarith only [absoluteDifference, le_abs_self (f centre - f x)]
  have integrated := intervalIntegral.integral_mono_on (μ := volume) (centreLower.trans centreUpper)
    ((continuous_const : Continuous fun _ : ℝ => f centre).intervalIntegrable a b)
    ((fContinuous.add continuous_const).intervalIntegrable a b) pointwise
  change (∫ _ in a..b, f centre) ≤ (∫ x in a..b, f x + variation) at integrated
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_add (fContinuous.intervalIntegrable a b)
      ((continuous_const : Continuous fun _ : ℝ => variation).intervalIntegrable a b),
    intervalIntegral.integral_const] at integrated
  simpa only [variation, smul_eq_mul] using integrated

theorem separated_samples_le_integrals {f gradient : ℝ → ℝ} {a b radius : ℝ}
    (points : Finset ℝ) (ordered : a ≤ b) (radiusPositive : 0 < radius)
    (windowFits : ∀ x ∈ points, a ≤ x - radius ∧ x + radius ≤ b)
    (separated : (points : Set ℝ).Pairwise (fun x y => 2 * radius ≤ |x - y|))
    (fNonnegative : ∀ x, 0 ≤ f x) (derivative : ∀ x, HasDerivAt f (gradient x) x)
    (gradientContinuous : Continuous gradient) :
    (2 * radius) * (∑ x ∈ points, f x) ≤
      (∫ x in a..b, f x) + (2 * radius) * ∫ x in a..b, |gradient x| := by
  classical
  let window (x : ℝ) := Ioc (x - radius) (x + radius)
  have windowOrdered (x : ℝ) : x - radius ≤ x + radius := by linarith
  have disjoint : Set.Pairwise (points : Set ℝ) (fun x y => Disjoint (window x) (window y)) := by
    intro x xMember y yMember distinct
    rw [Set.disjoint_left]
    intro z inX inY
    have hx : x - radius < z ∧ z ≤ x + radius := inX
    have hy : y - radius < z ∧ z ≤ y + radius := inY
    have close : |x - y| < 2 * radius := by
      rw [abs_lt]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    exact (not_lt_of_ge (separated xMember yMember distinct)) close
  have unionFits : (⋃ x ∈ points, window x) ⊆ Ioc a b := by
    intro z membership
    obtain ⟨x, atPoint, inside⟩ := Set.mem_iUnion₂.mp membership
    obtain ⟨left, right⟩ := windowFits x atPoint
    exact Ioc_subset_Ioc left right inside
  have compare {g : ℝ → ℝ} (gContinuous : Continuous g) (gNonnegative : ∀ x, 0 ≤ g x) :
      (∑ x ∈ points, ∫ t in x - radius..x + radius, g t) ≤ ∫ t in a..b, g t := by
    calc
      _ = ∫ t in ⋃ x ∈ points, window x, g t := by
        rw [integral_biUnion_finset points (fun x _ => measurableSet_Ioc) disjoint
          (fun x _ => (gContinuous.intervalIntegrable (x - radius) (x + radius)).1)]
        exact sum_congr rfl fun x _ => intervalIntegral.integral_of_le (windowOrdered x)
      _ ≤ _ := by
        rw [intervalIntegral.integral_of_le ordered]
        exact setIntegral_mono_set (gContinuous.intervalIntegrable a b).1
          (Filter.Eventually.of_forall gNonnegative) unionFits.eventuallySubset
  have fDifferentiable : Differentiable ℝ f := fun x => (derivative x).differentiableAt
  have fContinuous : Continuous f := fDifferentiable.continuous
  calc
    _ = ∑ x ∈ points, (2 * radius) * f x := mul_sum points _ _
    _ ≤ ∑ x ∈ points, ((∫ t in x - radius..x + radius, f t) +
        (2 * radius) * (∫ t in x - radius..x + radius, |gradient t|)) := by
      refine sum_le_sum fun x _ => ?_
      have localInequality := sample_mul_length_le_integrals derivative gradientContinuous
        (by linarith : x - radius ≤ x) (by linarith : x ≤ x + radius)
      rwa [show x + radius - (x - radius) = 2 * radius by ring] at localInequality
    _ = (∑ x ∈ points, ∫ t in x - radius..x + radius, f t) +
        (2 * radius) * (∑ x ∈ points, ∫ t in x - radius..x + radius, |gradient t|) := by
      rw [sum_add_distrib, mul_sum]
    _ ≤ _ := add_le_add (compare fContinuous fNonnegative)
      (mul_le_mul_of_nonneg_left (compare gradientContinuous.abs fun t => abs_nonneg (gradient t))
        (by positivity))


end DyadicMixedB4Sampling

end

section

open Finset Set
open scoped RealInnerProductSpace

namespace DyadicMixedB4Fourier

noncomputable section

theorem integral_three_periods {f : ℝ → ℝ} (continuous : Continuous f)
    (periodic : Function.Periodic f 1) :
    (∫ t in (-1 : ℝ)..2, f t) = 3 * ∫ t in (0 : ℝ)..1, f t := by
  have shift (a b : ℝ) : (∫ t in a..b, f t) = ∫ t in a + 1..b + 1, f t := by
    calc
      _ = ∫ t in a..b, f (t + 1) := intervalIntegral.integral_congr fun t _ => (periodic t).symm
      _ = _ := intervalIntegral.integral_comp_add_right f 1
  have first : (∫ t in (-1 : ℝ)..0, f t) = ∫ t in (0 : ℝ)..1, f t := by
    convert shift (-1) 0 using 2 <;> norm_num
  have last : (∫ t in (0 : ℝ)..1, f t) = ∫ t in (1 : ℝ)..2, f t := by
    convert shift 0 1 using 2 <;> norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals (continuous.intervalIntegrable (-1) 1)
      (continuous.intervalIntegrable 1 2),
    ← intervalIntegral.integral_add_adjacent_intervals (continuous.intervalIntegrable (-1) 0)
      (continuous.intervalIntegrable 0 1), first, ← last]
  ring

theorem parseval_real (limit : ℕ) (coefficient : ℕ → ℂ) :
    (∫ t in (0 : ℝ)..1, ‖∑ j ∈ range limit, coefficient j * mode (j : ℤ) t‖ ^ 2) =
      ∑ j ∈ range limit, ‖coefficient j‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum, ← intervalIntegral.integral_ofReal]
  exact parseval_finite_modes limit coefficient

theorem norm_frequency_nat (j : ℕ) : ‖frequency (j : ℤ)‖ = (j : ℝ) * (2 * Real.pi) := by
  rw [frequency, Int.cast_natCast, norm_mul, Complex.norm_natCast, norm_mul, Complex.norm_I,
    mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  norm_num

theorem additive_large_sieve (limit : ℕ) (coefficient : ℕ → ℂ) (points : Finset ℝ)
    {radius : ℝ} (radiusPositive : 0 < radius) (radiusUpper : radius ≤ 1)
    (unitInterval : (points : Set ℝ) ⊆ Icc 0 1)
    (separated : (points : Set ℝ).Pairwise (fun x y => 2 * radius ≤ |x - y|)) :
    (∑ x ∈ points, ‖∑ j ∈ range limit, coefficient j * mode (j : ℤ) x‖ ^ 2) ≤
      (3 / (2 * radius) + 6 * (1 + 2 * Real.pi * limit)) *
        ∑ j ∈ range limit, ‖coefficient j‖ ^ 2 := by
  let polynomial (t : ℝ) := ∑ j ∈ range limit, coefficient j * mode (j : ℤ) t
  let derivativePolynomial (t : ℝ) :=
    ∑ j ∈ range limit, (coefficient j * frequency (j : ℤ)) * mode (j : ℤ) t
  let energy (t : ℝ) := ‖polynomial t‖ ^ 2
  let derivativeEnergy (t : ℝ) := ‖derivativePolynomial t‖ ^ 2
  let variation (t : ℝ) := 2 * ⟪polynomial t, derivativePolynomial t⟫
  let band : ℝ := 1 + 2 * Real.pi * limit
  let mass := ∑ j ∈ range limit, ‖coefficient j‖ ^ 2
  have bandPositive : 0 < band := by dsimp [band]; positivity
  have polynomialDerivative (t : ℝ) : HasDerivAt polynomial (derivativePolynomial t) t :=
    hasDerivAt_mode_sum limit coefficient t
  have energyDerivative (t : ℝ) : HasDerivAt energy (variation t) t :=
    (polynomialDerivative t).norm_sq
  have polynomialContinuous : Continuous polynomial :=
    continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_mode (j : ℤ))
  have derivativeContinuous : Continuous derivativePolynomial :=
    continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_mode (j : ℤ))
  have energyContinuous : Continuous energy := polynomialContinuous.norm.pow 2
  have derivativeEnergyContinuous : Continuous derivativeEnergy := derivativeContinuous.norm.pow 2
  have variationContinuous : Continuous variation :=
    continuous_const.mul (polynomialContinuous.inner derivativeContinuous)
  have polynomialPeriodic : Function.Periodic polynomial 1 := periodic_mode_sum limit coefficient
  have derivativePeriodic : Function.Periodic derivativePolynomial 1 := periodic_mode_sum limit _
  have energyPeriodic : Function.Periodic energy 1 := fun t => by
    unfold energy
    rw [polynomialPeriodic]
  have variationPeriodic : Function.Periodic (fun t => |variation t|) 1 := fun t => by
    change |variation (t + 1)| = |variation t|
    dsimp only [variation]
    rw [polynomialPeriodic, derivativePeriodic]
  have energyIntegral : (∫ t in (0 : ℝ)..1, energy t) = mass := parseval_real limit coefficient
  have derivativeIntegral : (∫ t in (0 : ℝ)..1, derivativeEnergy t) ≤ band ^ 2 * mass := by
    change (∫ t in (0 : ℝ)..1,
      ‖∑ j ∈ range limit, (coefficient j * frequency (j : ℤ)) * mode (j : ℤ) t‖ ^ 2) ≤ _
    rw [parseval_real]
    unfold mass
    rw [mul_sum]
    refine sum_le_sum fun j member => ?_
    have jBound : (j : ℝ) ≤ limit := by exact_mod_cast (mem_range.mp member).le
    have frequencyBound : ‖frequency (j : ℤ)‖ ≤ band := by
      rw [norm_frequency_nat]
      dsimp [band]
      nlinarith [mul_nonneg (sub_nonneg.mpr jBound) Real.pi_pos.le]
    calc
      _ = ‖frequency (j : ℤ)‖ ^ 2 * ‖coefficient j‖ ^ 2 := by rw [norm_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) frequencyBound 2) (sq_nonneg _)
  have pointwise (t : ℝ) : |variation t| ≤ band * energy t + band⁻¹ * derivativeEnergy t := by
    have quadratic : 2 * ‖polynomial t‖ * ‖derivativePolynomial t‖ ≤
        band * energy t + band⁻¹ * derivativeEnergy t := by
      have square := sq_nonneg (band * ‖polynomial t‖ - ‖derivativePolynomial t‖)
      have multiplied :
          (2 * ‖polynomial t‖ * ‖derivativePolynomial t‖ - band * energy t) * band ≤
            derivativeEnergy t := by
        dsimp [energy, derivativeEnergy]
        nlinarith only [square]
      have divided := (le_div_iff₀ bandPositive).mpr multiplied
      rw [inv_mul_eq_div]
      linarith only [divided]
    calc
      _ ≤ 2 * ‖polynomial t‖ * ‖derivativePolynomial t‖ := by
        unfold variation
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), mul_assoc]
        exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
      _ ≤ _ := quadratic
  have variationIntegral : (∫ t in (0 : ℝ)..1, |variation t|) ≤ 2 * band * mass := by
    have scaledEnergy : IntervalIntegrable (fun t => band * energy t)
        MeasureTheory.volume 0 1 := (continuous_const.mul energyContinuous).intervalIntegrable 0 1
    have scaledDerivative : IntervalIntegrable (fun t => band⁻¹ * derivativeEnergy t)
        MeasureTheory.volume 0 1 := (continuous_const.mul derivativeEnergyContinuous).intervalIntegrable 0 1
    have integrated := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (by norm_num : (0 : ℝ) ≤ 1)
      (variationContinuous.abs.intervalIntegrable 0 1)
      (((continuous_const.mul energyContinuous).add
        (continuous_const.mul derivativeEnergyContinuous)).intervalIntegrable 0 1)
      (fun t _ => pointwise t)
    calc
      _ ≤ ∫ t in (0 : ℝ)..1, band * energy t + band⁻¹ * derivativeEnergy t := integrated
      _ = band * mass + band⁻¹ * ∫ t in (0 : ℝ)..1, derivativeEnergy t := by
        rw [intervalIntegral.integral_add scaledEnergy scaledDerivative,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, energyIntegral]
      _ ≤ band * mass + band⁻¹ * (band ^ 2 * mass) :=
        (add_le_add_right (mul_le_mul_of_nonneg_left derivativeIntegral (inv_nonneg.mpr bandPositive.le)) _)
      _ = _ := by field_simp [bandPositive.ne']; ring
  have windowFits (t : ℝ) (member : t ∈ points) : -1 ≤ t - radius ∧ t + radius ≤ 2 := by
    obtain ⟨lower, upper⟩ := unitInterval member
    constructor <;> linarith
  have samples := DyadicMixedB4Sampling.separated_samples_le_integrals points
    (by norm_num : (-1 : ℝ) ≤ 2) radiusPositive windowFits separated
    (fun t => sq_nonneg ‖polynomial t‖) energyDerivative variationContinuous
  rw [integral_three_periods energyContinuous energyPeriodic, energyIntegral,
    integral_three_periods variationContinuous.abs variationPeriodic] at samples
  change (∑ t ∈ points, energy t) ≤ (3 / (2 * radius) + 6 * band) * mass
  have multiplied : (∑ t ∈ points, energy t) * (2 * radius) ≤
      3 * mass + (2 * radius) * (3 * (2 * band * mass)) := by
    rw [mul_comm]
    exact samples.trans (by gcongr)
  calc
    _ ≤ (3 * mass + (2 * radius) * (3 * (2 * band * mass))) / (2 * radius) :=
      (le_div_iff₀ (by positivity)).mpr multiplied
    _ = _ := by field_simp [radiusPositive.ne']; ring


end
end DyadicMixedB4Fourier

end

namespace GoldbachTransitionSquare
noncomputable section
open MeasureTheory DyadicMixedB4Fourier

private def rationalPoint (q j : ℕ) : ℝ := (j:ℝ)/q

theorem rational_grid_sieve (q N : ℕ) (hq : 0<q) (c : ℕ → ℂ) :
    (∑ j ∈ range q, ‖∑ k ∈ range N, c k * mode (k:ℤ) (rationalPoint q j)‖^2) ≤
    (3*(q:ℝ) + 6*(1 + 2*Real.pi*N)) * ∑ k ∈ range N, ‖c k‖^2 := by
  have hqr : 0 < (q:ℝ) := by exact_mod_cast hq
  let pts := (range q).image (rationalPoint q)
  have inj : Function.Injective (rationalPoint q) := by
    intro a b hab
    unfold rationalPoint at hab
    exact_mod_cast (div_left_inj' hqr.ne').mp hab
  have unit : (pts : Set ℝ) ⊆ Set.Icc 0 1 := by
    intro x hx
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hx
    exact ⟨div_nonneg (Nat.cast_nonneg _) hqr.le, (div_le_one hqr).mpr
      (by exact_mod_cast (mem_range.mp hj).le)⟩
  have sep : (pts : Set ℝ).Pairwise (fun x y => 2 * (1/(2*(q:ℝ))) ≤ |x-y|) := by
    intro x hx y hy hne
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hx
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hy
    have hjk : j ≠ k := fun h => hne (congrArg (rationalPoint q) h)
    have hl : (1:ℝ) ≤ |(j:ℝ)-k| := by
      rcases lt_or_gt_of_ne hjk with h | h
      · rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h.le))]
        have : (j:ℝ)+1 ≤ k := by exact_mod_cast h
        linarith
      · rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h.le))]
        have : (k:ℝ)+1 ≤ j := by exact_mod_cast h
        linarith
    unfold rationalPoint
    rw [← sub_div, abs_div, abs_of_pos hqr]
    calc
      _ = 1/(q:ℝ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hl hqr.le
  have rad : 1/(2*(q:ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]; have : (1:ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have h := additive_large_sieve N c pts (by positivity : 0 < 1/(2*(q:ℝ))) rad unit sep
  have simpRad : (3:ℝ)/(2*(1/(2*(q:ℝ)))) = 3*q := by field_simp <;> ring
  rw [simpRad] at h
  simpa only [pts, sum_image (fun a _ b _ hab => inj hab)] using h

theorem permuted_grid_sum (p q : ℕ) (hq : 0<q) (hc : q.Coprime p) (f : ℕ → ℝ) :
    ∑ a ∈ range q, f ((p*a) % q) = ∑ a ∈ range q, f a := by
  let points := (range q).image (fun a => (p*a) % q)
  have inj : Set.InjOn (fun a => (p*a) % q) (range q : Set ℕ) := by
    intro a ha b hb he
    have hm : a ≡ b [MOD q] := Nat.ModEq.cancel_left_of_coprime hc he
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (mem_range.mp ha),
      Nat.mod_eq_of_lt (mem_range.mp hb)] using hm
  have sub : points ⊆ range q := by
    intro j hj
    obtain ⟨a,_,rfl⟩ := mem_image.mp hj
    exact mem_range.mpr (Nat.mod_lt _ hq)
  have eqp : points = range q := eq_of_subset_of_card_le sub
    (by simp only [points, card_image_of_injOn inj, le_refl])
  calc
    _ = ∑ j ∈ points, f j := (sum_image inj).symm
    _ = _ := by rw [eqp]

end
end GoldbachTransitionSquare

namespace GoldbachTransitionSquare
noncomputable section
open DyadicMixedB4Fourier

def row (N p : ℕ) (c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ j ∈ range N, c j * mode j (p*t)

theorem mode_translate (j : ℤ) (x y : ℝ) : mode j (x+y) = mode j x * mode j y := by
  simp only [mode, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem mode_norm_one (j : ℤ) (t : ℝ) : ‖mode j t‖ = 1 := by
  simp [mode, frequency, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem row_grid_energy (q N p : ℕ) (hq : 0<q) (hc : q.Coprime p) (β : ℝ) (c : ℕ → ℂ) :
    (∑ a ∈ range q, ‖row N p c (rationalPoint q a + β)‖^2) ≤
    (3*(q:ℝ) + 6*(1 + 2*Real.pi*N)) * ∑ j ∈ range N, ‖c j‖^2 := by
  let w (j:ℕ) := c j * mode j (p*β)
  let F (z:ℕ) := ‖∑ j ∈ range N, w j * mode j (rationalPoint q z)‖^2
  have hqr : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have reduce (a : ℕ) : (p:ℝ)*rationalPoint q a =
      rationalPoint q ((p*a) % q) + ((p*a/q:ℕ):ℝ) := by
    have h := Nat.mod_add_div (p*a) q
    have hr : (((p*a) % q:ℕ):ℝ)+(q:ℝ)*((p*a/q:ℕ):ℝ) = p*a := by exact_mod_cast h
    unfold rationalPoint
    field_simp
    linarith
  have one (a : ℕ) : ‖row N p c (rationalPoint q a + β)‖^2 = F ((p*a) % q) := by
    apply congrArg (fun z : ℂ => ‖z‖^2)
    refine sum_congr rfl fun j hj => ?_
    have per := (periodic_mode (j:ℤ)).nat_mul (p*a/q) (rationalPoint q ((p*a) % q))
    simp only [mul_one] at per
    rw [mul_add, mode_translate, reduce, per]
    unfold w
    ring
  calc
    _ = ∑ a ∈ range q, F ((p*a) % q) := sum_congr rfl fun a _ => one a
    _ = ∑ a ∈ range q, F a := permuted_grid_sum p q hq hc F
    _ ≤ _ := by
      simpa only [w, norm_mul, mode_norm_one, mul_one] using rational_grid_sieve q N hq w

end
end GoldbachTransitionSquare

namespace GoldbachTransitionSquare
noncomputable section
open MeasureTheory DyadicMixedB4Fourier

theorem continuous_row (N p : ℕ) (c : ℕ → ℂ) : Continuous (row N p c) := by
  unfold row
  apply continuous_finsetSum
  intro j _
  exact continuous_const.mul ((continuous_mode j).comp (continuous_const.mul continuous_id))

/-- Integral of row energy on the entire grid of translated intervals for q. -/
theorem gridInterval_energy (q N p : ℕ) (hq : 0<q) (hc : q.Coprime p) (c : ℕ → ℂ)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (∑ a ∈ range q, ∫ x in (rationalPoint q a - δ)..(rationalPoint q a + δ),
      ‖row N p c x‖^2) ≤
    (2*δ) * ((3*(q:ℝ) + 6*(1 + 2*Real.pi*N)) * ∑ j ∈ range N, ‖c j‖^2) := by
  let g (a : ℕ) (t : ℝ) := ‖row N p c (rationalPoint q a + t)‖^2
  have hg (a : ℕ) : Continuous (g a) :=
    (((continuous_row N p c).comp (continuous_const.add continuous_id)).norm).pow 2
  have shift (a : ℕ) :
      (∫ x in (rationalPoint q a - δ)..(rationalPoint q a + δ), ‖row N p c x‖^2)
      = ∫ x in -δ..δ, g a x := by
    simpa only [g, sub_eq_add_neg] using
      (intervalIntegral.integral_comp_add_left (fun x => ‖row N p c x‖^2)
        (rationalPoint q a) (a := -δ) (b := δ)).symm
  simp_rw [shift]
  rw [← intervalIntegral.integral_finsetSum (fun a _ => (hg a).intervalIntegrable (-δ) δ)]
  have hle := intervalIntegral.integral_mono_on (μ := volume) (neg_le_self hδ)
    ((continuous_finsetSum _ (fun a _ => hg a)).intervalIntegrable _ _)
    (intervalIntegrable_const (c := (3*(q:ℝ) + 6*(1 + 2*Real.pi*N)) *
      ∑ j ∈ range N, ‖c j‖^2)) (fun t _ => row_grid_energy q N p hq hc t c)
  refine hle.trans_eq ?_
  rw [intervalIntegral.integral_const, smul_eq_mul]; ring
end
end GoldbachTransitionSquare

namespace GoldbachTransitionSquare
noncomputable section
open MeasureTheory DyadicMixedB4Fourier

theorem row_periodic (N p : ℕ) (c : ℕ → ℂ) : Function.Periodic (row N p c) 1 := by
  intro t
  unfold row
  refine sum_congr rfl fun j _ => ?_
  rw [mul_add, mul_one]
  have per := (periodic_mode j).nat_mul p ((p:ℝ)*t)
  simpa only [mul_one] using congrArg (fun x : ℂ => c j * x) per

private def gridCell (n H q a : ℕ) : Set ℝ :=
  Set.Icc (rationalPoint q a - (H:ℝ)/(q*n:ℝ)) (rationalPoint q a + (H:ℝ)/(q*n:ℝ))

private theorem cellMass (n H N p q : ℕ) (hq : 0<q) (hc : q.Coprime p) (c : ℕ → ℂ) :
    (∑ a ∈ range (q+1), ∫ x in gridCell n H q a, ‖row N p c x‖^2) ≤
    4*((H:ℝ)/(q*n:ℝ)) * ((3*(q:ℝ) + 6*(1+2*Real.pi*N)) * ∑ j ∈ range N, ‖c j‖^2) := by
  let δ := (H:ℝ)/(q*n:ℝ)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have cellEq (a : ℕ) :
      (∫ x in gridCell n H q a, ‖row N p c x‖^2) =
        ∫ x in (rationalPoint q a - δ)..(rationalPoint q a + δ), ‖row N p c x‖^2 := by
    rw [intervalIntegral.integral_of_le (by linarith : rationalPoint q a - δ ≤ rationalPoint q a + δ)]
    exact integral_Icc_eq_integral_Ioc
  have qr : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have endpoint :
      (∫ x in gridCell n H q q, ‖row N p c x‖^2) =
        ∫ x in gridCell n H q 0, ‖row N p c x‖^2 := by
    rw [cellEq, cellEq]
    simp only [rationalPoint, div_self qr, Nat.cast_zero, zero_div, zero_sub, zero_add]
    have shift := intervalIntegral.integral_comp_add_left (fun t => ‖row N p c t‖^2)
      1 (a := -δ) (b := δ)
    have period (x : ℝ) : row N p c (1+x) = row N p c x := by
      rw [add_comm]; exact row_periodic N p c x
    simp only [period] at shift
    simpa only [sub_eq_add_neg] using shift.symm
  have zeroLe : (∫ x in gridCell n H q 0, ‖row N p c x‖^2) ≤
      ∑ a ∈ range q, ∫ x in gridCell n H q a, ‖row N p c x‖^2 :=
    single_le_sum (f := fun a => ∫ x in gridCell n H q a, ‖row N p c x‖^2)
      (fun a _ => integral_nonneg (fun _ => sq_nonneg _)) (mem_range.mpr hq)
  rw [sum_range_succ, endpoint]
  have bound := gridInterval_energy q N p hq hc c hδ
  simp_rw [← cellEq] at bound
  change _ ≤ 4*δ * _
  linarith

/-- For a finite cover by compact cells, summing cell energies bounds the energy on the cover. -/
private theorem cover_energy {ι : Type*} [DecidableEq ι] (indices : Finset ι)
    (cell : ι → Set ℝ) (g : ℝ → ℝ) (hg : Continuous g) (hn : ∀ x, 0 ≤ g x)
    (hc : ∀ i ∈ indices, IsCompact (cell i))
    (s : Set ℝ) (hs : MeasurableSet s) (hi : IntegrableOn g s)
    (cover : ∀ x ∈ s, ∃ i ∈ indices, x ∈ cell i) :
    (∫ x in s, g x) ≤ ∑ i ∈ indices, ∫ x in cell i, g x := by
  classical
  have intcell (i) (h : i ∈ indices) : Integrable ((cell i).indicator g) := by
    exact ((hg.continuousOn.integrableOn_compact (hc i h)).integrable_indicator (hc i h).measurableSet)
  have eqsum : (∑ i ∈ indices, ∫ x in cell i, g x) = ∫ x, ∑ i ∈ indices, (cell i).indicator g x := by
    rw [integral_finsetSum indices intcell]
    exact sum_congr rfl fun i hi' => (integral_indicator (hc i hi').measurableSet).symm
  rw [← integral_indicator hs, eqsum]
  · apply integral_mono (hi.integrable_indicator hs) (integrable_finsetSum _ intcell)
    intro x
    by_cases hx : x ∈ s
    · obtain ⟨i,hi',hx'⟩ := cover x hx
      rw [Set.indicator_of_mem hx]
      calc
        g x = (cell i).indicator g x := (Set.indicator_of_mem hx' _).symm
        _ ≤ _ := single_le_sum (fun j _ => Set.indicator_nonneg (fun _ _ => hn _) _) hi'
    · rw [Set.indicator_of_notMem hx]
      exact sum_nonneg (fun j _ => Set.indicator_nonneg (fun _ _ => hn _) _)
end
end GoldbachTransitionSquare


namespace GoldbachTransitionSquare
noncomputable section
open MeasureTheory DyadicMixedB4Fourier

def wideRowFactor (n B H N : ℕ) : ℝ :=
  4 * (H:ℝ) / n * (3*B + 6*(1+2*Real.pi*N)*(1+Real.log B))

/-- Integrated concentration on the specified wide arcs, for each prime-frequency row. -/
theorem wide_row_energy (n B H N p : ℕ) (hc : ∀ q, 1 ≤ q → q ≤ B → q.Coprime p)
    (c : ℕ → ℂ) :
    (∫ x in (Set.Icc (0:ℝ) 1 ∩ wide n B H), ‖row N p c x‖^2) ≤
      wideRowFactor n B H N * ∑ j ∈ range N, ‖c j‖^2 := by
  classical
  let Q := Icc 1 B
  let grid := Q.sigma fun q => range (q+1)
  let cell := fun i : Σ _ : ℕ, ℕ => gridCell n H i.1 i.2
  let g := fun t : ℝ => ‖row N p c t‖^2
  let s := Set.Icc (0:ℝ) 1 ∩ wide n B H
  let E := ∑ j ∈ range N, ‖c j‖^2
  let K := 6*(1+2*Real.pi*N)
  have hE : 0 ≤ E := sum_nonneg fun _ _ => sq_nonneg _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hg : Continuous g := (continuous_row N p c).norm.pow 2
  have hi : IntegrableOn g s :=
    (hg.continuousOn.integrableOn_compact (isCompact_Icc (α := ℝ) (a := 0) (b := 1))).mono_set Set.inter_subset_left
  have cover : ∀ x ∈ s, ∃ i ∈ grid, x ∈ cell i := by
    intro x hx
    obtain ⟨q,a,hq,hB,ha,_,hd⟩ := hx.2
    refine ⟨⟨q,a⟩, mem_sigma.mpr ⟨mem_Icc.mpr ⟨hq,hB⟩, mem_range.mpr (Nat.lt_succ_of_le ha)⟩, ?_⟩
    change (a:ℝ)/q - (H:ℝ)/(q*n:ℝ) ≤ x ∧ x ≤ (a:ℝ)/q + (H:ℝ)/(q*n:ℝ)
    obtain ⟨h1,h2⟩ := abs_le.mp hd
    constructor <;> linarith
  have hcover := cover_energy grid cell g hg (fun _ => sq_nonneg _)
    (fun _ _ => isCompact_Icc) s (measurableSet_Icc.inter (wide_measurable ..)) hi cover
  have sumOne : ∑ q ∈ Q, (q:ℝ)⁻¹ ≤ 1+Real.log B := by
    simpa only [Q, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      using harmonic_le_one_add_log B
  have term (q : ℕ) (hq : q ∈ Q) :
      4*((H:ℝ)/(q*n:ℝ))*((3*(q:ℝ)+K)*E) = (4*(H:ℝ)/n*E)*(3+K*(q:ℝ)⁻¹) := by
    have qne : (q:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (mem_Icc.mp hq).1)
    by_cases hn : n=0
    · simp [hn]
    · have nn : (n:ℝ) ≠ 0 := by exact_mod_cast hn
      field_simp <;> ring
  calc
    _ ≤ ∑ i ∈ grid, ∫ x in cell i, g x := hcover
    _ = ∑ q ∈ Q, ∑ a ∈ range (q+1), ∫ x in gridCell n H q a, g x := by
      exact sum_sigma ..
    _ ≤ ∑ q ∈ Q, (4*(H:ℝ)/n*E)*(3+K*(q:ℝ)⁻¹) := by
      refine sum_le_sum fun q hq => ?_
      rw [← term q hq]
      exact cellMass n H N p q (mem_Icc.mp hq).1 (hc q (mem_Icc.mp hq).1 (mem_Icc.mp hq).2) c
    _ = (4*(H:ℝ)/n*E)*(3*B + K* ∑ q ∈ Q, (q:ℝ)⁻¹) := by
      rw [← mul_sum, sum_add_distrib, ← mul_sum]
      have hcard : Q.card = B := by simp [Q, Nat.card_Icc]
      rw [sum_const, hcard, nsmul_eq_mul]; ring
    _ ≤ (4*(H:ℝ)/n*E)*(3*B + K*(1+Real.log B)) := by gcongr
    _ = _ := by dsimp [wideRowFactor,K,E]; ring

end
end GoldbachTransitionSquare


namespace GoldbachTransitionSquare
noncomputable section
open MeasureTheory DyadicMixedB4Fourier

def neighbours (P : Finset ℕ) (D p : ℕ) := P.filter fun q : ℕ => |(p:ℤ)-q| ≤ D

theorem neighbours_card (P : Finset ℕ) (D p : ℕ) : (neighbours P D p).card ≤ 2*D+1 := by
  have h : (neighbours P D p).card ≤ (Icc (-(D:ℤ)) (D:ℤ)).card := by
    apply card_le_card_of_injOn (fun q : ℕ => (p:ℤ)-q)
    · intro q hq
      exact mem_Icc.mpr (abs_le.mp (mem_filter.mp hq).2)
    · intro q _ r _ he
      dsimp at he
      omega
  rw [Int.card_Icc] at h
  omega

def closePairs (P : Finset ℕ) (D : ℕ) := (P ×ˢ P).filter fun i => |(i.1:ℤ)-i.2| ≤ D

theorem closePairs_left (P : Finset ℕ) (D : ℕ) (f : ℕ → ℝ) (hf : ∀ p ∈ P, 0 ≤ f p) :
    (∑ i ∈ closePairs P D, f i.1) ≤ (2*(D:ℝ)+1) * ∑ p ∈ P, f p := by
  have hp (i : ℕ × ℕ) : i ∈ closePairs P D ↔ i.1 ∈ P ∧ i.2 ∈ neighbours P D i.1 := by
    simp [closePairs, neighbours, and_assoc]
  rw [sum_finset_product (closePairs P D) P (neighbours P D) hp, mul_sum]
  refine sum_le_sum fun p h => ?_
  simp only [sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast neighbours_card P D p) (hf p h)

theorem closePairs_right (P : Finset ℕ) (D : ℕ) (f : ℕ → ℝ) (hf : ∀ p ∈ P, 0 ≤ f p) :
    (∑ i ∈ closePairs P D, f i.2) ≤ (2*(D:ℝ)+1) * ∑ p ∈ P, f p := by
  have hp (i : ℕ × ℕ) : i ∈ closePairs P D ↔ i.2 ∈ P ∧ i.1 ∈ neighbours P D i.2 := by
    simp only [closePairs, neighbours, mem_filter, mem_product, abs_sub_comm (i.2:ℤ)]
    tauto
  rw [sum_finset_product_right (closePairs P D) P (neighbours P D) hp, mul_sum]
  refine sum_le_sum fun p h => ?_
  simp only [sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast neighbours_card P D p) (hf p h)

theorem closePairs_cross (P : Finset ℕ) (D : ℕ) (v : ℕ → ℂ) :
    (∑ i ∈ closePairs P D, ‖v i.1 * v i.2‖) ≤
      (2*(D:ℝ)+1) * ∑ p ∈ P, ‖v p‖^2 := by
  have hle : ∑ i ∈ closePairs P D, 2 * ‖v i.1 * v i.2‖ ≤
      ∑ i ∈ closePairs P D, (‖v i.1‖^2 + ‖v i.2‖^2) := by
    refine sum_le_sum fun i _ => ?_
    rw [norm_mul]
    nlinarith [sq_nonneg (‖v i.1‖ - ‖v i.2‖)]
  rw [←mul_sum, sum_add_distrib] at hle
  linarith [closePairs_left P D (fun p => ‖v p‖^2) (fun _ _ => sq_nonneg _),
    closePairs_right P D (fun p => ‖v p‖^2) (fun _ _ => sq_nonneg _)]

def pairRows (edges : Finset (ℕ × ℕ)) (N n : ℕ) (c : ℕ → ℕ → ℂ) (t : ℝ) : ℂ :=
  (∑ i ∈ edges, row N i.1 (c i.1) t * row N i.2 (c i.2) t) * mode (-(n:ℤ)) t

theorem continuous_pairRows (edges : Finset (ℕ × ℕ)) (N n : ℕ) (c : ℕ → ℕ → ℂ) :
    Continuous (pairRows edges N n c) :=
  (continuous_finsetSum _ fun i _ => (continuous_row ..).mul (continuous_row ..)).mul (continuous_mode _)

theorem closePairs_wide (P : Finset ℕ) (D n B H N : ℕ) (c : ℕ → ℕ → ℂ)
    (hp : ∀ p ∈ P, ∀ q, 1 ≤ q → q ≤ B → q.Coprime p) :
    ‖∫ t in (Set.Icc (0:ℝ) 1 ∩ wide n B H), pairRows (closePairs P D) N n c t‖ ≤
      (2*(D:ℝ)+1)*wideRowFactor n B H N * ∑ p ∈ P, ∑ j ∈ range N, ‖c p j‖^2 := by
  let s := Set.Icc (0:ℝ) 1 ∩ wide n B H
  let f := pairRows (closePairs P D) N n c
  let g := fun (p : ℕ) (t : ℝ) => ‖row N p (c p) t‖^2
  have onS {h : ℝ → ℝ} (hh : Continuous h) : IntegrableOn h s :=
    (hh.continuousOn.integrableOn_compact (isCompact_Icc (α := ℝ) (a := 0) (b := 1))).mono_set Set.inter_subset_left
  have cg (p : ℕ) : Continuous (g p) := (continuous_row ..).norm.pow 2
  have G := continuous_finsetSum P fun p _ => cg p
  have point (t : ℝ) : ‖f t‖ ≤ (2*(D:ℝ)+1) * ∑ p ∈ P, g p t := by
    dsimp only [f,pairRows]
    rw [norm_mul, mode_norm_one, mul_one]
    exact (norm_sum_le ..).trans (closePairs_cross P D (fun p => row N p (c p) t))
  calc
    _ ≤ ∫ t in s, ‖f t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in s, (2*(D:ℝ)+1) * ∑ p ∈ P, g p t :=
      integral_mono (onS (continuous_pairRows .. |>.norm)) (onS (continuous_const.mul G)) point
    _ = (2*(D:ℝ)+1) * ∑ p ∈ P, ∫ t in s, g p t := by
      rw [integral_const_mul, integral_finsetSum P (fun p _ => onS (cg p))]
    _ ≤ (2*(D:ℝ)+1) * ∑ p ∈ P, wideRowFactor n B H N * ∑ j ∈ range N, ‖c p j‖^2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_le_sum fun p hi => wide_row_energy n B H N p (hp p hi) (c p)
    _ = _ := by rw [← mul_sum, mul_assoc]

end
end GoldbachTransitionSquare


namespace GoldbachTransitionSquare
noncomputable section
open MeasureTheory DyadicMixedB4Fourier

private theorem mode_add_index (j k : ℤ) (t : ℝ) : mode j t * mode k t = mode (j+k) t := by
  unfold mode frequency
  rw [←Complex.exp_add, Int.cast_add]
  congr 1
  ring

private theorem mode_row_index (a p : ℕ) (t : ℝ) : mode a (p*t) = mode ((a*p:ℕ):ℤ) t := by
  unfold mode frequency
  congr 1
  push_cast
  ring

private theorem mode_resonance (a p b q n : ℕ) (t : ℝ) :
    mode a (p*t) * mode b (q*t) * mode (-(n:ℤ)) t =
    mode (((a*p+b*q:ℕ):ℤ)-(n:ℤ)) t := by
  rw [mode_row_index, mode_row_index, mode_add_index, mode_add_index]
  push_cast
  congr 1

private def rowIndices (edges : Finset (ℕ×ℕ)) (N : ℕ) := edges ×ˢ (range N ×ˢ range N)

private def rowCoeff (c : ℕ → ℕ → ℂ) (i : (ℕ×ℕ)×(ℕ×ℕ)) :=
  c i.1.1 i.2.1 * c i.1.2 i.2.2

private def rowIndex (i : (ℕ×ℕ)×(ℕ×ℕ)) := i.2.1*i.1.1 + i.2.2*i.1.2

private theorem pairRows_expanded (edges : Finset (ℕ×ℕ)) (N n : ℕ) (c : ℕ → ℕ → ℂ) (t : ℝ) :
    pairRows edges N n c t =
    ∑ i ∈ rowIndices edges N, rowCoeff c i * mode ((rowIndex i:ℤ)-n) t := by
  unfold pairRows rowIndices
  rw [sum_mul, sum_product]
  refine sum_congr rfl fun i _ => ?_
  unfold row
  rw [sum_mul, sum_mul, sum_product]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum, sum_mul]
  refine sum_congr rfl fun b _ => ?_
  dsimp only [rowIndex, rowCoeff, Prod.fst, Prod.snd]
  rw [← mode_resonance]
  ring

theorem full_pairRows (edges : Finset (ℕ×ℕ)) (N n : ℕ) (c : ℕ → ℕ → ℂ) :
    (∫ t in (0:ℝ)..1, pairRows edges N n c t) =
      ∑ i ∈ (rowIndices edges N).filter (fun i => rowIndex i=n), rowCoeff c i := by
  simp_rw [pairRows_expanded]
  rw [intervalIntegral.integral_finsetSum (f := fun i t => rowCoeff c i * mode ((rowIndex i:ℤ)-n) t) (fun i _ =>
    (continuous_const.mul (continuous_mode ((rowIndex i:ℤ)-n))).intervalIntegrable _ _), sum_filter]
  refine sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_const_mul, mode_integral]
  by_cases hi : rowIndex i = n
  · simp [hi]
  · have hz : (rowIndex i:ℤ)-(n:ℤ) ≠ 0 := by omega
    simp [hi,hz]

private def asRepresentation (i : (ℕ×ℕ)×(ℕ×ℕ)) : Representation :=
  ⟨i.2.1,i.2.2,i.1.1,i.1.2⟩

private theorem asRep_inj : Function.Injective asRepresentation := by
  rintro ⟨⟨p,q⟩,⟨a,b⟩⟩ ⟨⟨r,s⟩,⟨u,v⟩⟩ h
  simpa [asRepresentation, and_assoc, and_left_comm, and_comm] using h

/-- Full-circle mass on the close pairs is controlled by the number of short representations. -/
theorem closePairs_full (P : Finset ℕ) (D B n : ℕ) (c : ℕ → ℕ → ℂ)
    (hzero : ∀ p, c p 0 = 0) {T : ℝ} (hT : ∀ p ∈ P, ∀ a ≤ B, ‖c p a‖ ≤ T) :
    ‖∫ t in (0:ℝ)..1, pairRows (closePairs P D) (B+1) n c t‖ ≤
      ((B:ℝ)^2*(2*D+1))*T^2 := by
  classical
  let indices := (rowIndices (closePairs P D) (B+1)).filter (fun i => rowIndex i=n)
  let nz := indices.filter (fun i => 0 < i.2.1 ∧ 0 < i.2.2)
  have spec (i) (hi : i ∈ nz) :
      i.1 ∈ closePairs P D ∧ i.2.1 ≤ B ∧ i.2.2 ≤ B ∧ rowIndex i=n ∧ 0 < i.2.1 ∧ 0 < i.2.2 := by
    simpa [nz,indices,rowIndices,and_assoc,Nat.lt_succ_iff] using hi
  have cnt := representation_card_near (n:=n) (B:=B) (D:=D) (nz.image asRepresentation) (by
    intro r hr
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hr
    obtain ⟨hpair,ha,hb,he,hapos,hbpos⟩ := spec i hi
    exact ⟨hapos,ha,hbpos,hb,he,(mem_filter.mp hpair).2⟩)
  rw [card_image_of_injective _ asRep_inj] at cnt
  have eqsum : (∑ i ∈ indices, rowCoeff c i) = ∑ i ∈ nz, rowCoeff c i := by
    symm
    apply sum_subset (filter_subset _ _)
    intro i hi hnot
    have hz : ¬ (0 < i.2.1 ∧ 0 < i.2.2) := fun hg => hnot (mem_filter.mpr ⟨hi,hg⟩)
    rcases (show i.2.1 = 0 ∨ i.2.2 = 0 by omega) with h | h <;> simp [rowCoeff,h,hzero]
  rw [full_pairRows]
  change ‖∑ i ∈ indices, rowCoeff c i‖ ≤ _
  rw [eqsum]
  calc
    _ ≤ ∑ i ∈ nz, ‖rowCoeff c i‖ := norm_sum_le ..
    _ ≤ ∑ _i ∈ nz, T^2 := by
      refine sum_le_sum fun i hi => ?_
      obtain ⟨hep,ha,hb,_⟩ := spec i hi
      obtain ⟨hp,hq⟩ := mem_product.mp (mem_filter.mp hep).1
      rw [rowCoeff,norm_mul,pow_two]
      exact mul_le_mul (hT _ hp _ ha) (hT _ hq _ hb) (norm_nonneg _)
        ((norm_nonneg _).trans (hT _ hp _ ha))
    _ ≤ _ := by
      rw [sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast cnt) (sq_nonneg _)

end
end GoldbachTransitionSquare


namespace GoldbachTransitionSquare
noncomputable section
open MeasureTheory DyadicMixedB4Fourier

def bigPrimes (n : ℕ) := (range (n+1)).filter fun p : ℕ => n.sqrt < p ∧ p.Prime

def rowSupport (n U L B : ℕ) :=
  (bigPrimes n ×ˢ range (B+1)).filter fun (i : ℕ×ℕ) => L < i.2 ∧ U < i.1 ∧ i.2*i.1 ≤ n

private def productIndex (i : ℕ×ℕ) := i.2*i.1

private def rawCoeff (U p a : ℕ) : ℝ := lowMoebiusWeight U a * Real.log p

def primeRowCoeff (n U L B p a : ℕ) : ℂ :=
  if (p,a) ∈ rowSupport n U L B then ((rawCoeff U p a : ℝ):ℂ) else 0

private theorem supportInfo {i : ℕ×ℕ} {n U L B : ℕ} (hi : i ∈ rowSupport n U L B) :
    i.1 ∈ bigPrimes n ∧ i.2 ≤ B ∧ L < i.2 ∧ U < i.1 ∧ i.2*i.1 ≤ n := by
  simpa [rowSupport, and_assoc, Nat.lt_succ_iff] using hi

private theorem supportIndex_dvd {i : ℕ×ℕ} {n U L B : ℕ} (hi : i ∈ rowSupport n U L B) :
    0 < productIndex i ∧ productIndex i ≤ n ∧ i.2 ∣ productIndex i ∧
    productIndex i / i.2 = i.1 := by
  obtain ⟨hp,_,ha,_,hn⟩ := supportInfo hi
  have ha' : 0 < i.2 := Nat.zero_lt_of_lt ha
  have hp' := (mem_filter.mp hp).2.2.pos
  exact ⟨Nat.mul_pos ha' hp',hn,dvd_mul_right ..,Nat.mul_div_cancel_left _ ha'⟩

private theorem supportIndex_inj (n U L B : ℕ) :
    Set.InjOn productIndex (rowSupport n U L B : Set (ℕ×ℕ)) := by
  intro i hi j hj he
  obtain ⟨hm,hn,hd,heq⟩ := supportIndex_dvd hi
  obtain ⟨_,_,hj',heq'⟩ := supportIndex_dvd hj
  rw [←he] at hj' heq'
  have pi := (mem_filter.mp (supportInfo hi).1).2
  have pj := (mem_filter.mp (supportInfo hj).1).2
  rw [←heq] at pi
  rw [←heq'] at pj
  have ha := unique_large_prime_cofactor hm hn hd hj' pi.2 pj.2 pi.1 pj.1
  exact Prod.ext (by rw [←heq,ha,heq']) ha

private def coreDivs (n U L B m : ℕ) :=
  (m.divisors.filter fun a => L < a ∧ a ≤ B ∧ U < m/a).filter
    (fun a => n.sqrt < m/a ∧ (m/a).Prime)

private theorem core_sum (n U L B m : ℕ) :
    core n U L B m = ∑ a ∈ coreDivs n U L B m, rawCoeff U (m/a) a := by
  unfold core band coreDivs
  conv_rhs => rw [sum_filter]
  refine sum_congr rfl fun a _ => ?_
  by_cases hr : n.sqrt < m/a <;> by_cases hp : (m/a).Prime <;>
    simp [largePrimeWeight,primeWeight,rawCoeff,hr,hp]

private theorem divisor_to_support {n U L B m a : ℕ} (hm : m ≤ n) (ha : a ∈ coreDivs n U L B m) :
    (m/a,a) ∈ rowSupport n U L B ∧ productIndex (m/a,a)=m := by
  obtain ⟨hbase,hp⟩ := mem_filter.mp ha
  obtain ⟨had,hcond⟩ := mem_filter.mp hbase
  have heq := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors had)
  have hle := (Nat.div_le_self m a).trans hm
  refine ⟨mem_filter.mpr ⟨mem_product.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hle),hp⟩,
    mem_range.mpr (Nat.lt_succ_of_le hcond.2.1)⟩, hcond.1,hcond.2.2, ?_⟩,heq⟩
  exact heq.le.trans hm

private theorem core_on_product {n U L B : ℕ} {i : ℕ×ℕ} (hi : i ∈ rowSupport n U L B) :
    core n U L B (productIndex i) = rawCoeff U i.1 i.2 := by
  obtain ⟨hp,hB,hL,hU,_⟩ := supportInfo hi
  obtain ⟨hm,hn,hd,heq⟩ := supportIndex_dvd hi
  have hp' := (mem_filter.mp hp).2
  have ha : i.2 ∈ coreDivs n U L B (productIndex i) := by
    apply mem_filter.mpr
    rw [heq]
    exact ⟨mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd,hm.ne'⟩, hL,hB,by rwa [heq]⟩,hp'⟩
  rw [core_sum, sum_eq_single_of_mem i.2 ha, heq]
  intro a ha' hne
  obtain ⟨hs,he⟩ := divisor_to_support hn ha'
  have same := supportIndex_inj n U L B hs hi he
  exact (hne (congrArg Prod.snd same)).elim

private theorem core_off_product {n U L B m : ℕ} (hm : m ≤ n)
    (hoff : m ∉ (rowSupport n U L B).image productIndex) : core n U L B m = 0 := by
  rw [core_sum]
  refine sum_eq_zero fun a ha => ?_
  obtain ⟨hs,he⟩ := divisor_to_support hm ha
  exact (hoff (mem_image.mpr ⟨_,hs,he⟩)).elim

private theorem phase_eq_mode_nat (m : ℕ) (t : ℝ) : phase (m*t) = mode m t := by
  unfold phase mode frequency
  congr 1
  push_cast
  ring

theorem core_rows (n U L B : ℕ) (t : ℝ) :
    fourierSum n (core n U L B) t =
    ∑ p ∈ bigPrimes n, row (B+1) p (primeRowCoeff n U L B p) t := by
  classical
  let S := rowSupport n U L B
  let f (m:ℕ) := ((core n U L B m : ℝ):ℂ) * phase (m*t)
  have subset : S.image productIndex ⊆ range (n+1) := by
    intro m hm
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hm
    exact mem_range.mpr (Nat.lt_succ_of_le (supportIndex_dvd hi).2.1)
  calc
    _ = ∑ m ∈ S.image productIndex, f m := by
      symm
      apply sum_subset subset
      intro m hm hoff
      simp [f,core_off_product (Nat.le_of_lt_succ (mem_range.mp hm)) hoff]
    _ = ∑ i ∈ S, f (productIndex i) := sum_image (supportIndex_inj n U L B)
    _ = ∑ i ∈ S, ((rawCoeff U i.1 i.2:ℝ):ℂ) * mode i.2 (i.1*t) := by
      refine sum_congr rfl fun i hi => ?_
      unfold f
      rw [core_on_product hi,phase_eq_mode_nat,mode_row_index]
      rfl
    _ = ∑ i ∈ bigPrimes n ×ˢ range (B+1), primeRowCoeff n U L B i.1 i.2 * mode i.2 (i.1*t) := by
      rw [←sum_filter_add_sum_filter_not (bigPrimes n ×ˢ range (B+1)) (fun i => i ∈ S)]
      have ident : ((bigPrimes n ×ˢ range (B+1)).filter (fun i => i ∈ S)) = S :=
        filter_mem_eq_inter.trans (inter_eq_right.mpr (filter_subset _ _))
      rw [ident, sum_eq_zero (s := (bigPrimes n ×ˢ range (B+1)).filter fun i => i ∉ S), add_zero]
      · exact sum_congr rfl fun i hi => by simp [primeRowCoeff,show (i.1,i.2) ∈ rowSupport n U L B from hi]
      · intro i hi
        simp [primeRowCoeff,show (i.1,i.2) ∉ rowSupport n U L B from (mem_filter.mp hi).2]
    _ = _ := sum_product ..
end
end GoldbachTransitionSquare


namespace GoldbachTransitionSquare
noncomputable section
open MeasureTheory DyadicMixedB4Fourier

def arcRows (s : Set ℝ) (edges : Finset (ℕ×ℕ)) (N n : ℕ) (c : ℕ → ℕ → ℂ) : ℂ :=
  ∫ t in (Set.Icc (0:ℝ) 1 ∩ s), pairRows edges N n c t

private theorem arcIntegrable (s : Set ℝ) (edges : Finset (ℕ×ℕ)) (N n : ℕ) (c : ℕ → ℕ → ℂ) :
    IntegrableOn (pairRows edges N n c) (Set.Icc (0:ℝ) 1 ∩ s) :=
  ((continuous_pairRows ..).continuousOn.integrableOn_compact isCompact_Icc).mono_set Set.inter_subset_left

theorem arcRows_partition (s : Set ℝ) (hs : MeasurableSet s) (edges : Finset (ℕ×ℕ))
    (N n : ℕ) (c : ℕ → ℕ → ℂ) :
    arcRows sᶜ edges N n c + arcRows s edges N n c = ∫ t in (0:ℝ)..1, pairRows edges N n c t := by
  let I := Set.Icc (0:ℝ) 1
  have disj : Disjoint (I ∩ sᶜ) (I ∩ s) := Set.disjoint_left.mpr fun _ h1 h2 => h1.2 h2.2
  have union : (I ∩ sᶜ) ∪ (I ∩ s) = I := by ext x; simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_compl_iff]; tauto
  change (∫ t in I ∩ sᶜ, _) + (∫ t in I ∩ s, _) = _
  rw [←setIntegral_union disj (measurableSet_Icc.inter hs) (arcIntegrable ..) (arcIntegrable ..),union]
  exact integral_Icc_eq_integral_Ioc.trans (intervalIntegral.integral_of_le zero_le_one).symm

def farPairs (P : Finset ℕ) (D : ℕ) := (P ×ˢ P) \ closePairs P D

theorem arcRows_far_close (s : Set ℝ) (P : Finset ℕ) (D N n : ℕ) (c : ℕ → ℕ → ℂ) :
    arcRows s (P ×ˢ P) N n c - arcRows s (farPairs P D) N n c =
    arcRows s (closePairs P D) N n c := by
  have hsubset : closePairs P D ⊆ P ×ˢ P := filter_subset _ _
  have point (t : ℝ) : pairRows (P ×ˢ P) N n c t =
      pairRows (farPairs P D) N n c t + pairRows (closePairs P D) N n c t := by
    unfold pairRows farPairs
    rw [← add_mul,sum_sdiff hsubset]
  change _ - _ = _
  apply sub_eq_iff_eq_add.mpr
  unfold arcRows
  simp_rw [point]
  rw [integral_add (arcIntegrable ..) (arcIntegrable ..),add_comm]

private theorem phase_eq_mode_neg (n : ℕ) (t : ℝ) : phase (-(n:ℝ)*t) = mode (-(n:ℤ)) t := by
  unfold phase mode frequency
  congr 1
  push_cast
  ring

theorem core_square_rows (s : Set ℝ) (hs : MeasurableSet s) (n U L B : ℕ) :
    pairIntegral s n (core n U L B) (core n U L B) =
    arcRows s (bigPrimes n ×ˢ bigPrimes n) (B+1) n (primeRowCoeff n U L B) := by
  have point (t : ℝ) :
      fourierSum n (core n U L B) t * fourierSum n (core n U L B) t * phase (-(n:ℝ)*t) =
      pairRows (bigPrimes n ×ˢ bigPrimes n) (B+1) n (primeRowCoeff n U L B) t := by
    rw [core_rows,phase_eq_mode_neg]
    unfold pairRows
    rw [sum_product, sum_mul]
    congr 1
    exact sum_congr rfl fun _ _ => mul_sum ..
  unfold pairIntegral arcRows
  simp_rw [point]
  rw [intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc,integral_indicator hs,
    Measure.restrict_restrict hs,Set.inter_comm]

private theorem support_card_le (n U L B : ℕ) : (rowSupport n U L B).card ≤ n+1 := by
  have bound (i) (hi : i ∈ rowSupport n U L B) : productIndex i ∈ range (n+1) :=
    mem_range.mpr (Nat.lt_succ_of_le (supportIndex_dvd hi).2.1)
  simpa using card_le_card_of_injOn productIndex bound (supportIndex_inj n U L B)

private theorem actualRow_norm (n U L B p a : ℕ) {T : ℝ} (hT : 0 ≤ T)
    (h : ∀ i ∈ rowSupport n U L B, |rawCoeff U i.1 i.2| ≤ T) :
    ‖primeRowCoeff n U L B p a‖ ≤ T := by
  by_cases hi : (p,a) ∈ rowSupport n U L B
  · simpa [primeRowCoeff,hi,Real.norm_eq_abs] using h (p,a) hi
  · simpa [primeRowCoeff,hi] using hT

private theorem primeRow_zero (n U L B p : ℕ) : primeRowCoeff n U L B p 0 = 0 := by
  simp [primeRowCoeff,rowSupport]

private theorem actualRow_energy (n U L B : ℕ) {T : ℝ} (hT : 0 ≤ T)
    (h : ∀ i ∈ rowSupport n U L B, |rawCoeff U i.1 i.2| ≤ T) :
    (∑ p ∈ bigPrimes n, ∑ a ∈ range (B+1), ‖primeRowCoeff n U L B p a‖^2) ≤
    ((n:ℝ)+1)*T^2 := by
  let S := rowSupport n U L B
  let V (i : ℕ×ℕ) := ‖primeRowCoeff n U L B i.1 i.2‖^2
  have eqs : (∑ i ∈ S, V i) = ∑ i ∈ bigPrimes n ×ˢ range (B+1), V i := by
    apply sum_subset (filter_subset _ _)
    intro i _ hn
    have hn' : (i.1,i.2) ∉ rowSupport n U L B := hn
    simp [V,primeRowCoeff,hn']
  calc
    _ = ∑ i ∈ bigPrimes n ×ˢ range (B+1), V i := (sum_product ..).symm
    _ = ∑ i ∈ S, V i := eqs.symm
    _ ≤ ∑ _i ∈ S, T^2 := sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (actualRow_norm n U L B i.1 i.2 hT h) 2
    _ ≤ _ := by
      rw [sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast support_card_le n U L B) (sq_nonneg _)

end
end GoldbachTransitionSquare


namespace GoldbachTransitionSquare
noncomputable section
open MeasureTheory DyadicMixedB4Fourier Filter Topology

def arcHeight (n : ℕ) := 256 * cutoffB n * (Nat.log 2 (n+2))^2

def farValue (n : ℕ) : ℂ := arcRows (deep n) (farPairs (bigPrimes n) (cutoffL n))
  (cutoffB n + 1) n (primeRowCoeff n (cutoffU n) (cutoffL n) (cutoffB n))

private theorem cubeCut_le_sqrt {n : ℕ} (hn : 1 ≤ n) : cutoffB n ≤ n.sqrt := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have h : (cutoffB n:ℝ) ≤ Real.sqrt n := by
    calc
      _ ≤ (n:ℝ)^(1/3:ℝ) := Nat.floor_le (by positivity)
      _ ≤ Real.sqrt n := by rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hn' (by norm_num)
  apply Nat.le_sqrt'.mpr
  have hh := pow_le_pow_left₀ (Nat.cast_nonneg (cutoffB n) (α := ℝ)) h 2
  rw [Real.sq_sqrt (Nat.cast_nonneg n)] at hh
  exact_mod_cast hh

private theorem bigPrime_coprime {n p q : ℕ} (hn : 1 ≤ n) (hp : p ∈ bigPrimes n)
    (hq : 1 ≤ q) (hB : q ≤ cutoffB n) : q.Coprime p := by
  obtain ⟨_,hr,hpr⟩ := mem_filter.mp hp
  exact (hpr.coprime_iff_not_dvd.mpr (fun h => (not_lt_of_ge (Nat.le_of_dvd hq h))
    (lt_of_le_of_lt (hB.trans (cubeCut_le_sqrt hn)) hr))).symm

private theorem wideRowFactor_nonneg (n B H N : ℕ) (hB : 1 ≤ B) : 0 ≤ wideRowFactor n B H N := by
  have hl := Real.log_nonneg (show (1:ℝ) ≤ B by exact_mod_cast hB)
  unfold wideRowFactor
  positivity

theorem core_far_bound (n : ℕ) (hn : 1 ≤ n) {T : ℝ} (hT : 0 ≤ T)
    (h : ∀ i ∈ rowSupport n (cutoffU n) (cutoffL n) (cutoffB n),
      |rawCoeff (cutoffU n) i.1 i.2| ≤ T) :
    ‖coreValue n - farValue n‖ ≤
      ((cutoffB n:ℝ)^2*(2*(cutoffL n:ℝ)+1))*T^2 +
      (2*(cutoffL n:ℝ)+1)*wideRowFactor n (cutoffB n) (arcHeight n) (cutoffB n+1)*(((n:ℝ)+1)*T^2) := by
  let B := cutoffB n
  let D := cutoffL n
  let H := arcHeight n
  let P := bigPrimes n
  let c := primeRowCoeff n (cutoffU n) D B
  let edges := closePairs P D
  have hB1 : 1 ≤ B := (Nat.one_le_floor_iff _).mpr
    (Real.one_le_rpow (by exact_mod_cast hn) (by norm_num))
  have energy := actualRow_energy n (cutoffU n) D B hT h
  have w := closePairs_wide P D n B H (B+1) c (fun _ hp _ hq hb => bigPrime_coprime hn hp hq hb)
  have w' := w.trans (mul_le_mul_of_nonneg_left energy
    (mul_nonneg (by positivity) (wideRowFactor_nonneg _ _ _ _ hB1)))
  have f := closePairs_full P D B n c (fun p => primeRow_zero _ _ _ _ p) (fun p _ a _ => actualRow_norm _ _ _ _ p a hT h)
  have eqall : coreValue n - farValue n = arcRows (deep n) edges (B+1) n c := by
    unfold coreValue farValue
    rw [core_square_rows (deep n) (wide_measurable ..).compl]
    exact arcRows_far_close ..
  have e := arcRows_partition (wide n B H) (wide_measurable ..) edges (B+1) n c
  have e' : arcRows (deep n) edges (B+1) n c =
      (∫ t in (0:ℝ)..1, pairRows edges (B+1) n c t) - arcRows (wide n B H) edges (B+1) n c :=
    eq_sub_iff_add_eq.mpr e
  rw [eqall,e']
  exact (norm_sub_le ..).trans (add_le_add f w')

end
end GoldbachTransitionSquare


namespace GoldbachTransitionSquare
noncomputable section
open MeasureTheory Filter Topology

/-- Binary logarithm comparison used in the mixed-band proof (#2492). -/
private theorem log2_le_four_log (n : ℕ) (hn : 2 ≤ n) : (Nat.log 2 (n + 2) : ℝ) ≤ 4 * Real.log n := by
  have hb := Real.natLog_le_logb (n + 2) 2
  rw [Real.logb] at hb
  push_cast at hb
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hx : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have square : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - 2 by linarith) (show 0 ≤ (n : ℝ) + 1 by positivity)]
  have logarithm := Real.log_le_log (by positivity : 0 < (n : ℝ) + 2) square
  rw [Real.log_pow] at logarithm
  norm_num at logarithm
  have divided := (le_div_iff₀ (by linarith : 0 < Real.log 2)).mp hb
  have multiplied := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (Nat.log 2 (n + 2)) : (0 : ℝ) ≤ _)
  linarith only [logarithm, divided, multiplied]

set_option maxHeartbeats 1400000 in
private theorem numeric_close {X R B D n H logB : ℝ} (hx : 1 ≤ X) (hr : 1 ≤ R) (hn : 1 ≤ n)
    (hb0 : 0 ≤ B) (hd0 : 0 ≤ D) (hl0 : 0 ≤ logB) (hh0 : 0 ≤ H)
    (hb : B ≤ X^43) (hd : D ≤ X^32) (hl : logB ≤ R*X) (hh : H ≤ 256*R^2*X^45) :
    B^2*(2*D+1)*(R*X)^4 +
      (2*D+1)*(4*H/n*(3*B+6*(1+2*Real.pi*(B+1))*(1+logB)))*((n+1)*(R*X)^4)
    ≤ 2000000*R^7*X^125 := by
  have hx0 := zero_le_one.trans hx
  have hr0 := zero_le_one.trans hr
  have hn0 := zero_lt_one.trans_le hn
  have hx32 : 1 ≤ X^32 := one_le_pow₀ hx
  have hx43 : 1 ≤ X^43 := one_le_pow₀ hx
  have hdx : 2*D+1 ≤ 3*X^32 := by linarith
  have hb1 : B+1 ≤ 2*X^43 := by linarith
  have hl1 : 1+logB ≤ 2*(R*X) := by linarith [one_le_mul_of_one_le_of_one_le hr hx]
  have hbpi : 1+2*Real.pi*(B+1) ≤ 17*X^43 := by
    have t : 2*Real.pi*(B+1) ≤ 2*4*(2*X^43) := by gcongr; exact Real.pi_lt_four.le
    linarith
  have hshape : 3*B+6*(1+2*Real.pi*(B+1))*(1+logB) ≤ 300*R*X^44 := by
    have hbx : B ≤ R*X^44 := calc
      _ ≤ X^43 := hb
      _ ≤ X^44 := pow_le_pow_right₀ hx (by decide)
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hr
    calc
      _ ≤ 3*(R*X^44)+6*(17*X^43)*(2*(R*X)) := by gcongr
      _ ≤ _ := by nlinarith only [show 0 ≤ R*X^44 by positivity]
  have hratio : (n+1)/n ≤ 2 := (div_le_iff₀ hn0).mpr (by linarith)
  have head : B^2*(2*D+1)*(R*X)^4 ≤ 3*R^7*X^125 := by
    calc
      _ ≤ (X^43)^2*(3*X^32)*(R*X)^4 := by gcongr
      _ = 3*R^4*X^122 := by ring
      _ ≤ _ := by gcongr <;> norm_num
  have tail : (2*D+1)*(4*H/n*(3*B+6*(1+2*Real.pi*(B+1))*(1+logB)))*((n+1)*(R*X)^4)
      ≤ 1843200*R^7*X^125 := by
    calc
      _ = (2*D+1)*(4*H)*(3*B+6*(1+2*Real.pi*(B+1))*(1+logB))*((n+1)/n)*(R*X)^4 := by ring
      _ ≤ (3*X^32)*(4*(256*R^2*X^45))*(300*R*X^44)*2*(R*X)^4 := by gcongr
      _ = _ := by ring
  nlinarith only [head,tail, show 0 ≤ R^7*X^125 by positivity]

set_option maxHeartbeats 1400000 in
theorem close_power_saving :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 2 ≤ n → ‖coreValue n - farValue n‖ ≤ K*(n:ℝ)^(125/128:ℝ) := by
  obtain ⟨C,hC,hdiv⟩ := divisor_envelope
  let R := max C 512
  have hR : 1 ≤ R := hC.trans (le_max_left ..)
  refine ⟨2000000*R^7,by positivity,?_⟩
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn1
  let X := (n:ℝ)^(1/128:ℝ)
  have hX : 1 ≤ X := Real.one_le_rpow hnR (by norm_num)
  have hx0 := zero_le_one.trans hX
  have hr0 := zero_le_one.trans hR
  have hp (k : ℕ) : X^k = (n:ℝ)^((k:ℝ)/128) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]; congr 1; ring
  have hl : Real.log n ≤ 128*X := by
    have h := Real.log_le_rpow_div (x:=(n:ℝ)) (Nat.cast_nonneg _) (by norm_num : (0:ℝ)<1/128)
    calc
      _ ≤ X/(1/128:ℝ) := h
      _ = _ := by ring
  have hlog : Real.log n ≤ R*X := hl.trans (mul_le_mul_of_nonneg_right (by dsimp [R]; linarith [le_max_right C 512]) hx0)
  have hb : (cutoffB n:ℝ) ≤ X^43 := by
    rw [hp]; exact (Nat.floor_le (by positivity : 0 ≤ (n:ℝ)^(1/3:ℝ))).trans
      (Real.rpow_le_rpow_of_exponent_le hnR (by norm_num))
  have hd : (cutoffL n:ℝ) ≤ X^32 := by
    rw [hp]; norm_num; exact Nat.floor_le (by positivity)
  have hb1 : 1 ≤ cutoffB n := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hnR (by norm_num))
  have hbn := (cubeCut_le_sqrt hn1).trans (Nat.sqrt_le_self n)
  have hlogb0 := Real.log_nonneg (show (1:ℝ) ≤ cutoffB n by exact_mod_cast hb1)
  have hlogb : Real.log (cutoffB n) ≤ R*X :=
    (Real.log_le_log (by exact_mod_cast (show 0 < cutoffB n from hb1)) (by exact_mod_cast hbn)).trans hlog
  have hlog2 : (Nat.log 2 (n+2):ℝ) ≤ R*X := by
    have hb2 := log2_le_four_log n hn
    have : 512*X ≤ R*X := mul_le_mul_of_nonneg_right (le_max_right ..) hx0
    linarith
  have hh : (arcHeight n:ℝ) ≤ 256*R^2*X^45 := by
    unfold arcHeight
    push_cast
    calc
      _ ≤ 256*(X^43)*(R*X)^2 := by gcongr
      _ = _ := by ring
  have weights (i : ℕ×ℕ) (hi : i ∈ rowSupport n (cutoffU n) (cutoffL n) (cutoffB n)) :
      |rawCoeff (cutoffU n) i.1 i.2| ≤ (R*X)^2 := by
    obtain ⟨hp',hB,_,_,_⟩ := supportInfo hi
    obtain ⟨hp,_,hprime⟩ := mem_filter.mp hp'
    have hdv := (hdiv n i.2 (hB.trans hbn)).trans
      (mul_le_mul_of_nonneg_right (show C ≤ R from le_max_left ..) hx0)
    have p1 : i.1 ≤ n := Nat.le_of_lt_succ (mem_range.mp hp)
    have hplog := Real.log_le_log (by exact_mod_cast hprime.pos : (0:ℝ) < i.1)
      (by exact_mod_cast p1 : (i.1:ℝ) ≤ n)
    rw [rawCoeff,abs_mul,abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le)),pow_two]
    exact mul_le_mul ((abs_lowMoebiusWeight_le ..).trans hdv) (hplog.trans hlog)
      (Real.log_nonneg (by exact_mod_cast hprime.one_le)) (mul_nonneg hr0 hx0)
  have h := core_far_bound n hn1 (sq_nonneg _) weights
  have num := numeric_close hX hR hnR (Nat.cast_nonneg _) (Nat.cast_nonneg _) hlogb0
    (Nat.cast_nonneg _) hb hd hlogb hh
  unfold wideRowFactor at h
  push_cast at h
  have last : X^125 = (n:ℝ)^(125/128:ℝ) := by simpa using hp 125
  rw [←last]
  apply h.trans
  convert num using 1 <;> ring

end
end GoldbachTransitionSquare


namespace GoldbachTransitionSquare
noncomputable section
open Filter Topology

private theorem close_eventually (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ‖coreValue n - farValue n‖ ≤ e*(n:ℝ) := by
  obtain ⟨K,_,hK⟩ := close_power_saving
  have tend : Tendsto (fun n : ℕ => (n:ℝ)^(-(3/128):ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<3/128)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have ht : Tendsto (fun n : ℕ => K*(n:ℝ)^(-(3/128):ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x:=K)).mul tend
  filter_upwards [eventually_ge_atTop 2, ht.eventually_lt_const he] with n hn hsmall
  have hpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  refine (hK n hn).trans ?_
  calc
    _ = (K*(n:ℝ)^(-(3/128):ℝ))*(n:ℝ) := by
      rw [mul_assoc, show (125/128:ℝ) = -(3/128:ℝ)+1 by norm_num,Real.rpow_add hpos,Real.rpow_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall.le hpos.le

theorem core_iff_far : smallEven coreValue ↔ smallEven farValue := by
  constructor
  · apply smallEven_transfer
    intro e he
    simpa only [norm_sub_rev] using close_eventually e he
  · exact smallEven_transfer close_eventually

theorem full_iff_far : smallEven fullValue ↔ smallEven farValue :=
  full_iff_large_prime_cofactors.trans core_iff_far

end
end GoldbachTransitionSquare


namespace GoldbachTransitionSquare
noncomputable section
open MeasureTheory DyadicMixedB4Fourier

/-- The short factor on the p-side is uniquely determined modulo the other prime. -/
def inverseResidue (n p q : ℕ) : ℕ := ((n : ZMod q) * (p : ZMod q)⁻¹).val

def partnerFactor (n p q : ℕ) := (n - inverseResidue n p q * p) / q

theorem resonance_inverse {n p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (ha : a < q) (hsum : a*p+b*q=n) :
    a = inverseResidue n p q ∧ b = partnerFactor n p q := by
  letI : Fact q.Prime := ⟨hq⟩
  have hnz : (p : ZMod q) ≠ 0 := fun hz => hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp
    ((ZMod.natCast_eq_zero_iff p q).mp hz)).symm
  have hm : (a:ZMod q)*(p:ZMod q) = (n:ZMod q) := by
    have t := congrArg (fun m : ℕ => (m:ZMod q)) hsum
    simpa only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,mul_zero,add_zero] using t
  have hz : (a:ZMod q) = (n:ZMod q)*(p:ZMod q)⁻¹ := by
    rw [←hm,mul_assoc,mul_inv_cancel₀ hnz,mul_one]
  have har : a = inverseResidue n p q := by
    rw [← ZMod.val_natCast_of_lt ha]
    exact congrArg ZMod.val hz
  refine ⟨har,?_⟩
  unfold partnerFactor
  rw [←har,←hsum,Nat.add_sub_cancel_left,Nat.mul_div_cancel _ hq.pos]

def inversePair (n B : ℕ) (c : ℕ → ℕ → ℂ) (p q : ℕ) : ℂ :=
  let a := inverseResidue n p q
  let b := partnerFactor n p q
  if a ≤ B ∧ b ≤ B ∧ a*p+b*q=n then c p a * c q b else 0

private theorem one_row_residue {n B p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hB : B < q) (c : ℕ → ℕ → ℂ) :
    (∑ i ∈ range (B+1) ×ˢ range (B+1), if i.1*p+i.2*q=n then c p i.1 * c q i.2 else 0)
    = inversePair n B c p q := by
  classical
  let a := inverseResidue n p q
  let b := partnerFactor n p q
  let F : Finset (ℕ×ℕ) := (range (B+1) ×ˢ range (B+1)).filter fun x => x.1*p+x.2*q=n
  have uniq {i : ℕ×ℕ} (h : i ∈ F) : i = (a,b) := by
    obtain ⟨hm,hs⟩ := mem_filter.mp h
    have hi : i.1 ≤ B := Nat.le_of_lt_succ (mem_range.mp (mem_product.mp hm).1)
    obtain ⟨h1,h2⟩ := resonance_inverse hp hq hne (hi.trans_lt hB) hs
    exact Prod.ext h1 h2
  change _ = if a ≤ B ∧ b ≤ B ∧ a*p+b*q=n then _ else _
  rw [←sum_filter]
  change (∑ i ∈ F, c p i.1 * c q i.2) = _
  by_cases h : a ≤ B ∧ b ≤ B ∧ a*p+b*q=n
  · rw [if_pos h]
    have hm : (a,b) ∈ F := mem_filter.mpr ⟨mem_product.mpr
      ⟨mem_range.mpr (Nat.lt_succ_of_le h.1),mem_range.mpr (Nat.lt_succ_of_le h.2.1)⟩,h.2.2⟩
    rw [sum_eq_single_of_mem (a,b) hm (fun i hi hne' => (hne' (uniq hi)).elim)]
  · rw [if_neg h]
    exact sum_eq_zero fun i hi => by
      obtain rfl := uniq hi
      obtain ⟨hm,hs⟩ := mem_filter.mp hi
      exact (h ⟨Nat.le_of_lt_succ (mem_range.mp (mem_product.mp hm).1),
        Nat.le_of_lt_succ (mem_range.mp (mem_product.mp hm).2),hs⟩).elim

private theorem far_info {n D : ℕ} {i : ℕ×ℕ} (hi : i ∈ farPairs (bigPrimes n) D) :
    i.1 ∈ bigPrimes n ∧ i.2 ∈ bigPrimes n ∧ i.1 ≠ i.2 := by
  obtain ⟨hm,hout⟩ := mem_sdiff.mp hi
  obtain ⟨hp,hq⟩ := mem_product.mp hm
  refine ⟨hp,hq,fun eq => hout (mem_filter.mpr ⟨hm,?_⟩)⟩
  simp [eq]

def inverseTotal (n : ℕ) : ℂ :=
  ∑ i ∈ farPairs (bigPrimes n) (cutoffL n),
    inversePair n (cutoffB n) (primeRowCoeff n (cutoffU n) (cutoffL n) (cutoffB n)) i.1 i.2

def wideFar (n : ℕ) : ℂ :=
  arcRows (wide n (cutoffB n) (arcHeight n)) (farPairs (bigPrimes n) (cutoffL n))
    (cutoffB n + 1) n (primeRowCoeff n (cutoffU n) (cutoffL n) (cutoffB n))

theorem far_eq_inverse_discrepancy (n : ℕ) (hn : 1 ≤ n) :
    farValue n = inverseTotal n - wideFar n := by
  let B := cutoffB n
  let D := cutoffL n
  let c := primeRowCoeff n (cutoffU n) D B
  let edges := farPairs (bigPrimes n) D
  have he : (∫ t in (0:ℝ)..1, pairRows edges (B+1) n c t) = inverseTotal n := by
    rw [full_pairRows,sum_filter]
    unfold rowIndices
    rw [sum_product]
    apply sum_congr rfl
    intro i hi
    obtain ⟨hp,hq,hne⟩ := far_info hi
    exact one_row_residue (mem_filter.mp hp).2.2 (mem_filter.mp hq).2.2 hne
      ((cubeCut_le_sqrt hn).trans_lt (mem_filter.mp hq).2.1) c
  exact eq_sub_iff_add_eq.mpr ((arcRows_partition _ (wide_measurable ..) edges (B+1) n c).trans he)

/-- The project target now asks for cancellation of the inverse-residue sum
    against its wide-arc average over distant prime pairs. -/
theorem full_iff_inverse_discrepancy :
    smallEven fullValue ↔ smallEven (fun n => inverseTotal n - wideFar n) := by
  rw [full_iff_far]
  have transform {f g : ℕ → ℂ} (h : ∀ n, 1 ≤ n → f n = g n) : smallEven f → smallEven g := by
    intro hf e he
    obtain ⟨N, hN⟩ := hf e he
    refine ⟨max 1 N, fun n hn heven => ?_⟩
    rw [←h n ((le_max_left ..).trans hn)]
    exact hN n ((le_max_right ..).trans hn) heven
  exact ⟨transform (fun n hn => far_eq_inverse_discrepancy n hn),
    transform (fun n hn => (far_eq_inverse_discrepancy n hn).symm)⟩
end
end GoldbachTransitionSquare


namespace GoldbachTransitionSquare
noncomputable section
open MeasureTheory DyadicMixedB4Fourier

private theorem twice_cubeCut {n : ℕ} (hn : 64 ≤ n) : 2*cutoffB n ≤ n.sqrt := by
  have hB : (cutoffB n:ℝ) ≤ (n:ℝ)^(1/3:ℝ) := Nat.floor_le (by positivity)
  have hcube : cutoffB n ^ 3 ≤ n := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg (cutoffB n) (α:=ℝ)) hB 3
    have hrt : ((n:ℝ)^(1/3:ℝ))^3 = n := by
      simpa only [one_div,Nat.cast_ofNat] using Real.rpow_inv_natCast_pow (Nat.cast_nonneg n) (by decide : (3:ℕ) ≠ 0)
    rw [hrt] at h
    exact_mod_cast h
  have four : 4 ≤ cutoffB n := by
    apply Nat.le_floor
    have h64 : ((4:ℝ)^3)^((3:ℝ)⁻¹) = 4 := by
      simpa using Real.pow_rpow_inv_natCast (by norm_num : (0:ℝ)≤4) (by decide : (3:ℕ)≠0)
    have hh : (4:ℝ)^3 ≤ n := by norm_num; exact_mod_cast hn
    norm_num only [Nat.cast_ofNat]
    calc
      (4:ℝ) = _ := h64.symm
      _ ≤ _ := by rw [one_div]; exact Real.rpow_le_rpow (by norm_num) hh (by positivity)
  apply Nat.le_sqrt'.mpr
  calc
    (2*cutoffB n)^2 = (cutoffB n)^2 * 4 := by ring
    _ ≤ (cutoffB n)^2 * cutoffB n := Nat.mul_le_mul_left _ four
    _ = _ := by ring
    _ ≤ _ := hcube

private theorem inverse_mod {n p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    inverseResidue n p q * p ≡ n [MOD q] := by
  letI : Fact q.Prime := ⟨hq⟩
  have hpn : (p:ZMod q) ≠ 0 := fun hz => hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp
    ((ZMod.natCast_eq_zero_iff p q).mp hz)).symm
  apply (ZMod.natCast_eq_natCast_iff ..).mp
  rw [Nat.cast_mul,inverseResidue,ZMod.natCast_zmod_val,mul_assoc,inv_mul_cancel₀ hpn,mul_one]

theorem inverse_reciprocity {n p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    inverseResidue n p q * p + inverseResidue n q p * q ≡ n [MOD p*q] := by
  have cp : p.Coprime q := hp.coprime_iff_not_dvd.mpr (fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h))
  apply (Nat.modEq_and_modEq_iff_modEq_mul cp).mp
  constructor
  · have h0 : inverseResidue n p q * p ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left ..)
    simpa using h0.add (inverse_mod hq hp hpq.symm)
  · have h0 : inverseResidue n q p * q ≡ 0 [MOD q] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left ..)
    simpa using (inverse_mod hp hq hpq).add h0

private theorem short_pair_forces_eq {n p q B : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hn : n < p*q) (hbq : 2*B < q) (hbp : 2*B < p)
    (ha : inverseResidue n p q ≤ B) (hb : inverseResidue n q p ≤ B) :
    inverseResidue n p q*p + inverseResidue n q p*q = n := by
  let r := inverseResidue n p q
  let s := inverseResidue n q p
  have hr : 2*r < q := lt_of_le_of_lt (Nat.mul_le_mul_left _ ha) hbq
  have hs : 2*s < p := lt_of_le_of_lt (Nat.mul_le_mul_left _ hb) hbp
  have hl : r*p+s*q < p*q := by
    have h1 := Nat.mul_lt_mul_of_pos_right hr hp.pos
    have h2 := Nat.mul_lt_mul_of_pos_right hs hq.pos
    nlinarith
  have h := inverse_reciprocity (n:=n) hp hq hpq
  change (r*p+s*q) % (p*q) = n % (p*q) at h
  rwa [Nat.mod_eq_of_lt hl,Nat.mod_eq_of_lt hn] at h

private theorem inversePair_symmetric {n B p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hn : n < p*q) (hbq : 2*B < q) (hbp : 2*B < p)
    (c : ℕ → ℕ → ℂ) (h0 : ∀ r a, B < a → c r a = 0) :
    inversePair n B c p q = c p (inverseResidue n p q) * c q (inverseResidue n q p) := by
  let a := inverseResidue n p q
  let b := inverseResidue n q p
  let b' := partnerFactor n p q
  change (if a ≤ B ∧ b' ≤ B ∧ a*p+b'*q=n then c p a * c q b' else 0) = c p a * c q b
  by_cases h : a ≤ B ∧ b' ≤ B ∧ a*p+b'*q=n
  · rw [if_pos h]
    have hb := (resonance_inverse hq hp hpq.symm (show b' < p by omega)
      (by rw [add_comm]; exact h.2.2 : b'*q+a*p=n)).1
    rw [show b'=b from hb]
  · rw [if_neg h]
    by_cases ha : a ≤ B
    · by_cases hb : b ≤ B
      · have he := short_pair_forces_eq hp hq hpq hn hbq hbp ha hb
        have hb' := (resonance_inverse hp hq hpq (show a < q by omega) he).2
        exact (h ⟨ha,by rwa [←show b=b' from hb'],by rwa [←show b=b' from hb']⟩).elim
      · rw [h0 q b (by omega),mul_zero]
    · rw [h0 p a (by omega),zero_mul]

def reciprocalTotal (n : ℕ) : ℂ :=
  let c := primeRowCoeff n (cutoffU n) (cutoffL n) (cutoffB n)
  ∑ i ∈ farPairs (bigPrimes n) (cutoffL n),
    c i.1 (inverseResidue n i.1 i.2) * c i.2 (inverseResidue n i.2 i.1)

theorem inverse_eq_reciprocal (n : ℕ) (hn : 64 ≤ n) : inverseTotal n = reciprocalTotal n := by
  apply sum_congr rfl
  intro i hi
  obtain ⟨h1,h2,hne⟩ := far_info hi
  obtain ⟨_,hp,hpp⟩ := mem_filter.mp h1
  obtain ⟨_,hq,hqp⟩ := mem_filter.mp h2
  have hnq : n < i.1*i.2 := (Nat.lt_succ_sqrt n).trans_le (Nat.mul_le_mul hp hq)
  apply inversePair_symmetric hpp hqp hne hnq ((twice_cubeCut hn).trans_lt hq) ((twice_cubeCut hn).trans_lt hp)
  intro p a ha
  have hn' : (p,a) ∉ rowSupport n (cutoffU n) (cutoffL n) (cutoffB n) :=
    fun h => (not_le_of_gt ha) (supportInfo h).2.1
  simp [primeRowCoeff,hn']

end
end GoldbachTransitionSquare

namespace GoldbachTransitionSquare
noncomputable section
open Filter Topology

theorem full_to_far_power_saving :
    ∃ K : ℝ, 0<K ∧ ∀ n : ℕ, 2 ≤ n → ‖fullValue n - farValue n‖ ≤ K*(n:ℝ)^(125/128:ℝ) := by
  obtain ⟨C,hC,h1⟩ := transition_power_saving
  obtain ⟨D,hD,h2⟩ := close_power_saving
  refine ⟨C+D,add_pos hC hD,?_⟩
  intro n hn
  have h1' := h1 n (cutoffU n) (cutoffL n) (cutoffB n) (by omega) (Nat.floor_le (by positivity))
    (deep n) (wide_measurable ..).compl
  change ‖fullValue n-coreValue n‖ ≤ _ at h1'
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hscale := Real.rpow_le_rpow_of_exponent_le hn' (by norm_num : (124/128:ℝ)≤125/128)
  have ht := norm_add_le (fullValue n-coreValue n) (coreValue n-farValue n)
  rw [sub_add_sub_cancel] at ht
  rw [add_mul]
  exact ht.trans (add_le_add (h1'.trans (mul_le_mul_of_nonneg_left hscale hC.le)) (h2 n hn))

end
end GoldbachTransitionSquare

namespace GoldbachTransitionSquare

/-- For each fixed target, only the signed discrepancy between the reciprocal
    prime-pair sum and its wide-arc contribution remains. This bound includes
    the discarded prime powers, small prime cofactors and close prime pairs. -/
theorem full_to_fixed_target_discrepancy :
    ∃ K : ℝ, 0<K ∧ ∀ n : ℕ, 64 ≤ n →
      ‖fullValue n - (reciprocalTotal n - wideFar n)‖ ≤ K*(n:ℝ)^(125/128:ℝ) := by
  obtain ⟨K,hK,h⟩ := full_to_far_power_saving
  refine ⟨K,hK,fun n hn => ?_⟩
  have e := far_eq_inverse_discrepancy n (by omega)
  rw [inverse_eq_reciprocal n hn] at e
  rw [←e]
  exact h n (by omega)

end GoldbachTransitionSquare


theorem Conjectures.Goldbach.Type2FixedTargetReciprocalError :
let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let Λ := ArithmeticFunction.vonMangoldt; let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊; let B₁ := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊; let B₂ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let τ₂ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₁ n < a ∧ a ≤ B₂ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let Jdeep := fun (n : ℕ) (u v : ℕ → ℝ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume; let P := fun n : ℕ => (Finset.range (n+1)).filter (fun p : ℕ => n.sqrt < p ∧ p.Prime);
let M := fun (j : ℤ) (t : ℝ) => Complex.exp (((j : ℂ) * (2*(Real.pi:ℂ)*Complex.I))*(t:ℂ));
let C := fun (n p a : ℕ) => if (p,a) ∈ ((P n).product (Finset.range (B₂ n+1))).filter (fun (i : ℕ×ℕ) => B₁ n < i.2 ∧ U n < i.1 ∧ i.2*i.1 ≤ n) then (((∑ d ∈ a.divisors.filter (fun d => U n < d), μ d) * Real.log p : ℝ):ℂ) else 0;
let R := fun (n p : ℕ) (t : ℝ) => ∑ a ∈ Finset.range (B₂ n+1), C n p a * M a ((p:ℝ)*t);
let D := fun n : ℕ => (P n).product (P n) \ (((P n).product (P n)).filter (fun i => |(i.1:ℤ)-i.2| ≤ B₁ n));
let I := fun (n p q : ℕ) => ((n:ZMod q)*(p:ZMod q)⁻¹).val;
let V := fun n : ℕ => ∑ i ∈ D n, C n i.1 (I n i.1 i.2) * C n i.2 (I n i.2 i.1);
let W := fun n : ℕ => ∫ t in (Set.Icc (0:ℝ) 1 ∩ wideArcs n), (∑ i ∈ D n, R n i.1 t * R n i.2 t) * M (-(n:ℤ)) t;
∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 64 ≤ n → ‖Jdeep n (τ₂ n) (τ₂ n) - (V n - W n)‖ ≤ K*(n:ℝ)^(125/128:ℝ)
:= GoldbachTransitionSquare.full_to_fixed_target_discrepancy
