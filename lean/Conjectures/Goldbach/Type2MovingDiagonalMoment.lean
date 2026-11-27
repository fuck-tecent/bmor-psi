import Mathlib

/-!
# Mean square for the moving Type II (2,2) diagonal

The analytic estimates through 'diagonal_moment' are by 34245621, released with
the Apache-2.0 catalogue proposal #2834. The final dyadic transfer below
uses base-eight logarithms and an upper block only when it is nonempty.
https://github.com/34245621/goldbach-proofs/blob/4f7a6da273db9318568610b397f5349d56f7add1/lean/Conjectures/Goldbach/Type2MovingDiagonalMoment.lean

The short-factor weights, integration arcs, and Fourier frequency all use the same n.
The power saving in the mean square bounds the number of even exceptions in each dyadic block.
Pointwise cancellation at every even target remains open.
-/

namespace TypeTwoDiagonal
open Finset
noncomputable section
def blockSum {Z : Type*} [AddCommMonoid Z] (v : ℕ → Z) (l r : ℕ) := ∑ j ∈ Ico l r, v j

private theorem block_split {Z : Type*} [AddCommMonoid Z] (v : ℕ → Z) {l m r : ℕ}
    (h1 : l ≤ m) (h2 : m ≤ r) : blockSum v l r = blockSum v l m + blockSum v m r :=
  (sum_Ico_consecutive v h1 h2).symm

private theorem scaled_prefix_square (x y : ℂ) {d : ℝ} (h : 0<d) :
    d*‖x+y‖^2 ≤ d*(d+1)*‖x‖^2+(d+1)*‖y‖^2 := by
  have step := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
  nlinarith [mul_le_mul_of_nonneg_left step h.le,sq_nonneg (d*‖x‖-‖y‖)]

/-- Rademacher--Menshov inequality. Each sample may stop at a different
    frequency, as happens on the hyperbola a*p ≤ n. -/
theorem dyadic_prefix_bound (A : Finset ℕ) (F : ℕ → ℕ → ℂ) (energy : ℕ → ℝ)
    (he : ∀ j, 0 ≤ energy j) (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (common : ∀ S ⊆ A, ∀ l r, r ≤ N → (∑ i ∈ S, ‖blockSum (F i) l r‖^2) ≤ C*blockSum energy l r)
    (cut : ℕ → ℕ) (k l : ℕ) (S : Finset ℕ) (hS : S⊆A) (hub : l+2^k ≤ N) :
    (∑ i ∈ S, ‖blockSum (F i) l (min (l+2^k) (cut i))‖^2) ≤
      ((k:ℝ)+1)^2*C*blockSum energy l (l+2^k) := by
  classical
  induction k generalizing l S with
  | zero =>
    let V := S.filter (fun i => l<cut i)
    simp only [pow_zero,Nat.cast_zero,zero_add,one_pow,one_mul] at hub ⊢
    have restrict : (∑ i ∈ S, ‖blockSum (F i) l (min (l+1) (cut i))‖^2) =
        ∑ i ∈ V, ‖blockSum (F i) l (min (l+1) (cut i))‖^2 := by
      symm
      apply sum_subset (filter_subset ..)
      intro i hi ho
      have bound : cut i ≤ l := by by_contra! h; exact ho (mem_filter.mpr ⟨hi,h⟩)
      simp [blockSum,Ico_eq_empty_of_le ((min_le_right ..).trans bound)]
    rw [restrict]
    calc
      _ = ∑ i ∈ V, ‖blockSum (F i) l (l+1)‖^2 := sum_congr rfl fun i hi => by
        rw [min_eq_left (show l+1 ≤ cut i from (mem_filter.mp hi).2)]
      _ ≤ _ := common V ((filter_subset ..).trans hS) l (l+1) hub
  | succ k ih =>
    let d : ℝ := (k:ℝ)+1
    let m := l+2^k
    let r := m+2^k
    have hr : l+2^(k+1) = r := by dsimp [r,m]; rw [pow_succ]; omega
    rw [hr] at hub ⊢
    let L := S.filter (fun i => cut i ≤ m)
    let R := S.filter (fun i => ¬ cut i ≤ m)
    have lm : l ≤ m := Nat.le_add_right ..
    have mr : m ≤ r := Nat.le_add_right ..
    let a := fun i => blockSum (F i) l m
    let b := fun i => blockSum (F i) m (min r (cut i))
    let v := fun i => ‖blockSum (F i) l (min r (cut i))‖^2
    have hsplit : ∑ i ∈ S, v i = (∑ i ∈ L, v i)+(∑ i ∈ R, v i) := (sum_filter_add_sum_filter_not _ _ _).symm
    have low : (∑ i ∈ L, v i) ≤ d^2*C*blockSum energy l m := by
      refine le_trans (le_of_eq (sum_congr rfl fun i hi => ?_)) (ih l L ((filter_subset ..).trans hS) (mr.trans hub))
      have e := (mem_filter.mp hi).2
      dsimp only [v]
      rw [min_eq_right (e.trans mr),min_eq_right e]
    have rem := ih m R ((filter_subset ..).trans hS) hub
    change (∑ i ∈ R, ‖b i‖^2) ≤ d^2*C*blockSum energy m r at rem
    have mid := common R ((filter_subset ..).trans hS) l m (mr.trans hub)
    change (∑ i ∈ R, ‖a i‖^2) ≤ C*blockSum energy l m at mid
    have hd : 0<d := by dsimp [d]; positivity
    have high : d*(∑ i ∈ R, v i) ≤ d*(d+1)*(∑ i ∈ R, ‖a i‖^2)+(d+1)*(∑ i ∈ R, ‖b i‖^2) := by
      simp only [mul_sum,←sum_add_distrib]
      refine sum_le_sum fun i hi => ?_
      have e : m ≤ min r (cut i) := le_min mr (le_of_lt (lt_of_not_ge (mem_filter.mp hi).2))
      dsimp only [v]
      rw [block_split (F i) lm e]
      exact scaled_prefix_square (a i) (b i) hd
    have el : 0 ≤ C*blockSum energy l m := mul_nonneg hC (sum_nonneg fun j _ => he j)
    have er : 0 ≤ C*blockSum energy m r := mul_nonneg hC (sum_nonneg fun j _ => he j)
    have h1 := mul_le_mul_of_nonneg_left low hd.le
    have h2 := mul_le_mul_of_nonneg_left mid (show 0 ≤ d*(d+1) by positivity)
    have h3 := mul_le_mul_of_nonneg_left rem (show 0 ≤ d+1 by positivity)
    have h4 := mul_nonneg (sq_nonneg d) el
    have h5 := mul_nonneg (show 0 ≤ d*(d+1) by positivity) er
    change (∑ i ∈ S, v i) ≤ _
    rw [hsplit,block_split energy lm mr,Nat.cast_succ]
    change _ ≤ (d+1)^2*C*(blockSum energy l m + blockSum energy m r)
    apply le_of_mul_le_mul_left _ hd
    nlinarith only [h1,h2,h3,h4,h5,high]

theorem blockSum_comm {Z : Type*} [AddCommMonoid Z] (f : ℕ → ℕ → Z) (a b l r : ℕ) :
    blockSum (fun u => blockSum (f u) l r) a b =
      blockSum (fun v => blockSum (fun u => f u v) a b) l r := by
  unfold blockSum
  rw [sum_comm]

/-- Two independently moving cutoffs are allowed for each sample. A common
    rectangular Bessel estimate loses at most two squared logarithms. -/
theorem moving_rectangles (S : Finset ℕ) (F : ℕ → ℕ → ℕ → ℂ) (E : ℕ → ℕ → ℝ)
    (hE : ∀ a b, 0 ≤ E a b) (x y : ℕ → ℕ) (h k : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (fixed : ∀ T ⊆ S, ∀ a b l r, b ≤ 2^h → r ≤ 2^k →
      (∑ i ∈ T, ‖blockSum (fun u => blockSum (F i u) l r) a b‖^2) ≤
        C * blockSum (fun u => blockSum (E u) l r) a b) :
    (∑ i ∈ S, ‖blockSum (fun u => blockSum (F i u) 0 (min (2^k) (y i)))
      0 (min (2^h) (x i))‖^2) ≤
      ((h:ℝ)+1)^2 * (((k:ℝ)+1)^2 * C) *
        blockSum (fun u => blockSum (E u) 0 (2^k)) 0 (2^h) := by
  classical
  let G i u := blockSum (F i u) 0 (min (2^k) (y i))
  let e u := blockSum (E u) 0 (2^k)
  have he : ∀ u, 0 ≤ e u := fun u => sum_nonneg (fun v _ => hE u v)
  have Gfixed : ∀ T ⊆ S, ∀ a b, b ≤ 2^h →
      (∑ i ∈ T, ‖blockSum (G i) a b‖^2) ≤ (((k:ℝ)+1)^2*C) * blockSum e a b := by
    intro T hT a b hb
    let A i v := blockSum (fun u => F i u v) a b
    let energy v := blockSum (fun u => E u v) a b
    have pos : ∀ v, 0 ≤ energy v := fun v => sum_nonneg (fun u _ => hE u v)
    have common : ∀ Z ⊆ T, ∀ l r, r ≤ 2^k →
        (∑ i ∈ Z, ‖blockSum (A i) l r‖^2) ≤ C*blockSum energy l r := by
      intro Z hz l r hr
      simpa only [A,energy,←blockSum_comm (F _) a b l r,←blockSum_comm E a b l r]
        using fixed Z (hz.trans hT) a b l r hb hr
    have m := dyadic_prefix_bound T A energy pos (2^k) C hC common y k 0 T
      (fun _ ht => ht) (by simp)
    simpa only [G,e,A,energy,zero_add,blockSum_comm (F _) a b 0 _,blockSum_comm E a b 0 _]
      using m
  have m := dyadic_prefix_bound S G e he (2^h) (((k:ℝ)+1)^2*C)
    (mul_nonneg (sq_nonneg _) hC) Gfixed x h 0 S (fun _ hi => hi) (by simp)
  simpa only [G,e,zero_add] using m

end
end TypeTwoDiagonal

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
noncomputable def arcHeight (n : ℕ) := 256 * cutoffB n * (Nat.log 2 (n+2))^2
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

end
end GoldbachTransitionSquare

namespace GoldbachTransitionSquare
noncomputable section
open MeasureTheory

private def muR (d : ℕ) : ℝ := ((ArithmeticFunction.moebius d : ℤ):ℝ)

private def coprimeFlag (g : ℕ) : ArithmeticFunction ℝ where
  toFun d := if d ≠ 0 ∧ d.Coprime g then 1 else 0
  map_zero' := by simp

private theorem coprimeFlag_mult (g : ℕ) : (coprimeFlag g).IsMultiplicative := by
  constructor
  · simp [coprimeFlag]
  · intro a b _
    by_cases ha : a=0 <;> by_cases hb : b=0 <;> by_cases h1 : a.Coprime g <;> by_cases h2 : b.Coprime g <;>
      simp [coprimeFlag,Nat.coprime_mul_iff_left,ha,hb,h1,h2] <;> split_ifs <;> grind

private def restrictedMu (g d : ℕ) : ℝ := if d.Coprime g then muR d else 0

private theorem restrictedMu_abs (g d : ℕ) : |restrictedMu g d| ≤ 1 := by
  unfold restrictedMu muR
  split_ifs
  · exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d)
  · simp

/-- Möbius cancellation on the divisors coprime to a fixed integer. -/
private theorem restrictedMu_divisor_sandwich (g m : ℕ) (hm : 1 ≤ m) :
    0 ≤ ∑ d ∈ m.divisors, restrictedMu g d ∧
    ∑ d ∈ m.divisors, restrictedMu g d ≤ 1 := by
  let f := coprimeFlag g
  have h := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub f (coprimeFlag_mult g) (n:=m)
    (Nat.ne_of_gt hm)
  have one (d : ℕ) (hd : d ∈ m.divisors) : muR d * f d = restrictedMu g d := by
    have hz := (Nat.pos_of_mem_divisors hd).ne'
    by_cases hc : d.Coprime g <;> simp [f,coprimeFlag,restrictedMu,hz,hc]
  have heq : (∑ d ∈ m.divisors, restrictedMu g d) = ∏ p ∈ m.primeFactors, (1-f p) := by
    rw [h]
    exact sum_congr rfl (fun d hd => (one d hd).symm)
  have bounds (p : ℕ) : 0 ≤ 1-f p ∧ 1-f p ≤ 1 := by
    change 0 ≤ 1-(if p ≠ 0 ∧ p.Coprime g then (1:ℝ) else 0) ∧ _
    by_cases hp : p ≠ 0 ∧ p.Coprime g
    · change _ ∧ 1-(if p ≠ 0 ∧ p.Coprime g then (1:ℝ) else 0) ≤ 1
      rw [if_pos hp]; norm_num
    · change _ ∧ 1-(if p ≠ 0 ∧ p.Coprime g then (1:ℝ) else 0) ≤ 1
      rw [if_neg hp]; norm_num
  rw [heq]
  refine ⟨prod_nonneg (fun i _ => (bounds i).1),?_⟩
  simpa using prod_le_prod₀ (s:=m.primeFactors) (fun i _ => (bounds i).1) (fun i _ => (bounds i).2)

private theorem quotient_error (X d : ℕ) (hd : 0 < d) :
    0 ≤ (X:ℝ)/d - ((X/d:ℕ):ℝ) ∧ (X:ℝ)/d - ((X/d:ℕ):ℝ) ≤ 1 := by
  have hdp : (0:ℝ) < d := by exact_mod_cast hd
  have hr : ((X % d:ℕ):ℝ)+(d:ℝ)*((X/d:ℕ):ℝ)=X := by exact_mod_cast Nat.mod_add_div X d
  have hlt : ((X % d:ℕ):ℝ) < d := by exact_mod_cast Nat.mod_lt X hd
  have h0 : (0:ℝ) ≤ (X % d:ℕ) := Nat.cast_nonneg _
  constructor
  · apply sub_nonneg.mpr
    apply (le_div_iff₀ hdp).mpr
    nlinarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hdp]
    nlinarith

/-- Uniform in the excluded prime factors: no analytic estimate on the
    Mertens function is needed for this elementary bound. -/
theorem restricted_mobius_reciprocal (X g : ℕ) :
    |∑ d ∈ Icc 1 X, restrictedMu g d/(d:ℝ)| ≤ 2 := by
  by_cases hz : X=0
  · simp [hz]
  have hx : (0:ℝ) < X := by exact_mod_cast Nat.pos_of_ne_zero hz
  have hx0 := hx.le
  let S := Icc 1 X
  let floorSum := ∑ d ∈ S, restrictedMu g d * ((X/d:ℕ):ℝ)
  have exactFloor : floorSum = ∑ m ∈ S, ∑ d ∈ m.divisors, restrictedMu g d := by
    rw [finite_divisor_hyperbola X (fun d _ => restrictedMu g d)]
    refine sum_congr rfl fun d _ => ?_
    simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel, mul_comm]
  have hf0 : 0 ≤ floorSum := by
    rw [exactFloor]; exact sum_nonneg fun m hm => (restrictedMu_divisor_sandwich g m (mem_Icc.mp hm).1).1
  have hfu : floorSum ≤ X := by
    rw [exactFloor]
    calc
      _ ≤ ∑ _m ∈ S, (1:ℝ) := sum_le_sum fun m hm => (restrictedMu_divisor_sandwich g m (mem_Icc.mp hm).1).2
      _ = _ := by simp [S,Nat.card_Icc]
  have error : |∑ d ∈ S, restrictedMu g d*((X:ℝ)/d-((X/d:ℕ):ℝ))| ≤ X := by
    calc
      _ ≤ ∑ d ∈ S, |restrictedMu g d*((X:ℝ)/d-((X/d:ℕ):ℝ))| := abs_sum_le_sum_abs ..
      _ ≤ ∑ _d ∈ S, (1:ℝ) := by
        refine sum_le_sum fun d hd => ?_
        obtain ⟨h0,h1⟩ := quotient_error X d (mem_Icc.mp hd).1
        rw [abs_mul,abs_of_nonneg h0]
        exact (mul_le_mul (restrictedMu_abs ..) h1 h0 zero_le_one).trans_eq (by ring)
      _ = _ := by simp [S,Nat.card_Icc]
  have eqn : (X:ℝ)*(∑ d ∈ S, restrictedMu g d/(d:ℝ)) =
      floorSum + ∑ d ∈ S, restrictedMu g d*((X:ℝ)/d-((X/d:ℕ):ℝ)) := by
    unfold floorSum
    rw [mul_sum,←sum_add_distrib]
    exact sum_congr rfl fun d _ => by ring
  have ab := abs_add_le floorSum (∑ d ∈ S, restrictedMu g d*((X:ℝ)/d-((X/d:ℕ):ℝ)))
  rw [←eqn,abs_mul,abs_of_nonneg hx0,abs_of_nonneg hf0] at ab
  change |∑ d ∈ S, restrictedMu g d/(d:ℝ)| ≤ 2
  apply (mul_le_mul_iff_right₀ hx).mp
  linarith

end
end GoldbachTransitionSquare


namespace GoldbachTransitionSquare
noncomputable section

private theorem muR_mul_restricted (g k : ℕ) : muR (g*k) = muR g * restrictedMu g k := by
  by_cases h : g.Coprime k
  · rw [restrictedMu,if_pos h.symm]
    unfold muR
    exact_mod_cast ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h
  · have ns : ¬ Squarefree (g*k) := fun hs => h (Nat.coprime_of_squarefree_mul hs)
    simp [muR,restrictedMu,show ¬k.Coprime g from fun t => h t.symm,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree ns]

private def sieveColumn (g d : ℕ) : ℝ := if g ∣ d then muR d/(d:ℝ) else 0

private theorem multiples_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) (U g : ℕ) (hg : 0 < g) :
    (∑ d ∈ (Icc 1 U).filter (fun d => g ∣ d), f d) = ∑ k ∈ Icc 1 (U/g), f (g*k) := by
  let e : ℕ ↪ ℕ := ⟨fun k => g*k,fun _ _ he => Nat.eq_of_mul_eq_mul_left hg he⟩
  have he : (Icc 1 U).filter (fun d => g ∣ d) = (Icc 1 (U/g)).map e := by
    ext d
    simp only [mem_filter,mem_map,mem_Icc]
    constructor
    · rintro ⟨⟨h1,h2⟩,k,rfl⟩
      refine ⟨k,⟨?_,(Nat.le_div_iff_mul_le hg).mpr (by simpa [Nat.mul_comm] using h2)⟩,rfl⟩
      by_contra! h0
      have : k=0 := by omega
      simp [this] at h1
    · rintro ⟨k,⟨hk,hk'⟩,rfl⟩
      change (1 ≤ g*k ∧ g*k ≤ U) ∧ g ∣ g*k
      exact ⟨⟨Nat.mul_pos hg hk,by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hg).mp hk'⟩,
        dvd_mul_right ..⟩
  rw [he,sum_map]
  rfl

private theorem column_le (g U : ℕ) (hg : 0<g) :
    |∑ d ∈ Icc 1 U, sieveColumn g d| ≤ 2/(g:ℝ) := by
  have hgr : (g:ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have eqn : (∑ d ∈ Icc 1 U, sieveColumn g d) =
      (muR g/(g:ℝ)) * ∑ k ∈ Icc 1 (U/g), restrictedMu g k/(k:ℝ) := by
    unfold sieveColumn
    rw [←sum_filter,multiples_sum _ _ _ hg,mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [muR_mul_restricted,Nat.cast_mul]
    ring
  have hmu : |muR g| ≤ 1 := by unfold muR; exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=g)
  rw [eqn,abs_mul,abs_div]
  simp only [abs_of_nonneg (Nat.cast_nonneg g : (0:ℝ) ≤ (g:ℝ))]
  calc
    _ ≤ (1/(g:ℝ))*2 := mul_le_mul (div_le_div_of_nonneg_right hmu (Nat.cast_nonneg g))
      (restricted_mobius_reciprocal ..) (abs_nonneg _) (by positivity)
    _ = _ := by ring

private theorem gcd_totient_column (U d e : ℕ) (hd : d ∈ Icc 1 U) (he : e ∈ Icc 1 U) :
    (∑ g ∈ Icc 1 U, if g ∣ d ∧ g ∣ e then (g.totient:ℝ) else 0) = d.gcd e := by
  have hpos := Nat.gcd_pos_of_pos_left e (mem_Icc.mp hd).1
  have hsub : (Icc 1 U).filter (fun g => g ∣ d ∧ g ∣ e) = (d.gcd e).divisors := by
    ext g
    simp only [mem_filter,mem_Icc,Nat.mem_divisors]
    constructor
    · rintro ⟨_,h1,h2⟩
      exact ⟨Nat.dvd_gcd h1 h2,hpos.ne'⟩
    · rintro ⟨hdv,_⟩
      have hg := Nat.pos_of_dvd_of_pos hdv hpos
      have hgd := hdv.trans (Nat.gcd_dvd_left d e)
      exact ⟨⟨hg,(Nat.le_of_dvd (mem_Icc.mp hd).1 hgd).trans (mem_Icc.mp hd).2⟩,hgd,hdv.trans (Nat.gcd_dvd_right d e)⟩
  rw [←sum_filter,hsub]
  exact_mod_cast Nat.sum_totient (d.gcd e)

def mobiusLCMMass (U : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 U, ∑ e ∈ Icc 1 U, muR d*muR e/(d.lcm e:ℝ)

theorem selberg_diagonal (U : ℕ) :
    mobiusLCMMass U = ∑ g ∈ Icc 1 U, (g.totient:ℝ)*(∑ d ∈ Icc 1 U, sieveColumn g d)^2 := by
  let I := Icc 1 U
  let w (g d e : ℕ) := (g.totient:ℝ)*sieveColumn g d*sieveColumn g e
  have entry (d : ℕ) (hd : d ∈ I) (e : ℕ) (he : e ∈ I) :
      muR d*muR e/(d.lcm e:ℝ) = ∑ g ∈ I, w g d e := by
    have d0 : (d:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (mem_Icc.mp hd).1)
    have e0 : (e:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (mem_Icc.mp he).1)
    have l0 : (d.lcm e:ℝ) ≠ 0 := by exact_mod_cast (Nat.lcm_ne_zero (Nat.ne_of_gt (mem_Icc.mp hd).1) (Nat.ne_of_gt (mem_Icc.mp he).1))
    have prod : (d.gcd e:ℝ)*(d.lcm e:ℝ) = d*e := by exact_mod_cast Nat.gcd_mul_lcm d e
    calc
      _ = (muR d/(d:ℝ))*(muR e/(e:ℝ))*(d.gcd e:ℝ) := by
        field_simp
        linear_combination -(muR d*muR e)*prod
      _ = _ := by
        rw [←gcd_totient_column U d e hd he,mul_sum]
        refine sum_congr rfl fun g _ => ?_
        by_cases h1 : g ∣ d <;> by_cases h2 : g ∣ e <;> simp [w,sieveColumn,h1,h2] <;> ring
  calc
    mobiusLCMMass U = ∑ i ∈ I ×ˢ I, ∑ g ∈ I, w g i.1 i.2 := by
      rw [sum_product]
      exact sum_congr rfl fun d hd => sum_congr rfl fun e he => entry d hd e he
    _ = ∑ g ∈ I, ∑ i ∈ I ×ˢ I, w g i.1 i.2 := sum_comm
    _ = _ := by
      refine sum_congr rfl fun g _ => ?_
      rw [sum_product,pow_two,sum_mul,mul_sum]
      refine sum_congr rfl fun d _ => ?_
      rw [mul_sum,mul_sum]
      refine sum_congr rfl fun e _ => ?_
      dsimp [w]
      ring

/-- An elementary logarithmic upper bound saves two powers of log over
    expanding the Möbius coefficients in absolute value. -/
theorem mobiusLCMMass_le (U : ℕ) : mobiusLCMMass U ≤ 4*(1+Real.log U) := by
  rw [selberg_diagonal]
  calc
    _ ≤ ∑ g ∈ Icc 1 U, 4*(g:ℝ)⁻¹ := by
      refine sum_le_sum fun g hg => ?_
      have gp := (mem_Icc.mp hg).1
      have g0 : (g:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt gp)
      have hu := column_le g U gp
      have hφ : (g.totient:ℝ) ≤ g := by exact_mod_cast Nat.totient_le g
      calc
        _ ≤ (g:ℝ)*(2/(g:ℝ))^2 := mul_le_mul hφ (by simpa using pow_le_pow_left₀ (abs_nonneg _) hu 2)
          (sq_nonneg _) (Nat.cast_nonneg g)
        _ = _ := by field_simp <;> norm_num
    _ ≤ _ := by
      rw [←mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using harmonic_le_one_add_log U

end
end GoldbachTransitionSquare


namespace GoldbachTransitionSquare
noncomputable section

def shortSieve (U m : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 U, if d ∣ m then muR d else 0

private theorem low_eq_short {m : ℕ} (U : ℕ) (hm : 1 < m) : lowMoebiusWeight U m = -shortSieve U m := by
  have hn : m ≠ 1 := by omega
  have z : (∑ d ∈ m.divisors, ArithmeticFunction.moebius d) = 0 := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply (f:=ArithmeticFunction.moebius),
      ArithmeticFunction.moebius_mul_coe_zeta,ArithmeticFunction.one_apply_ne hn]
  have zr : (∑ d ∈ m.divisors, muR d) = 0 := by unfold muR; exact_mod_cast z
  have partition := sum_filter_add_sum_filter_not m.divisors (fun d => U<d) muR
  simp only [not_lt] at partition
  have eqs : m.divisors.filter (fun d => d ≤ U) = (Icc 1 U).filter (fun d => d ∣ m) := by
    ext d
    simp only [mem_filter,mem_Icc,Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd,_⟩,hU⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega),hU⟩,hd⟩
    · rintro ⟨⟨_,hU⟩,hd⟩
      exact ⟨⟨hd,by omega⟩,hU⟩
  rw [eqs,zr] at partition
  apply eq_neg_iff_add_eq_zero.mpr
  unfold shortSieve
  rw [←sum_filter]
  exact partition

private theorem shortSieve_square (B U : ℕ) :
    (∑ a ∈ Icc 1 B, (shortSieve U a)^2) =
      ∑ d ∈ Icc 1 U, ∑ e ∈ Icc 1 U, muR d*muR e*((B/(d.lcm e):ℕ):ℝ) := by
  let I := Icc 1 U
  let J := Icc 1 B
  let w (i : ℕ×ℕ) (m : ℕ) := if i.1.lcm i.2 ∣ m then muR i.1 * muR i.2 else 0
  have square (a : ℕ) : (shortSieve U a)^2 = ∑ i ∈ I ×ˢ I, w i a := by
    unfold shortSieve
    rw [pow_two,sum_mul,sum_product]
    refine sum_congr rfl fun d _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun e _ => ?_
    dsimp only [w,Prod.fst,Prod.snd]
    by_cases hd : d ∣ a <;> by_cases he : e ∣ a <;> simp [Nat.lcm_dvd_iff,hd,he]
  calc
    _ = ∑ m ∈ J, ∑ i ∈ I ×ˢ I, w i m := sum_congr rfl fun m _ => square m
    _ = ∑ i ∈ I ×ˢ I, ∑ m ∈ J, w i m := sum_comm
    _ = _ := by
      rw [sum_product]
      refine sum_congr rfl fun d hd => sum_congr rfl fun e he => ?_
      have hl : 0 < d.lcm e := Nat.pos_of_ne_zero
        (Nat.lcm_ne_zero (Nat.ne_of_gt (mem_Icc.mp hd).1) (Nat.ne_of_gt (mem_Icc.mp he).1))
      dsimp only [w,J,Prod.fst,Prod.snd]
      rw [←sum_filter,multiples_sum _ _ _ hl]
      simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
      ring

theorem shortSieve_l2 (B U : ℕ) :
    (∑ a ∈ Icc 1 B, (shortSieve U a)^2) ≤
    4*(B:ℝ)*(1+Real.log U)+(U:ℝ)^2 := by
  let I := Icc 1 U
  have hm (d : ℕ) : |muR d| ≤ 1 := by
    unfold muR; exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d)
  have entry (d : ℕ) (hd : d ∈ I) (e : ℕ) (he : e ∈ I) :
      muR d*muR e*((B/(d.lcm e):ℕ):ℝ) ≤
      (B:ℝ)*(muR d*muR e/(d.lcm e:ℝ))+1 := by
    have hl : 0 < d.lcm e := Nat.pos_of_ne_zero
      (Nat.lcm_ne_zero (Nat.ne_of_gt (mem_Icc.mp hd).1) (Nat.ne_of_gt (mem_Icc.mp he).1))
    obtain ⟨h0,h1⟩ := quotient_error B (d.lcm e) hl
    have hh : |muR d*muR e| ≤ 1 := by
      rw [abs_mul]
      simpa using mul_le_mul (hm d) (hm e) (abs_nonneg _) zero_le_one
    have lower : -1 ≤ muR d*muR e*((B:ℝ)/(d.lcm e:ℝ)-((B/(d.lcm e):ℕ):ℝ)) := by
      apply (abs_le.mp _).1
      rw [abs_mul,abs_of_nonneg h0]
      simpa using mul_le_mul hh h1 h0 zero_le_one
    linarith [show muR d*muR e*((B:ℝ)/(d.lcm e:ℝ)-((B/(d.lcm e):ℕ):ℝ)) =
      (B:ℝ)*(muR d*muR e/(d.lcm e:ℝ)) - muR d*muR e*((B/(d.lcm e):ℕ):ℝ) by ring]
  rw [shortSieve_square]
  calc
    _ ≤ ∑ d ∈ I, ∑ e ∈ I, ((B:ℝ)*(muR d*muR e/(d.lcm e:ℝ))+1) :=
      sum_le_sum fun d hd => sum_le_sum fun e he => entry d hd e he
    _ = (B:ℝ)*mobiusLCMMass U+(U:ℝ)^2 := by
      simp only [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,mul_one]
      simp [I,Nat.card_Icc,mobiusLCMMass,pow_two]
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_left (mobiusLCMMass_le U) (Nat.cast_nonneg B)
      linarith

end
end GoldbachTransitionSquare

namespace GoldbachTransitionSquare
private noncomputable def rowBudget (B U : ℕ) : ℝ := 4*(B:ℝ)*(1+Real.log U)+(U:ℝ)^2
end GoldbachTransitionSquare

namespace GoldbachTransitionSquare
noncomputable section
open DyadicMixedB4Fourier

private theorem deep_separates_rationals {n B H d j : ℕ} {t : ℝ} (hn : 0<n) (ht : t ∉ wide n B H)
    (hd : 0<d) (hB : d≤B) (hj : j≤d) : (H:ℝ)/n < |(d:ℝ)*t-(j:ℝ)| := by
  let g := j.gcd d
  let q := d/g
  let a := j/g
  have hg : 0<g := Nat.gcd_pos_of_pos_right j hd
  have da : g*a = j := Nat.mul_div_cancel' (Nat.gcd_dvd_left j d)
  have dq : g*q = d := Nat.mul_div_cancel' (Nat.gcd_dvd_right j d)
  have hq : 0<q := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz,mul_zero] at dq
    exact hd.ne' dq.symm
  have qd : q≤d := Nat.div_le_self ..
  have aq : a≤q := Nat.div_le_div_right hj
  have cop : a.Coprime q := Nat.coprime_div_gcd_div_gcd hg
  have hq0 : 0<(q:ℝ) := by exact_mod_cast hq
  have hn0 : 0<(n:ℝ) := by exact_mod_cast hn
  have hg1 : (1:ℝ)≤g := by exact_mod_cast hg
  have gap : (H:ℝ)/((q:ℝ)*n) < |t-(a:ℝ)/q| := by
    by_contra! h
    exact ht ⟨q,a,hq,qd.trans hB,aq,cop,h⟩
  have gap' : (H:ℝ)/n < |(q:ℝ)*t-a| := by
    have eqn : (q:ℝ)*t-a = (t-(a:ℝ)/q)*q := by field_simp
    rw [eqn,abs_mul,abs_of_pos hq0]
    calc
      _ = ((H:ℝ)/((q:ℝ)*n))*q := by field_simp
      _ < _ := mul_lt_mul_of_pos_right gap hq0
  have rel : (d:ℝ)*t-j = (g:ℝ)*((q:ℝ)*t-a) := by rw [←dq,←da]; push_cast; ring
  rw [rel,abs_mul,abs_of_pos (by exact_mod_cast hg : (0:ℝ)<g)]
  exact gap'.trans_le (le_mul_of_one_le_left (abs_nonneg _) hg1)

def orbitPoint (t : ℝ) (a : ℕ) := Int.fract ((a:ℝ)*t)

private theorem rotation_separated {n B H a b : ℕ} {t : ℝ} (hn : 0<n) (ht : t ∈ Set.Icc 0 1)
    (hm : t ∉ wide n B H) (ha : a≤B) (hb : b≤B) (hne : a≠b) :
    (H:ℝ)/n < |orbitPoint t a-orbitPoint t b| := by
  wlog hab : b<a generalizing a b
  · rw [abs_sub_comm]
    exact this hb ha hne.symm (by omega)
  let d := a-b
  have de : (d:ℝ) = (a:ℝ)-b := by dsimp [d]; rw [Nat.cast_sub hab.le]
  let A := ⌊(a:ℝ)*t⌋
  let C := ⌊(b:ℝ)*t⌋
  have ca : C ≤ A := Int.floor_le_floor (mul_le_mul_of_nonneg_right (by exact_mod_cast hab.le) ht.1)
  have ad : A ≤ C+d := by
    have e : (a:ℝ)*t ≤ (b:ℝ)*t+d := by rw [de]; nlinarith [mul_nonneg (sub_nonneg.mpr (show (b:ℝ)≤a by exact_mod_cast hab.le)) (sub_nonneg.mpr ht.2)]
    simpa only [Int.floor_add_natCast,C,A] using Int.floor_le_floor e
  let j := (A-C).toNat
  have je : (j:ℤ)=A-C := Int.toNat_of_nonneg (sub_nonneg.mpr ca)
  have jle : j≤d := by omega
  have h := deep_separates_rationals hn hm (show 0<d by dsimp [d]; omega)
    (show d≤B from (Nat.sub_le ..).trans ha) jle
  have jr : (j:ℝ) = (A:ℝ)-C := by exact_mod_cast je
  simpa only [orbitPoint,Int.fract,de,jr,A,C,sub_mul,sub_sub_sub_comm] using h

theorem deep_orbit_sieve (n B H N : ℕ) (hn : 0<n) (hH : 0<H) (t : ℝ) (ht : t ∈ Set.Icc 0 1)
    (hm : t ∉ wide n B H) (A : Finset ℕ) (hA : ∀ a ∈ A, a ≤ B) (c : ℕ → ℂ) :
    (∑ a ∈ A, ‖∑ j ∈ range N, c j * mode (j:ℤ) ((a:ℝ)*t)‖^2) ≤
      (3/(min 1 ((H:ℝ)/n)) + 6*(1+2*Real.pi*N)) * (∑ j ∈ range N, ‖c j‖^2) := by
  let r := min 1 ((H:ℝ)/n)
  have hH' : (0:ℝ)<H := by exact_mod_cast hH
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hr : 0<r := lt_min zero_lt_one (div_pos hH' hn')
  have hru : r ≤ 1 := min_le_left ..
  let X := A.image (orbitPoint t)
  have single : Set.InjOn (orbitPoint t) (A : Set ℕ) := by
    intro i hi j hj he
    by_contra h
    have sep := rotation_separated hn ht hm (hA i hi) (hA j hj) h
    rw [he,sub_self,abs_zero] at sep
    linarith [div_pos hH' hn']
  have unit : (X : Set ℝ) ⊆ Set.Icc 0 1 := by
    intro x hx
    obtain ⟨a,_,rfl⟩ := mem_image.mp hx
    exact ⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩
  have sep : (X : Set ℝ).Pairwise (fun x y => 2*(r/2) ≤ |x-y|) := by
    intro x hx y hy hne
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hy
    have e := rotation_separated hn ht hm (hA i hi) (hA j hj) (fun h => hne (h ▸ rfl))
    linarith [show r ≤ (H:ℝ)/n from min_le_right ..]
  have sieve := additive_large_sieve N c X (show 0<r/2 by positivity) (by linarith) unit sep
  rw [show 2*(r/2)=r by ring] at sieve
  unfold X at sieve
  rw [sum_image single] at sieve
  refine le_trans ?_ sieve
  apply le_of_eq
  refine sum_congr rfl fun a _ => ?_
  have per := periodic_mode_sum N c
  have he := per.sub_zsmul_eq (x:=(a:ℝ)*t) ⌊(a:ℝ)*t⌋
  simpa only [orbitPoint,Int.fract,zsmul_eq_mul,mul_one] using congrArg (fun z : ℂ => ‖z‖^2) he.symm

end
end GoldbachTransitionSquare

open TypeTwoDiagonal (blockSum dyadic_prefix_bound)

namespace GoldbachTransitionSquare
noncomputable section
open DyadicMixedB4Fourier

private theorem padded_block {V : Type*} [AddCommMonoid V] (f : ℕ → V) (l r N : ℕ) (hr : r ≤ N) :
    (∑ j ∈ range N, if j ∈ Ico l r then f j else 0) = blockSum f l r := by
  rw [←sum_filter]
  have e : (range N).filter (fun j => j ∈ Ico l r) = Ico l r :=
    filter_mem_eq_inter.trans (inter_eq_right.mpr (fun j hj => mem_range.mpr ((mem_Ico.mp hj).2.trans_le hr)))
  rw [e]; rfl

theorem deep_prefix_sieve (n B H k : ℕ) (hn : 0<n) (hH : 0<H) (t : ℝ) (ht : t ∈ Set.Icc 0 1)
    (hm : t ∉ wide n B H) (A : Finset ℕ) (hA : ∀ a ∈ A, a ≤ B) (c : ℕ → ℂ) (cut : ℕ → ℕ) :
    (∑ a ∈ A, ‖∑ j ∈ range (min (2^k) (cut a)), c j * mode (j:ℤ) ((a:ℝ)*t)‖^2) ≤
      ((k:ℝ)+1)^2 * (3/(min 1 ((H:ℝ)/n)) + 6*(1+2*Real.pi*(2^k:ℕ))) * (∑ j ∈ range (2^k), ‖c j‖^2) := by
  let N := 2^k
  let C := 3/(min 1 ((H:ℝ)/n)) + 6*(1+2*Real.pi*(N:ℝ))
  let F := fun (a j : ℕ) => c j * mode (j:ℤ) ((a:ℝ)*t)
  let energy := fun j => ‖c j‖^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have common (S : Finset ℕ) (hS : S⊆A) (l r : ℕ) (hr : r ≤ N) :
      (∑ a ∈ S, ‖blockSum (F a) l r‖^2) ≤ C*blockSum energy l r := by
    let v := fun j => if j ∈ Ico l r then c j else 0
    have e (a : ℕ) : (∑ j ∈ range N, v j*mode (j:ℤ) ((a:ℝ)*t)) = blockSum (F a) l r := by
      refine Eq.trans (sum_congr rfl fun j _ => ?_) (padded_block (F a) l r N hr)
      by_cases h : j ∈ Ico l r
      · simp only [v,F,if_pos h]
      · simp only [v,F,if_neg h,zero_mul]
    have ene : (∑ j ∈ range N, ‖v j‖^2) = blockSum energy l r := by
      refine Eq.trans (sum_congr rfl fun j _ => ?_) (padded_block energy l r N hr)
      by_cases h : j ∈ Ico l r
      · simp only [v,energy,if_pos h]
      · simp only [v,energy,if_neg h,norm_zero,zero_pow (by decide : 2≠0)]
    have sieve := deep_orbit_sieve n B H N hn hH t ht hm S (fun a ha => hA a (hS ha)) v
    simpa only [e,ene,C] using sieve
  have h := dyadic_prefix_bound A F energy (fun _ => sq_nonneg _) N C hC common cut k 0 A (fun _ h => h) (by dsimp [N]; omega)
  simpa only [blockSum,zero_add,Nat.Ico_zero_eq_range,F,energy,C,N] using h

end
end GoldbachTransitionSquare
namespace GoldbachTransitionSquare
noncomputable section
open DyadicMixedB4Fourier

private def primeSignal (n U p : ℕ) : ℂ :=
  if p ∈ bigPrimes n ∧ U<p then (Real.log p:ℝ) else 0

private theorem signal_energy (n U N : ℕ) :
    (∑ p ∈ range N, ‖primeSignal n U p‖^2) ≤ (N:ℝ)*(Real.log n)^2 := by
  calc
    _ ≤ ∑ _p ∈ range N, (Real.log n)^2 := by
      refine sum_le_sum fun p _ => ?_
      unfold primeSignal
      split_ifs with h
      · have info := mem_filter.mp h.1
        have hlog := Real.log_nonneg (by exact_mod_cast info.2.2.one_le : (1:ℝ)≤p)
        rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlog]
        exact pow_le_pow_left₀ hlog (Real.log_le_log (by exact_mod_cast info.2.2.pos) (by exact_mod_cast Nat.le_of_lt_succ (mem_range.mp info.1))) 2
      · simpa using sq_nonneg (Real.log n)
    _ = _ := by simp

private theorem by_short_factor (n U L B : ℕ) (t : ℝ) :
    fourierSum n (core n U L B) t = ∑ a ∈ Ioc L B, (lowMoebiusWeight U a:ℂ)*
      ∑ p ∈ range (n/a+1), primeSignal n U p*mode (p:ℤ) ((a:ℝ)*t) := by
  let A := Ioc L B
  let P := bigPrimes n
  rw [core_rows]
  simp_rw [row]
  rw [sum_comm]
  let terms := fun a p => primeRowCoeff n U L B p a*mode (a:ℤ) ((p:ℝ)*t)
  have sub : A ⊆ range (B+1) := fun a ha => mem_range.mpr (Nat.lt_succ_of_le (mem_Ioc.mp ha).2)
  calc
    _ = ∑ a ∈ A, ∑ p ∈ P, terms a p := by
      symm
      apply sum_subset sub
      intro a ha ho
      refine sum_eq_zero fun p _ => ?_
      have off : (p,a) ∉ rowSupport n U L B := fun h => ho (mem_Ioc.mpr ⟨(supportInfo h).2.2.1,(supportInfo h).2.1⟩)
      simp [terms,primeRowCoeff,off]
    _ = _ := by
      refine sum_congr rfl fun a ha => ?_
      let J := range (n/a+1)
      have ai := mem_Ioc.mp ha
      have ap : 0<a := (Nat.zero_le L).trans_lt ai.1
      have Jsub : J ⊆ range (n+1) := range_mono (by have := Nat.div_le_self n a; omega)
      have psub : P ⊆ range (n+1) := filter_subset ..
      have extP : (∑ p ∈ P, terms a p) = ∑ p ∈ range (n+1), terms a p := by
        apply sum_subset psub
        intro p _ hp
        have ho : (p,a) ∉ rowSupport n U L B := fun h => hp (supportInfo h).1
        simp [terms,primeRowCoeff,ho]
      let g := fun p => if p ∈ J then (lowMoebiusWeight U a:ℂ)*(primeSignal n U p*mode (p:ℤ) ((a:ℝ)*t)) else 0
      have pad : (∑ p ∈ J, (lowMoebiusWeight U a:ℂ)*(primeSignal n U p*mode (p:ℤ) ((a:ℝ)*t))) =
          ∑ p ∈ range (n+1), g p := by
        calc
          _ = ∑ p ∈ J, g p := sum_congr rfl fun p hp => by simp only [g,if_pos hp]
          _ = _ := sum_subset Jsub fun p _ hp => by simp only [g,if_neg hp]
      rw [mul_sum,extP,pad]
      refine sum_congr rfl fun p _ => ?_
      have eqph : mode (a:ℤ) ((p:ℝ)*t) = mode (p:ℤ) ((a:ℝ)*t) := by
        unfold mode frequency
        congr 1
        push_cast
        ring
      have bj : p ∈ J ↔ a*p ≤ n := by
        simp only [J,mem_range,Nat.lt_succ_iff,Nat.le_div_iff_mul_le ap,Nat.mul_comm p a]
      have hs : (p,a) ∈ rowSupport n U L B ↔ (p ∈ P ∧ U<p) ∧ p ∈ J := by
        simp only [rowSupport,mem_filter,mem_product,mem_range,Nat.lt_succ_iff,bj]
        dsimp only [P]
        tauto
      change primeRowCoeff n U L B p a * _ = _
      rw [eqph]
      by_cases hP : p ∈ bigPrimes n ∧ U<p <;> by_cases hJ : p∈J
      · have hIn := hs.mpr ⟨hP,hJ⟩
        simp only [primeRowCoeff,if_pos hIn,rawCoeff,g,if_pos hJ,primeSignal,if_pos hP,Complex.ofReal_mul,mul_assoc]
      all_goals
        have hOut : (p,a) ∉ rowSupport n U L B := by rw [hs]; tauto
        simp only [primeRowCoeff,if_neg hOut,g,primeSignal,hP,hJ,if_true,if_false,zero_mul,mul_zero]

theorem core_deep_pointwise (n U L B H k : ℕ) (hn : 0<n) (hL : 1 ≤ L) (hH : 0<H)
    (hcover : n/(L+1)+1 ≤ 2^k) {t : ℝ} (ht : t ∈ Set.Icc 0 1) (hm : t ∉ wide n B H) :
    ‖fourierSum n (core n U L B) t‖^2 ≤ rowBudget B U * (((k:ℝ)+1)^2 *
      (3/(min 1 ((H:ℝ)/n))+6*(1+2*Real.pi*(2^k:ℕ))) * ((2^k:ℕ)*(Real.log n)^2)) := by
  let A := Ioc L B
  let v := primeSignal n U
  let cut := fun a => n/a+1
  let F := fun a => ∑ p ∈ range (cut a), v p*mode (p:ℤ) ((a:ℝ)*t)
  let w := fun a => (lowMoebiusWeight U a:ℂ)
  have hcut (a : ℕ) (ha : a ∈ A) : cut a ≤ 2^k := by
    have le : n/a ≤ n/(L+1) := (Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr
      ((Nat.mul_le_mul_left (n/a) (show L+1 ≤ a from (mem_Ioc.mp ha).1)).trans (Nat.div_mul_le_self n a))
    exact (Nat.succ_le_succ le).trans hcover
  have hmass : (∑ a ∈ A, ‖w a‖^2) ≤ rowBudget B U := by
    calc
      _ = ∑ a ∈ A, (shortSieve U a)^2 := sum_congr rfl fun a ha => by
        simp only [w,Complex.norm_real,Real.norm_eq_abs,low_eq_short U (hL.trans_lt (mem_Ioc.mp ha).1),abs_neg,sq_abs]
      _ ≤ ∑ a ∈ Icc 1 B, (shortSieve U a)^2 := sum_le_sum_of_subset_of_nonneg
        (fun a ha => mem_Icc.mpr ⟨(hL.trans_lt (mem_Ioc.mp ha).1).le,(mem_Ioc.mp ha).2⟩) (fun a _ _ => sq_nonneg _)
      _ ≤ _ := shortSieve_l2 B U
  have rot := deep_prefix_sieve n B H k hn hH t ht hm A (fun a ha => (mem_Ioc.mp ha).2) v cut
  have same : (∑ a ∈ A, ‖F a‖^2) = ∑ a ∈ A, ‖∑ j ∈ range (min (2^k) (cut a)), v j*mode (j:ℤ) ((a:ℝ)*t)‖^2 :=
    sum_congr rfl fun a ha => by rw [min_eq_right (hcut a ha)]
  have e := (le_of_eq same).trans rot
  refine le_trans ?_ (mul_le_mul hmass (e.trans (mul_le_mul_of_nonneg_left (signal_energy n U (2^k)) (by positivity))) (sum_nonneg fun a _ => sq_nonneg _) (by exact (sum_nonneg fun a _ => sq_nonneg _).trans hmass))
  rw [by_short_factor]
  change ‖∑ a ∈ A, w a*F a‖^2 ≤ _
  have bound := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le A (fun a => w a*F a)) 2
  simp only [norm_mul] at bound
  exact bound.trans (sum_mul_sq_le_sq_mul_sq A (fun a => ‖w a‖) (fun a => ‖F a‖))

end
end GoldbachTransitionSquare
namespace GoldbachTransitionSquare
noncomputable section

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem core_pointwise_power : ∃ K : ℝ, 0<K ∧ ∀ n : ℕ, 2 ≤ n →
    ∀ t ∈ Set.Icc (0:ℝ) 1 ∩ deep n,
    ‖fourierSum n (core n (cutoffU n) (cutoffL n) (cutoffB n)) t‖^2 ≤ K*(n:ℝ)^(181/96:ℝ) := by
  let K := (389:ℝ)*386^2*(6+6*(1+8*Real.pi))*4*96^2
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  intro n hn t ht
  let B := cutoffB n
  let U := cutoffU n
  let L := cutoffL n
  let H := arcHeight n
  let P := n/(L+1)+1
  let k := Nat.log 2 P+1
  let N := 2^k
  let X := (n:ℝ)^(1/96:ℝ)
  have h1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1≤n by omega)
  have n0 : 0<(n:ℝ) := zero_lt_one.trans_le h1
  have hX : 1 ≤ X := Real.one_le_rpow h1 (by norm_num)
  have x0 : 0<X := zero_lt_one.trans_le hX
  have xp (a : ℕ) : X^a = (n:ℝ)^((a:ℝ)/96) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul n0.le]
    congr 1
    ring
  have xm {a b : ℕ} (h : a≤b) : X^a ≤ X^b := pow_le_pow_right₀ hX h
  have x96 : X^96 = n := by rw [xp]; norm_num
  have x32 : X^32 = (n:ℝ)^(1/3:ℝ) := by rw [xp]; norm_num
  have x24 : X^24 = (n:ℝ)^(1/4:ℝ) := by rw [xp]; norm_num
  have x6 : X^6 = (n:ℝ)^(1/16:ℝ) := by rw [xp]; norm_num
  have hB : (B:ℝ) ≤ X^32 := by rw [x32]; exact Nat.floor_le (by positivity)
  have hU : (U:ℝ) ≤ X^6 := by rw [x6]; exact Nat.floor_le (by positivity)
  have b1 : 1 ≤ B := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow h1 (by norm_num))
  have u1 : 1 ≤ U := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow h1 (by norm_num))
  have l1 : 1 ≤ L := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow h1 (by norm_num))
  have hlog := Real.log_nonneg h1
  have lg : Real.log n ≤ 96*X := (Real.log_le_rpow_div (x:=(n:ℝ)) n0.le (by norm_num : (0:ℝ)<1/96)).trans_eq (by dsimp [X]; ring)
  have logU := Real.log_le_log (by exact_mod_cast (show 0<U by omega)) (hU.trans ((xm (by decide : 6≤96)).trans x96.le))
  have lg0 : 0≤Real.log (U:ℝ) := Real.log_nonneg (by exact_mod_cast u1)
  have bud : rowBudget B U ≤ 389*X^33 := by
    have m := mul_le_mul hB (show 1+Real.log (U:ℝ) ≤ 97*X by linarith) (by linarith) (by positivity)
    have u := pow_le_pow_left₀ (Nat.cast_nonneg U) hU 2
    unfold rowBudget
    nlinarith [xm (by decide : 12≤33)]
  have HB : B ≤ H := by
    have ll := Nat.log_pos (by decide : 1<2) (by omega : 2≤n+2)
    change B ≤ 256*B*(Nat.log 2 (n+2))^2
    exact (show B≤256*B by omega).trans (Nat.le_mul_of_pos_right _ (by positivity))
  have hH : 0<H := (show 0<B from b1).trans_le HB
  have hH' : (0:ℝ)<H := by exact_mod_cast hH
  have lb : X^32 ≤ 2*(H:ℝ) := by
    have hf : X^32 < (B:ℝ)+1 := by rw [x32]; exact Nat.lt_floor_add_one _
    have e : (B:ℝ) ≤ H := by exact_mod_cast HB
    have b' : (1:ℝ) ≤ B := by exact_mod_cast b1
    linarith
  have nH : (n:ℝ)/H ≤ 2*X^64 := by
    rw [div_le_iff₀ hH',←x96]
    have h := mul_le_mul_of_nonneg_left lb (show 0≤X^64 by positivity)
    nlinarith only [h]
  have p1 : 1 ≤ P := Nat.succ_le_succ (Nat.zero_le _)
  have qbound : ((n/(L+1):ℕ):ℝ) ≤ X^72 := by
    have lf : X^24 ≤ ((L+1:ℕ):ℝ) := by rw [x24,Nat.cast_add,Nat.cast_one]; exact (Nat.lt_floor_add_one _).le
    have d := Nat.div_mul_le_self n (L+1)
    have d' : ((n/(L+1):ℕ):ℝ)*((L+1:ℕ):ℝ) ≤ n := by exact_mod_cast d
    have m := (mul_le_mul_of_nonneg_left lf (Nat.cast_nonneg (n/(L+1)))).trans d'
    have m' : ((n/(L+1):ℕ):ℝ)*X^24 ≤ X^72*X^24 := by
      rw [←x96] at m
      convert m using 1 <;> ring
    exact le_of_mul_le_mul_right m' (by positivity)
  have hPN : P ≤ N := (Nat.lt_pow_succ_log_self (by decide : 1<2) P).le
  have hNp : N ≤ 2*P := by
    dsimp [N,k]
    rw [pow_succ,Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self _ (by omega))
  have nb : (N:ℝ) ≤ 4*X^72 := by
    have e : (N:ℝ) ≤ 2*((n/(L+1):ℕ):ℝ)+2 := by
      have h : (N:ℝ) ≤ 2*(P:ℝ) := by exact_mod_cast hNp
      dsimp [P] at h; push_cast at h; linarith
    linarith [one_le_pow₀ hX (n:=72)]
  have kp : (k:ℝ)+1 ≤ 386*X := by
    have pm : P ≤ n+2 := by dsimp [P]; have := Nat.div_le_self n (L+1); omega
    have a : (Nat.log 2 P:ℝ) ≤ Nat.log 2 (n+2) := by exact_mod_cast Nat.log_mono_right pm
    dsimp [k]; push_cast
    linarith [log2_le_four_log n hn]
  have rad : 3/(min 1 ((H:ℝ)/n)) ≤ 6*X^64 := by
    rcases le_total 1 ((H:ℝ)/n) with ha | ha
    · rw [min_eq_left ha,div_one]; linarith [one_le_pow₀ hX (n:=64)]
    · rw [min_eq_right ha,div_div_eq_mul_div]
      calc
        _ = 3*((n:ℝ)/H) := by ring
        _ ≤ _ := by linarith
  have fac : 3/(min 1 ((H:ℝ)/n))+6*(1+2*Real.pi*(N:ℝ)) ≤ (6+6*(1+8*Real.pi))*X^72 := by
    have m := mul_le_mul_of_nonneg_left nb (show 0 ≤ 2*Real.pi by positivity)
    nlinarith [xm (by decide : 64≤72),one_le_pow₀ hX (n:=72)]
  have base := core_deep_pointwise n U L B H k (by omega) l1 hH hPN ht.1 ht.2
  change _ ≤ rowBudget B U * (((k:ℝ)+1)^2 * (3/(min 1 ((H:ℝ)/n))+6*(1+2*Real.pi*(N:ℝ))) * ((N:ℝ)*(Real.log n)^2)) at base
  apply base.trans
  calc
    _ ≤ (389*X^33)*((386*X)^2*((6+6*(1+8*Real.pi))*X^72)*((4*X^72)*(96*X)^2)) := by gcongr
    _ = _ := by
      have h : X^181 = (n:ℝ)^(181/96:ℝ) := xp 181
      rw [←h]; dsimp [K]; ring

end
end GoldbachTransitionSquare

namespace TypeTwoDiagonal
open Finset MeasureTheory
noncomputable section

def unitMeasure : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) 1)

def phase (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * (-(n:ℝ)*t):ℝ):ℂ)*Complex.I)

def coefficient (A : Set ℝ) (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  ∫ t, A.indicator (fun u => f u * phase n u) t ∂unitMeasure

def mass (A : Set ℝ) (f : ℝ → ℂ) : ℝ :=
  ∫ t, A.indicator (fun u => ‖f u‖^2) t ∂unitMeasure

/-- The interval Parseval argument follows muxkin, goldbach-proofs PR 2394,
    commit e8a1d429f5758874590eae79ce35af2ac63febd6 (Apache-2.0).
    Here the integrand is an arbitrary continuous function. -/
theorem fixed_bessel (A : Set ℝ) (hA : MeasurableSet A) (f : ℝ → ℂ)
    (hf : Continuous f) (S : Finset ℕ) :
    (∑ n ∈ S, ‖coefficient A f n‖^2) ≤ mass A f := by
  let g := A.indicator f
  have hg : MemLp g 2 unitMeasure := by
    apply MemLp.indicator hA.nullMeasurableSet
    apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).2
    exact ((hf.norm.pow 2).intervalIntegrable (μ := volume) 0 1).1
  have hc (n : ℕ) : fourierCoeffOn zero_lt_one g (n:ℤ) = coefficient A f n := by
    rw [fourierCoeffOn_eq_integral, sub_zero, one_div_one, one_smul, coefficient,
      intervalIntegral.integral_of_le zero_le_one]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    by_cases h : t ∈ A
    · simp only [g,Set.indicator_of_mem h,smul_eq_mul,fourier_coe_apply]
      rw [mul_comm]
      congr 2
      dsimp [phase]
      push_cast
      ring
    · simp [g,h]
  let T : Finset ℤ := S.map ⟨Int.ofNat, fun _ _ h => Int.ofNat_inj.mp h⟩
  have h := sum_le_hasSum T (fun i _ => sq_nonneg ‖fourierCoeffOn zero_lt_one g i‖)
    (hasSum_sq_fourierCoeffOn zero_lt_one hg)
  have en (t : ℝ) : ‖g t‖^2 = A.indicator (fun t => ‖f t‖^2) t := by
    by_cases ht : t ∈ A <;> simp [g,ht]
  simp only [T,sum_map,sub_zero,inv_one,one_smul,en] at h
  change (∑ n ∈ S, ‖fourierCoeffOn zero_lt_one g (n : ℤ)‖^2) ≤ _ at h
  simpa only [hc,intervalIntegral.integral_of_le zero_le_one,mass,unitMeasure] using h

def region (u v : ℝ → ℕ) (a b l r : ℕ) :=
  {t | u t ∈ Ico a b ∧ v t ∈ Ico l r}

def atom (u v : ℝ → ℕ) (i j : ℕ) := {t | u t = i ∧ v t = j}

theorem measurable_region {u v : ℝ → ℕ} (hu : Measurable u) (hv : Measurable v)
    (a b l r : ℕ) : MeasurableSet (region u v a b l r) :=
  (hu (Ico a b).measurableSet).inter (hv (Ico l r).measurableSet)

theorem measurable_atom {u v : ℝ → ℕ} (hu : Measurable u) (hv : Measurable v)
    (i j : ℕ) : MeasurableSet (atom u v i j) :=
  (hu (measurableSet_singleton i)).inter (hv (measurableSet_singleton j))

theorem atom_sum {E : Type*} [NormedAddCommGroup E] (u v : ℝ → ℕ) (g : ℝ → E)
    (a b l r : ℕ) (t : ℝ) :
    blockSum (fun i => blockSum (fun j => (atom u v i j).indicator g t) l r) a b =
      (region u v a b l r).indicator g t := by
  classical
  simp only [blockSum,Set.indicator,atom,Set.mem_setOf_eq,region]
  simp_rw [ite_and]
  classical
  simp [sum_ite_irrel,Finset.sum_ite_eq]

theorem integrate_atoms {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {u v : ℝ → ℕ} (hu : Measurable u) (hv : Measurable v) (g : ℝ → E)
    (hg : Integrable g unitMeasure) (a b l r : ℕ) :
    blockSum (fun i => blockSum (fun j => ∫ t, (atom u v i j).indicator g t ∂unitMeasure) l r) a b =
      ∫ t, (region u v a b l r).indicator g t ∂unitMeasure := by
  classical
  have hi i j := hg.indicator (measurable_atom hu hv i j)
  simp only [blockSum]
  simp_rw [←integral_finsetSum _ (fun j _ => hi _ j)]
  rw [←integral_finsetSum _ (fun _ _ => integrable_finsetSum _ (fun j _ => hi _ j))]
  exact integral_congr_ae (Filter.Eventually.of_forall (atom_sum u v g a b l r))

theorem continuous_unit_integrable {E : Type*} [NormedAddCommGroup E] {g : ℝ → E}
    (hg : Continuous g) : Integrable g unitMeasure :=
  (hg.intervalIntegrable (μ := volume) 0 1).1

theorem mass_nonneg (A : Set ℝ) (f : ℝ → ℂ) : 0 ≤ mass A f :=
  integral_nonneg (fun t => Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)

theorem mass_le_full (A : Set ℝ) (hA : MeasurableSet A) (f : ℝ → ℂ) (hf : Continuous f) :
    mass A f ≤ mass Set.univ f := by
  have hg := continuous_unit_integrable (hf.norm.pow 2)
  simp only [mass,Set.indicator_univ]
  apply integral_mono (hg.indicator hA) hg
  intro t
  by_cases ht : t ∈ A <;> simp [ht,sq_nonneg]

theorem moving_fourier (S : Finset ℕ) (f : ℝ → ℂ) (hf : Continuous f)
    {u v : ℝ → ℕ} (hu : Measurable u) (hv : Measurable v)
    (x y : ℕ → ℕ) (h k : ℕ) (hx : ∀ i ∈ S, x i ≤ 2^h) (hy : ∀ i ∈ S, y i ≤ 2^k) :
    (∑ i ∈ S, ‖coefficient (region u v 0 (x i) 0 (y i)) f i‖^2) ≤
      ((h:ℝ)+1)^2 * ((k:ℝ)+1)^2 * mass Set.univ f := by
  classical
  let F i a b := coefficient (atom u v a b) f i
  let E a b := mass (atom u v a b) f
  have pair i a b l r :
      blockSum (fun j => blockSum (F i j) l r) a b = coefficient (region u v a b l r) f i := by
    exact integrate_atoms hu hv _ (continuous_unit_integrable (hf.mul (by unfold phase; fun_prop))) a b l r
  have en a b l r :
      blockSum (fun j => blockSum (E j) l r) a b = mass (region u v a b l r) f :=
    integrate_atoms hu hv _ (continuous_unit_integrable (hf.norm.pow 2)) a b l r
  have ht := moving_rectangles S F E (fun a b => mass_nonneg _ _) x y h k 1 zero_le_one
    (fun T _ a b l r _ _ => by
      simp only [pair,en,one_mul]
      exact fixed_bessel _ (measurable_region hu hv ..) f hf T)
  simp only [pair,en,mul_one] at ht
  calc
    _ = ∑ i ∈ S, ‖coefficient (region u v 0 (min (2^h) (x i)) 0 (min (2^k) (y i))) f i‖^2 :=
      sum_congr rfl (fun i hi => by rw [min_eq_right (hx i hi),min_eq_right (hy i hi)])
    _ ≤ _ := ht.trans (mul_le_mul_of_nonneg_left
      (mass_le_full _ (measurable_region hu hv ..) f hf) (by positivity))

theorem moving_exterior (S : Finset ℕ) (f : ℝ → ℂ) (hf : Continuous f)
    {u v : ℝ → ℕ} (hu : Measurable u) (hv : Measurable v)
    (x y : ℕ → ℕ) (h k : ℕ) (hx : ∀ i ∈ S, x i ≤ 2^h) (hy : ∀ i ∈ S, y i ≤ 2^k) :
    (∑ i ∈ S, ‖coefficient (region u v 0 (x i) 0 (y i))ᶜ f i‖^2) ≤
      2*(1+((h:ℝ)+1)^2*((k:ℝ)+1)^2)*mass Set.univ f := by
  classical
  let A i := region u v 0 (x i) 0 (y i)
  have split i : coefficient (A i)ᶜ f i = coefficient Set.univ f i - coefficient (A i) f i := by
    change (∫ t, _ ∂unitMeasure) = _
    have hA : MeasurableSet (A i) := measurable_region hu hv ..
    have hg : Integrable (fun t => f t * phase i t) unitMeasure :=
      continuous_unit_integrable (hf.mul (show Continuous (phase i) by unfold phase; fun_prop))
    apply eq_sub_iff_add_eq.mpr
    rw [coefficient,coefficient,Set.indicator_univ,←integral_add (hg.indicator hA.compl) (hg.indicator hA)]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun t => by by_cases ht : t ∈ A i <;> simp [ht]))
  have pt i : ‖coefficient (A i)ᶜ f i‖^2 ≤ 2*(‖coefficient Set.univ f i‖^2+‖coefficient (A i) f i‖^2) := by
    rw [split]
    have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (coefficient Set.univ f i) (coefficient (A i) f i)) 2
    nlinarith only [h,sq_nonneg (‖coefficient Set.univ f i‖-‖coefficient (A i) f i‖)]
  have a := fixed_bessel Set.univ MeasurableSet.univ f hf S
  have b := moving_fourier S f hf hu hv x y h k hx hy
  calc
    _ ≤ _ := sum_le_sum (fun i _ => pt i)
    _ = 2*((∑ i ∈ S, ‖coefficient Set.univ f i‖^2)+(∑ i ∈ S, ‖coefficient (A i) f i‖^2)) := by
      rw [←mul_sum,sum_add_distrib]
    _ ≤ _ := by dsimp only [A]; linarith only [a,b]

end
end TypeTwoDiagonal

namespace TypeTwoDiagonal
open Finset MeasureTheory
noncomputable section

def centers (D : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 D) ×ˢ (range (D+1))).filter (fun c => c.2 ≤ c.1 ∧ c.2.Coprime c.1)

def offset (c : ℕ × ℕ) (t : ℝ) := |(c.1:ℝ)*t - c.2|

theorem center_info {D : ℕ} {c : ℕ × ℕ} (hc : c ∈ centers D) :
    1 ≤ c.1 ∧ c.1 ≤ D ∧ c.2 ≤ c.1 ∧ c.2.Coprime c.1 := by
  obtain ⟨h,ha,hc⟩ := mem_filter.mp hc
  obtain ⟨hq,-⟩ := mem_product.mp h
  exact ⟨(mem_Icc.mp hq).1,(mem_Icc.mp hq).2,ha,hc⟩

theorem center_mem {D q a : ℕ} (hq : 1 ≤ q) (hD : q ≤ D) (ha : a ≤ q) (hc : a.Coprime q) :
    (q,a) ∈ centers D :=
  mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨hq,hD⟩,mem_range.mpr (by omega)⟩,ha,hc⟩

/-- At the largest radius in the whole dyadic block, at most one reduced
    fraction can influence a given frequency. -/
theorem separated_center {D : ℕ} {R t : ℝ} (hR : 0 ≤ R) (hsep : 2*(D:ℝ)*R < 1)
    {c d : ℕ × ℕ} (hc : c ∈ centers D) (hd : d ∈ centers D)
    (htc : offset c t ≤ R) (htd : offset d t ≤ R) : c = d := by
  rcases c with ⟨q,a⟩
  rcases d with ⟨s,b⟩
  obtain ⟨hq,hqD,_,ha⟩ := center_info hc
  obtain ⟨hs,hsD,_,hb⟩ := center_info hd
  change 1 ≤ q at hq
  change q ≤ D at hqD
  change a.Coprime q at ha
  change s ≤ D at hsD
  change b.Coprime s at hb
  change |(q:ℝ)*t-a| ≤ R at htc
  change |(s:ℝ)*t-b| ≤ R at htd
  have hab : |(q*b:ℕ) - ((s*a:ℕ):ℝ)| < 1 := calc
    _ = |(s:ℝ)*((q:ℝ)*t-a)-(q:ℝ)*((s:ℝ)*t-b)| := by push_cast; ring_nf
    _ ≤ |(s:ℝ)*((q:ℝ)*t-a)| + |(q:ℝ)*((s:ℝ)*t-b)| := abs_sub _ _
    _ ≤ (D:ℝ)*R+(D:ℝ)*R := by
      have absv (v : ℕ) (z : ℝ) : |(v:ℝ)*z| = v*|z| := by
        simpa only [abs_of_nonneg (Nat.cast_nonneg v : (0:ℝ) ≤ v)] using abs_mul (v:ℝ) z
      rw [absv s,absv q]
      exact add_le_add (mul_le_mul (by exact_mod_cast hsD) htc (abs_nonneg _) (Nat.cast_nonneg D))
        (mul_le_mul (by exact_mod_cast hqD) htd (abs_nonneg _) (Nat.cast_nonneg D))
    _ < 1 := by linarith
  have eq : q*b = s*a := by
    rcases lt_trichotomy (q*b) (s*a) with hl|he|hg
    · have h : ((q*b+1:ℕ):ℝ) ≤ (s*a:ℕ) := by exact_mod_cast hl
      have := (abs_lt.mp hab).1
      push_cast at h this
      linarith
    · exact he
    · have h : ((s*a+1:ℕ):ℝ) ≤ (q*b:ℕ) := by exact_mod_cast hg
      have := (abs_lt.mp hab).2
      push_cast at h this
      linarith
  have qd : q ∣ s := ha.symm.dvd_mul_right.mp (eq ▸ Nat.dvd_mul_right q b)
  have sd : s ∣ q := hb.symm.dvd_mul_right.mp (eq.symm ▸ Nat.dvd_mul_right s a)
  have qe := Nat.dvd_antisymm qd sd
  subst s
  have ab : b = a := Nat.eq_of_mul_eq_mul_left hq eq
  simp [ab]

def near (D : ℕ) (R t : ℝ) := (centers D).filter (fun c => offset c t ≤ R)

def denLabel (D : ℕ) (R t : ℝ) :=
  D+1 - ∑ c ∈ near D R t, (D+1-c.1)

def distLabel (D : ℕ) (R t : ℝ) := ∑ c ∈ near D R t, offset c t

theorem near_singleton {D : ℕ} {R t : ℝ} (hR : 0 ≤ R) (hs : 2*(D:ℝ)*R < 1)
    {c : ℕ×ℕ} (hc : c ∈ near D R t) : near D R t = {c} := by
  ext d
  simp only [mem_singleton]
  constructor
  · intro hd
    obtain ⟨hd',hd''⟩ := mem_filter.mp hd
    obtain ⟨hc',hc''⟩ := mem_filter.mp hc
    exact separated_center hR hs hd' hc' hd'' hc''
  · rintro rfl
    exact hc

def heightRank (S : Finset ℕ) (r : ℕ → ℝ) (z : ℝ) := (S.filter (fun j => r j < z)).card
def heightCut (S : Finset ℕ) (r : ℕ → ℝ) (i : ℕ) := (S.filter (fun j => r j ≤ r i)).card

theorem rank_lt_iff {S : Finset ℕ} {r : ℕ → ℝ} {z : ℝ} {i : ℕ} (hi : i ∈ S) :
    heightRank S r z < heightCut S r i ↔ z ≤ r i := by
  constructor
  · contrapose!
    intro hz
    apply card_le_card
    intro j hj
    exact mem_filter.mpr ⟨(mem_filter.mp hj).1,lt_of_le_of_lt (mem_filter.mp hj).2 hz⟩
  · intro hz
    apply card_lt_card
    change S.filter (fun j => r j < z) ⊂ S.filter (fun j => r j ≤ r i)
    refine Finset.ssubset_iff_subset_ne.mpr ⟨fun j hj => mem_filter.mpr
      ⟨(mem_filter.mp hj).1,(mem_filter.mp hj).2.le.trans hz⟩,?_⟩
    intro eq
    have hm : i ∈ S.filter (fun j => r j ≤ r i) := mem_filter.mpr ⟨hi,le_rfl⟩
    rw [←eq] at hm
    exact (not_lt_of_ge hz) (mem_filter.mp hm).2

theorem offset_continuous (c : ℕ × ℕ) : Continuous (offset c) := by
  unfold offset
  fun_prop

theorem denLabel_measurable (D : ℕ) (R : ℝ) : Measurable (denLabel D R) := by
  classical
  change Measurable (fun t => D+1 - ∑ c ∈ near D R t, (D+1-c.1))
  simp only [near,sum_filter]
  apply Measurable.sub measurable_const
  apply Finset.measurable_fun_sum
  intro c _
  exact Measurable.ite (measurableSet_le (offset_continuous c).measurable measurable_const)
    measurable_const measurable_const

theorem distLabel_measurable (D : ℕ) (R : ℝ) : Measurable (distLabel D R) := by
  classical
  change Measurable (fun t => ∑ c ∈ near D R t, offset c t)
  simp only [near,sum_filter]
  apply Finset.measurable_fun_sum
  intro c _
  exact Measurable.ite (measurableSet_le (offset_continuous c).measurable measurable_const)
    (offset_continuous c).measurable measurable_const

theorem heightRank_measurable (S : Finset ℕ) (r : ℕ → ℝ) : Measurable (heightRank S r) := by
  classical
  change Measurable (fun z => (S.filter (fun j => r j < z)).card)
  simp only [card_eq_sum_ones,sum_filter]
  apply Finset.measurable_fun_sum
  intro j _
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const measurable_const

def rationalArcs (B : ℕ) (r : ℝ) : Set ℝ :=
  {t | ∃ c ∈ centers B, offset c t ≤ r}

/-- Within a separated envelope the denominator and the rank of the scaled
    distance give both moving boundaries, including ties and empty regions. -/
theorem arcs_as_rectangle {S : Finset ℕ} {B : ℕ → ℕ} {r : ℕ → ℝ} {D : ℕ} {R : ℝ}
    (hR : 0 ≤ R) (hs : 2*(D:ℝ)*R < 1) {i : ℕ} (hi : i ∈ S) (hb : B i ≤ D) (hr : r i ≤ R) :
    rationalArcs (B i) (r i) =
      region (denLabel D R) (fun t => heightRank S r (distLabel D R t))
        0 (B i+1) 0 (heightCut S r i) := by
  classical
  ext t
  change (∃ c ∈ centers (B i), offset c t ≤ r i) ↔ _ ∈ Ico 0 _ ∧ _ ∈ Ico 0 _
  simp only [mem_Ico,zero_le,true_and,Nat.lt_add_one_iff,rank_lt_iff hi]
  by_cases h : (near D R t).Nonempty
  · obtain ⟨c,hc⟩ := h
    obtain ⟨hcD,ht⟩ := mem_filter.mp hc
    obtain ⟨hq,hD,ha,hac⟩ := center_info hcD
    have ss := near_singleton hR hs hc
    simp only [denLabel,distLabel,ss,sum_singleton]
    have cancel : D+1-(D+1-c.1) = c.1 := by omega
    rw [cancel]
    constructor
    · rintro ⟨d,hd,hdt⟩
      obtain ⟨hp,hpB,hb',hbc⟩ := center_info hd
      have hdD : d ∈ centers D := center_mem hp (hpB.trans hb) hb' hbc
      have eq := separated_center hR hs hdD hcD (hdt.trans hr) ht
      simpa only [eq] using And.intro hpB hdt
    · rintro ⟨hB,ht⟩
      exact ⟨c,center_mem hq hB ha hac,ht⟩
  · have he := not_nonempty_iff_eq_empty.mp h
    simp only [denLabel,distLabel,he,sum_empty,Nat.sub_zero]
    constructor
    · rintro ⟨d,hd,hdt⟩
      obtain ⟨hp,hpB,hb',hbc⟩ := center_info hd
      exact (h ⟨d,mem_filter.mpr ⟨center_mem hp (hpB.trans hb) hb' hbc,hdt.trans hr⟩⟩).elim
    · rintro ⟨hbad,-⟩
      omega

theorem rational_exterior_bessel (S : Finset ℕ) (f : ℝ → ℂ) (hf : Continuous f)
    (B : ℕ → ℕ) (r : ℕ → ℝ) (D : ℕ) (R : ℝ) (hR : 0 ≤ R) (hs : 2*(D:ℝ)*R < 1)
    (hb : ∀ i ∈ S, B i ≤ D) (hr : ∀ i ∈ S, r i ≤ R)
    (h k : ℕ) (hh : D+1 ≤ 2^h) (hk : S.card ≤ 2^k) :
    (∑ i ∈ S, ‖coefficient (rationalArcs (B i) (r i))ᶜ f i‖^2) ≤
      2*(1+((h:ℝ)+1)^2*((k:ℝ)+1)^2)*mass Set.univ f := by
  refine (le_of_eq (sum_congr rfl (fun i hi => ?_))).trans
    (moving_exterior S f hf (denLabel_measurable D R)
      ((heightRank_measurable S r).comp (distLabel_measurable D R))
      (fun i => B i+1) (heightCut S r) h k
      (fun i hi => (Nat.succ_le_succ (hb i hi)).trans hh)
      (fun i _ => (card_le_card (filter_subset ..)).trans hk))
  rw [arcs_as_rectangle hR hs hi (hb i hi) (hr i hi)]
  rfl

end
end TypeTwoDiagonal

namespace TypeTwoDiagonal
open Finset GoldbachTransitionSquare
noncomputable section

def arcRadius (n : ℕ) : ℝ := (arcHeight n : ℝ)/n

theorem actual_arcs (n : ℕ) (hn : 0<n) :
    deep n = (rationalArcs (cutoffB n) (arcRadius n))ᶜ := by
  apply congrArg Set.compl
  ext t
  have test (q a : ℕ) (hq : 0<q) :
      |t-(a:ℝ)/q| ≤ (arcHeight n:ℝ)/((q:ℝ)*n) ↔ offset (q,a) t ≤ arcRadius n := by
    have pos : (0:ℝ)<q := by exact_mod_cast hq
    have eq : (q:ℝ)*(t-(a:ℝ)/q)=(q:ℝ)*t-a := by field_simp
    have scale : offset (q,a) t = (q:ℝ)*|t-(a:ℝ)/q| := by
      unfold offset
      change |(q:ℝ)*t-a| = _
      rw [←eq,abs_mul,abs_of_pos pos]
    rw [scale,arcRadius,le_div_iff₀ (mul_pos pos (by exact_mod_cast hn)),
      le_div_iff₀ (by exact_mod_cast hn : (0:ℝ)<n)]
    constructor <;> intro h <;> linarith only [h]
  change (∃ q a : ℕ, 1≤q ∧ q≤cutoffB n ∧ a≤q ∧ a.Coprime q ∧
    |t-(a:ℝ)/q| ≤ (arcHeight n:ℝ)/((q:ℝ)*n)) ↔ _
  constructor
  · rintro ⟨q,a,hq,hb,ha,hac,h⟩
    exact ⟨(q,a),center_mem hq hb ha hac,(test q a hq).mp h⟩
  · rintro ⟨⟨q,a⟩,hc,h⟩
    obtain ⟨hq,hb,ha,hac⟩ := center_info hc
    exact ⟨q,a,hq,hb,ha,hac,(test q a hq).mpr h⟩

def octave (k : ℕ) := (2^k : ℕ)^3

theorem octave_eq (k : ℕ) : octave k = 2^(3*k) := by
  simp [octave,pow_mul,Nat.mul_comm]

theorem block_log (k n : ℕ) (hn : n ≤ 8*octave k) :
    Nat.log 2 (n+2) ≤ 3*k+4 := by
  have h := Nat.log_mono_right (b:=2)
    (show n+2 ≤ 2^(3*k+4) by
      rw [pow_add,←octave_eq k]
      have ho : 0 < octave k := by unfold octave; positivity
      omega)
  simpa [Nat.log_pow] using h

theorem block_base (k n : ℕ) (hn : n ≤ 8*octave k) : cutoffB n ≤ 2*2^k := by
  have hn' : (n:ℝ) ≤ ((2*(2^k:ℕ):ℕ):ℝ)^3 := by
    exact_mod_cast (show n ≤ (2*2^k)^3 from hn.trans_eq (by unfold octave; ring))
  have h := Real.rpow_le_rpow (Nat.cast_nonneg n) hn' (by norm_num : (0:ℝ)≤1/3)
  rw [←Real.rpow_natCast_mul (by positivity)] at h
  norm_num at h
  exact_mod_cast (Nat.floor_le (by positivity : 0 ≤ (n:ℝ)^(1/3:ℝ))).trans h

theorem octave_separation (k : ℕ) (hk : 32 ≤ k) : 2048*(3*k+4)^2 < 2^k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [pow_succ 2 k]
    have h : (3*(k+1)+4)^2 ≤ 2*(3*k+4)^2 := by
      nlinarith [Nat.zero_le ((k-32)^2),Nat.mul_le_mul_right k hk]
    omega

theorem block_bessel (k : ℕ) (hk : 32 ≤ k) (S : Finset ℕ)
    (hS : ∀ n ∈ S, octave k ≤ n ∧ n ≤ 8*octave k) (f : ℝ → ℂ) (hf : Continuous f) :
    (∑ n ∈ S, ‖coefficient (deep n) f n‖^2) ≤
      2*(1+(((k+2:ℕ):ℝ)+1)^2*(((3*k+4:ℕ):ℝ)+1)^2)*mass Set.univ f := by
  let D := 2*2^k
  let R : ℝ := (256*(D:ℝ)*(3*k+4)^2)/(octave k:ℝ)
  have ho : 0 < octave k := by unfold octave; positivity
  have hor : (0:ℝ)<octave k := by exact_mod_cast ho
  have hR : 0≤R := by dsimp [R,D]; positivity
  have sep : 2*(D:ℝ)*R < 1 := by
    have h : (2048:ℝ)*(3*(k:ℝ)+4)^2 < (2:ℝ)^k := by exact_mod_cast octave_separation k hk
    have hx : 0 < (2:ℝ)^k := by positivity
    have hs := mul_lt_mul_of_pos_right h (sq_pos_of_pos hx)
    dsimp [R]
    rw [←mul_div_assoc,div_lt_one hor]
    dsimp [D,octave]
    push_cast
    nlinarith only [hs,mul_nonneg (sq_nonneg (3*(k:ℝ)+4)) (sq_nonneg ((2:ℝ)^k))]
  have hB i hi : cutoffB i ≤ D := block_base k i (hS i hi).2
  have hr (i : ℕ) (hi : i ∈ S) : arcRadius i ≤ R := by
    obtain ⟨h0,h1⟩ := hS i hi
    have H : (arcHeight i:ℝ) ≤ 256*(D:ℝ)*(3*k+4)^2 := by
      unfold arcHeight
      push_cast
      gcongr
      · exact_mod_cast hB i hi
      · exact_mod_cast block_log k i h1
    exact div_le_div₀ (by positivity) H hor (by exact_mod_cast h0)
  have hh : D+1 ≤ 2^(k+2) := by
    dsimp [D]
    rw [pow_add]
    have : 0<2^k := by positivity
    omega
  have subset : S ⊆ range (8*octave k+1) := fun i hi => mem_range.mpr (by have := (hS i hi).2; omega)
  have card := card_le_card subset
  rw [card_range] at card
  have card' : S.card ≤ 2^(3*k+4) := by
    rw [pow_add,←octave_eq]
    omega
  refine (le_of_eq (sum_congr rfl (fun n hn => ?_))).trans
    (rational_exterior_bessel S f hf cutoffB arcRadius D R hR sep hB hr (k+2) (3*k+4) hh card')
  rw [actual_arcs n (ho.trans_le (hS n hn).1)]

end
end TypeTwoDiagonal

namespace TypeTwoDiagonal
open Finset GoldbachTransitionSquare
noncomputable section

def crossedMultiples (N x y : ℕ) : Finset ℕ :=
  (Ioc (min x y) (max x y)).biUnion (fun d => (Ioc 0 N).filter (fun m => d ∣ m))

theorem same_side {N m x y : ℕ} (hm : m ∈ Ioc 0 N) (hout : m ∉ crossedMultiples N x y)
    {d : ℕ} (hd : d ∣ m) : d ≤ x ↔ d ≤ y := by
  have h : d ∉ Ioc (min x y) (max x y) :=
    fun hh => hout (mem_biUnion.mpr ⟨d,hh,mem_filter.mpr ⟨hm,hd⟩⟩)
  simp only [mem_Ioc] at h
  omega

def bucket (M A z : ℕ) := M*z/A

theorem bucket_diameter {M A x y : ℕ} (hA : 0<A) (eq : bucket M A x = bucket M A y) :
    M*(max x y - min x y) ≤ A := by
  have one {a b : ℕ} (hab : a ≤ b) (he : M*b/A = M*a/A) : M*(b-a) ≤ A := by
    have ht : M*b < M*b/A*A+A := Nat.lt_div_mul_add hA
    rw [he] at ht
    have hl := Nat.div_mul_le_self (M*a) A
    rw [Nat.mul_sub]
    omega
  rcases le_total x y with h|h
  · rw [max_eq_right h,min_eq_left h]
    exact one h eq.symm
  · rw [max_eq_left h,min_eq_right h]
    exact one h eq

theorem crossed_count (N M A x y : ℕ) (hA : 0<A) (hx : A≤x) (hy : A≤y)
    (eq : bucket M A x = bucket M A y) : M*(crossedMultiples N x y).card ≤ N := by
  let l := min x y
  let u := max x y
  have bound : (crossedMultiples N x y).card ≤ (u-l)*(N/(l+1)) := calc
    _ ≤ ∑ d ∈ Ioc l u, ((Ioc 0 N).filter (fun m => d ∣ m)).card := card_biUnion_le
    _ ≤ ∑ _ ∈ Ioc l u, N/(l+1) := by
      apply sum_le_sum
      intro d hd
      rw [Nat.Ioc_filter_dvd_card_eq_div]
      exact Nat.div_le_div_left (mem_Ioc.mp hd).1 (by omega)
    _ = _ := by simp
  have diam := bucket_diameter hA eq
  have small : A ≤ l+1 := by dsimp [l]; omega
  calc
    _ ≤ M*((u-l)*(N/(l+1))) := Nat.mul_le_mul_left _ bound
    _ = (M*(u-l))*(N/(l+1)) := (Nat.mul_assoc ..).symm
    _ ≤ (l+1)*(N/(l+1)) := Nat.mul_le_mul_right _ (diam.trans small)
    _ ≤ N := by simpa [Nat.mul_comm] using Nat.div_mul_le_self N (l+1)

structure BandParams where
  top : ℕ
  mob : ℕ
  lo : ℕ
  hi : ℕ
  primeLo : ℕ

def actualParams (n : ℕ) : BandParams := ⟨n,cutoffU n,cutoffL n,cutoffB n,n.sqrt⟩

def padded (P : BandParams) (m : ℕ) : ℝ :=
  if m ≤ P.top then band P.mob P.lo P.hi (fun q => if P.primeLo < q then primeWeight q else 0) m else 0

theorem padded_actual (n m : ℕ) (hm : m ≤ n) :
    padded (actualParams n) m = core n (cutoffU n) (cutoffL n) (cutoffB n) m := by
  simp only [padded,actualParams,hm,ite_eq_left]
  rfl

def changes (N : ℕ) (P Q : BandParams) :=
  Ioc (min P.top Q.top) (max P.top Q.top) ∪ crossedMultiples N P.mob Q.mob ∪
    crossedMultiples N P.lo Q.lo ∪ crossedMultiples N P.hi Q.hi ∪ crossedMultiples N P.primeLo Q.primeLo

theorem padded_eq_off_changes {N m : ℕ} (P Q : BandParams) (hmN : m ≤ N)
    (hout : m ∉ changes N P Q) : padded P m = padded Q m := by
  classical
  by_cases h0 : m=0
  · subst m
    simp [padded,band]
  have hm : m ∈ Ioc 0 N := mem_Ioc.mpr ⟨Nat.pos_of_ne_zero h0,hmN⟩
  simp only [changes,mem_union,not_or] at hout
  obtain ⟨⟨⟨⟨ht,hu⟩,hl⟩,hb⟩,hp⟩ := hout
  have top : m ≤ P.top ↔ m ≤ Q.top := by simp only [mem_Ioc] at ht; omega
  unfold padded
  rw [if_congr top rfl rfl]
  by_cases hq : m ≤ Q.top
  · simp only [if_pos hq,band]
    have membership (a : ℕ) (ha : a ∈ m.divisors) :
        (P.lo < a ∧ a ≤ P.hi ∧ P.mob < m/a) ↔ (Q.lo < a ∧ a ≤ Q.hi ∧ Q.mob < m/a) := by
      have div := Nat.dvd_of_mem_divisors ha
      have lo := same_side hm hl div
      have hi := same_side hm hb div
      have mo := same_side hm hu (Nat.div_dvd_of_dvd div)
      omega
    rw [filter_congr membership]
    apply sum_congr rfl
    intro a ha
    have div := Nat.dvd_of_mem_divisors (mem_filter.mp ha).1
    have weights : lowMoebiusWeight P.mob a = lowMoebiusWeight Q.mob a := by
      unfold lowMoebiusWeight
      congr 1
      apply filter_congr
      intro d hd
      have h := same_side hm hu ((Nat.dvd_of_mem_divisors hd).trans div)
      omega
    have p := same_side hm hp (Nat.div_dvd_of_dvd div)
    rw [weights,if_congr (by omega : P.primeLo < m/a ↔ Q.primeLo < m/a) rfl rfl]
  · simp [hq]

def Below (P Q : BandParams) : Prop := P.top ≤ Q.top ∧ P.mob ≤ Q.mob ∧ P.lo ≤ Q.lo ∧
  P.hi ≤ Q.hi ∧ P.primeLo ≤ Q.primeLo

def buckets (M : ℕ) (A P : BandParams) : BandParams :=
  ⟨bucket M A.top P.top,bucket M A.mob P.mob,bucket M A.lo P.lo,
    bucket M A.hi P.hi,bucket M A.primeLo P.primeLo⟩

def label (M : ℕ) (A P : BandParams) :=
  let b := buckets M A P
  b.top+b.mob+b.lo+b.hi+b.primeLo

theorem ordered_buckets {M : ℕ} {A P Q : BandParams} (h : Below P Q)
    (eq : label M A P = label M A Q) : buckets M A P = buckets M A Q := by
  have mono (d : ℕ) {x y : ℕ} (hxy : x≤y) : bucket M d x ≤ bucket M d y :=
    Nat.div_le_div_right (Nat.mul_le_mul_left _ hxy)
  obtain ⟨t,u,l,b,p⟩ := h
  have t' := mono A.top t
  have u' := mono A.mob u
  have l' := mono A.lo l
  have b' := mono A.hi b
  have p' := mono A.primeLo p
  dsimp [label,buckets] at eq
  unfold buckets
  congr 1 <;> omega

theorem actual_ordered {n m : ℕ} (h : n ≤ m) : Below (actualParams n) (actualParams m) := by
  refine ⟨h,?_,?_,?_,Nat.sqrt_le_sqrt h⟩ <;>
    exact Nat.floor_mono (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast h) (by norm_num))

theorem changes_count {N M : ℕ} (A P Q : BandParams) (hP : Below A P) (hQ : Below A Q)
    (hpos : Below ⟨1,1,1,1,1⟩ A) (hN : A.top ≤ N) (eq : buckets M A P = buckets M A Q) :
    M*(changes N P Q).card ≤ 5*N := by
  have eTop := congrArg BandParams.top eq
  have eMob := congrArg BandParams.mob eq
  have eLo := congrArg BandParams.lo eq
  have eHi := congrArg BandParams.hi eq
  have ePrime := congrArg BandParams.primeLo eq
  obtain ⟨ht,hu,hl,hb,hp⟩ := hpos
  have h0 := (bucket_diameter ht eTop).trans hN
  have h1 := crossed_count N M A.mob P.mob Q.mob hu hP.2.1 hQ.2.1 eMob
  have h2 := crossed_count N M A.lo P.lo Q.lo hl hP.2.2.1 hQ.2.2.1 eLo
  have h3 := crossed_count N M A.hi P.hi Q.hi hb hP.2.2.2.1 hQ.2.2.2.1 eHi
  have h4 := crossed_count N M A.primeLo P.primeLo Q.primeLo hp hP.2.2.2.2 hQ.2.2.2.2 ePrime
  have union (s t : Finset ℕ) : M*(s ∪ t).card ≤ M*s.card + M*t.card :=
    (Nat.mul_le_mul_left M (card_union_le s t)).trans_eq (Nat.mul_add ..)
  unfold changes
  calc
    _ ≤ _ := union _ _
    _ ≤ _ := Nat.add_le_add_right (union _ _) _
    _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_right (union _ _) _) _
    _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (union _ _) _) _) _
    _ ≤ 5*N := by rw [Nat.card_Ioc]; omega

theorem frozen_l2 {N M : ℕ} (P Q : BandParams) {W : ℝ}
    (hp : ∀ m ≤ N, |padded P m| ≤ W) (hq : ∀ m ≤ N, |padded Q m| ≤ W)
    (small : M*(changes N P Q).card ≤ 5*N) :
    (M:ℝ)*(∑ m ∈ range (N+1), (padded P m-padded Q m)^2) ≤ 20*N*W^2 := by
  classical
  let ch := changes N P Q
  have step (m : ℕ) (hm : m ∈ range (N+1)) :
      (padded P m - padded Q m)^2 ≤ if m ∈ ch then 4*W^2 else 0 := by
    have mn : m ≤ N := Nat.le_of_lt_succ (mem_range.mp hm)
    split_ifs with hc
    · have h := (abs_sub _ _).trans (add_le_add (hp m mn) (hq m mn))
      have hh := pow_le_pow_left₀ (abs_nonneg _) h 2
      rw [sq_abs] at hh
      linarith only [hh]
    · rw [padded_eq_off_changes P Q mn hc]
      simp
  have count : ((range (N+1)).filter (fun m => m ∈ ch)).card ≤ ch.card :=
    card_le_card (fun m hm => (mem_filter.mp hm).2)
  have sumBd := sum_le_sum step
  rw [←sum_filter,sum_const,nsmul_eq_mul] at sumBd
  have small' : (M:ℝ) * (ch.card:ℝ) ≤ 5*(N:ℝ) := by exact_mod_cast small
  have cmp : (M:ℝ) * (((range (N+1)).filter (fun m => m ∈ ch)).card:ℝ) ≤ M*(ch.card:ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast count) (Nat.cast_nonneg M)
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left sumBd (Nat.cast_nonneg M)
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right (cmp.trans small') (sq_nonneg W)]

end
end TypeTwoDiagonal

namespace TypeTwoDiagonal
open Finset MeasureTheory
noncomputable section

def clip (T : ℝ) (z : ℂ) := ((T / max T ‖z‖ : ℝ):ℂ)*z

theorem clip_continuous {T : ℝ} (hT : 0<T) : Continuous (clip T) := by
  unfold clip
  apply Continuous.mul _ continuous_id
  apply Complex.continuous_ofReal.comp
  exact continuous_const.div (continuous_const.max continuous_norm) (fun z => (hT.trans_le (le_max_left ..)).ne')

theorem clip_bounds {T : ℝ} (hT : 0<T) (z : ℂ) :
    ‖clip T z‖ ≤ T ∧ ‖clip T z‖ ≤ ‖z‖ := by
  have hd : 0 < max T ‖z‖ := hT.trans_le (le_max_left ..)
  rw [clip,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hT.le hd.le)]
  constructor
  · rw [div_mul_eq_mul_div,div_le_iff₀ hd]
    gcongr
    exact le_max_right ..
  · exact mul_le_of_le_one_left (norm_nonneg _) ((div_le_one hd).mpr (le_max_left ..))

theorem clip_near {T : ℝ} (hT : 0<T) {x y : ℂ} (hx : ‖x‖ ≤ T) :
    ‖x - clip T y‖ ≤ 2*‖x-y‖ := by
  by_cases hy : ‖y‖ ≤ T
  · simp only [clip,max_eq_left hy,div_self hT.ne',Complex.ofReal_one,one_mul]
    linarith [norm_nonneg (x-y)]
  have p : 0 < ‖y‖ := hT.trans (lt_of_not_ge hy)
  have c : y - clip T y = ((1-T/‖y‖ : ℝ):ℂ)*y := by
    simp only [clip,max_eq_right (lt_of_not_ge hy).le,Complex.ofReal_sub,Complex.ofReal_one]
    ring
  have d : ‖y - clip T y‖ = ‖y‖ - T := by
    rw [c,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg
      (sub_nonneg.mpr ((div_le_one p).mpr (lt_of_not_ge hy).le))]
    field_simp
  have h₁ := dist_triangle x y (clip T y)
  simp only [dist_eq_norm] at h₁
  have h₂ := norm_sub_norm_le y x
  rw [norm_sub_rev y x] at h₂
  linarith

theorem mass_clipped_square {T : ℝ} (hT : 0<T) (f : ℝ → ℂ) (hf : Continuous f) :
    mass Set.univ (fun t => (clip T (f t))^2) ≤ T^2*mass Set.univ f := by
  have hc := (clip_continuous hT).comp hf
  simp only [mass,Set.indicator_univ,←integral_const_mul]
  apply integral_mono (continuous_unit_integrable ((hc.pow 2).norm.pow 2))
    (continuous_unit_integrable (continuous_const.mul (hf.norm.pow 2)))
  intro t
  change ‖(clip T (f t))^2‖^2 ≤ T^2*‖f t‖^2
  rw [norm_pow]
  obtain ⟨a,b⟩ := clip_bounds hT (f t)
  have p := pow_le_pow_left₀ (norm_nonneg _) a 2
  have q := pow_le_pow_left₀ (norm_nonneg _) b 2
  calc
    _ = ‖clip T (f t)‖^2 * ‖clip T (f t)‖^2 := by ring
    _ ≤ _ := mul_le_mul p q (sq_nonneg _) (sq_nonneg _)

theorem clipped_coefficient_error (A : Set ℝ) (hA : MeasurableSet A)
    (x y : ℝ → ℂ) (hx : Continuous x) (hy : Continuous y) (n : ℕ) {T s : ℝ}
    (hT : 0<T) (hs : 0<s) (bound : ∀ t ∈ Set.Ioc (0:ℝ) 1, t ∈ A → ‖x t‖ ≤ T) :
    ‖coefficient A (fun t => (x t)^2) n - coefficient A (fun t => (clip T (y t))^2) n‖ ≤
      2*s*mass Set.univ (fun t => x t-y t) + s⁻¹*(mass Set.univ x + mass Set.univ y) := by
  let g t := clip T (y t)
  have hg : Continuous g := (clip_continuous hT).comp hy
  have e : Continuous (phase n) := by unfold phase; fun_prop
  have hfun t (ht : t ∈ Set.Ioc (0:ℝ) 1) (ha : t ∈ A) :
      ‖((x t)^2-(g t)^2)*phase n t‖ ≤ 2*s*‖x t-y t‖^2 + s⁻¹*(‖x t‖^2+‖y t‖^2) := by
    have hp : ‖phase n t‖ = 1 := GoldbachTransitionSquare.norm_phase _
    rw [sq_sub_sq,norm_mul,norm_mul,hp,mul_one]
    have h1 := clip_near hT (y:=y t) (bound t ht ha)
    have h2 : ‖x t + g t‖ ≤ ‖x t‖ + ‖y t‖ :=
      (norm_add_le (x t) (g t)).trans (add_le_add le_rfl (clip_bounds hT (y t)).2)
    have yh := GoldbachTransitionFourier.scaled_young (x:=‖x t-y t‖) (y:=‖x t‖) hs
    have zh := GoldbachTransitionFourier.scaled_young (x:=‖x t-y t‖) (y:=‖y t‖) hs
    nlinarith only [mul_le_mul h1 h2 (norm_nonneg _) (by positivity : 0≤2*‖x t-y t‖),yh,zh,
      mul_le_mul h2 h1 (norm_nonneg _) (by positivity : 0≤‖x t‖+‖y t‖)]
  have hxi : Integrable (A.indicator (fun t => x t^2*phase n t)) unitMeasure :=
    (continuous_unit_integrable ((hx.pow 2).mul e)).indicator hA
  have hgi : Integrable (A.indicator (fun t => g t^2*phase n t)) unitMeasure :=
    (continuous_unit_integrable ((hg.pow 2).mul e)).indicator hA
  let b t := 2*s*‖x t-y t‖^2 + s⁻¹*(‖x t‖^2+‖y t‖^2)
  have hb : Continuous b := by dsimp [b]; fun_prop
  unfold coefficient
  change ‖(∫ t, A.indicator (fun u => x u ^ 2 * phase n u) t ∂unitMeasure) -
           ∫ t, A.indicator (fun u => g u ^ 2 * phase n u) t ∂unitMeasure‖ ≤ _
  rw [← integral_sub hxi hgi]
  refine (norm_integral_le_integral_norm _).trans ?_
  have step : (∫ t, ‖A.indicator (fun u => x u^2 * phase n u) t -
      A.indicator (fun u => g u^2 * phase n u) t‖ ∂unitMeasure) ≤ ∫ t,b t ∂unitMeasure := by
    apply integral_mono_ae (hxi.sub hgi).norm (continuous_unit_integrable hb)
    filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioc (a:=(0:ℝ)) (b:=1))] with t ht
    change ‖A.indicator (fun u => x u^2*phase n u) t - A.indicator (fun u => g u^2*phase n u) t‖ ≤ b t
    by_cases h : t ∈ A
    · simp only [Set.indicator_of_mem h,←sub_mul]
      exact hfun t ht h
    · simp only [Set.indicator_of_notMem h,sub_self,norm_zero]
      dsimp [b]
      positivity
  refine step.trans_eq ?_
  simp only [mass,Set.indicator_univ,b]
  rw [integral_add,integral_const_mul,integral_const_mul,integral_add] <;>
    apply continuous_unit_integrable <;> fun_prop

end
end TypeTwoDiagonal

namespace TypeTwoDiagonal
open Finset MeasureTheory GoldbachTransitionSquare
noncomputable section

def spec (N : ℕ) (P : BandParams) := fourierSum N (padded P)

theorem spec_actual {n N : ℕ} (hn : n ≤ N) :
    spec N (actualParams n) = fourierSum n (core n (cutoffU n) (cutoffL n) (cutoffB n)) := by
  funext t
  unfold spec fourierSum
  rw [←sum_subset (s₁:=range (n+1)) (s₂:=range (N+1)) (range_mono (Nat.succ_le_succ hn)) (by
    intro i hi ho
    have h : ¬i ≤ n := by simpa only [mem_range,Nat.lt_succ_iff] using ho
    simp [padded,actualParams,h])]
  exact sum_congr rfl (fun i hi => by rw [padded_actual n i (Nat.le_of_lt_succ (mem_range.mp hi))])

theorem mass_spec (N : ℕ) (P : BandParams) :
    mass Set.univ (spec N P) = ∑ m ∈ range (N+1), (padded P m)^2 := by
  simpa only [mass,Set.indicator_univ,spec,unitMeasure,fourierSum,GoldbachTransitionSquare.phase,intervalIntegral.integral_of_le zero_le_one]
    using GoldbachTransitionFourier.continuous_parseval N (padded P)

theorem mass_diff (N : ℕ) (P Q : BandParams) :
    mass Set.univ (fun t => spec N P t-spec N Q t) =
      ∑ m ∈ range (N+1), (padded P m - padded Q m)^2 := by
  have eq : (fun t => spec N P t-spec N Q t) = fourierSum N (fun m => padded P m-padded Q m) :=
    funext (fun t => (fourierSum_sub ..).symm)
  rw [eq]
  simpa only [mass,Set.indicator_univ,unitMeasure,fourierSum,GoldbachTransitionSquare.phase,intervalIntegral.integral_of_le zero_le_one]
    using GoldbachTransitionFourier.continuous_parseval N (fun m => padded P m-padded Q m)

theorem spec_energy (N : ℕ) (P : BandParams) {W : ℝ} (h : ∀ m ≤ N, |padded P m| ≤ W) :
    mass Set.univ (spec N P) ≤ ((N:ℝ)+1)*W^2 := by
  rw [mass_spec]
  calc
    _ ≤ ∑ _m ∈ range (N+1), W^2 := sum_le_sum fun m hm => by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (h m (Nat.le_of_lt_succ (mem_range.mp hm))) 2
    _ = _ := by simp

theorem coeff_core {n N : ℕ} (hn : n ≤ N) :
    coreValue n = coefficient (deep n) (fun t => (spec N (actualParams n) t)^2) n := by
  rw [spec_actual hn]
  unfold coreValue pairIntegral coefficient
  rw [intervalIntegral.integral_of_le zero_le_one]
  simp only [pow_two]
  rfl

theorem sq_triangle (a b : ℂ) : ‖a‖^2 ≤ 2*(‖a-b‖^2+‖b‖^2) := by
  have tri := norm_add_le (a-b) b
  rw [sub_add_cancel] at tri
  have h := pow_le_pow_left₀ (norm_nonneg _) tri 2
  nlinarith only [h,sq_nonneg (‖a-b‖-‖b‖)]

def logCost (k : ℕ) : ℝ := 2*(1+(((k+2:ℕ):ℝ)+1)^2*(((3*k+4:ℕ):ℝ)+1)^2)

def freezeCost (N M : ℕ) (W s : ℝ) :=
  2*s*(20*N*W^2/M) + s⁻¹*(2*((N:ℝ)+1)*W^2)

/-- The moving diagonal is estimated on a whole class by one clipped
    spectrum. Only the coefficient error is paid separately at each target. -/
theorem cell_moment (k M N : ℕ) (hk : 32 ≤ k) (hM : 0<M) (S : Finset ℕ)
    (hS : ∀ i ∈ S, octave k ≤ i ∧ i ≤ 8*octave k) (hN : ∀ i ∈ S, i ≤ N)
    (P : BandParams) (T W s : ℝ) (hT : 0<T) (hs : 0<s)
    (hW : ∀ m ≤ N, |padded P m| ≤ W)
    (hWn : ∀ i ∈ S, ∀ m ≤ N, |padded (actualParams i) m| ≤ W)
    (hchanges : ∀ i ∈ S, M*(changes N (actualParams i) P).card ≤ 5*N)
    (hcap : ∀ i ∈ S, ∀ t ∈ Set.Ioc (0:ℝ) 1, t ∈ deep i → ‖spec N (actualParams i) t‖ ≤ T) :
    (∑ i ∈ S, ‖coreValue i‖^2) ≤
      2*(S.card:ℝ)*(freezeCost N M W s)^2 + 2*logCost k*T^2*(((N:ℝ)+1)*W^2) := by
  let y := spec N P
  let g := fun t => (clip T (y t))^2
  have hy : Continuous y := continuous_fourierSum ..
  have hg : Continuous g := ((clip_continuous hT).comp hy).pow 2
  have ey := spec_energy N P hW
  have hM' : (0:ℝ)<M := by exact_mod_cast hM
  have err i (hi : i∈S) : ‖coreValue i-coefficient (deep i) g i‖ ≤ freezeCost N M W s := by
    let A := actualParams i
    have ex := spec_energy N A (hWn i hi)
    have d : mass Set.univ (fun t => spec N A t-y t) ≤ 20*N*W^2/M := by
      rw [le_div_iff₀ hM',mul_comm,mass_diff]
      exact frozen_l2 A P (hWn i hi) hW (hchanges i hi)
    have hd : MeasurableSet (deep i) := (wide_measurable ..).compl
    rw [coeff_core (hN i hi)]
    apply (clipped_coefficient_error (deep i) hd (spec N A) y (continuous_fourierSum ..)
      hy i hT hs (hcap i hi)).trans
    apply add_le_add (mul_le_mul_of_nonneg_left d (by positivity)) (mul_le_mul_of_nonneg_left _ (by positivity))
    change mass Set.univ (spec N A)+mass Set.univ y ≤ _
    linarith only [ex,ey]
  have sumB := block_bessel k hk S hS g hg
  change _ ≤ logCost k*mass Set.univ g at sumB
  have L : 0 ≤ logCost k := by unfold logCost; positivity
  have massB := (mass_clipped_square hT y hy).trans (mul_le_mul_of_nonneg_left ey (sq_nonneg T))
  calc
    _ ≤ ∑ i ∈ S, 2*((freezeCost N M W s)^2+‖coefficient (deep i) g i‖^2) := by
      apply sum_le_sum
      intro i hi
      exact (sq_triangle ..).trans (by gcongr; exact err i hi)
    _ = 2*((S.card:ℝ)*(freezeCost N M W s)^2 + ∑ i ∈ S, ‖coefficient (deep i) g i‖^2) := by
      rw [←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul]
    _ ≤ _ := by nlinarith only [sumB.trans (mul_le_mul_of_nonneg_left massB L)]

end
end TypeTwoDiagonal

namespace TypeTwoDiagonal
open Finset GoldbachTransitionSquare
noncomputable section

theorem root_comparison {X n : ℕ} (hX : 0<X) (hn : n ≤ 8*X) {e : ℝ} (he : 0≤e) (h1 : e≤1) :
    ⌊(n:ℝ)^e⌋₊ ≤ 16*⌊(X:ℝ)^e⌋₊ := by
  have x1 : (1:ℝ)≤X := by exact_mod_cast hX
  have base : 1 ≤ ⌊(X:ℝ)^e⌋₊ := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow x1 he)
  have small : (X:ℝ)^e ≤ 2*(⌊(X:ℝ)^e⌋₊:ℝ) := by
    have p := Nat.lt_floor_add_one ((X:ℝ)^e)
    have h : (1:ℝ)≤⌊(X:ℝ)^e⌋₊ := by exact_mod_cast base
    linarith
  have eight : (8:ℝ)^e ≤ 8 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤8) h1
  have upper : (n:ℝ)^e ≤ 16*(⌊(X:ℝ)^e⌋₊:ℝ) := calc
    _ ≤ (8*(X:ℝ))^e := Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hn) he
    _ = (8:ℝ)^e * (X:ℝ)^e := Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
    _ ≤ 8*(2*(⌊(X:ℝ)^e⌋₊:ℝ)) := mul_le_mul eight small (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by norm_num)
    _ = _ := by ring
  exact_mod_cast (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) e)).trans upper

theorem params_positive {X : ℕ} (hx : 0<X) : Below ⟨1,1,1,1,1⟩ (actualParams X) := by
  have fr (e : ℝ) (he : 0≤e) : 1 ≤ ⌊(X:ℝ)^e⌋₊ :=
    (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow (by exact_mod_cast hx) he)
  refine ⟨hx,fr _ (by norm_num),fr _ (by norm_num),fr _ (by norm_num),?_⟩
  change 1 ≤ Nat.sqrt X
  exact Nat.sqrt_pos.mpr hx

theorem block_label {M X n : ℕ} (hx : 0<X) (hn : n ≤ 8*X) :
    label M (actualParams X) (actualParams n) ≤ 80*M := by
  have ratio (A b : ℕ) (ha : 0<A) (hb : b≤16*A) : bucket M A b ≤ 16*M := by
    have bound : M*b ≤ (16*M)*A := (Nat.mul_le_mul_left M hb).trans_eq (by ring)
    exact (Nat.div_le_div_right bound).trans_eq (Nat.mul_div_cancel _ ha)
  obtain ⟨hp,hu,hl,hb,hs⟩ := params_positive hx
  have top := ratio _ _ hp (show n ≤ 16*X by omega)
  have u := ratio _ _ hu (root_comparison hx hn (by norm_num : (0:ℝ)≤1/16) (by norm_num))
  have l := ratio _ _ hl (root_comparison hx hn (by norm_num : (0:ℝ)≤1/4) (by norm_num))
  have b := ratio _ _ hb (root_comparison hx hn (by norm_num : (0:ℝ)≤1/3) (by norm_num))
  have sq : n.sqrt ≤ 16*X.sqrt := by
    simpa only [←Real.sqrt_eq_rpow,Real.nat_floor_real_sqrt_eq_nat_sqrt] using
      root_comparison hx hn (by norm_num : (0:ℝ)≤1/2) (by norm_num)
  have p := ratio _ _ hs sq
  change bucket M X n + bucket M (cutoffU X) (cutoffU n) + bucket M (cutoffL X) (cutoffL n) +
    bucket M (cutoffB X) (cutoffB n) + bucket M X.sqrt n.sqrt ≤ _
  dsimp [actualParams,cutoffU,cutoffL,cutoffB] at top u l b p ⊢
  omega

theorem block_changes {k M i j : ℕ} (hi : octave k ≤ i) (hj : octave k ≤ j)
    (eq : label M (actualParams (octave k)) (actualParams i) =
      label M (actualParams (octave k)) (actualParams j)) :
    M*(changes (8*octave k) (actualParams i) (actualParams j)).card ≤ 5*(8*octave k) := by
  apply changes_count (actualParams (octave k)) _ _ (actual_ordered hi) (actual_ordered hj)
    (params_positive (by unfold octave; positivity)) (by change octave k ≤ 8*octave k; omega)
  rcases le_total i j with le|ge
  · exact ordered_buckets (actual_ordered le) eq
  · exact (ordered_buckets (actual_ordered ge) eq.symm).symm

theorem class_moment (k M : ℕ) (hk : 32 ≤ k) (hM : 0<M) (S : Finset ℕ)
    (hS : ∀ i ∈ S, octave k ≤ i ∧ i ≤ 8*octave k)
    (T W s : ℝ) (hT : 0<T) (hs : 0<s)
    (hW : ∀ i ∈ S, ∀ m ≤ 8*octave k, |padded (actualParams i) m| ≤ W)
    (hcap : ∀ i ∈ S, ∀ t ∈ Set.Ioc (0:ℝ) 1, t ∈ deep i → ‖spec (8*octave k) (actualParams i) t‖ ≤ T) :
    (∑ i ∈ S, ‖coreValue i‖^2) ≤
      2*(S.card:ℝ)*(freezeCost (8*octave k) M W s)^2 +
      (80*(M:ℝ)+1)*(2*logCost k*T^2*((((8*octave k:ℕ):ℝ)+1)*W^2)) := by
  classical
  let key i := label M (actualParams (octave k)) (actualParams i)
  let B := range (80*M+1)
  let G j := S.filter (fun i => key i=j)
  let N := 8*octave k
  let err := (freezeCost N M W s)^2
  let cost := 2*logCost k*T^2*(((N:ℝ)+1)*W^2)
  have Xpos : 0 < octave k := by unfold octave; positivity
  have maps : ∀ i ∈ S, key i ∈ B := fun i hi => mem_range.mpr
    (Nat.lt_succ_of_le (block_label Xpos (hS i hi).2))
  have each j : (∑ i ∈ G j, ‖coreValue i‖^2) ≤ 2*((G j).card:ℝ)*err + cost := by
    by_cases h : (G j).Nonempty
    · obtain ⟨a,ha⟩ := h
      have ha' := (mem_filter.mp ha).1
      apply cell_moment k M N hk hM (G j) (fun i hi => hS i (mem_filter.mp hi).1)
        (fun i hi => (hS i (mem_filter.mp hi).1).2) (actualParams a) T W s hT hs (hW a ha')
        (fun i hi => hW i (mem_filter.mp hi).1) _ (fun i hi => hcap i (mem_filter.mp hi).1)
      intro i hi
      exact block_changes (hS i (mem_filter.mp hi).1).1 (hS a ha').1
        ((mem_filter.mp hi).2.trans (mem_filter.mp ha).2.symm)
    · have empty := not_nonempty_iff_eq_empty.mp h
      simp only [empty,sum_empty,card_empty,Nat.cast_zero,mul_zero,zero_mul,zero_add]
      dsimp [cost,logCost]
      positivity
  have total : (∑ j ∈ B, ((G j).card:ℝ)) = (S.card:ℝ) := by
    exact_mod_cast (Finset.card_eq_sum_card_fiberwise (s:=S) (t:=B) (f:=key) maps).symm
  calc
    _ = ∑ j ∈ B, ∑ i ∈ G j, ‖coreValue i‖^2 := (sum_fiberwise_of_maps_to maps _).symm
    _ ≤ ∑ j ∈ B, (2*((G j).card:ℝ)*err+cost) := sum_le_sum (fun j _ => each j)
    _ = _ := by
      rw [sum_add_distrib,←sum_mul,←mul_sum,total,sum_const,nsmul_eq_mul]
      simp [err,cost,N,B]

end
end TypeTwoDiagonal

namespace TypeTwoDiagonal
open Finset GoldbachTransitionSquare
noncomputable section
/-- A divisor estimate on the common scale of the dyadic block. -/
theorem fine_divisor_envelope : ∃ C : ℝ, 1 ≤ C ∧ ∀ n m : ℕ, m ≤ n →
    (m.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (1 / 3072 : ℝ) := by
  obtain ⟨C, CLower, estimate⟩ := divisorPower 3072 (by decide)
  let p : ℝ := 1 / 3072
  have CNonnegative : 0 ≤ C := zero_le_one.trans CLower
  refine ⟨C ^ p, Real.one_le_rpow CLower (by norm_num [p]), fun n m upper => ?_⟩
  by_cases mPositive : 0 < m
  · have mReal : (m : ℝ) ≤ n := by exact_mod_cast upper
    have standard := (estimate m mPositive).trans (mul_le_mul_of_nonneg_left mReal CNonnegative)
    have powered := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg m.divisors.card) 3072) standard
      (show 0 ≤ p by norm_num [p])
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg m.divisors.card),
      Real.mul_rpow CNonnegative (Nat.cast_nonneg n)] at powered
    norm_num [p] at powered ⊢
    exact powered
  · have mZero : m = 0 := by omega
    subst m
    simp only [Nat.divisors_zero, Finset.card_empty, Nat.cast_zero]
    positivity

def scale (N : ℕ) : ℝ := (N:ℝ)^(1/3072:ℝ)

theorem scale_one {N : ℕ} (h : 0<N) : 1 ≤ scale N :=
  Real.one_le_rpow (by exact_mod_cast h) (by norm_num)

theorem scale_power (N j : ℕ) : (scale N)^j = (N:ℝ)^((j:ℝ)/3072) := by
  unfold scale
  rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg N)]
  congr 1
  ring

theorem scale_exact (N : ℕ) : (scale N)^3072 = N := by
  rw [scale_power]
  norm_num

theorem block_weight_envelope : ∃ D : ℝ, 1 ≤ D ∧ ∀ N : ℕ, 0<N → ∀ i m : ℕ, m ≤ N →
    |padded (actualParams i) m| ≤ D*(scale N)^3 := by
  obtain ⟨C,hC,h⟩ := fine_divisor_envelope
  refine ⟨3072*C^2,by nlinarith [sq_nonneg (C-1)],?_⟩
  intro N hN i m hm
  by_cases hmi : m ≤ i
  · rw [padded_actual i m hmi]
    have H := band_uniform_bound N (cutoffU i) (cutoffL i) (cutoffB i) m hm hN
      (h N) (abs_largePrimeWeight_le i)
    have lg : Real.log (N:ℝ) ≤ 3072*scale N :=
      (Real.log_le_rpow_div (x:=(N:ℝ)) (Nat.cast_nonneg N) (by norm_num : (0:ℝ)<1/3072)).trans_eq
        (by unfold scale; ring)
    change |core i (cutoffU i) (cutoffL i) (cutoffB i) m| ≤ (C*scale N)^2*Real.log N at H
    exact H.trans ((mul_le_mul_of_nonneg_left lg (sq_nonneg (C*scale N))).trans_eq (by ring))
  · have pad : padded (actualParams i) m = 0 := if_neg (show ¬m ≤ (actualParams i).top from hmi)
    rw [pad,abs_zero]
    have hz := scale_one hN
    positivity

def logConstant : ℝ := 2*(1+(6200:ℝ)^2*19000^2)

theorem block_log_cost (k : ℕ) :
    logCost k ≤ logConstant * scale (8*octave k)^4 := by
  let N := 8*octave k
  let z := scale N
  have hn : 0<N := by dsimp [N,octave]; positivity
  have z1 : 1≤z := scale_one hn
  have zk : ((2:ℝ)^k) ≤ N := by
    exact_mod_cast (show 2^k ≤ N by
      dsimp [N,octave]; have p : 0<2^k := by positivity
      have h := Nat.pow_le_pow_right (Nat.succ_le_of_lt p) (show 1 ≤ 3 by decide)
      simp only [pow_one] at h
      omega)
  have q := Real.log_le_log (by positivity) zk
  rw [Real.log_pow] at q
  have lg : Real.log (N:ℝ) ≤ 3072*z :=
    (Real.log_le_rpow_div (x:=(N:ℝ)) (Nat.cast_nonneg _) (by norm_num : (0:ℝ)<1/3072)).trans_eq
      (by dsimp [z,scale]; ring)
  have bound : (k:ℝ) ≤ 6144*z := by
    have h := mul_le_mul_of_nonneg_left (show (1/2:ℝ) ≤ Real.log 2 by linarith [Real.log_two_gt_d9]) (Nat.cast_nonneg (α:=ℝ) k)
    linarith
  have h1 : (k:ℝ)+3 ≤ 6200*z := by linarith
  have h2 : 3*(k:ℝ)+5 ≤ 19000*z := by linarith
  have zz : 1≤z^4 := one_le_pow₀ z1
  have hh := mul_le_mul (pow_le_pow_left₀ (by positivity : 0≤(k:ℝ)+3) h1 2)
    (pow_le_pow_left₀ (by positivity : 0≤3*(k:ℝ)+5) h2 2) (sq_nonneg _)
    (sq_nonneg _)
  change logCost k ≤ logConstant*z^4
  dsimp [logCost,logConstant]
  push_cast
  nlinarith only [hh,zz]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1200000 in
theorem cost_bound {N : ℕ} (hN : 0<N) (C : ℝ) :
    let z := scale N
    let M := ⌈z^96⌉₊
    freezeCost N M (C*z^3) (z^48) ≤ 44*C^2*z^3030 := by
  intro z M
  have hz : 1≤z := scale_one hN
  have h0 : 0<z := zero_lt_one.trans_le hz
  have eq : z^3072 = (N:ℝ) := scale_exact N
  have hm : z^96 ≤ (M:ℝ) := Nat.le_ceil _
  have hp : (0:ℝ)<M := (pow_pos h0 96).trans_le hm
  have hn1 : (N:ℝ)+1 ≤ 2*z^3072 := by
    rw [eq]
    have h : (1:ℝ)≤N := by exact_mod_cast hN
    linarith
  have s0 : 0<z^48 := pow_pos h0 _
  have a : 20*(N:ℝ)*(C*z^3)^2/(M:ℝ) ≤ 20*C^2*z^2982 := by
    rw [div_le_iff₀ hp,←eq]
    calc
      _ = (20*C^2*z^2982)*z^96 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)
  have b : 2*((N:ℝ)+1)*(C*z^3)^2 ≤ (4*C^2*z^3030)*z^48 := calc
    _ ≤ 2*(2*z^3072)*(C*z^3)^2 := by gcongr
    _ = _ := by ring
  have b' : (z^48)⁻¹*(2*((N:ℝ)+1)*(C*z^3)^2) ≤ 4*C^2*z^3030 := by
    rwa [inv_mul_eq_div,div_le_iff₀ s0]
  change 2*z^48*_+_ ≤ _
  exact (add_le_add (mul_le_mul_of_nonneg_left a (by positivity : 0≤2*z^48)) b').trans_eq (by ring)

end
end TypeTwoDiagonal

namespace TypeTwoDiagonal
open Finset GoldbachTransitionSquare
noncomputable section

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
private theorem numeric_moment {z A C K D L : ℝ} (hz : 1≤z) (hC : 0≤C) (hK : 0≤K)
    (hD : 0≤D) (hL : 0≤L)
    (hb : A ≤ 2*(2*z^3072)*(D*z^2976)^2 +
      2*(2*(2*z^3072)*(44*C^2*z^3030)^2 +
        (161*z^96)*(2*(L*z^4)*(K*z^5792)*((2*z^3072)*(C*z^3)^2)))) :
    A ≤ (4*D^2+8*(44*C^2)^2+1288*L*K*C^2)*z^9132 := by
  have h1 := pow_le_pow_right₀ hz (by decide : 9024≤9132)
  have h2 := pow_le_pow_right₀ hz (by decide : 8970≤9132)
  calc
    A ≤ _ := hb
    _ = (4*D^2)*z^9024 + (8*(44*C^2)^2)*z^9132 + (1288*L*K*C^2)*z^8970 := by ring
    _ ≤ _ := by
      rw [add_mul,add_mul]
      gcongr

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1800000 in
theorem diagonal_moment : ∃ Ctotal : ℝ, 0<Ctotal ∧ ∀ k : ℕ, 32 ≤ k →
    ∀ S : Finset ℕ, (∀ i ∈ S, octave k ≤ i ∧ i ≤ 8*octave k) →
    (∑ i ∈ S, ‖fullValue i‖^2) ≤ Ctotal*((8*octave k:ℕ):ℝ)^(761/256:ℝ) := by
  obtain ⟨C,hC,weight⟩ := block_weight_envelope
  obtain ⟨K,hK,cap⟩ := core_pointwise_power
  obtain ⟨D,hD,remove⟩ := transition_power_saving
  have L : 0<logConstant := by norm_num [logConstant]
  refine ⟨4*D^2+8*(44*C^2)^2+1288*logConstant*K*C^2,by positivity,?_⟩
  intro k hk S hS
  let N := 8*octave k
  let z := scale N
  let M := ⌈z^96⌉₊
  let T := Real.sqrt (K*z^5792)
  have Npos : 0<N := by dsimp [N,octave]; positivity
  have hz : 1≤z := scale_one Npos
  have zpos : 0<z := zero_lt_one.trans_le hz
  have hM : 0<M := Nat.ceil_pos.mpr (pow_pos zpos _)
  have hT : 0<T := Real.sqrt_pos.mpr (by positivity)
  have hT2 : T^2 = K*z^5792 := Real.sq_sqrt (by positivity)
  have eqN : z^3072 = N := scale_exact N
  have plus : (N:ℝ)+1 ≤ 2*z^3072 := by
    rw [eqN]
    have h : (1:ℝ)≤N := by exact_mod_cast Npos
    linarith
  have labelBd : 80*(M:ℝ)+1 ≤ 161*z^96 := by
    have hm := Nat.ceil_lt_add_one (show 0≤z^96 by positivity)
    change (M:ℝ) < _ at hm
    linarith [one_le_pow₀ hz (n:=96)]
  have Nbd i (hi : i∈S) : i≤N := (hS i hi).2
  have two i (hi : i∈S) : 2 ≤ i := by
    have one : 1≤3*k := by omega
    have base := Nat.pow_le_pow_right (by decide : 1≤2) one
    rw [pow_one,←octave_eq] at base
    exact base.trans (hS i hi).1
  have cut i (hi : i∈S) (t : ℝ) (ht : t∈Set.Ioc (0:ℝ) 1) (hd : t∈deep i) :
      ‖spec N (actualParams i) t‖ ≤ T := by
    rw [spec_actual (Nbd i hi)]
    apply Real.le_sqrt_of_sq_le
    have h := cap i (two i hi) t ⟨⟨ht.1.le,ht.2⟩,hd⟩
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hK.le)
    rw [scale_power]
    norm_num
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nbd i hi) (by norm_num)
  have main := class_moment k M hk hM S hS T (C*z^3) (z^48) hT (pow_pos zpos _)
    (fun i _ m hm => weight N Npos i m hm) cut
  change _ ≤ 2*(S.card:ℝ)*_ + (80*(M:ℝ)+1)*(2*logCost k*T^2*(((N:ℝ)+1)*(C*z^3)^2)) at main
  have card : (S.card:ℝ) ≤ 2*z^3072 := by
    have sub : S ⊆ range (N+1) := fun i hi => mem_range.mpr (Nat.lt_succ_of_le (Nbd i hi))
    have h := card_le_card sub
    rw [card_range] at h
    exact (show (S.card:ℝ) ≤ (N:ℝ)+1 by exact_mod_cast h).trans plus
  have cost := cost_bound Npos C
  change freezeCost N M (C*z^3) (z^48) ≤ _ at cost
  have free0 : 0≤freezeCost N M (C*z^3) (z^48) := by unfold freezeCost; positivity
  have lc : 0≤logCost k := by unfold logCost; positivity
  have main' : (∑ i ∈ S, ‖coreValue i‖^2) ≤
      2*(2*z^3072)*(44*C^2*z^3030)^2 +
        (161*z^96)*(2*(logConstant*z^4)*(K*z^5792)*((2*z^3072)*(C*z^3)^2)) := by
    apply main.trans
    rw [hT2]
    gcongr
    · exact block_log_cost k
  have reduction i (hi : i∈S) : ‖fullValue i - coreValue i‖ ≤ D*z^2976 := by
    have h := remove i (cutoffU i) (cutoffL i) (cutoffB i) (by have := two i hi; omega)
      (Nat.floor_le (by positivity)) (deep i) (wide_measurable ..).compl
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hD.le)
    rw [scale_power]
    norm_num
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nbd i hi) (by norm_num)
  have tot : (∑ i ∈ S, ‖fullValue i‖^2) ≤
      2*(S.card:ℝ)*(D*z^2976)^2 + 2*(∑ i ∈ S, ‖coreValue i‖^2) := calc
    _ ≤ ∑ i ∈ S, 2*((D*z^2976)^2+‖coreValue i‖^2) := by
      apply sum_le_sum
      intro i hi
      exact (sq_triangle ..).trans (by gcongr; exact reduction i hi)
    _ = _ := by rw [←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul]; ring
  have final := numeric_moment (z:=z) (C:=C) (K:=K) (D:=D) (L:=logConstant)
    hz (by linarith) hK.le hD.le L.le
    (tot.trans (add_le_add (by gcongr) (mul_le_mul_of_nonneg_left main' (by norm_num))))
  have exp : z^9132 = (N:ℝ)^(761/256:ℝ) := (scale_power N 9132).trans (by norm_num)
  rwa [exp] at final

end
end TypeTwoDiagonal

namespace TypeTwoDiagonal
open Finset GoldbachTransitionSquare
noncomputable section

theorem octave_succ (k : ℕ) : octave (k+1) = 8*octave k := by
  rw [octave,octave,pow_succ]
  ring


end
end TypeTwoDiagonal

namespace TypeTwoDiagonal
open Finset GoldbachTransitionSquare
noncomputable section

/-- Cover an arbitrary doubling window by adjacent base-eight blocks. If
the second block is used, its upper endpoint is below 16X. -/
theorem moving_window_bound : ∃ C : ℝ, 0<C ∧ ∀ X : ℕ, 2^96 ≤ X →
    (∑ n ∈ Icc X (2*X), ‖fullValue n‖^2) ≤ C*(X:ℝ)^(761/256:ℝ) := by
  obtain ⟨K,hK,block⟩ := diagonal_moment
  let α : ℝ := 761/256
  have hα : 0 ≤ α := by norm_num [α]
  refine ⟨K*((8:ℝ)^α+(16:ℝ)^α), by positivity,?_⟩
  intro X hX
  have hXpos : 0<X := lt_of_lt_of_le (by decide : 0<(2^96:ℕ)) hX
  let k := Nat.log 8 X
  have oct (r : ℕ) : octave r = 8^r := by
    rw [octave_eq, pow_mul]; rfl
  have hk : 32 ≤ k := (Nat.le_log_iff_pow_le (by decide) hXpos.ne').mpr (by exact hX)
  have hlo : octave k ≤ X := by rw [oct]; exact Nat.pow_log_le_self _ hXpos.ne'
  have hhi : X < 8*octave k := by
    simpa [oct,k,pow_succ,mul_comm] using (Nat.lt_pow_succ_log_self (by decide : 1<8) X)
  let S := Icc X (2*X)
  let A := S.filter (fun i => i ≤ 8*octave k)
  let B := S.filter (fun i => ¬i ≤ 8*octave k)
  have transfer (j : ℕ) (hj : 32 ≤ j) (T : Finset ℕ) (c : ℕ)
      (hT : ∀ i∈T, octave j ≤ i ∧ i ≤ 8*octave j) (hs : 8*octave j ≤ c*X) :
      (∑ i∈T, ‖fullValue i‖^2) ≤ K*(c:ℝ)^α*(X:ℝ)^α := by
    refine (block j hj T hT).trans ?_
    have hp := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (8*octave j:ℕ))
      (show ((8*octave j:ℕ):ℝ) ≤ (c:ℝ)*X by exact_mod_cast hs) hα
    rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _) ] at hp
    simpa [mul_assoc,α] using (mul_le_mul_of_nonneg_left hp hK.le)
  have hA : (∑ i∈A, ‖fullValue i‖^2) ≤ K*(8:ℝ)^α*(X:ℝ)^α := by
    apply transfer k hk A 8 _ (Nat.mul_le_mul_left 8 hlo)
    intro i hi
    obtain ⟨hs, hb⟩ := mem_filter.mp hi
    exact ⟨hlo.trans (mem_Icc.mp hs).1,hb⟩
  have hB : (∑ i∈B, ‖fullValue i‖^2) ≤ K*(16:ℝ)^α*(X:ℝ)^α := by
    rcases B.eq_empty_or_nonempty with h | ⟨i,hi⟩
    · rw [h,sum_empty]; positivity
    obtain ⟨hmem,habove⟩ := mem_filter.mp hi
    have hscale : 8*octave (k+1) ≤ 16*X := by
      rw [octave_succ]
      have := (mem_Icc.mp hmem).2
      omega
    apply transfer (k+1) (by omega) B 16 _ hscale
    intro j hj
    obtain ⟨hs,ha⟩ := mem_filter.mp hj
    rw [octave_succ]
    have := (mem_Icc.mp hs).2
    omega
  change (∑ n∈S, ‖fullValue n‖^2) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not S (fun i => i ≤ 8*octave k)]
  exact (add_le_add hA hB).trans_eq (by ring)
end
end TypeTwoDiagonal

theorem Conjectures.Goldbach.Type2MovingDiagonalMoment :
let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let Λ := ArithmeticFunction.vonMangoldt; let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊; let B₁ := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊; let B₂ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let τ₂ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₁ n < a ∧ a ≤ B₂ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let Jdeep := fun (n : ℕ) (u v : ℕ → ℝ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume; ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2^96 ≤ X → (∑ n ∈ Finset.Icc X (2*X), ‖Jdeep n (τ₂ n) (τ₂ n)‖^2) ≤ C*(X:ℝ)^(761/256:ℝ) := TypeTwoDiagonal.moving_window_bound
