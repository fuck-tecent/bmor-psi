import Mathlib

/-!
# Moving second moment of the prime deep minor arc integral

The denominator cutoff, widths, prime summation limit and Fourier target all move with the same n.
The exponent agrees with the fixed-spectrum result of muxkin in goldbach-proofs PR 2394,
revision e8a1d429f5758874590eae79ce35af2ac63febd6 (Apache-2.0).
The Vaughan development and rational approximation helpers are adapted from that proof.
https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/2394
-/

/-!
The Vaughan estimate and its supporting development are adapted from OpenAI,
openai/math, revision 3344da59991ed94f9ba711217b29c1d760badfa6,
lean/OAI/NumberTheory/EgyptianFractions (Apache License 2.0).
This version selects the declarations supporting the final estimate and adapts them
to version 4.36.0 of the proof assistant and its pinned Mathlib. Section comments identify upstream files.
https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/NumberTheory/EgyptianFractions
-/

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanDyadic

namespace OAI
/-!
# Exact dyadic decomposition of a truncated hyperbola

The long--long convolution is partitioned into genuine dyadic row intervals.
Each column interval is shortened to `N / 2^j`, retaining the exact `mn ≤ N`
cutoff. This is a finite reindexing, with no analytic cancellation hypothesis.
-/

noncomputable section
open scoped BigOperators
open Finset

namespace Problem337.VaughanDyadic

/-- Rows above the lower cutoff, inside one half-open power-of-two interval. -/
def shell (U N j : ℕ) : Finset ℕ :=
  (Ioc U N).filter fun m => 2 ^ j ≤ m ∧ m < 2 ^ (j + 1)

lemma mem_shell {U N j m : ℕ} :
    m ∈ shell U N j ↔ U < m ∧ m ≤ N ∧ 2 ^ j ≤ m ∧ m < 2 ^ (j + 1) := by
  simp only [shell, mem_filter, mem_Ioc]
  tauto

lemma shell_eq_log_fiber (U N j : ℕ) :
    shell U N j = (Ioc U N).filter (fun m => Nat.log 2 m = j) := by
  ext m
  simp only [shell, mem_filter]
  apply and_congr_right
  intro hm
  exact (Nat.log_eq_iff (Or.inr ⟨by decide, (lt_of_le_of_lt (Nat.zero_le U)
    (mem_Ioc.mp hm).1).ne'⟩)).symm

/-- The shell is a single consecutive interval, so its phase correlations remain geometric. -/
lemma shell_eq_Icc (U N j : ℕ) :
    shell U N j = Icc (max (U + 1) (2 ^ j)) (min N (2 ^ (j + 1) - 1)) := by
  ext m
  rw [mem_shell]
  simp only [mem_Icc, max_le_iff, le_min_iff]
  have hp : 0 < 2 ^ (j + 1) := by positivity
  omega

/-- Exact partition, valid also when the original interval is empty. -/
theorem sum_eq_sum_shells {E : Type*} [AddCommMonoid E]
    (U N : ℕ) (f : ℕ → E) :
    (∑ m ∈ Ioc U N, f m) =
      ∑ j ∈ range (Nat.log 2 N + 1), ∑ m ∈ shell U N j, f m := by
  simp_rw [shell_eq_log_fiber]
  apply (sum_fiberwise_of_maps_to ?_ f).symm
  intro m hm
  exact mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (mem_Ioc.mp hm).2))

lemma inner_sum_eq_common_cutoff {E : Type*} [AddCommMonoid E]
    (N U V j m : ℕ) (hm : m ∈ shell U N j) (f : ℕ → E) :
    (∑ n ∈ Ioc V (N / m), f n) =
      ∑ n ∈ Ioc V (N / 2 ^ j), if m * n ≤ N then f n else 0 := by
  have hmem := mem_shell.mp hm
  have hm0 : 0 < m := lt_of_le_of_lt (Nat.zero_le U) hmem.1
  have hpow : 0 < 2 ^ j := by positivity
  have hdiv : N / m ≤ N / 2 ^ j := Nat.div_le_div_left hmem.2.2.1 hpow
  have hsets : Ioc V (N / m) =
      (Ioc V (N / 2 ^ j)).filter (fun n => m * n ≤ N) := by
    ext n
    simp only [mem_Ioc, mem_filter]
    constructor
    · rintro ⟨hV, hn⟩
      exact ⟨⟨hV, hn.trans hdiv⟩,
        by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm0).mp hn⟩
    · rintro ⟨⟨hV, _⟩, hn⟩
      exact ⟨hV, (Nat.le_div_iff_mul_le hm0).mpr (by simpa [Nat.mul_comm] using hn)⟩
  rw [hsets, sum_filter]

/-- The actual dyadic block, not a rectangular surrogate without the cutoff. -/
def block {E : Type*} [AddCommMonoid E] (N U V j : ℕ) (F : ℕ → ℕ → E) : E :=
  ∑ m ∈ shell U N j, ∑ n ∈ Ioc V (N / 2 ^ j),
    if m * n ≤ N then F m n else 0

/-- Exact long--long hyperbola decomposition into common-column dyadic blocks. -/
theorem sum_hyperbola_eq_sum_blocks {E : Type*} [AddCommMonoid E]
    (N U V : ℕ) (F : ℕ → ℕ → E) :
    (∑ m ∈ Ioc U N, ∑ n ∈ Ioc V (N / m), F m n) =
      ∑ j ∈ range (Nat.log 2 N + 1), block N U V j F := by
  rw [sum_eq_sum_shells]
  apply sum_congr rfl
  intro j hj
  unfold block
  apply sum_congr rfl
  intro m hm
  exact inner_sum_eq_common_cutoff N U V j m hm (F m)

/-- Product-finset form of the same exact decomposition. -/
theorem sum_filtered_product_eq_sum_blocks {E : Type*} [AddCommMonoid E]
    (N U V : ℕ) (F : ℕ → ℕ → E) :
    (∑ d ∈ (Ioc U N ×ˢ Ioc V N).filter (fun d => d.1 * d.2 ≤ N), F d.1 d.2) =
      ∑ j ∈ range (Nat.log 2 N + 1), block N U V j F := by
  rw [← sum_hyperbola_eq_sum_blocks, sum_filter, sum_product]
  apply sum_congr rfl
  intro m hm
  have hm0 : 0 < m := lt_of_le_of_lt (Nat.zero_le U) (mem_Ioc.mp hm).1
  rw [← sum_filter]
  have he : (Ioc V N).filter (fun n => m * n ≤ N) = Ioc V (N / m) := by
    ext n
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨hV, _⟩, hmn⟩
      exact ⟨hV, (Nat.le_div_iff_mul_le hm0).mpr (by simpa [Nat.mul_comm] using hmn)⟩
    · rintro ⟨hV, hn⟩
      exact ⟨⟨hV, hn.trans (Nat.div_le_self N m)⟩,
        by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm0).mp hn⟩
  rw [he]

/-- Triangle inequality with the actual dyadic block norms. -/
theorem norm_hyperbola_le_sum_block_norms {E : Type*} [SeminormedAddCommGroup E]
    (N U V : ℕ) (F : ℕ → ℕ → E) :
    ‖∑ m ∈ Ioc U N, ∑ n ∈ Ioc V (N / m), F m n‖ ≤
      ∑ j ∈ range (Nat.log 2 N + 1), ‖block N U V j F‖ := by
  rw [sum_hyperbola_eq_sum_blocks]
  exact norm_sum_le _ _

/-- Any genuine uniform block estimate pays only the number of dyadic blocks. -/
theorem norm_hyperbola_le_block_count {E : Type*} [SeminormedAddCommGroup E]
    (N U V : ℕ) (F : ℕ → ℕ → E) (B : ℝ)
    (hB : ∀ j < Nat.log 2 N + 1, ‖block N U V j F‖ ≤ B) :
    ‖∑ m ∈ Ioc U N, ∑ n ∈ Ioc V (N / m), F m n‖ ≤
      (Nat.log 2 N + 1 : ℕ) * B := by
  calc
    _ ≤ ∑ j ∈ range (Nat.log 2 N + 1), ‖block N U V j F‖ :=
      norm_hyperbola_le_sum_block_norms N U V F
    _ ≤ ∑ j ∈ range (Nat.log 2 N + 1), B :=
      sum_le_sum fun j hj => hB j (mem_range.mp hj)
    _ = _ := by simp

/-- Real-log normalization of the finite dyadic block count. -/
theorem norm_hyperbola_le_log_budget {E : Type*} [SeminormedAddCommGroup E]
    (N U V : ℕ) (F : ℕ → ℕ → E) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ j < Nat.log 2 N + 1, ‖block N U V j F‖ ≤ B) :
    ‖∑ m ∈ Ioc U N, ∑ n ∈ Ioc V (N / m), F m n‖ ≤
      (1 + Real.log N / Real.log 2) * B := by
  refine (norm_hyperbola_le_block_count N U V F B hB).trans ?_
  apply mul_le_mul_of_nonneg_right _ hB0
  have h := Real.natLog_le_logb N 2
  simp only [Real.logb, Nat.cast_ofNat] at h
  push_cast
  linarith

end Problem337.VaughanDyadic

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanIdentity

namespace OAI
/-!
# Vaughan's identity with finite cutoffs

This file supplies an unconditional algebraic input to the analytic three-prime
route. Multiplication of arithmetic functions below is Dirichlet convolution.
No estimate for exponential sums over primes is assumed or asserted here.
-/

noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius
  ArithmeticFunction.zeta

namespace Problem337.Vaughan

/-- The part of an arithmetic function supported on integers at most `U`. -/
def shortPart {R : Type*} [Zero R] (U : ℕ) (f : ArithmeticFunction R) :
    ArithmeticFunction R :=
  ⟨fun n => if n ≤ U then f n else 0, by simp⟩

/-- The complementary part, supported on integers strictly above `U`. -/
def longPart {R : Type*} [Zero R] (U : ℕ) (f : ArithmeticFunction R) :
    ArithmeticFunction R :=
  ⟨fun n => if U < n then f n else 0, by simp⟩

@[simp] lemma shortPart_apply {R : Type*} [Zero R]
    (U : ℕ) (f : ArithmeticFunction R) (n : ℕ) :
    shortPart U f n = if n ≤ U then f n else 0 := rfl

@[simp] lemma longPart_apply {R : Type*} [Zero R]
    (U : ℕ) (f : ArithmeticFunction R) (n : ℕ) :
    longPart U f n = if U < n then f n else 0 := rfl

lemma shortPart_add_longPart {R : Type*} [AddMonoid R]
    (U : ℕ) (f : ArithmeticFunction R) : shortPart U f + longPart U f = f := by
  ext n
  by_cases hn : n ≤ U <;> simp [hn, Nat.not_lt.mpr, Nat.lt_of_not_ge]

lemma longPart_eq_sub_shortPart {R : Type*} [AddCommGroup R]
    (U : ℕ) (f : ArithmeticFunction R) : longPart U f = f - shortPart U f := by
  have h := shortPart_add_longPart U f
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h)

/-- Vaughan's four-term identity, valid also at zero and for zero cutoffs.
The first convolution is Type I; the second has a coefficient supported on
`[1,U*V]`; the last is the long-long Type II convolution. -/
theorem vonMangoldt_identity (U V : ℕ) :
    ArithmeticFunction.vonMangoldt =
      shortPart V ArithmeticFunction.vonMangoldt +
      shortPart U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log -
      (shortPart U (μ : ArithmeticFunction ℝ) *
        shortPart V ArithmeticFunction.vonMangoldt) * (ζ : ArithmeticFunction ℝ) +
      (longPart U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) *
        longPart V ArithmeticFunction.vonMangoldt := by
  rw [longPart_eq_sub_shortPart, longPart_eq_sub_shortPart]
  have hμ : (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) = 1 :=
    ArithmeticFunction.coe_moebius_mul_coe_zeta
  have hΛ : (ζ : ArithmeticFunction ℝ) * ArithmeticFunction.vonMangoldt =
      ArithmeticFunction.log := ArithmeticFunction.zeta_mul_vonMangoldt
  calc
    ArithmeticFunction.vonMangoldt =
        ((μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) *
          ArithmeticFunction.vonMangoldt := by rw [hμ, one_mul]
    _ = _ := by
      rw [← hΛ]
      have hshort : ((μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) *
          shortPart V ArithmeticFunction.vonMangoldt =
          shortPart V ArithmeticFunction.vonMangoldt := by rw [hμ, one_mul]
      linear_combination hshort

/-- A convolution of two short parts has the expected product support. -/
lemma shortPart_mul_eq_zero_of_lt {R : Type*} [Semiring R]
    (U V n : ℕ) (f g : ArithmeticFunction R) (hn : U * V < n) :
    (shortPart U f * shortPart V g) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro ab hab
  have habn := (Nat.mem_divisorsAntidiagonal.mp hab).1
  by_cases ha : ab.1 ≤ U
  · have hb : ¬ ab.2 ≤ V := by
      intro hb
      have hm := Nat.mul_le_mul ha hb
      rw [habn] at hm
      omega
    simp [ha, hb]
  · simp [ha]

/-- Convolving a long part cannot create a smaller positive index. -/
lemma longPart_mul_eq_zero_of_le {R : Type*} [Semiring R]
    (U n : ℕ) (f g : ArithmeticFunction R) (hn : n ≤ U) :
    (longPart U f * g) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro ab hab
  obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hab
  have ha : ab.1 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) ⟨ab.2, hprod.symm⟩
  have hnot : ¬ U < ab.1 := by omega
  simp [hnot]

lemma abs_shortPart_le (U : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    |shortPart U f n| ≤ |f n| := by
  by_cases hn : n ≤ U <;> simp [hn, abs_nonneg]

lemma abs_longPart_le (U : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    |longPart U f n| ≤ |f n| := by
  by_cases hn : U < n <;> simp [hn, abs_nonneg]

lemma abs_real_moebius_le_one (n : ℕ) :
    |(μ : ArithmeticFunction ℝ) n| ≤ 1 := by
  change |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))

/-- The short convolution coefficient appearing in Type I sums. -/
def typeICoefficient (U V : ℕ) : ArithmeticFunction ℝ :=
  shortPart U (μ : ArithmeticFunction ℝ) * shortPart V ArithmeticFunction.vonMangoldt

/-- The coefficient appearing in the long-long Type II sum. -/
def typeIICoefficient (U : ℕ) : ArithmeticFunction ℝ :=
  longPart U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)

lemma typeICoefficient_eq_zero (U V n : ℕ) (hn : U * V < n) :
    typeICoefficient U V n = 0 := shortPart_mul_eq_zero_of_lt U V n _ _ hn

lemma typeIICoefficient_eq_zero (U n : ℕ) (hn : n ≤ U) :
    typeIICoefficient U n = 0 := longPart_mul_eq_zero_of_le U n _ _ hn

/-- The Type I coefficient costs only a logarithm, not a divisor function. -/
lemma abs_typeICoefficient_le_log (U V n : ℕ) :
    |typeICoefficient U V n| ≤ Real.log n := by
  unfold typeICoefficient
  rw [ArithmeticFunction.mul_apply]
  calc
    _ ≤ ∑ ab ∈ n.divisorsAntidiagonal,
        |shortPart U (μ : ArithmeticFunction ℝ) ab.1 *
          shortPart V ArithmeticFunction.vonMangoldt ab.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ab ∈ n.divisorsAntidiagonal, ArithmeticFunction.vonMangoldt ab.2 := by
      apply Finset.sum_le_sum
      intro ab hab
      rw [abs_mul]
      have hμ := (abs_shortPart_le U (μ : ArithmeticFunction ℝ) ab.1).trans
        (abs_real_moebius_le_one ab.1)
      have hΛ := abs_shortPart_le V ArithmeticFunction.vonMangoldt ab.2
      rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] at hΛ
      calc
        _ ≤ 1 * ArithmeticFunction.vonMangoldt ab.2 :=
          mul_le_mul hμ hΛ (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    _ = Real.log n := by
      rw [Nat.sum_divisorsAntidiagonal' (fun _ b => ArithmeticFunction.vonMangoldt b)]
      exact ArithmeticFunction.vonMangoldt_sum

/-- A uniform elementary coefficient bound for the Type II sum. -/
lemma abs_typeIICoefficient_le_divisors_card (U n : ℕ) :
    |typeIICoefficient U n| ≤ (n.divisors.card : ℝ) := by
  rw [typeIICoefficient, ArithmeticFunction.coe_mul_zeta_apply]
  calc
    _ ≤ ∑ d ∈ n.divisors, |longPart U (μ : ArithmeticFunction ℝ) d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact (abs_longPart_le U (μ : ArithmeticFunction ℝ) d).trans
        (abs_real_moebius_le_one d)
    _ = _ := by simp

end Problem337.Vaughan

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanHyperbola

namespace OAI
/-!
# Finite hyperbola reindexing for Vaughan sums

An exact finite change of variables from `n = a*b` to pairs of positive
integers below a hyperbola. The arbitrary weight version is suitable for
both rational additive characters and real-frequency exponential sums.
-/

noncomputable section
open scoped BigOperators

namespace Problem337.Vaughan

/-- Positive lattice points below the multiplicative hyperbola `a*b ≤ N`. -/
def hyperbola (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter (fun ab => ab.1 * ab.2 ≤ N)

@[simp] lemma mem_hyperbola {N a b : ℕ} :
    (a, b) ∈ hyperbola N ↔ 1 ≤ a ∧ 1 ≤ b ∧ a * b ≤ N := by
  change ((a, b) ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
    (fun ab => ab.1 * ab.2 ≤ N)) ↔ _
  rw [Finset.mem_filter]
  have hm : (a, b) ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N) ↔
      a ∈ Finset.Icc 1 N ∧ b ∈ Finset.Icc 1 N := Finset.mem_product
  rw [hm]
  simp only [Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨ha, _⟩, ⟨hb, _⟩⟩, hp⟩
    exact ⟨ha, hb, hp⟩
  · rintro ⟨ha, hb, hp⟩
    have haN : a ≤ N := (Nat.le_mul_of_pos_right a (by omega : 0 < b)).trans hp
    have hbN : b ≤ N := (Nat.le_mul_of_pos_left b (by omega : 0 < a)).trans hp
    exact ⟨⟨⟨ha, haN⟩, ⟨hb, hbN⟩⟩, hp⟩

/-- The divisor-antidiagonal fibers partition the positive hyperbola exactly.
The summand may also depend on the product index `n`. -/
theorem sum_divisor_fibers {A : Type*} [AddCommMonoid A]
    (N : ℕ) (F : ℕ → ℕ → ℕ → A) :
    (∑ n ∈ Finset.Icc 1 N, ∑ ab ∈ n.divisorsAntidiagonal, F n ab.1 ab.2) =
      ∑ ab ∈ hyperbola N, F (ab.1 * ab.2) ab.1 ab.2 := by
  rw [Finset.sum_sigma']
  apply Finset.sum_nbij'
    (fun x : Sigma (fun _n : ℕ => ℕ × ℕ) => x.2)
    (fun ab : ℕ × ℕ => (⟨ab.1 * ab.2, ab⟩ : Sigma (fun _n : ℕ => ℕ × ℕ)))
  · rintro ⟨n, a, b⟩ hx
    obtain ⟨hn, hab⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hab
    apply mem_hyperbola.mpr
    change a * b = n at hprod
    change n ≠ 0 at hn0
    have hab0 : a * b ≠ 0 := by rw [hprod]; exact hn0
    exact ⟨Nat.pos_of_ne_zero (left_ne_zero_of_mul hab0),
      Nat.pos_of_ne_zero (right_ne_zero_of_mul hab0), by rw [hprod]; exact hnN⟩
  · rintro ⟨a, b⟩ hab
    obtain ⟨ha, hb, hp⟩ := mem_hyperbola.mp hab
    apply Finset.mem_sigma.mpr
    constructor
    · exact Finset.mem_Icc.mpr ⟨Nat.mul_pos ha hb, hp⟩
    · exact Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, Nat.ne_of_gt (Nat.mul_pos ha hb)⟩
  · rintro ⟨n, a, b⟩ hx
    have hprod := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hx).2).1
    change (⟨a * b, (a, b)⟩ : Sigma (fun _n : ℕ => ℕ × ℕ)) = ⟨n, (a, b)⟩
    rw [hprod]
  · intro ab hab
    rfl
  · rintro ⟨n, a, b⟩ hx
    have hprod := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hx).2).1
    change F n a b = F (a * b) a b
    rw [hprod]

/-- The hyperbola sum as ordinary nested integer intervals. The inner endpoint
is the natural-number quotient `N / a`; the outer interval excludes zero. -/
theorem sum_hyperbola_eq_nested {A : Type*} [AddCommMonoid A]
    (N : ℕ) (F : ℕ → ℕ → A) :
    (∑ ab ∈ hyperbola N, F ab.1 ab.2) =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (N / a), F a b := by
  rw [Finset.sum_sigma']
  apply Finset.sum_nbij'
    (fun ab : ℕ × ℕ => (⟨ab.1, ab.2⟩ : Sigma (fun _a : ℕ => ℕ)))
    (fun x : Sigma (fun _a : ℕ => ℕ) => (x.1, x.2))
  · rintro ⟨a, b⟩ hab
    obtain ⟨ha, hb, hp⟩ := mem_hyperbola.mp hab
    apply Finset.mem_sigma.mpr
    constructor
    · exact Finset.mem_Icc.mpr ⟨ha,
        (Nat.le_mul_of_pos_right a (by omega : 0 < b)).trans hp⟩
    · apply Finset.mem_Icc.mpr
      exact ⟨hb, (Nat.le_div_iff_mul_le (by omega : 0 < a)).mpr (by simpa [mul_comm] using hp)⟩
  · rintro ⟨a, b⟩ hx
    obtain ⟨ha, hb⟩ := Finset.mem_sigma.mp hx
    obtain ⟨ha1, haN⟩ := Finset.mem_Icc.mp ha
    obtain ⟨hb1, hbN⟩ := Finset.mem_Icc.mp hb
    change 1 ≤ a at ha1
    change 1 ≤ b at hb1
    change b ≤ N / a at hbN
    apply mem_hyperbola.mpr
    refine ⟨ha1, hb1, ?_⟩
    have hp := (Nat.le_div_iff_mul_le (by omega : 0 < a)).mp hbN
    simpa [mul_comm] using hp
  · intro ab hab
    rfl
  · intro x hx
    rfl
  · intro ab hab
    rfl

/-- Real arithmetic coefficients with complex weights, the combination used
for the von-Mangoldt exponential sum. -/
theorem sum_real_convolution_hyperbola
    (N : ℕ) (f g : ArithmeticFunction ℝ) (w : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 N, ((f * g) n : ℂ) * w n) =
      ∑ ab ∈ hyperbola N, ((f ab.1 * g ab.2 : ℝ) : ℂ) * w (ab.1 * ab.2) := by
  simp_rw [ArithmeticFunction.mul_apply, Complex.ofReal_sum, Finset.sum_mul]
  exact sum_divisor_fibers N (fun n a b => ((f a * g b : ℝ) : ℂ) * w n)

/-- The traditional nested-interval form of the finite convolution identity. -/
theorem sum_real_convolution_eq_nested
    (N : ℕ) (f g : ArithmeticFunction ℝ) (w : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 N, ((f * g) n : ℂ) * w n) =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (N / a),
        ((f a * g b : ℝ) : ℂ) * w (a * b) := by
  rw [sum_real_convolution_hyperbola]
  exact sum_hyperbola_eq_nested (A := ℂ) N
    (fun a b => ((f a * g b : ℝ) : ℂ) * w (a * b))

end Problem337.Vaughan

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanWeighted

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Problem337.Vaughan

/-- Finite complex weighted sum of a real arithmetic function. -/
def weightedSum (s : Finset ℕ) (w : ℕ → ℂ) (f : ArithmeticFunction ℝ) : ℂ :=
  ∑ n ∈ s, (f n : ℂ) * w n

@[simp] theorem weightedSum_add (s : Finset ℕ) (w : ℕ → ℂ)
    (f g : ArithmeticFunction ℝ) :
    weightedSum s w (f + g) = weightedSum s w f + weightedSum s w g := by
  simp [weightedSum, add_mul, Finset.sum_add_distrib]

@[simp] theorem weightedSum_sub (s : Finset ℕ) (w : ℕ → ℂ)
    (f g : ArithmeticFunction ℝ) :
    weightedSum s w (f - g) = weightedSum s w f - weightedSum s w g := by
  simp [sub_eq_add_neg, weightedSum, add_mul, Finset.sum_add_distrib]

/-- Exact complex weighted Vaughan decomposition, using the canonical cutoff API. -/
theorem weighted_identity (s : Finset ℕ) (w : ℕ → ℂ) (U V : ℕ) :
    weightedSum s w Λ = weightedSum s w (shortPart V Λ) +
      weightedSum s w (shortPart U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) -
      weightedSum s w (typeICoefficient U V * ζ) +
      weightedSum s w (typeIICoefficient U * longPart V Λ) := by
  have h := congrArg (weightedSum s w) (vonMangoldt_identity U V)
  simpa only [weightedSum_add, weightedSum_sub, typeICoefficient, typeIICoefficient] using h

lemma positive_interval (N : ℕ) : Finset.Icc 1 N = Finset.Ioc 0 N := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-- A convolution sum with its outer coefficient factored out. -/
theorem weightedSum_mul (N : ℕ) (w : ℕ → ℂ) (f g : ArithmeticFunction ℝ) :
    weightedSum (Finset.Ioc 0 N) w (f * g) =
      ∑ a ∈ Finset.Ioc 0 N, (f a : ℂ) *
        ∑ b ∈ Finset.Ioc 0 (N / a), (g b : ℂ) * w (a * b) := by
  simpa only [weightedSum, positive_interval, Finset.mul_sum, Complex.ofReal_mul,
    mul_assoc] using sum_real_convolution_eq_nested N f g w

/-- A compactly supported coefficient restricts the outer interval exactly. -/
theorem weightedSum_mul_of_support (N A : ℕ) (w : ℕ → ℂ)
    (f g : ArithmeticFunction ℝ) (hf : ∀ a, A < a → f a = 0) :
    weightedSum (Finset.Ioc 0 N) w (f * g) =
      ∑ a ∈ Finset.Ioc 0 (min A N), (f a : ℂ) *
        ∑ b ∈ Finset.Ioc 0 (N / a), (g b : ℂ) * w (a * b) := by
  rw [weightedSum_mul]
  symm
  apply Finset.sum_subset
  · intro a ha
    obtain ⟨ha0, haAN⟩ := Finset.mem_Ioc.mp ha
    exact Finset.mem_Ioc.mpr ⟨ha0, (le_min_iff.mp haAN).2⟩
  · intro a ha hnot
    have hA : A < a := by
      simp only [Finset.mem_Ioc] at ha hnot
      omega
    simp [hf a hA]

/-- Exact first Type I sum with its actual short cutoff. -/
theorem first_typeI_eq_sum (N U : ℕ) (w : ℕ → ℂ) :
    weightedSum (Finset.Ioc 0 N) w
        (shortPart U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) =
      ∑ a ∈ Finset.Ioc 0 (min U N), ((μ a : ℝ) : ℂ) *
        ∑ b ∈ Finset.Ioc 0 (N / a), (Real.log b : ℂ) * w (a * b) := by
  rw [weightedSum_mul_of_support N U w _ _ (by
    intro a ha
    simp [not_le.mpr ha])]
  apply Finset.sum_congr rfl
  intro a ha
  have haU := (le_min_iff.mp (Finset.mem_Ioc.mp ha).2).1
  simp [haU]

/-- Exact second Type I sum, supported up to the product cutoff. -/
theorem second_typeI_eq_sum (N U V : ℕ) (w : ℕ → ℂ) :
    weightedSum (Finset.Ioc 0 N) w (typeICoefficient U V * ζ) =
      ∑ a ∈ Finset.Ioc 0 (min (U * V) N), (typeICoefficient U V a : ℂ) *
        ∑ b ∈ Finset.Ioc 0 (N / a), w (a * b) := by
  rw [weightedSum_mul_of_support N (U * V) w _ _ (typeICoefficient_eq_zero U V)]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  simp [ArithmeticFunction.zeta_apply_ne (Nat.ne_of_gt (Finset.mem_Ioc.mp hb).1)]

end Problem337.Vaughan

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.FirstDerivativeSum

namespace OAI
open scoped BigOperators

namespace Problem337

/-- A finite integration-by-parts identity with endpoint terms exposed. -/
theorem weighted_difference_sum (a b : ℕ → ℂ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), b j * (a (j + 1) - a j)) =
      b n * a (n + 1) - b 0 * a 0 -
        ∑ j ∈ Finset.range n, (b (j + 1) - b j) * a (j + 1) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

end Problem337

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.ThreePrimePartialSummation

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.ThreePrimeAnalysis

/-- Finite Abel summation controlled by initial sums and total variation. -/
theorem weighted_sum_norm_le_partial_sum_bound
    (a b : ℕ → ℂ) (n : ℕ) (B : ℝ)
    (hprefix : ∀ k ≤ n + 1, ‖∑ j ∈ Finset.range k, a j‖ ≤ B) :
    ‖∑ j ∈ Finset.range (n + 1), b j * a j‖ ≤
      B * (‖b n‖ + ∑ j ∈ Finset.range n, ‖b (j + 1) - b j‖) := by
  let A : ℕ → ℂ := fun k => ∑ j ∈ Finset.range k, a j
  have hdiff (j : ℕ) : A (j + 1) - A j = a j := by
    simp [A, Finset.sum_range_succ]
  have hid := Problem337.weighted_difference_sum A b n
  simp only [hdiff, A, Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero] at hid
  rw [hid]
  calc
    _ ≤ ‖b n * ∑ j ∈ Finset.range (n + 1), a j‖ +
        ‖∑ j ∈ Finset.range n, (b (j + 1) - b j) *
          ∑ i ∈ Finset.range (j + 1), a i‖ := norm_sub_le _ _
    _ ≤ ‖b n‖ * B + ∑ j ∈ Finset.range n, ‖b (j + 1) - b j‖ * B := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hprefix (n + 1) le_rfl) (norm_nonneg _)
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hprefix (j + 1) (by
          have := Finset.mem_range.mp hj
          omega)) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

end Problem337.ThreePrimeAnalysis

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanTypeI

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Problem337.Vaughan

/-- Indexing positive initial intervals by a zero-based range. -/
lemma sum_Ioc_zero_eq_sum_range_succ {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (N : ℕ) :
    (∑ j ∈ Finset.Ioc 0 N, f j) = ∑ j ∈ Finset.range N, f (j + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le N), Finset.sum_range_succ, ih]

/-- Adding a logarithmic weight costs at most twice the endpoint logarithm.
The initial-sum bound remains explicit; no cancellation estimate is assumed silently. -/
theorem log_weighted_sum_norm_le (w : ℕ → ℂ) (N : ℕ) (B : ℝ)
    (hprefix : ∀ k ≤ N, ‖∑ j ∈ Finset.Ioc 0 k, w j‖ ≤ B) :
    ‖∑ j ∈ Finset.Ioc 0 N, (Real.log j : ℂ) * w j‖ ≤
      2 * B * Real.log N := by
  cases N with
  | zero => simp
  | succ n =>
    have hlog (j : ℕ) : 0 ≤ Real.log (j + 1 : ℕ) :=
      Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j))
    have hmono (j : ℕ) : Real.log (j + 1 : ℕ) ≤ Real.log (j + 1 + 1 : ℕ) := by
      apply Real.log_le_log
      · positivity
      · exact_mod_cast Nat.le_succ (j + 1)
    have hvar : (∑ j ∈ Finset.range n,
        ‖(Real.log (j + 1 + 1 : ℕ) : ℂ) - (Real.log (j + 1 : ℕ) : ℂ)‖) =
        Real.log (n + 1 : ℕ) := by
      calc
        _ = ∑ j ∈ Finset.range n,
            (Real.log (j + 1 + 1 : ℕ) - Real.log (j + 1 : ℕ)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (sub_nonneg.mpr (hmono j))]
        _ = _ := by
          simpa using Finset.sum_range_sub (fun j => Real.log (j + 1 : ℕ)) n
    have h := ThreePrimeAnalysis.weighted_sum_norm_le_partial_sum_bound
      (fun j => w (j + 1)) (fun j => (Real.log (j + 1 : ℕ) : ℂ)) n B (by
        intro k hk
        simpa only [sum_Ioc_zero_eq_sum_range_succ] using hprefix k hk)
    rw [hvar, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hlog n)] at h
    rw [sum_Ioc_zero_eq_sum_range_succ]
    convert h using 1
    ring

/-- Type I logarithmic bilinear estimate for coefficients bounded by one. -/
theorem norm_log_bilinear_sum_le (w : ℕ → ℂ) (N A : ℕ) (c B : ℕ → ℝ)
    (hA : A ≤ N)
    (hc : ∀ a ∈ Finset.Ioc 0 A, |c a| ≤ 1)
    (hprefix : ∀ a ∈ Finset.Ioc 0 A, ∀ k ≤ N / a,
      ‖∑ b ∈ Finset.Ioc 0 k, w (a * b)‖ ≤ B a) :
    ‖∑ a ∈ Finset.Ioc 0 A, (c a : ℂ) *
        ∑ b ∈ Finset.Ioc 0 (N / a), (Real.log b : ℂ) * w (a * b)‖ ≤
      2 * Real.log N * ∑ a ∈ Finset.Ioc 0 A, B a := by
  calc
    _ ≤ ∑ a ∈ Finset.Ioc 0 A,
        ‖(c a : ℂ) * ∑ b ∈ Finset.Ioc 0 (N / a),
          (Real.log b : ℂ) * w (a * b)‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ Finset.Ioc 0 A, 2 * Real.log N * B a := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨ha0, haA⟩ := Finset.mem_Ioc.mp ha
      have haN := haA.trans hA
      have hq : 1 ≤ N / a := (Nat.le_div_iff_mul_le ha0).mpr (by simpa using haN)
      have hB : 0 ≤ B a := by simpa using hprefix a ha 0 (Nat.zero_le _)
      have hlog : Real.log (N / a : ℕ) ≤ Real.log N := by
        apply Real.log_le_log
        · exact_mod_cast (Nat.zero_lt_of_lt hq)
        · exact_mod_cast Nat.div_le_self N a
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        _ ≤ 1 * ‖∑ b ∈ Finset.Ioc 0 (N / a),
            (Real.log b : ℂ) * w (a * b)‖ :=
          mul_le_mul_of_nonneg_right (hc a ha) (norm_nonneg _)
        _ ≤ 2 * B a * Real.log (N / a : ℕ) := by
          simpa using log_weighted_sum_norm_le (fun b => w (a * b)) (N / a) (B a)
            (hprefix a ha)
        _ ≤ 2 * Real.log N * B a := by
          nlinarith [mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * B a by positivity)]
    _ = _ := by rw [Finset.mul_sum]

/-- Type I bilinear estimate for coefficients with the logarithmic majorant. -/
theorem norm_bilinear_sum_le_log (w : ℕ → ℂ) (N A : ℕ) (c B : ℕ → ℝ)
    (hA : A ≤ N)
    (hc : ∀ a ∈ Finset.Ioc 0 A, |c a| ≤ Real.log a)
    (hinner : ∀ a ∈ Finset.Ioc 0 A,
      ‖∑ b ∈ Finset.Ioc 0 (N / a), w (a * b)‖ ≤ B a) :
    ‖∑ a ∈ Finset.Ioc 0 A, (c a : ℂ) *
        ∑ b ∈ Finset.Ioc 0 (N / a), w (a * b)‖ ≤
      Real.log N * ∑ a ∈ Finset.Ioc 0 A, B a := by
  calc
    _ ≤ ∑ a ∈ Finset.Ioc 0 A,
        ‖(c a : ℂ) * ∑ b ∈ Finset.Ioc 0 (N / a), w (a * b)‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ Finset.Ioc 0 A, Real.log N * B a := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨ha0, haA⟩ := Finset.mem_Ioc.mp ha
      have hB : 0 ≤ B a := (norm_nonneg _).trans (hinner a ha)
      have hlog : Real.log a ≤ Real.log N := Real.log_le_log
        (by exact_mod_cast ha0) (by exact_mod_cast haA.trans hA)
      have hlogN : 0 ≤ Real.log N := (abs_nonneg _).trans ((hc a ha).trans hlog)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul ((hc a ha).trans hlog) (hinner a ha) (norm_nonneg _) hlogN
    _ = _ := by rw [Finset.mul_sum]

/-- The first Vaughan Type I term in its finite bilinear form. -/
theorem first_typeI_sum_bound (w : ℕ → ℂ) (N U : ℕ) (B : ℕ → ℝ)
    (hprefix : ∀ a ∈ Finset.Ioc 0 (min U N), ∀ k ≤ N / a,
      ‖∑ b ∈ Finset.Ioc 0 k, w (a * b)‖ ≤ B a) :
    ‖∑ a ∈ Finset.Ioc 0 (min U N), ((μ a : ℝ) : ℂ) *
        ∑ b ∈ Finset.Ioc 0 (N / a), (Real.log b : ℂ) * w (a * b)‖ ≤
      2 * Real.log N * ∑ a ∈ Finset.Ioc 0 (min U N), B a := by
  apply norm_log_bilinear_sum_le w N (min U N) (fun a => (μ a : ℝ)) B
    (min_le_right _ _) _ hprefix
  intro a ha
  exact abs_real_moebius_le_one a

/-- The second Vaughan Type I term in its finite bilinear form. -/
theorem second_typeI_sum_bound (w : ℕ → ℂ) (N U V : ℕ) (B : ℕ → ℝ)
    (hinner : ∀ a ∈ Finset.Ioc 0 (min (U * V) N),
      ‖∑ b ∈ Finset.Ioc 0 (N / a), w (a * b)‖ ≤ B a) :
    ‖∑ a ∈ Finset.Ioc 0 (min (U * V) N), (typeICoefficient U V a : ℂ) *
        ∑ b ∈ Finset.Ioc 0 (N / a), w (a * b)‖ ≤
      Real.log N * ∑ a ∈ Finset.Ioc 0 (min (U * V) N), B a := by
  exact norm_bilinear_sum_le_log w N (min (U * V) N) (typeICoefficient U V) B
    (min_le_right _ _) (fun a _ => abs_typeICoefficient_le_log U V a) hinner

/-- First Type I estimate directly for the actual Vaughan convolution. -/
theorem first_typeI_bound (w : ℕ → ℂ) (N U : ℕ) (B : ℕ → ℝ)
    (hprefix : ∀ a ∈ Finset.Ioc 0 (min U N), ∀ k ≤ N / a,
      ‖∑ b ∈ Finset.Ioc 0 k, w (a * b)‖ ≤ B a) :
    ‖weightedSum (Finset.Ioc 0 N) w
        (shortPart U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)‖ ≤
      2 * Real.log N * ∑ a ∈ Finset.Ioc 0 (min U N), B a := by
  rw [first_typeI_eq_sum]
  exact first_typeI_sum_bound w N U B hprefix

/-- Second Type I estimate directly for the actual Vaughan convolution. -/
theorem second_typeI_bound (w : ℕ → ℂ) (N U V : ℕ) (B : ℕ → ℝ)
    (hinner : ∀ a ∈ Finset.Ioc 0 (min (U * V) N),
      ‖∑ b ∈ Finset.Ioc 0 (N / a), w (a * b)‖ ≤ B a) :
    ‖weightedSum (Finset.Ioc 0 N) w (typeICoefficient U V * ζ)‖ ≤
      Real.log N * ∑ a ∈ Finset.Ioc 0 (min (U * V) N), B a := by
  rw [second_typeI_eq_sum]
  exact second_typeI_sum_bound w N U V B hinner

end Problem337.Vaughan

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanDecomposition

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Problem337.Vaughan

/-- Taking a short part restricts a finite weighted sum to the smaller interval. -/
theorem weightedSum_shortPart (N V : ℕ) (w : ℕ → ℂ) (f : ArithmeticFunction ℝ) :
    weightedSum (Finset.Ioc 0 N) w (shortPart V f) =
      weightedSum (Finset.Ioc 0 (min V N)) w f := by
  unfold weightedSum
  calc
    _ = ∑ n ∈ Finset.Ioc 0 (min V N), (shortPart V f n : ℂ) * w n := by
      symm
      apply Finset.sum_subset
      · intro n hn
        obtain ⟨hn0, hnVN⟩ := Finset.mem_Ioc.mp hn
        exact Finset.mem_Ioc.mpr ⟨hn0, (le_min_iff.mp hnVN).2⟩
      · intro n hn hnot
        have hV : ¬ n ≤ V := by
          simp only [Finset.mem_Ioc] at hn hnot
          omega
        simp [hV]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [(le_min_iff.mp (Finset.mem_Ioc.mp hn).2).1]

/-- The initial von Mangoldt segment has the elementary `V log V` bound. -/
theorem norm_short_vonMangoldt_sum_le (N V : ℕ) (w : ℕ → ℂ)
    (hw : ∀ n ∈ Finset.Ioc 0 N, ‖w n‖ ≤ 1) :
    ‖weightedSum (Finset.Ioc 0 N) w (shortPart V Λ)‖ ≤
      (V : ℝ) * Real.log V := by
  rw [weightedSum_shortPart]
  unfold weightedSum
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 (min V N), ‖(Λ n : ℂ) * w n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Ioc 0 (min V N), Real.log V := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hn0, hnVN⟩ := Finset.mem_Ioc.mp hn
      obtain ⟨hnV, hnN⟩ := le_min_iff.mp hnVN
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      calc
        Λ n * ‖w n‖ ≤ Λ n * 1 := mul_le_mul_of_nonneg_left
          (hw n (Finset.mem_Ioc.mpr ⟨hn0, hnN⟩)) ArithmeticFunction.vonMangoldt_nonneg
        _ ≤ Real.log n := by simpa using (ArithmeticFunction.vonMangoldt_le_log (n := n))
        _ ≤ Real.log V := Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast hnV)
    _ = (min V N : ℕ) * Real.log V := by simp
    _ ≤ (V : ℝ) * Real.log V := mul_le_mul_of_nonneg_right
      (by exact_mod_cast min_le_left V N) (Real.log_natCast_nonneg V)

/-- The actual Type II term is a hyperbola with both short factors removed. -/
theorem typeII_eq_hyperbola (N U V : ℕ) (w : ℕ → ℂ) :
    weightedSum (Finset.Ioc 0 N) w (typeIICoefficient U * longPart V Λ) =
      ∑ d ∈ (hyperbola N).filter (fun d => U < d.1 ∧ V < d.2),
        (typeIICoefficient U d.1 : ℂ) * (Λ d.2 : ℂ) * w (d.1 * d.2) := by
  unfold weightedSum
  rw [← positive_interval N, sum_real_convolution_hyperbola, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hU : U < d.1
  · by_cases hV : V < d.2 <;> simp [hU, hV]
  · simp [hU, typeIICoefficient_eq_zero U d.1 (not_lt.mp hU)]

end Problem337.Vaughan

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.DivisorSquareMean

namespace OAI
/-!
# An elementary mean-square bound for the divisor function

The pointwise majorant `tau^2 ≤ zeta^4` and the elementary harmonic-sum
bound supply the coefficient energy used in finite Type-II estimates.
-/

noncomputable section

open scoped BigOperators ArithmeticFunction.zeta
open Finset ArithmeticFunction

namespace Problem337.DivisorSquareMean

lemma square_le_sigma_convolution_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (k + 1) ^ 2 ≤ (sigma 0 * sigma 0) (p ^ k) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => sigma 0 a * sigma 0 b),
    Nat.sum_divisors_prime_pow hp]
  calc
    (k + 1) ^ 2 = ∑ i ∈ range (k + 1), (k + 1) := by simp [pow_two]
    _ ≤ ∑ i ∈ range (k + 1), sigma 0 (p ^ i) * sigma 0 (p ^ k / p ^ i) := by
      apply sum_le_sum
      intro i hi
      have hik : i ≤ k := by simpa using hi
      rw [Nat.pow_div hik hp.pos,
        sigma_zero_apply_prime_pow hp, sigma_zero_apply_prime_pow hp]
      have hsub : i + (k - i) = k := Nat.add_sub_of_le hik
      nlinarith

theorem card_divisors_sq_le_convolution (n : ℕ) :
    n.divisors.card ^ 2 ≤ (sigma 0 * sigma 0) n := by
  by_cases hn : n = 0
  · simp [hn]
  have hf : IsMultiplicative (sigma 0 * sigma 0) :=
    isMultiplicative_sigma.mul isMultiplicative_sigma
  rw [Nat.card_divisors hn, ← prod_pow,
    hf.multiplicative_factorization (sigma 0 * sigma 0) hn]
  change (∏ p ∈ n.primeFactors, (n.factorization p + 1) ^ 2) ≤
    ∏ p ∈ n.factorization.support, (sigma 0 * sigma 0) (p ^ n.factorization p)
  rw [Nat.support_factorization]
  exact prod_le_prod fun p hp =>
    square_le_sigma_convolution_prime_pow (Nat.prime_of_mem_primeFactors hp) _

theorem card_divisors_sq_le_zeta_four (n : ℕ) :
    n.divisors.card ^ 2 ≤ (ζ ^ 4) n := by
  have hs : sigma 0 = ζ * ζ := by
    rw [← zeta_mul_pow_eq_sigma, pow_zero_eq_zeta]
  convert card_divisors_sq_le_convolution n using 1
  rw [hs]
  congr 1
  ring

lemma real_harmonic_eq_sum (N : ℕ) :
    (harmonic N : ℝ) = ∑ n ∈ Ioc 0 N, (n : ℝ)⁻¹ := by
  have hset : Ioc 0 N = Icc 1 N := by
    ext n
    simp only [mem_Ioc, mem_Icc]
    omega
  simp [hset, harmonic_eq_sum_Icc]

lemma real_harmonic_nonneg (N : ℕ) : 0 ≤ (harmonic N : ℝ) := by
  rw [real_harmonic_eq_sum]
  positivity

lemma real_harmonic_mono {M N : ℕ} (h : M ≤ N) :
    (harmonic M : ℝ) ≤ (harmonic N : ℝ) := by
  rw [real_harmonic_eq_sum, real_harmonic_eq_sum]
  exact sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right h)
    (fun _ _ _ => by positivity)

/-- The summatory `(k+1)`-fold divisor function costs at most `k` harmonic factors. -/
theorem sum_zeta_pow_le_harmonic (k N : ℕ) :
    (∑ n ∈ Ioc 0 N, (ζ ^ (k + 1)) n : ℕ) ≤
      (N : ℝ) * (harmonic N : ℝ) ^ k := by
  induction k generalizing N with
  | zero =>
    rw [Nat.zero_add, pow_one, sum_Ioc_zeta, pow_zero, mul_one]
  | succ k ih =>
    rw [show k + 1 + 1 = (k + 1) + 1 by omega, pow_succ',
      sum_Ioc_mul_eq_sum_sum]
    simp only [Nat.cast_sum, Nat.cast_mul]
    calc
      ∑ n ∈ Ioc 0 N, (ζ n : ℝ) *
          (∑ m ∈ Ioc 0 (N / n), ((ζ ^ (k + 1)) m : ℝ))
        ≤ ∑ n ∈ Ioc 0 N, ((N : ℝ) / n) * (harmonic N : ℝ) ^ k := by
          apply sum_le_sum
          intro n hn
          have hn0 : n ≠ 0 := (mem_Ioc.mp hn).1.ne'
          rw [zeta_apply_ne hn0, Nat.cast_one, one_mul]
          have hi := ih (N / n)
          simp only [Nat.cast_sum] at hi
          exact hi.trans (mul_le_mul Nat.cast_div_le
            (pow_le_pow_left₀ (real_harmonic_nonneg _) (real_harmonic_mono (Nat.div_le_self N n)) k)
            (pow_nonneg (real_harmonic_nonneg _) _) (by positivity))
      _ = (N : ℝ) * (harmonic N : ℝ) ^ (k + 1) := by
        simp_rw [div_eq_mul_inv, mul_assoc]
        rw [← mul_sum, ← sum_mul, ← real_harmonic_eq_sum, pow_succ]
        ring

/-- Sharp elementary harmonic form of the divisor mean-square bound. -/
theorem sum_card_divisors_sq_le_harmonic (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (n.divisors.card : ℝ) ^ 2) ≤
      (N : ℝ) * (harmonic N : ℝ) ^ 3 := by
  calc
    (∑ n ∈ Ioc 0 N, (n.divisors.card : ℝ) ^ 2)
      ≤ (∑ n ∈ Ioc 0 N, (ζ ^ 4) n : ℕ) := by
        rw [Nat.cast_sum]
        apply sum_le_sum
        intro n hn
        have h : ((n.divisors.card ^ 2 : ℕ) : ℝ) ≤ (((ζ ^ 4) n : ℕ) : ℝ) :=
          Nat.cast_le.mpr (card_divisors_sq_le_zeta_four n)
        simpa only [Nat.cast_pow] using h
    _ ≤ (N : ℝ) * (harmonic N : ℝ) ^ 3 := by
      have h := sum_zeta_pow_le_harmonic 3 N
      simp only [show (3 : ℕ) + 1 = 4 from rfl] at h
      exact h

/-- The classical elementary `N (1 + log N)^3` divisor mean square, including `N = 0`. -/
theorem sum_card_divisors_sq_le_log (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (n.divisors.card : ℝ) ^ 2) ≤
      (N : ℝ) * (1 + Real.log N) ^ 3 := by
  exact (sum_card_divisors_sq_le_harmonic N).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (real_harmonic_nonneg N) (harmonic_le_one_add_log N) 3)
      (Nat.cast_nonneg N))

/-- A finite subinterval/subset version, allowing a uniform coefficient multiplier. -/
theorem sum_norm_sq_le_log_of_subset {E : Type*} [SeminormedAddCommGroup E]
    (b : ℕ → E) (T : Finset ℕ) (N : ℕ) (B : ℝ)
    (hT : T ⊆ Ioc 0 N)
    (hb : ∀ n ∈ T, ‖b n‖ ≤ B * (n.divisors.card : ℝ)) :
    (∑ n ∈ T, ‖b n‖ ^ 2) ≤ B ^ 2 * ((N : ℝ) * (1 + Real.log N) ^ 3) := by
  calc
    (∑ n ∈ T, ‖b n‖ ^ 2)
      ≤ ∑ n ∈ T, (B * (n.divisors.card : ℝ)) ^ 2 :=
        sum_le_sum fun n hn => pow_le_pow_left₀ (norm_nonneg _) (hb n hn) 2
    _ = B ^ 2 * ∑ n ∈ T, (n.divisors.card : ℝ) ^ 2 := by
      simp_rw [mul_pow]
      rw [mul_sum]
    _ ≤ B ^ 2 * ∑ n ∈ Ioc 0 N, (n.divisors.card : ℝ) ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hT (fun _ _ _ => sq_nonneg _)) (sq_nonneg B)
    _ ≤ B ^ 2 * ((N : ℝ) * (1 + Real.log N) ^ 3) :=
      mul_le_mul_of_nonneg_left (sum_card_divisors_sq_le_log N) (sq_nonneg B)

end Problem337.DivisorSquareMean

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanDyadicDecomposition

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Finset

namespace Problem337.Vaughan

lemma long_hyperbola_eq_filtered_product (N U V : ℕ) :
    (hyperbola N).filter (fun d => U < d.1 ∧ V < d.2) =
      (Ioc U N ×ˢ Ioc V N).filter (fun d => d.1 * d.2 ≤ N) := by
  ext d
  rcases d with ⟨a, b⟩
  simp only [mem_filter, mem_hyperbola, mem_product, mem_Ioc]
  constructor
  · rintro ⟨⟨ha, hb, hp⟩, hU, hV⟩
    exact ⟨⟨⟨hU, (Nat.le_mul_of_pos_right a hb).trans hp⟩,
      ⟨hV, (Nat.le_mul_of_pos_left b ha).trans hp⟩⟩, hp⟩
  · rintro ⟨⟨⟨hU, ha⟩, ⟨hV, hb⟩⟩, hp⟩
    exact ⟨⟨by omega, by omega, hp⟩, hU, hV⟩

/-- The dyadic block with the actual arithmetic coefficients in Vaughan's identity. -/
def typeIIBlock (N U V j : ℕ) (w : ℕ → ℂ) : ℂ :=
  VaughanDyadic.block N U V j
    (fun m n => (typeIICoefficient U m : ℂ) * (Λ n : ℂ) * w (m * n))

/-- No arithmetic coefficient or hyperbolic cutoff is lost in dyadic decomposition. -/
theorem typeII_eq_sum_dyadic_blocks (N U V : ℕ) (w : ℕ → ℂ) :
    weightedSum (Ioc 0 N) w (typeIICoefficient U * longPart V Λ) =
      ∑ j ∈ range (Nat.log 2 N + 1), typeIIBlock N U V j w := by
  rw [typeII_eq_hyperbola, long_hyperbola_eq_filtered_product]
  exact VaughanDyadic.sum_filtered_product_eq_sum_blocks (E := ℂ) N U V
    (fun m n => (typeIICoefficient U m : ℂ) * (Λ n : ℂ) * w (m * n))

/-- A genuine uniform block bound has only a logarithmic decomposition cost. -/
theorem norm_typeII_le_dyadic_log_budget (N U V : ℕ) (w : ℕ → ℂ)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ j < Nat.log 2 N + 1, ‖typeIIBlock N U V j w‖ ≤ B) :
    ‖weightedSum (Ioc 0 N) w (typeIICoefficient U * longPart V Λ)‖ ≤
      (1 + Real.log N / Real.log 2) * B := by
  let F : ℕ → ℕ → ℂ :=
    fun m n => (typeIICoefficient U m : ℂ) * (Λ n : ℂ) * w (m * n)
  have he : weightedSum (Ioc 0 N) w (typeIICoefficient U * longPart V Λ) =
      ∑ m ∈ Ioc U N, ∑ n ∈ Ioc V (N / m), F m n := by
    rw [typeII_eq_sum_dyadic_blocks, VaughanDyadic.sum_hyperbola_eq_sum_blocks]
    rfl
  rw [he]
  exact VaughanDyadic.norm_hyperbola_le_log_budget N U V F B hB0 hB

/-- Sharp unconditional row energy for the actual Type II coefficient in a dyadic shell. -/
theorem typeII_shell_energy_le (N U j : ℕ) :
    (∑ m ∈ VaughanDyadic.shell U N j, ‖(typeIICoefficient U m : ℂ)‖ ^ 2) ≤
      (2 ^ (j + 1) : ℕ) * (1 + Real.log (2 ^ (j + 1) : ℕ)) ^ 3 := by
  have hT : VaughanDyadic.shell U N j ⊆ Ioc 0 (2 ^ (j + 1)) := by
    intro m hm
    have h := VaughanDyadic.mem_shell.mp hm
    exact mem_Ioc.mpr ⟨lt_of_le_of_lt (Nat.zero_le U) h.1, h.2.2.2.le⟩
  have h := DivisorSquareMean.sum_norm_sq_le_log_of_subset
    (fun m => (typeIICoefficient U m : ℂ)) (VaughanDyadic.shell U N j)
    (2 ^ (j + 1)) 1 hT (by
      intro m hm
      simpa only [Complex.norm_real, Real.norm_eq_abs, one_mul] using
        abs_typeIICoefficient_le_divisors_card U m)
  simpa only [one_pow, one_mul] using h

end Problem337.Vaughan

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.HyperbolaCorrelation

namespace OAI
noncomputable section
open scoped BigOperators
open ComplexConjugate

namespace Problem337.HyperbolaCorrelation

/-- The common support of two columns cut off by a product bound. -/
theorem product_support_iff (X m n₁ n₂ : ℕ) (hn : 0 < max n₁ n₂) :
    (m * n₁ ≤ X ∧ m * n₂ ≤ X) ↔ m ≤ X / max n₁ n₂ := by
  rw [Nat.le_div_iff_mul_le hn, mul_max, max_le_iff]

/-- Intersecting two hyperbolic columns leaves an ordinary integer interval.
Empty intervals and a zero value of one of the two column indices are allowed. -/
theorem filter_common_support (X L U n₁ n₂ : ℕ) (hn : 0 < max n₁ n₂) :
    (Finset.Icc L U).filter (fun m => m * n₁ ≤ X ∧ m * n₂ ≤ X) =
      Finset.Icc L (min U (X / max n₁ n₂)) := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc, product_support_iff X m n₁ n₂ hn,
    le_min_iff]
  tauto

/-- Exact correlation identity for arbitrary complex hyperbolic columns. -/
theorem cutoff_correlation (X L U n₁ n₂ : ℕ) (hn : 0 < max n₁ n₂)
    (f g : ℕ → ℂ) :
    (∑ m ∈ Finset.Icc L U,
      (if m * n₁ ≤ X then f m else 0) *
        conj (if m * n₂ ≤ X then g m else 0)) =
      ∑ m ∈ Finset.Icc L (min U (X / max n₁ n₂)), f m * conj (g m) := by
  rw [← filter_common_support X L U n₁ n₂ hn, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases h₁ : m * n₁ ≤ X <;> by_cases h₂ : m * n₂ ≤ X <;> simp [h₁, h₂]

/-- The standard real-frequency complex phase. -/
def phase (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

@[simp] theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := by
  simp [phase, Complex.norm_exp]

theorem phase_sub (x y : ℝ) : phase (x - y) = phase x * conj (phase y) := by
  simp only [phase, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

/-- A column of a bilinear exponential sum with its actual hyperbolic support. -/
def column (α : ℝ) (X n m : ℕ) : ℂ :=
  if m * n ≤ X then phase (α * (m : ℝ) * (n : ℝ)) else 0

/-- The off-diagonal correlation is a geometric exponential sum on one interval,
not a sum over an arbitrary subset. Differences are taken in `ℝ`, so negative
frequencies are retained rather than truncated by natural subtraction. -/
theorem column_correlation (α : ℝ) (X L U n₁ n₂ : ℕ)
    (hn : 0 < max n₁ n₂) :
    (∑ m ∈ Finset.Icc L U, column α X n₁ m * conj (column α X n₂ m)) =
      ∑ m ∈ Finset.Icc L (min U (X / max n₁ n₂)),
        phase (α * (m : ℝ) * ((n₁ : ℝ) - (n₂ : ℝ))) := by
  unfold column
  rw [cutoff_correlation X L U n₁ n₂ hn]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← phase_sub]
  congr 1
  ring

end Problem337.HyperbolaCorrelation

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanBilinear

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.VaughanBilinear

/-- The exact correlation expansion of a weighted finite bilinear energy.
No distinctness or unit-modulus assumption on the phase is needed. -/
theorem energy_identity {α β : Type*} (s : Finset α) (t : Finset β)
    (b : β → ℂ) (z : α → β → ℂ) :
    ((∑ m ∈ s, ‖∑ n ∈ t, b n * z m n‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ t, ∑ k ∈ t, b n * (starRingEnd ℂ) (b k) *
        ∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k) := by
  classical
  have hpoint (m : α) :
      (‖∑ n ∈ t, b n * z m n‖ ^ 2 : ℂ) =
        ∑ n ∈ t, ∑ k ∈ t,
          b n * (starRingEnd ℂ) (b k) *
            (z m n * (starRingEnd ℂ) (z m k)) := by
    rw [← Complex.mul_conj']
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro k hk
    ring
  push_cast
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]

/-- Bounding a bilinear energy by absolute correlations retains the
arithmetic cancellation in the first variable. -/
theorem energy_le_correlations {α β : Type*} (s : Finset α) (t : Finset β)
    (b : β → ℂ) (z : α → β → ℂ) :
    (∑ m ∈ s, ‖∑ n ∈ t, b n * z m n‖ ^ 2) ≤
      ∑ n ∈ t, ∑ k ∈ t, ‖b n‖ * ‖b k‖ *
        ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖ := by
  have h := congrArg Complex.re (energy_identity s t b z)
  simp only [Complex.ofReal_re, Complex.re_sum] at h
  rw [h]
  apply Finset.sum_le_sum
  intro n hn
  apply Finset.sum_le_sum
  intro k hk
  calc
    _ ≤ ‖b n * (starRingEnd ℂ) (b k) *
        ∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖ := Complex.re_le_norm _
    _ = _ := by simp only [norm_mul, Complex.norm_conj]

/-- Finite Type-II Cauchy--Schwarz, with the full correlation sum explicit.
This is an unconditional algebraic bound, not a minor-arc hypothesis. -/
theorem norm_bilinear_sq_le {α β : Type*} (s : Finset α) (t : Finset β)
    (a : α → ℂ) (b : β → ℂ) (z : α → β → ℂ) :
    ‖∑ m ∈ s, a m * ∑ n ∈ t, b n * z m n‖ ^ 2 ≤
      (∑ m ∈ s, ‖a m‖ ^ 2) *
        (∑ n ∈ t, ∑ k ∈ t, ‖b n‖ * ‖b k‖ *
          ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖) := by
  calc
    _ ≤ (∑ m ∈ s, ‖a m‖ * ‖∑ n ∈ t, b n * z m n‖) ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa only [norm_mul] using
        norm_sum_le s (fun m => a m * ∑ n ∈ t, b n * z m n)
    _ ≤ (∑ m ∈ s, ‖a m‖ ^ 2) *
        ∑ m ∈ s, ‖∑ n ∈ t, b n * z m n‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq s _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (energy_le_correlations s t b z)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- The standard real additive phase, with the `2π` convention. -/
def phase (x : ℝ) : ℂ := Real.fourierChar x

@[simp] theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := Circle.norm_coe _

theorem phase_mul_conj (x y : ℝ) :
    phase x * (starRingEnd ℂ) (phase y) = phase (x - y) := by
  unfold phase
  rw [Circle.starRingEnd_addChar, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  congr 2

theorem phase_nat_mul (x : ℝ) (n : ℕ) : phase (x * n) = phase x ^ n := by
  unfold phase
  rw [mul_comm, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow, Circle.coe_pow]

/-- An exact geometric cancellation bound in a form valid even at resonance. -/
theorem phase_sum_mul_bound (x : ℝ) (M : ℕ) :
    ‖∑ m ∈ Finset.range M, phase (x * m)‖ * ‖1 - phase x‖ ≤ 2 := by
  simp_rw [phase_nat_mul]
  rw [← norm_mul, geom_sum_mul_neg]
  calc
    ‖1 - phase x ^ M‖ ≤ ‖(1 : ℂ)‖ + ‖phase x ^ M‖ := norm_sub_le _ _
    _ = 2 := by simp; norm_num

/-- The usual geometric sum bound away from resonance. -/
theorem phase_sum_le_min (x : ℝ) (M : ℕ) (hx : phase x ≠ 1) :
    ‖∑ m ∈ Finset.range M, phase (x * m)‖ ≤
      min (M : ℝ) (2 / ‖1 - phase x‖) := by
  apply le_min
  · calc
      _ ≤ ∑ m ∈ Finset.range M, ‖phase (x * m)‖ := norm_sum_le _ _
      _ = M := by simp
  · have hpos : 0 < ‖1 - phase x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx.symm)
    exact (le_div_iff₀ hpos).mpr (phase_sum_mul_bound x M)

/-- A total geometric majorant. Resonant frequencies use the trivial bound;
the definition never interprets division by zero as cancellation. -/
def geometricBound (M : ℕ) (x : ℝ) : ℝ :=
  if phase x = 1 then M else min (M : ℝ) (2 / ‖1 - phase x‖)

theorem phase_sum_le_geometricBound (x : ℝ) (M : ℕ) :
    ‖∑ m ∈ Finset.range M, phase (x * m)‖ ≤ geometricBound M x := by
  unfold geometricBound
  split_ifs with hx
  · simp_rw [phase_nat_mul, hx]
    simp
  · exact phase_sum_le_min x M hx

/-- A finite real Schur bound, proved by symmetrizing `2xy ≤ x²+y²`.
The coefficients need not be nonnegative. -/
theorem symmetric_weighted_sum_le {β : Type*} (t : Finset β)
    (f : β → ℝ) (K : β → β → ℝ)
    (hK : ∀ n ∈ t, ∀ k ∈ t, 0 ≤ K n k)
    (hsym : ∀ n ∈ t, ∀ k ∈ t, K n k = K k n) :
    (∑ n ∈ t, ∑ k ∈ t, f n * f k * K n k) ≤
      ∑ n ∈ t, f n ^ 2 * ∑ k ∈ t, K n k := by
  have hfirst : (∑ n ∈ t, ∑ k ∈ t, f n ^ 2 * K n k) =
      ∑ n ∈ t, f n ^ 2 * ∑ k ∈ t, K n k := by
    simp only [Finset.mul_sum]
  have hsecond : (∑ n ∈ t, ∑ k ∈ t, f k ^ 2 * K n k) =
      ∑ n ∈ t, f n ^ 2 * ∑ k ∈ t, K n k := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro k hk
    rw [hsym k hk n hn]
  calc
    _ ≤ ∑ n ∈ t, ∑ k ∈ t,
        (f n ^ 2 * K n k + f k ^ 2 * K n k) / 2 := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro k hk
      nlinarith [mul_nonneg (sq_nonneg (f n - f k)) (hK n hn k hk)]
    _ = ((∑ n ∈ t, ∑ k ∈ t, f n ^ 2 * K n k) +
        (∑ n ∈ t, ∑ k ∈ t, f k ^ 2 * K n k)) / 2 := by
      simp only [add_div, Finset.sum_div, Finset.sum_add_distrib]
    _ = _ := by rw [hfirst, hsecond]; ring

/-- Reversing a correlation conjugates it, hence preserves its norm. -/
theorem correlation_norm_symm {α β : Type*} (s : Finset α)
    (z : α → β → ℂ) (n k : β) :
    ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖ =
      ‖∑ m ∈ s, z m k * (starRingEnd ℂ) (z m n)‖ := by
  have hc : (∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)) =
      (starRingEnd ℂ) (∑ m ∈ s, z m k * (starRingEnd ℂ) (z m n)) := by
    simp only [map_sum, map_mul, starRingEnd_self_apply]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  rw [hc, Complex.norm_conj]

/-- Type-II energy bound using an absolute correlation row bound. Unlike the
bounded-coefficient version, this retains both coefficient squared sums and
therefore applies directly to divisor-coefficient second-moment estimates. -/
theorem norm_bilinear_sq_le_energy {α β : Type*} (s : Finset α) (t : Finset β)
    (a : α → ℂ) (b : β → ℂ) (z : α → β → ℂ) (C : ℝ)
    (hrow : ∀ n ∈ t,
      (∑ k ∈ t, ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖) ≤ C) :
    ‖∑ m ∈ s, a m * ∑ n ∈ t, b n * z m n‖ ^ 2 ≤
      (∑ m ∈ s, ‖a m‖ ^ 2) * C * (∑ n ∈ t, ‖b n‖ ^ 2) := by
  have hweight := symmetric_weighted_sum_le t (fun n => ‖b n‖)
    (fun n k => ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖)
    (fun _ _ _ _ => norm_nonneg _)
    (fun n _ k _ => correlation_norm_symm s z n k)
  have hbound :
      (∑ n ∈ t, ∑ k ∈ t, ‖b n‖ * ‖b k‖ *
        ‖∑ m ∈ s, z m n * (starRingEnd ℂ) (z m k)‖) ≤
      C * ∑ n ∈ t, ‖b n‖ ^ 2 := by
    refine hweight.trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hrow n hn) (sq_nonneg ‖b n‖)
  calc
    _ ≤ _ := norm_bilinear_sq_le s t a b z
    _ ≤ (∑ m ∈ s, ‖a m‖ ^ 2) * (C * ∑ n ∈ t, ‖b n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hbound (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by ring

end Problem337.VaughanBilinear

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.HyperbolaTypeII

namespace OAI
noncomputable section
open scoped BigOperators
open ComplexConjugate

namespace Problem337.HyperbolaCorrelation

lemma phase_eq_vaughan (x : ℝ) : phase x = VaughanBilinear.phase x := rfl

lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  simp only [phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Translation of an integer interval does not affect its geometric-sum bound. -/
theorem phase_sum_Icc_le (x : ℝ) (L U : ℕ) :
    ‖∑ m ∈ Finset.Icc L U, phase (x * (m : ℝ))‖ ≤
      VaughanBilinear.geometricBound (U + 1 - L) x := by
  have hI : Finset.Icc L U = Finset.Ico L (U + 1) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hI, Finset.sum_Ico_eq_sum_range]
  have hsum : (∑ m ∈ Finset.range (U + 1 - L), phase (x * ((L + m : ℕ) : ℝ))) =
      phase (x * L) * ∑ m ∈ Finset.range (U + 1 - L), phase (x * (m : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Nat.cast_add, mul_add, phase_add]
  rw [hsum, norm_mul, norm_phase, one_mul]
  exact VaughanBilinear.phase_sum_le_geometricBound x (U + 1 - L)

lemma geometricBound_mono {M N : ℕ} (hMN : M ≤ N) (x : ℝ) :
    VaughanBilinear.geometricBound M x ≤ VaughanBilinear.geometricBound N x := by
  unfold VaughanBilinear.geometricBound
  split_ifs
  · exact_mod_cast hMN
  · exact min_le_min_right _ (by exact_mod_cast hMN)

/-- A hyperbolic correlation admits the same geometric majorant as a full
interval of rows. The moving endpoint introduces no additional loss. -/
theorem column_correlation_le (α : ℝ) (X L U n₁ n₂ : ℕ)
    (hn : 0 < max n₁ n₂) :
    ‖∑ m ∈ Finset.Icc L U, column α X n₁ m * conj (column α X n₂ m)‖ ≤
      VaughanBilinear.geometricBound (U + 1 - L) (α * ((n₁ : ℝ) - (n₂ : ℝ))) := by
  rw [column_correlation α X L U n₁ n₂ hn]
  have heq : (fun m : ℕ => phase (α * (m : ℝ) * ((n₁ : ℝ) - (n₂ : ℝ)))) =
      (fun m : ℕ => phase ((α * ((n₁ : ℝ) - (n₂ : ℝ))) * (m : ℝ))) := by
    funext m
    congr 1
    ring
  simp_rw [heq]
  exact (phase_sum_Icc_le _ L (min U (X / max n₁ n₂))).trans
    (geometricBound_mono (by omega) _)

end Problem337.HyperbolaCorrelation

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.GeometricCharacterBound

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

/-- Geometric cancellation on the complex unit circle. -/
theorem norm_geometric_sum_le_two_div {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1)
    (N : ℕ) : ‖∑ j ∈ Finset.range N, z ^ j‖ ≤ 2 / ‖z - 1‖ := by
  rw [geom_sum_eq hne, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, hz]

/-- The elementary peak bound for a geometric kernel. -/
theorem norm_geometric_sum_le_card {z : ℂ} (hz : ‖z‖ = 1) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, z ^ j‖ ≤ (N : ℝ) := by
  calc
    ‖∑ j ∈ Finset.range N, z ^ j‖ ≤ ∑ j ∈ Finset.range N, ‖z ^ j‖ := norm_sum_le _ _
    _ = (N : ℝ) := by simp [norm_pow, hz]

/-- The chord distance for a phase of period one. -/
theorem norm_exp_phase_sub_one (x : ℝ) :
    ‖Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) - 1‖ =
      2 * |Real.sin (Real.pi * x)| := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  have heq : 2 * Real.pi * x / 2 = Real.pi * x := by ring
  rw [heq, Real.norm_eq_abs, abs_mul]
  norm_num

/-- Geometric cancellation expressed directly in terms of the phase sine. -/
theorem norm_geometric_phase_sum_le {x : ℝ} (hx : Real.sin (Real.pi * x) ≠ 0)
    (N : ℕ) :
    ‖∑ j ∈ Finset.range N, (Complex.exp (Complex.I * (2 * Real.pi * x : ℝ))) ^ j‖ ≤
      1 / |Real.sin (Real.pi * x)| := by
  have habs : 0 < |Real.sin (Real.pi * x)| := abs_pos.2 hx
  have hne : Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) ≠ 1 := by
    intro h
    have hn := norm_exp_phase_sub_one x
    rw [h, sub_self, norm_zero] at hn
    linarith
  have hbound := norm_geometric_sum_le_two_div
    (Complex.norm_exp_I_mul_ofReal (2 * Real.pi * x)) hne N
  rw [norm_exp_phase_sub_one] at hbound
  convert hbound using 1
  field_simp

/-- Uniform lower bound for the sine away from both ends of a period. -/
theorem sin_pi_mul_lower_on_middle {δ x : ℝ} (hδ : 0 < δ)
    (hleft : δ ≤ x) (hright : x ≤ 1 - δ) :
    2 * δ ≤ Real.sin (Real.pi * x) := by
  have hx0 : 0 ≤ x := le_trans hδ.le hleft
  have hx1 : 0 ≤ 1 - x := by linarith
  by_cases hx : x ≤ 1 / 2
  · have hs := Real.mul_le_sin (x := Real.pi * x)
      (mul_nonneg Real.pi_pos.le hx0) (by nlinarith [Real.pi_pos])
    have heq : 2 / Real.pi * (Real.pi * x) = 2 * x := by field_simp
    rw [heq] at hs
    linarith
  · have hs := Real.mul_le_sin (x := Real.pi * (1 - x))
      (mul_nonneg Real.pi_pos.le hx1)
      (by nlinarith [Real.pi_pos])
    have heq : 2 / Real.pi * (Real.pi * (1 - x)) = 2 * (1 - x) := by field_simp
    rw [heq, show Real.pi * (1 - x) = Real.pi - Real.pi * x by ring,
      Real.sin_pi_sub] at hs
    linarith

end Problem337

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.RationalPhaseSpacing

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RationalPhaseSpacing

/-- A reduced rational approximation with error at most `q⁻²` separates
frequencies whose index difference has absolute value at most `q/2`.
The estimate is uniform over every possible nearest integer. -/
theorem separation_of_rational_approximation
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (h : ℤ) (hne : h ≠ 0) (hsmall : 2 * |h| ≤ (q : ℤ)) (k : ℤ) :
    1 / (2 * (q : ℝ)) ≤ |α * (h : ℝ) - k| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hhpos : (0 : ℤ) < |h| := abs_pos.mpr hne
  have hnotdvd : ¬ (q : ℤ) ∣ h := by
    intro hd
    have hle := Int.le_of_dvd hhpos ((dvd_abs (q : ℤ) h).mpr hd)
    omega
  have hnonzero : a * h - k * (q : ℤ) ≠ 0 := by
    intro hz
    apply hnotdvd
    apply hcop.symm.dvd_of_dvd_mul_left
    refine ⟨k, ?_⟩
    linear_combination hz
  have hinteger : (1 : ℝ) ≤ |(a : ℝ) * h - (k : ℝ) * q| := by
    exact_mod_cast Int.one_le_abs hnonzero
  have hsmallR : (2 : ℝ) * |(h : ℝ)| ≤ q := by exact_mod_cast hsmall
  have herr : (q : ℝ) * |α - (a : ℝ) / q| * |(h : ℝ)| ≤ 1 / 2 := by
    have hb := (le_div_iff₀ (sq_pos_of_pos hqR)).mp happrox
    have hc := mul_le_mul_of_nonneg_left hsmallR
      (mul_nonneg hqR.le (abs_nonneg (α - (a : ℝ) / q)))
    nlinarith
  have hid : (a : ℝ) * h - (k : ℝ) * q =
      (q : ℝ) * (α * h - k) - (q : ℝ) * (α - (a : ℝ) / q) * h := by
    field_simp
    ring
  have htri : |(a : ℝ) * h - (k : ℝ) * q| ≤
      (q : ℝ) * |α * h - k| + (q : ℝ) * |α - (a : ℝ) / q| * |(h : ℝ)| := by
    rw [hid]
    calc
      _ ≤ |(q : ℝ) * (α * h - k)| + |(q : ℝ) * (α - (a : ℝ) / q) * h| :=
        abs_sub _ _
      _ = _ := by simp only [abs_mul, abs_of_pos hqR]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * q)).mpr
  nlinarith

/-- Fractional parts at two nearby distinct integer indices are separated
under the same reduced rational approximation. -/
theorem fract_separation
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (m n : ℤ) (hne : m ≠ n) (hsmall : 2 * |m - n| ≤ (q : ℤ)) :
    1 / (2 * (q : ℝ)) ≤ |Int.fract (α * m) - Int.fract (α * n)| := by
  have hs := separation_of_rational_approximation α a q hq hcop happrox
    (m - n) (sub_ne_zero.mpr hne) hsmall (⌊α * m⌋ - ⌊α * n⌋)
  simpa only [Int.fract, Int.cast_sub, mul_sub, sub_sub_sub_comm] using hs

/-- A canonical finite bin index for the phase of an integer. -/
def phaseBin (q : ℕ) (α : ℝ) (n : ℤ) : ℕ :=
  ⌊2 * (q : ℝ) * Int.fract (α * n)⌋₊

theorem phaseBin_lt (q : ℕ) (hq : 0 < q) (α : ℝ) (n : ℤ) :
    phaseBin q α n < 2 * q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  apply (Nat.floor_lt (mul_nonneg (by positivity) (Int.fract_nonneg (α * (n : ℝ))))).mpr
  push_cast
  nlinarith [Int.fract_lt_one (α * n)]

/-- Bin encoding preserves the multiplicity of indices in every short block:
no two indices have the same bin. -/
theorem phaseBin_injOn
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (A : Finset ℤ) (hspan : ∀ m ∈ A, ∀ n ∈ A, 2 * |m - n| ≤ (q : ℤ)) :
    Set.InjOn (phaseBin q α) A := by
  intro m hm n hn heq
  by_contra hne
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hs := fract_separation α a q hq hcop happrox m n hne (hspan m hm n hn)
  have hmlo := Nat.floor_le (show 0 ≤ 2 * (q : ℝ) * Int.fract (α * m) from mul_nonneg (by positivity) (Int.fract_nonneg _))
  have hnlo := Nat.floor_le (show 0 ≤ 2 * (q : ℝ) * Int.fract (α * n) from mul_nonneg (by positivity) (Int.fract_nonneg _))
  have hmhi := Nat.lt_floor_add_one (2 * (q : ℝ) * Int.fract (α * m))
  have hnhi := Nat.lt_floor_add_one (2 * (q : ℝ) * Int.fract (α * n))
  change phaseBin q α m = phaseBin q α n at heq
  change (phaseBin q α m : ℝ) ≤ _ at hmlo
  change (phaseBin q α n : ℝ) ≤ _ at hnlo
  change _ < (phaseBin q α m : ℝ) + 1 at hmhi
  change _ < (phaseBin q α n : ℝ) + 1 at hnhi
  rw [heq] at hmlo hmhi
  have hlt : |Int.fract (α * m) - Int.fract (α * n)| < 1 / (2 * (q : ℝ)) := by
    apply abs_sub_lt_iff.mpr
    constructor
    · apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * q)).mpr
      nlinarith
    · apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * q)).mpr
      nlinarith
  exact (not_lt_of_ge hs) hlt

/-- A reciprocal truncated at `Y`, with its correct value at the singular
point. The special value is needed for geometric exponential sums. -/
def truncatedInv (Y x : ℝ) : ℝ := if x = 0 then Y else min Y (1 / x)

theorem truncatedInv_nonneg {Y x : ℝ} (hY : 0 ≤ Y) (hx : 0 ≤ x) :
    0 ≤ truncatedInv Y x := by
  unfold truncatedInv
  split_ifs
  · exact hY
  · exact le_min hY (one_div_nonneg.mpr hx)

theorem truncatedInv_le_cap (Y x : ℝ) : truncatedInv Y x ≤ Y := by
  unfold truncatedInv
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/-- Bin majorant for the one-sided reciprocal distance. -/
def binWeight (H : ℕ) (Y : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then Y else (H : ℝ) / j

theorem binWeight_nonneg {H j : ℕ} {Y : ℝ} (hY : 0 ≤ Y) :
    0 ≤ binWeight H Y j := by
  unfold binWeight
  split_ifs
  · exact hY
  · positivity

theorem truncatedInv_fract_le_binWeight (q : ℕ) (hq : 0 < q)
    (Y α : ℝ) (n : ℤ) :
    truncatedInv Y (Int.fract (α * n)) ≤ binWeight (2 * q) Y (phaseBin q α n) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  by_cases hj : phaseBin q α n = 0
  · simpa [binWeight, hj] using truncatedInv_le_cap Y (Int.fract (α * n))
  · have hjpos : (0 : ℝ) < phaseBin q α n := by exact_mod_cast Nat.pos_of_ne_zero hj
    have hlo := Nat.floor_le (show 0 ≤ 2 * (q : ℝ) * Int.fract (α * n)
      from mul_nonneg (by positivity) (Int.fract_nonneg _))
    change (phaseBin q α n : ℝ) ≤ _ at hlo
    have hxpos : 0 < Int.fract (α * n) := by nlinarith [Int.fract_nonneg (α * (n : ℝ))]
    rw [binWeight, ite_eq_right hj, truncatedInv, ite_eq_right (ne_of_gt hxpos)]
    apply (min_le_right _ _).trans
    apply (div_le_div_iff₀ hxpos hjpos).mpr
    push_cast
    simpa using hlo

/-- Summing the bin majorants costs one singular term and a harmonic sum. -/
theorem sum_binWeight_le (H : ℕ) (hH : 0 < H) (Y : ℝ) :
    (∑ j ∈ Finset.range H, binWeight H Y j) ≤
      Y + (H : ℝ) * (1 + Real.log (H : ℝ)) := by
  have hterm (j : ℕ) : binWeight H Y j =
      (if j = 0 then Y else 0) + (H : ℝ) * (1 / (j : ℝ)) := by
    by_cases hj : j = 0
    · simp [binWeight, hj]
    · simp [binWeight, hj, div_eq_mul_inv]
  have hsum : (∑ j ∈ Finset.range H, binWeight H Y j) =
      Y + (H : ℝ) * ∑ j ∈ Finset.range H, (1 / (j : ℝ)) := by
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [hH]
  have hrecip : (∑ j ∈ Finset.range H, (1 / (j : ℝ))) ≤ (harmonic H : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (H + 1), (1 / (j : ℝ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        intro j _ _
        positivity
      _ = (harmonic H : ℝ) := by
        rw [Finset.sum_range_succ']
        simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  rw [hsum]
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left (hrecip.trans (harmonic_le_one_add_log H)) (Nat.cast_nonneg H)

/-- A reduced rational approximation controls the sum of truncated one-sided
reciprocal distances on every short block. No cancellation hypothesis is used. -/
theorem sum_truncatedInv_fract_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (A : Finset ℤ) (hspan : ∀ m ∈ A, ∀ n ∈ A, 2 * |m - n| ≤ (q : ℤ))
    (Y : ℝ) (hY : 0 ≤ Y) :
    (∑ n ∈ A, truncatedInv Y (Int.fract (α * n))) ≤
      Y + (2 * (q : ℝ)) * (1 + Real.log (2 * (q : ℝ))) := by
  classical
  have hinj := phaseBin_injOn α a q hq hcop happrox A hspan
  calc
    _ ≤ ∑ n ∈ A, binWeight (2 * q) Y (phaseBin q α n) := by
      exact Finset.sum_le_sum (fun n _ => truncatedInv_fract_le_binWeight q hq Y α n)
    _ = ∑ j ∈ A.image (phaseBin q α), binWeight (2 * q) Y j := by
      rw [Finset.sum_image]
      exact fun m hm n hn heq => hinj hm hn heq
    _ ≤ ∑ j ∈ Finset.range (2 * q), binWeight (2 * q) Y j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hj
        exact Finset.mem_range.mpr (phaseBin_lt q hq α n)
      · intro j _ _
        exact binWeight_nonneg hY
    _ ≤ _ := by simpa only [Nat.cast_mul, Nat.cast_ofNat] using sum_binWeight_le (2 * q) (by omega) Y

/-- Distance of a real phase to the nearest integer, expressed without a
choice of nearest integer. -/
def intDistance (x : ℝ) : ℝ := min (Int.fract x) (1 - Int.fract x)

@[simp] theorem intDistance_eq_abs_sub_round (x : ℝ) :
    intDistance x = |x - round x| := (abs_sub_round_eq_min x).symm

theorem intDistance_nonneg (x : ℝ) : 0 ≤ intDistance x :=
  le_min (Int.fract_nonneg x) (sub_nonneg.mpr (Int.fract_lt_one x).le)

/-- Two one-sided reciprocal majorants control the nearest-integer one,
including integer phases where the truncation must equal `Y`. -/
theorem truncatedInv_intDistance_le {Y : ℝ} (hY : 0 ≤ Y) (x : ℝ) :
    truncatedInv Y (intDistance x) ≤
      truncatedInv Y (Int.fract x) + truncatedInv Y (Int.fract (-x)) := by
  have hsecond : truncatedInv Y (1 - Int.fract x) ≤ truncatedInv Y (Int.fract (-x)) := by
    by_cases hx : Int.fract x = 0
    · have hneg := Int.fract_neg_eq_zero.mpr hx
      rw [hneg]
      simpa [truncatedInv] using truncatedInv_le_cap Y (1 - Int.fract x)
    · rw [Int.fract_neg hx]
  unfold intDistance
  rcases le_total (Int.fract x) (1 - Int.fract x) with h | h
  · rw [min_eq_left h]
    exact le_add_of_nonneg_right (truncatedInv_nonneg hY (Int.fract_nonneg _))
  · rw [min_eq_right h]
    exact hsecond.trans (le_add_of_nonneg_left (truncatedInv_nonneg hY (Int.fract_nonneg _)))

/-- The classical truncated reciprocal-distance estimate on one short block,
with an explicit constant and correct treatment of integer phases. -/
theorem sum_truncatedInv_intDistance_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (A : Finset ℤ) (hspan : ∀ m ∈ A, ∀ n ∈ A, 2 * |m - n| ≤ (q : ℤ))
    (Y : ℝ) (hY : 0 ≤ Y) :
    (∑ n ∈ A, truncatedInv Y (intDistance (α * n))) ≤
      2 * Y + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ))) := by
  have hnegative : |(-α) - ((-a : ℤ) : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 := by
    simpa only [Int.cast_neg, neg_div, neg_sub_neg, abs_sub_comm] using happrox
  have hp := sum_truncatedInv_fract_le α a q hq hcop happrox A hspan Y hY
  have hn := sum_truncatedInv_fract_le (-α) (-a) q hq hcop.neg_left hnegative A hspan Y hY
  have hs : (∑ n ∈ A, truncatedInv Y (intDistance (α * n))) ≤
      (∑ n ∈ A, truncatedInv Y (Int.fract (α * n))) +
        ∑ n ∈ A, truncatedInv Y (Int.fract ((-α) * n)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n _
    simpa only [neg_mul] using truncatedInv_intDistance_le hY (α * n)
  linarith

/-- Any interval of `floor(q/2)+1` consecutive integers is a short block. -/
theorem short_interval_span (q : ℕ) (L : ℤ) :
    ∀ m ∈ Finset.Ico L (L + (q / 2 : ℕ) + 1),
      ∀ n ∈ Finset.Ico L (L + (q / 2 : ℕ) + 1),
        2 * |m - n| ≤ (q : ℤ) := by
  intro m hm n hn
  have hm' := Finset.mem_Ico.mp hm
  have hn' := Finset.mem_Ico.mp hn
  have hh : 2 * (q / 2 : ℕ) ≤ q := by omega
  have hh' : (2 : ℤ) * (q / 2 : ℕ) ≤ q := by exact_mod_cast hh
  have habs : |m - n| ≤ (q / 2 : ℕ) := by
    apply abs_le.mpr
    constructor <;> omega
  omega

/-- Interval form of the short-block estimate used in Type I/II decompositions. -/
theorem sum_truncatedInv_intDistance_short_interval_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (L : ℤ) (Y : ℝ) (hY : 0 ≤ Y) :
    (∑ n ∈ Finset.Ico L (L + (q / 2 : ℕ) + 1), truncatedInv Y (intDistance (α * n))) ≤
      2 * Y + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ))) :=
  sum_truncatedInv_intDistance_le α a q hq hcop happrox _ (short_interval_span q L) Y hY

theorem sum_int_Ico_add (f : ℤ → ℝ) (L M R : ℤ)
    (hLM : L ≤ M) (hMR : M ≤ R) :
    (∑ n ∈ Finset.Ico L M, f n) + (∑ n ∈ Finset.Ico M R, f n) =
      ∑ n ∈ Finset.Ico L R, f n := by
  have hdisj : Disjoint (Finset.Ico L M) (Finset.Ico M R) := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    have h := Finset.mem_Ico.mp hn
    have h' := Finset.mem_Ico.mp hn'
    omega
  have hunion : Finset.Ico L M ∪ Finset.Ico M R = Finset.Ico L R := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Ico]
    omega
  rw [← Finset.sum_union hdisj, hunion]

/-- Aggregate an estimate on consecutive blocks, with no periodicity premise. -/
theorem sum_int_Ico_le_blocks (f : ℤ → ℝ) (B : ℕ) (hB : 0 < B) (C : ℝ)
    (hblock : ∀ L : ℤ, (∑ n ∈ Finset.Ico L (L + B), f n) ≤ C)
    (L : ℤ) (k : ℕ) :
    (∑ n ∈ Finset.Ico L (L + (k : ℤ) * B), f n) ≤ (k : ℝ) * C := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hBz : (0 : ℤ) < B := by exact_mod_cast hB
    have hleft : L ≤ L + (k : ℤ) * B := le_add_of_nonneg_right (by positivity)
    have hright : L + (k : ℤ) * B ≤ L + (k : ℤ) * B + B := by omega
    have hend : L + ((k + 1 : ℕ) : ℤ) * B = L + (k : ℤ) * B + B := by
      push_cast
      ring
    rw [hend, ← sum_int_Ico_add f L (L + (k : ℤ) * B)
      (L + (k : ℤ) * B + B) hleft hright]
    calc
      _ ≤ (k : ℝ) * C + C := add_le_add ih (hblock (L + (k : ℤ) * B))
      _ = ((k + 1 : ℕ) : ℝ) * C := by push_cast; ring

/-- Full interval version, with the exact number of short blocks. -/
theorem sum_truncatedInv_intDistance_interval_le_blocks
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (L : ℤ) (N : ℕ) (Y : ℝ) (hY : 0 ≤ Y) :
    (∑ n ∈ Finset.Ico L (L + N), truncatedInv Y (intDistance (α * n))) ≤
      ((N / (q / 2 + 1) + 1 : ℕ) : ℝ) *
        (2 * Y + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ)))) := by
  let B : ℕ := q / 2 + 1
  have hB : 0 < B := by dsimp [B]; omega
  have hcover : N ≤ (N / B + 1) * B := by
    simpa only [Nat.mul_comm] using (Nat.lt_mul_div_succ N hB).le
  have hcoverZ : (N : ℤ) ≤ ((N / B + 1 : ℕ) : ℤ) * B := by exact_mod_cast hcover
  have hs := sum_int_Ico_le_blocks
    (fun n : ℤ => truncatedInv Y (intDistance (α * n))) B hB
    (2 * Y + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ))))
    (fun l => by
      simpa [B, Nat.cast_add, Nat.cast_one, add_assoc] using
        sum_truncatedInv_intDistance_short_interval_le α a q hq hcop happrox l Y hY)
    L (N / B + 1)
  apply le_trans ?_ hs
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Ico_subset_Ico le_rfl (by omega)
  · intro n _ _
    exact truncatedInv_nonneg hY (intDistance_nonneg _)

/-- Standard convenient full-interval form of the rational approximation
reciprocal-distance estimate. It applies equally to negative interval origins. -/
theorem sum_truncatedInv_intDistance_interval_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (L : ℤ) (N : ℕ) (Y : ℝ) (hY : 0 ≤ Y) :
    (∑ n ∈ Finset.Ico L (L + N), truncatedInv Y (intDistance (α * n))) ≤
      (2 * (N : ℝ) / q + 1) *
        (2 * Y + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ)))) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hh : q ≤ 2 * (q / 2 + 1) := by omega
  have hhR : (q : ℝ) ≤ 2 * ((q / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast hh
  have hdivR : ((N / (q / 2 + 1) : ℕ) : ℝ) * ((q / 2 + 1 : ℕ) : ℝ) ≤ N := by
    exact_mod_cast Nat.div_mul_le_self N (q / 2 + 1)
  have hcount : ((N / (q / 2 + 1) + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) / q + 1 := by
    push_cast
    apply add_le_add _ le_rfl
    apply (le_div_iff₀ hqR).mpr
    nlinarith [mul_le_mul_of_nonneg_left hhR (Nat.cast_nonneg (N / (q / 2 + 1)) :
      (0 : ℝ) ≤ (N / (q / 2 + 1) : ℕ))]
  have hlog : 0 ≤ Real.log (2 * (q : ℝ)) := by
    apply Real.log_nonneg
    have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  exact (sum_truncatedInv_intDistance_interval_le_blocks α a q hq hcop happrox L N Y hY).trans
    (mul_le_mul_of_nonneg_right hcount (by positivity))

end Problem337.RationalPhaseSpacing

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanNearRational

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.VaughanBilinear

theorem phase_int (n : ℤ) : phase n = 1 := by
  rw [phase, Real.fourierChar_apply]
  have he : (↑(2 * Real.pi * (n : ℝ)) : ℂ) * Complex.I =
      (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_int_mul_two_pi_mul_I]

theorem phase_fract (x : ℝ) : phase (Int.fract x) = phase x := by
  rw [Int.fract, ← phase_mul_conj, phase_int]
  simp

theorem phase_eq_geometric_phase (x : ℝ) :
    phase x = Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) := by
  rw [phase, Real.fourierChar_apply]
  congr 1
  ring

/-- The explicit geometric majorant itself is bounded by the truncated
reciprocal distance. This also allows variable inner interval lengths. -/
theorem geometricBound_le_truncatedInv (M : ℕ) (x : ℝ) :
    geometricBound M x ≤
      RationalPhaseSpacing.truncatedInv M (RationalPhaseSpacing.intDistance x) := by
  by_cases hd : RationalPhaseSpacing.intDistance x = 0
  · rw [RationalPhaseSpacing.truncatedInv, ite_eq_left hd]
    unfold geometricBound
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  have hdpos : 0 < RationalPhaseSpacing.intDistance x :=
    lt_of_le_of_ne (RationalPhaseSpacing.intDistance_nonneg x) (Ne.symm hd)
  have hlow : RationalPhaseSpacing.intDistance x ≤ Int.fract x := min_le_left _ _
  have hhigh : Int.fract x ≤ 1 - RationalPhaseSpacing.intDistance x := by
    have h := min_le_right (Int.fract x) (1 - Int.fract x)
    change RationalPhaseSpacing.intDistance x ≤ 1 - Int.fract x at h
    linarith
  have hs := sin_pi_mul_lower_on_middle hdpos hlow hhigh
  have hchord : 2 * RationalPhaseSpacing.intDistance x ≤ ‖1 - phase x‖ := by
    rw [norm_sub_rev, ← phase_fract x, phase_eq_geometric_phase, norm_exp_phase_sub_one]
    have habs := le_abs_self (Real.sin (Real.pi * Int.fract x))
    nlinarith
  have hnorm : 0 < ‖1 - phase x‖ := by linarith
  have hx : phase x ≠ 1 := by
    intro hx
    simp [hx] at hnorm
  rw [geometricBound, ite_eq_right hx, RationalPhaseSpacing.truncatedInv, ite_eq_right hd]
  apply min_le_min_left
  apply (div_le_div_iff₀ hnorm hdpos).mpr
  simpa using hchord

/-- A uniform harmonic row bound for indexed integer frequencies. The map
into the interval must be injective, but need not exhaust the interval. -/
theorem sum_geometricBound_difference_le {β : Type*}
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (M : ℕ) (t : Finset β) (f : β → ℤ) (L : ℤ) (N : ℕ)
    (hf : ∀ k ∈ t, f k ∈ Finset.Ico L (L + N))
    (hinj : Set.InjOn f t) (n : ℤ) :
    (∑ k ∈ t, geometricBound M (θ * ((n - f k : ℤ) : ℝ))) ≤
      (2 * (N : ℝ) / q + 1) *
        (2 * (M : ℝ) + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ)))) := by
  classical
  let A := t.image (fun k => n - f k)
  let L' : ℤ := n - L - N + 1
  have hA : A ⊆ Finset.Ico L' (L' + N) := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    have hk' := Finset.mem_Ico.mp (hf k hk)
    apply Finset.mem_Ico.mpr
    dsimp [L']
    omega
  calc
    _ ≤ ∑ k ∈ t, RationalPhaseSpacing.truncatedInv M
        (RationalPhaseSpacing.intDistance (θ * ((n - f k : ℤ) : ℝ))) :=
      Finset.sum_le_sum (fun k _ => geometricBound_le_truncatedInv M _)
    _ = ∑ j ∈ A, RationalPhaseSpacing.truncatedInv M
        (RationalPhaseSpacing.intDistance (θ * j)) := by
      rw [Finset.sum_image]
      intro k hk i hi heq
      apply hinj hk hi
      dsimp at heq
      omega
    _ ≤ ∑ j ∈ Finset.Ico L' (L' + N), RationalPhaseSpacing.truncatedInv M
        (RationalPhaseSpacing.intDistance (θ * j)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hA (fun _ _ _ =>
        RationalPhaseSpacing.truncatedInv_nonneg (Nat.cast_nonneg M)
          (RationalPhaseSpacing.intDistance_nonneg _))
    _ ≤ _ := RationalPhaseSpacing.sum_truncatedInv_intDistance_interval_le
      θ a q hq hcop happrox L' N M (Nat.cast_nonneg M)

end Problem337.VaughanBilinear

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanHyperbolicNearRational

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.VaughanBilinear

/-- A full Type-II estimate for the actual hyperbolic region `m*n ≤ X`.
The rational approximation is the only analytic input: support intersection,
geometric cancellation, harmonic spacing, and coefficient-energy estimates
are all supplied by checked lemmas. Empty row and column intervals are allowed. -/
theorem near_rational_hyperbolic_bilinear_sq_le
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (X L U V N : ℕ) (t : Finset ℕ)
    (ht : t ⊆ Finset.Ico V (V + N)) (hpos : ∀ n ∈ t, 0 < n)
    (c b : ℕ → ℂ) :
    ‖∑ m ∈ Finset.Icc L U, c m * ∑ n ∈ t,
      b n * HyperbolaCorrelation.column θ X n m‖ ^ 2 ≤
      (∑ m ∈ Finset.Icc L U, ‖c m‖ ^ 2) *
        ((2 * (N : ℝ) / q + 1) *
          (2 * ((U + 1 - L : ℕ) : ℝ) +
            4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ))))) *
              (∑ n ∈ t, ‖b n‖ ^ 2) := by
  apply norm_bilinear_sq_le_energy
  intro n hn
  calc
    _ ≤ ∑ k ∈ t, geometricBound (U + 1 - L) (θ * ((n : ℝ) - k)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact HyperbolaCorrelation.column_correlation_le θ X L U n k
        ((hpos n hn).trans_le (le_max_left _ _))
    _ ≤ _ := by
      simpa only [Int.cast_sub, Int.cast_natCast] using
        (sum_geometricBound_difference_le θ a q hq hcop happrox
          (U + 1 - L) t (fun k : ℕ => (k : ℤ)) (V : ℤ) N
          (by
            intro k hk
            obtain ⟨hl, hu⟩ := Finset.mem_Ico.mp (ht hk)
            apply Finset.mem_Ico.mpr
            constructor <;> exact_mod_cast (by assumption))
          (by
            intro i hi j hj hij
            dsimp at hij
            exact_mod_cast hij)
          (n : ℤ))

end Problem337.VaughanBilinear

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanDyadicEstimate

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction
open Finset

namespace Problem337.Vaughan

lemma typeIIBlock_eq_bilinear (θ : ℝ) (N U V j : ℕ) :
    typeIIBlock N U V j (fun k => VaughanBilinear.phase (θ * k)) =
      ∑ m ∈ Icc (max (U + 1) (2 ^ j)) (min N (2 ^ (j + 1) - 1)),
        (typeIICoefficient U m : ℂ) *
          ∑ n ∈ Ioc V (N / 2 ^ j), (Λ n : ℂ) *
            HyperbolaCorrelation.column θ N n m := by
  unfold typeIIBlock VaughanDyadic.block
  rw [VaughanDyadic.shell_eq_Icc]
  apply sum_congr rfl
  intro m hm
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  unfold HyperbolaCorrelation.column
  by_cases h : m * n ≤ N
  · simp only [ite_eq_left h, HyperbolaCorrelation.phase_eq_vaughan]
    rw [mul_assoc]
    congr 2
    congr 1
    push_cast
    ring
  · simp [h]

lemma dyadic_row_length_le (N U j : ℕ) :
    min N (2 ^ (j + 1) - 1) + 1 - max (U + 1) (2 ^ j) ≤ 2 ^ j := by
  have htop : min N (2 ^ (j + 1) - 1) ≤ 2 ^ (j + 1) - 1 := min_le_right _ _
  have hlow : 2 ^ j ≤ max (U + 1) (2 ^ j) := le_max_right _ _
  have hp : 0 < 2 ^ j := by positivity
  rw [pow_succ] at htop
  omega

/-- The elementary bounded-weight column energy, used only as a normalization
inside the actual Type II block estimate. -/
lemma mangoldt_column_energy_le (V T : ℕ) :
    (∑ n ∈ Ioc V T, ‖(Λ n : ℂ)‖ ^ 2) ≤ (T : ℝ) * (Real.log T) ^ 2 := by
  calc
    _ ≤ ∑ n ∈ Ioc V T, (Real.log T) ^ 2 := by
      apply sum_le_sum
      intro n hn
      have h := mem_Ioc.mp hn
      have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le V) h.1
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast h.2))
    _ = ((T - V : ℕ) : ℝ) * (Real.log T) ^ 2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le T V) (sq_nonneg _)

/-- A genuine rational-approximation estimate for one actual Vaughan block.
All coefficient energies and correlations have been evaluated explicitly. -/
theorem typeIIBlock_sq_le_raw
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N U V j : ℕ) :
    ‖typeIIBlock N U V j (fun k => VaughanBilinear.phase (θ * k))‖ ^ 2 ≤
      ((2 ^ (j + 1) : ℕ) * (1 + Real.log (2 ^ (j + 1) : ℕ)) ^ 3) *
        ((2 * ((N / 2 ^ j : ℕ) : ℝ) / q + 1) *
          (2 * ((2 ^ j : ℕ) : ℝ) + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ))))) *
            (((N / 2 ^ j : ℕ) : ℝ) * (Real.log (N / 2 ^ j : ℕ)) ^ 2) := by
  have hlog : 0 ≤ 1 + Real.log (2 * (q : ℝ)) := by
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 * q by linarith)
    linarith
  have h := VaughanBilinear.near_rational_hyperbolic_bilinear_sq_le θ a q hq hcop happrox
    N (max (U + 1) (2 ^ j)) (min N (2 ^ (j + 1) - 1)) (V + 1) (N / 2 ^ j)
    (Ioc V (N / 2 ^ j)) (by
      intro n hn
      have hn' := mem_Ioc.mp hn
      exact mem_Ico.mpr ⟨by omega, by omega⟩)
    (fun n hn => lt_of_le_of_lt (Nat.zero_le V) (mem_Ioc.mp hn).1)
    (fun m => (typeIICoefficient U m : ℂ)) (fun n => (Λ n : ℂ))
  rw [← typeIIBlock_eq_bilinear, ← VaughanDyadic.shell_eq_Icc] at h
  refine h.trans ?_
  have hA := typeII_shell_energy_le N U j
  have hB := mangoldt_column_energy_le V (N / 2 ^ j)
  have hlength : ((min N (2 ^ (j + 1) - 1) + 1 - max (U + 1) (2 ^ j) : ℕ) : ℝ) ≤
      ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast dyadic_row_length_le N U j
  gcongr

end Problem337.Vaughan

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.TypeIIBlockScalar

namespace OAI
namespace Problem337.TypeIIBlockScalar

/-- The scalar aggregation for one dyadic Vaughan Type-II block. All analytic
information is explicit in the three elementary size bounds. -/
theorem block_bound (X M T Q U V H : ℝ)
    (hX : 0 ≤ X) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hQ : 0 < Q) (hU : 0 < U) (hV : 0 < V) (hH : 1 ≤ H)
    (hMT : M * T ≤ X) (hTU : T ≤ 2 * X / U) (hMV : M ≤ X / V) :
    (2 * M * H ^ 3) * ((2 * T / Q + 1) * (2 * M + 4 * Q * H)) *
        (T * H ^ 2) ≤
      32 * X * H ^ 6 * (X / Q + X / U + X / V + Q) := by
  have hH0 : 0 ≤ H := by linarith
  have hXQ : 0 ≤ X / Q := div_nonneg hX hQ.le
  have hXU : 0 ≤ X / U := div_nonneg hX hU.le
  have hXV : 0 ≤ X / V := div_nonneg hX hV.le
  have hMTQ : M * T / Q ≤ X / Q := div_le_div_of_nonneg_right hMT hQ.le
  have hTH : T * H ≤ (2 * X / U) * H := mul_le_mul_of_nonneg_right hTU hH0
  have hQH : X / Q ≤ H * (X / Q) := by nlinarith [mul_le_mul_of_nonneg_right hH hXQ]
  have hVH : X / V ≤ H * (X / V) := by nlinarith [mul_le_mul_of_nonneg_right hH hXV]
  have hinner : (2 * T / Q + 1) * (2 * M + 4 * Q * H) ≤
      16 * H * (X / Q + X / U + X / V + Q) := by
    have heq : (2 * T / Q + 1) * (2 * M + 4 * Q * H) =
        4 * (M * T / Q) + 8 * T * H + 2 * M + 4 * Q * H := by
      field_simp
      ring
    rw [heq]
    have hTH' : T * H ≤ 2 * (X / U) * H := by convert hTH using 1; ring
    nlinarith [mul_nonneg hH0 hXQ, mul_nonneg hH0 hXV, mul_nonneg hH0 hQ.le]
  have hfactor : 2 * (M * T) * H ^ 5 ≤ 2 * X * H ^ 5 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMT (by norm_num)) (by positivity)
  have hinner0 : 0 ≤ (2 * T / Q + 1) * (2 * M + 4 * Q * H) := by positivity
  calc
    _ = (2 * (M * T) * H ^ 5) * ((2 * T / Q + 1) * (2 * M + 4 * Q * H)) := by ring
    _ ≤ (2 * X * H ^ 5) * (16 * H * (X / Q + X / U + X / V + Q)) :=
      mul_le_mul hfactor hinner hinner0 (by positivity)
    _ = _ := by ring

end Problem337.TypeIIBlockScalar

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.HyperbolaDyadicBridge

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.VaughanDyadic

/-- Empty high shells contribute nothing to the long--long hyperbola. -/
theorem block_eq_zero_of_large_base {E : Type*} [AddCommMonoid E]
    (N U V j : ℕ) (F : ℕ → ℕ → E) (hN : N < 2 ^ j * (V + 1)) :
    block N U V j F = 0 := by
  unfold block
  apply Finset.sum_eq_zero
  intro m hm
  apply Finset.sum_eq_zero
  intro n hn
  have hm2 := (mem_shell.mp hm).2.2.1
  have hnV : V + 1 ≤ n := (Finset.mem_Ioc.mp hn).1
  have hmn : N < m * n := hN.trans_le (Nat.mul_le_mul hm2 hnV)
  simp [not_le.mpr hmn]

/-- Every nonzero block has row scale at most the hyperbolic long-column cap. -/
theorem base_le_div_of_block_ne_zero {E : Type*} [AddCommMonoid E]
    (N U V j : ℕ) (F : ℕ → ℕ → E) (hblock : block N U V j F ≠ 0) :
    2 ^ j ≤ N / (V + 1) := by
  apply (Nat.le_div_iff_mul_le (Nat.succ_pos V)).mpr
  by_contra h
  exact hblock (block_eq_zero_of_large_base N U V j F (Nat.lt_of_not_ge h))

end Problem337.VaughanDyadic

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanDyadicUniform

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction
open Finset

namespace Problem337.Vaughan

def typeIILogScale (N : ℕ) : ℝ := 1 + Real.log (2 * (N : ℝ))

lemma one_le_typeIILogScale (N : ℕ) : 1 ≤ typeIILogScale N := by
  have h := Real.log_natCast_nonneg (2 * N)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h
  unfold typeIILogScale
  linarith

lemma log_nat_le_typeIILogScale (N T : ℕ) (hT : T ≤ N) :
    Real.log T ≤ typeIILogScale N := by
  by_cases h0 : T = 0
  · simp only [h0, Nat.cast_zero, Real.log_zero]
    exact zero_le_one.trans (one_le_typeIILogScale N)
  have ht : (0 : ℝ) < T := by exact_mod_cast Nat.pos_of_ne_zero h0
  have htn : (T : ℝ) ≤ 2 * (N : ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr hT
    nlinarith [Nat.cast_nonneg N (α := ℝ)]
  have hlog := Real.log_le_log ht htn
  unfold typeIILogScale
  linarith

/-- Uniform logarithmic normalization of the coefficient block estimate. -/
theorem typeIIBlock_sq_le_normalized
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N U V j : ℕ) (hqN : q ≤ N) (hM : 2 ^ j ≤ N) :
    ‖typeIIBlock N U V j (fun k => VaughanBilinear.phase (θ * k))‖ ^ 2 ≤
      (2 * ((2 ^ j : ℕ) : ℝ) * (typeIILogScale N) ^ 3) *
        ((2 * ((N / 2 ^ j : ℕ) : ℝ) / q + 1) *
          (2 * ((2 ^ j : ℕ) : ℝ) + 4 * (q : ℝ) * typeIILogScale N)) *
            (((N / 2 ^ j : ℕ) : ℝ) * (typeIILogScale N) ^ 2) := by
  have hH0 : 0 ≤ typeIILogScale N := zero_le_one.trans (one_le_typeIILogScale N)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hMR : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  have hqlog : 1 + Real.log (2 * (q : ℝ)) ≤ typeIILogScale N := by
    unfold typeIILogScale
    apply add_le_add le_rfl
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.mul_le_mul_left 2 hqN)
  have hMlog : 1 + Real.log (2 ^ (j + 1) : ℕ) ≤ typeIILogScale N := by
    unfold typeIILogScale
    apply add_le_add le_rfl
    apply Real.log_le_log (by positivity)
    rw [pow_succ, Nat.cast_mul, Nat.cast_ofNat]
    have hMRN : ((2 ^ j : ℕ) : ℝ) ≤ N := by exact_mod_cast hM
    nlinarith
  have hTlog := log_nat_le_typeIILogScale N (N / 2 ^ j) (Nat.div_le_self _ _)
  have hraw := typeIIBlock_sq_le_raw θ a q hq hcop happrox N U V j
  refine hraw.trans ?_
  have hqlog0 : 0 ≤ 1 + Real.log (2 * (q : ℝ)) := by
    have h := Real.log_natCast_nonneg (2 * q)
    simp only [Nat.cast_mul, Nat.cast_ofNat] at h
    linarith
  have hMlog0 : 0 ≤ 1 + Real.log (2 ^ (j + 1) : ℕ) := by
    linarith [Real.log_natCast_nonneg (2 ^ (j + 1))]
  have hTlog0 := Real.log_natCast_nonneg (N / 2 ^ j)
  have he : ((2 ^ (j + 1) : ℕ) : ℝ) = 2 * ((2 ^ j : ℕ) : ℝ) := by
    rw [pow_succ, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [he] at hMlog hMlog0 ⊢
  gcongr

/-- Uniform actual Type II block bound, with no cancellation or energy premise. -/
theorem typeIIBlock_sq_le_uniform
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N U V j : ℕ) (hqN : q ≤ N) (hU : 0 < U) (hV : 0 < V) :
    ‖typeIIBlock N U V j (fun k => VaughanBilinear.phase (θ * k))‖ ^ 2 ≤
      32 * (N : ℝ) * (typeIILogScale N) ^ 6 *
        ((N : ℝ) / q + (N : ℝ) / U + (N : ℝ) / V + q) := by
  have hH : 0 ≤ typeIILogScale N := zero_le_one.trans (one_le_typeIILogScale N)
  by_cases hb : typeIIBlock N U V j (fun k => VaughanBilinear.phase (θ * k)) = 0
  · rw [hb, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    positivity
  have hs : (VaughanDyadic.shell U N j).Nonempty := by
    by_contra he
    have he' : VaughanDyadic.shell U N j = ∅ := not_nonempty_iff_eq_empty.mp he
    apply hb
    simp [typeIIBlock, VaughanDyadic.block, he']
  obtain ⟨m, hm⟩ := hs
  have hm' := VaughanDyadic.mem_shell.mp hm
  have hM : 2 ^ j ≤ N := hm'.2.2.1.trans hm'.2.1
  have hbase := VaughanDyadic.base_le_div_of_block_ne_zero N U V j
    (fun m n => (typeIICoefficient U m : ℂ) * (Λ n : ℂ) *
      VaughanBilinear.phase (θ * (m * n : ℕ))) hb
  have hMT : (((2 ^ j : ℕ) : ℝ) * ((N / 2 ^ j : ℕ) : ℝ)) ≤ N := by
    exact_mod_cast Nat.mul_div_le N (2 ^ j)
  have hU2M : (U : ℝ) ≤ 2 * ((2 ^ j : ℕ) : ℝ) := by
    have hnat : U ≤ 2 * 2 ^ j := by
      have hu := hm'.1
      have hmhi := hm'.2.2.2
      rw [pow_succ] at hmhi
      omega
    exact_mod_cast hnat
  have hTU : ((N / 2 ^ j : ℕ) : ℝ) ≤ 2 * (N : ℝ) / U := by
    apply (le_div_iff₀ (by exact_mod_cast hU : (0 : ℝ) < U)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hU2M
      (Nat.cast_nonneg (N / 2 ^ j) : (0 : ℝ) ≤ (N / 2 ^ j : ℕ))]
  have hMV : ((2 ^ j : ℕ) : ℝ) ≤ (N : ℝ) / V := by
    apply (le_div_iff₀ (by exact_mod_cast hV : (0 : ℝ) < V)).mpr
    have hn : 2 ^ j * V ≤ N :=
      (Nat.mul_le_mul_left (2 ^ j) (Nat.le_succ V)).trans
        ((Nat.le_div_iff_mul_le (Nat.succ_pos V)).mp hbase)
    exact_mod_cast hn
  exact (typeIIBlock_sq_le_normalized θ a q hq hcop happrox N U V j hqN hM).trans
    (TypeIIBlockScalar.block_bound N (2 ^ j : ℕ) (N / 2 ^ j : ℕ) q U V (typeIILogScale N)
      (Nat.cast_nonneg N) (by positivity) (Nat.cast_nonneg _)
      (by exact_mod_cast hq) (by exact_mod_cast hU) (by exact_mod_cast hV)
      (one_le_typeIILogScale N) hMT hTU hMV)

end Problem337.Vaughan

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanCutoff

namespace OAI
noncomputable section
open Filter

namespace Problem337.Vaughan

/-- The conventional balanced natural cutoff for Vaughan's identity. -/
def optimizedCutoff (X : ℝ) : ℕ := ⌊X ^ (2 / 5 : ℝ)⌋₊

theorem optimizedCutoff_le (X : ℝ) (hX : 0 ≤ X) :
    (optimizedCutoff X : ℝ) ≤ X ^ (2 / 5 : ℝ) :=
  Nat.floor_le (Real.rpow_nonneg hX _)

theorem optimizedCutoff_lower (X : ℝ) (hX : 2 ≤ X ^ (2 / 5 : ℝ)) :
    X ^ (2 / 5 : ℝ) / 2 ≤ (optimizedCutoff X : ℝ) := by
  have hfloor := Nat.lt_floor_add_one (X ^ (2 / 5 : ℝ))
  unfold optimizedCutoff
  linarith

theorem optimizedCutoff_pos (X : ℝ) (hX : 2 ≤ X ^ (2 / 5 : ℝ)) :
    0 < optimizedCutoff X := by
  have h : 2 ≤ optimizedCutoff X := Nat.le_floor hX
  omega

theorem optimizedCutoff_sq_le (X : ℝ) (hX : 0 ≤ X) :
    (optimizedCutoff X : ℝ) ^ 2 ≤ X ^ (4 / 5 : ℝ) := by
  have hpow : (X ^ (2 / 5 : ℝ)) ^ 2 = X ^ (4 / 5 : ℝ) := by
    have h := Real.rpow_mul hX (2 / 5 : ℝ) (2 : ℝ)
    norm_num at h
    exact h.symm
  rw [← hpow]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (optimizedCutoff_le X hX) 2

theorem optimizedCutoff_le_four_fifths (X : ℝ) (hX : 1 ≤ X) :
    (optimizedCutoff X : ℝ) ≤ X ^ (4 / 5 : ℝ) :=
  (optimizedCutoff_le X (by linarith)).trans
    (Real.rpow_le_rpow_of_exponent_le hX (by norm_num))

/-- The reciprocal square-root loss from a long-variable cutoff has precisely
the required four-fifths power, with a harmless explicit constant. -/
theorem div_sqrt_optimizedCutoff_le (X : ℝ) (hX : 0 < X)
    (hpow : 2 ≤ X ^ (2 / 5 : ℝ)) :
    X / Real.sqrt (optimizedCutoff X : ℝ) ≤ 2 * X ^ (4 / 5 : ℝ) := by
  have hsq : (X ^ (1 / 5 : ℝ)) ^ 2 = X ^ (2 / 5 : ℝ) := by
    have h := Real.rpow_mul hX.le (1 / 5 : ℝ) (2 : ℝ)
    norm_num at h
    exact h.symm
  have hcut := optimizedCutoff_lower X hpow
  have hs : X ^ (1 / 5 : ℝ) / 2 ≤ Real.sqrt (optimizedCutoff X : ℝ) := by
    apply (Real.le_sqrt (by positivity) (Nat.cast_nonneg _)).mpr
    nlinarith [sq_nonneg (X ^ (1 / 5 : ℝ))]
  have hpos : 0 < Real.sqrt (optimizedCutoff X : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast optimizedCutoff_pos X hpow)
  apply (div_le_iff₀ hpos).mpr
  have hprod : X ^ (4 / 5 : ℝ) * X ^ (1 / 5 : ℝ) = X := by
    rw [← Real.rpow_add hX]
    norm_num
  calc
    X = X ^ (4 / 5 : ℝ) * X ^ (1 / 5 : ℝ) := hprod.symm
    _ = (2 * X ^ (4 / 5 : ℝ)) * (X ^ (1 / 5 : ℝ) / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)

/-- A concrete scalar optimization of the cutoff-dependent error terms. -/
theorem optimizedCutoff_error_le (X : ℝ) (hX : 1 ≤ X)
    (hpow : 2 ≤ X ^ (2 / 5 : ℝ)) :
    (optimizedCutoff X : ℝ) + (optimizedCutoff X : ℝ) ^ 2 +
        X / Real.sqrt (optimizedCutoff X : ℝ) ≤ 4 * X ^ (4 / 5 : ℝ) := by
  have h1 := optimizedCutoff_le_four_fifths X hX
  have h2 := optimizedCutoff_sq_le X (by linarith)
  have h3 := div_sqrt_optimizedCutoff_le X (by linarith) hpow
  linarith

/-- The short initial segment is also absorbed by the four-fifths budget. -/
theorem optimizedCutoff_log_le (X : ℝ) (hX : 1 ≤ X)
    (hpow : 2 ≤ X ^ (2 / 5 : ℝ)) :
    (optimizedCutoff X : ℝ) * Real.log (optimizedCutoff X : ℝ) ≤
      X ^ (4 / 5 : ℝ) * Real.log X := by
  have hUX : (optimizedCutoff X : ℝ) ≤ X := by
    calc
      _ ≤ X ^ (2 / 5 : ℝ) := optimizedCutoff_le X (by linarith)
      _ ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
      _ = X := Real.rpow_one X
  have hlog : Real.log (optimizedCutoff X : ℝ) ≤ Real.log X :=
    Real.log_le_log (by exact_mod_cast optimizedCutoff_pos X hpow) hUX
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  exact (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)).trans
    (mul_le_mul_of_nonneg_right (optimizedCutoff_le_four_fifths X hX) hlogX)

/-- Scalar normalization to the usual three-term Vaughan envelope. The
Diophantine denominator only needs the ordinary range `1 ≤ q ≤ X`. -/
theorem optimizedCutoff_standard_envelope (X q : ℝ) (hX : 1 ≤ X)
    (hq : 1 ≤ q) (hqX : q ≤ X) (hpow : 2 ≤ X ^ (2 / 5 : ℝ)) :
    X / q + ((optimizedCutoff X : ℝ) + (optimizedCutoff X : ℝ) ^ 2 +
        X / Real.sqrt (optimizedCutoff X : ℝ)) + q ≤
      4 * (X / Real.sqrt q + X ^ (4 / 5 : ℝ) + Real.sqrt (X * q)) := by
  have hX0 : 0 ≤ X := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hsqpos : 0 < Real.sqrt q := Real.sqrt_pos.mpr (by linarith)
  have hsqq : Real.sqrt q ≤ q := Real.sqrt_le_self_iff.mpr (Or.inr hq)
  have hdiv : X / q ≤ X / Real.sqrt q :=
    div_le_div_of_nonneg_left hX0 hsqpos hsqq
  have hqsqrt : q ≤ Real.sqrt (X * q) := by
    apply (Real.le_sqrt hq0 (mul_nonneg hX0 hq0)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hqX hq0]
  have herr := optimizedCutoff_error_le X hX hpow
  have hnonneg : 0 ≤ X / Real.sqrt q := div_nonneg hX0 hsqpos.le
  nlinarith [Real.sqrt_nonneg (X * q)]

/-- Optimization of the square-root expression arising from a Type II block.
Both long-variable cutoffs are the same balanced natural cutoff. -/
theorem sqrt_optimizedCutoff_envelope_le (X q : ℝ) (hX : 1 ≤ X)
    (hq : 0 < q) (hpow : 2 ≤ X ^ (2 / 5 : ℝ)) :
    Real.sqrt (X * (X / q + X / (optimizedCutoff X : ℝ) +
        X / (optimizedCutoff X : ℝ) + q)) ≤
      3 * (X / Real.sqrt q + X ^ (4 / 5 : ℝ) + Real.sqrt (X * q)) := by
  have hX0 : 0 ≤ X := by linarith
  have hU0 : 0 < (optimizedCutoff X : ℝ) := by
    exact_mod_cast optimizedCutoff_pos X hpow
  have hA : 0 ≤ X / Real.sqrt q := by positivity
  have hB : 0 ≤ X ^ (4 / 5 : ℝ) := by positivity
  have hC : 0 ≤ Real.sqrt (X * q) := Real.sqrt_nonneg _
  have hqeq : X * (X / q) = (X / Real.sqrt q) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hq.le]
    ring
  have hUeq : X * (X / (optimizedCutoff X : ℝ)) =
      (X / Real.sqrt (optimizedCutoff X : ℝ)) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hU0.le]
    ring
  have hUbound := pow_le_pow_left₀ (show 0 ≤ X / Real.sqrt (optimizedCutoff X : ℝ) by
    positivity) (div_sqrt_optimizedCutoff_le X (by linarith) hpow) 2
  have hCeq := Real.sq_sqrt (mul_nonneg hX0 hq.le)
  apply (Real.sqrt_le_left (by positivity)).mpr
  rw [mul_add, mul_add, mul_add, hqeq, hUeq]
  nlinarith [mul_nonneg hA hB, mul_nonneg hA hC, mul_nonneg hB hC,
    sq_nonneg (X / Real.sqrt q), sq_nonneg (X ^ (4 / 5 : ℝ)),
    sq_nonneg (Real.sqrt (X * q))]

/-- The precise squared Type II block budget transfers to the standard
Vaughan envelope after choosing both cutoffs as `optimizedCutoff X`. -/
theorem optimizedCutoff_squared_budget (X q C R : ℝ) (hX : 1 ≤ X)
    (hq : 0 < q) (hC : 0 ≤ C) (hpow : 2 ≤ X ^ (2 / 5 : ℝ))
    (hbound : R ^ 2 ≤ C * X * (1 + Real.log (2 * X)) ^ 6 *
      (X / q + X / (optimizedCutoff X : ℝ) + X / (optimizedCutoff X : ℝ) + q)) :
    R ≤ 3 * Real.sqrt C * (1 + Real.log (2 * X)) ^ 3 *
      (X / Real.sqrt q + X ^ (4 / 5 : ℝ) + Real.sqrt (X * q)) := by
  let L : ℝ := 1 + Real.log (2 * X)
  let E : ℝ := X / Real.sqrt q + X ^ (4 / 5 : ℝ) + Real.sqrt (X * q)
  have hX0 : 0 ≤ X := by linarith
  have hL : 0 ≤ L := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * X by linarith)
    dsimp [L]
    linarith
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hD : X * (X / q + X / (optimizedCutoff X : ℝ) +
      X / (optimizedCutoff X : ℝ) + q) ≤ (3 * E) ^ 2 :=
    (Real.sqrt_le_left (by positivity)).mp (sqrt_optimizedCutoff_envelope_le X q hX hq hpow)
  change R ≤ 3 * Real.sqrt C * L ^ 3 * E
  apply le_of_sq_le_sq _ (by positivity)
  calc
    R ^ 2 ≤ C * X * L ^ 6 *
        (X / q + X / (optimizedCutoff X : ℝ) + X / (optimizedCutoff X : ℝ) + q) := hbound
    _ = (C * L ^ 6) * (X *
        (X / q + X / (optimizedCutoff X : ℝ) + X / (optimizedCutoff X : ℝ) + q)) := by ring
    _ ≤ (C * L ^ 6) * (3 * E) ^ 2 := mul_le_mul_of_nonneg_left hD (by positivity)
    _ = (3 * Real.sqrt C * L ^ 3 * E) ^ 2 := by
      have hs := Real.sq_sqrt hC
      calc
        _ = (3 * E) ^ 2 * L ^ 6 * (Real.sqrt C) ^ 2 := by rw [hs]; ring
        _ = _ := by ring

end Problem337.Vaughan

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanOptimized

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction

namespace Problem337.Vaughan

/-- The standard three-term envelope for a reduced rational approximation. -/
def approximationEnvelope (X q : ℝ) : ℝ :=
  X / Real.sqrt q + X ^ (4 / 5 : ℝ) + Real.sqrt (X * q)

lemma approximationEnvelope_nonneg (X q : ℝ) (hX : 0 ≤ X) :
    0 ≤ approximationEnvelope X q := by
  unfold approximationEnvelope
  positivity

lemma dyadic_log_le_three_scale (N : ℕ) :
    1 + Real.log N / Real.log 2 ≤ 3 * typeIILogScale N := by
  have hlog := Real.log_natCast_nonneg N
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hdiv : Real.log N / Real.log 2 ≤ 2 * Real.log N := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr
    nlinarith [mul_le_mul_of_nonneg_right htwo hlog]
  have hN := log_nat_le_typeIILogScale N N le_rfl
  have hH := one_le_typeIILogScale N
  linarith

/-- Balanced cutoffs turn each actual Type II block into the standard envelope. -/
theorem optimized_typeIIBlock_bound
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N j : ℕ) (hqN : q ≤ N)
    (hpow : 2 ≤ (N : ℝ) ^ (2 / 5 : ℝ)) :
    ‖typeIIBlock N (optimizedCutoff N) (optimizedCutoff N) j
      (fun k => VaughanBilinear.phase (θ * k))‖ ≤
      18 * (typeIILogScale N) ^ 3 * approximationEnvelope N q := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hq.trans_le hqN
  have hU := optimizedCutoff_pos N hpow
  have hs := typeIIBlock_sq_le_uniform θ a q hq hcop happrox N
    (optimizedCutoff N) (optimizedCutoff N) j hqN hU hU
  have hb := optimizedCutoff_squared_budget N q 32
    ‖typeIIBlock N (optimizedCutoff N) (optimizedCutoff N) j
      (fun k => VaughanBilinear.phase (θ * k))‖
    hN (by exact_mod_cast hq) (by norm_num) hpow hs
  have hsqrt : Real.sqrt (32 : ℝ) ≤ 6 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  change _ ≤ 3 * Real.sqrt 32 * (typeIILogScale N) ^ 3 * approximationEnvelope N q at hb
  refine hb.trans ?_
  have hH : 0 ≤ typeIILogScale N := zero_le_one.trans (one_le_typeIILogScale N)
  have hE := approximationEnvelope_nonneg N q (Nat.cast_nonneg N)
  gcongr
  norm_num at *
  linarith

/-- Summing the genuine dyadic blocks costs one further logarithm, not a
power of the summation length. All cancellation hypotheses are discharged. -/
theorem optimized_typeII_bound
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N : ℕ) (hqN : q ≤ N)
    (hpow : 2 ≤ (N : ℝ) ^ (2 / 5 : ℝ)) :
    ‖weightedSum (Finset.Ioc 0 N) (fun k => VaughanBilinear.phase (θ * k))
      (typeIICoefficient (optimizedCutoff N) * longPart (optimizedCutoff N) Λ)‖ ≤
      54 * (typeIILogScale N) ^ 4 * approximationEnvelope N q := by
  have hH : 0 ≤ typeIILogScale N := zero_le_one.trans (one_le_typeIILogScale N)
  have hE := approximationEnvelope_nonneg N q (Nat.cast_nonneg N)
  have hb := norm_typeII_le_dyadic_log_budget N (optimizedCutoff N) (optimizedCutoff N)
    (fun k => VaughanBilinear.phase (θ * k))
    (18 * (typeIILogScale N) ^ 3 * approximationEnvelope N q) (by positivity)
    (fun j _ => optimized_typeIIBlock_bound θ a q hq hcop happrox N j hqN hpow)
  refine hb.trans ?_
  calc
    _ ≤ (3 * typeIILogScale N) *
        (18 * (typeIILogScale N) ^ 3 * approximationEnvelope N q) :=
      mul_le_mul_of_nonneg_right (dyadic_log_le_three_scale N) (by positivity)
    _ = _ := by ring

end Problem337.Vaughan

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.RationalPhaseHyperbola

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RationalPhaseSpacing

/-- Monotonicity in the cap, valid also at integer phases. -/
theorem truncatedInv_mono_cap {Y Z : ℝ} (hYZ : Y ≤ Z) (x : ℝ) :
    truncatedInv Y x ≤ truncatedInv Z x := by
  unfold truncatedInv
  split_ifs
  · exact hYZ
  · exact min_le_min hYZ le_rfl

/-- Positive indices in the first half-block cannot approach an integer more
closely than `1/(2q)`. This removes the artificial singular term in Type I. -/
theorem intDistance_lower_bound
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (n : ℤ) (hn : n ≠ 0) (hsmall : 2 * |n| ≤ (q : ℤ)) :
    1 / (2 * (q : ℝ)) ≤ intDistance (α * n) := by
  simpa only [intDistance_eq_abs_sub_round] using
    separation_of_rational_approximation α a q hq hcop happrox n hn hsmall (round (α * n))

/-- First-block harmonic estimate with arbitrary, even varying, caps. The
bound is independent of those caps because zero frequency is excluded. -/
theorem sum_truncatedInv_first_block_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (cap : ℤ → ℝ) :
    (∑ n ∈ Finset.Ico 1 ((q / 2 + 1 : ℕ) : ℤ),
      truncatedInv (cap n) (intDistance (α * n))) ≤
      8 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ))) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hhalf : (2 : ℤ) * (q / 2 : ℕ) ≤ q := by exact_mod_cast (show 2 * (q / 2) ≤ q by omega)
  have hspan : ∀ m ∈ Finset.Ico 1 ((q / 2 + 1 : ℕ) : ℤ),
      ∀ n ∈ Finset.Ico 1 ((q / 2 + 1 : ℕ) : ℤ), 2 * |m - n| ≤ (q : ℤ) := by
    intro m hm n hn
    apply short_interval_span q 0 m _ n _
    · have hh := Finset.mem_Ico.mp hm
      apply Finset.mem_Ico.mpr
      push_cast at hh ⊢
      omega
    · have hh := Finset.mem_Ico.mp hn
      apply Finset.mem_Ico.mpr
      push_cast at hh ⊢
      omega
  have hpoint : ∀ n ∈ Finset.Ico 1 ((q / 2 + 1 : ℕ) : ℤ),
      truncatedInv (cap n) (intDistance (α * n)) ≤
        truncatedInv (2 * (q : ℝ)) (intDistance (α * n)) := by
    intro n hn
    have hn' := Finset.mem_Ico.mp hn
    have hnp : 0 < n := by omega
    have hsmall : 2 * |n| ≤ (q : ℤ) := by
      rw [abs_of_pos hnp]
      push_cast at hn'
      omega
    have hd := intDistance_lower_bound α a q hq hcop happrox n (by omega) hsmall
    have hdp : 0 < intDistance (α * n) := (by positivity : (0 : ℝ) < 1 / (2 * q)).trans_le hd
    have hinv : 1 / intDistance (α * n) ≤ 2 * (q : ℝ) := by
      apply (div_le_iff₀ hdp).mpr
      have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * q)).mp hd
      nlinarith
    simp only [truncatedInv, ite_eq_right (ne_of_gt hdp), min_eq_right hinv]
    exact min_le_right _ _
  have hs := sum_truncatedInv_intDistance_le α a q hq hcop happrox
    (Finset.Ico 1 ((q / 2 + 1 : ℕ) : ℤ)) hspan (2 * (q : ℝ)) (by positivity)
  have hlog : 0 ≤ Real.log (2 * (q : ℝ)) := by
    apply Real.log_nonneg
    have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  exact (Finset.sum_le_sum hpoint).trans (hs.trans (by nlinarith))

/-- On later blocks the hyperbolic cap `X/n` is bounded by the cap at the
left endpoint. This is the actual ingredient that removes an `O(X)` error. -/
theorem sum_truncatedInv_hyperbolic_block_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (L : ℤ) (hL : 0 < L) (X : ℝ) (hX : 0 ≤ X) :
    (∑ n ∈ Finset.Ico L (L + (q / 2 + 1 : ℕ)),
      truncatedInv (X / (n : ℝ)) (intDistance (α * n))) ≤
      2 * X / (L : ℝ) + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ))) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hs := sum_truncatedInv_intDistance_short_interval_le α a q hq hcop happrox
    L (X / (L : ℝ)) (by positivity)
  have hpoint : ∀ n ∈ Finset.Ico L (L + (q / 2 + 1 : ℕ)),
      truncatedInv (X / (n : ℝ)) (intDistance (α * n)) ≤
        truncatedInv (X / (L : ℝ)) (intDistance (α * n)) := by
    intro n hn
    apply truncatedInv_mono_cap
    apply div_le_div_of_nonneg_left hX hLr
    exact_mod_cast (Finset.mem_Ico.mp hn).1
  apply (Finset.sum_le_sum hpoint).trans
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc, mul_div_assoc] using hs

/-- Prefix aggregation with hyperbolic caps. The first block has no singular
term; the remaining singular terms sum harmonically rather than linearly. -/
theorem sum_truncatedInv_hyperbolic_prefix_blocks_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (X : ℝ) (hX : 0 ≤ X) (k : ℕ) :
    (∑ n ∈ Finset.Ico 1 ((k : ℤ) * (q / 2 + 1 : ℕ) + (q / 2 + 1 : ℕ)),
      truncatedInv (X / (n : ℝ)) (intDistance (α * n))) ≤
      ((k : ℝ) + 2) * (4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ)))) +
        (2 * X / ((q / 2 + 1 : ℕ) : ℝ)) * (harmonic k : ℝ) := by
  let B : ℕ := q / 2 + 1
  let C : ℝ := 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ)))
  change (∑ n ∈ Finset.Ico 1 ((k : ℤ) * B + B),
      truncatedInv (X / (n : ℝ)) (intDistance (α * n))) ≤
      ((k : ℝ) + 2) * C + (2 * X / (B : ℝ)) * (harmonic k : ℝ)
  have hB : 0 < B := by dsimp [B]; omega
  have hBz : (0 : ℤ) < B := by exact_mod_cast hB
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  induction k with
  | zero =>
    have hs := sum_truncatedInv_first_block_le α a q hq hcop happrox (fun n => X / (n : ℝ))
    convert hs using 1 <;> simp [B, C]
    ring
  | succ k ih =>
    have hmiddle : 0 < (k : ℤ) * B + B := by positivity
    have hleft : (1 : ℤ) ≤ (k : ℤ) * B + B := by omega
    have hright : (k : ℤ) * B + B ≤ (k : ℤ) * B + B + B := by omega
    have hend : ((k + 1 : ℕ) : ℤ) * B + B = (k : ℤ) * B + B + B := by
      push_cast
      ring
    rw [hend, ← sum_int_Ico_add _ 1 ((k : ℤ) * B + B)
      ((k : ℤ) * B + B + B) hleft hright]
    have hblock := sum_truncatedInv_hyperbolic_block_le α a q hq hcop happrox
      ((k : ℤ) * B + B) hmiddle X hX
    have hrecip : 2 * X / ((k : ℝ) * B + B) =
        (2 * X / (B : ℝ)) * (1 / ((k : ℝ) + 1)) := by
      have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hfactor : (k : ℝ) * B + B = (B : ℝ) * ((k : ℝ) + 1) := by ring
      rw [hfactor]
      field_simp
    have hblock' : (∑ n ∈ Finset.Ico ((k : ℤ) * B + B) ((k : ℤ) * B + B + B),
        truncatedInv (X / (n : ℝ)) (intDistance (α * n))) ≤
        (2 * X / (B : ℝ)) * (1 / ((k : ℝ) + 1)) + C := by
      change (∑ n ∈ Finset.Ico ((k : ℤ) * B + B) ((k : ℤ) * B + B + B),
          truncatedInv (X / (n : ℝ)) (intDistance (α * n))) ≤
          2 * X / (((k : ℤ) * B + B : ℤ) : ℝ) + C at hblock
      push_cast at hblock
      simpa only [hrecip] using hblock
    have hharm : (harmonic (k + 1) : ℝ) = (harmonic k : ℝ) + 1 / ((k : ℝ) + 1) := by
      rw [harmonic_succ]
      push_cast
      simp only [one_div]
    apply (add_le_add ih hblock').trans
    rw [hharm]
    push_cast
    ring_nf
    exact le_rfl

/-- A uniform hyperbolic reciprocal-distance bound. This is the scalar
Type-I estimate: the potentially large cap contributes `X/q`, not `X`. -/
theorem sum_truncatedInv_hyperbolic_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (X : ℝ) (hX : 0 ≤ X) (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 (M : ℤ),
      truncatedInv (X / (n : ℝ)) (intDistance (α * n))) ≤
      8 * ((M : ℝ) + q) * (1 + Real.log (2 * (q : ℝ))) +
        (4 * X / (q : ℝ)) * (1 + Real.log ((M : ℝ) + 1)) := by
  let B : ℕ := q / 2 + 1
  let k : ℕ := M / B
  let C : ℝ := 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ)))
  have hB : 0 < B := by dsimp [B]; omega
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcover : (M : ℤ) < (k : ℤ) * B + B := by
    exact_mod_cast (Nat.lt_div_mul_add (a := M) hB)
  have hsub : Finset.Icc 1 (M : ℤ) ⊆ Finset.Ico 1 ((k : ℤ) * B + B) := by
    intro n hn
    have hh := Finset.mem_Icc.mp hn
    exact Finset.mem_Ico.mpr ⟨hh.1, hh.2.trans_lt hcover⟩
  have hsum := sum_truncatedInv_hyperbolic_prefix_blocks_le α a q hq hcop happrox X hX k
  have hsum' : (∑ n ∈ Finset.Icc 1 (M : ℤ),
      truncatedInv (X / (n : ℝ)) (intDistance (α * n))) ≤
        ((k : ℝ) + 2) * C + (2 * X / (B : ℝ)) * (harmonic k : ℝ) := by
    apply le_trans ?_ hsum
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro n hn _
    apply truncatedInv_nonneg
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ico.mp hn).1
      positivity
    · exact intDistance_nonneg _
  have hqB : (q : ℝ) ≤ 2 * (B : ℝ) := by
    exact_mod_cast (show q ≤ 2 * B by dsimp [B]; omega)
  have hkB : (k : ℝ) * B ≤ M := by exact_mod_cast Nat.div_mul_le_self M B
  have hkq : (k : ℝ) * q ≤ 2 * (M : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hqB (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hlogq : 0 ≤ 1 + Real.log (2 * (q : ℝ)) := by
    have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hh := Real.log_nonneg (show 1 ≤ 2 * (q : ℝ) by linarith)
    linarith
  have hCbound : ((k : ℝ) + 2) * C ≤
      8 * ((M : ℝ) + q) * (1 + Real.log (2 * (q : ℝ))) := by
    have hh := mul_le_mul_of_nonneg_right hkq hlogq
    dsimp [C]
    nlinarith
  have hA : 2 * X / (B : ℝ) ≤ 4 * X / (q : ℝ) := by
    apply (div_le_div_iff₀ hBr hqR).mpr
    nlinarith [mul_le_mul_of_nonneg_left hqB hX]
  have hharm : (harmonic k : ℝ) ≤ 1 + Real.log ((M : ℝ) + 1) := by
    have hkle : k ≤ M + 1 := (Nat.div_le_self M B).trans (by omega)
    have hmono : (harmonic k : ℝ) ≤ (harmonic (M + 1) : ℝ) := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkle)
      intro n _ _
      positivity
    exact hmono.trans (by simpa only [Nat.cast_add, Nat.cast_one] using harmonic_le_one_add_log (M + 1))
  have hharm0 : (0 : ℝ) ≤ harmonic k := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    positivity
  exact hsum'.trans (add_le_add hCbound (mul_le_mul hA hharm hharm0 (by positivity)))

end Problem337.RationalPhaseSpacing

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.RealPhaseEnvelope

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RealPhase

/-- Distance to the nearest integer. The tie convention of `round` does not
affect this distance. -/
def integerDistance (x : ℝ) : ℝ := |x - round x|

lemma integerDistance_nonneg (x : ℝ) : 0 ≤ integerDistance x := abs_nonneg _

lemma abs_sin_fract (x : ℝ) :
    |Real.sin (Real.pi * Int.fract x)| = |Real.sin (Real.pi * x)| := by
  have he : Real.pi * Int.fract x = Real.pi * x - (⌊x⌋ : ℝ) * Real.pi := by
    simp only [Int.fract]
    ring
  rw [he, Real.sin_sub_int_mul_pi, abs_mul, abs_zpow]
  simp

/-- Jordan's sine inequality in the nearest-integer convention used by
Diophantine approximation and minor-arc spacing. -/
theorem two_integerDistance_le_abs_sin (x : ℝ) :
    2 * integerDistance x ≤ |Real.sin (Real.pi * x)| := by
  have hd : integerDistance x = min (Int.fract x) (1 - Int.fract x) :=
    abs_sub_round_eq_min x
  by_cases hzero : integerDistance x = 0
  · simp [hzero]
  have hp : 0 < integerDistance x :=
    lt_of_le_of_ne (integerDistance_nonneg x) (Ne.symm hzero)
  have hl : integerDistance x ≤ Int.fract x := by rw [hd]; exact min_le_left _ _
  have hr : Int.fract x ≤ 1 - integerDistance x := by
    have h := min_le_right (Int.fract x) (1 - Int.fract x)
    rw [← hd] at h
    linarith
  calc
    2 * integerDistance x ≤ Real.sin (Real.pi * Int.fract x) :=
      sin_pi_mul_lower_on_middle hp hl hr
    _ ≤ |Real.sin (Real.pi * Int.fract x)| := le_abs_self _
    _ = _ := abs_sin_fract x

/-- Period-one complex phase, with the same normalization as the standard
cyclic character and the circle-method Fourier sum. -/
def phase (x : ℝ) : ℂ := Complex.exp (Complex.I * (2 * Real.pi * x : ℝ))

lemma norm_phase (x : ℝ) : ‖phase x‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal _

lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [show Complex.I * (2 * Real.pi * (x + y) : ℝ) =
      Complex.I * (2 * Real.pi * x : ℝ) + Complex.I * (2 * Real.pi * y : ℝ) by
    push_cast; ring]
  exact Complex.exp_add _ _

lemma phase_nat_mul (x : ℝ) (n : ℕ) : phase ((n : ℝ) * x) = phase x ^ n := by
  unfold phase
  rw [show Complex.I * (2 * Real.pi * ((n : ℝ) * x) : ℝ) =
      (n : ℂ) * (Complex.I * (2 * Real.pi * x : ℝ)) by push_cast; ring]
  exact Complex.exp_nat_mul _ _

/-- A capped geometric envelope with the integer frequencies accounted for
explicitly, rather than assigning an invalid reciprocal at distance zero. -/
def envelope (N : ℕ) (x : ℝ) : ℝ :=
  if integerDistance x = 0 then N else min (N : ℝ) (1 / (2 * integerDistance x))

theorem norm_sum_phase_le_envelope (x : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, phase ((n : ℝ) * x)‖ ≤ envelope N x := by
  simp_rw [phase_nat_mul]
  have hcap := norm_geometric_sum_le_card (norm_phase x) N
  by_cases hx : integerDistance x = 0
  · simpa [envelope, hx] using hcap
  simp only [envelope, ite_eq_right hx]
  refine le_min hcap ?_
  have hd : 0 < integerDistance x :=
    lt_of_le_of_ne (integerDistance_nonneg x) (Ne.symm hx)
  have hs := two_integerDistance_le_abs_sin x
  have hspos : 0 < |Real.sin (Real.pi * x)| := by linarith
  calc
    _ ≤ 1 / |Real.sin (Real.pi * x)| :=
      norm_geometric_phase_sum_le (abs_pos.mp hspos) N
    _ ≤ 1 / (2 * integerDistance x) :=
      one_div_le_one_div_of_le (by positivity) hs

/-- Translating the integer interval and adding a constant phase preserve
the norm, so the same envelope handles every interval location. -/
theorem norm_sum_shift_phase_eq (x β t : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, phase (x * (t + n) + β)‖ =
      ‖∑ n ∈ Finset.range N, phase ((n : ℝ) * x)‖ := by
  have he : ∀ n : ℕ, phase (x * (t + n) + β) =
      phase (x * t + β) * phase ((n : ℝ) * x) := by
    intro n
    rw [← phase_add]
    congr 1
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, norm_mul, norm_phase, one_mul]

theorem norm_sum_shift_phase_le_envelope (x β t : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, phase (x * (t + n) + β)‖ ≤ envelope N x := by
  rw [norm_sum_shift_phase_eq]
  exact norm_sum_phase_le_envelope x N

end Problem337.RealPhase

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.RealTypeI

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RealTypeI

open RationalPhaseSpacing

lemma geometric_envelope_le_truncated_real (t : ℝ) (M : ℕ) (cap : ℝ)
    (hM : (M : ℝ) ≤ cap) :
    RealPhase.envelope M t ≤ truncatedInv cap (intDistance t) := by
  have heq : RealPhase.integerDistance t = intDistance t := abs_sub_round_eq_min t
  unfold RealPhase.envelope
  rw [heq]
  unfold truncatedInv
  split_ifs with hzero
  · exact hM
  · have hd : 0 < intDistance t :=
      lt_of_le_of_ne (intDistance_nonneg _) (Ne.symm hzero)
    exact min_le_min hM (one_div_le_one_div_of_le hd (by linarith))

/-- The explicit scalar cost of a hyperbolic Type I sum. -/
def hyperbolicCost (X : ℝ) (M q : ℕ) : ℝ :=
  8 * ((M : ℝ) + q) * (1 + Real.log (2 * (q : ℝ))) +
    (4 * X / (q : ℝ)) * (1 + Real.log ((M : ℝ) + 1))

end Problem337.RealTypeI

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanRealTypeIHyperbolic

namespace OAI
/-!
# Actual near-rational estimates for the two Vaughan Type I terms

The initial-sum estimate uses the sharper canonical harmonic hyperbola bound
for its scalar aggregation.
The variable hyperbolic lengths are retained throughout.  In particular the
right hand side has size `N / q + A + q`, up to logarithmic factors, rather
than the much larger fixed-cap estimate obtained by replacing every `N / d`
with `N`.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Problem337.VaughanHyperbolic

open Vaughan

open RationalPhaseSpacing

/-- Every truncated hyperbolic inner sum has the required variable-cap envelope.
This includes the zero-frequency case and does not require a nonresonance
assumption. -/
theorem norm_phase_Ioc_mul_le_variable (α : ℝ) (N d k : ℕ) (hk : k ≤ N / d) :
    ‖∑ b ∈ Finset.Ioc 0 k, RealPhase.phase (α * (d * b : ℕ))‖ ≤
      truncatedInv ((N : ℝ) / d) (intDistance (α * d)) := by
  have heq : (∑ b ∈ Finset.Ioc 0 k, RealPhase.phase (α * (d * b : ℕ))) =
      ∑ j ∈ Finset.range k, RealPhase.phase ((α * d) * (1 + j) + 0) := by
    rw [sum_Ioc_zero_eq_sum_range_succ]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    push_cast
    ring
  rw [heq]
  exact (RealPhase.norm_sum_shift_phase_le_envelope (α * d) 0 1 k).trans
    (RealTypeI.geometric_envelope_le_truncated_real (α * d) k ((N : ℝ) / d)
      ((by exact_mod_cast hk : (k : ℝ) ≤ (N / d : ℕ)).trans Nat.cast_div_le))

/-- The positive-initial-interval convention used by Vaughan's identity. -/
theorem sum_variable_reciprocal_Ioc_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N A : ℕ) :
    (∑ d ∈ Finset.Ioc 0 A,
      truncatedInv ((N : ℝ) / d) (intDistance (α * d))) ≤
      RealTypeI.hyperbolicCost (N : ℝ) A q := by
  have hcast : (∑ d ∈ Finset.Ioc 0 A,
      truncatedInv ((N : ℝ) / d) (intDistance (α * d))) =
      ∑ d ∈ Finset.Icc 1 (A : ℤ),
        truncatedInv ((N : ℝ) / d) (intDistance (α * d)) := by
    apply Finset.sum_nbij' (fun d : ℕ => (d : ℤ)) Int.toNat
    · intro d hd
      obtain ⟨hd0, hdA⟩ := Finset.mem_Ioc.mp hd
      exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hd0, by exact_mod_cast hdA⟩
    · intro d hd
      obtain ⟨hd1, hdA⟩ := Finset.mem_Icc.mp hd
      apply Finset.mem_Ioc.mpr
      omega
    · intro d hd
      exact Int.toNat_natCast d
    · intro d hd
      exact Int.toNat_of_nonneg (by have := (Finset.mem_Icc.mp hd).1; omega)
    · intro d hd
      simp
  rw [hcast]
  exact sum_truncatedInv_hyperbolic_le α a q hq hcop happrox N (Nat.cast_nonneg N) A

/-- The first actual Vaughan convolution, with its logarithmic inner weight,
is bounded using only a reduced rational approximation to the frequency. -/
theorem first_typeI_real_phase_bound
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N U : ℕ) :
    ‖weightedSum (Finset.Ioc 0 N) (fun n => RealPhase.phase (α * n))
        (shortPart U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)‖ ≤
      2 * Real.log N * RealTypeI.hyperbolicCost (N : ℝ) (min U N) q := by
  apply (first_typeI_bound (fun n => RealPhase.phase (α * n)) N U
    (fun d => truncatedInv ((N : ℝ) / d) (intDistance (α * d)))
    (fun d _ k hk => norm_phase_Ioc_mul_le_variable α N d k hk)).trans
  exact mul_le_mul_of_nonneg_left
    (sum_variable_reciprocal_Ioc_le α a q hq hcop happrox N (min U N))
    (by positivity)

/-- The second actual Vaughan convolution has one logarithmic coefficient
factor and the same variable-length reciprocal budget. -/
theorem second_typeI_real_phase_bound
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N U V : ℕ) :
    ‖weightedSum (Finset.Ioc 0 N) (fun n => RealPhase.phase (α * n))
        (typeICoefficient U V * ζ)‖ ≤
      Real.log N * RealTypeI.hyperbolicCost (N : ℝ) (min (U * V) N) q := by
  apply (second_typeI_bound (fun n => RealPhase.phase (α * n)) N U V
    (fun d => truncatedInv ((N : ℝ) / d) (intDistance (α * d)))
    (fun d _ => norm_phase_Ioc_mul_le_variable α N d (N / d) le_rfl)).trans
  exact mul_le_mul_of_nonneg_left
    (sum_variable_reciprocal_Ioc_le α a q hq hcop happrox N (min (U * V) N))
    (Real.log_natCast_nonneg N)

end Problem337.VaughanHyperbolic

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanTypeINormalized

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Problem337.VaughanHyperbolic

/-- A common logarithmic majorant for both actual Type I costs. -/
theorem hyperbolicCost_min_le (N A q : ℕ) (hN : 1 ≤ N) (hq : 0 < q)
    (hqN : q ≤ N) :
    RealTypeI.hyperbolicCost N (min A N) q ≤
      8 * ((N : ℝ) / q + A + q) * (1 + Real.log (2 * (N : ℝ))) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqNr : (q : ℝ) ≤ N := by exact_mod_cast hqN
  have hminA : ((min A N : ℕ) : ℝ) ≤ A := by exact_mod_cast min_le_left A N
  have hminN : ((min A N : ℕ) : ℝ) ≤ N := by exact_mod_cast min_le_right A N
  have hlogq : 0 ≤ 1 + Real.log (2 * (q : ℝ)) := by
    have := Real.log_nonneg (show 1 ≤ 2 * (q : ℝ) by linarith)
    linarith
  have hH : 0 ≤ 1 + Real.log (2 * (N : ℝ)) := by
    have := Real.log_nonneg (show 1 ≤ 2 * (N : ℝ) by linarith)
    linarith
  have hlogqN : 1 + Real.log (2 * (q : ℝ)) ≤
      1 + Real.log (2 * (N : ℝ)) := by
    gcongr
  have hlogmin : 1 + Real.log (((min A N : ℕ) : ℝ) + 1) ≤
      1 + Real.log (2 * (N : ℝ)) := by
    exact add_le_add le_rfl (Real.log_le_log (by positivity) (by linarith))
  unfold RealTypeI.hyperbolicCost
  calc
    _ ≤ 8 * ((A : ℝ) + q) * (1 + Real.log (2 * (N : ℝ))) +
        (4 * (N : ℝ) / q) * (1 + Real.log (2 * (N : ℝ))) := by
      apply add_le_add
      · exact mul_le_mul (by gcongr) hlogqN hlogq (by positivity)
      · exact mul_le_mul_of_nonneg_left hlogmin (by positivity)
    _ ≤ _ := by
      have hd : 0 ≤ (N : ℝ) / q := by positivity
      simp only [mul_div_assoc]
      nlinarith [mul_nonneg hd hH]

private lemma log_le_common (N : ℕ) (hN : 1 ≤ N) :
    Real.log N ≤ 1 + Real.log (2 * (N : ℝ)) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h := Real.log_le_log (show 0 < (N : ℝ) by linarith)
    (show (N : ℝ) ≤ 2 * N by linarith)
  linarith

/-- Uniform Type I bound in the parameters of the optimized Vaughan cutoff. -/
theorem first_typeI_normalized_bound
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N U : ℕ) (hN : 1 ≤ N) (hqN : q ≤ N) :
    ‖Vaughan.weightedSum (Finset.Ioc 0 N) (fun n => RealPhase.phase (α * n))
        (Vaughan.shortPart U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)‖ ≤
      16 * (1 + Real.log (2 * (N : ℝ))) ^ 2 * ((N : ℝ) / q + U + q) := by
  have hH : 0 ≤ 1 + Real.log (2 * (N : ℝ)) :=
    (Real.log_natCast_nonneg N).trans (log_le_common N hN)
  calc
    _ ≤ 2 * Real.log N * RealTypeI.hyperbolicCost N (min U N) q :=
      first_typeI_real_phase_bound α a q hq hcop happrox N U
    _ ≤ 2 * Real.log N *
        (8 * ((N : ℝ) / q + U + q) * (1 + Real.log (2 * (N : ℝ)))) :=
      mul_le_mul_of_nonneg_left (hyperbolicCost_min_le N U q hN hq hqN) (by positivity)
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (log_le_common N hN)
        (show 0 ≤ 16 * ((N : ℝ) / q + U + q) *
          (1 + Real.log (2 * (N : ℝ))) by positivity)
      nlinarith

/-- Uniform second Type I bound with the full product support retained. -/
theorem second_typeI_normalized_bound
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N U V : ℕ) (hN : 1 ≤ N) (hqN : q ≤ N) :
    ‖Vaughan.weightedSum (Finset.Ioc 0 N) (fun n => RealPhase.phase (α * n))
        (Vaughan.typeICoefficient U V * ζ)‖ ≤
      8 * (1 + Real.log (2 * (N : ℝ))) ^ 2 * ((N : ℝ) / q + U * V + q) := by
  have hH : 0 ≤ 1 + Real.log (2 * (N : ℝ)) :=
    (Real.log_natCast_nonneg N).trans (log_le_common N hN)
  calc
    _ ≤ Real.log N * RealTypeI.hyperbolicCost N (min (U * V) N) q :=
      second_typeI_real_phase_bound α a q hq hcop happrox N U V
    _ ≤ Real.log N *
        (8 * ((N : ℝ) / q + (U * V : ℕ) + q) * (1 + Real.log (2 * (N : ℝ)))) :=
      mul_le_mul_of_nonneg_left (hyperbolicCost_min_le N (U * V) q hN hq hqN)
        (Real.log_natCast_nonneg N)
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (log_le_common N hN)
        (show 0 ≤ 8 * ((N : ℝ) / q + U * V + q) *
          (1 + Real.log (2 * (N : ℝ))) by positivity)
      push_cast
      nlinarith

end Problem337.VaughanHyperbolic

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.VaughanEstimate

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Problem337.Vaughan

lemma realPhase_eq_bilinear_phase (x : ℝ) :
    RealPhase.phase x = VaughanBilinear.phase x :=
  (VaughanBilinear.phase_eq_geometric_phase x).symm

lemma optimized_typeI_scales (X q : ℝ) (hX : 1 ≤ X) (hq : 1 ≤ q)
    (hqX : q ≤ X) (hpow : 2 ≤ X ^ (2 / 5 : ℝ)) :
    X / q + (optimizedCutoff X : ℝ) + q ≤ 4 * approximationEnvelope X q ∧
    X / q + (optimizedCutoff X : ℝ) ^ 2 + q ≤ 4 * approximationEnvelope X q := by
  have hs := optimizedCutoff_standard_envelope X q hX hq hqX hpow
  have hdiv : 0 ≤ X / Real.sqrt (optimizedCutoff X : ℝ) := by positivity
  change _ ≤ 4 * approximationEnvelope X q at hs
  constructor <;> nlinarith [Nat.cast_nonneg (optimizedCutoff X) (α := ℝ),
    sq_nonneg (optimizedCutoff X : ℝ)]

/-- An explicit classical Vaughan estimate for the actual von Mangoldt
exponential sum. The only analytic input is a reduced rational approximation;
all Type I and Type II cancellation estimates have been proved above. -/
theorem vonMangoldt_sum_bound
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N : ℕ) (hqN : q ≤ N)
    (hpow : 2 ≤ (N : ℝ) ^ (2 / 5 : ℝ)) :
    ‖weightedSum (Finset.Ioc 0 N) (fun k => VaughanBilinear.phase (θ * k)) Λ‖ ≤
      200 * (typeIILogScale N) ^ 4 * approximationEnvelope N q := by
  let U := optimizedCutoff (N : ℝ)
  let w : ℕ → ℂ := fun k => VaughanBilinear.phase (θ * k)
  let H := typeIILogScale N
  let E := approximationEnvelope (N : ℝ) q
  have hN : 1 ≤ N := hq.trans_le hqN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqNr : (q : ℝ) ≤ N := by exact_mod_cast hqN
  have hH : 1 ≤ H := one_le_typeIILogScale N
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hE : 0 ≤ E := approximationEnvelope_nonneg N q (Nat.cast_nonneg N)
  have hH14 : H ≤ H ^ 4 := by
    simpa using (pow_le_pow_right₀ hH (show 1 ≤ 4 by omega))
  have hH24 : H ^ 2 ≤ H ^ 4 := pow_le_pow_right₀ hH (by omega)
  have hcost := optimized_typeI_scales N q hNr hqr hqNr hpow
  have hfirst := VaughanHyperbolic.first_typeI_normalized_bound θ a q hq hcop happrox
    N U hN hqN
  have hsecond := VaughanHyperbolic.second_typeI_normalized_bound θ a q hq hcop happrox
    N U U hN hqN
  simp only [realPhase_eq_bilinear_phase] at hfirst hsecond
  have h1 : ‖weightedSum (Finset.Ioc 0 N) w
      (shortPart U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)‖ ≤ 64 * H ^ 4 * E := by
    calc
      _ ≤ 16 * H ^ 2 * ((N : ℝ) / q + U + q) := hfirst
      _ ≤ 16 * H ^ 2 * (4 * E) := mul_le_mul_of_nonneg_left hcost.1 (by positivity)
      _ ≤ 64 * H ^ 4 * E := by nlinarith [mul_le_mul_of_nonneg_right hH24 hE]
  have h2 : ‖weightedSum (Finset.Ioc 0 N) w (typeICoefficient U U * ζ)‖ ≤
      32 * H ^ 4 * E := by
    calc
      _ ≤ 8 * H ^ 2 * ((N : ℝ) / q + (U : ℝ) ^ 2 + q) := by
        simpa only [H, typeIILogScale, w, pow_two] using hsecond
      _ ≤ 8 * H ^ 2 * (4 * E) := mul_le_mul_of_nonneg_left hcost.2 (by positivity)
      _ ≤ 32 * H ^ 4 * E := by nlinarith [mul_le_mul_of_nonneg_right hH24 hE]
  have h0 : ‖weightedSum (Finset.Ioc 0 N) w (shortPart U Λ)‖ ≤ H ^ 4 * E := by
    have hlog : Real.log N ≤ H ^ 4 := (log_nat_le_typeIILogScale N N le_rfl).trans hH14
    have hpower : (N : ℝ) ^ (4 / 5 : ℝ) ≤ E := by
      dsimp [E, approximationEnvelope]
      have hd : 0 ≤ (N : ℝ) / Real.sqrt q := by positivity
      linarith [Real.sqrt_nonneg ((N : ℝ) * q)]
    calc
      _ ≤ (U : ℝ) * Real.log U := norm_short_vonMangoldt_sum_le N U w (by
        intro n hn
        simp [w])
      _ ≤ (N : ℝ) ^ (4 / 5 : ℝ) * Real.log N := optimizedCutoff_log_le N hNr hpow
      _ ≤ E * H ^ 4 := mul_le_mul hpower hlog (Real.log_natCast_nonneg N) hE
      _ = _ := by ring
  have hII : ‖weightedSum (Finset.Ioc 0 N) w (typeIICoefficient U * longPart U Λ)‖ ≤
      54 * H ^ 4 * E := optimized_typeII_bound θ a q hq hcop happrox N hqN hpow
  change ‖weightedSum (Finset.Ioc 0 N) w Λ‖ ≤ 200 * H ^ 4 * E
  rw [weighted_identity (Finset.Ioc 0 N) w U U]
  calc
    _ ≤ (‖weightedSum (Finset.Ioc 0 N) w (shortPart U Λ)‖ +
        ‖weightedSum (Finset.Ioc 0 N) w
          (shortPart U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)‖) +
        ‖weightedSum (Finset.Ioc 0 N) w (typeICoefficient U U * ζ)‖ +
        ‖weightedSum (Finset.Ioc 0 N) w (typeIICoefficient U * longPart U Λ)‖ := by
      apply (norm_add_le _ _).trans
      apply add_le_add _ le_rfl
      apply (norm_sub_le _ _).trans
      exact add_le_add (norm_add_le _ _) le_rfl
    _ ≤ _ := by nlinarith [mul_nonneg (pow_nonneg hH0 4) hE]

/-- The ordinary logarithmic form of the classical Vaughan estimate. -/
theorem vonMangoldt_sum_log_bound
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N : ℕ) (hqN : q ≤ N)
    (hpow : 2 ≤ (N : ℝ) ^ (2 / 5 : ℝ)) (hlog : 1 ≤ Real.log N) :
    ‖weightedSum (Finset.Ioc 0 N) (fun k => VaughanBilinear.phase (θ * k)) Λ‖ ≤
      16200 * (Real.log N) ^ 4 * approximationEnvelope N q := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hq.trans_le hqN
  have hH : typeIILogScale N ≤ 3 * Real.log N := by
    unfold typeIILogScale
    rw [Real.log_mul (by norm_num) hNr.ne']
    linarith [Real.log_two_lt_d9]
  have hH0 : 0 ≤ typeIILogScale N := zero_le_one.trans (one_le_typeIILogScale N)
  have hE := approximationEnvelope_nonneg N q (Nat.cast_nonneg N)
  refine (vonMangoldt_sum_bound θ a q hq hcop happrox N hqN hpow).trans ?_
  calc
    _ ≤ 200 * (3 * Real.log N) ^ 4 * approximationEnvelope N q := by gcongr
    _ = _ := by ring

open Filter in
/-- The estimate holds uniformly in every reduced approximation once the
summation length is large, with an absolute explicit constant. -/
theorem eventually_vonMangoldt_sum_log_bound :
    ∀ᶠ N : ℕ in atTop, ∀ (θ : ℝ) (a : ℤ) (q : ℕ), 0 < q →
      IsCoprime a (q : ℤ) → |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 → q ≤ N →
      ‖weightedSum (Finset.Ioc 0 N) (fun k => VaughanBilinear.phase (θ * k)) Λ‖ ≤
        16200 * (Real.log N) ^ 4 * approximationEnvelope N q := by
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))
  have hpow : ∀ᶠ N : ℕ in atTop, 2 ≤ (N : ℝ) ^ (2 / 5 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hlog, hpow] with N hlog hpow
  intro θ a q hq hcop happrox hqN
  exact vonMangoldt_sum_log_bound θ a q hq hcop happrox N hqN hpow hlog

end Problem337.Vaughan

end

end OAI

open Filter


open Filter
/-- For small and large rational denominators the two endpoint terms in the
classical Vaughan estimate are simultaneously controlled by the same cutoff. -/
theorem GBMoving.vaughan_denominator_terms {x q P T : ℝ} (hx : 0 < x) (hT : 0 < T)
    (hP : 0 < P) (hTsize : T ≤ Real.sqrt P) (hlow : P ≤ q) (hhigh : q ≤ x/P) :
    x / Real.sqrt q ≤ x/T ∧ Real.sqrt (x*q) ≤ x/T := by
  have hq := hP.trans_le hlow
  have hT2 : T^2 ≤ P := (Real.le_sqrt (by positivity) hP.le).mp hTsize
  constructor
  · exact div_le_div_of_nonneg_left hx.le hT (hTsize.trans (Real.sqrt_le_sqrt hlow))
  · apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    rw [div_pow, le_div_iff₀ (by positivity)]
    have hprod := (le_div_iff₀ hP).mp hhigh
    nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT2 hq.le) hx.le,
      mul_le_mul_of_nonneg_left hprod hx.le]

theorem GBMoving.minor_approximant (Q n : ℕ) (t : ℝ) (hQ : 1 ≤ Q) (hQn : Q ≤ n)
    (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hminor : t ∉ {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ a.Coprime q ∧
      |t - a/(q:ℝ)| ≤ (Q:ℝ)/(q*n)}) :
    ∃ q a : ℕ, Q < q ∧ q ≤ n / Q ∧ a ≤ q ∧ a.Coprime q ∧
      |t - a/(q:ℝ)| ≤ 1 / ((q:ℝ)*((n/Q : ℕ)+1 : ℝ)) := by
  let B := n / Q
  have hB : 0 < B := Nat.div_pos hQn hQ
  obtain ⟨s,hs,hd⟩ := Real.exists_rat_abs_sub_le_and_den_le t hB
  have hdpos : (0 : ℝ) < s.den := Nat.cast_pos.mpr s.pos
  have hBpos : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  have hQB : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  rw [Rat.cast_def, mul_comm ((B : ℝ) + 1) (s.den : ℝ)] at hs
  have hclose : |t * s.den - s.num| < 1 := by
    have h := (mul_le_mul_of_nonneg_right hs hdpos.le)
    rw [← abs_of_pos hdpos, ← abs_mul, abs_of_pos hdpos] at h
    rw [sub_mul, div_mul_cancel₀ _ hdpos.ne'] at h
    refine h.trans_lt ?_
    rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    nlinarith
  obtain ⟨hl,hu⟩ := abs_lt.mp hclose
  have ht0 : 0 ≤ t * s.den := mul_nonneg ht.1 hdpos.le
  have ht1 : t * s.den ≤ s.den := by simpa using mul_le_mul_of_nonneg_right ht.2 hdpos.le
  have hnlo : (-1 : ℤ) < s.num := by exact_mod_cast (show (-1 : ℝ) < s.num by linarith)
  have hnhi : s.num < (s.den : ℤ) + 1 := by exact_mod_cast (show (s.num : ℝ) < s.den + 1 by linarith)
  have hcast : (s.num.natAbs : ℤ) = s.num := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
  have hcast' : (s.num.natAbs : ℝ) = s.num := by
    calc (s.num.natAbs : ℝ) = ((s.num.natAbs : ℤ) : ℝ) := by simp
         _ = _ := congrArg (fun z : ℤ => (z : ℝ)) hcast
  have hle : s.num.natAbs ≤ s.den := by exact_mod_cast (show (s.num.natAbs : ℤ) ≤ s.den by omega)
  rw [← hcast'] at hs
  refine ⟨s.den, s.num.natAbs, ?_, hd, hle, s.reduced, hs⟩
  by_contra! hsmall
  apply hminor
  refine ⟨s.den, s.num.natAbs, s.pos, hsmall, hle, s.reduced, hs.trans ?_⟩
  have hbound : (n : ℝ) < Q * ((B : ℝ) + 1) := by exact_mod_cast Nat.lt_mul_div_succ n hQ
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hbound.le hdpos.le]



theorem GBMoving.mangoldt_pointwise_bridge (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    let w := fun k : ℕ => if k.Prime then Real.log (k : ℝ) else 0
    let e := fun x : ℝ => Complex.exp (((2*Real.pi*x : ℝ):ℂ)*Complex.I)
    ‖∑ k ∈ Finset.range (n+1), ((ArithmeticFunction.vonMangoldt k - w k : ℝ):ℂ) * e ((k:ℝ)*t)‖ ≤
      2 * Real.sqrt n * Real.log n := by
  intro w e
  have hnon (k : ℕ) : 0 ≤ ArithmeticFunction.vonMangoldt k - w k := by
    by_cases hk : k.Prime <;> simp [w,hk,ArithmeticFunction.vonMangoldt_apply_prime]
  calc
    _ ≤ ∑ k ∈ Finset.range (n+1), ‖((ArithmeticFunction.vonMangoldt k - w k : ℝ):ℂ) * e ((k:ℝ)*t)‖ := norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (n+1), (ArithmeticFunction.vonMangoldt k - w k) := by
      simp only [norm_mul,e,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hnon _)]
    _ = Chebyshev.psi n - Chebyshev.theta n := by
      rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
      simp [Chebyshev.psi,Chebyshev.theta,w,Finset.sum_filter,Finset.sum_sub_distrib]
    _ ≤ _ := Chebyshev.psi_sub_theta_le (by exact_mod_cast hn)

open Finset MeasureTheory

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

theorem norm_phase (t : ℝ) : ‖phase t‖ = 1 := by simp [phase, Complex.norm_exp]

theorem continuous_fourierSum (n : ℕ) (w : ℕ → ℝ) : Continuous (fourierSum n w) := by
  unfold fourierSum phase
  fun_prop

end
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


def cutoffB (n : ℕ) := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
def deep (n : ℕ) := (wide n (cutoffB n) (256 * cutoffB n * (Nat.log 2 (n+2))^2))ᶜ

noncomputable def arcHeight (n : ℕ) := 256 * cutoffB n * (Nat.log 2 (n+2))^2

end
end GoldbachTransitionSquare

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



end
end TypeTwoDiagonal

namespace TypeTwoDiagonal
def logCost (k : ℕ) : ℝ := 2*(1+(((k+2:ℕ):ℝ)+1)^2*(((3*k+4:ℕ):ℝ)+1)^2)
end TypeTwoDiagonal

namespace TypeTwoDiagonal
open Finset MeasureTheory GoldbachTransitionSquare
noncomputable section

theorem square_difference_coeff (A : Set ℝ) (hA : MeasurableSet A)
    (p q : ℝ → ℂ) (hp : Continuous p) (hq : Continuous q) (n : ℕ)
    {T : ℝ} (hT : 0<T)
    (hcap : ∀ t ∈ Set.Ioc (0:ℝ) 1, t ∈ A → ‖p t + q t‖ ≤ T) :
    coefficient A (fun t => (p t)^2) n - coefficient A (fun t => (q t)^2) n =
      coefficient A (fun t => clip T (p t+q t)*(p t-q t)) n := by
  have he : Continuous (phase n) := by unfold phase; fun_prop
  have hi (f : ℝ → ℂ) (hf : Continuous f) :
      Integrable (A.indicator (fun t => f t ^ 2 * phase n t)) unitMeasure :=
    (continuous_unit_integrable ((hf.pow 2).mul he)).indicator hA
  unfold coefficient
  rw [←integral_sub (hi p hp) (hi q hq)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioc (a:=(0:ℝ)) (b:=1))] with t ht
  by_cases ha : t ∈ A
  · simp only [Set.indicator_of_mem ha,clip,max_eq_left (hcap t ht ha),div_self hT.ne',
      Complex.ofReal_one,one_mul]
    ring
  · simp [ha]

theorem clipped_product_mass (p q : ℝ → ℂ) (hp : Continuous p) (hq : Continuous q)
    {T : ℝ} (hT : 0<T) :
    mass Set.univ (fun t => clip T (p t) * q t) ≤ T^2*mass Set.univ q := by
  simp only [mass,Set.indicator_univ]
  rw [←integral_const_mul]
  have hc := ((clip_continuous hT).comp hp).mul hq
  apply integral_mono (continuous_unit_integrable (hc.norm.pow 2)) (continuous_unit_integrable (continuous_const.mul (hq.norm.pow 2)))
  intro t
  change ‖clip T (p t) * q t‖^2 ≤ T^2*‖q t‖^2
  rw [norm_mul,mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (clip_bounds hT _).1 2) (sq_nonneg _)

/-- Telescoping the squares makes the energy budget additive across disjoint
    index intervals, even when the masks and terminal indices vary together. -/
theorem moving_square_bound (k h : ℕ) (hk : 32 ≤ k) (S : Finset ℕ)
    (hS : ∀ i ∈ S, octave k ≤ i ∧ i ≤ 8*octave k)
    (P : ℕ → ℝ → ℂ) (hc : ∀ j, Continuous (P j)) (h0 : P 0 = fun _ => 0)
    (energy : ℕ → ℝ) (he : ∀ j, 0 ≤ energy j)
    (diff : ∀ l r, l ≤ r → r ≤ 2^h →
      mass Set.univ (fun t => P r t-P l t) ≤ blockSum energy l r)
    (cut : ℕ → ℕ) (hcut : ∀ i ∈ S, cut i ≤ 2^h)
    (T : ℝ) (hT : 0<T)
    (cap : ∀ i ∈ S, ∀ j ≤ 2^h, ∀ t ∈ Set.Ioc (0:ℝ) 1, t ∈ deep i → ‖P j t‖ ≤ T) :
    (∑ i ∈ S, ‖coefficient (deep i) (fun t => (P (cut i) t)^2) i‖^2) ≤
      ((h:ℝ)+1)^2*(logCost k*(2*T)^2)*blockSum energy 0 (2^h) := by
  classical
  let B i j := coefficient (deep i) (fun t => (P j t)^2) i
  let F i j := B i (j+1) - B i j
  have tel (i l r : ℕ) (hlr : l ≤ r) : blockSum (F i) l r = B i r-B i l := by
    unfold blockSum
    rw [sum_Ico_eq_sub _ hlr]
    simp only [F, sum_range_sub]
    abel
  have pos : 0≤logCost k := by unfold logCost; positivity
  have h2 : 0<2*T := by positivity
  have common (A : Finset ℕ) (hA : A ⊆ S) (l r : ℕ) (hr : r ≤ 2^h) :
      (∑ i ∈ A, ‖blockSum (F i) l r‖^2) ≤ (logCost k*(2*T)^2)*blockSum energy l r := by
    by_cases hl : l ≤ r
    · let g := fun t => clip (2*T) (P r t + P l t)*(P r t - P l t)
      have hg : Continuous g := ((clip_continuous h2).comp ((hc r).add (hc l))).mul ((hc r).sub (hc l))
      have eq i (hi : i ∈ A) : blockSum (F i) l r = coefficient (deep i) g i := by
        rw [tel i l r hl]
        apply square_difference_coeff _ (wide_measurable ..).compl _ _ (hc r) (hc l) i h2
        intro t ht hd
        have z := add_le_add (cap i (hA hi) r hr t ht hd) (cap i (hA hi) l (hl.trans hr) t ht hd)
        exact (norm_add_le ..).trans (z.trans_eq (by ring))
      have bound := block_bessel k hk A (fun i hi => hS i (hA hi)) g hg
      change _ ≤ logCost k * mass Set.univ g at bound
      have en := (clipped_product_mass _ _ ((hc r).add (hc l)) ((hc r).sub (hc l)) h2).trans
        (mul_le_mul_of_nonneg_left (diff l r hl hr) (sq_nonneg _))
      calc
        _ = ∑ i ∈ A, ‖coefficient (deep i) g i‖^2 := sum_congr rfl (fun i hi => by rw [eq i hi])
        _ ≤ _ := bound.trans ((mul_le_mul_of_nonneg_left en pos).trans_eq (mul_assoc ..).symm)
    · simp [blockSum,Ico_eq_empty_of_le (le_of_lt (lt_of_not_ge hl))]
  have bd := dyadic_prefix_bound S F energy he (2^h) _ (mul_nonneg pos (sq_nonneg _)) common cut h 0 S (Subset.rfl) (by simp)
  simp only [zero_add] at bd
  apply le_trans (le_of_eq (sum_congr rfl (fun i hi => ?_))) bd
  rw [min_eq_right (hcut i hi),tel i 0 (cut i) (Nat.zero_le _)]
  simp [B, h0, coefficient]

end
end TypeTwoDiagonal

namespace GBMoving
open Finset Filter GoldbachTransitionSquare
noncomputable section

def w (j : ℕ) : ℝ := if j.Prime then Real.log j else 0

/-- A rational approximation selected by the actual mask also controls shorter
    and longer prime sums throughout the same block. -/
theorem denominator_on_deep (n B : ℕ) (hB : B ≤ cutoffB n)
    (hn : 2 ≤ n) (hc : 2 ≤ (n:ℝ)^(1/3:ℝ)) (t : ℝ)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hd : t ∈ deep n) :
    ∃ q a : ℕ, B ≤ q ∧ 0<q ∧ a.Coprime q ∧
      |t-(a:ℝ)/q| ≤ 1/(q:ℝ)^2 ∧ q ≤ n ∧
      (n:ℝ)/Real.sqrt q ≤ 2*(n:ℝ)^(5/6:ℝ) ∧
      Real.sqrt ((n:ℝ)*q) ≤ 2*(n:ℝ)^(5/6:ℝ) := by
  have hx : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have hx1 : 1≤(n:ℝ) := by exact_mod_cast (by omega : 1≤n)
  have hQ : 1 ≤ cutoffB n := (Nat.le_floor_iff (Real.rpow_nonneg hx.le _)).mpr (by push_cast; linarith)
  have hQn : cutoffB n ≤ n := Nat.floor_le_of_le <| (Real.rpow_le_rpow_of_exponent_le hx1
    (by norm_num : (1/3:ℝ) ≤ 1)).trans_eq (Real.rpow_one _)
  have hH : cutoffB n ≤ arcHeight n := by
    have hk : 1 ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by decide) (by simp)
    dsimp [arcHeight]
    nlinarith [Nat.mul_le_mul_left (256*cutoffB n)
      (show 1 ≤ (Nat.log 2 (n+2))^2 by simpa only [sq,Nat.one_mul] using Nat.mul_le_mul hk hk)]
  obtain ⟨q,a,hPq,hqB,_,hcop,happrox⟩ := minor_approximant (cutoffB n) n t hQ hQn ht (by
    rintro ⟨q,a,hq,hqQ,ha,hc',he⟩
    exact hd ⟨q,a,hq,hqQ,ha,hc',he.trans (div_le_div_of_nonneg_right (by exact_mod_cast hH) (by positivity))⟩)
  have hqp : 0<q := by omega
  have hqr : (0:ℝ)<q := by exact_mod_cast hqp
  have hPr : (0:ℝ)<cutoffB n := by exact_mod_cast (by omega : 0<cutoffB n)
  have hsec : |t - (a:ℝ)/q| ≤ 1/(q:ℝ)^2 := by
    apply happrox.trans
    apply one_div_le_one_div_of_le (by positivity)
    rw [sq]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ_of_le hqB) hqr.le
  have hhigh : (q:ℝ) ≤ n/(cutoffB n) := (le_div_iff₀ hPr).mpr
    (by exact_mod_cast (Nat.le_div_iff_mul_le hQ).mp hqB)
  have hT : 0 < (n:ℝ)^(1/6:ℝ)/2 := by positivity
  have hTsq : ((n:ℝ)^(1/6:ℝ))^2 = (n:ℝ)^(1/3:ℝ) := by
    rw [←Real.rpow_mul_natCast hx.le]; norm_num
  have hTlow : (n:ℝ)^(1/6:ℝ)/2 ≤ Real.sqrt (cutoffB n) := by
    apply (Real.le_sqrt (by positivity) hPr.le).mpr
    have hf : (n:ℝ)^(1/3:ℝ) < (cutoffB n:ℝ)+1 := Nat.lt_floor_add_one _
    nlinarith only [hf,hTsq,hc]
  obtain ⟨hl,hr⟩ := vaughan_denominator_terms hx hT hPr hTlow
    (by exact_mod_cast hPq.le : (cutoffB n:ℝ) ≤ q) hhigh
  have xid : (n:ℝ)/((n:ℝ)^(1/6:ℝ)/2) = 2*(n:ℝ)^(5/6:ℝ) := by
    have hh := Real.rpow_pos_of_pos hx (1/6:ℝ)
    have hid : (n:ℝ)^(5/6:ℝ)*(n:ℝ)^(1/6:ℝ)=n := by rw [←Real.rpow_add hx]; norm_num
    field_simp; nlinarith only [hid]
  rw [xid] at hl hr
  exact ⟨q,a,hB.trans hPq.le,hqp,hcop,hsec,hqB.trans (Nat.div_le_self _ _),hl,hr⟩

theorem prime_sum_trivial (y : ℕ) (t : ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hl : ∀ i ≤ y, i.Prime → Real.log i ≤ L) :
    ‖fourierSum y w t‖ ≤ ((y:ℝ)+1)*L := by
  unfold fourierSum
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ _i ∈ range (y+1), L := sum_le_sum fun i hi => by
      rw [norm_mul,GoldbachTransitionSquare.norm_phase,mul_one,Complex.norm_real,Real.norm_eq_abs]
      by_cases hp : i.Prime
      · have one : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hp.one_le
        simpa only [w,if_pos hp,abs_of_nonneg (Real.log_nonneg one)] using
          (hl i (Nat.le_of_lt_succ (mem_range.mp hi)) hp)
      · simpa [w,hp] using hL
    _ = _ := by simp

theorem sum_vaughan_eq (y : ℕ) (t : ℝ) :
    fourierSum y ArithmeticFunction.vonMangoldt t = OAI.Problem337.Vaughan.weightedSum
      (Finset.Ioc 0 y) (fun k => OAI.Problem337.VaughanBilinear.phase (t*k)) ArithmeticFunction.vonMangoldt := by
  dsimp [fourierSum,GoldbachTransitionSquare.phase,OAI.Problem337.Vaughan.weightedSum,OAI.Problem337.VaughanBilinear.phase]
  rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le y)]
  simp only [ArithmeticFunction.map_zero,Complex.ofReal_zero,zero_mul,zero_add,Real.fourierChar_apply]
  apply Finset.sum_congr rfl
  intro k _; rw [mul_comm t (k:ℝ)]

theorem enough_prefixes :
    ∀ᶠ n : ℕ in atTop, ∀ t ∈ Set.Icc (0:ℝ) 1, t ∈ deep n → ∀ y : ℕ, y ≤ 16*n →
      ‖fourierSum y w t‖ ≤ 1000000*(Real.log (16*(n:ℝ)))^4*(n:ℝ)^(5/6:ℝ) := by
  obtain ⟨B,hB⟩ := eventually_atTop.mp OAI.Problem337.Vaughan.eventually_vonMangoldt_sum_log_bound
  have cub := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/3)).comp tendsto_natCast_atTop_atTop
  have logg := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2:ℕ),cub.eventually_ge_atTop (max (B:ℝ) 2),
    logg.eventually_ge_atTop 1] with n hn hc hlog
  intro t ht hd y hy
  let x : ℝ := n
  let L := Real.log (16*x)
  let Z := x^(5/6:ℝ)
  have hx : 0<x := by dsimp [x]; exact_mod_cast (by omega : 0<n)
  have hx1 : 1≤x := by dsimp [x]; exact_mod_cast (by omega : 1≤n)
  change max (B:ℝ) 2 ≤ x^(1/3:ℝ) at hc
  have hfloor : B ≤ cutoffB n := (Nat.le_floor_iff (Real.rpow_nonneg hx.le _)).mpr ((le_max_left ..).trans hc)
  obtain ⟨q,a,hBq,hq,hcop,hsec,hqn,hm1,hm2⟩ := denominator_on_deep n B hfloor hn ((le_max_right ..).trans hc) t ht hd
  have hL : 1≤L := le_trans hlog (Real.log_le_log hx (by dsimp [x]; linarith only [hx.le] : x ≤ 16*x))
  have hlog4 : L≤L^4 := by simpa only [pow_one] using pow_le_pow_right₀ hL (by decide : 1≤4)
  have hZ : 0<Z := Real.rpow_pos_of_pos hx _
  have hyx : (y:ℝ) ≤ 16*x := by dsimp [x]; exact_mod_cast hy
  change x/Real.sqrt q ≤ 2*Z at hm1
  change Real.sqrt (x*q) ≤ 2*Z at hm2
  change _ ≤ 1000000*L^4*Z
  by_cases hyq : q ≤ y
  · have yp : 0<y := hq.trans_le hyq
    have yr : 0<(y:ℝ) := by exact_mod_cast yp
    have ly : 0 ≤ Real.log (y:ℝ) := Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt yp)
    have ly' : Real.log (y:ℝ) ≤ L := Real.log_le_log yr hyx
    have hv := hB y (hBq.trans hyq) t (a:ℤ) q hq hcop.isCoprime (by simpa using hsec) hyq
    rw [←sum_vaughan_eq] at hv
    have h1 : (y:ℝ)/Real.sqrt q ≤ 32*Z := calc
      _ ≤ (16*x)/Real.sqrt q := div_le_div_of_nonneg_right hyx (Real.sqrt_nonneg _)
      _ = 16*(x/Real.sqrt q) := by ring
      _ ≤ _ := by linarith only [hm1]
    have h2 : Real.sqrt ((y:ℝ)*q) ≤ 8*Z := calc
      _ ≤ Real.sqrt ((16*x)*q) := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hyx (by positivity))
      _ = 4*Real.sqrt (x*q) := by rw [show 16*x*(q:ℝ) = 16*(x*q) by ring,Real.sqrt_mul (by norm_num : (0:ℝ)≤16)]; norm_num
      _ ≤ _ := by linarith only [hm2]
    have hy45 : (y:ℝ)^(4/5:ℝ) ≤ 16*Z := calc
      _ ≤ (16*x)^(4/5:ℝ) := Real.rpow_le_rpow yr.le hyx (by norm_num)
      _ = (16:ℝ)^(4/5:ℝ)*x^(4/5:ℝ) := Real.mul_rpow (by norm_num) hx.le
      _ ≤ 16*Z := mul_le_mul
        ((Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤16) (by norm_num : (4/5:ℝ)≤1)).trans_eq (Real.rpow_one _))
        (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (4/5:ℝ)≤5/6)) (by positivity) (by norm_num)
    change ‖fourierSum y ArithmeticFunction.vonMangoldt t‖ ≤
      16200*(Real.log y)^4*((y:ℝ)/Real.sqrt q+(y:ℝ)^(4/5:ℝ)+Real.sqrt ((y:ℝ)*q)) at hv
    have von : ‖fourierSum y ArithmeticFunction.vonMangoldt t‖ ≤ 907200*L^4*Z := hv.trans (calc
      _ ≤ 16200*L^4*(56*Z) := by gcongr <;> first | assumption | linarith only [h1,h2,hy45]
      _ = _ := by ring)
    have err : ‖fourierSum y ArithmeticFunction.vonMangoldt t-fourierSum y w t‖ ≤ 2*Real.sqrt y*Real.log y := by
      simpa only [fourierSum,GoldbachTransitionSquare.phase,w,←Finset.sum_sub_distrib,←sub_mul,←Complex.ofReal_sub] using mangoldt_pointwise_bridge y yp t
    have ys : Real.sqrt y ≤ 4*Z := calc
      _ ≤ Real.sqrt (16*x) := Real.sqrt_le_sqrt hyx
      _ = 4*Real.sqrt x := by rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤16)]; norm_num
      _ ≤ _ := by rw [Real.sqrt_eq_rpow]; gcongr; exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1/2:ℝ)≤5/6)
    have er : 2*Real.sqrt y*Real.log y ≤ (2*(4*Z))*L^4 :=
      mul_le_mul (by linarith only [ys]) (ly'.trans hlog4) ly (by positivity)
    have tri := norm_sub_le (fourierSum y ArithmeticFunction.vonMangoldt t)
      (fourierSum y ArithmeticFunction.vonMangoldt t-fourierSum y w t)
    rw [sub_sub_cancel] at tri
    nlinarith only [tri,err,er,von,mul_nonneg (sq_nonneg (L^2)) hZ.le,
      mul_nonneg (show 0≤L^4 by positivity) hZ.le]
  · have yq : y+1 ≤ q := by omega
    have qr : (q:ℝ) ≤ Real.sqrt (x*q) := (Real.le_sqrt (by positivity) (by positivity)).mpr (by
      rw [sq]; exact mul_le_mul_of_nonneg_right (by dsimp [x]; exact_mod_cast hqn : (q:ℝ) ≤ x) (by positivity))
    have small := prime_sum_trivial y t (by linarith only [hL] : 0≤L) (fun i hi hp =>
      Real.log_le_log (by exact_mod_cast hp.pos) ((by exact_mod_cast hi : (i:ℝ) ≤ y).trans hyx))
    have ey : (y:ℝ)+1 ≤ 2*Z := (by exact_mod_cast yq : (y:ℝ)+1 ≤ (q:ℝ)).trans (qr.trans hm2)
    have s := small.trans (mul_le_mul ey hlog4 (by linarith only [hL]) (by positivity))
    nlinarith only [s,mul_nonneg (show 0≤L^4 by positivity) hZ.le]

end
end GBMoving

namespace GBMoving
open Finset TypeTwoDiagonal GoldbachTransitionSquare MeasureTheory Filter
noncomputable section

def P (j : ℕ) (t : ℝ) : ℂ :=
  ∑ i  ∈  range j, (w i : ℂ)*GoldbachTransitionSquare.phase ((i:ℝ)*t)

theorem P_succ (j : ℕ) : P (j+1) = fourierSum j w := rfl

theorem P_cont (j : ℕ) : Continuous (P j) := by
  cases j with
  | zero => rw [show P 0 = fun _ => 0 by funext; simp [P]]; exact continuous_const
  | succ j => exact continuous_fourierSum j w

theorem P_zero : P 0 = fun _ => 0 := by funext; simp [P]

theorem prime_interval_energy (l r : ℕ) (hl : l ≤ r) :
    mass Set.univ (fun t => P r t-P l t) = blockSum (fun j => (w j)^2) l r := by
  let f j := if j  ∈  Ico l r then w j else 0
  have incl : Ico l r ⊆ range (r+1) :=
    fun i hi => mem_range.mpr (by have := (mem_Ico.mp hi).2; omega)
  have eq : (fun t => P r t-P l t) = fourierSum r f := by
    funext t
    dsimp only [P,fourierSum,f]
    rw [←sum_Ico_eq_sub _ hl]
    simp only [apply_ite (fun x : ℝ => (x:ℂ)),Complex.ofReal_zero,ite_mul,zero_mul,sum_ite_mem,inter_eq_right.mpr incl]
  rw [eq]
  have par : mass Set.univ (fourierSum r f) = ∑ j  ∈  range (r+1), (f j)^2 := by
    simpa only [mass,Set.indicator_univ,unitMeasure,fourierSum,GoldbachTransitionSquare.phase,
      intervalIntegral.integral_of_le zero_le_one] using GoldbachTransitionFourier.continuous_parseval r f
  rw [par]
  simp only [f,ite_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,
    sum_ite_mem,inter_eq_right.mpr incl,blockSum]

theorem w_bound (j M : ℕ) (h : j  ≤  M) (hM : 1 ≤ M) : |w j|  ≤  Real.log M := by
  by_cases hp : j.Prime
  · rw [w,if_pos hp,abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_le : (1:ℝ)  ≤  j))]
    exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast h)
  · simp [w,hp,Real.log_nonneg (by exact_mod_cast hM : (1:ℝ) ≤ M)]

def value (n : ℕ) : ℂ := coefficient (deep n) (fun t => (fourierSum n w t)^2) n

theorem prime_block (k N : ℕ) (hk : 32  ≤  k) (hN : N=octave k)
    (S : Finset ℕ) (hS : ∀ i  ∈  S, N ≤ i ∧ i ≤ 8*N)
    (hu : ∀ n  ∈  S, ∀ t  ∈  Set.Icc (0:ℝ) 1, t ∈ deep n → ∀ y : ℕ, y ≤ 16*n →
      ‖fourierSum y w t‖  ≤  1000000*(Real.log (16*(n:ℝ)))^4*(n:ℝ)^(5/6:ℝ)) :
    (∑ n  ∈  S, ‖value n‖^2)  ≤  ((3*(k:ℝ)+5)^2)*(logCost k*
      (2*(1000000*(Real.log (128*(N:ℝ)))^4*(8*(N:ℝ))^(5/6:ℝ)))^2)*
      (16*(N:ℝ)*(Real.log (16*(N:ℝ)))^2) := by
  have hn : 0<N := by rw [hN,octave]; positivity
  have hr : (0:ℝ)<N := by exact_mod_cast hn
  have p16 : 2^(3*k+4) = 16*N := by rw [pow_add,←octave_eq,←hN]; ring
  let T := 1000000*(Real.log (128*(N:ℝ)))^4*(8*(N:ℝ))^(5/6:ℝ)
  have lg : 0<Real.log (128*(N:ℝ)) := Real.log_pos (by
    have one : (1:ℝ) ≤ N := by exact_mod_cast hn
    linarith)
  have hT : 0<T := by dsimp [T]; positivity
  have cap n (hi : n ∈ S) (j : ℕ) (hj : j ≤ 2^(3*k+4)) (t : ℝ) (ht : t ∈ Set.Ioc (0:ℝ) 1) (hd : t ∈ deep n) :
      ‖P j t‖  ≤  T := by
    obtain ⟨lo,up⟩ := hS n hi
    rw [p16] at hj
    cases j with
    | zero => simpa only [P_zero,norm_zero] using hT.le
    | succ j =>
      have nn : 0<(n:ℝ) := by exact_mod_cast hn.trans_le lo
      have v := hu n hi t ⟨ht.1.le,ht.2⟩ hd j (by omega)
      apply v.trans
      dsimp only [T]
      have nu : (n:ℝ) ≤ 8*(N:ℝ) := by exact_mod_cast up
      have z : 0  ≤  Real.log (16*(n:ℝ)) := Real.log_nonneg (by
        have one : (1:ℝ) ≤ n := by exact_mod_cast hn.trans_le lo
        linarith)
      have z' : Real.log (16*(n:ℝ))  ≤  Real.log (128*(N:ℝ)) := Real.log_le_log (by positivity) (by linarith only [nu])
      gcongr
  have M : 1 ≤ 16*N := by omega
  have energy : blockSum (fun j => (w j)^2) 0 (2^(3*k+4))  ≤
      16*(N:ℝ)*(Real.log (16*(N:ℝ)))^2 := by
    rw [p16]
    unfold blockSum
    calc
      _  ≤  ∑ _j  ∈  Ico 0 (16*N), (Real.log ((16*N:ℕ):ℝ))^2 := by
        apply sum_le_sum
        intro j hj
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (w_bound j (16*N) (mem_Ico.mp hj).2.le M) 2
      _ = _ := by simp
  have h := moving_square_bound k (3*k+4) hk S (by simpa only [←hN] using hS) P P_cont P_zero
    (fun j => (w j)^2) (fun j => sq_nonneg _) (fun l r hl _ => (prime_interval_energy l r hl).le)
    (fun n => n+1) (by intro i hi; rw [p16]; have := (hS i hi).2; omega) T hT cap
  change (∑ n  ∈  S, ‖value n‖^2)  ≤  _ at h
  have cp : 0  ≤  (((3*k+4:ℕ):ℝ)+1)^2*(logCost k*(2*T)^2) := by unfold logCost; positivity
  apply h.trans
  apply (mul_le_mul_of_nonneg_left energy cp).trans_eq
  dsimp only [T]
  push_cast
  ring

end
end GBMoving

namespace GBMoving
open Finset Filter TypeTwoDiagonal
noncomputable section

theorem pack_prime_block (k N X : ℕ) (ho : N = octave k)
    (hn : N ≤ 8*X) (hx : 1024 ≤ X) (hlog : 1 ≤ Real.log (X:ℝ)) :
    ((3*(k:ℝ)+5)^2)*(logCost k*
      (2*(1000000*(Real.log (128*(N:ℝ)))^4*(8*(N:ℝ))^(5/6:ℝ)))^2)*
      (16*(N:ℝ)*(Real.log (16*(N:ℝ)))^2) ≤
      10^26*(2*Real.log (X:ℝ))^16*(X:ℝ)^(8/3:ℝ) := by
  let L := 2*Real.log (X:ℝ)
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have lp : 0 < L := by linarith
  have xp : (0:ℝ)<X := by exact_mod_cast (by omega : 0<X)
  have np : 0<N := by rw [ho,octave]; positivity
  have nr : (0:ℝ)<N := by exact_mod_cast np
  have nr1 : (1:ℝ) ≤ N := by exact_mod_cast np
  have nx : (N:ℝ) ≤ 8*(X:ℝ) := by exact_mod_cast hn
  have lg128 : Real.log (128*(N:ℝ)) ≤ L := calc
    _ ≤ Real.log ((X:ℝ)*(X:ℝ)) := Real.log_le_log (by positivity) (by
      have xx := mul_le_mul_of_nonneg_right (by exact_mod_cast hx : (1024:ℝ) ≤ X) xp.le
      linarith only [xx,nx])
    _ = _ := by rw [Real.log_mul xp.ne' xp.ne']; dsimp [L]; ring
  have lg16 : Real.log (16*(N:ℝ)) ≤ L :=
    (Real.log_le_log (by positivity) (by linarith only [nr.le] : 16*(N:ℝ) ≤ 128*N)).trans lg128
  have lk : (k:ℝ)*Real.log 2 ≤ L := calc
    _ = Real.log ((2:ℝ)^k) := (Real.log_pow ..).symm
    _ ≤ Real.log (128*(N:ℝ)) := Real.log_le_log (by positivity) (by
      have small : 2^k ≤ N := by
        rw [ho,octave_eq]
        exact Nat.pow_le_pow_right (by decide) (by omega)
      have s : (2:ℝ)^k ≤ N := by exact_mod_cast small
      linarith)
    _ ≤ _ := lg128
  have kl : (k:ℝ) ≤ 2*L := by
    have z := mul_le_mul_of_nonneg_left (by linarith [Real.log_two_gt_d9] : (1/2:ℝ) ≤ Real.log 2) (Nat.cast_nonneg k)
    linarith only [z,lk]
  have a : 3*(k:ℝ)+5 ≤ 11*L := by linarith
  have b : (k:ℝ)+3 ≤ 5*L := by linarith
  have a2 := pow_le_pow_left₀ (by positivity : 0 ≤ 3*(k:ℝ)+5) a 2
  have b2 := pow_le_pow_left₀ (by positivity : 0 ≤ (k:ℝ)+3) b 2
  have c : logCost k ≤ 6052*L^4 := by
    have p := mul_le_mul b2 a2 (by positivity) (by positivity)
    have one : 1 ≤ L^4 := one_le_pow₀ hL
    unfold logCost
    push_cast
    nlinarith only [p,one]
  have lr : 0 ≤ Real.log (128*(N:ℝ)) := Real.log_nonneg (by linarith)
  have ls : 0 ≤ Real.log (16*(N:ℝ)) := Real.log_nonneg (by linarith)
  have power : (8*(N:ℝ))^(5/6:ℝ) ≤ 64*(X:ℝ)^(5/6:ℝ) := calc
    _ ≤ (64*(X:ℝ))^(5/6:ℝ) := Real.rpow_le_rpow (by positivity) (by linarith only [nx]) (by norm_num)
    _ = (64:ℝ)^(5/6:ℝ)*(X:ℝ)^(5/6:ℝ) := Real.mul_rpow (by norm_num) xp.le
    _ ≤ _ := mul_le_mul_of_nonneg_right
      ((Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 64) (by norm_num : (5/6:ℝ) ≤ 1)).trans_eq (Real.rpow_one _)) (by positivity)
  have cap : 2*(1000000*Real.log (128*(N:ℝ))^4*(8*(N:ℝ))^(5/6:ℝ)) ≤
      2*(1000000*L^4*(64*(X:ℝ)^(5/6:ℝ))) := by gcongr
  have cap2 := pow_le_pow_left₀ (by positivity) cap 2
  have ez : 16*(N:ℝ)*Real.log (16*(N:ℝ))^2 ≤ 128*(X:ℝ)*L^2 :=
    mul_le_mul (by linarith only [nx]) (pow_le_pow_left₀ ls lg16 2) (sq_nonneg _) (by positivity)
  have lc : 0≤logCost k := by unfold logCost; positivity
  have xl : ((X:ℝ)^(5/6:ℝ))^2*(X:ℝ)=(X:ℝ)^(8/3:ℝ) := by
    rw [←Real.rpow_mul_natCast xp.le, ←Real.rpow_add_one xp.ne']; norm_num
  change _ ≤ 10^26*L^16*(X:ℝ)^(8/3:ℝ)
  calc
    _ ≤ (11*L)^2*(6052*L^4*(2*(1000000*L^4*(64*(X:ℝ)^(5/6:ℝ))))^2)*(128*(X:ℝ)*L^2) := by
      apply mul_le_mul _ ez (by positivity) (by positivity)
      exact mul_le_mul a2 (mul_le_mul c cap2 (by positivity) (by positivity)) (by positivity) (by positivity)
    _ ≤ _ := by
      rw [←xl]
      nlinarith only [mul_nonneg (show 0 ≤ L^16 by positivity)
        (mul_nonneg (sq_nonneg ((X:ℝ)^(5/6:ℝ))) xp.le)]

theorem moving_prime_moment (η : ℝ) (he : 0<η) :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      (∑ n ∈ Icc X (2*X), ‖value n‖^2) ≤ (X:ℝ)^(8/3 + η : ℝ) := by
  obtain ⟨M,hm⟩ := eventually_atTop.mp enough_prefixes
  have ht : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have small := ((isLittleO_log_rpow_rpow_atTop (16:ℝ) he).comp_tendsto ht).bound
    (by norm_num : (0:ℝ)<1/(2*10^26*2^16))
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop M,eventually_ge_atTop (2^96:ℕ),
    (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 1,small] with X hM hX hl hsmall
  have xp : 0<X := (by decide : 0<(2^96:ℕ)).trans_le hX
  have xr : (0:ℝ)<X := by exact_mod_cast xp
  have hx : 1024 ≤ X := (by decide : 1024 ≤ (2^96:ℕ)).trans hX
  let j := Nat.log 2 X
  let k := j/3
  have hj : 96 ≤ j := (Nat.le_log_iff_pow_le (by decide) xp.ne').mpr hX
  have hk : 32 ≤ k := by dsimp [k]; omega
  have low : octave k ≤ X := by
    rw [octave_eq]
    exact (Nat.pow_le_pow_right (by decide : 1≤2) (by dsimp [k]; omega : 3*k ≤ j)).trans (Nat.pow_log_le_self 2 xp.ne')
  have high : X ≤ 8*octave k := by
    have h := Nat.lt_pow_succ_log_self (by decide : 1<2) X
    have hh : X < 2^(3*k+3) := h.trans_le (Nat.pow_le_pow_right (by decide : 1≤2)
      (by change j+1 ≤ 3*(j/3)+3; omega))
    rw [pow_add,←octave_eq] at hh
    omega
  have succ_oct : octave (k+1) = 8*octave k := by rw [octave,octave,pow_succ]; ring
  let S := Icc X (2*X)
  let A := S.filter (fun n => n ≤ 8*octave k)
  let B := S.filter (fun n => ¬n ≤ 8*octave k)
  let K := 10^26*(2*Real.log (X:ℝ))^16*(X:ℝ)^(8/3:ℝ)
  have block (u : ℕ) (hu : 32≤u) (b : Finset ℕ) (hb : b ⊆ S)
      (hd : ∀ n ∈ b, octave u ≤ n ∧ n ≤ 8*octave u) (hscale : octave u ≤ 8*X) :
      (∑ n ∈ b, ‖value n‖^2) ≤ K :=
    (prime_block u (octave u) hu rfl b hd
      (fun n h => hm n (hM.trans (mem_Icc.mp (hb h)).1))).trans
      (pack_prime_block u (octave u) X rfl hscale hx hl)
  have ba := block k hk A (filter_subset ..) (by
    intro n h; obtain ⟨ha,hm'⟩ := mem_filter.mp h; exact ⟨low.trans (mem_Icc.mp ha).1,hm'⟩) (by omega)
  have bb := block (k+1) (by omega) B (filter_subset ..) (by
    intro n h; obtain ⟨ha,hm'⟩ := mem_filter.mp h
    have hh := (mem_Icc.mp ha).2
    rw [succ_oct]; omega) (by rw [succ_oct]; omega)
  have e : (Real.log (X:ℝ))^16 ≤ (1/(2*10^26*2^16):ℝ)*(X:ℝ)^η := by
    change ‖(Real.log (X:ℝ))^(16:ℝ)‖ ≤ _ * ‖(X:ℝ)^η‖ at hsmall
    simpa only [Real.norm_eq_abs,Real.rpow_ofNat,abs_of_nonneg (show 0 ≤ Real.log (X:ℝ)^16 by positivity),
      abs_of_nonneg (Real.rpow_nonneg xr.le η)] using hsmall
  calc
    _ = (∑ n ∈ A, ‖value n‖^2)+(∑ n ∈ B, ‖value n‖^2) := (sum_filter_add_sum_filter_not ..).symm
    _ ≤ K+K := add_le_add ba bb
    _ ≤ _ := by
      dsimp only [K]
      rw [Real.rpow_add xr]
      nlinarith only [mul_le_mul_of_nonneg_right e (Real.rpow_nonneg xr.le (8/3:ℝ))]

end
end GBMoving

namespace GBMoving
open Finset
noncomputable section

/-- The same lower scale works for every positive threshold. -/
theorem prime_exceptions (η : ℝ) (he : 0<η) :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X → ∀ ε : ℝ, 0<ε →
      (((Icc X (2*X)).filter (fun n : ℕ => Even n ∧ ε*(n:ℝ) ≤ ‖value n‖)).card:ℝ) ≤
        (X:ℝ)^(2/3+η:ℝ)/ε^2 := by
  classical
  obtain ⟨N,hN⟩ := moving_prime_moment η he
  refine ⟨max 1 N,?_⟩
  intro X hX ε hp
  have xp : 0<(X:ℝ) := by exact_mod_cast (le_max_left 1 N).trans hX
  let S := Icc X (2*X)
  let E := S.filter (fun n : ℕ => Even n ∧ ε*(n:ℝ) ≤ ‖value n‖)
  have low : (E.card:ℝ)*(ε*(X:ℝ))^2 ≤ (X:ℝ)^(8/3+η:ℝ) := calc
    _ = ∑ _n ∈ E, (ε*(X:ℝ))^2 := by simp
    _ ≤ ∑ n ∈ E, ‖value n‖^2 := by
      apply sum_le_sum
      intro n hn
      obtain ⟨hs,_,h⟩ := mem_filter.mp hn
      apply pow_le_pow_left₀ (by positivity)
      exact (mul_le_mul_of_nonneg_left (by exact_mod_cast (mem_Icc.mp hs).1) hp.le).trans h
    _ ≤ ∑ n ∈ S, ‖value n‖^2 :=
      sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => sq_nonneg _)
    _ ≤ _ := hN X ((le_max_right 1 N).trans hX)
  have eq : (X:ℝ)^(8/3+η:ℝ) = (X:ℝ)^(2/3+η:ℝ)*(X:ℝ)^2 := by
    rw [←Real.rpow_natCast (X:ℝ) 2,←Real.rpow_add xp]; norm_num; ring_nf
  apply (le_div_iff₀ (sq_pos_of_pos hp)).mpr
  apply le_of_mul_le_mul_right _ (sq_pos_of_pos xp)
  rw [eq,mul_pow] at low
  simpa only [mul_assoc] using low

end
end GBMoving

theorem Conjectures.Goldbach.DeepPrimeMovingDiagonal :
let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let deepCoeff := fun (n m : ℕ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun u => (S n w u)^2 * E (-(m:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ X : ℕ, N ≤ X → (∑ n ∈ Finset.Icc X (2*X), ‖deepCoeff n n‖^2) ≤ (X:ℝ)^(8/3+η:ℝ) := by
  dsimp only
  intro η he
  obtain ⟨N,hN⟩ := GBMoving.moving_prime_moment η he
  refine ⟨N,fun X hX => ?_⟩
  simpa only [GBMoving.value,GBMoving.w,GoldbachTransitionSquare.fourierSum,GoldbachTransitionSquare.phase,GoldbachTransitionSquare.deep,GoldbachTransitionSquare.wide,GoldbachTransitionSquare.cutoffB,TypeTwoDiagonal.phase,TypeTwoDiagonal.coefficient,TypeTwoDiagonal.unitMeasure,intervalIntegral.integral_of_le zero_le_one] using hN X hX
