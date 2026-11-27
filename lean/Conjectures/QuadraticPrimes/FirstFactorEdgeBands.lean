import Mathlib

/-!
This proof uses the switched-cofactor estimate from YouhuaLi's verified PR #3911.
For an independent single-file replay, its Selberg sieve dependency and the estimate are
included here under the repository's Apache-2.0 license, with upstream notices retained.
The argument for the two bands follows those reused sections.
-/

namespace Conjectures.TwinPrimes.CofactorTwoLinearSieve_aux


/-!
The finite Goldbach Selberg sieve and smooth-number Euler product bounds below are adapted
from OpenAI, openai/math (Apache License 2.0), revision 3344da59991ed94f9ba711217b29c1d760badfa6.
https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/NumberTheory/EgyptianFractions
The modules are combined for verification with the pinned toolchain. The cutoff and denominator estimates are derived here.
-/

-- Upstream module OAI.NumberTheory.EgyptianFractions.SelbergOptimal

namespace OAI
noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius
open Finset ArithmeticFunction

namespace Problem337.SelbergOptimal

/-- Complementation turns a sum over multiples among divisors into a divisor sum. -/
theorem sum_multiples_complement (P l : ℕ) (hP : P ≠ 0) (hl : l ∣ P)
    (f : ℕ → ℝ) :
    (∑ d ∈ P.divisors, if l ∣ d then f (P / d) else 0) =
      ∑ d ∈ (P / l).divisors, f d := by
  calc
    _ = ∑ d ∈ P.divisors, if l ∣ P / d then f d else 0 := by
      rw [← Nat.sum_div_divisors P (fun d => if l ∣ d then f (P / d) else 0)]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hP]
    _ = ∑ d ∈ (P / l).divisors, f d := by
      rw [← Finset.sum_filter]
      congr 1
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hd, _⟩, hld⟩
        refine ⟨?_, Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) hl)
          (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP hl)))⟩
        apply (Nat.dvd_div_iff_mul_dvd hl).2
        rw [Nat.mul_comm]
        exact (Nat.dvd_div_iff_mul_dvd hd).1 hld
      · rintro ⟨hd, _⟩
        have hdP : d ∣ P := hd.trans (Nat.div_dvd_of_dvd hl)
        refine ⟨⟨hdP, hP⟩, ?_⟩
        apply (Nat.dvd_div_iff_mul_dvd hdP).2
        rw [Nat.mul_comm]
        exact (Nat.dvd_div_iff_mul_dvd hl).1 hd

/-- Inverse of the upper divisor-sum transform, expressed through ordinary
Möbius inversion after complementing divisors. -/
def upperInverse (P : ℕ) (y : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ x ∈ (P / d).divisorsAntidiagonal, (μ x.1 : ℝ) * y (P / x.2)

theorem sum_upperInverse (P l : ℕ) (hP : P ≠ 0) (hl : l ∣ P)
    (y : ℕ → ℝ) :
    (∑ d ∈ P.divisors, if l ∣ d then upperInverse P y d else 0) = y l := by
  let f : ℕ → ℝ := fun n =>
    ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℝ) * y (P / x.2)
  have hmob : ∀ n > 0, ∑ d ∈ n.divisors, f d = y (P / n) := by
    apply ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mpr
    intro n hn
    rfl
  change (∑ d ∈ P.divisors, if l ∣ d then f (P / d) else 0) = y l
  rw [sum_multiples_complement P l hP hl f]
  rw [hmob (P / l) (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) hl)
    (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP hl)))]
  rw [Nat.div_div_self hl hP]

theorem upperInverse_one (P : ℕ) (hP : P ≠ 0) (y : ℕ → ℝ) :
    upperInverse P y 1 = ∑ d ∈ P.divisors, (μ d : ℝ) * y d := by
  unfold upperInverse
  rw [Nat.div_one, Nat.sum_divisorsAntidiagonal (f := fun d e => (μ d : ℝ) * y (P / e))]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hP]

/-- The positive finite normalizing sum of the optimal Selberg weights. -/
def normalizer (s : BoundingSieve) (z : ℕ) : ℝ :=
  ∑ d ∈ s.prodPrimes.divisors, if d ≤ z then s.selbergTerms d else 0

theorem normalizer_pos (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    0 < normalizer s z := by
  apply Finset.sum_pos'
  · intro d hd
    split_ifs
    · exact (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hd)).le
    · exact le_rfl
  · refine ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, s.prodPrimes_ne_zero⟩, ?_⟩
    rw [ite_eq_left hz]
    exact s.selbergTerms_pos (one_dvd _)

/-- The diagonal coordinates attaining the constrained minimum. -/
def optimalDiagonal (s : BoundingSieve) (z d : ℕ) : ℝ :=
  if d ≤ z then (μ d : ℝ) * s.selbergTerms d / normalizer s z else 0

/-- Selberg weights obtained by upper Möbius inversion. -/
def optimalWeight (s : BoundingSieve) (z d : ℕ) : ℝ :=
  if d ∣ s.prodPrimes then
    upperInverse s.prodPrimes (optimalDiagonal s z) d / s.nu d else 0

theorem optimalWeight_transform (s : BoundingSieve) (z l : ℕ)
    (hl : l ∣ s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors,
      if l ∣ d then s.nu d * optimalWeight s z d else 0) =
      optimalDiagonal s z l := by
  calc
    _ = ∑ d ∈ s.prodPrimes.divisors,
        if l ∣ d then upperInverse s.prodPrimes (optimalDiagonal s z) d else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdP := Nat.dvd_of_mem_divisors hd
      rw [optimalWeight, ite_eq_left hdP]
      have hnu := s.nu_ne_zero hdP
      congr 1
      field_simp
    _ = _ := sum_upperInverse _ _ s.prodPrimes_ne_zero hl _

theorem optimalWeight_one (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    optimalWeight s z 1 = 1 := by
  rw [optimalWeight, ite_eq_left (one_dvd _), s.nu_mult.map_one, div_one,
    upperInverse_one _ s.prodPrimes_ne_zero]
  have hG : normalizer s z ≠ 0 := (normalizer_pos s hz).ne'
  calc
    _ = (∑ d ∈ s.prodPrimes.divisors,
        if d ≤ z then s.selbergTerms d else 0) / normalizer s z := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d hd
      have hmu : (μ d : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
          (s.squarefree_of_mem_divisors_prodPrimes hd)
      unfold optimalDiagonal
      split_ifs with he
      · rw [mul_div_assoc, ← mul_assoc, ← pow_two, hmu, one_mul]
      · simp
    _ = 1 := div_self hG

/-- The diagonalized main term at the optimal weights is exactly the
reciprocal of the finite Selberg normalizer. -/
theorem mainSum_optimalWeight (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    s.mainSum (BoundingSieve.lambdaSquared (optimalWeight s z)) =
      1 / normalizer s z := by
  rw [s.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  have hG : normalizer s z ≠ 0 := (normalizer_pos s hz).ne'
  calc
    _ = (∑ d ∈ s.prodPrimes.divisors,
        if d ≤ z then s.selbergTerms d else 0) / normalizer s z ^ 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d hd
      have hdP := Nat.dvd_of_mem_divisors hd
      have hg : s.selbergTerms d ≠ 0 := (s.selbergTerms_pos hdP).ne'
      have hmu : (μ d : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
          (s.squarefree_of_mem_divisors_prodPrimes hd)
      rw [optimalWeight_transform s z d hdP]
      unfold optimalDiagonal
      split_ifs with he
      · rw [div_pow, mul_pow, hmu, one_mul]
        field_simp
      · simp
    _ = 1 / normalizer s z := by
      change normalizer s z / normalizer s z ^ 2 = _
      field_simp

/-- The Selberg upper-bound sieve with its main term optimized. -/
theorem siftedSum_le (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    s.siftedSum ≤ s.totalMass / normalizer s z +
      s.errSum (BoundingSieve.lambdaSquared (optimalWeight s z)) := by
  have h := s.siftedSum_le_mainSum_errSum_of_upperMoebius
    (BoundingSieve.lambdaSquared (optimalWeight s z))
    (BoundingSieve.upperMoebius_lambdaSquared _ (optimalWeight_one s hz))
  rw [mainSum_optimalWeight s hz, mul_one_div] at h
  exact h

/-- No optimal weight lies above the chosen truncation. -/
theorem optimalWeight_eq_zero_of_lt (s : BoundingSieve) {z d : ℕ} (hzd : z < d) :
    optimalWeight s z d = 0 := by
  unfold optimalWeight
  split_ifs with hdP
  · suffices upperInverse s.prodPrimes (optimalDiagonal s z) d = 0 by rw [this, zero_div]
    unfold upperInverse
    apply Finset.sum_eq_zero
    intro x hx
    have hx2 : x.2 ∣ s.prodPrimes / d :=
      Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)
    have hxP : x.2 ∣ s.prodPrimes := hx2.trans (Nat.div_dvd_of_dvd hdP)
    have hdx : d ∣ s.prodPrimes / x.2 := by
      apply (Nat.dvd_div_iff_mul_dvd hxP).2
      rw [Nat.mul_comm]
      exact (Nat.dvd_div_iff_mul_dvd hdP).1 hx2
    have hpos : 0 < s.prodPrimes / x.2 :=
      Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero s.prodPrimes_ne_zero) hxP)
        (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hxP))
    have hlong : z < s.prodPrimes / x.2 := hzd.trans_le (Nat.le_of_dvd hpos hdx)
    simp [optimalDiagonal, not_le.mpr hlong]
  · rfl

/-- Upper Möbius inversion does not increase the crude full-divisor
absolute-mass bound. This estimate is independent of squarefreeness. -/
theorem abs_upperInverse_le (P d : ℕ) (hP : P ≠ 0) (hd : d ∣ P)
    (y : ℕ → ℝ) :
    |upperInverse P y d| ≤ ∑ e ∈ P.divisors, |y e| := by
  unfold upperInverse
  rw [Nat.sum_divisorsAntidiagonal' (f := fun a b => (μ a : ℝ) * y (P / b))]
  calc
    _ ≤ ∑ e ∈ (P / d).divisors, |(μ ((P / d) / e) : ℝ) * y (P / e)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ (P / d).divisors, |y (P / e)| := by
      apply Finset.sum_le_sum
      intro e he
      have hmu : |(μ ((P / d) / e) : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := (P / d) / e)
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_right hmu (abs_nonneg (y (P / e)))
    _ ≤ ∑ e ∈ P.divisors, |y (P / e)| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        exact Nat.mem_divisors.mpr
          ⟨(Nat.dvd_of_mem_divisors he).trans (Nat.div_dvd_of_dvd hd), hP⟩
      · intro e he hnot
        exact abs_nonneg _
    _ = _ := Nat.sum_div_divisors P (fun e => |y e|)

/-- The optimal diagonal coordinates have total absolute mass one. -/
theorem sum_abs_optimalDiagonal (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    (∑ d ∈ s.prodPrimes.divisors, |optimalDiagonal s z d|) = 1 := by
  have hG := normalizer_pos s hz
  calc
    _ = (∑ d ∈ s.prodPrimes.divisors,
        if d ≤ z then s.selbergTerms d else 0) / normalizer s z := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d hd
      have hg := s.selbergTerms_pos (Nat.dvd_of_mem_divisors hd)
      have hmu : |(μ d : ℝ)| = 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree
          (s.squarefree_of_mem_divisors_prodPrimes hd)
      unfold optimalDiagonal
      split_ifs
      · rw [abs_div, abs_mul, hmu, abs_of_pos hg, abs_of_pos hG, one_mul]
      · simp
    _ = 1 := div_self hG.ne'

/-- A coefficient bound adequate for polynomial-error applications of the sieve. -/
theorem abs_optimalWeight_le (s : BoundingSieve) {z d : ℕ} (hz : 1 ≤ z)
    (hd : d ∣ s.prodPrimes) :
    |optimalWeight s z d| ≤ (s.nu d)⁻¹ := by
  rw [optimalWeight, ite_eq_left hd, abs_div, abs_of_pos (s.nu_pos_of_dvd_prodPrimes hd)]
  have h := abs_upperInverse_le s.prodPrimes d s.prodPrimes_ne_zero hd
    (optimalDiagonal s z)
  rw [sum_abs_optimalDiagonal s hz] at h
  simpa only [one_div] using div_le_div_of_nonneg_right h
    (s.nu_pos_of_dvd_prodPrimes hd).le

/-- The upper inverse in the more usual sum-over-multiples form. -/
theorem upperInverse_eq_sum_multiples (P d : ℕ) (hP : P ≠ 0) (hd : d ∣ P)
    (y : ℕ → ℝ) :
    upperInverse P y d =
      ∑ e ∈ P.divisors, if d ∣ e then (μ (e / d) : ℝ) * y e else 0 := by
  unfold upperInverse
  rw [Nat.sum_divisorsAntidiagonal' (f := fun a b => (μ a : ℝ) * y (P / b)),
    ← sum_multiples_complement P d hP hd
      (fun e => (μ ((P / d) / e) : ℝ) * y (P / e))]
  apply Finset.sum_congr rfl
  intro e he
  have heP := Nat.dvd_of_mem_divisors he
  rw [Nat.div_div_self heP hP]
  split_ifs with hde
  · have hPe : 0 < P / e := Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) heP)
      (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP heP))
    have hquot : (P / d) / (P / e) = e / d := by
      rw [← Nat.div_mul_div heP hde, Nat.mul_comm, Nat.mul_div_cancel _ hPe]
    rw [hquot]
  · rfl

/-- Divisor multiples are parametrized by the complementary quotient. -/
theorem sum_multiples_eq (P d : ℕ) (hP : P ≠ 0) (hd : d ∣ P)
    (f : ℕ → ℝ) :
    (∑ e ∈ P.divisors, if d ∣ e then f e else 0) =
      ∑ t ∈ (P / d).divisors, f (d * t) := by
  calc
    _ = ∑ e ∈ P.divisors, if d ∣ e then f (P / (P / e)) else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      rw [Nat.div_div_self (Nat.dvd_of_mem_divisors he) hP]
    _ = ∑ t ∈ (P / d).divisors, f (P / t) :=
      sum_multiples_complement P d hP hd (fun t => f (P / t))
    _ = ∑ t ∈ (P / d).divisors, f (d * t) := by
      rw [← Nat.sum_div_divisors (P / d) (fun t => f (P / t))]
      apply Finset.sum_congr rfl
      intro t ht
      have htQ := Nat.dvd_of_mem_divisors ht
      have hQpos : 0 < P / d := Nat.div_pos
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) hd)
        (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP hd))
      have hQt : 0 < (P / d) / t := Nat.div_pos (Nat.le_of_dvd hQpos htQ)
        (Nat.pos_of_mem_divisors ht)
      have hprod : ((P / d) / t) * (d * t) = P := by
        calc
          _ = d * (((P / d) / t) * t) := by ring
          _ = d * (P / d) := by rw [Nat.div_mul_cancel htQ]
          _ = P := Nat.mul_div_cancel' hd
      congr 1
      conv_lhs => arg 1; rw [← hprod]
      exact Nat.mul_div_cancel_left (d * t) hQt

/-- The two Möbius signs from upper inversion collapse on squarefree divisors. -/
theorem moebius_div_mul (e d : ℕ) (he : Squarefree e) (hd : d ∣ e) :
    (μ (e / d) : ℝ) * (μ e : ℝ) = (μ d : ℝ) := by
  have hm : d * (e / d) = e := Nat.mul_div_cancel' hd
  have hcop : d.Coprime (e / d) := Nat.coprime_of_squarefree_mul (hm.symm ▸ he)
  have hmu := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  rw [hm] at hmu
  have heq : (μ e : ℝ) = (μ d : ℝ) * (μ (e / d) : ℝ) := by exact_mod_cast hmu
  have hsquare : (μ (e / d) : ℝ) ^ 2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
      (he.squarefree_of_dvd (Nat.div_dvd_of_dvd hd))
  rw [heq]
  calc
    _ = (μ d : ℝ) * (μ (e / d) : ℝ) ^ 2 := by ring
    _ = _ := by rw [hsquare, mul_one]

/-- The truncated normalizer on complementary divisors. -/
def complementNormalizer (s : BoundingSieve) (z d : ℕ) : ℝ :=
  ∑ t ∈ (s.prodPrimes / d).divisors, if t ≤ z / d then s.selbergTerms t else 0

/-- Explicit classical formula for the optimal coefficient. In particular,
the sign is the Möbius sign and the remaining factors are nonnegative. -/
theorem optimalWeight_formula (s : BoundingSieve) (z d : ℕ)
    (hd : d ∣ s.prodPrimes) :
    optimalWeight s z d = (μ d : ℝ) * s.selbergTerms d / s.nu d *
      (complementNormalizer s z d / normalizer s z) := by
  rw [optimalWeight, ite_eq_left hd,
    upperInverse_eq_sum_multiples _ _ s.prodPrimes_ne_zero hd]
  have hdpos : 0 < d := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hd)
  have hsum :
      (∑ e ∈ s.prodPrimes.divisors,
        if d ∣ e then (μ (e / d) : ℝ) * optimalDiagonal s z e else 0) =
      (μ d : ℝ) / normalizer s z *
        (s.selbergTerms d * complementNormalizer s z d) := by
    calc
      _ = (μ d : ℝ) / normalizer s z *
          (∑ e ∈ s.prodPrimes.divisors,
            if d ∣ e then (if e ≤ z then s.selbergTerms e else 0) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        by_cases hde : d ∣ e
        · rw [ite_eq_left hde, ite_eq_left hde]
          unfold optimalDiagonal
          split_ifs with hez
          · rw [mul_div_assoc, ← mul_assoc,
              moebius_div_mul e d (s.squarefree_of_mem_divisors_prodPrimes he) hde]
            ring
          · simp
        · simp [hde]
      _ = (μ d : ℝ) / normalizer s z *
          (∑ t ∈ (s.prodPrimes / d).divisors,
            if d * t ≤ z then s.selbergTerms (d * t) else 0) := by
        rw [sum_multiples_eq _ _ s.prodPrimes_ne_zero hd]
      _ = _ := by
        congr 1
        unfold complementNormalizer
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        have htQ := Nat.dvd_of_mem_divisors ht
        have hdt : d * t ∣ s.prodPrimes := by
          simpa [Nat.mul_comm] using (Nat.dvd_div_iff_mul_dvd hd).1 htQ
        have hcop : d.Coprime t := Nat.coprime_of_squarefree_mul
          (s.squarefree_of_dvd_prodPrimes hdt)
        have hiff : d * t ≤ z ↔ t ≤ z / d := by
          rw [Nat.le_div_iff_mul_le hdpos, Nat.mul_comm]
        simp only [hiff]
        split_ifs
        · exact s.selbergTerms_isMultiplicative.map_mul_of_coprime hcop
        · simp
  rw [hsum]
  ring

end Problem337.SelbergOptimal

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.SelbergWeightBound

namespace OAI
noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius
open Finset

namespace Problem337.SelbergOptimal

/-- Summation over the divisors of a coprime product has no multiplicities. -/
theorem sum_coprime_divisors {a b : ℕ} (hab : a.Coprime b) (f : ℕ → ℝ) :
    (∑ d ∈ (a * b).divisors, f d) =
      ∑ e ∈ a.divisors, ∑ t ∈ b.divisors, f (e * t) := by
  rw [hab.divisors_mul]
  simp only [sum_map]
  exact (sum_attach (a.divisors ×ˢ b.divisors)
    (fun p : ℕ × ℕ => f (p.1 * p.2))).trans (sum_product _ _ _)

/-- The complementary divisor of a squarefree integer is coprime to it. -/
theorem coprime_complement (s : BoundingSieve) {d : ℕ} (hd : d ∣ s.prodPrimes) :
    d.Coprime (s.prodPrimes / d) := by
  apply Nat.coprime_of_squarefree_mul
  simpa only [Nat.mul_div_cancel' hd] using s.prodPrimes_squarefree

/-- Split the finite Selberg normalizer at a divisor of the sieving product. -/
theorem normalizer_decompose (s : BoundingSieve) (z : ℕ) {d : ℕ}
    (hd : d ∣ s.prodPrimes) :
    normalizer s z =
      ∑ e ∈ d.divisors, ∑ t ∈ (s.prodPrimes / d).divisors,
        if e * t ≤ z then s.selbergTerms e * s.selbergTerms t else 0 := by
  have hcop := coprime_complement s hd
  unfold normalizer
  conv_lhs => rw [← Nat.mul_div_cancel' hd]
  rw [sum_coprime_divisors hcop]
  apply sum_congr rfl
  intro e he
  apply sum_congr rfl
  intro t ht
  rw [s.selbergTerms_isMultiplicative.map_mul_of_coprime
    (hcop.coprime_dvd_left (Nat.dvd_of_mem_divisors he) |>.coprime_dvd_right
      (Nat.dvd_of_mem_divisors ht))]

theorem sum_selbergTerms_divisors (s : BoundingSieve) {d : ℕ}
    (hd : d ∣ s.prodPrimes) :
    (∑ e ∈ d.divisors, s.selbergTerms e) = s.selbergTerms d / s.nu d := by
  have h := s.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hd
  rw [← sum_filter, Nat.divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero hd] at h
  simpa only [div_eq_mul_inv] using h

/-- The positive numerator of an optimal Selberg weight is a subsum of the
normalizer, after splitting into complementary divisor coordinates. -/
theorem truncated_complement_sum_le_normalizer (s : BoundingSieve) (z : ℕ)
    {d : ℕ} (hd : d ∣ s.prodPrimes) :
    (s.selbergTerms d / s.nu d) *
        (∑ t ∈ (s.prodPrimes / d).divisors,
          if d * t ≤ z then s.selbergTerms t else 0) ≤ normalizer s z := by
  rw [← sum_selbergTerms_divisors s hd, sum_mul,
    normalizer_decompose s z hd]
  apply sum_le_sum
  intro e he
  rw [mul_sum]
  apply sum_le_sum
  intro t ht
  have heP := (Nat.dvd_of_mem_divisors he).trans hd
  have htP := (Nat.dvd_of_mem_divisors ht).trans (Nat.div_dvd_of_dvd hd)
  have he0 := (s.selbergTerms_pos heP).le
  have ht0 := (s.selbergTerms_pos htP).le
  by_cases hdt : d * t ≤ z
  · have het : e * t ≤ z :=
      (Nat.mul_le_mul_right t (Nat.le_of_dvd
        (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hd))
        (Nat.dvd_of_mem_divisors he))).trans hdt
    simp only [ite_eq_left hdt, ite_eq_left het, le_refl]
  · simp only [ite_eq_right hdt, mul_zero]
    split_ifs <;> positivity

/-- The same bound in the quotient-cutoff form used in the explicit weights. -/
theorem truncated_div_sum_le_normalizer (s : BoundingSieve) (z : ℕ)
    {d : ℕ} (hd : d ∣ s.prodPrimes) :
    (s.selbergTerms d / s.nu d) *
        (∑ t ∈ (s.prodPrimes / d).divisors,
          if t ≤ z / d then s.selbergTerms t else 0) ≤ normalizer s z := by
  have hd0 : 0 < d :=
    Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hd)
  simpa only [Nat.le_div_iff_mul_le hd0, Nat.mul_comm] using
    truncated_complement_sum_le_normalizer s z hd

/-- The normalized explicit optimal-weight expression has absolute value at
most one. This bound is independent of the local sieve dimension. -/
theorem abs_normalized_complement_le_one (s : BoundingSieve) {z : ℕ}
    (hz : 1 ≤ z) {d : ℕ} (hd : d ∣ s.prodPrimes) :
    |(μ d : ℝ) * (s.selbergTerms d / s.nu d) /
        normalizer s z *
        (∑ t ∈ (s.prodPrimes / d).divisors,
          if t ≤ z / d then s.selbergTerms t else 0)| ≤ 1 := by
  have hG := normalizer_pos s hz
  have hnu := s.nu_pos_of_dvd_prodPrimes hd
  have hg := s.selbergTerms_pos hd
  have hsum : 0 ≤ ∑ t ∈ (s.prodPrimes / d).divisors,
      if t ≤ z / d then s.selbergTerms t else 0 := by
    apply sum_nonneg
    intro t ht
    split_ifs
    · exact (s.selbergTerms_pos ((Nat.dvd_of_mem_divisors ht).trans
        (Nat.div_dvd_of_dvd hd))).le
    · exact le_rfl
  have hmu : |(μ d : ℝ)| = 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree
      (s.squarefree_of_dvd_prodPrimes hd)
  rw [abs_mul, abs_div, abs_mul, hmu, one_mul,
    abs_of_pos (div_pos hg hnu), abs_of_pos hG, abs_of_nonneg hsum]
  rw [div_mul_eq_mul_div, div_le_one hG]
  exact truncated_div_sum_le_normalizer s z hd

end Problem337.SelbergOptimal

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.SelbergErrorBound

namespace OAI
/-!
# Remainder control for the Selberg square sieve

The estimates here retain the actual local remainder.  In particular no
prime distribution hypothesis is manufactured by passing to square weights.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace Problem337.SelbergError

/-- A weighted version of the divisor expansion of the square sieve. -/
theorem sum_lambdaSquared_mul (P : ℕ) (hP : P ≠ 0)
    (lam f : ℕ → ℝ) :
    (∑ d ∈ P.divisors, BoundingSieve.lambdaSquared lam d * f d) =
      ∑ a ∈ P.divisors, ∑ b ∈ P.divisors,
        lam a * lam b * f (Nat.lcm a b) := by
  have henlarge (g : ℕ → ℕ → ℕ → ℝ) :
      (∑ d ∈ P.divisors, ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
        if d = Nat.lcm a b then g a b d else 0) =
      ∑ d ∈ P.divisors, ∑ a ∈ P.divisors, ∑ b ∈ P.divisors,
        if d = Nat.lcm a b then g a b d else 0 := by
    congr! 1 with d hd
    rw [Nat.mem_divisors] at hd
    have heq : ∀ a b, (a ∣ d ∧ b ∣ d ∧ d = Nat.lcm a b) =
        (d = Nat.lcm a b) := by
      simp +contextual [← and_assoc, Nat.dvd_lcm_left, Nat.dvd_lcm_right]
    simp_rw [← Nat.divisors_filter_dvd_of_dvd hd.2 hd.1,
      sum_filter, ite_sum_zero, ← ite_and, heq]
  calc
    _ = ∑ d ∈ P.divisors, ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
        if d = Nat.lcm a b then lam a * lam b * f d else 0 := by
      simp [BoundingSieve.lambdaSquared, sum_mul]
    _ = ∑ d ∈ P.divisors, ∑ a ∈ P.divisors, ∑ b ∈ P.divisors,
        if d = Nat.lcm a b then lam a * lam b * f d else 0 := henlarge _
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro a ha
      rw [sum_comm]
      apply sum_congr rfl
      intro b hb
      have hlcm : Nat.lcm a b ∈ P.divisors :=
        Nat.mem_divisors.mpr ⟨Nat.lcm_dvd_iff.mpr
          ⟨Nat.dvd_of_mem_divisors ha, Nat.dvd_of_mem_divisors hb⟩, hP⟩
      rw [sum_ite_eq_of_mem' _ _ _ hlcm]

/-- Absolute square weights are dominated by the square weights of absolute
values.  This inequality does not assume that the original weights are positive. -/
theorem abs_lambdaSquared_le (lam : ℕ → ℝ) (d : ℕ) :
    |BoundingSieve.lambdaSquared lam d| ≤
      BoundingSieve.lambdaSquared (fun n => |lam n|) d := by
  unfold BoundingSieve.lambdaSquared
  calc
    _ ≤ ∑ a ∈ d.divisors, |∑ b ∈ d.divisors,
        if d = Nat.lcm a b then lam a * lam b else 0| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
        |if d = Nat.lcm a b then lam a * lam b else 0| := by
      apply sum_le_sum
      intro a ha
      exact abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_ite, abs_mul, abs_zero]

/-- Exact local remainders can be bounded before any uniform estimate is made. -/
theorem errSum_lambdaSquared_le (s : BoundingSieve) (lam : ℕ → ℝ) :
    s.errSum (BoundingSieve.lambdaSquared lam) ≤
      ∑ a ∈ s.prodPrimes.divisors, ∑ b ∈ s.prodPrimes.divisors,
        |lam a| * |lam b| * |s.rem (Nat.lcm a b)| := by
  calc
    _ ≤ ∑ d ∈ s.prodPrimes.divisors,
        BoundingSieve.lambdaSquared (fun n => |lam n|) d * |s.rem d| := by
      apply sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_right (abs_lambdaSquared_le lam d) (abs_nonneg _)
    _ = _ := sum_lambdaSquared_mul s.prodPrimes
      BoundingSieve.prodPrimes_ne_zero _ _

/-- A factorizable local remainder envelope gives the usual weighted L1-square
bound for the square-sieve error. -/
theorem errSum_lambdaSquared_le_sq (s : BoundingSieve) (lam w : ℕ → ℝ)
    (hrem : ∀ a ∈ s.prodPrimes.divisors, ∀ b ∈ s.prodPrimes.divisors,
      |s.rem (Nat.lcm a b)| ≤ w a * w b) :
    s.errSum (BoundingSieve.lambdaSquared lam) ≤
      (∑ d ∈ s.prodPrimes.divisors, |lam d| * w d) ^ 2 := by
  calc
    _ ≤ ∑ a ∈ s.prodPrimes.divisors, ∑ b ∈ s.prodPrimes.divisors,
        |lam a| * |lam b| * |s.rem (Nat.lcm a b)| := errSum_lambdaSquared_le s lam
    _ ≤ ∑ a ∈ s.prodPrimes.divisors, ∑ b ∈ s.prodPrimes.divisors,
        |lam a| * |lam b| * (w a * w b) := by
      apply sum_le_sum
      intro a ha
      apply sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (hrem a ha b hb) (by positivity)
    _ = _ := by
      rw [sq, sum_mul_sum]
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      ring

end Problem337.SelbergError

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.DivisorTupleBounds

namespace OAI
/-!
# Elementary summatory bounds for divisor tuples

These finite hyperbola estimates supply logarithmic remainder bounds for
square sieves.  They do not use a prime number theorem.
-/
noncomputable section
open scoped BigOperators
open Finset

namespace Problem337.SelbergError

/-- Ordered positive factor tuples, expressed by Dirichlet powers of zeta. -/
def divisorTupleCount (k n : ℕ) : ℕ :=
  (ArithmeticFunction.zeta ^ k) n

private lemma sum_divisorsAntidiagonal_le_rectangle (N : ℕ)
    (F : ℕ × ℕ → ℝ) (hF : ∀ x, 0 ≤ F x) :
    (∑ n ∈ Icc 1 N, ∑ x ∈ n.divisorsAntidiagonal, F x) ≤
      ∑ x ∈ Icc 1 N ×ˢ Icc 1 N, F x := by
  have hdisj : Set.PairwiseDisjoint (Icc 1 N : Finset ℕ)
      Nat.divisorsAntidiagonal := by
    intro n hn m hm hnm
    apply disjoint_left.mpr
    intro x hxn hxm
    exact hnm ((Nat.mem_divisorsAntidiagonal.mp hxn).1.symm.trans
      (Nat.mem_divisorsAntidiagonal.mp hxm).1)
  rw [← sum_biUnion hdisj]
  apply sum_le_sum_of_subset_of_nonneg
  · intro x hx
    obtain ⟨n, hn, hxn⟩ := mem_biUnion.mp hx
    obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hxn
    have ha : 0 < x.1 := by
      by_contra h
      have : x.1 = 0 := by omega
      simp [this] at hprod
      omega
    have hb : 0 < x.2 := by
      by_contra h
      have : x.2 = 0 := by omega
      simp [this] at hprod
      omega
    have haN : x.1 ≤ N := (Nat.le_of_dvd (by omega : 0 < n)
      ⟨x.2, hprod.symm⟩).trans (mem_Icc.mp hn).2
    have hbN : x.2 ≤ N := (Nat.le_of_dvd (by omega : 0 < n)
      ⟨x.1, by simpa [Nat.mul_comm] using hprod.symm⟩).trans (mem_Icc.mp hn).2
    exact mem_product.mpr ⟨mem_Icc.mpr ⟨ha, haN⟩, mem_Icc.mpr ⟨hb, hbN⟩⟩
  · intro x hx hxnot
    exact hF x

/-- The harmonic norm on an initial interval is submultiplicative for
Dirichlet convolution of nonnegative arithmetic functions. -/
theorem harmonic_convolution_le (f g : ArithmeticFunction ℕ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ((f * g) n : ℝ) / n) ≤
      (∑ a ∈ Icc 1 N, (f a : ℝ) / a) *
      (∑ b ∈ Icc 1 N, (g b : ℝ) / b) := by
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ x ∈ n.divisorsAntidiagonal,
        ((f x.1 : ℝ) / x.1) * ((g x.2 : ℝ) / x.2) := by
      apply sum_congr rfl
      intro n hn
      rw [ArithmeticFunction.mul_apply, Nat.cast_sum, sum_div]
      apply sum_congr rfl
      intro x hx
      have hp := (Nat.mem_divisorsAntidiagonal.mp hx).1
      rw [Nat.cast_mul, ← hp, Nat.cast_mul]
      ring
    _ ≤ ∑ x ∈ Icc 1 N ×ˢ Icc 1 N,
        ((f x.1 : ℝ) / x.1) * ((g x.2 : ℝ) / x.2) :=
      sum_divisorsAntidiagonal_le_rectangle N _ (by intro x; positivity)
    _ = _ := by rw [sum_product, sum_mul_sum]

lemma zeta_harmonic_sum (N : ℕ) :
    (∑ n ∈ Icc 1 N, (ArithmeticFunction.zeta n : ℝ) / n) =
      (harmonic N : ℝ) := by
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  apply sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
  simp [ArithmeticFunction.zeta_apply_ne hn0]

/-- The harmonic sum over ordered `k`-factor tuples has at most the expected
`k` logarithmic factors. -/
theorem divisorTuple_harmonic_le (k N : ℕ) :
    (∑ n ∈ Icc 1 N, (divisorTupleCount k n : ℝ) / n) ≤
      (harmonic N : ℝ) ^ k := by
  induction k with
  | zero =>
    simp only [divisorTupleCount, pow_zero, ArithmeticFunction.one_apply]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_div, zero_div]
    by_cases hN : 1 ≤ N
    · simp [hN]
    · have : N = 0 := by omega
      simp [this]
  | succ k ih =>
    have h := harmonic_convolution_le (ArithmeticFunction.zeta ^ k)
      ArithmeticFunction.zeta N
    rw [zeta_harmonic_sum] at h
    calc
      _ ≤ (∑ n ∈ Icc 1 N, (divisorTupleCount k n : ℝ) / n) *
          (harmonic N : ℝ) := by simpa [divisorTupleCount, pow_succ] using h
      _ ≤ (harmonic N : ℝ) ^ k * (harmonic N : ℝ) :=
        mul_le_mul_of_nonneg_right ih (by rw [harmonic, Rat.cast_sum]; positivity)
      _ = _ := (pow_succ _ _).symm

/-- A uniform summatory bound, with one harmless extra logarithmic factor.
It holds also at `N = 0` and requires no squarefreeness restriction. -/
theorem divisorTuple_sum_le (k N : ℕ) :
    (∑ n ∈ Icc 1 N, (divisorTupleCount k n : ℝ)) ≤
      (N : ℝ) * (harmonic N : ℝ) ^ k := by
  calc
    _ ≤ ∑ n ∈ Icc 1 N, (N : ℝ) * ((divisorTupleCount k n : ℝ) / n) := by
      apply sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
      rw [← mul_div_assoc, le_div_iff₀ hn0]
      nlinarith [show (0 : ℝ) ≤ divisorTupleCount k n by positivity]
    _ = (N : ℝ) * ∑ n ∈ Icc 1 N, (divisorTupleCount k n : ℝ) / n :=
      (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (divisorTuple_harmonic_le k N) (by positivity)

/-- At a prime, there are exactly `k` ordered `k`-factor tuples. -/
theorem divisorTupleCount_prime (k p : ℕ) (hp : p.Prime) :
    divisorTupleCount k p = k := by
  induction k with
  | zero => simp [divisorTupleCount, hp.ne_one]
  | succ k ih =>
    have h1 : (ArithmeticFunction.zeta ^ k) 1 = 1 :=
      ArithmeticFunction.isMultiplicative_zeta.pow.1
    change (ArithmeticFunction.zeta ^ (k + 1)) p = k + 1
    rw [pow_succ, ArithmeticFunction.mul_zeta_apply, hp.divisors]
    change (ArithmeticFunction.zeta ^ k) p = k at ih
    simp [hp.ne_one.symm, h1, ih, Nat.add_comm]

/-- A squarefree number has one independent choice among `k` tuple positions
for every prime factor. -/
theorem divisorTupleCount_squarefree (k n : ℕ) (hn : Squarefree n) :
    divisorTupleCount k n = k ^ n.primeFactors.card := by
  have hmult := (ArithmeticFunction.isMultiplicative_zeta.pow
    (k := k)).prod_primeFactors hn
  change (ArithmeticFunction.zeta ^ k) n = _
  rw [← hmult]
  calc
    _ = ∏ p ∈ n.primeFactors, k := by
      apply prod_congr rfl
      intro p hp
      exact divisorTupleCount_prime k p (Nat.prime_of_mem_primeFactors hp)
    _ = _ := by simp

/-- Explicit elementary logarithmic summatory majorant. -/
theorem divisorTuple_sum_le_log (k N : ℕ) :
    (∑ n ∈ Icc 1 N, (divisorTupleCount k n : ℝ)) ≤
      (N : ℝ) * (1 + Real.log N) ^ k := by
  refine (divisorTuple_sum_le k N).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ (by rw [harmonic, Rat.cast_sum]; positivity)
    (harmonic_le_one_add_log N) k

/-- A finite squarefree support has a power-of-prime-count sum bounded by
an elementary divisor-tuple sum. -/
theorem sum_squarefree_pow_le (S : Finset ℕ) (k N : ℕ)
    (hS : ∀ n ∈ S, Squarefree n) (hSN : S ⊆ Icc 1 N) :
    (∑ n ∈ S, (k : ℝ) ^ n.primeFactors.card) ≤
      (N : ℝ) * (1 + Real.log N) ^ k := by
  calc
    _ = ∑ n ∈ S, (divisorTupleCount k n : ℝ) := by
      apply sum_congr rfl
      intro n hn
      rw [divisorTupleCount_squarefree k n (hS n hn), Nat.cast_pow]
    _ ≤ ∑ n ∈ Icc 1 N, (divisorTupleCount k n : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hSN (by intros; positivity)
    _ ≤ _ := divisorTuple_sum_le_log k N

end Problem337.SelbergError

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.OptimizedSelbergError

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset

namespace Problem337.SelbergOptimal

/-- The actual optimal weights have a logarithmically bounded weighted mass.
This uses the sharp coefficient bound, not the crude inverse-density estimate. -/
theorem optimalWeight_primeFactor_mass_le (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    (∑ d ∈ s.prodPrimes.divisors, |optimalWeight s z d| *
      (2 : ℝ) ^ d.primeFactors.card) ≤ (z : ℝ) * (1 + Real.log z) ^ 2 := by
  calc
    _ ≤ ∑ d ∈ s.prodPrimes.divisors,
        if d ≤ z then (2 : ℝ) ^ d.primeFactors.card else 0 := by
      apply sum_le_sum
      intro d hd
      by_cases hdz : d ≤ z
      · rw [ite_eq_left hdz]
        have hw : |optimalWeight s z d| ≤ 1 := by
          rw [optimalWeight_formula s z d (Nat.dvd_of_mem_divisors hd)]
          convert abs_normalized_complement_le_one s hz (Nat.dvd_of_mem_divisors hd) using 1
          unfold complementNormalizer
          congr 1
          ring
        simpa using mul_le_mul_of_nonneg_right hw
          (by positivity : 0 ≤ (2 : ℝ) ^ d.primeFactors.card)
      · rw [ite_eq_right hdz, optimalWeight_eq_zero_of_lt s (lt_of_not_ge hdz)]
        simp
    _ = ∑ d ∈ s.prodPrimes.divisors.filter (fun d => d ≤ z),
        (2 : ℝ) ^ d.primeFactors.card := (sum_filter _ _).symm
    _ ≤ _ := SelbergError.sum_squarefree_pow_le _ 2 z
      (fun d hd => s.squarefree_of_mem_divisors_prodPrimes (mem_filter.mp hd).1)
      (by
        intro d hd
        obtain ⟨hdP, hdz⟩ := mem_filter.mp hd
        exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdP, hdz⟩)

/-- A dimension-two local remainder envelope gives an explicit logarithmic
error for the constructed optimal Selberg weights. -/
theorem errSum_optimalWeight_le_log (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z)
    (hrem : ∀ a ∈ s.prodPrimes.divisors, ∀ b ∈ s.prodPrimes.divisors,
      |s.rem (Nat.lcm a b)| ≤
        (2 : ℝ) ^ a.primeFactors.card * (2 : ℝ) ^ b.primeFactors.card) :
    s.errSum (BoundingSieve.lambdaSquared (optimalWeight s z)) ≤
      (z : ℝ) ^ 2 * (1 + Real.log z) ^ 4 := by
  calc
    _ ≤ (∑ d ∈ s.prodPrimes.divisors, |optimalWeight s z d| *
        (2 : ℝ) ^ d.primeFactors.card) ^ 2 :=
      SelbergError.errSum_lambdaSquared_le_sq s (optimalWeight s z)
        (fun d => (2 : ℝ) ^ d.primeFactors.card) hrem
    _ ≤ ((z : ℝ) * (1 + Real.log z) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (sum_nonneg (by intros; positivity))
        (optimalWeight_primeFactor_mass_le s hz) 2
    _ = _ := by ring

/-- Fully optimized finite Selberg inequality with explicit logarithmic error. -/
theorem siftedSum_le_log_error (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z)
    (hrem : ∀ a ∈ s.prodPrimes.divisors, ∀ b ∈ s.prodPrimes.divisors,
      |s.rem (Nat.lcm a b)| ≤
        (2 : ℝ) ^ a.primeFactors.card * (2 : ℝ) ^ b.primeFactors.card) :
    s.siftedSum ≤ s.totalMass / normalizer s z +
      (z : ℝ) ^ 2 * (1 + Real.log z) ^ 4 :=
  (siftedSum_le s hz).trans
    (add_le_add le_rfl (errSum_optimalWeight_le_log s hz hrem))

end Problem337.SelbergOptimal

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.GoldbachSieveLocal

namespace OAI
/-!
Finite local arithmetic for a possible binary Goldbach sieve.  These results
count roots of the polynomial `x * (u - x)` and provide its multiplicative local
density.  They do not assert any prime-pair bound or positive density of Goldbach
numbers.
-/

noncomputable section

open scoped BigOperators

namespace Problem337

/-- Residue classes removed by the binary Goldbach sieve. -/
def GoldbachSieveRoot (u d : ℕ) :=
  {x : ZMod d // x * ((u : ZMod d) - x) = 0}

/-- Local number of roots of `x * (u - x)` modulo `d`. -/
def goldbachSieveRootCount (u d : ℕ) : ℕ :=
  Nat.card (GoldbachSieveRoot u d)

/-- The Chinese remainder theorem separates the local root conditions. -/
def goldbachSieveRootEquiv (u a b : ℕ) (hab : a.Coprime b) :
    GoldbachSieveRoot u (a * b) ≃
      GoldbachSieveRoot u a × GoldbachSieveRoot u b := by
  let e := ZMod.chineseRemainder hab
  apply (Equiv.subtypeEquiv e.toEquiv ?_).trans Equiv.subtypeProdEquivProd
  intro x
  change x * ((u : ZMod (a * b)) - x) = 0 ↔
    (e x).1 * ((u : ZMod a) - (e x).1) = 0 ∧
      (e x).2 * ((u : ZMod b) - (e x).2) = 0
  have h := e.injective.eq_iff (a := x * ((u : ZMod (a * b)) - x)) (b := 0)
  simpa only [map_mul, map_sub, map_natCast, map_zero, Prod.mk_zero_zero,
    Prod.mul_def, Prod.sub_def, Prod.fst_natCast, Prod.snd_natCast,
    Prod.mk.injEq, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] using h.symm

/-- Root counts are multiplicative at coprime moduli, with no distribution hypothesis. -/
theorem goldbachSieveRootCount_mul (u a b : ℕ) (hab : a.Coprime b) :
    goldbachSieveRootCount u (a * b) =
      goldbachSieveRootCount u a * goldbachSieveRootCount u b := by
  unfold goldbachSieveRootCount
  rw [Nat.card_congr (goldbachSieveRootEquiv u a b hab), Nat.card_prod]

@[simp] theorem goldbachSieveRootCount_one (u : ℕ) :
    goldbachSieveRootCount u 1 = 1 := by
  unfold goldbachSieveRootCount GoldbachSieveRoot
  have e : {x : ZMod 1 // x * ((u : ZMod 1) - x) = 0} ≃ ZMod 1 :=
    Equiv.subtypeUnivEquiv (fun x => Subsingleton.elim _ _)
  rw [Nat.card_congr e, Nat.card_zmod]

/-- At a prime, the only roots are zero and the target residue. -/
theorem goldbachSieveRootCount_prime (u p : ℕ) (hp : p.Prime) :
    goldbachSieveRootCount u p = if p ∣ u then 1 else 2 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hroots : (Finset.univ.filter
      (fun x : ZMod p => x * ((u : ZMod p) - x) = 0)) = {0, (u : ZMod p)} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      mul_eq_zero, sub_eq_zero, Finset.mem_insert, Finset.mem_singleton]
    tauto
  unfold goldbachSieveRootCount GoldbachSieveRoot
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hroots]
  by_cases h : p ∣ u
  · simp [h, (ZMod.natCast_eq_zero_iff u p).mpr h]
  · have hne : (u : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff u p).not.mpr h
    simp [h, Ne.symm hne]

/-- A finite product of distinct primes gives the product of the local counts. -/
theorem goldbachSieveRootCount_prod_primes (u : ℕ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    goldbachSieveRootCount u (∏ p ∈ s, p) =
      ∏ p ∈ s, goldbachSieveRootCount u p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      have hpp := hs p (Finset.mem_insert_self p s)
      have hsp : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
      have hcop : p.Coprime (∏ q ∈ s, q) := by
        apply Nat.Coprime.prod_right
        intro q hq
        apply (Nat.coprime_primes hpp (hsp q hq)).mpr
        intro heq
        exact hp (heq ▸ hq)
      rw [Finset.prod_insert hp, goldbachSieveRootCount_mul u p _ hcop,
        ih hsp, Finset.prod_insert hp]

/-- Exact squarefree local factor for the binary Goldbach sieve. -/
theorem goldbachSieveRootCount_squarefree (u d : ℕ) (hd : Squarefree d) :
    goldbachSieveRootCount u d =
      ∏ p ∈ d.primeFactors, if p ∣ u then 1 else 2 := by
  calc
    goldbachSieveRootCount u d =
        goldbachSieveRootCount u (∏ p ∈ d.primeFactors, p) := by
          rw [Nat.prod_primeFactors_of_squarefree hd]
    _ = ∏ p ∈ d.primeFactors, goldbachSieveRootCount u p :=
      goldbachSieveRootCount_prod_primes u d.primeFactors
        (fun p hp => (Nat.mem_primeFactors.mp hp).1)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      exact goldbachSieveRootCount_prime u p (Nat.mem_primeFactors.mp hp).1

/-- The exact finite local root density, normalized as an arithmetic function. -/
def goldbachSieveDensity (u : ℕ) : ArithmeticFunction ℝ where
  toFun d := (goldbachSieveRootCount u d : ℝ) / (d : ℝ)
  map_zero' := by simp

@[simp] theorem goldbachSieveDensity_apply (u d : ℕ) :
    goldbachSieveDensity u d = (goldbachSieveRootCount u d : ℝ) / (d : ℝ) := rfl

/-- The finite local density has exactly the multiplicativity required by a sieve. -/
theorem goldbachSieveDensity_isMultiplicative (u : ℕ) :
    (goldbachSieveDensity u).IsMultiplicative := by
  constructor
  · simp
  · intro a b hab
    simp only [goldbachSieveDensity_apply, goldbachSieveRootCount_mul u a b hab,
      Nat.cast_mul, mul_div_mul_comm]

/-- The local density at a prime is `1/p` or `2/p`. -/
theorem goldbachSieveDensity_prime (u p : ℕ) (hp : p.Prime) :
    goldbachSieveDensity u p = if p ∣ u then 1 / (p : ℝ) else 2 / (p : ℝ) := by
  rw [goldbachSieveDensity_apply, goldbachSieveRootCount_prime u p hp]
  split_ifs <;> norm_num

/-- All prime local root densities are positive. -/
theorem goldbachSieveDensity_prime_pos (u p : ℕ) (hp : p.Prime) :
    0 < goldbachSieveDensity u p := by
  rw [goldbachSieveDensity_prime u p hp]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  split_ifs <;> positivity

/-- At odd primes the sieve is nondegenerate. At two, this requires an even target. -/
theorem goldbachSieveDensity_prime_lt_one (u p : ℕ) (hp : p.Prime)
    (hparity : p = 2 → 2 ∣ u) : goldbachSieveDensity u p < 1 := by
  rw [goldbachSieveDensity_prime u p hp]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  split_ifs with h
  · rw [div_lt_one hpR]
    exact_mod_cast hp.one_lt
  · have hp2 : 2 < p := by
      have := hp.two_le
      by_contra hnot
      have heq : p = 2 := by omega
      exact h (heq ▸ hparity heq)
    rw [div_lt_one hpR]
    exact_mod_cast hp2

end Problem337

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.ResidueIntervalCount

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- The exact number of natural numbers below `N` in one residue class. -/
theorem card_range_zmod_eq {d : ℕ} [NeZero d] (N : ℕ) (r : ZMod d) :
    ((Finset.range N).filter (fun n : ℕ => (n : ZMod d) = r)).card =
      N / d + if r.val < N % d then 1 else 0 := by
  have hd : 0 < d := NeZero.pos d
  have he : (Finset.range N).filter (fun n : ℕ => (n : ZMod d) = r) =
      (Finset.range N).filter (fun n => Nat.ModEq d n r.val) := by
    apply Finset.filter_congr
    intro n hn
    simpa only [ZMod.natCast_zmod_val] using
      (ZMod.natCast_eq_natCast_iff n r.val d)
  rw [he, ← Nat.count_eq_card_filter_range,
    Nat.count_modEq_card N hd r.val, Nat.mod_eq_of_lt r.val_lt]

/-- Exact quotient/remainder decomposition for any collection of residues. -/
theorem card_range_zmod_mem {d : ℕ} [NeZero d] (N : ℕ) (S : Finset (ZMod d)) :
    ((Finset.range N).filter (fun n : ℕ => (n : ZMod d) ∈ S)).card =
      (N / d) * S.card + (S.filter (fun r => r.val < N % d)).card := by
  classical
  rw [← Finset.sum_card_fiberwise_eq_card_filter (Finset.range N) S
    (fun n : ℕ => (n : ZMod d))]
  simp_rw [card_range_zmod_eq]
  rw [Finset.sum_add_distrib]
  simp [mul_comm]

/-- The elementary progression-counting error is at most the number of
residue classes, uniformly in the interval length and modulus. -/
theorem abs_card_range_zmod_mem_sub {d : ℕ} [NeZero d]
    (N : ℕ) (S : Finset (ZMod d)) :
    |(((Finset.range N).filter (fun n : ℕ => (n : ZMod d) ∈ S)).card : ℝ) -
      (N : ℝ) * S.card / d| ≤ (S.card : ℝ) := by
  classical
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hr : ((N % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt N (NeZero.pos d)
  have hq : (N : ℝ) = (N / d : ℕ) * (d : ℝ) + (N % d : ℕ) := by
    exact_mod_cast (show N = (N / d) * d + N % d by
      simpa only [Nat.mul_comm] using (Nat.div_add_mod N d).symm)
  have hs : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have ht : (0 : ℝ) ≤ (S.filter (fun r => r.val < N % d)).card := Nat.cast_nonneg _
  have hts : ((S.filter (fun r => r.val < N % d)).card : ℝ) ≤ S.card := by
    exact_mod_cast Finset.card_filter_le S (fun r => r.val < N % d)
  have hfrac0 : (0 : ℝ) ≤ (N % d : ℕ) / d := by positivity
  have hfrac1 : ((N % d : ℕ) : ℝ) / d ≤ 1 := (div_le_one hd).2 hr.le
  have hmain : (N : ℝ) * S.card / d =
      (N / d : ℕ) * (S.card : ℝ) + ((N % d : ℕ) : ℝ) / d * S.card := by
    rw [hq]
    field_simp
  rw [card_range_zmod_mem, Nat.cast_add, Nat.cast_mul, hmain]
  rw [abs_le]
  constructor <;> nlinarith

end Problem337

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.PeriodicResidueCount

namespace OAI
noncomputable section

namespace Problem337

/-- A periodic predicate has one full period's worth of solutions in each block. -/
theorem periodic_count_mul {p : ℕ → Prop} [DecidablePred p] {d : ℕ}
    (hp : Function.Periodic p d) (q : ℕ) :
    Nat.count p (q * d) = q * Nat.count p d := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, Nat.count_add']
    have hshift : (fun k => p (k + d)) = p := by
      funext k
      exact hp k
    simp only [hshift, ih]
    ring

/-- Exact quotient-and-remainder formula for a periodic counting function. -/
theorem periodic_count_div_mod {p : ℕ → Prop} [DecidablePred p] {d : ℕ}
    (hp : Function.Periodic p d) (N : ℕ) :
    Nat.count p N = (N / d) * Nat.count p d + Nat.count p (N % d) := by
  conv_lhs => rw [← Nat.mod_add_div N d]
  rw [Nat.count_add']
  have hshift : (fun k => p (k + d * (N / d))) = p := by
    funext k
    simpa [Nat.mul_comm] using hp.nsmul (N / d) k
  simp only [hshift]
  rw [Nat.mul_comm d, periodic_count_mul hp]
  omega

/-- The count on an initial interval differs from its periodic mean by at most the number
of allowed residues in one period. This bound is uniform in the length of the interval. -/
theorem periodic_count_discrepancy {p : ℕ → Prop} [DecidablePred p] {d : ℕ}
    (hd : 0 < d) (hp : Function.Periodic p d) (N : ℕ) :
    |(Nat.count p N : ℝ) - (N : ℝ) * Nat.count p d / d| ≤ Nat.count p d := by
  have hcount := periodic_count_div_mod hp N
  have hrem := Nat.count_monotone p (Nat.mod_lt N hd).le
  have hdiv := Nat.mod_add_div N d
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hremR : (Nat.count p (N % d) : ℝ) ≤ Nat.count p d := by exact_mod_cast hrem
  have hmodR : ((N % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt N hd).le
  have hdivR : ((N % d : ℕ) : ℝ) + (d : ℝ) * (N / d : ℕ) = N := by exact_mod_cast hdiv
  have hcountR : (Nat.count p N : ℝ) =
      (N / d : ℕ) * (Nat.count p d : ℝ) + Nat.count p (N % d) := by exact_mod_cast hcount
  have hnonneg : (0 : ℝ) ≤ Nat.count p d := by positivity
  have hterm0 : 0 ≤ ((N % d : ℕ) : ℝ) * Nat.count p d / d := by positivity
  have hterm : ((N % d : ℕ) : ℝ) * Nat.count p d / d ≤ Nat.count p d := by
    apply (div_le_iff₀ hdR).2
    nlinarith [mul_le_mul_of_nonneg_right hmodR hnonneg]
  have heq : (Nat.count p N : ℝ) - (N : ℝ) * Nat.count p d / d =
      Nat.count p (N % d) - ((N % d : ℕ) : ℝ) * Nat.count p d / d := by
    rw [hcountR, ← hdivR]
    field_simp
    ring
  rw [heq, abs_le]
  constructor <;> linarith [show (0 : ℝ) ≤ Nat.count p (N % d) by positivity]

/-- Shifting a periodic predicate does not change its mass over a full period. -/
theorem periodic_count_shift_period {p : ℕ → Prop} [DecidablePred p] {d : ℕ}
    (hp : Function.Periodic p d) (a : ℕ) :
    Nat.count (fun n => p (a + n)) d = Nat.count p d := by
  have h₁ := Nat.count_add p a d
  have h₂ := Nat.count_add' p a d
  have hshift : (fun n => p (n + d)) = p := funext hp
  simp only [hshift] at h₂
  omega

/-- Counting a predicate on a shifted natural interval is the same as counting
its translate on an initial interval. -/
theorem filter_Ico_card_eq_count_shift (p : ℕ → Prop) [DecidablePred p]
    (a N : ℕ) :
    ((Finset.Ico a (a + N)).filter p).card =
      Nat.count (fun n => p (a + n)) N := by
  rw [Nat.count_eq_card_filter_range, ← Nat.Ico_zero_eq_range]
  have hmap := Finset.map_add_left_Ico 0 N a
  rw [Nat.add_zero] at hmap
  rw [← hmap, Finset.filter_map, Finset.card_map]
  rfl

/-- Sharp periodic discrepancy on any shifted interval: the error is bounded
by one period's mass, independent of both endpoints. -/
theorem periodic_Ico_count_discrepancy {p : ℕ → Prop} [DecidablePred p] {d : ℕ}
    (hd : 0 < d) (hp : Function.Periodic p d) (a N : ℕ) :
    |(((Finset.Ico a (a + N)).filter p).card : ℝ) -
      (N : ℝ) * Nat.count p d / d| ≤ Nat.count p d := by
  have hshift : Function.Periodic (fun n => p (a + n)) d := by
    intro n
    simpa only [Nat.add_assoc] using hp (a + n)
  have h := periodic_count_discrepancy hd hshift N
  rw [periodic_count_shift_period hp a] at h
  simpa only [filter_Ico_card_eq_count_shift] using h

/-- The periodic mass of a predicate on residue classes is its finite cardinality. -/
theorem zmod_predicate_period_count (d : ℕ) [NeZero d]
    (P : ZMod d → Prop) [DecidablePred P] :
    Nat.count (fun n : ℕ => P (n : ZMod d)) d =
      (Finset.univ.filter P).card := by
  classical
  simpa [Nat.count_eq_card_filter_range, Nat.div_self (NeZero.pos d)] using
    (card_range_zmod_mem d (Finset.univ.filter P))

/-- Residue classes are equidistributed up to one copy of the allowed set on
any natural interval, without a primality or coprimality assumption. -/
theorem zmod_predicate_Ico_discrepancy (d : ℕ) [NeZero d]
    (P : ZMod d → Prop) [DecidablePred P] (a N : ℕ) :
    |(((Finset.Ico a (a + N)).filter (fun n : ℕ => P (n : ZMod d))).card : ℝ) -
      (N : ℝ) * (Finset.univ.filter P).card / d| ≤ (Finset.univ.filter P).card := by
  have hp : Function.Periodic (fun n : ℕ => P (n : ZMod d)) d := by
    intro n
    simp
  have h := periodic_Ico_count_discrepancy (NeZero.pos d) hp a N
  simpa only [zmod_predicate_period_count d P] using h

end Problem337

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.GoldbachSieveRemainder

namespace OAI
/-!
The exact finite progression error for the binary Goldbach polynomial. No
prime-distribution estimate or sieve-density lower bound is assumed here.
-/

noncomputable section

namespace Problem337

/-- The local root-count definition is the cardinality of the corresponding
finite set whenever the modulus is nonzero. -/
theorem goldbachSieveRootCount_eq_filter_card (u d : ℕ) [NeZero d] :
    goldbachSieveRootCount u d =
      (Finset.univ.filter (fun x : ZMod d => x * ((u : ZMod d) - x) = 0)).card := by
  classical
  unfold goldbachSieveRootCount GoldbachSieveRoot
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- On the natural interval used for ordered positive prime pairs, the
truncated natural subtraction agrees with subtraction in the residue ring. -/
theorem goldbach_polynomial_dvd_iff_zmod (u d n : ℕ) (hn : n ≤ u) :
    d ∣ n * (u - n) ↔
      (n : ZMod d) * ((u : ZMod d) - (n : ZMod d)) = 0 := by
  rw [← Nat.cast_sub hn, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]

/-- Sharp, uniform error for counting divisibility of `n*(u-n)` on `1 ≤ n < u`.
The formulation includes the empty intervals at `u=0` and `u=1`. -/
theorem goldbach_polynomial_count_discrepancy (u d : ℕ) [NeZero d] :
    |(((Finset.Icc 1 (u - 1)).filter (fun n => d ∣ n * (u - n))).card : ℝ) -
      ((u - 1 : ℕ) : ℝ) * goldbachSieveRootCount u d / d| ≤
        goldbachSieveRootCount u d := by
  classical
  have hI : Finset.Icc 1 (u - 1) = Finset.Ico 1 (1 + (u - 1)) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hfilter : (Finset.Icc 1 (u - 1)).filter (fun n => d ∣ n * (u - n)) =
      (Finset.Ico 1 (1 + (u - 1))).filter
        (fun n : ℕ => (n : ZMod d) * ((u : ZMod d) - (n : ZMod d)) = 0) := by
    rw [← hI]
    apply Finset.filter_congr
    intro n hn
    exact goldbach_polynomial_dvd_iff_zmod u d n
      ((Finset.mem_Icc.mp hn).2.trans (Nat.sub_le u 1))
  rw [hfilter, goldbachSieveRootCount_eq_filter_card]
  exact zmod_predicate_Ico_discrepancy d
    (fun x : ZMod d => x * ((u : ZMod d) - x) = 0) 1 (u - 1)

/-- The same error with the normalized multiplicative sieve density. -/
theorem goldbach_polynomial_count_density_discrepancy (u d : ℕ) [NeZero d] :
    |(((Finset.Icc 1 (u - 1)).filter (fun n => d ∣ n * (u - n))).card : ℝ) -
      goldbachSieveDensity u d * ((u - 1 : ℕ) : ℝ)| ≤
        goldbachSieveRootCount u d := by
  simpa only [goldbachSieveDensity_apply, div_mul_eq_mul_div, mul_div_assoc, mul_comm] using
    goldbach_polynomial_count_discrepancy u d

end Problem337

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.PrimePairSieveModel

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.PrimePairSieve

/-- Pushing a finite set through a noninjective map retains the multiplicity
of each image value. In particular, the two ordered Goldbach pairs with
coordinates exchanged must not be identified by the polynomial map. -/
def fiberWeight (A : Finset ℕ) (f : ℕ → ℕ) (y : ℕ) : ℝ :=
  ((A.filter (fun x => f x = y)).card : ℝ)

lemma fiberWeight_nonneg (A : Finset ℕ) (f : ℕ → ℕ) (y : ℕ) :
    0 ≤ fiberWeight A f y := by
  exact Nat.cast_nonneg _

lemma sum_fiberWeight_indicator (A : Finset ℕ) (f : ℕ → ℕ)
    (p : ℕ → Prop) [DecidablePred p] :
    (∑ y ∈ A.image f, if p y then fiberWeight A f y else 0) =
      ((A.filter (fun x => p (f x))).card : ℝ) := by
  classical
  rw [← Finset.sum_filter]
  unfold fiberWeight
  rw [← Nat.cast_sum]
  congr 1
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, _, hp⟩
    exact ⟨hx, hp⟩
  · rintro ⟨hx, hp⟩
    exact ⟨hx, Finset.mem_image_of_mem f hx, hp⟩

/-- A concrete `BoundingSieve` attached to any polynomial image, with exact
fiber weights rather than an unjustified injectivity assumption. -/
def imageSieve (A : Finset ℕ) (f : ℕ → ℕ) (P : ℕ)
    (hP : Squarefree P) (ν : ArithmeticFunction ℝ)
    (hν : ν.IsMultiplicative)
    (hνpos : ∀ p : ℕ, p.Prime → p ∣ P → 0 < ν p)
    (hνlt : ∀ p : ℕ, p.Prime → p ∣ P → ν p < 1) : BoundingSieve where
  support := A.image f
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fiberWeight A f
  weights_nonneg := fiberWeight_nonneg A f
  totalMass := A.card
  nu := ν
  nu_mult := hν
  nu_pos_of_prime := hνpos
  nu_lt_one_of_prime := hνlt

lemma imageSieve_multSum (A : Finset ℕ) (f : ℕ → ℕ) (P : ℕ)
    (hP : Squarefree P) (ν : ArithmeticFunction ℝ)
    (hν : ν.IsMultiplicative)
    (hνpos : ∀ p : ℕ, p.Prime → p ∣ P → 0 < ν p)
    (hνlt : ∀ p : ℕ, p.Prime → p ∣ P → ν p < 1) (d : ℕ) :
    (imageSieve A f P hP ν hν hνpos hνlt).multSum d =
      ((A.filter (fun x => d ∣ f x)).card : ℝ) := by
  exact sum_fiberWeight_indicator A f (fun y => d ∣ y)

lemma imageSieve_siftedSum (A : Finset ℕ) (f : ℕ → ℕ) (P : ℕ)
    (hP : Squarefree P) (ν : ArithmeticFunction ℝ)
    (hν : ν.IsMultiplicative)
    (hνpos : ∀ p : ℕ, p.Prime → p ∣ P → 0 < ν p)
    (hνlt : ∀ p : ℕ, p.Prime → p ∣ P → ν p < 1) :
    (imageSieve A f P hP ν hν hνpos hνlt).siftedSum =
      ((A.filter (fun x => P.Coprime (f x))).card : ℝ) := by
  exact sum_fiberWeight_indicator A f (fun y => P.Coprime y)

/-- First coordinates of the ordered representations of `N` by two primes. -/
def primePairs (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (N - 1)).filter (fun x => x.Prime ∧ (N - x).Prime)

/-- The original integer coordinates left after sieving both prime factors. -/
def siftedPairs (N P : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (N - 1)).filter (fun x => P.Coprime (x * (N - x)))

/-- A prime pair is either sifted or has a coordinate among the prime divisors
of `P`. This is the exact small-prime correction, valid even for `N=0,1`. -/
theorem primePairs_subset (N P : ℕ) (hP : P ≠ 0) :
    primePairs N ⊆ siftedPairs N P ∪
      (P.primeFactors ∪ P.primeFactors.image (fun p => N - p)) := by
  intro x hx
  obtain ⟨hxI, hxprime, hother⟩ := Finset.mem_filter.mp hx
  have hxN : x ≤ N := by
    have := (Finset.mem_Icc.mp hxI).2
    omega
  by_cases hxdvd : x ∣ P
  · exact Finset.mem_union_right _ (Finset.mem_union_left _
      (Nat.mem_primeFactors.mpr ⟨hxprime, hxdvd, hP⟩))
  by_cases hydvd : N - x ∣ P
  · apply Finset.mem_union_right
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨N - x, Nat.mem_primeFactors.mpr ⟨hother, hydvd, hP⟩,
      Nat.sub_sub_self hxN⟩
  apply Finset.mem_union_left
  apply Finset.mem_filter.mpr
  exact ⟨hxI, ((hxprime.coprime_iff_not_dvd.mpr hxdvd).symm).mul_right
    ((hother.coprime_iff_not_dvd.mpr hydvd).symm)⟩

/-- At most twice the number of sieving primes is lost when passing from
ordered prime pairs to sifted polynomial values with multiplicities. -/
theorem card_primePairs_le_sifted (N P : ℕ) (hP : P ≠ 0) :
    (primePairs N).card ≤ (siftedPairs N P).card + 2 * P.primeFactors.card := by
  calc
    (primePairs N).card ≤
        (siftedPairs N P ∪ (P.primeFactors ∪
          P.primeFactors.image (fun p => N - p))).card :=
      Finset.card_le_card (primePairs_subset N P hP)
    _ ≤ (siftedPairs N P).card + (P.primeFactors ∪
          P.primeFactors.image (fun p => N - p)).card := Finset.card_union_le _ _
    _ ≤ (siftedPairs N P).card +
        (P.primeFactors.card + (P.primeFactors.image (fun p => N - p)).card) :=
      Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ ≤ (siftedPairs N P).card + 2 * P.primeFactors.card := by
      have := Finset.card_image_le (s := P.primeFactors) (f := fun p => N - p)
      omega

/-- The exact polynomial divisor count is the remainder term supplied to the
Selberg sieve; no analytic approximation is built into this model. -/
lemma imageSieve_rem (A : Finset ℕ) (f : ℕ → ℕ) (P : ℕ)
    (hP : Squarefree P) (ν : ArithmeticFunction ℝ)
    (hν : ν.IsMultiplicative)
    (hνpos : ∀ p : ℕ, p.Prime → p ∣ P → 0 < ν p)
    (hνlt : ∀ p : ℕ, p.Prime → p ∣ P → ν p < 1) (d : ℕ) :
    (imageSieve A f P hP ν hν hνpos hνlt).rem d =
      ((A.filter (fun x => d ∣ f x)).card : ℝ) - ν d * A.card := by
  rw [BoundingSieve.rem, imageSieve_multSum]
  rfl

/-- A fully concrete prime-pair Λ² bound with ordered-pair multiplicities and
an explicit small-prime correction. The main coefficient and its arithmetic
remainder are still to be estimated by the sieve application. -/
theorem primePairs_lambdaSquared_bound (N P : ℕ)
    (hP : Squarefree P) (ν : ArithmeticFunction ℝ)
    (hν : ν.IsMultiplicative)
    (hνpos : ∀ p : ℕ, p.Prime → p ∣ P → 0 < ν p)
    (hνlt : ∀ p : ℕ, p.Prime → p ∣ P → ν p < 1)
    (w : ℕ → ℝ) (hw : w 1 = 1) :
    ((primePairs N).card : ℝ) ≤
      ((Finset.Icc 1 (N - 1)).card : ℝ) *
        (∑ d ∈ P.divisors, BoundingSieve.lambdaSquared w d * ν d) +
      (∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d| *
        |(((Finset.Icc 1 (N - 1)).filter
            (fun x => d ∣ x * (N - x))).card : ℝ) -
          ν d * (Finset.Icc 1 (N - 1)).card|) +
      2 * P.primeFactors.card := by
  let s := imageSieve (Finset.Icc 1 (N - 1)) (fun x => x * (N - x))
    P hP ν hν hνpos hνlt
  have hcard : ((primePairs N).card : ℝ) ≤
      ((siftedPairs N P).card : ℝ) + 2 * P.primeFactors.card := by
    exact_mod_cast card_primePairs_le_sifted N P hP.ne_zero
  have hs : s.siftedSum = ((siftedPairs N P).card : ℝ) :=
    imageSieve_siftedSum _ _ _ _ _ _ _ _
  have hb := s.siftedSum_le_mainSum_errSum_of_upperMoebius
    (BoundingSieve.lambdaSquared w) (BoundingSieve.upperMoebius_lambdaSquared w hw)
  have herr : s.errSum (BoundingSieve.lambdaSquared w) =
      ∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d| *
        |(((Finset.Icc 1 (N - 1)).filter
            (fun x => d ∣ x * (N - x))).card : ℝ) -
          ν d * (Finset.Icc 1 (N - 1)).card| := by
    unfold BoundingSieve.errSum
    simp only [s, imageSieve_rem]
    rfl
  rw [hs, herr] at hb
  change ((siftedPairs N P).card : ℝ) ≤
    ((Finset.Icc 1 (N - 1)).card : ℝ) *
      (∑ d ∈ P.divisors, BoundingSieve.lambdaSquared w d * ν d) + _ at hb
  linarith

end Problem337.PrimePairSieve

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.GoldbachSieveApplication

namespace OAI
/-!
A finite, unconditional Selberg upper bound for ordered prime pairs with the
actual Goldbach local density and explicit root-count error. The analytic
estimates for the optimizing weights and denominator are separate tasks.
-/

noncomputable section
open scoped BigOperators

namespace Problem337

/-- The actual Goldbach local density and progression error may be inserted in
the multiplicity-preserving Selberg model. All arithmetic approximation input
has been discharged; the weights are still arbitrary with `w 1 = 1`. -/
theorem goldbach_primePairs_lambdaSquared_bound (N P : ℕ)
    (hN : 2 ∣ N) (hP : Squarefree P) (w : ℕ → ℝ) (hw : w 1 = 1) :
    ((PrimePairSieve.primePairs N).card : ℝ) ≤
      ((N - 1 : ℕ) : ℝ) *
        (∑ d ∈ P.divisors, BoundingSieve.lambdaSquared w d * goldbachSieveDensity N d) +
      (∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d| * goldbachSieveRootCount N d) +
      2 * P.primeFactors.card := by
  have hpos : ∀ p : ℕ, p.Prime → p ∣ P → 0 < goldbachSieveDensity N p := by
    intro p hp _
    exact goldbachSieveDensity_prime_pos N p hp
  have hlt : ∀ p : ℕ, p.Prime → p ∣ P → goldbachSieveDensity N p < 1 := by
    intro p hp _
    exact goldbachSieveDensity_prime_lt_one N p hp (fun _ => hN)
  have hb := PrimePairSieve.primePairs_lambdaSquared_bound N P hP
    (goldbachSieveDensity N) (goldbachSieveDensity_isMultiplicative N)
    hpos hlt w hw
  have hcard : (Finset.Icc 1 (N - 1)).card = N - 1 := by simp
  rw [hcard] at hb
  refine hb.trans (add_le_add (add_le_add le_rfl ?_) le_rfl)
  apply Finset.sum_le_sum
  intro d hd
  have hd0 : d ≠ 0 := by
    have hdiv := (Nat.mem_divisors.mp hd).1
    intro hzero
    subst d
    exact hP.ne_zero (by simpa using hdiv)
  let : NeZero d := ⟨hd0⟩
  exact mul_le_mul_of_nonneg_left (goldbach_polynomial_count_density_discrepancy N d)
    (abs_nonneg _)

end Problem337

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.GoldbachSieveRootBounds

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

instance goldbachSieveRootFintype (u d : ℕ) [NeZero d] :
    Fintype (GoldbachSieveRoot u d) :=
  inferInstanceAs (Fintype {x : ZMod d // x * ((u : ZMod d) - x) = 0})

instance goldbachSieveRootNonempty (u d : ℕ) : Nonempty (GoldbachSieveRoot u d) :=
  ⟨⟨0, by simp⟩⟩

/-- Reduction modulo two possibly noncoprime moduli is injective when the
source modulus is their least common multiple. This remains true on roots. -/
def goldbachSieveRootLCMEmbedding (u a b : ℕ) :
    GoldbachSieveRoot u (a.lcm b) ↪
      GoldbachSieveRoot u a × GoldbachSieveRoot u b := by
  let e : ZMod (a.lcm b) →+* ZMod a × ZMod b :=
    ZMod.castHom (dvd_refl (a.lcm b)) _
  have einj : Function.Injective e := ZMod.castHom_injective _
  have he (x : GoldbachSieveRoot u (a.lcm b)) :
      (e x.val).1 * ((u : ZMod a) - (e x.val).1) = 0 ∧
        (e x.val).2 * ((u : ZMod b) - (e x.val).2) = 0 := by
    have h := congrArg e x.property
    simpa only [map_mul, map_sub, map_natCast, map_zero, Prod.mul_def,
      Prod.sub_def, Prod.ext_iff, Prod.fst_natCast, Prod.snd_natCast,
      Prod.fst_zero, Prod.snd_zero] using h
  refine ⟨fun x => (⟨(e x.val).1, (he x).1⟩, ⟨(e x.val).2, (he x).2⟩), ?_⟩
  intro x y hxy
  apply Subtype.ext
  apply einj
  apply Prod.ext
  · exact congrArg (fun z : GoldbachSieveRoot u a × GoldbachSieveRoot u b => z.1.val) hxy
  · exact congrArg (fun z : GoldbachSieveRoot u a × GoldbachSieveRoot u b => z.2.val) hxy

/-- LCM-submultiplicativity of the root count. This needs no squarefreeness. -/
theorem goldbachSieveRootCount_lcm_le (u a b : ℕ) [NeZero a] [NeZero b] :
    goldbachSieveRootCount u (a.lcm b) ≤
      goldbachSieveRootCount u a * goldbachSieveRootCount u b := by
  unfold goldbachSieveRootCount
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective (goldbachSieveRootLCMEmbedding u a b)
    (goldbachSieveRootLCMEmbedding u a b).injective

/-- Zero is always a root, so each positive modulus has positive local count. -/
theorem goldbachSieveRootCount_pos (u d : ℕ) [NeZero d] :
    0 < goldbachSieveRootCount u d := by
  exact Nat.card_pos

/-- The local root count cannot exceed the modulus. -/
theorem goldbachSieveRootCount_le (u d : ℕ) [NeZero d] :
    goldbachSieveRootCount u d ≤ d := by
  calc
    goldbachSieveRootCount u d ≤ Nat.card (ZMod d) :=
      Nat.card_le_card_of_injective (fun x : GoldbachSieveRoot u d => x.val)
        Subtype.val_injective
    _ = d := Nat.card_zmod d

/-- Exact exponent of two in a squarefree local root count. -/
theorem goldbachSieveRootCount_eq_two_pow (u d : ℕ) (hd : Squarefree d) :
    goldbachSieveRootCount u d =
      2 ^ (d.primeFactors.filter (fun p => ¬p ∣ u)).card := by
  rw [goldbachSieveRootCount_squarefree u d hd]
  have hf : (∏ p ∈ d.primeFactors, if p ∣ u then 1 else 2) =
      ∏ p ∈ d.primeFactors.filter (fun p => ¬p ∣ u), (2 : ℕ) := by
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro p hp
    split_ifs <;> simp_all
  rw [hf, Finset.prod_const]

/-- Squarefree local root counts are bounded by the number of subsets of
prime factors, uniformly in the target. -/
theorem goldbachSieveRootCount_le_two_pow (u d : ℕ) (hd : Squarefree d) :
    goldbachSieveRootCount u d ≤ 2 ^ d.primeFactors.card := by
  rw [goldbachSieveRootCount_eq_two_pow u d hd]
  exact Nat.pow_le_pow_right (by omega) (Finset.card_filter_le _ _)

end Problem337

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.GoldbachSelbergBound

namespace OAI
noncomputable section
open scoped BigOperators
open Finset

namespace Problem337.GoldbachSelberg

/-- The actual multiplicity-preserving sieve for an even target. -/
def sieve (N P : ℕ) (hN : 2 ∣ N) (hP : Squarefree P) : BoundingSieve :=
  PrimePairSieve.imageSieve (Icc 1 (N - 1)) (fun x => x * (N - x)) P hP
    (goldbachSieveDensity N) (goldbachSieveDensity_isMultiplicative N)
    (fun p hp _ => goldbachSieveDensity_prime_pos N p hp)
    (fun p hp _ => goldbachSieveDensity_prime_lt_one N p hp (fun _ => hN))

/-- A concrete finite denominator, independent of proof-valued sieve parameters. -/
def denominator (N P z : ℕ) : ℝ :=
  ∑ d ∈ P.divisors, if d ≤ z then
    goldbachSieveDensity N d *
      ∏ p ∈ d.primeFactors, (1 - goldbachSieveDensity N p)⁻¹ else 0

theorem normalizer_eq_denominator (N P z : ℕ) (hN : 2 ∣ N) (hP : Squarefree P) :
    SelbergOptimal.normalizer (sieve N P hN hP) z = denominator N P z := by
  unfold SelbergOptimal.normalizer denominator
  apply sum_congr rfl
  intro d hd
  rw [BoundingSieve.selbergTerms_apply]
  rfl

theorem denominator_pos (N P : ℕ) (hN : 2 ∣ N) (hP : Squarefree P)
    {z : ℕ} (hz : 1 ≤ z) : 0 < denominator N P z := by
  rw [← normalizer_eq_denominator N P z hN hP]
  exact SelbergOptimal.normalizer_pos _ hz

/-- The local error of this actual sieve is bounded by its actual root count. -/
theorem rem_bound (N P d : ℕ) (hN : 2 ∣ N) (hP : Squarefree P) [NeZero d] :
    |(sieve N P hN hP).rem d| ≤ goldbachSieveRootCount N d := by
  unfold sieve
  rw [PrimePairSieve.imageSieve_rem]
  simpa using goldbach_polynomial_count_density_discrepancy N d

/-- The polynomial root count yields the dimension-two factorizable remainder
bound required by the optimized logarithmic error estimate. -/
theorem rem_lcm_bound (N P : ℕ) (hN : 2 ∣ N) (hP : Squarefree P)
    (a : ℕ) (ha : a ∈ P.divisors) (b : ℕ) (hb : b ∈ P.divisors) :
    |(sieve N P hN hP).rem (Nat.lcm a b)| ≤
      (2 : ℝ) ^ a.primeFactors.card * (2 : ℝ) ^ b.primeFactors.card := by
  let : NeZero a := ⟨(Nat.pos_of_mem_divisors ha).ne'⟩
  let : NeZero b := ⟨(Nat.pos_of_mem_divisors hb).ne'⟩
  let : NeZero (Nat.lcm a b) := ⟨Nat.lcm_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  have ha2 := goldbachSieveRootCount_le_two_pow N a
    (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors ha))
  have hb2 := goldbachSieveRootCount_le_two_pow N b
    (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hb))
  calc
    _ ≤ (goldbachSieveRootCount N (Nat.lcm a b) : ℝ) := rem_bound N P _ hN hP
    _ ≤ (goldbachSieveRootCount N a : ℝ) * goldbachSieveRootCount N b := by
      exact_mod_cast goldbachSieveRootCount_lcm_le N a b
    _ ≤ _ := by exact_mod_cast Nat.mul_le_mul ha2 hb2

/-- An unconditional, explicit finite upper sieve for ordered Goldbach pairs.
Only evenness, squarefreeness of the chosen sieving product, and `z ≥ 1` are
assumed. The remaining denominator is an actual finite arithmetic sum; no
prime-distribution or unproved remainder estimate is hidden in a premise. -/
theorem primePairs_le (N P : ℕ) (hN : 2 ∣ N) (hP : Squarefree P)
    {z : ℕ} (hz : 1 ≤ z) :
    ((PrimePairSieve.primePairs N).card : ℝ) ≤
      ((N - 1 : ℕ) : ℝ) / denominator N P z +
      (z : ℝ) ^ 2 * (1 + Real.log z) ^ 4 + 2 * P.primeFactors.card := by
  let s := sieve N P hN hP
  have he := SelbergOptimal.siftedSum_le_log_error s hz
    (fun a ha b hb => rem_lcm_bound N P hN hP a ha b hb)
  have hsum : s.siftedSum = ((PrimePairSieve.siftedPairs N P).card : ℝ) :=
    PrimePairSieve.imageSieve_siftedSum _ _ _ _ _ _ _ _
  have hmass : s.totalMass = ((N - 1 : ℕ) : ℝ) := by
    simp [s, sieve, PrimePairSieve.imageSieve]
  have hnorm : SelbergOptimal.normalizer s z = denominator N P z :=
    normalizer_eq_denominator N P z hN hP
  rw [hsum, hmass, hnorm] at he
  have hpairs : ((PrimePairSieve.primePairs N).card : ℝ) ≤
      (PrimePairSieve.siftedPairs N P).card + 2 * P.primeFactors.card := by
    exact_mod_cast PrimePairSieve.card_primePairs_le_sifted N P hP.ne_zero
  linarith

/-- With the primorial cutoff, the denominator is a sum over every squarefree
integer up to the cutoff, not an unspecified subset of them. -/
theorem denominator_primorial (N z : ℕ) :
    denominator N (primorial z) z =
      ∑ d ∈ Icc 1 z, if Squarefree d then
        goldbachSieveDensity N d *
          ∏ p ∈ d.primeFactors, (1 - goldbachSieveDensity N p)⁻¹ else 0 := by
  classical
  unfold denominator
  rw [← sum_filter]
  have hsets : (primorial z).divisors.filter (fun d => d ≤ z) =
      (Icc 1 z).filter Squarefree := by
    ext d
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨hd, hdz⟩
      exact ⟨⟨Nat.pos_of_mem_divisors hd, hdz⟩,
        (squarefree_primorial z).squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)⟩
    · rintro ⟨⟨hdpos, hdz⟩, hsq⟩
      exact ⟨Nat.mem_divisors.mpr
        ⟨hsq.dvd_primorial.trans (primorial_dvd_primorial hdz),
          primorial_ne_zero z⟩, hdz⟩
  rw [hsets, sum_filter]

/-- The explicit prime-pair sieve at the canonical primorial product. -/
theorem primePairs_le_primorial (N : ℕ) (hN : 2 ∣ N) {z : ℕ} (hz : 1 ≤ z) :
    ((PrimePairSieve.primePairs N).card : ℝ) ≤
      ((N - 1 : ℕ) : ℝ) / denominator N (primorial z) z +
      (z : ℝ) ^ 2 * (1 + Real.log z) ^ 4 + 2 * (Nat.primesLE z).card := by
  simpa only [primeFactors_primorial] using
    primePairs_le N (primorial z) hN (squarefree_primorial z) hz

end Problem337.GoldbachSelberg

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.SmoothRankin

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

/-- A finite nonnegative sum over smooth numbers is bounded by the finite
Euler product. Only the local prime-power series need to be summable. -/
theorem smooth_sum_le_euler_product
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hf1 : f 1 = 1)
    (hmul : ∀ {m n}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hsum : ∀ {p : ℕ}, p.Prime → Summable (fun j : ℕ => ‖f (p ^ j)‖))
    (N : ℕ) (s : Finset ℕ) (hs : ∀ n ∈ s, n ∈ N.smoothNumbers) :
    (∑ n ∈ s, f n) ≤ ∏ p ∈ N.primesBelow, ∑' j : ℕ, f (p ^ j) := by
  classical
  obtain ⟨_, hprod⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    hf1 hmul hsum N
  calc
    (∑ n ∈ s, f n) = ∑ n ∈ s.subtype (fun n => n ∈ N.smoothNumbers), f n :=
      (Finset.sum_subtype_of_mem f hs).symm
    _ ≤ ∑' n : N.smoothNumbers, f n :=
      hprod.summable.sum_le_tsum _ (fun n _ => hf n)
    _ = ∏ p ∈ N.primesBelow, ∑' j : ℕ, f (p ^ j) := hprod.tsum_eq

/-- The elementary exponential weight used in Rankin's tail estimate. -/
theorem rankin_weight_bound {V β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hn : Real.exp V ≤ (n : ℝ)) :
    1 ≤ Real.exp (-β * V) * (n : ℝ) ^ β := by
  have hpow := Real.rpow_le_rpow (le_of_lt (Real.exp_pos V)) hn hβ
  rw [← Real.exp_mul] at hpow
  have h := mul_le_mul_of_nonneg_left hpow (le_of_lt (Real.exp_pos (-β * V)))
  have hid : Real.exp (-β * V) * Real.exp (V * β) = 1 := by
    rw [← Real.exp_add]
    have : -β * V + V * β = 0 := by ring
    rw [this, Real.exp_zero]
  rwa [hid] at h

/-- Rankin's trick followed by a finite Euler product. This form applies to
`f n = τ(n)^r / n`; the local weight then has exponent `-1 + β`. -/
theorem smooth_rankin_bound
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hf1 : f 1 = 1)
    (hmul : ∀ {m n}, Nat.Coprime m n → f (m * n) = f m * f n)
    {V β : ℝ} (hβ : 0 ≤ β)
    (hsum : ∀ {p : ℕ}, p.Prime →
      Summable (fun j : ℕ => ‖f (p ^ j) * ((p ^ j : ℕ) : ℝ) ^ β‖))
    (N : ℕ) (s : Finset ℕ) (hs : ∀ n ∈ s, n ∈ N.smoothNumbers)
    (hlarge : ∀ n ∈ s, Real.exp V ≤ (n : ℝ)) :
    (∑ n ∈ s, f n) ≤ Real.exp (-β * V) *
      (∏ p ∈ N.primesBelow, ∑' j : ℕ, f (p ^ j) * ((p ^ j : ℕ) : ℝ) ^ β) := by
  have hg : ∀ n : ℕ, 0 ≤ f n * (n : ℝ) ^ β := by
    intro n
    exact mul_nonneg (hf n) (Real.rpow_nonneg (Nat.cast_nonneg n) β)
  have hg1 : f 1 * (1 : ℝ) ^ β = 1 := by simp [hf1]
  have hgmul : ∀ {m n : ℕ}, Nat.Coprime m n →
      f (m * n) * ((m * n : ℕ) : ℝ) ^ β =
        (f m * (m : ℝ) ^ β) * (f n * (n : ℝ) ^ β) := by
    intro m n hmn
    rw [hmul hmn, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring
  have heuler := smooth_sum_le_euler_product (fun n => f n * (n : ℝ) ^ β)
    hg (by simpa using hg1) hgmul hsum N s hs
  calc
    (∑ n ∈ s, f n) ≤ ∑ n ∈ s, Real.exp (-β * V) * (f n * (n : ℝ) ^ β) := by
      apply Finset.sum_le_sum
      intro n hn
      have h := mul_le_mul_of_nonneg_left (rankin_weight_bound hβ (hlarge n hn)) (hf n)
      nlinarith
    _ = Real.exp (-β * V) * ∑ n ∈ s, f n * (n : ℝ) ^ β := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-β * V) *
        (∏ p ∈ N.primesBelow, ∑' j : ℕ, f (p ^ j) * ((p ^ j : ℕ) : ℝ) ^ β) :=
      mul_le_mul_of_nonneg_left heuler (le_of_lt (Real.exp_pos _))

/-- The multiplicative weight occurring in divisor harmonic moments. -/
def divisorHarmonicWeight (r n : ℕ) : ℝ :=
  (n.divisors.card : ℝ) ^ r / (n : ℝ)

theorem divisorHarmonicWeight_nonneg (r n : ℕ) : 0 ≤ divisorHarmonicWeight r n := by
  unfold divisorHarmonicWeight
  positivity

theorem divisorHarmonicWeight_one (r : ℕ) : divisorHarmonicWeight r 1 = 1 := by
  simp [divisorHarmonicWeight]

theorem divisorHarmonicWeight_mul (r : ℕ) {m n : ℕ} (h : m.Coprime n) :
    divisorHarmonicWeight r (m * n) = divisorHarmonicWeight r m * divisorHarmonicWeight r n := by
  simp only [divisorHarmonicWeight, h.card_divisors_mul, Nat.cast_mul, mul_pow]
  ring

theorem divisorHarmonicWeight_prime_power (r : ℕ) {p : ℕ} (hp : p.Prime) (j : ℕ)
    (β : ℝ) :
    divisorHarmonicWeight r (p ^ j) * ((p ^ j : ℕ) : ℝ) ^ β =
      ((j + 1 : ℕ) : ℝ) ^ r * ((p : ℝ) ^ (β - 1)) ^ j := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpow : (0 : ℝ) < (p : ℝ) ^ j := pow_pos hpR j
  simp only [divisorHarmonicWeight, Nat.divisors_prime_pow hp, Finset.card_map,
    Finset.card_range, Nat.cast_pow]
  rw [Real.rpow_pow_comm (le_of_lt hpR), Real.rpow_sub_one (ne_of_gt hpow)]
  ring

theorem summable_successor_pow_geometric (r : ℕ) {q : ℝ} (hq : 0 < q) (hqone : q < 1) :
    Summable (fun j : ℕ => ‖((j + 1 : ℕ) : ℝ) ^ r * q ^ j‖) := by
  have hnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hq] using hqone
  have h := (summable_norm_pow_mul_geometric_of_norm_lt_one r hnorm).comp_injective
    Nat.succ_injective
  have h' := h.mul_right q⁻¹
  apply h'.congr
  intro j
  change ‖((j + 1 : ℕ) : ℝ) ^ r * q ^ (j + 1)‖ * q⁻¹ =
    ‖((j + 1 : ℕ) : ℝ) ^ r * q ^ j‖
  rw [pow_succ, ← mul_assoc, norm_mul, Real.norm_eq_abs q, abs_of_pos hq]
  field_simp

theorem divisorHarmonicWeight_local_summable (r : ℕ) {β : ℝ} (hβ : β < 1)
    {p : ℕ} (hp : p.Prime) :
    Summable (fun j : ℕ => ‖divisorHarmonicWeight r (p ^ j) * ((p ^ j : ℕ) : ℝ) ^ β‖) := by
  simp_rw [divisorHarmonicWeight_prime_power r hp]
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact summable_successor_pow_geometric r (Real.rpow_pos_of_pos (by linarith) _)
    (Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith))

/-- Concrete smooth initial-interval Rankin estimate for any natural moment order. -/
theorem divisor_smooth_rankin_bound (r : ℕ) {V β : ℝ} (hβ : 0 ≤ β) (hβone : β < 1)
    (N : ℕ) (s : Finset ℕ) (hs : ∀ n ∈ s, n ∈ N.smoothNumbers)
    (hlarge : ∀ n ∈ s, Real.exp V ≤ (n : ℝ)) :
    (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤ Real.exp (-β * V) *
      (∏ p ∈ N.primesBelow, ∑' j : ℕ,
        ((j + 1 : ℕ) : ℝ) ^ r * ((p : ℝ) ^ (β - 1)) ^ j) := by
  have h := smooth_rankin_bound (divisorHarmonicWeight r) (divisorHarmonicWeight_nonneg r)
    (divisorHarmonicWeight_one r) (divisorHarmonicWeight_mul r) hβ
    (divisorHarmonicWeight_local_summable r hβone) N s hs hlarge
  change (∑ n ∈ s, divisorHarmonicWeight r n) ≤ _
  apply h.trans_eq
  apply congrArg (fun x : ℝ => Real.exp (-β * V) * x)
  apply Finset.prod_congr rfl
  intro p hp
  apply tsum_congr
  intro j
  exact divisorHarmonicWeight_prime_power r (Nat.prime_of_mem_primesBelow hp) j β

/-- The unweighted finite Euler-product bound for harmonic divisor moments. -/
theorem divisor_harmonic_sum_le_euler_product (r N : ℕ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, n ∈ N.smoothNumbers) :
    (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
      ∏ p ∈ N.primesBelow, ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ r * ((p : ℝ)⁻¹) ^ j := by
  have hlarge : ∀ n ∈ s, Real.exp (0 : ℝ) ≤ (n : ℝ) := by
    intro n hn
    rw [Real.exp_zero]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_zero_of_mem_smoothNumbers (hs n hn))
  simpa [Real.rpow_neg_one] using divisor_smooth_rankin_bound r (le_refl (0 : ℝ)) (by norm_num : (0 : ℝ) < 1)
    N s hs hlarge

/-- A local Euler factor, in the indexing convenient for Rankin's trick. -/
def divisorEulerFactor (r p : ℕ) (β : ℝ) : ℝ :=
  ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ r * ((p : ℝ) ^ (β - 1)) ^ j

theorem divisorEulerFactor_one_le (r : ℕ) {p : ℕ} (hp : p.Prime) {β : ℝ}
    (hβ : β < 1) : 1 ≤ divisorEulerFactor r p β := by
  have hs := divisorHarmonicWeight_local_summable r hβ hp
  simp_rw [divisorHarmonicWeight_prime_power r hp] at hs
  have h := hs.of_norm.sum_le_tsum {0} (by
    intro j _
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    positivity)
  simpa [divisorEulerFactor] using h

/-- Logarithmic local-factor estimates turn the Rankin Euler product into a
single exponential. This is the precise smooth initial-interval bound used in the
divisor-moment decomposition. -/
theorem divisor_smooth_rankin_log_bound (r : ℕ) {V β C : ℝ}
    (hβ : 0 ≤ β) (hβone : β < 1) (N : ℕ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, n ∈ N.smoothNumbers)
    (hlarge : ∀ n ∈ s, Real.exp V ≤ (n : ℝ))
    (hlocal : ∀ p ∈ N.primesBelow,
      Real.log (divisorEulerFactor r p β) ≤ C * (p : ℝ) ^ (β - 1)) :
    (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
      Real.exp (-β * V + C * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (β - 1)) := by
  have hpos : ∀ p ∈ N.primesBelow, 0 < divisorEulerFactor r p β := by
    intro p hp
    have := divisorEulerFactor_one_le r (Nat.prime_of_mem_primesBelow hp) hβone
    linarith
  have hprodpos : 0 < ∏ p ∈ N.primesBelow, divisorEulerFactor r p β := Finset.prod_pos hpos
  have hlog : Real.log (∏ p ∈ N.primesBelow, divisorEulerFactor r p β) ≤
      C * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (β - 1) := by
    rw [Real.log_prod (fun p hp => ne_of_gt (hpos p hp)), Finset.mul_sum]
    exact Finset.sum_le_sum hlocal
  have hprod := (Real.log_le_iff_le_exp hprodpos).mp hlog
  have hrank := divisor_smooth_rankin_bound r hβ hβone N s hs hlarge
  change (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
    Real.exp (-β * V) * ∏ p ∈ N.primesBelow, divisorEulerFactor r p β at hrank
  calc
    (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
        Real.exp (-β * V) * ∏ p ∈ N.primesBelow, divisorEulerFactor r p β := hrank
    _ ≤ Real.exp (-β * V) *
        Real.exp (C * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (β - 1)) :=
      mul_le_mul_of_nonneg_left hprod (le_of_lt (Real.exp_pos _))
    _ = Real.exp (-β * V + C * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (β - 1)) :=
      (Real.exp_add _ _).symm

end Problem337

end

end OAI


open Finset

namespace CentralSelberg

theorem prime_log_mass (m : ℕ) (hm : 0 < m) :
    (∑ p ∈ m.primeFactors, Real.log (p:ℝ)) ≤ Real.log m := by
  rw [← Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  rw [← Nat.cast_prod]
  apply Real.log_le_log
  · exact_mod_cast Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  · exact_mod_cast Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)

/-- An elementary upper bound for the weighted prime harmonic sum via counting multiples. -/
theorem weighted_harmonic (y : ℕ) (hy : 1 ≤ y) :
    (∑ p ∈ y.primesLE, Real.log (p:ℝ)/(p:ℝ)) ≤ 2*Real.log y := by
  let T := Finset.Ioc 0 y
  have hcnt (p : ℕ) : ((T.filter (p ∣ ·)).card:ℝ) = (y/p:ℕ) := by
    exact_mod_cast Nat.Ioc_filter_dvd_card_eq_div y p
  have hsum : (∑ p ∈ y.primesLE, ((y/p:ℕ):ℝ)*Real.log p) ≤ (y:ℝ)*Real.log y := by
    calc
      _ = ∑ p ∈ y.primesLE, ∑ k ∈ T, if p ∣ k then Real.log p else 0 := by
        refine sum_congr rfl fun p _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcnt]
      _ = ∑ k ∈ T, ∑ p ∈ y.primesLE, if p ∣ k then Real.log p else 0 := Finset.sum_comm
      _ ≤ ∑ _k ∈ T, Real.log y := by
        refine sum_le_sum fun k hk => ?_
        obtain ⟨hkpos, hky⟩ := Finset.mem_Ioc.mp hk
        rw [← Finset.sum_filter]
        have heq : (y.primesLE.filter (· ∣ k)) = k.primeFactors := by
          ext p
          simp only [Finset.mem_filter, Nat.mem_primesLE, Nat.mem_primeFactors]
          exact ⟨fun h => ⟨h.1.2, h.2, hkpos.ne'⟩, fun h => ⟨⟨(Nat.le_of_dvd hkpos h.2.1).trans hky, h.1⟩, h.2.1⟩⟩
        rw [heq]
        exact (prime_log_mass _ hkpos).trans (Real.log_le_log (by exact_mod_cast hkpos) (by exact_mod_cast hky))
      _ = _ := by simp [T]
  have hyR : (0:ℝ) < y := by exact_mod_cast hy
  apply (le_of_mul_le_mul_left (a := (y:ℝ)) ?_ hyR)
  calc
    _ = ∑ p ∈ y.primesLE, (y:ℝ)*(Real.log p/p) := Finset.mul_sum ..
    _ ≤ ∑ p ∈ y.primesLE, 2*(((y/p:ℕ):ℝ)*Real.log p) := by
      refine sum_le_sum fun p hp => ?_
      obtain ⟨hpy,hprime⟩ := Nat.mem_primesLE.mp hp
      have hp0 : (0:ℝ) < p := by exact_mod_cast hprime.pos
      have hd : 1 ≤ y/p := (Nat.le_div_iff_mul_le hprime.pos).mpr (by simpa)
      have hdiv : y ≤ 2*((y/p)*p) := by
        have he := Nat.div_add_mod y p
        have hr := Nat.mod_lt y hprime.pos
        have hpq := Nat.mul_le_mul_right p hd
        rw [Nat.mul_comm p] at he
        omega
      have hr : (y:ℝ) ≤ 2*(((y/p:ℕ):ℝ)*p) := by exact_mod_cast hdiv
      rw [← mul_div_assoc, div_le_iff₀ hp0]
      calc
        _ ≤ (2*(((y/p:ℕ):ℝ)*p))*Real.log p :=
          mul_le_mul_of_nonneg_right hr (Real.log_nonneg (by exact_mod_cast hprime.one_le))
        _ = _ := by ring
    _ ≤ _ := by rw [← Finset.mul_sum]; linarith

end CentralSelberg


open Finset
namespace CentralSelberg

/-- First logarithmic moment of a finite Euler product. -/
theorem powerset_moment (s : Finset ℕ) (g l : ℕ → ℝ)
    (hg : ∀ i ∈ s, 0 ≤ g i) :
    (∑ t ∈ s.powerset, (∏ i ∈ t, g i)*(∑ i ∈ t, l i)) =
      (∏ i ∈ s, (1+g i)) * (∑ i ∈ s, g i/(1+g i)*l i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hn : 1+g a ≠ 0 := by have := hg a (Finset.mem_insert_self ..); linarith
    have hi := ih (fun p hp => hg p (mem_insert_of_mem hp))
    rw [Finset.sum_powerset_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hexp : (∑ t ∈ s.powerset, (∏ i ∈ insert a t, g i)*(∑ i ∈ insert a t, l i)) =
        g a*l a * (∏ i ∈ s, (1+g i)) +
        g a * (∑ t ∈ s.powerset, (∏ i ∈ t, g i)*(∑ i ∈ t, l i)) := by
      rw [Finset.prod_one_add s, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t ht => ?_
      have hat : a ∉ t := fun h => ha ((Finset.mem_powerset.mp ht) h)
      rw [Finset.prod_insert hat, Finset.sum_insert hat]
      ring
    rw [hexp, hi]
    field_simp
    ring

end CentralSelberg


open Finset
open OAI.Problem337
namespace CentralSelberg
noncomputable section

def rho (n p : ℕ) := goldbachSieveDensity n p

def wgt (n p : ℕ) : ℝ := rho n p * (1-rho n p)⁻¹

def loc (n p : ℕ) : ℝ := if 2<p ∧ p∣n then 1+1/((p:ℝ)-2) else 1

theorem rho_bounds (n : ℕ) (hn : 2∣n) (p : ℕ) (hp : p.Prime) :
    0 < rho n p ∧ rho n p < 1 :=
  ⟨goldbachSieveDensity_prime_pos n p hp, goldbachSieveDensity_prime_lt_one n p hp (fun _ => hn)⟩

theorem wgt_pos (n : ℕ) (hn : 2∣n) (p : ℕ) (hp : p.Prime) : 0 < wgt n p := by
  have h := rho_bounds n hn p hp
  exact mul_pos h.1 (inv_pos.mpr (by linarith [h.2]))

theorem wgt_ratio (n : ℕ) (hn : 2∣n) (p : ℕ) (hp : p.Prime) :
    wgt n p/(1+wgt n p) = rho n p := by
  have h := (rho_bounds n hn p hp).2
  have hpos := wgt_pos n hn p hp
  unfold wgt at *
  field_simp
  ring

theorem harmonic_product (y : ℕ) :
    Real.log ((y:ℝ)+1) ≤ ∏ p ∈ y.primesLE, (1-(p:ℝ)⁻¹)⁻¹ := by
  let S := Finset.Icc 1 y
  have hsm (k : ℕ) (hk : k ∈ S) : k ∈ (y+1).smoothNumbers :=
    Nat.mem_smoothNumbers_of_lt (Finset.mem_Icc.mp hk).1 (by have := (Finset.mem_Icc.mp hk).2; omega)
  have H := divisor_harmonic_sum_le_euler_product 0 (y+1) S hsm
  simp only [pow_zero, one_mul, one_div] at H
  have hgeo (p : ℕ) (hp : p∈y.primesLE) : (∑' j : ℕ, ((p:ℝ)⁻¹)^j) = (1-(p:ℝ)⁻¹)⁻¹ := by
    apply tsum_geometric_of_lt_one
    · positivity
    · exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt)
  calc
    _ ≤ (harmonic y:ℝ) := by simpa using log_add_one_le_harmonic y
    _ = ∑ k ∈ S, (k:ℝ)⁻¹ := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rfl
    _ ≤ _ := H.trans_eq (Finset.prod_congr rfl hgeo)

end
end CentralSelberg


open Finset OAI.Problem337
namespace CentralSelberg
noncomputable section

def singular (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors.filter (fun p => 2<p), (1+1/((p:ℝ)-2))

theorem factor_one_le (n p : ℕ) : 1 ≤ loc n p := by
  unfold loc
  split
  · rename_i h
    have : (2:ℝ)<p := by exact_mod_cast h.1
    linarith [show 0≤1/((p:ℝ)-2) by positivity]
  · rfl

theorem singular_one_le (n : ℕ) : 1 ≤ singular n := by
  apply Finset.one_le_prod₀
  intro p hp
  have h : (2:ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2
  linarith [show 0 ≤ 1/((p:ℝ)-2) by positivity]

theorem local_correction (n y : ℕ) (hn : 0<n) :
    (∏ p ∈ y.primesLE, loc n p) ≤ singular n := by
  let T := y.primesLE.filter (fun p => 2<p ∧ p∣n)
  have sub : T ⊆ n.primeFactors.filter (fun p => 2<p) := by
    intro p hp
    obtain ⟨h,ho,hd⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primesLE h,hd,hn.ne'⟩,ho⟩
  change (∏ p ∈ y.primesLE, if 2<p ∧ p∣n then _ else 1) ≤ _
  rw [← Finset.prod_filter]
  exact Finset.prod_le_prod_of_subset_of_one_le₀ sub (fun p hp => by
    have h : (2:ℝ)<p := by exact_mod_cast (Finset.mem_filter.mp hp).2.1
    positivity) (fun p hp _ => by
    have h : (2:ℝ)<p := by exact_mod_cast (Finset.mem_filter.mp hp).2
    linarith [show 0 ≤ 1/((p:ℝ)-2) by positivity])

theorem euler_mass (n y : ℕ) (hn : 2∣n) (hnp : 0<n) :
    (Real.log ((y:ℝ)+1))^2 ≤ 2*singular n*(∏ p ∈ y.primesLE, (1+wgt n p)) := by
  let T := y.primesLE
  have hloc (p : ℕ) (hp : p ∈ T) :
      ((1-(p:ℝ)⁻¹)⁻¹)^2 ≤ (if p=2 then 2 else 1)*loc n p*(1+wgt n p) := by
    have hpP := Nat.prime_of_mem_primesLE hp
    have hr := goldbachSieveDensity_prime n p hpP
    unfold wgt rho loc
    rw [hr]
    by_cases h2 : p=2
    · subst p; norm_num [hn]
    · have hh : 2 < p := by have := hpP.two_le; omega
      have hrp : (2:ℝ) < p := by exact_mod_cast hh
      have hp0 : (0:ℝ)<p := by linarith
      by_cases hd : p∣n
      · simp only [hh,hd,h2,if_true,true_and,if_false,one_mul]
        have hp1 : 0 < (p:ℝ) - 1 := by linarith
        have hp2 : 0 < (p:ℝ) - 2 := by linarith
        field_simp [hp1, hp2]
        nlinarith [sq_nonneg (p:ℝ)]
      · simp only [hh,hd,h2,if_true,true_and,if_false,one_mul]
        have hp1 : 0 < (p:ℝ) - 1 := by linarith
        have hp2 : 0 < (p:ℝ) - 2 := by linarith
        field_simp [hp1, hp2]
        nlinarith [sq_nonneg (p:ℝ)]
  have htwo : (∏ p ∈ T, (if p=2 then (2:ℝ) else 1)) ≤ 2 := by
    rw [Finset.prod_ite_eq']; split <;> norm_num
  have hpos := Finset.prod_nonneg (s := T) (f := fun p => 1+wgt n p) (fun p hp => by
    have := wgt_pos n hn p (Nat.prime_of_mem_primesLE hp); linarith)
  have hcorr := local_correction n y hnp
  have hcpos := Finset.prod_nonneg (s := T) (f := loc n)
    (fun p hp => by linarith [factor_one_le n p])
  have htwo' := mul_le_mul htwo hcorr hcpos (by norm_num : (0:ℝ) ≤ 2)
  calc
    _ ≤ (∏ p ∈ T, (1-(p:ℝ)⁻¹)⁻¹)^2 :=
      pow_le_pow_left₀ (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) y])) (harmonic_product y) _
    _ = ∏ p ∈ T, ((1-(p:ℝ)⁻¹)⁻¹)^2 := (Finset.prod_pow ..).symm
    _ ≤ ∏ p ∈ T, (if p=2 then 2 else 1)*loc n p*(1+wgt n p) := Finset.prod_le_prod₀
      (fun p hp => sq_nonneg _) hloc
    _ ≤ _ := by
      simp only [Finset.prod_mul_distrib]
      exact mul_le_mul_of_nonneg_right htwo' hpos

end
end CentralSelberg


open Finset OAI.Problem337
namespace CentralSelberg
noncomputable section

def mass (n y : ℕ) : ℝ := ∏ p ∈ y.primesLE, (1+wgt n p)
def index (t : Finset ℕ) : ℕ := ∏ p ∈ t, p
def weight (n : ℕ) (t : Finset ℕ) : ℝ := ∏ p ∈ t, wgt n p

theorem denominator_as_sum (n y z : ℕ) :
    GoldbachSelberg.denominator n (primorial y) z =
      ∑ t ∈ y.primesLE.powerset, if index t ≤ z then weight n t else 0 := by
  classical
  let P := primorial y
  have prime (t : Finset ℕ) (ht : t∈y.primesLE.powerset) : ∀ p∈t, p.Prime :=
    fun p hp => Nat.prime_of_mem_primesLE ((Finset.mem_powerset.mp ht) hp)
  have hfac (t : Finset ℕ) (ht : t∈y.primesLE.powerset) :
      (index t).primeFactors=t := Nat.primeFactors_prod (prime t ht)
  have hmap : P.divisors = y.primesLE.powerset.image index := by
    ext d
    constructor
    · intro hd
      have hsq := (squarefree_primorial y).squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
      have hmono := Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) (primorial_ne_zero y)
      rw [primeFactors_primorial] at hmono
      exact Finset.mem_image.mpr ⟨d.primeFactors, Finset.mem_powerset.mpr hmono, Nat.prod_primeFactors_of_squarefree hsq⟩
    · rintro hd
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hd
      exact Nat.mem_divisors.mpr ⟨Finset.prod_dvd_prod_of_subset _ _ _ (Finset.mem_powerset.mp ht),primorial_ne_zero y⟩
  unfold GoldbachSelberg.denominator
  change (∑ d ∈ P.divisors, _) = _
  rw [hmap, Finset.sum_image (fun a ha b hb hh => (hfac a ha).symm.trans ((congrArg Nat.primeFactors hh).trans (hfac b hb)))]
  refine Finset.sum_congr rfl fun t ht => ?_
  split_ifs
  · rw [hfac t ht, index, (goldbachSieveDensity_isMultiplicative n).map_prod_of_prime t (prime t ht)]
    exact (Finset.prod_mul_distrib).symm
  · rfl

theorem retained (n y : ℕ) (hn : 2∣n) (hy : 2≤y) :
    mass n y ≤ 2 * GoldbachSelberg.denominator n (primorial y) (y^8) := by
  let T := y.primesLE.powerset
  let W := weight n
  let D := GoldbachSelberg.denominator n (primorial y) (y^8)
  have wp (t : Finset ℕ) (ht : t ∈ T) : 0 ≤ W t :=
    Finset.prod_nonneg fun p hp => (wgt_pos n hn p (Nat.prime_of_mem_primesLE ((Finset.mem_powerset.mp ht) hp))).le
  have total : (∑ t ∈ T, W t) = mass n y := (Finset.prod_one_add _).symm
  have heavy_point (t : Finset ℕ) (ht : t ∈ T) :
      (if y^8 < index t then W t else 0)*(8*Real.log y) ≤ W t*Real.log (index t) := by
    have hip : 0 < index t := Finset.prod_pos fun p hp =>
      (Nat.prime_of_mem_primesLE ((Finset.mem_powerset.mp ht) hp)).pos
    split
    · rename_i hl
      apply mul_le_mul_of_nonneg_left _ (wp t ht)
      have hlog := Real.log_le_log (show (0:ℝ) < ((y^8:ℕ):ℝ) by positivity) (show ((y^8:ℕ):ℝ) ≤ index t by exact_mod_cast hl.le)
      simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using hlog
    · rw [zero_mul]
      exact mul_nonneg (wp t ht) (Real.log_nonneg (by exact_mod_cast hip))
  have mean := powerset_moment y.primesLE (wgt n) (fun p => Real.log (p:ℝ))
    (fun p hp => (wgt_pos n hn p (Nat.prime_of_mem_primesLE hp)).le)
  have hsumlog (t : Finset ℕ) (ht : t∈T) :
      Real.log (index t) = ∑ p ∈ t, Real.log (p:ℝ) := by
    unfold index
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp; exact_mod_cast (Nat.prime_of_mem_primesLE ((Finset.mem_powerset.mp ht) hp)).ne_zero
  have bound : (∑ p ∈ y.primesLE, wgt n p/(1+wgt n p)*Real.log p) ≤ 4*Real.log y := by
    calc
      _ ≤ ∑ p ∈ y.primesLE, 2*(Real.log p/p) := by
        refine sum_le_sum fun p hp => ?_
        have hpP := Nat.prime_of_mem_primesLE hp
        have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpP.one_le)
        rw [wgt_ratio n hn p hpP]
        unfold rho
        rw [goldbachSieveDensity_prime n p hpP]
        split <;> ring_nf <;> first | rfl | nlinarith [mul_nonneg hlog (inv_nonneg.mpr (Nat.cast_nonneg p : (0:ℝ) ≤ _))]
      _ ≤ _ := by rw [←Finset.mul_sum]; linarith [weighted_harmonic y (by omega)]
  have hmass : 0 ≤ mass n y := Finset.prod_nonneg (fun p hp => by
    linarith [wgt_pos n hn p (Nat.prime_of_mem_primesLE hp)])
  have moment : (∑ t ∈ T, W t*Real.log (index t)) ≤ mass n y * (4*Real.log y) := by
    calc
      _ = ∑ t ∈ y.primesLE.powerset, (∏ p ∈ t, wgt n p)*(∑ p ∈ t, Real.log p) :=
        sum_congr rfl (fun t ht => by rw [hsumlog t ht]; rfl)
      _ = _ := mean
      _ ≤ _ := mul_le_mul_of_nonneg_left bound hmass
  have hdiff : (∑ t ∈ T, if y^8 < index t then W t else 0) = mass n y - D := by
    rw [← total, show D = _ from denominator_as_sum n y (y^8), ← Finset.sum_sub_distrib]
    apply sum_congr rfl; intro t _; by_cases h : index t ≤ y^8 <;> simp [h,not_lt.mpr,lt_of_not_ge,W]
  have hh := (sum_le_sum heavy_point).trans moment
  rw [← Finset.sum_mul, hdiff] at hh
  have hl : 0 < Real.log y := Real.log_pos (by exact_mod_cast (show 1<y by omega))
  change mass n y ≤ 2*D
  apply (le_of_mul_le_mul_right (a := Real.log y) ?_ hl)
  linarith only [hh]

end
end CentralSelberg


open Filter Topology
namespace CentralSelberg

/-- A small prime cutoff with enough logarithmic length for the denominator. -/
theorem scales :
    ∀ᶠ n : ℕ in atTop, ∃ y : ℕ, 2≤y ∧
       Real.log (n:ℝ) ≤ 32*Real.log ((y:ℝ)+1) ∧
       (((y^8:ℕ):ℝ)^2*(1+Real.log (y^8:ℕ))^4 + 2*(y:ℝ)) * (Real.log n)^2 ≤ 18*n := by
  have hs := (isLittleO_log_rpow_rpow_atTop (6:ℝ) (by norm_num : (0:ℝ)<1/2)).bound (by norm_num : (0:ℝ)<1)
  have hs' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hs
  have hl := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
  filter_upwards [hs',hl,eventually_ge_atTop (2^32:ℕ)] with n hn hlog hn32
  change 1 ≤ Real.log (n:ℝ) at hlog
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hn1 : 1 ≤ (n:ℝ) := by linarith [show (2:ℝ)^32 ≤ n by exact_mod_cast hn32]
  have hbig : (Real.log n)^6 ≤ Real.sqrt n := by
    have hr : (n:ℝ)^(1/2:ℝ) = Real.sqrt n := (Real.sqrt_eq_rpow _).symm
    simpa only [Real.norm_eq_abs, Real.rpow_natCast_mul, Real.rpow_ofNat, abs_of_nonneg (by positivity : 0≤(Real.log n)^6),
      abs_of_nonneg (Real.rpow_nonneg hn0.le _), one_mul, hr, abs_of_nonneg (Real.sqrt_nonneg _)] using hn
  let u : ℝ := (n:ℝ)^(1/32:ℝ)
  let y := ⌊u⌋₊
  have hu : 0≤u := Real.rpow_nonneg hn0.le _
  have hu32 : u^32 = n := by
    rw [show u^32 = (n:ℝ)^((1/32:ℝ)*32) from (Real.rpow_mul_natCast hn0.le _ _).symm]
    norm_num
  have hy2 : 2≤y := by
    apply (Nat.le_floor_iff hu).mpr
    by_contra! h
    have hp := pow_lt_pow_left₀ h hu (by decide : 32≠0)
    rw [hu32] at hp
    exact (not_lt_of_ge (show (2:ℝ)^32 ≤ n by exact_mod_cast hn32)) hp
  have hyp : (0:ℝ)<y := by exact_mod_cast (show 0<y by omega)
  have hyr : (1:ℝ)≤y := by exact_mod_cast (show 1≤y by omega)
  have hlow := pow_le_pow_left₀ hyp.le (Nat.floor_le hu : (y:ℝ) ≤ u) 32
  have hhigh := pow_le_pow_left₀ hu (Nat.lt_floor_add_one u).le 32
  rw [hu32] at hlow hhigh
  have hylog : Real.log (n:ℝ) ≤ 32*Real.log ((y:ℝ)+1) := by
    have hh := Real.log_le_log hn0 hhigh
    simpa only [Real.log_pow, Nat.cast_ofNat, y] using hh
  have hy16 : (y:ℝ)^16 ≤ Real.sqrt n := by
    apply (Real.le_sqrt (by positivity) hn0.le).mpr
    convert hlow using 1 <;> ring
  have hy1 : (y:ℝ) ≤ Real.sqrt n := by
    exact (le_self_pow₀ hyr (by decide : 16≠0)).trans hy16
  have hly : Real.log ((y^8:ℕ):ℝ) ≤ Real.log n := by
    apply Real.log_le_log (by positivity)
    rw [Nat.cast_pow]
    exact (pow_le_pow_right₀ hyr (by decide : 8≤32)).trans hlow
  have hp4 : (1+Real.log ((y^8:ℕ):ℝ))^4 ≤ (2*Real.log n)^4 :=
    pow_le_pow_left₀ (by have := Real.log_nonneg (show (1:ℝ)≤(y^8:ℕ) by exact_mod_cast (Nat.one_le_pow _ _ (by omega : 1≤y))); linarith) (by linarith) _
  rw [Nat.cast_pow] at hp4
  have hsqr := Real.sq_sqrt hn0.le
  have hmain : Real.sqrt n*(Real.log n)^6 ≤ n := by nlinarith [mul_le_mul_of_nonneg_left hbig (Real.sqrt_nonneg n)]
  have hminor : Real.sqrt n*(Real.log n)^2 ≤ n :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlog (by decide : 2≤6)) (Real.sqrt_nonneg n)).trans hmain
  refine ⟨y,hy2,hylog,?_⟩
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.sqrt n*(2*Real.log n)^4 + 2*Real.sqrt n)*(Real.log n)^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply add_le_add _ (by linarith only [hy1])
      apply mul_le_mul (by convert hy16 using 1 <;> ring) hp4 (by positivity) (Real.sqrt_nonneg n)
    _ ≤ _ := by linarith only [hmain,hminor]

end CentralSelberg

open Finset Filter OAI.Problem337
namespace CentralSelberg
noncomputable section

def w (k : ℕ) : ℝ := if k.Prime then Real.log k else 0
def C (n : ℕ) : ℝ := ∑ p ∈ (range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n), w p*w (n-p)

theorem center_card (n : ℕ) (hn : 2 ≤ n) : C n ≤ ((PrimePairSieve.primePairs n).card:ℝ)*(Real.log n)^2 := by
  let T := (range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n)
  have hw (k : ℕ) (hk : k.Prime) : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk.one_le)
  calc
    _ ≤ ∑ p ∈ T, if p∈PrimePairSieve.primePairs n then (Real.log n)^2 else 0 := by
      refine sum_le_sum fun p hp => ?_
      obtain ⟨hpx,h1,h2⟩ := Finset.mem_filter.mp hp
      have hp' := Finset.mem_range.mp hpx
      by_cases hpP : p.Prime
      · by_cases hqP : (n-p).Prime
        · have mem : p∈PrimePairSieve.primePairs n := Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨hpP.one_le, by have := hqP.one_le; omega⟩, hpP,hqP⟩
          rw [if_pos mem, w, if_pos hpP, w, if_pos hqP, pow_two]
          exact mul_le_mul
            (Real.log_le_log (by exact_mod_cast hpP.pos) (by exact_mod_cast (show p≤n by omega)))
            (Real.log_le_log (by exact_mod_cast hqP.pos) (by exact_mod_cast Nat.sub_le n p))
            (hw _ hqP) (Real.log_nonneg (by exact_mod_cast (show 1≤n by omega)))
        · simp [w,hqP,PrimePairSieve.primePairs]
      · simp [w,hpP,PrimePairSieve.primePairs]
    _ = ((T.filter (·∈PrimePairSieve.primePairs n)).card:ℝ)*(Real.log n)^2 := by rw [←sum_filter]; simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card (fun p hp => (mem_filter.mp hp).2))) (sq_nonneg _)

theorem central_upper :
    ∃ K : ℝ, 0<K ∧ ∃ X : ℕ, ∀ n≥X, Even n → C n ≤ K*(n:ℝ)* singular n := by
  obtain ⟨X,hX⟩ := eventually_atTop.mp scales
  refine ⟨4114,by norm_num,max X 2,?_⟩
  intro n hn he
  have hn2 : 2 ≤ n := (le_max_right ..).trans hn
  have hn0 : 0<n := by omega
  obtain ⟨y,hy,hlog,herr⟩ := hX n ((le_max_left ..).trans hn)
  have he' : 2∣n := even_iff_two_dvd.mp he
  have zpos : 1≤ y^8 := Nat.one_le_pow _ _ (by omega)
  let D := GoldbachSelberg.denominator n (primorial y) (y^8)
  have hD : 0<D := GoldbachSelberg.denominator_pos n _ he' (squarefree_primorial _) zpos
  have hsing := singular_one_le n
  have hDen : (Real.log n)^2 ≤ 4096 * singular n * D := by
    have hp : 0≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1≤n by omega))
    have hsq := pow_le_pow_left₀ hp hlog 2
    have hEu := euler_mass n y he' hn0
    have hcut := retained n y he' hy
    change _ ≤ 2*singular n * mass n y at hEu
    change mass n y ≤ 2*D at hcut
    nlinarith only [hsq,hEu,mul_le_mul_of_nonneg_left hcut (a := singular n) (by linarith)]
  have first : (((n-1:ℕ):ℝ)/D)*(Real.log n)^2 ≤ 4096*(n:ℝ)*singular n := by
    have hnle : ((n-1:ℕ):ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
    calc
      _ ≤ ((n:ℝ)/D)*(Real.log n)^2 := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hnle hD.le) (sq_nonneg _)
      _ ≤ ((n:ℝ)/D)*(4096*singular n*D) := mul_le_mul_of_nonneg_left hDen (by positivity)
      _ = _ := by field_simp
  have hcard : ((Nat.primesLE y).card:ℝ) ≤ y := by
    exact_mod_cast Finset.card_le_card (s := y.primesLE) (t := Icc 1 y) (fun p hp =>
      Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hp).one_le,(Nat.mem_primesLE.mp hp).1⟩) |>.trans_eq (by simp)
  have hs := GoldbachSelberg.primePairs_le n (primorial y) he' (squarefree_primorial _) zpos
  rw [primeFactors_primorial] at hs
  change _ ≤ ((n-1:ℕ):ℝ)/D + _ + _ at hs
  have hb := center_card n hn2
  have heP := mul_le_mul_of_nonneg_right hs (sq_nonneg (Real.log n))
  have hbc := mul_le_mul_of_nonneg_right hcard (sq_nonneg (Real.log n))
  have hsn := mul_le_mul_of_nonneg_left hsing (Nat.cast_nonneg (α:=ℝ) n)
  nlinarith only [hb, heP, hbc, herr, first, hsn]

end
end CentralSelberg

open Filter Topology
namespace CentralSelberg

theorem scales2 :
    ∀ᶠ n : ℕ in atTop, ∃ y : ℕ, 2≤y ∧ y ≤ n ∧
       Real.log (n:ℝ) ≤ 32*Real.log ((y:ℝ)+1) ∧
       (((y^8:ℕ):ℝ)^2*(1+Real.log (y^8:ℕ))^4 + 2*(y:ℝ)) * (Real.log n)^2 ≤ 18*n := by
  have hs := (isLittleO_log_rpow_rpow_atTop (6:ℝ) (by norm_num : (0:ℝ)<1/2)).bound (by norm_num : (0:ℝ)<1)
  have hs' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hs
  have hl := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
  filter_upwards [hs',hl,eventually_ge_atTop (2^32:ℕ)] with n hn hlog hn32
  change 1 ≤ Real.log (n:ℝ) at hlog
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hn1 : 1 ≤ (n:ℝ) := by linarith [show (2:ℝ)^32 ≤ n by exact_mod_cast hn32]
  have hbig : (Real.log n)^6 ≤ Real.sqrt n := by
    have hr : (n:ℝ)^(1/2:ℝ) = Real.sqrt n := (Real.sqrt_eq_rpow _).symm
    simpa only [Real.norm_eq_abs, Real.rpow_natCast_mul, Real.rpow_ofNat, abs_of_nonneg (by positivity : 0≤(Real.log n)^6),
      abs_of_nonneg (Real.rpow_nonneg hn0.le _), one_mul, hr, abs_of_nonneg (Real.sqrt_nonneg _)] using hn
  let u : ℝ := (n:ℝ)^(1/32:ℝ)
  let y := ⌊u⌋₊
  have hu : 0≤u := Real.rpow_nonneg hn0.le _
  have hu32 : u^32 = n := by
    rw [show u^32 = (n:ℝ)^((1/32:ℝ)*32) from (Real.rpow_mul_natCast hn0.le _ _).symm]
    norm_num
  have hy2 : 2≤y := by
    apply (Nat.le_floor_iff hu).mpr
    by_contra! h
    have hp := pow_lt_pow_left₀ h hu (by decide : 32≠0)
    rw [hu32] at hp
    exact (not_lt_of_ge (show (2:ℝ)^32 ≤ n by exact_mod_cast hn32)) hp
  have hyn : y ≤ n := by
    have h1 : (y:ℝ) ≤ u := Nat.floor_le hu
    have h2 : u ≤ (n:ℝ) := by
      have hx := Real.rpow_le_rpow_of_exponent_le hn1 (show (1/32:ℝ) ≤ 1 by norm_num)
      simpa [u] using hx
    exact_mod_cast h1.trans h2
  have hyp : (0:ℝ)<y := by exact_mod_cast (show 0<y by omega)
  have hyr : (1:ℝ)≤y := by exact_mod_cast (show 1≤y by omega)
  have hlow := pow_le_pow_left₀ hyp.le (Nat.floor_le hu : (y:ℝ) ≤ u) 32
  have hhigh := pow_le_pow_left₀ hu (Nat.lt_floor_add_one u).le 32
  rw [hu32] at hlow hhigh
  have hylog : Real.log (n:ℝ) ≤ 32*Real.log ((y:ℝ)+1) := by
    have hh := Real.log_le_log hn0 hhigh
    simpa only [Real.log_pow, Nat.cast_ofNat, y] using hh
  have hy16 : (y:ℝ)^16 ≤ Real.sqrt n := by
    apply (Real.le_sqrt (by positivity) hn0.le).mpr
    convert hlow using 1 <;> ring
  have hy1 : (y:ℝ) ≤ Real.sqrt n := by
    exact (le_self_pow₀ hyr (by decide : 16≠0)).trans hy16
  have hly : Real.log ((y^8:ℕ):ℝ) ≤ Real.log n := by
    apply Real.log_le_log (by positivity)
    rw [Nat.cast_pow]
    exact (pow_le_pow_right₀ hyr (by decide : 8≤32)).trans hlow
  have hp4 : (1+Real.log ((y^8:ℕ):ℝ))^4 ≤ (2*Real.log n)^4 :=
    pow_le_pow_left₀ (by have := Real.log_nonneg (show (1:ℝ)≤(y^8:ℕ) by exact_mod_cast (Nat.one_le_pow _ _ (by omega : 1≤y))); linarith) (by linarith) _
  rw [Nat.cast_pow] at hp4
  have hsqr := Real.sq_sqrt hn0.le
  have hmain : Real.sqrt n*(Real.log n)^6 ≤ n := by nlinarith [mul_le_mul_of_nonneg_left hbig (Real.sqrt_nonneg n)]
  have hminor : Real.sqrt n*(Real.log n)^2 ≤ n :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlog (by decide : 2≤6)) (Real.sqrt_nonneg n)).trans hmain
  refine ⟨y,hy2,hyn,hylog,?_⟩
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.sqrt n*(2*Real.log n)^4 + 2*Real.sqrt n)*(Real.log n)^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply add_le_add _ (by linarith only [hy1])
      apply mul_le_mul (by convert hy16 using 1 <;> ring) hp4 (by positivity) (Real.sqrt_nonneg n)
    _ ≤ _ := by linarith only [hmain,hminor]

end CentralSelberg

noncomputable section

def CofRoot (u r d : ℕ) :=
  {x : ZMod d // x * ((r : ZMod d) * x - (u : ZMod d)) = 0}

def cofRootCount (u r d : ℕ) : ℕ :=
  Nat.card (CofRoot u r d)

def cofRootEquiv (u r a b : ℕ) (hab : a.Coprime b) :
    CofRoot u r (a * b) ≃ CofRoot u r a × CofRoot u r b := by
  let e := ZMod.chineseRemainder hab
  apply (Equiv.subtypeEquiv e.toEquiv ?_).trans Equiv.subtypeProdEquivProd
  intro x
  change x * ((r : ZMod (a * b)) * x - (u : ZMod (a * b))) = 0 ↔
    (e x).1 * ((r : ZMod a) * (e x).1 - (u : ZMod a)) = 0 ∧
      (e x).2 * ((r : ZMod b) * (e x).2 - (u : ZMod b)) = 0
  have h := e.injective.eq_iff
    (a := x * ((r : ZMod (a * b)) * x - (u : ZMod (a * b)))) (b := 0)
  simpa only [map_mul, map_sub, map_natCast, map_zero, Prod.mk_zero_zero,
    Prod.mul_def, Prod.sub_def, Prod.fst_natCast, Prod.snd_natCast,
    Prod.mk.injEq, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] using h.symm

theorem cofRootCount_mul (u r a b : ℕ) (hab : a.Coprime b) :
    cofRootCount u r (a * b) = cofRootCount u r a * cofRootCount u r b := by
  unfold cofRootCount
  rw [Nat.card_congr (cofRootEquiv u r a b hab), Nat.card_prod]

@[simp] theorem cofRootCount_one (u r : ℕ) : cofRootCount u r 1 = 1 := by
  unfold cofRootCount CofRoot
  have e : {x : ZMod 1 // x * ((r : ZMod 1) * x - (u : ZMod 1)) = 0} ≃ ZMod 1 :=
    Equiv.subtypeUnivEquiv (fun x => Subsingleton.elim _ _)
  rw [Nat.card_congr e, Nat.card_zmod]

theorem cofRootCount_prod_primes (u r : ℕ) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    cofRootCount u r (∏ p ∈ s, p) = ∏ p ∈ s, cofRootCount u r p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      have hpp := hs p (Finset.mem_insert_self p s)
      have hsp : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
      have hcop : p.Coprime (∏ q ∈ s, q) := by
        apply Nat.Coprime.prod_right
        intro q hq
        apply (Nat.coprime_primes hpp (hsp q hq)).mpr
        intro heq
        exact hp (heq ▸ hq)
      rw [Finset.prod_insert hp, cofRootCount_mul u r p _ hcop, ih hsp, Finset.prod_insert hp]

theorem cofRootCount_squarefree (u r d : ℕ) (hd : Squarefree d) :
    cofRootCount u r d = ∏ p ∈ d.primeFactors, cofRootCount u r p := by
  calc
    cofRootCount u r d = cofRootCount u r (∏ p ∈ d.primeFactors, p) := by
          rw [Nat.prod_primeFactors_of_squarefree hd]
    _ = ∏ p ∈ d.primeFactors, cofRootCount u r p :=
      cofRootCount_prod_primes u r d.primeFactors
        (fun p hp => (Nat.mem_primeFactors.mp hp).1)

theorem cofRootCount_eq_filter_card (u r d : ℕ) [NeZero d] :
    cofRootCount u r d =
      (Finset.univ.filter
        (fun x : ZMod d => x * ((r : ZMod d) * x - (u : ZMod d)) = 0)).card := by
  classical
  unfold cofRootCount CofRoot
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem cofRootCount_eq_goldbach (u r d : ℕ) [NeZero d] (h : Nat.Coprime r d) :
    cofRootCount u r d = goldbachSieveRootCount u d := by
  classical
  have hbij : Function.Bijective (fun x : ZMod d => (r : ZMod d) * x) := by
    have hu : IsUnit (r : ZMod d) := (ZMod.isUnit_iff_coprime r d).mpr h
    obtain ⟨v, hv⟩ := hu
    constructor
    · intro x y hxy
      have hxy' := congrArg (fun z : ZMod d => ((v⁻¹ : (ZMod d)ˣ) : ZMod d) * z) hxy
      simp only [← hv, ← mul_assoc, Units.inv_mul, one_mul] at hxy'
      exact hxy'
    · intro y
      refine ⟨((v⁻¹ : (ZMod d)ˣ) : ZMod d) * y, ?_⟩
      have hz : (r : ZMod d) * (((v⁻¹ : (ZMod d)ˣ) : ZMod d) * y) = y := by
        rw [← hv, ← mul_assoc, Units.mul_inv, one_mul]
      exact hz
  have key : ∀ x : ZMod d, (x * ((r : ZMod d) * x - (u : ZMod d)) = 0) ↔
      ((r : ZMod d) * x) * ((u : ZMod d) - (r : ZMod d) * x) = 0 := by
    intro x
    have halg : (r : ZMod d) * (x * ((r : ZMod d) * x - (u : ZMod d)))
        = -((r : ZMod d) * x * ((u : ZMod d) - (r : ZMod d) * x)) := by ring
    constructor
    · intro hx
      have h1 : (r : ZMod d) * (x * ((r : ZMod d) * x - (u : ZMod d))) = 0 := by
        rw [hx, mul_zero]
      have h2 : -((r : ZMod d) * x * ((u : ZMod d) - (r : ZMod d) * x)) = 0 := by
        rw [← halg]
        exact h1
      exact neg_eq_zero.mp h2
    · intro hx
      have h1 : (r : ZMod d) * (x * ((r : ZMod d) * x - (u : ZMod d))) = 0 := by
        rw [halg, hx, neg_zero]
      have hz : (r : ZMod d) * (x * ((r : ZMod d) * x - (u : ZMod d)))
          = (r : ZMod d) * 0 := by rw [h1, mul_zero]
      exact hbij.1 hz
  unfold cofRootCount goldbachSieveRootCount
  apply Nat.card_congr
  refine Equiv.ofBijective
    (fun x : CofRoot u r d =>
      (⟨(r : ZMod d) * x.val, (key x.val).mp x.property⟩ : GoldbachSieveRoot u d)) ?_
  constructor
  · intro x y hxy
    have hxy' := congrArg (fun z : GoldbachSieveRoot u d => z.val) hxy
    apply Subtype.ext
    exact hbij.1 hxy'
  · intro y
    obtain ⟨x₀, hx₀⟩ := hbij.2 y.val
    have hx₀' : (r : ZMod d) * x₀ = y.val := hx₀
    have hprop : x₀ * ((r : ZMod d) * x₀ - (u : ZMod d)) = 0 := by
      rw [key x₀, hx₀']
      exact y.property
    refine ⟨⟨x₀, hprop⟩, ?_⟩
    apply Subtype.ext
    exact hx₀'

theorem cofRootCount_prime_of_dvd (u r p : ℕ) (hp : p.Prime) (hdvd : p ∣ r)
    (hu : ¬ p ∣ u) : cofRootCount u r p = 1 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hr0 : (r : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff r p).mpr hdvd
  have hu0 : (u : ZMod p) ≠ 0 := by
    intro hz
    exact hu ((ZMod.natCast_eq_zero_iff u p).mp hz)
  rw [cofRootCount_eq_filter_card]
  have hset : (Finset.univ.filter
      (fun x : ZMod p => x * ((r : ZMod p) * x - (u : ZMod p)) = 0)) = {0} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [hr0, zero_mul, zero_sub, mul_eq_zero, neg_eq_zero]
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact hx
      · exact absurd hx hu0
    · intro hx
      subst hx
      simp
  rw [hset, Finset.card_singleton]

theorem cofRootCount_two_prime (r p : ℕ) (hp : p.Prime) (hro : Odd r) :
    cofRootCount 2 r p = if p ∣ 2 * r then 1 else 2 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  by_cases hdvd : p ∣ r
  · have hp2 : p ≠ 2 := by
      intro heq
      subst heq
      obtain ⟨k, hk⟩ := hro
      obtain ⟨m, hm⟩ := hdvd
      omega
    have hu : ¬ (p ∣ 2) := by
      intro hd
      have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
      have htl := hp.two_le
      exact hp2 (by omega)
    have h1 : cofRootCount 2 r p = 1 := cofRootCount_prime_of_dvd 2 r p hp hdvd hu
    rw [h1, if_pos (hp.dvd_mul.mpr (Or.inr hdvd))]
  · have hcop : Nat.Coprime p r := hp.coprime_iff_not_dvd.mpr hdvd
    have hrp : Nat.Coprime r p := hcop.symm
    have heq : p ∣ 2 * r ↔ p ∣ 2 := by
      constructor
      · intro hx
        rcases hp.dvd_mul.mp hx with h1 | h1
        · exact h1
        · exact absurd h1 hdvd
      · intro hx
        exact hp.dvd_mul.mpr (Or.inl hx)
    rw [cofRootCount_eq_goldbach 2 r p hrp, goldbachSieveRootCount_prime 2 p hp]
    by_cases h2 : p ∣ 2
    · rw [if_pos h2, if_pos (heq.mpr h2)]
    · rw [if_neg h2, if_neg (fun hx => h2 (heq.mp hx))]

theorem cofRootCount_two_eq (r d : ℕ) (hro : Odd r) (hd : Squarefree d) :
    cofRootCount 2 r d = goldbachSieveRootCount (2 * r) d := by
  rw [cofRootCount_squarefree 2 r d hd, goldbachSieveRootCount_squarefree (2*r) d hd]
  apply Finset.prod_congr rfl
  intro p hp
  exact cofRootCount_two_prime r p (Nat.mem_primeFactors.mp hp).1 hro

theorem cof_dvd_iff_zmod (u r d s : ℕ) (h : u ≤ r * s) :
    d ∣ s * (r * s - u) ↔
      (s : ZMod d) * ((r : ZMod d) * (s : ZMod d) - (u : ZMod d)) = 0 := by
  have h1 : ((r * s - u : ℕ) : ZMod d) = (r : ZMod d) * (s : ZMod d) - (u : ZMod d) := by
    rw [Nat.cast_sub h, Nat.cast_mul]
  have h2 : ((s * (r * s - u) : ℕ) : ZMod d) =
      (s : ZMod d) * ((r : ZMod d) * (s : ZMod d) - (u : ZMod d)) := by
    rw [Nat.cast_mul, h1]
  rw [← h2, ZMod.natCast_eq_zero_iff]

theorem cof_count_discrepancy (r Y d : ℕ) [NeZero d] (hY : 1 ≤ Y) (hr : 2 ≤ r) :
    |(((Finset.Ioc Y (2*Y)).filter (fun s => d ∣ s * (r*s - 2))).card : ℝ) -
      (Y:ℝ) * cofRootCount 2 r d / d| ≤ cofRootCount 2 r d := by
  classical
  have hI : Finset.Ioc Y (2*Y) = Finset.Ico (Y+1) ((Y+1) + Y) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have hfilt : (Finset.Ioc Y (2*Y)).filter (fun s => d ∣ s * (r*s - 2)) =
      (Finset.Ico (Y+1) ((Y+1)+Y)).filter
        (fun s : ℕ => (s : ZMod d) * ((r : ZMod d) * (s : ZMod d) - (2 : ZMod d)) = 0) := by
    rw [← hI]
    apply Finset.filter_congr
    intro s hs
    have hs1 : 1 ≤ s := by have := (Finset.mem_Ioc.mp hs).1; omega
    have h2 : (2:ℕ) ≤ r * s := by
      calc (2:ℕ) ≤ r := hr
        _ = r * 1 := (Nat.mul_one r).symm
        _ ≤ r * s := Nat.mul_le_mul (le_refl r) hs1
    exact cof_dvd_iff_zmod 2 r d s h2
  rw [hfilt, cofRootCount_eq_filter_card]
  exact zmod_predicate_Ico_discrepancy d
    (fun x : ZMod d => x * ((r : ZMod d) * x - (2 : ZMod d)) = 0) (Y+1) Y

theorem cof_density_discrepancy (r Y d : ℕ) [NeZero d] (hY : 1 ≤ Y) (hr : 2 ≤ r)
    (hro : Odd r) (hd : Squarefree d) :
    |(((Finset.Ioc Y (2*Y)).filter (fun s => d ∣ s * (r*s - 2))).card : ℝ) -
      goldbachSieveDensity (2*r) d * (Y:ℝ)| ≤ goldbachSieveRootCount (2*r) d := by
  have h := cof_count_discrepancy r Y d hY hr
  rw [cofRootCount_two_eq r d hro hd] at h
  simpa only [goldbachSieveDensity_apply, div_mul_eq_mul_div, mul_div_assoc, mul_comm] using h

def cofactorSieve (Y r P : ℕ) (hP : Squarefree P) : BoundingSieve where
  support := (Finset.Ioc Y (2*Y)).image (fun s => s * (r*s - 2))
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := PrimePairSieve.fiberWeight (Finset.Ioc Y (2*Y)) (fun s => s * (r*s - 2))
  weights_nonneg := fun n => PrimePairSieve.fiberWeight_nonneg _ _ n
  totalMass := (Y : ℝ)
  nu := goldbachSieveDensity (2*r)
  nu_mult := goldbachSieveDensity_isMultiplicative (2*r)
  nu_pos_of_prime := fun p hp _ => goldbachSieveDensity_prime_pos (2*r) p hp
  nu_lt_one_of_prime := fun p hp _ =>
    goldbachSieveDensity_prime_lt_one (2*r) p hp (fun _ => ⟨r, rfl⟩)

theorem cofactorSieve_totalMass (Y r P : ℕ) (hP : Squarefree P) :
    (cofactorSieve Y r P hP).totalMass = (Y : ℝ) := rfl

theorem cofactorSieve_multSum (Y r P : ℕ) (hP : Squarefree P) (d : ℕ) :
    (cofactorSieve Y r P hP).multSum d =
      ((((Finset.Ioc Y (2*Y)).filter (fun s => d ∣ s * (r*s - 2))).card : ℕ) : ℝ) :=
  PrimePairSieve.sum_fiberWeight_indicator _ _ (fun y => d ∣ y)

theorem cofactorSieve_siftedSum (Y r P : ℕ) (hP : Squarefree P) :
    (cofactorSieve Y r P hP).siftedSum =
      ((((Finset.Ioc Y (2*Y)).filter
        (fun s => P.Coprime (s * (r*s - 2)))).card : ℕ) : ℝ) :=
  PrimePairSieve.sum_fiberWeight_indicator _ _ (fun y => P.Coprime y)

theorem cofactorSieve_rem (Y r P : ℕ) (hP : Squarefree P) (d : ℕ) :
    (cofactorSieve Y r P hP).rem d =
      ((((Finset.Ioc Y (2*Y)).filter (fun s => d ∣ s * (r*s - 2))).card : ℕ) : ℝ) -
        goldbachSieveDensity (2*r) d * (Y : ℝ) := by
  rw [BoundingSieve.rem, cofactorSieve_multSum]
  rfl

theorem cof_normalizer (Y r P z : ℕ) (hP : Squarefree P) :
    SelbergOptimal.normalizer (cofactorSieve Y r P hP) z =
      GoldbachSelberg.denominator (2*r) P z := by
  unfold SelbergOptimal.normalizer GoldbachSelberg.denominator
  apply sum_congr rfl
  intro d hd
  rw [BoundingSieve.selbergTerms_apply]
  rfl

theorem cof_denominator_pos (Y r P : ℕ) (hP : Squarefree P) {z : ℕ} (hz : 1 ≤ z) :
    0 < GoldbachSelberg.denominator (2*r) P z := by
  rw [← cof_normalizer Y r P z hP]
  exact SelbergOptimal.normalizer_pos _ hz

theorem cof_rem_bound (Y r P d : ℕ) (hY : 1 ≤ Y) (hr : 2 ≤ r) (hro : Odd r)
    (hP : Squarefree P) (hd : Squarefree d) [NeZero d] :
    |(cofactorSieve Y r P hP).rem d| ≤ goldbachSieveRootCount (2*r) d := by
  rw [cofactorSieve_rem]
  exact cof_density_discrepancy r Y d hY hr hro hd

theorem cof_rem_lcm_bound (Y r P : ℕ) (hY : 1 ≤ Y) (hr : 2 ≤ r) (hro : Odd r)
    (hP : Squarefree P) (a : ℕ) (ha : a ∈ P.divisors) (b : ℕ) (hb : b ∈ P.divisors) :
    |(cofactorSieve Y r P hP).rem (Nat.lcm a b)| ≤
      (2 : ℝ) ^ a.primeFactors.card * (2 : ℝ) ^ b.primeFactors.card := by
  let : NeZero a := ⟨(Nat.pos_of_mem_divisors ha).ne'⟩
  let : NeZero b := ⟨(Nat.pos_of_mem_divisors hb).ne'⟩
  let : NeZero (Nat.lcm a b) := ⟨Nat.lcm_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  have hsq : Squarefree (Nat.lcm a b) :=
    hP.squarefree_of_dvd (Nat.lcm_dvd (Nat.dvd_of_mem_divisors ha) (Nat.dvd_of_mem_divisors hb))
  have ha2 := goldbachSieveRootCount_le_two_pow (2*r) a
    (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors ha))
  have hb2 := goldbachSieveRootCount_le_two_pow (2*r) b
    (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hb))
  calc
    _ ≤ (goldbachSieveRootCount (2*r) (Nat.lcm a b) : ℝ) :=
      cof_rem_bound Y r P _ hY hr hro hP hsq
    _ ≤ (goldbachSieveRootCount (2*r) a : ℝ) * goldbachSieveRootCount (2*r) b := by
      exact_mod_cast goldbachSieveRootCount_lcm_le (2*r) a b
    _ ≤ _ := by exact_mod_cast Nat.mul_le_mul ha2 hb2

theorem cof_card_le_sifted (Y r P : ℕ) (hY : 1 ≤ Y) (hr : 2 ≤ r) (hro : Odd r)
    (hP : Squarefree P) {z : ℕ} (hz : 1 ≤ z) :
    ((((Finset.Ioc Y (2*Y)).filter
        (fun s => P.Coprime (s * (r*s - 2)))).card : ℕ) : ℝ) ≤
      (Y:ℝ) / GoldbachSelberg.denominator (2*r) P z +
        (z:ℝ)^2 * (1 + Real.log z)^4 := by
  have he := SelbergOptimal.siftedSum_le_log_error (cofactorSieve Y r P hP) hz
    (fun a ha b hb => cof_rem_lcm_bound Y r P hY hr hro hP a ha b hb)
  rw [cofactorSieve_siftedSum, cofactorSieve_totalMass, cof_normalizer Y r P z hP] at he
  exact he

theorem singular_two_mul (r : ℕ) (hrp : r.Prime) (hr2 : 2 < r) :
    CentralSelberg.singular (2*r) = 1 + 1/((r:ℝ)-2) := by
  have hset : (2*r).primeFactors.filter (fun p => 2 < p) = {r} := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hpp, hpd, -⟩, hp2⟩
      have hpr : p ∣ r := by
        rcases hpp.dvd_mul.mp hpd with h1 | h1
        · exfalso
          have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h1
          have := hpp.two_le
          omega
        · exact h1
      exact (hrp.dvd_iff_eq hpp.ne_one).mp hpr |>.symm
    · intro hp
      subst hp
      exact ⟨⟨hrp, ⟨2, by ring⟩, Nat.mul_ne_zero (by norm_num) (by omega)⟩, hr2⟩
  unfold CentralSelberg.singular
  rw [hset]
  simp

theorem singular_two_mul_le (r : ℕ) (hrp : r.Prime) (hr2 : 2 < r) :
    CentralSelberg.singular (2*r) ≤ 2 := by
  rw [singular_two_mul r hrp hr2]
  have h3 : (3:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr2
  have h1 : (0:ℝ) < (r:ℝ) - 2 := by linarith
  have hle : (1:ℝ)/((r:ℝ)-2) ≤ 1 := by
    rw [div_le_one h1]
    linarith
  linarith

theorem cofactor_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y r : ℕ), 3 ≤ Y → r.Prime → 2 < r →
      ((((Finset.Ioc Y (2*Y)).filter (fun s => s.Prime ∧ (r*s-2).Prime)).card:ℕ):ℝ) ≤
        C*(Y:ℝ)/(Real.log Y)^2 := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp CentralSelberg.scales2
  refine ⟨8210 + (Real.log ((max X 3 : ℕ) : ℝ))^2, by positivity, ?_⟩
  intro Y r hY hrp hr2
  have hY1 : 1 ≤ Y := by omega
  have hYpos : 0 < Y := by omega
  have hlogYpos : 0 < Real.log Y := Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hr2le : 2 ≤ r := by omega
  have hro : Odd r := hrp.odd_of_ne_two (by omega)
  have hcardIoc : (Finset.Ioc Y (2*Y)).card = Y := by
    rw [Nat.card_Ioc]
    omega
  rw [le_div_iff₀ (pow_pos hlogYpos 2)]
  by_cases hcase : Y < max X 3
  · have hcardT : ((((Finset.Ioc Y (2*Y)).filter
        (fun s => s.Prime ∧ (r*s-2).Prime)).card : ℕ) : ℝ) ≤ (Y : ℝ) := by
      have h1 : ((Finset.Ioc Y (2*Y)).filter
          (fun s => s.Prime ∧ (r*s-2).Prime)).card ≤ (Finset.Ioc Y (2*Y)).card := by
        apply Finset.card_le_card
        intro s hs
        exact (Finset.mem_filter.mp hs).1
      rw [hcardIoc] at h1
      exact_mod_cast h1
    have hmono : Real.log Y ≤ Real.log ((max X 3 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast hYpos) (by exact_mod_cast (le_of_lt hcase))
    have hsq : (Real.log Y)^2 ≤ (Real.log ((max X 3 : ℕ) : ℝ))^2 :=
      pow_le_pow_left₀ hlogYpos.le hmono 2
    calc _ ≤ (Y:ℝ) * (Real.log Y)^2 :=
          mul_le_mul_of_nonneg_right hcardT (sq_nonneg (Real.log Y))
      _ ≤ (Y:ℝ) * (Real.log ((max X 3 : ℕ) : ℝ))^2 :=
          mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg Y)
      _ ≤ (8210 + (Real.log ((max X 3 : ℕ) : ℝ))^2) * (Y:ℝ) := by
          calc (Y:ℝ) * (Real.log ((max X 3 : ℕ) : ℝ))^2
              ≤ (Y:ℝ) * (Real.log ((max X 3 : ℕ) : ℝ))^2 + 8210 * (Y:ℝ) :=
                le_add_of_nonneg_right (by positivity)
            _ = (8210 + (Real.log ((max X 3 : ℕ) : ℝ))^2) * (Y:ℝ) := by ring
  · have hcase' : max X 3 ≤ Y := by omega
    obtain ⟨y, hy2, hyn, hlog, herr⟩ := hX Y ((le_max_left X 3).trans hcase')
    have hzpos : 1 ≤ y^8 := Nat.one_le_pow _ _ (by omega)
    have hsing := singular_two_mul_le r hrp hr2
    have hone := CentralSelberg.singular_one_le (2*r)
    have hEu := CentralSelberg.euler_mass (2*r) y ⟨r, rfl⟩ (by omega)
    have hcut := CentralSelberg.retained (2*r) y ⟨r, rfl⟩ hy2
    change _ ≤ 2*CentralSelberg.singular (2*r)*CentralSelberg.mass (2*r) y at hEu
    change CentralSelberg.mass (2*r) y ≤ 2*_ at hcut
    have hmass0 : (0:ℝ) ≤ CentralSelberg.mass (2*r) y := by
      apply Finset.prod_nonneg
      intro p hp
      have := CentralSelberg.wgt_pos (2*r) ⟨r, rfl⟩ p (Nat.prime_of_mem_primesLE hp)
      linarith
    have h1 : (Real.log ((y:ℝ)+1))^2 ≤
        4 * CentralSelberg.singular (2*r) * GoldbachSelberg.denominator (2*r) (primorial y) (y^8) := by
      calc _ ≤ 2*CentralSelberg.singular (2*r)*CentralSelberg.mass (2*r) y := hEu
        _ ≤ 2*CentralSelberg.singular (2*r)*(2*GoldbachSelberg.denominator (2*r) (primorial y) (y^8)) := by
            apply mul_le_mul_of_nonneg_left hcut
            nlinarith [hone]
        _ = _ := by ring
    have hDpos : 0 < GoldbachSelberg.denominator (2*r) (primorial y) (y^8) :=
      cof_denominator_pos Y r _ (squarefree_primorial y) hzpos
    have h2 : (Real.log ((y:ℝ)+1))^2 ≤
        8 * GoldbachSelberg.denominator (2*r) (primorial y) (y^8) := by
      calc _ ≤ 4*CentralSelberg.singular (2*r)*GoldbachSelberg.denominator (2*r) (primorial y) (y^8) := h1
        _ ≤ 4*2*GoldbachSelberg.denominator (2*r) (primorial y) (y^8) := by
            apply mul_le_mul_of_nonneg_right _ hDpos.le
            nlinarith [hsing]
        _ = _ := by ring
    have hsq : (Real.log Y)^2 ≤ (32*Real.log ((y:ℝ)+1))^2 :=
      pow_le_pow_left₀ hlogYpos.le hlog 2
    have hDen : (Real.log Y)^2 ≤
        8192 * GoldbachSelberg.denominator (2*r) (primorial y) (y^8) := by
      calc _ ≤ (32*Real.log ((y:ℝ)+1))^2 := hsq
        _ = 1024 * (Real.log ((y:ℝ)+1))^2 := by ring
        _ ≤ 1024 * (8*GoldbachSelberg.denominator (2*r) (primorial y) (y^8)) := by
            exact mul_le_mul_of_nonneg_left h2 (by norm_num)
        _ = _ := by ring
    have hD0 : GoldbachSelberg.denominator (2*r) (primorial y) (y^8) ≠ 0 := hDpos.ne'
    have hfirst : ((Y:ℝ)/GoldbachSelberg.denominator (2*r) (primorial y) (y^8))*(Real.log Y)^2
        ≤ 8192*(Y:ℝ) := by
      calc _ ≤ ((Y:ℝ)/GoldbachSelberg.denominator (2*r) (primorial y) (y^8)) *
            (8192*GoldbachSelberg.denominator (2*r) (primorial y) (y^8)) := by
            exact mul_le_mul_of_nonneg_left hDen (by positivity)
        _ = _ := by field_simp
    have herr' : (((y^8:ℕ):ℝ)^2*(1+Real.log (y^8:ℕ))^4 + 2*(y:ℝ)) * (Real.log Y)^2 ≤
        18*(Y:ℝ) := by
      have hthis := herr
      push_cast at hthis ⊢
      exact hthis
    have herr2 : ((y^8:ℕ):ℝ)^2*(1+Real.log (y^8:ℕ))^4*(Real.log Y)^2 ≤ 18*(Y:ℝ) := by
      have h0 : (0:ℝ) ≤ 2*(y:ℝ)*(Real.log Y)^2 := by positivity
      nlinarith [herr']
    have hsub : (Finset.Ioc Y (2*Y)).filter (fun s => s.Prime ∧ (r*s-2).Prime) ⊆
        (Finset.Ioc Y (2*Y)).filter
          (fun s => (primorial y).Coprime (s * (r*s - 2))) := by
      intro s hs
      obtain ⟨hsI, hsP, hsQ⟩ := Finset.mem_filter.mp hs
      have hsY : Y < s := (Finset.mem_Ioc.mp hsI).1
      have hsy : ¬ (s ∣ primorial y) := by
        intro hd
        have hmem : s ∈ (primorial y).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hsP, hd, primorial_ne_zero y⟩
        rw [primeFactors_primorial] at hmem
        have := (Nat.mem_primesLE.mp hmem).1
        omega
      have hq : y < r*s - 2 := by
        have h3 : 3 ≤ r := by omega
        have hs1 : Y + 1 ≤ s := by omega
        have hmul : 3*(Y+1) ≤ r*s := Nat.mul_le_mul h3 hs1
        omega
      have hqy : ¬ ((r*s - 2) ∣ primorial y) := by
        intro hd
        have hmem : r*s - 2 ∈ (primorial y).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hsQ, hd, primorial_ne_zero y⟩
        rw [primeFactors_primorial] at hmem
        have := (Nat.mem_primesLE.mp hmem).1
        omega
      refine Finset.mem_filter.mpr ⟨hsI, ?_⟩
      exact ((hsP.coprime_iff_not_dvd.mpr hsy).symm).mul_right
        ((hsQ.coprime_iff_not_dvd.mpr hqy).symm)
    have hcardle : ((((Finset.Ioc Y (2*Y)).filter
        (fun s => s.Prime ∧ (r*s-2).Prime)).card : ℕ) : ℝ) ≤
        (Y:ℝ)/GoldbachSelberg.denominator (2*r) (primorial y) (y^8) +
          ((y^8:ℕ):ℝ)^2*(1+Real.log (y^8:ℕ))^4 := by
      calc _ ≤ ((((Finset.Ioc Y (2*Y)).filter
              (fun s => (primorial y).Coprime (s * (r*s - 2)))).card : ℕ) : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ _ := cof_card_le_sifted Y r (primorial y) hY1 hr2le hro
              (squarefree_primorial y) hzpos
    have hmul := mul_le_mul_of_nonneg_right hcardle (sq_nonneg (Real.log Y))
    calc _ ≤ ((Y:ℝ)/GoldbachSelberg.denominator (2*r) (primorial y) (y^8) +
          ((y^8:ℕ):ℝ)^2*(1+Real.log (y^8:ℕ))^4) * (Real.log Y)^2 := hmul
      _ = ((Y:ℝ)/GoldbachSelberg.denominator (2*r) (primorial y) (y^8)) *
            (Real.log Y)^2 +
          ((y^8:ℕ):ℝ)^2*(1+Real.log (y^8:ℕ))^4 * (Real.log Y)^2 := by ring
      _ ≤ 8192*(Y:ℝ) + 18*(Y:ℝ) := add_le_add hfirst herr2
      _ ≤ (8210 + (Real.log ((max X 3 : ℕ) : ℝ))^2) * (Y:ℝ) := by
          calc 8192*(Y:ℝ) + 18*(Y:ℝ) = 8210*(Y:ℝ) := by ring
            _ ≤ 8210*(Y:ℝ) + (Real.log ((max X 3 : ℕ) : ℝ))^2 * (Y:ℝ) :=
                le_add_of_nonneg_right
                  (mul_nonneg (sq_nonneg (Real.log ((max X 3 : ℕ) : ℝ))) (Nat.cast_nonneg Y))
            _ = (8210 + (Real.log ((max X 3 : ℕ) : ℝ))^2) * (Y:ℝ) := by ring

end

end Conjectures.TwinPrimes.CofactorTwoLinearSieve_aux

theorem Conjectures.TwinPrimes.CofactorTwoLinearSieve : ∃ C : ℝ, 0 < C ∧ ∀ (Y r : ℕ), 3 ≤ Y → r.Prime → 2 < r → ((((Finset.Ioc Y (2*Y)).filter (fun s => s.Prime ∧ (r*s-2).Prime)).card:ℕ):ℝ) ≤ C*(Y:ℝ)/(Real.log Y)^2 := Conjectures.TwinPrimes.CofactorTwoLinearSieve_aux.cofactor_upper

/-! The finite Selberg inequality, the periodic counting estimate and the definitions
of its weights come from `Conjectures.TwinPrimes.CofactorTwoLinearSieve`.
The affine change of variable below applies that sieve to the switched progression. -/

namespace Conjectures.QuadraticPrimes.SwitchedCofactorSmallSieveAux

open Conjectures.TwinPrimes.CofactorTwoLinearSieve_aux
open OAI.Problem337 Finset
noncomputable section

def splitPrimes (y : ℕ) := y.primesLE.filter fun q => q % 4 = 1
def wheel (y : ℕ) := ∏ q ∈ splitPrimes y, q
def value (p r t : ℕ) := 4 * (p*t+r)^2 + 1

theorem mem_split {q y : ℕ} (hq : q ∈ splitPrimes y) :
    q.Prime ∧ q ≤ y ∧ q % 4 = 1 := by
  obtain ⟨h,hm⟩ := mem_filter.mp hq
  exact ⟨Nat.prime_of_mem_primesLE h, (Nat.mem_primesLE.mp h).1, hm⟩

theorem wheel_sq (y : ℕ) : Squarefree (wheel y) := by
  apply (squarefree_primorial y).squarefree_of_dvd
  rw [primorial_eq_prod_primesLE]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)

theorem wheel_factors (y : ℕ) : (wheel y).primeFactors = splitPrimes y :=
  Nat.primeFactors_prod fun q hq => (mem_split hq).1

theorem affine_discrepancy (N p r d : ℕ) [NeZero d] (hd : Squarefree d)
    (hs : ∀ q ∈ d.primeFactors, q % 4 = 1) (hp : p.Coprime d) :
    |(((range N).filter fun t => d ∣ value p r t).card : ℝ) -
      (N : ℝ) * goldbachSieveRootCount 2 d / d| ≤ goldbachSieveRootCount 2 d := by
  classical
  have hodd : Nat.Coprime 2 d := Nat.prime_two.coprime_iff_not_dvd.mpr fun h =>
    by have := hs 2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two,h,NeZero.ne _⟩); omega
  obtain ⟨i, hi⟩ := (ZMod.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three hd).2
    (fun q hq => by rw [hs q hq]; decide)
  have hii : i*i = -1 := hi.symm
  have hunit : IsUnit i := isUnit_iff_exists_inv.2 ⟨-i, by rw [mul_neg, hii, neg_neg]⟩
  let v := hunit.mul ((ZMod.isUnit_iff_coprime (2*p) d).2 (hodd.mul_left hp))
  let e : ZMod d ≃ ZMod d := v.unit.mulLeft.trans (Equiv.addRight (1 + i*(2*r)))
  let R := univ.filter (fun t : ZMod d => 4*((p:ZMod d)*t+r)^2 + 1 = 0)
  have he (t : ZMod d) : e t = 1 + i*(2*((p:ZMod d)*t+r)) := by
    change (↑v.unit : ZMod d)*t + (1 + i*(2*r)) = _
    rw [v.unit_spec]
    push_cast
    ring
  have hc : R.card = goldbachSieveRootCount 2 d := by
    rw [goldbachSieveRootCount_eq_filter_card]
    apply Finset.card_equiv e
    intro t
    simp only [R, mem_filter, mem_univ, true_and, he, Nat.cast_ofNat]
    have h : (1+i*(2*((p:ZMod d)*t+r)))*(2-(1+i*(2*((p:ZMod d)*t+r)))) =
        4*((p:ZMod d)*t+r)^2 + 1 := by
      linear_combination -4*((p:ZMod d)*t+r)^2 * hii
    rw [h]
  have hset : ((range N).filter fun t => d ∣ value p r t) =
      ((range N).filter fun t : ℕ => (t : ZMod d) ∈ R) := by
    apply filter_congr
    intro t _
    rw [← ZMod.natCast_eq_zero_iff]
    simp [R, value]
  rw [hset, ← hc]
  exact abs_card_range_zmod_mem_sub N R

def sieve (N p r y : ℕ) := PrimePairSieve.imageSieve (range N) (value p r) (wheel y)
  (wheel_sq y) (goldbachSieveDensity 2) (goldbachSieveDensity_isMultiplicative 2)
  (fun q hq _ => goldbachSieveDensity_prime_pos _ _ hq)
  (fun q hq _ => goldbachSieveDensity_prime_lt_one _ _ hq (fun _ => dvd_refl _))

theorem finite_upper (N p r y z : ℕ) (hp : p.Prime) (hy : y < p) (hz : 1 ≤ z) :
    (((range N).filter fun t => (wheel y).Coprime (value p r t)).card : ℝ) ≤
      N / GoldbachSelberg.denominator 2 (wheel y) z + (z : ℝ)^2 * (1+Real.log z)^4 := by
  let s := sieve N p r y
  have hP := wheel_sq y
  have hf := wheel_factors y
  have hrem (d : ℕ) [NeZero d] (hd : d ∣ wheel y) :
      |s.rem d| ≤ goldbachSieveRootCount 2 d := by
    have sub := Nat.primeFactors_mono hd hP.ne_zero
    rw [hf] at sub
    have hc : p.Coprime d := hp.coprime_iff_not_dvd.mpr (by
      intro h
      have := (mem_split (sub (Nat.mem_primeFactors.mpr ⟨hp,h,NeZero.ne _⟩))).2.1
      omega)
    have H := affine_discrepancy N p r d (hP.squarefree_of_dvd hd)
      (fun q hq => (mem_split (sub hq)).2.2) hc
    dsimp only [s, sieve]
    rw [PrimePairSieve.imageSieve_rem, card_range, goldbachSieveDensity_apply]
    convert H using 2 <;> ring
  have hh := SelbergOptimal.siftedSum_le_log_error s hz (by
    intro a ha b hb
    letI : NeZero a := ⟨(Nat.pos_of_mem_divisors ha).ne'⟩
    letI : NeZero b := ⟨(Nat.pos_of_mem_divisors hb).ne'⟩
    letI : NeZero (Nat.lcm a b) := ⟨Nat.lcm_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
    have ha' : a ∣ wheel y := Nat.dvd_of_mem_divisors ha
    have hb' : b ∣ wheel y := Nat.dvd_of_mem_divisors hb
    apply (hrem _ (Nat.lcm_dvd ha' hb')).trans
    exact_mod_cast (goldbachSieveRootCount_lcm_le 2 a b).trans (Nat.mul_le_mul
      (goldbachSieveRootCount_le_two_pow 2 a (hP.squarefree_of_dvd ha'))
      (goldbachSieveRootCount_le_two_pow 2 b (hP.squarefree_of_dvd hb'))))
  have hnorm : SelbergOptimal.normalizer s z = GoldbachSelberg.denominator 2 (wheel y) z := by
    unfold SelbergOptimal.normalizer GoldbachSelberg.denominator
    apply sum_congr rfl
    intro d _
    rw [BoundingSieve.selbergTerms_apply]
    rfl
  rw [hnorm] at hh
  dsimp only [s, sieve] at hh
  rw [PrimePairSieve.imageSieve_siftedSum] at hh
  simpa only [PrimePairSieve.imageSieve, card_range] using hh

open CentralSelberg

def splitMass (n y : ℕ) : ℝ := ∏ p ∈ splitPrimes y, (1+wgt n p)

/- The logarithmic first-moment argument is adapted from
`CentralSelberg.retained`, restricting its finite prime set to the split primes. -/
theorem split_denominator_sum (n y z : ℕ) :
    GoldbachSelberg.denominator n (wheel y) z =
      ∑ t ∈ (splitPrimes y).powerset, if index t ≤ z then weight n t else 0 := by
  classical
  let P := wheel y
  have prime (t : Finset ℕ) (ht : t∈(splitPrimes y).powerset) : ∀ p∈t, p.Prime :=
    fun p hp => (mem_split ((Finset.mem_powerset.mp ht) hp)).1
  have hfac (t : Finset ℕ) (ht : t∈(splitPrimes y).powerset) :
      (index t).primeFactors=t := Nat.primeFactors_prod (prime t ht)
  have hmap : P.divisors = (splitPrimes y).powerset.image index := by
    ext d
    constructor
    · intro hd
      have hsq := (wheel_sq y).squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
      have hmono := Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) ((wheel_sq y).ne_zero)
      rw [wheel_factors] at hmono
      exact Finset.mem_image.mpr ⟨d.primeFactors, Finset.mem_powerset.mpr hmono, Nat.prod_primeFactors_of_squarefree hsq⟩
    · rintro hd
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hd
      exact Nat.mem_divisors.mpr ⟨Finset.prod_dvd_prod_of_subset _ _ _ (Finset.mem_powerset.mp ht),(wheel_sq y).ne_zero⟩
  unfold GoldbachSelberg.denominator
  change (∑ d ∈ P.divisors, _) = _
  rw [hmap, Finset.sum_image (fun a ha b hb hh => (hfac a ha).symm.trans ((congrArg Nat.primeFactors hh).trans (hfac b hb)))]
  refine Finset.sum_congr rfl fun t ht => ?_
  split_ifs
  · rw [hfac t ht, index, (goldbachSieveDensity_isMultiplicative n).map_prod_of_prime t (prime t ht)]
    exact (Finset.prod_mul_distrib).symm
  · rfl

theorem split_retained (n y : ℕ) (hn : 2∣n) (hy : 2≤y) :
    splitMass n y ≤ 2 * GoldbachSelberg.denominator n (wheel y) (y^8) := by
  let T := (splitPrimes y).powerset
  let W := weight n
  let D := GoldbachSelberg.denominator n (wheel y) (y^8)
  have wp (t : Finset ℕ) (ht : t ∈ T) : 0 ≤ W t :=
    Finset.prod_nonneg fun p hp => (wgt_pos n hn p ((mem_split ((Finset.mem_powerset.mp ht) hp)).1)).le
  have total : (∑ t ∈ T, W t) = splitMass n y := (Finset.prod_one_add _).symm
  have heavy_point (t : Finset ℕ) (ht : t ∈ T) :
      (if y^8 < index t then W t else 0)*(8*Real.log y) ≤ W t*Real.log (index t) := by
    have hip : 0 < index t := Finset.prod_pos fun p hp =>
      ((mem_split ((Finset.mem_powerset.mp ht) hp)).1).pos
    split
    · rename_i hl
      apply mul_le_mul_of_nonneg_left _ (wp t ht)
      have hlog := Real.log_le_log (show (0:ℝ) < ((y^8:ℕ):ℝ) by positivity) (show ((y^8:ℕ):ℝ) ≤ index t by exact_mod_cast hl.le)
      simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using hlog
    · rw [zero_mul]
      exact mul_nonneg (wp t ht) (Real.log_nonneg (by exact_mod_cast hip))
  have mean := powerset_moment (splitPrimes y) (wgt n) (fun p => Real.log (p:ℝ))
    (fun p hp => (wgt_pos n hn p ((mem_split hp).1)).le)
  have hsumlog (t : Finset ℕ) (ht : t∈T) :
      Real.log (index t) = ∑ p ∈ t, Real.log (p:ℝ) := by
    unfold index
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp; exact_mod_cast ((mem_split ((Finset.mem_powerset.mp ht) hp)).1).ne_zero
  have bound : (∑ p ∈ (splitPrimes y), wgt n p/(1+wgt n p)*Real.log p) ≤ 4*Real.log y := by
    calc
      _ ≤ ∑ p ∈ (splitPrimes y), 2*(Real.log p/p) := by
        refine sum_le_sum fun p hp => ?_
        have hpP := (mem_split hp).1
        have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpP.one_le)
        rw [wgt_ratio n hn p hpP]
        unfold rho
        rw [goldbachSieveDensity_prime n p hpP]
        split <;> ring_nf <;> first | rfl | nlinarith [mul_nonneg hlog (inv_nonneg.mpr (Nat.cast_nonneg p : (0:ℝ) ≤ _))]
      _ ≤ ∑ p ∈ y.primesLE, 2*(Real.log p/p) := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro p _ _
        exact mul_nonneg (by norm_num) (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
      _ ≤ _ := by rw [←Finset.mul_sum]; linarith [weighted_harmonic y (by omega)]
  have hmass : 0 ≤ splitMass n y := Finset.prod_nonneg (fun p hp => by
    linarith [wgt_pos n hn p ((mem_split hp).1)])
  have moment : (∑ t ∈ T, W t*Real.log (index t)) ≤ splitMass n y * (4*Real.log y) := by
    calc
      _ = ∑ t ∈ (splitPrimes y).powerset, (∏ p ∈ t, wgt n p)*(∑ p ∈ t, Real.log p) :=
        sum_congr rfl (fun t ht => by rw [hsumlog t ht]; rfl)
      _ = _ := mean
      _ ≤ _ := mul_le_mul_of_nonneg_left bound hmass
  have hdiff : (∑ t ∈ T, if y^8 < index t then W t else 0) = splitMass n y - D := by
    rw [← total, show D = _ from split_denominator_sum n y (y^8), ← Finset.sum_sub_distrib]
    apply sum_congr rfl; intro t _; by_cases h : index t ≤ y^8 <;> simp [h,not_lt.mpr,lt_of_not_ge,W]
  have hh := (sum_le_sum heavy_point).trans moment
  rw [← Finset.sum_mul, hdiff] at hh
  have hl : 0 < Real.log y := Real.log_pos (by exact_mod_cast (show 1<y by omega))
  change splitMass n y ≤ 2*D
  apply (le_of_mul_le_mul_right (a := Real.log y) ?_ hl)
  linarith only [hh]



/-! The convolution of the mod-four character with the constant-one arithmetic
function has nonnegative coefficients. Its harmonic sum is large because each
nonempty initial sum of the alternating odd reciprocals is at least 2/3. -/
open ArithmeticFunction

def character : ArithmeticFunction ℝ where
  toFun n := (ZMod.χ₄ (n : ZMod 4) : ℤ)
  map_zero' := by change ((0:ℤ):ℝ) = 0; norm_num

theorem character_mul (m n : ℕ) : character (m*n) = character m * character n := by
  change (↑(ZMod.χ₄ ((m*n:ℕ) : ZMod 4)) : ℝ) = _
  simp only [Nat.cast_mul, map_mul, Int.cast_mul]
  rfl

theorem character_one : character 1 = 1 := by
  change (↑(ZMod.χ₄ ((1:ℕ) : ZMod 4)) : ℝ) = 1
  simp

def coeff := character * (zeta : ArithmeticFunction ℝ)

theorem coeff_mult : coeff.IsMultiplicative :=
  (show character.IsMultiplicative from ⟨character_one, fun {_ _} _ => character_mul _ _⟩).mul
    (by arith_mult)

theorem character_formula (n : ℕ) :
    character n = if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1 := by
  change ((ZMod.χ₄ n : ℤ) : ℝ) = _
  rw [ZMod.χ₄_nat_eq_if_mod_four]
  split_ifs <;> norm_num

theorem coeff_prime_power (p j : ℕ) (hp : p.Prime) :
    coeff (p^j) = ∑ k ∈ range (j+1), (character p)^k := by
  rw [coeff, coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
  apply sum_congr rfl
  intro k hk
  clear hk
  induction k with
  | zero => simp [character_one]
  | succ k ih => rw [pow_succ, character_mul, ih, pow_succ]

theorem alternating_geom (j : ℕ) :
    (∑ k ∈ range (j+1), (-1:ℝ)^k) = if Even j then 1 else 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ, ih, pow_succ]
    rcases Nat.even_or_odd j with hj|hj
    · simp [hj, hj.neg_one_pow, Nat.even_add_one]
    · simp [(Nat.not_even_iff_odd.mpr hj), hj.neg_one_pow, Nat.even_add_one, hj]

theorem prime_coeff_values (p j : ℕ) (hp : p.Prime) : coeff (p^j) =
    if p=2 then 1 else if p % 4=1 then ((j+1:ℕ):ℝ) else if Even j then 1 else 0 := by
  rw [coeff_prime_power p j hp, character_formula]
  by_cases h : p=2
  · subst p
    simp [Finset.sum_range_succ']
  · have ho := hp.eq_two_or_odd.resolve_left h
    simp only [h, ho, one_ne_zero, ite_false]
    by_cases h4 : p % 4=1
    · simp [h4]
    · simp only [h4, ite_false, alternating_geom]

theorem coeff_nonneg (n : ℕ) : 0 ≤ coeff n := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => simp
  | prime_pow p j hp => rw [prime_coeff_values p j hp]; split_ifs <;> positivity
  | coprime a b _ _ hab ha hb => rw [coeff_mult.2 hab]; exact mul_nonneg ha hb

def charTerm (n : ℕ) := character n / n

theorem char_block (m : ℕ) :
    (0:ℝ) ≤ charTerm (4*m) + charTerm (4*m+1) + charTerm (4*m+2) + charTerm (4*m+3) := by
  simp only [charTerm,character_formula]
  have h0 : 4*m % 2=0 := by omega
  have h1 : (4*m+1)%2=1 := by omega
  have h2 : (4*m+2)%2=0 := by omega
  have h3 : (4*m+3)%2=1 := by omega
  have h4 : (4*m+1)%4=1 := by omega
  have h5 : (4*m+3)%4≠1 := by omega
  simp [h0,h1,h2,h3,h4,h5,div_eq_mul_inv]
  exact inv_anti₀ (by positivity) (by linarith)

theorem char_four_blocks (j : ℕ) :
    (2/3:ℝ) ≤ ∑ n ∈ range (4*j+4), charTerm n := by
  induction j with
  | zero => norm_num [charTerm, character_formula, Finset.sum_range_succ]
  | succ j ih =>
    have h := char_block (j+1)
    rw [show 4*(j+1)+4 = (4*j+4)+1+1+1+1 by omega]
    rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ]
    rw [show 4*(j+1)=4*j+4 by omega] at h
    linarith only [h,ih]

theorem char_lower (N : ℕ) (hN : 1 ≤ N) :
    (2/3:ℝ) ≤ ∑ n ∈ Icc 1 N, charTerm n := by
  have hr : (∑ n ∈ Icc 1 N, charTerm n) = ∑ n ∈ range (N+1), charTerm n := by
    have he : range (N+1) = insert 0 (Icc 1 N) := by ext n; simp; omega
    rw [he,sum_insert (by simp)]
    simp [charTerm]
  rw [hr]
  by_cases h : N<4
  · interval_cases N <;> norm_num [charTerm,character_formula,sum_range_succ]
  let j := N/4
  have hj : 1 ≤ j := by dsimp [j]; omega
  have H := char_four_blocks (j-1)
  rw [show 4*(j-1)+4=4*j by omega] at H
  have H' := char_four_blocks j
  have hc : ∀ n : ℕ, n % 2=0 → charTerm n = 0 := by
    intro n hn; simp [charTerm,character_formula,hn]
  have h1 : 0 ≤ charTerm (4*j+1) := by
    simp [charTerm,character_formula,show (4*j+1)%2=1 by omega,show (4*j+1)%4=1 by omega]
    positivity
  have hx : N=4*j ∨ N=4*j+1 ∨ N=4*j+2 ∨ N=4*j+3 := by dsimp [j]; omega
  rcases hx with h|h|h|h
  · rw [h,sum_range_succ,hc _ (by omega),add_zero]; exact H
  · rw [h,sum_range_succ,sum_range_succ,hc _ (by omega),add_zero]; linarith
  · rw [h,sum_range_succ,hc _ (by omega),add_zero,sum_range_succ,sum_range_succ,hc _ (by omega),add_zero]; linarith
  · simpa only [h] using H'


theorem coeff_harmonic_lower (N : ℕ) :
    (2/3:ℝ) * Real.log ((N:ℝ)+1) ≤ ∑ n ∈ Icc 1 N, coeff n / n := by
  classical
  let D := ((Icc 1 N) ×ˢ (Icc 1 N)).filter fun ab : ℕ × ℕ => ab.1*ab.2 ≤ N
  let F := fun ab : ℕ × ℕ => (ab.1:ℝ)⁻¹ * charTerm ab.2
  have maps : ∀ ab ∈ D, ab.1*ab.2 ∈ Icc 1 N := by
    intro ab h
    obtain ⟨hp,hle⟩ := mem_filter.mp h
    obtain ⟨ha,hb⟩ := mem_product.mp hp
    exact mem_Icc.mpr ⟨Nat.mul_pos (mem_Icc.mp ha).1 (mem_Icc.mp hb).1,hle⟩
  have fiber (n : ℕ) (hn : n ∈ Icc 1 N) :
      D.filter (fun ab => ab.1*ab.2=n) = n.divisorsAntidiagonal := by
    ext ⟨a,b⟩
    simp only [D, mem_filter,mem_product,mem_Icc,Nat.mem_divisorsAntidiagonal]
    obtain ⟨hn1,hnN⟩ := mem_Icc.mp hn
    constructor
    · exact fun h => ⟨h.2,by omega⟩
    · rintro ⟨hab,hn0⟩
      have ha := left_ne_zero_of_mul (hab.trans_ne hn0)
      have hb := right_ne_zero_of_mul (hab.trans_ne hn0)
      have haN := (Nat.le_of_dvd hn1 (show a ∣ n from ⟨b,hab.symm⟩)).trans hnN
      have hbN := (Nat.le_of_dvd hn1 (show b ∣ n from ⟨a,by rw [mul_comm,hab]⟩)).trans hnN
      exact ⟨⟨⟨⟨by omega,haN⟩,⟨by omega,hbN⟩⟩,hab.trans_le hnN⟩,hab⟩
  have hcoeff (n : ℕ) (hn : n ∈ Icc 1 N) :
      (∑ ab ∈ D.filter (fun ab => ab.1*ab.2=n), F ab) = coeff n / n := by
    rw [fiber n hn, coeff, mul_comm character, ArithmeticFunction.mul_apply, sum_div]
    apply sum_congr rfl
    rintro ⟨a,b⟩ hab
    obtain ⟨hab,hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hab
    change a*b=n at hab
    have ha : a ≠ 0 := by intro h; simp [h] at hab; omega
    rw [← hab, Nat.cast_mul]
    simp [F, charTerm, ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne ha]
    <;> ring
  have tri (a : ℕ) (ha : a ∈ Icc 1 N) :
      (Icc 1 N).filter (fun b => a*b≤N) = Icc 1 (N/a) := by
    ext b
    have h := (mem_Icc.mp ha).1
    rw [mem_filter,mem_Icc,mem_Icc,Nat.le_div_iff_mul_le h,mul_comm b a]
    constructor
    · exact fun z => ⟨z.1.1,z.2⟩
    · intro z
      exact ⟨⟨z.1,(Nat.le_mul_of_pos_left b h).trans z.2⟩,z.2⟩
  calc
    _ ≤ (2/3:ℝ) * (harmonic N : ℝ) := by gcongr; exact_mod_cast log_add_one_le_harmonic N
    _ = ∑ a ∈ Icc 1 N, (a:ℝ)⁻¹ * (2/3) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum, mul_comm, sum_mul]; push_cast; rfl
    _ ≤ ∑ a ∈ Icc 1 N, (a:ℝ)⁻¹ * ∑ b ∈ Icc 1 (N/a), charTerm b := by
      apply sum_le_sum; intro a ha
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply char_lower
      exact (Nat.le_div_iff_mul_le (mem_Icc.mp ha).1).2 (by simpa using (mem_Icc.mp ha).2)
    _ = ∑ ab ∈ D, F ab := by
      dsimp only [D]
      rw [sum_filter, sum_product]
      refine sum_congr rfl fun a ha => ?_
      rw [← tri a ha, mul_sum, sum_filter]
    _ = ∑ n ∈ Icc 1 N, coeff n / n := by
      rw [← sum_fiberwise_of_maps_to maps F]
      exact sum_congr rfl hcoeff


def densityWeight (n : ℕ) : ℝ := coeff n / n

theorem weight_nonneg (n : ℕ) : 0 ≤ densityWeight n := div_nonneg (coeff_nonneg n) (Nat.cast_nonneg n)

theorem weight_power (p j : ℕ) : densityWeight (p^j) = coeff (p^j)*((p:ℝ)⁻¹)^j := by
  simp [densityWeight,div_eq_mul_inv]

theorem prime_majorant (p j : ℕ) (hp : p.Prime) :
    densityWeight (p^j) ≤ (if p=2 then (p:ℝ)⁻¹ else 2*(p:ℝ)⁻¹)^j := by
  rw [weight_power,prime_coeff_values p j hp]
  by_cases h : p=2
  · simp [h]
  · simp only [h,ite_false,mul_pow]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hj : (j+1:ℝ) ≤ 2^j := by
      induction j with
      | zero => norm_num
      | succ j hj => rw [pow_succ]; push_cast; linarith [one_le_pow₀ (show (1:ℝ)≤2 by norm_num) (n:=j)]
    split_ifs <;> push_cast <;> first | linarith | positivity

theorem weight_summable {p : ℕ} (hp : p.Prime) :
    Summable (fun j : ℕ => densityWeight (p^j)) := by
  let t : ℝ := if p=2 then (p:ℝ)⁻¹ else 2*(p:ℝ)⁻¹
  have ht : 0 ≤ t := by dsimp [t]; split <;> positivity
  have hl : t < 1 := by
    dsimp [t]; split_ifs with h
    · norm_num [h]
    · have hp2 : 2<p := by have := hp.two_le; omega
      have hpr : (2:ℝ)<p := by exact_mod_cast hp2
      rw [← div_eq_mul_inv, div_lt_one (by positivity : (0:ℝ)<p)]
      exact hpr
  exact (summable_geometric_of_lt_one ht hl).of_nonneg_of_le
    (fun j => weight_nonneg _) (fun j => prime_majorant p j hp)

theorem local_two : (∑' j : ℕ, densityWeight (2^j)) = 2 := by
  calc _ = ∑' j : ℕ, ((2:ℝ)⁻¹)^j := tsum_congr (fun j => by
          rw [weight_power, prime_coeff_values 2 j Nat.prime_two]; norm_num)
       _ = 2 := tsum_geometric_inv_two

theorem local_split {p : ℕ} (hp : p.Prime) (h4 : p % 4=1) :
    (∑' j : ℕ, densityWeight (p^j)) ≤ 1+CentralSelberg.wgt 2 p := by
  have h2 : p≠2 := by omega
  have hp2 : 2<p := by have := hp.two_le; omega
  have hpr : (2:ℝ)<p := by exact_mod_cast hp2
  have hp0 : 0<(p:ℝ) := by positivity
  have hlt : 2*(p:ℝ)⁻¹ < 1 := by rw [← div_eq_mul_inv,div_lt_one hp0]; exact hpr
  have h := (weight_summable hp).tsum_le_tsum
    (fun j => (prime_majorant p j hp).trans_eq (by simp [h2]))
    (summable_geometric_of_lt_one (by positivity : 0≤2*(p:ℝ)⁻¹) hlt)
  rw [tsum_geometric_of_lt_one (by positivity) hlt] at h
  apply h.trans_eq
  have hn : ¬p ∣ 2 := fun h => (Nat.le_of_dvd (by decide) h).not_gt hp2
  unfold CentralSelberg.wgt CentralSelberg.rho
  rw [goldbachSieveDensity_prime 2 p hp, if_neg hn,div_eq_mul_inv]
  field_simp [show 1-2*(p:ℝ)⁻¹≠0 by linarith]
  <;> ring

theorem local_inert {p : ℕ} (hp : p.Prime) (h2 : p≠2) (h4 : p % 4≠1) :
    (∑' j : ℕ, densityWeight (p^j)) ≤ 1 + 2/(p:ℝ)^2 := by
  let t : ℝ := (p:ℝ)⁻¹
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have ht2 : t ≤ 1/2 := by dsimp [t]; rw [← one_div]; exact one_div_le_one_div_of_le (by norm_num) hp2
  have hl : t<1 := by linarith
  have hs := weight_summable hp
  have major (j : ℕ) : densityWeight (p^(j+2)) ≤ t^j * t^2 := by
    rw [weight_power,prime_coeff_values p (j+2) hp,if_neg h2,if_neg h4, pow_add]
    change (if Even (j+2) then (1:ℝ) else 0)*(t^j*t^2) ≤ _
    split <;> simp [mul_nonneg (pow_nonneg ht _) (sq_nonneg t)]
  have hm := ((summable_nat_add_iff 2).2 hs).tsum_le_tsum major
    ((summable_geometric_of_lt_one ht hl).mul_right _)
  rw [tsum_mul_right,tsum_geometric_of_lt_one ht hl] at hm
  have hc : (1-t)⁻¹ ≤ 2 := by
    rw [← one_div,div_le_iff₀ (by linarith)]
    linarith
  have hfirst : (∑ j ∈ range 2, densityWeight (p^j)) = 1 := by
    simp [Finset.sum_range_succ, weight_power,prime_coeff_values p _ hp,h2,h4,
      densityWeight, coeff_mult.map_one]
  rw [← hs.sum_add_tsum_nat_add 2, hfirst]
  apply add_le_add_right
  apply hm.trans
  calc (1-t)⁻¹ * t^2 ≤ 2*t^2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
       _ = _ := by simp [t,div_eq_mul_inv]

/-! Only the split primes contribute a first-order term to the Euler product.
The remaining factors are controlled by the convergent sum of inverse squares. -/

def eulerConstant := 2*Real.exp (∑' m : ℕ, 2/(m:ℝ)^2)

theorem eulerConstant_pos : 0 < eulerConstant := by unfold eulerConstant; positivity

theorem euler_lower (y : ℕ) :
    (2/3:ℝ)*Real.log ((y:ℝ)+1) ≤ eulerConstant *
      ∏ p ∈ y.primesLE.filter (fun p => p % 4=1), (1+CentralSelberg.wgt 2 p) := by
  have hE := smooth_sum_le_euler_product densityWeight weight_nonneg
    (by simp [densityWeight, coeff_mult.map_one])
    (fun hc => by simp only [densityWeight, coeff_mult.2 hc,Nat.cast_mul,mul_div_mul_comm])
    (fun hp => by simpa only [Real.norm_eq_abs,abs_of_nonneg (weight_nonneg _)] using weight_summable hp)
    (y+1) (Icc 1 y) (fun n hn => Nat.mem_smoothNumbers_of_lt (mem_Icc.mp hn).1 (by have := (mem_Icc.mp hn).2; omega))
  let g := fun p : ℕ => if p % 4=1 then 1+CentralSelberg.wgt 2 p else (1:ℝ)
  let h := fun p : ℕ => if p=2 then (2:ℝ) else 1
  let b := fun p : ℕ => 2/(p:ℝ)^2
  have hg (p : ℕ) (hp : p.Prime) : 1 ≤ g p := by
    dsimp [g]; split <;> linarith [CentralSelberg.wgt_pos 2 (dvd_refl _) p hp]
  have hb (p : ℕ) : 1+b p ≤ Real.exp (b p) := by linarith [Real.add_one_le_exp (b p)]
  have hb0 (p : ℕ) : 0 ≤ b p := by dsimp [b]; positivity
  have hloc (p : ℕ) (hp : p.Prime) :
      (∑' j : ℕ, densityWeight (p^j)) ≤ h p * Real.exp (b p) * g p := by
    have h1 : 1 ≤ Real.exp (b p) := (Real.one_le_exp_iff.mpr (hb0 p))
    by_cases h2 : p=2
    · subst p; rw [local_two]; simp only [h,ite_true]; nlinarith [hg 2 Nat.prime_two, mul_le_mul_of_nonneg_left (hg 2 Nat.prime_two) (Real.exp_pos (b 2)).le]
    · by_cases h4 : p % 4=1
      · apply (local_split hp h4).trans
        simp only [h,h2,ite_false,one_mul,g,h4,ite_true]
        exact le_mul_of_one_le_left (by linarith [CentralSelberg.wgt_pos 2 (dvd_refl _) p hp]) h1
      · simpa [h,h2,g,h4,b] using (local_inert hp h2 h4).trans (hb p)
  have htwo : (∏ p ∈ y.primesLE, h p) ≤ 2 := by
    dsimp [h]; rw [prod_ite_eq']; split <;> norm_num
  have hbS : Summable b := by
    simpa only [b,div_eq_mul_inv] using
      (Real.summable_nat_pow_inv.mpr (by decide : 1<2)).mul_left (2:ℝ)
  have hsum := hbS.sum_le_tsum y.primesLE (fun n _ => hb0 n)
  have hgP : 0 ≤ ∏ p ∈ y.primesLE, g p :=
    prod_nonneg fun p hp => (zero_le_one.trans (hg p (Nat.prime_of_mem_primesLE hp)))
  calc
    _ ≤ _ := coeff_harmonic_lower y
    _ ≤ ∏ p ∈ y.primesLE, ∑' j : ℕ, densityWeight (p^j) := hE
    _ ≤ ∏ p ∈ y.primesLE, (h p * Real.exp (b p) * g p) :=
      Finset.prod_le_prod₀ (fun _ _ => tsum_nonneg fun _ => weight_nonneg _) (fun p hp => hloc p (Nat.prime_of_mem_primesLE hp))
    _ = ((∏ p ∈ y.primesLE, h p)*Real.exp (∑ p ∈ y.primesLE, b p))*(∏ p ∈ y.primesLE, g p) := by
      rw [prod_mul_distrib,prod_mul_distrib,Real.exp_sum]
    _ ≤ _ := by
      unfold eulerConstant
      rw [Finset.prod_filter]
      apply mul_le_mul_of_nonneg_right _ hgP
      exact mul_le_mul htwo (Real.exp_le_exp.mpr hsum) (Real.exp_pos _).le (by norm_num)


open Filter in
theorem upper_of_mass (A : ℝ) (hA : 0<A)
    (hMass : ∀ y : ℕ, (2/3:ℝ)*Real.log ((y:ℝ)+1) ≤ A*splitMass 2 y) :
    ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ x p r : ℕ, N≤x → p.Prime → Nat.nthRoot 5 (x^2) < p → p ≤ 5 * Nat.nthRoot 3 (x^2) → r < p → (4*r^2+1)%p=0 → (((Finset.range (x+1)).filter fun t => let k:=p*t+r; x<2*k ∧ k≤x ∧ (4*k^2+1).minFac=p).card : ℝ) ≤ C*x/(p*Real.log x) := by
  obtain ⟨M,hM⟩ := eventually_atTop.1 CentralSelberg.scales
  have logEventually := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
  obtain ⟨L,hL⟩ := eventually_atTop.1 logEventually
  let K := max 125 (max M L)
  refine ⟨2*(384*A+72),by positivity,125*K^3+2,?_⟩
  intro x p r hx hp hlo hup _ _
  let n := x/p+1
  have hx0 : 0<x := by omega
  have hx2 : 2≤x := by omega
  have hn0 : 0<n := Nat.succ_pos _
  have hxnp : x < n*p := (Nat.div_lt_iff_lt_mul hp.pos).1 (Nat.lt_succ_self _)
  have hp3 : p^3 ≤ 125*x^2 := by
    calc _ ≤ (5*Nat.nthRoot 3 (x^2))^3 := Nat.pow_le_pow_left hup _
         _ = 125*(Nat.nthRoot 3 (x^2))^3 := by ring
         _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_nthRoot_le_iff.mpr (.inl (by decide)))
  have hxScale : x ≤ 125*n^3 := by
    have H : x^2*x ≤ x^2*(125*n^3) := calc
      _ = x^3 := by ring
      _ ≤ (n*p)^3 := Nat.pow_le_pow_left hxnp.le _
      _ = n^3*p^3 := mul_pow _ _ _
      _ ≤ n^3*(125*x^2) := Nat.mul_le_mul_left _ hp3
      _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left H (by positivity)
  have hKn : K≤n := by
    by_contra! hn
    have := Nat.mul_le_mul_left 125 (Nat.pow_le_pow_left hn.le 3)
    omega
  have h125 : 125≤n := (le_max_left _ _).trans hKn
  have hMn : M≤n := (le_max_left M L).trans ((le_max_right 125 _).trans hKn)
  have hLn : L≤n := (le_max_right M L).trans ((le_max_right 125 _).trans hKn)
  have hlog : 1 ≤ Real.log (n:ℝ) := hL n hLn
  have hx4 : x≤n^4 := hxScale.trans (by calc
    125*n^3 ≤ n*n^3 := Nat.mul_le_mul_right _ h125
    _ = _ := by ring)
  have hlogx : Real.log (x:ℝ) ≤ 4*Real.log (n:ℝ) := by
    have H := Real.log_le_log (by exact_mod_cast hx0 : 0<(x:ℝ)) (by exact_mod_cast hx4 : (x:ℝ)≤(n:ℝ)^4)
    simpa using H
  obtain ⟨y,hy,hny,herr⟩ := hM n hMn
  let z := y^8
  let E := (z:ℝ)^2*(1+Real.log (z:ℝ))^4
  have hz : 1 ≤ z := Nat.one_le_pow _ _ (by omega : 0<y)
  have hzlog : 0 ≤ Real.log (z:ℝ) := Real.log_nonneg (by exact_mod_cast hz)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have he2 : E * (Real.log n)^2 ≤ 18*n := by
    exact (mul_le_mul_of_nonneg_right (show E ≤ E+2*y from le_add_of_nonneg_right (by positivity)) (sq_nonneg _)).trans herr
  have he : E*Real.log n ≤ 18*n := (mul_le_mul_of_nonneg_left
    (by rw [sq]; exact le_mul_of_one_le_right (by linarith only [hlog]) hlog : Real.log (n:ℝ) ≤ (Real.log n)^2) hE).trans he2
  have hE18 : E ≤ 18*n := (le_mul_of_one_le_right hE hlog).trans he
  have h16 : y^16 ≤ 18*n := by
    have hh : (y:ℝ)^16 ≤ E := by
      calc _ = (z:ℝ)^2 := by dsimp [z]; push_cast; ring
           _ ≤ _ := le_mul_of_one_le_right (sq_nonneg _) (one_le_pow₀ (by linarith : 1≤1+Real.log (z:ℝ)))
    exact_mod_cast hh.trans hE18
  have hpx : x^2 < p^5 := (Nat.nthRoot_lt_iff (by decide : 5≠0)).mp hlo
  have hn5 : n ≤ p^5 := by
    have hnx : n ≤ x+1 := Nat.succ_le_succ (Nat.div_le_self _ _)
    have : x ≤ x^2 := Nat.le_self_pow (by decide : 2 ≠ 0) x
    omega
  have hyp : y < p := by
    by_contra! h
    have H := Nat.pow_le_pow_left h 16
    have h11 := Nat.pow_le_pow_left hp.two_le 11
    have hbig : 18*p^5 < p^16 := calc
      _ < p^11*p^5 := Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos hp.pos 5)
      _ = _ := by ring
    omega
  let D := GoldbachSelberg.denominator 2 (wheel y) z
  have hD : 0<D := GoldbachSelberg.denominator_pos 2 _ (dvd_refl _) (wheel_sq y) hz
  have hret := split_retained 2 y (dvd_refl _) hy
  have hDA := (hMass y).trans (mul_le_mul_of_nonneg_left hret hA.le)
  have hxD : Real.log (x:ℝ) ≤ (384*A)*D := by
    dsimp only [D,z]
    linarith only [hDA,hny,hlogx]
  have main : ((n:ℝ)/D)*Real.log x ≤ (384*A)*n := by
    have H := mul_le_mul_of_nonneg_left hxD (show 0 ≤ (n:ℝ)/D by positivity)
    convert H using 1
    field_simp
  have err : E*Real.log x ≤ 72*n := by
    linarith only [he, mul_le_mul_of_nonneg_left hlogx hE]
  have H := finite_upper n p r y z hp hyp hz
  let T := (range (x+1)).filter fun t => let k:=p*t+r; x<2*k ∧ k≤x ∧ (4*k^2+1).minFac=p
  have sub : T ⊆ (range n).filter (fun t => (wheel y).Coprime (value p r t)) := by
    intro t ht
    obtain ⟨_,_,hk,hfac⟩ := mem_filter.mp ht
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hp.pos).2 (by
      simpa only [mul_comm t p] using (show p*t≤x by omega)))),?_⟩
    unfold wheel
    rw [Nat.coprime_prod_left_iff]
    intro q hq
    apply (mem_split hq).1.coprime_iff_not_dvd.mpr
    intro hd
    have Hq := Nat.minFac_le_of_dvd (mem_split hq).1.two_le hd
    change (value p r t).minFac=p at hfac
    rw [hfac] at Hq
    have := (mem_split hq).2.1
    omega
  have hcard : (T.card:ℝ) ≤ n/D+E := (Nat.cast_le.mpr (card_le_card sub)).trans H
  have hxlog : 0 < Real.log (x:ℝ) := Real.log_pos (by exact_mod_cast (show 1<x by omega))
  have hmid : (T.card:ℝ)*Real.log x ≤ (384*A+72)*n := by
    nlinarith only [mul_le_mul_of_nonneg_right hcard hxlog.le,main,err]
  have hpx' : p ≤ x := by
    have H : 1 ≤ x/p := by dsimp [n] at h125; omega
    simpa using (Nat.le_div_iff_mul_le hp.pos).mp H
  have hnp : n*p ≤ 2*x := by
    dsimp [n]; rw [Nat.add_mul,one_mul]
    have := Nat.div_mul_le_self x p
    omega
  apply (le_div_iff₀ (mul_pos (by exact_mod_cast hp.pos) hxlog)).2
  change T.card * ((p:ℝ)*Real.log x) ≤ _
  have hnpr : (n:ℝ)*p ≤ 2*x := by exact_mod_cast hnp
  nlinarith only [mul_le_mul_of_nonneg_right hmid (Nat.cast_nonneg p),
    mul_le_mul_of_nonneg_left hnpr (by positivity : 0≤384*A+72)]

end
end Conjectures.QuadraticPrimes.SwitchedCofactorSmallSieveAux

open Conjectures.QuadraticPrimes.SwitchedCofactorSmallSieveAux in
theorem Conjectures.QuadraticPrimes.SwitchedCofactorSmallSieve :
    ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ x p r : ℕ, N≤x → p.Prime → Nat.nthRoot 5 (x^2) < p → p ≤ 5 * Nat.nthRoot 3 (x^2) → r < p → (4*r^2+1)%p=0 → (((Finset.range (x+1)).filter fun t => let k:=p*t+r; x<2*k ∧ k≤x ∧ (4*k^2+1).minFac=p).card : ℝ) ≤ C*x/(p*Real.log x) :=
  upper_of_mass eulerConstant eulerConstant_pos euler_lower

namespace QuadraticFirstFactorEdges

open Finset

def value (k : ℕ) : ℕ := 4*k^2+1

def primesBand (z : ℕ) : Finset ℕ := (Ioc z (2*z)).filter Nat.Prime

def roots (p : ℕ) : Finset ℕ := (range p).filter (fun r => value r % p = 0)

theorem roots_card_le_two {p : ℕ} (hp : p.Prime) : (roots p).card ≤ 2 := by
  let _ : Fact p.Prime := ⟨hp⟩
  let P : Polynomial (ZMod p) := Polynomial.monomial 2 4 + 1
  have h0 : P ≠ 0 := by
    intro h
    have hc := congrArg (fun Q : Polynomial (ZMod p) => Q.coeff 0) h
    simp [P] at hc
  have hdeg : P.natDegree ≤ 2 := by
    unfold P
    apply (Polynomial.natDegree_add_le _ _).trans
    exact max_le (Polynomial.natDegree_monomial_le _) (by simp)
  let f : ℕ → ZMod p := fun r => r
  have inj : Set.InjOn f ↑(roots p) := by
    intro a ha b hb h
    have ha' := mem_range.mp (mem_filter.mp ha).1
    have hb' := mem_range.mp (mem_filter.mp hb).1
    change (a : ZMod p) = (b : ZMod p) at h
    simpa only [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] using congrArg ZMod.val h
  have sub : (roots p).image f ⊆ P.roots.toFinset := by
    intro v hv
    rcases mem_image.mp hv with ⟨r, hr, rfl⟩
    have hCast : ((value r : ℕ) : ZMod p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact Nat.dvd_of_mod_eq_zero (mem_filter.mp hr).2
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots h0).mpr
    simpa [P, f, value, Polynomial.IsRoot] using hCast
  rw [← card_image_of_injOn inj]
  exact (card_le_card sub).trans ((Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' P).trans hdeg))

theorem band_reciprocals {z : ℕ} (hz : 1 < z) :
    (∑ p ∈ primesBand z, 1 / (p : ℝ)) ≤ 2 * Real.log 4 / Real.log z := by
  have hzPos : (0 : ℝ) < z := by exact_mod_cast (show 0 < z by omega)
  have hLog : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast hz)
  have hprod : 0 < (z : ℝ) * Real.log z := mul_pos hzPos hLog
  have hSub : primesBand z ⊆ Nat.primesLE (2*z) := by
    intro p hp
    obtain ⟨hb,hp⟩ := mem_filter.mp hp
    rw [Nat.primesLE_eq_filter_Icc_zero]
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le p,(mem_Ioc.mp hb).2⟩,hp⟩
  have hsum : (∑ p ∈ primesBand z, Real.log (p : ℝ)) ≤ Chebyshev.theta ((2*z : ℕ) : ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    apply sum_le_sum_of_subset_of_nonneg hSub
    intro p hp _
    rw [Nat.primesLE_eq_filter_Icc_zero] at hp
    exact Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_lt.le)
  calc
    (∑ p ∈ primesBand z, 1 / (p : ℝ)) ≤
        ∑ p ∈ primesBand z, Real.log (p : ℝ) / ((z : ℝ) * Real.log z) := by
      apply sum_le_sum
      intro p hp
      have hpZ : z < p := (mem_Ioc.mp (mem_filter.mp hp).1).1
      have hZP : (z : ℝ) ≤ p := by exact_mod_cast hpZ.le
      calc
        1 / (p : ℝ) ≤ 1 / (z : ℝ) := one_div_le_one_div_of_le hzPos hZP
        _ ≤ Real.log (p : ℝ) / ((z : ℝ)*Real.log z) := by
          apply (le_div_iff₀ hprod).mpr
          have he : 1 / (z : ℝ) * ((z : ℝ)*Real.log z) = Real.log z := by field_simp
          rw [he]
          exact Real.log_le_log hzPos hZP
    _ = (∑ p ∈ primesBand z, Real.log (p : ℝ)) / ((z : ℝ)*Real.log z) := (Finset.sum_div _ _ _).symm
    _ ≤ Chebyshev.theta ((2*z : ℕ) : ℝ) / ((z : ℝ)*Real.log z) :=
      div_le_div_of_nonneg_right hsum hprod.le
    _ ≤ (Real.log 4 * ((2*z : ℕ) : ℝ)) / ((z : ℝ)*Real.log z) :=
      div_le_div_of_nonneg_right (Chebyshev.theta_le_log4_mul_x (by positivity)) hprod.le
    _ = 2*Real.log 4 / Real.log z := by push_cast; field_simp

theorem edge_band_bounds {x z : ℕ} (hx : 32 ≤ x)
    (hz : z = Nat.nthRoot 5 (x^2) ∨ (z^3 ≥ 4*x^2+1 ∧ (z-1)^3 < 4*x^2+1)) :
    Nat.nthRoot 5 (x^2) ≤ z ∧ 2*z ≤ 5*Nat.nthRoot 3 (x^2) ∧
      1 < z ∧ Real.log (x : ℝ) ≤ 5 * Real.log (z : ℝ) := by
  let u := Nat.nthRoot 5 (x^2)
  let v := Nat.nthRoot 3 (x^2)
  have hx2 : 32^2 ≤ x^2 := Nat.pow_le_pow_left hx 2
  have hu : 2 ≤ u := (Nat.le_nthRoot_iff (by decide : 5 ≠ 0)).mpr (by omega)
  have hv : 4 ≤ v := (Nat.le_nthRoot_iff (by decide : 3 ≠ 0)).mpr (by omega)
  have hu2 : u^5 ≤ x^2 := Nat.pow_nthRoot_le (.inl (by decide))
  have hu3 : u^3 ≤ x^2 :=
    (pow_le_pow_right₀ (by omega : 1 ≤ u) (by decide : 3 ≤ 5)).trans hu2
  have huv : u ≤ v := (Nat.le_nthRoot_iff (by decide : 3 ≠ 0)).mpr hu3
  have cutoffs : u ≤ z ∧ 2*z ≤ 5*v := by
    rcases hz with rfl | ⟨hLower,hUpper⟩
    · exact ⟨le_rfl,by omega⟩
    · have hEq : (2*(v+1))^3 = 8*(v+1)^3 := by ring
      have hCub := Nat.lt_pow_nthRoot_add_one (by decide : 3 ≠ 0) (x^2)
      change x^2 < (v+1)^3 at hCub
      have hNext : 4*x^2+1 < (2*(v+1))^3 := by rw [hEq]; omega
      have hzUpper : z-1 < 2*(v+1) := by
        by_contra! h
        exact (not_le_of_gt (hUpper.trans hNext)) (Nat.pow_le_pow_left h 3)
      have hzLower : u ≤ z := by
        by_contra! h
        have hM := (Nat.pow_le_pow_left h.le 3).trans hu3
        omega
      exact ⟨hzLower,by omega⟩
  refine ⟨cutoffs.1,cutoffs.2,by omega,?_⟩
  have hNext := Nat.lt_pow_nthRoot_add_one (by decide : 5 ≠ 0) (x^2)
  change x^2 < (u+1)^5 at hNext
  have hUp : x^2 ≤ 32*u^5 := by
    have hNat := hNext.le.trans (Nat.pow_le_pow_left (show u+1 ≤ 2*u by omega) 5)
    simpa only [mul_pow, show (2 : ℕ)^5 = 32 by decide] using hNat
  have hLo : 32*x ≤ x^2 := by simpa only [pow_two] using Nat.mul_le_mul_right x hx
  have hXU : x ≤ u^5 := Nat.le_of_mul_le_mul_left (hLo.trans hUp) (by decide : 0 < 32)
  have hXZ : (x : ℝ) ≤ (z : ℝ)^5 := by exact_mod_cast hXU.trans (Nat.pow_le_pow_left cutoffs.1 5)
  have h := Real.log_le_log (show (0 : ℝ) < x by positivity) hXZ
  simpa only [Real.log_pow, Nat.cast_ofNat] using h


end QuadraticFirstFactorEdges

namespace QuadraticFirstFactorEdges

open Finset

def bandHits (x z : ℕ) : Finset ℕ := (Ioc (x/2) x).filter fun k =>
  z < (value k).minFac ∧ (value k).minFac ≤ 2*z

def switchedHits (x p r : ℕ) : Finset ℕ := (range (x+1)).filter fun t =>
  let k := p*t+r
  x < 2*k ∧ k ≤ x ∧ (value k).minFac = p

private def encode (k : ℕ) : Σ _ : ℕ, Σ _ : ℕ, ℕ :=
  ⟨(value k).minFac, ⟨k % (value k).minFac, k / (value k).minFac⟩⟩

private def decode (v : Σ _ : ℕ, Σ _ : ℕ, ℕ) : ℕ := v.1*v.2.2+v.2.1

private theorem decode_encode (k : ℕ) : decode (encode k) = k := by
  simpa only [decode,encode,Nat.add_comm] using Nat.mod_add_div k (value k).minFac

theorem band_hits_card_le (x z : ℕ) :
    (bandHits x z).card ≤ ∑ p ∈ primesBand z, ∑ r ∈ roots p, (switchedHits x p r).card := by
  let all : Finset (Σ _ : ℕ, Σ _ : ℕ, ℕ) :=
    (primesBand z).sigma fun p => (roots p).sigma fun r => switchedHits x p r
  have hh : (bandHits x z).card ≤ all.card := by
    apply card_le_card_of_injOn encode
    · intro k hk
      obtain ⟨hI,hband⟩ := mem_filter.mp hk
      have hI := mem_Ioc.mp hI
      let p := (value k).minFac
      let r := k % p
      let t := k / p
      have hkPos : 0 < k := by omega
      have hValue : value k ≠ 1 := by
        unfold value
        have hSq : 0 < k^2 := pow_pos hkPos _
        omega
      have hp : p.Prime := Nat.minFac_prime hValue
      have hd : p ∣ value k := Nat.minFac_dvd _
      have hpBand : p ∈ primesBand z := mem_filter.mpr ⟨mem_Ioc.mpr hband,hp⟩
      have hEq : r ≡ k [MOD p] := Nat.mod_modEq k p
      have hMod : value r ≡ value k [MOD p] :=
        ((Nat.ModEq.refl 4).mul (hEq.pow 2)).add (Nat.ModEq.refl 1)
      have hz : value r % p = 0 := by
        have h := hMod.trans (Nat.modEq_zero_iff_dvd.mpr hd)
        simpa only [Nat.ModEq,Nat.zero_mod] using h
      have hr : r ∈ roots p := mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt k hp.pos),hz⟩
      have htEq : p*t+r=k := decode_encode k
      have ht : t ∈ switchedHits x p r := by
        apply mem_filter.mpr
        refine ⟨mem_range.mpr (by
          have ht := (Nat.div_le_self k p).trans hI.2
          change t≤x at ht
          omega), ?_⟩
        dsimp only
        rw [htEq]
        exact ⟨by omega,hI.2,rfl⟩
      exact mem_sigma.mpr ⟨hpBand,mem_sigma.mpr ⟨hr,ht⟩⟩
    · exact (show Function.LeftInverse decode encode from decode_encode).injective.injOn
  simpa only [all,card_sigma] using hh

theorem edge_of_switched_sieve
    (hSieve : ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ x p r : ℕ, N≤x → p.Prime →
      Nat.nthRoot 5 (x^2) < p → p ≤ 5*Nat.nthRoot 3 (x^2) → r < p →
      value r % p=0 → ((switchedHits x p r).card : ℝ) ≤ C*x/(p*Real.log x)) :
    ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ x z : ℕ, N≤x →
      (z=Nat.nthRoot 5 (x^2) ∨ (z^3≥4*x^2+1 ∧ (z-1)^3<4*x^2+1)) →
      ((bandHits x z).card : ℝ) ≤ C*x/(Real.log x)^2 := by
  obtain ⟨C,hC,N,hS⟩ := hSieve
  have hL4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨20*C*Real.log 4,by positivity,max N 32,?_⟩
  intro x z hx hz
  obtain ⟨hzLo,hzHi,hzOne,hlogs⟩ := edge_band_bounds ((le_max_right N 32).trans hx) hz
  have hX : 1 < x := (show 1 < 32 by decide).trans_le ((le_max_right N 32).trans hx)
  have hLogX : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hX)
  have hLogZ : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast hzOne)
  have hb : ((bandHits x z).card : ℝ) ≤
      ∑ p ∈ primesBand z, ∑ r ∈ roots p, ((switchedHits x p r).card : ℝ) := by
    exact_mod_cast band_hits_card_le x z
  have hRate : 2*Real.log 4 / Real.log z ≤ 10*Real.log 4 / Real.log x := by
    apply (div_le_div_iff₀ hLogZ hLogX).mpr
    calc
      2*Real.log 4 * Real.log x ≤ (2*Real.log 4)*(5*Real.log z) :=
        mul_le_mul_of_nonneg_left hlogs (by positivity)
      _ = 10*Real.log 4*Real.log z := by ring
  apply hb.trans
  calc
    (∑ p ∈ primesBand z, ∑ r ∈ roots p, ((switchedHits x p r).card : ℝ)) ≤
        ∑ p ∈ primesBand z, (2*C*x/Real.log x)*(1/(p:ℝ)) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpB,hpPrime⟩ := mem_filter.mp hp
      have hpB := mem_Ioc.mp hpB
      have hPosP : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
      calc
        (∑ r ∈ roots p, ((switchedHits x p r).card : ℝ)) ≤
            ∑ _r ∈ roots p, C*x/(p*Real.log x) := by
          apply sum_le_sum
          intro r hr
          obtain ⟨hrP,hrF⟩ := mem_filter.mp hr
          exact hS x p r ((le_max_left N 32).trans hx) hpPrime (hzLo.trans_lt hpB.1)
            (hpB.2.trans hzHi) (mem_range.mp hrP) hrF
        _ = ((roots p).card : ℝ) * (C*x/(p*Real.log x)) := by rw [sum_const,nsmul_eq_mul]
        _ ≤ 2 * (C*x/(p*Real.log x)) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast roots_card_le_two hpPrime
          · positivity
        _ = (2*C*x/Real.log x)*(1/(p:ℝ)) := by field_simp
    _ = (2*C*x/Real.log x)*(∑ p ∈ primesBand z,1/(p:ℝ)) := (mul_sum _ _ _).symm
    _ ≤ (2*C*x/Real.log x)*(2*Real.log 4/Real.log z) :=
      mul_le_mul_of_nonneg_left (band_reciprocals hzOne) (by positivity)
    _ ≤ (2*C*x/Real.log x)*(10*Real.log 4/Real.log x) :=
      mul_le_mul_of_nonneg_left hRate (by positivity)
    _ = (20*C*Real.log 4)*x/(Real.log x)^2 := by field_simp; ring


end QuadraticFirstFactorEdges

theorem Conjectures.QuadraticPrimes.FirstFactorEdgeBands :
    ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ x z : ℕ, N≤x → (z=Nat.nthRoot 5 (x^2) ∨ (z^3≥4*x^2+1 ∧ (z-1)^3<4*x^2+1)) → (((Finset.Ioc (x/2) x).filter fun k => z<(4*k^2+1).minFac ∧ (4*k^2+1).minFac≤2*z).card : ℝ) ≤ C*x/(Real.log x)^2 := by
  exact QuadraticFirstFactorEdges.edge_of_switched_sieve
    Conjectures.QuadraticPrimes.SwitchedCofactorSmallSieve
