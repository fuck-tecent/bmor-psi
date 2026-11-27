import Mathlib

/-! Ramanujan sums at all frequencies, their integrated form, and their mean absolute bound. -/

namespace GoldbachRamanujan

open Finset Polynomial
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

private noncomputable def primitiveTrace (k : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun q => ∑ z ∈ primitiveRoots q ℂ, z ^ k, by simp [primitiveRoots_zero]⟩

private def divisibleTrace (k : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun q => if q ∣ k then (q : ℂ) else 0, by simp⟩

private theorem all_roots_trace {q : ℕ} (hq : 0 < q) (k : ℕ) :
    (∑ z ∈ nthRootsFinset q (1 : ℂ), z ^ k) = divisibleTrace k q := by
  let _ : NeZero q := ⟨hq.ne'⟩
  let u := Complex.exp (2 * Real.pi * Complex.I / q)
  have hu : IsPrimitiveRoot u q := Complex.isPrimitiveRoot_exp q hq.ne'
  have param : (∑ i ∈ range q, (u^k)^i) = ∑ z ∈ nthRootsFinset q (1 : ℂ), z ^ k := by
    apply sum_bij (fun i _ => u ^ i)
    · intro i _
      apply (Polynomial.mem_nthRootsFinset hq _).mpr
      rw [← pow_mul, Nat.mul_comm, pow_mul, hu.pow_eq_one, one_pow]
    · intro i hi j hj heq
      exact hu.pow_inj (mem_range.mp hi) (mem_range.mp hj) heq
    · intro z hz
      obtain ⟨i, hi, heq⟩ := hu.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hq _).mp hz)
      exact ⟨i, mem_range.mpr hi, heq⟩
    · intro i _
      rw [← pow_mul, Nat.mul_comm, pow_mul]
  rw [← param]
  change _ = if q ∣ k then (q : ℂ) else 0
  by_cases h : q ∣ k
  · simp [(hu.pow_eq_one_iff_dvd k).2 h, h]
  · have hne := (hu.pow_eq_one_iff_dvd k).not.mpr h
    have hp : (u^k)^q = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul, hu.pow_eq_one, one_pow]
    simp [geom_sum_eq hne, hp, h]

private theorem invert_trace (k : ℕ) :
    primitiveTrace k = divisibleTrace k * (μ : ArithmeticFunction ℂ) := by
  classical
  have conv : primitiveTrace k * (ζ : ArithmeticFunction ℂ) = divisibleTrace k := by
    ext q
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    change (∑ d ∈ q.divisors, ∑ z ∈ primitiveRoots d ℂ, z ^ k) = _
    rw [← sum_biUnion (fun _ _ _ _ hd => IsPrimitiveRoot.disjoint (R := ℂ) hd),
      ← IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots]
    rcases q with _ | q
    · simp
    · exact all_roots_trace (Nat.succ_pos _) k
  calc
    _ = primitiveTrace k * ((ζ : ArithmeticFunction ℂ) * (μ : ArithmeticFunction ℂ)) := by simp
    _ = (primitiveTrace k * (ζ : ArithmeticFunction ℂ)) * (μ : ArithmeticFunction ℂ) :=
      (mul_assoc ..).symm
    _ = _ := by rw [conv]

/-- Sum the exact catalogue phase over reduced centers. No coprimality is required of k. -/
theorem all_frequencies {q : ℕ} (hq : 0 < q) (k : ℕ) :
    (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      Complex.exp (((2*Real.pi*(k:ℝ)*a/q : ℝ):ℂ)*Complex.I)) =
        ∑ d ∈ q.divisors, (if d ∣ k then (d : ℂ) else 0) *
          (ArithmeticFunction.moebius (q/d) : ℂ) := by
  let _ : NeZero q := ⟨hq.ne'⟩
  let u := Complex.exp (2 * Real.pi * Complex.I / q)
  have hu : IsPrimitiveRoot u q := Complex.isPrimitiveRoot_exp q hq.ne'
  calc
    _ = ∑ z ∈ primitiveRoots q ℂ, z^k := by
      apply sum_bij (fun a _ => u ^ a)
      · intro a ha
        exact (mem_primitiveRoots hq).mpr (hu.pow_of_coprime a (mem_filter.mp ha).2)
      · intro i hi j hj heq
        exact hu.pow_inj (mem_range.mp (mem_filter.mp hi).1) (mem_range.mp (mem_filter.mp hj).1) heq
      · intro z hz
        obtain ⟨a, ha, hc, heq⟩ := hu.isPrimitiveRoot_iff.mp ((mem_primitiveRoots hq).mp hz)
        exact ⟨a, mem_filter.mpr ⟨mem_range.mpr ha, hc⟩, heq⟩
      · intro a _
        dsimp [u]
        rw [← pow_mul, ← Complex.exp_nat_mul]
        congr 1
        push_cast
        ring
    _ = _ := by
      change primitiveTrace k q = _
      rw [invert_trace, ArithmeticFunction.mul_apply,
        Nat.sum_divisorsAntidiagonal (fun x y => divisibleTrace k x * (μ : ArithmeticFunction ℂ) y)]
      rfl

end GoldbachRamanujan

namespace GoldbachRamanujan

private noncomputable def wave (ω t : ℝ) : ℂ := Complex.exp (((ω*t : ℝ) : ℂ)*Complex.I)

private theorem wave_add (ω x y : ℝ) : wave ω (x+y) = wave ω x * wave ω y := by
  unfold wave
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem interval_wave (ω x R : ℝ) (hω : ω ≠ 0) :
    (∫ t in (x-R)..(x+R), wave ω t) = wave ω x * ((2*Real.sin (ω*R)/ω : ℝ) : ℂ) := by
  have translate := intervalIntegral.integral_comp_add_left (a := -R) (b := R) (wave ω) x
  rw [← sub_eq_add_neg] at translate
  rw [← translate]
  simp_rw [wave_add]
  rw [intervalIntegral.integral_const_mul]
  apply congrArg (fun z : ℂ => wave ω x * z)
  change (∫ t in -R..R, (fun y : ℝ => Complex.exp ((y : ℂ)*Complex.I)) (ω*t)) = _
  rw [intervalIntegral.integral_comp_mul_left (a := -R) (b := R)
    (fun y : ℝ => Complex.exp ((y : ℂ)*Complex.I)) hω, mul_neg, integral_exp_mul_I_eq_sin]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul,
    Complex.ofReal_ofNat, div_eq_mul_inv]
  ring

/-- Fourier mode on the full periodic arcs at one denominator, with arbitrary common radius.
The q=1 term is a single interval about 0 on the real line. -/
theorem arcs_at_denominator {q k : ℕ} (hq : 0 < q) (hk : 0 < k) (R : ℝ) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ∫ t in ((a:ℝ)/q-R)..((a:ℝ)/q+R),
        Complex.exp (((2*Real.pi*(k:ℝ)*t : ℝ):ℂ)*Complex.I)) =
      (∑ d ∈ q.divisors, (if d ∣ k then (d:ℂ) else 0) *
        (ArithmeticFunction.moebius (q/d):ℂ)) *
      ((Real.sin (2*Real.pi*(k:ℝ)*R)/(Real.pi*k) : ℝ):ℂ) := by
  let ω := 2*Real.pi*(k:ℝ)
  have hω : ω ≠ 0 := by dsimp [ω]; positivity
  have factor : 2*Real.sin (ω*R)/ω = Real.sin (2*Real.pi*(k:ℝ)*R)/(Real.pi*k) := by
    dsimp [ω]
    ring
  change (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
    ∫ t in ((a:ℝ)/q-R)..((a:ℝ)/q+R), wave ω t) = _
  simp_rw [interval_wave _ _ _ hω, factor]
  rw [← Finset.sum_mul, ← all_frequencies hq k]
  apply congrArg (fun z : ℂ => z * ((Real.sin (2*Real.pi*(k:ℝ)*R)/(Real.pi*k):ℝ):ℂ))
  apply Finset.sum_congr rfl
  intro a _
  unfold wave ω
  rw [← mul_div_assoc]

end GoldbachRamanujan

namespace GoldbachMinor

open Finset

noncomputable def ram (q k : ℕ) : ℝ :=
  ∑ d ∈ q.divisors, (if d ∣ k then (d:ℝ) else 0) * (ArithmeticFunction.moebius (q/d):ℝ)

noncomputable def arcLength (Q n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, q.totient * (2*(Q:ℝ)/(q*n))

noncomputable def majorCoefficient (Q n k : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ram q k *
    (Real.sin (2*Real.pi*(k:ℝ)*((Q:ℝ)/(q*n))) / (Real.pi*k))

noncomputable def minorCoefficient (Q n k : ℕ) : ℝ :=
  if k=0 then 1 - arcLength Q n else -majorCoefficient Q n k

end GoldbachMinor

namespace GoldbachMinor
open Finset

noncomputable def harmonicCutoff (Q : ℕ) : ℝ := ∑ d ∈ Finset.Icc 1 Q, 1/(d:ℝ)

private theorem harmonic_divisors (Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (q.divisors.card:ℝ)/(q:ℝ)) ≤ harmonicCutoff Q ^ 2 := by
  classical
  let F (p : ℕ × ℕ) : ℝ := (1/(p.1:ℝ))*(1/(p.2:ℝ))
  let S := Finset.Icc 1 Q
  have eq (q : ℕ) (hq : q ∈ S) :
      (q.divisors.card:ℝ)/q = ∑ p ∈ q.divisorsAntidiagonal, F p := by
    change _ = ∑ p ∈ q.divisorsAntidiagonal, 1/(p.1:ℝ)*(1/(p.2:ℝ))
    rw [Nat.sum_divisorsAntidiagonal (fun x y => 1/(x:ℝ)*(1/(y:ℝ)))]
    calc
      _ = ∑ _d ∈ q.divisors, 1/(q:ℝ) := by simp [div_eq_mul_inv,nsmul_eq_mul]
      _ = _ := by
        apply sum_congr rfl
        intro d hd
        have hprod : (d:ℝ)*((q/d:ℕ):ℝ) = q := by exact_mod_cast Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1
        rw [one_div_mul_one_div,hprod]
  have disj : (S:Set ℕ).PairwiseDisjoint Nat.divisorsAntidiagonal := by
    intro q _ r _ hqr
    apply disjoint_left.mpr
    intro p hp hp'
    exact hqr ((Nat.mem_divisorsAntidiagonal.mp hp).1.symm.trans (Nat.mem_divisorsAntidiagonal.mp hp').1)
  have sub : S.biUnion Nat.divisorsAntidiagonal ⊆ S ×ˢ S := by
    intro p hp
    obtain ⟨q,hq,hp⟩ := mem_biUnion.mp hp
    obtain ⟨h1,h2⟩ := mem_Icc.mp hq
    obtain ⟨e,_⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have hpos : 0 < p.1*p.2 := e ▸ h1
    have ha : 0 < p.1 := Nat.pos_of_ne_zero (left_ne_zero_of_mul hpos.ne')
    have hb : 0 < p.2 := Nat.pos_of_ne_zero (right_ne_zero_of_mul hpos.ne')
    have ha' : p.1≤q := by rw [←e]; exact Nat.le_mul_of_pos_right _ hb
    have hb' : p.2≤q := by rw [←e,mul_comm]; exact Nat.le_mul_of_pos_right _ ha
    exact mem_product.mpr ⟨mem_Icc.mpr ⟨ha,ha'.trans h2⟩,mem_Icc.mpr ⟨hb,hb'.trans h2⟩⟩
  calc
    _ = ∑ q ∈ S, ∑ p ∈ q.divisorsAntidiagonal, F p := sum_congr rfl eq
    _ = ∑ p ∈ S.biUnion Nat.divisorsAntidiagonal, F p := (sum_biUnion disj).symm
    _ ≤ ∑ p ∈ S ×ˢ S, F p := sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by dsimp [F]; positivity)
    _ = _ := by simp [F, S, harmonicCutoff, sq, sum_product, sum_mul, mul_sum]; rw [sum_comm]

private theorem ram_frequency_sum (q K : ℕ) : (∑ k ∈ Finset.Icc 1 K, |ram q k|) ≤
    (K:ℝ)*q.divisors.card := by
  have one (k : ℕ) : |ram q k| ≤ ∑ d ∈ q.divisors, if d ∣ k then (d:ℝ) else 0 := by
    refine (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum (fun d _ => ?_))
    split_ifs <;> rcases ArithmeticFunction.moebius_eq_or (q/d) with h|h|h <;> simp [h]
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 K, ∑ d ∈ q.divisors, if d ∣ k then (d:ℝ) else 0 :=
      sum_le_sum (fun k _ => one k)
    _ = ∑ d ∈ q.divisors, ∑ k ∈ Finset.Icc 1 K, if d ∣ k then (d:ℝ) else 0 := sum_comm
    _ ≤ ∑ _d ∈ q.divisors, (K:ℝ) := by
      apply sum_le_sum
      intro d _
      have same : Finset.Icc 1 K = Finset.Ioc 0 K := by ext k; simp only [mem_Icc,mem_Ioc]; omega
      rw [same, ← sum_filter, sum_const, Nat.Ioc_filter_dvd_card_eq_div,nsmul_eq_mul]
      exact_mod_cast Nat.div_mul_le_self K d
    _ = _ := by simp [mul_comm]

/-- Averaged nonzero Fourier modes: the two harmonic factors come from summing divisors,
while the denominator Q enters only to the first power. -/
theorem coefficient_mean (Q n K : ℕ) (hn : 0<n) :
    (∑ k ∈ Finset.Icc 1 K, |majorCoefficient Q n k|) ≤
      (2*(Q:ℝ)/n)*K*(harmonicCutoff Q)^2 := by
  let A := 2*(Q:ℝ)/n
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have term (k : ℕ) (hk : k ∈ Finset.Icc 1 K) : |majorCoefficient Q n k| ≤
      ∑ q ∈ Finset.Icc 1 Q, (A/(q:ℝ))*|ram q k| := by
    have hkp : 0<(k:ℝ) := by exact_mod_cast (mem_Icc.mp hk).1
    have hp : 0<Real.pi*(k:ℝ) := mul_pos Real.pi_pos hkp
    refine (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum (fun q hq => ?_))
    have hq' : 0<(q:ℝ) := by exact_mod_cast (mem_Icc.mp hq).1
    have hx : 0≤2*Real.pi*(k:ℝ)*((Q:ℝ)/(q*n)) := by positivity
    have hs := Real.abs_sin_le_abs (x:=2*Real.pi*(k:ℝ)*((Q:ℝ)/(q*n)))
    rw [abs_of_nonneg hx] at hs
    rw [abs_mul,abs_div,abs_of_pos hp,mul_comm (A/(q:ℝ))]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    refine (div_le_div_of_nonneg_right hs hp.le).trans_eq ?_
    dsimp [A]
    field_simp
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 K, ∑ q ∈ Finset.Icc 1 Q, (A/(q:ℝ))*|ram q k| := sum_le_sum term
    _ = ∑ q ∈ Finset.Icc 1 Q, (A/(q:ℝ)) * (∑ k ∈ Finset.Icc 1 K, |ram q k|) := by
      rw [sum_comm]; simp_rw [mul_sum]
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, (A/(q:ℝ))*((K:ℝ)*q.divisors.card) := by
      apply sum_le_sum
      intro q _
      exact mul_le_mul_of_nonneg_left (ram_frequency_sum q K) (by positivity)
    _ = A*K*(∑ q ∈ Finset.Icc 1 Q, (q.divisors.card:ℝ)/q) := by
      rw [mul_sum]; apply sum_congr rfl; intro q _; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_divisors Q) (mul_nonneg hA (by positivity))

end GoldbachMinor
