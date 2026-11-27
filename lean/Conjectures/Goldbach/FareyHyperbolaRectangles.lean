import Mathlib

/-! # Counting points on a modular hyperbola in a rectangle

Fourier inversion in the second coordinate expresses the count in terms of a
reciprocal sum on the first interval. We bound its nonzero frequencies with
the complete Weil estimate for composite moduli and a gcd-weighted bound for
the Fourier coefficients of an interval. Applying the same estimate to the
full first interval centers the count at the product of the two lengths times
the totient divided by the square of the modulus. This also covers empty
intervals. The contribution of the zero frequency is computed exactly.

The project formulation cites Igor Shparlinski, Modular Hyperbolas, Theorem 13
and equation (10), https://arxiv.org/abs/1103.2879.
-/

/- Portions adapted from the MathlibNt library of subfish-zhou/goldbach-lean,
Copyright 2026 UyNewNas. Distributed under the Apache License, Version 2.0. A copy of the license
accompanies this repository in LICENSE.
https://github.com/subfish-zhou/goldbach-lean/tree/9d4c3a4010d42aedd9e7231bf94386019cfffccc/MathlibNt/AnalyticNumberTheory/LargeSieve
Each SOURCE comment records the original module name. The modules have
been joined into a single file, with their scopes preserved, and the
proof scripts updated for the toolchain pinned by this repository. -/

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryCompletion -/

/-!
# Finite Fourier completion of the reciprocal sum

The modulus is any positive natural number, including one. Neither frequency
is assumed coprime to it. These are finite identities and bounds, not an
assertion of the complete Kloosterman square-root estimate.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

variable {q : ℕ} [NeZero q]

def reciprocalPhase (q : ℕ) [NeZero q] (d : ℤ) (u : ZMod q) : ℂ :=
  if IsUnit u then ZMod.stdAddChar ((d : ZMod q) * u⁻¹) else 0

def completeKloosterman (q : ℕ) [NeZero q] (m : ZMod q) (d : ℤ) : ℂ :=
  ∑ u : ZMod q, ZMod.stdAddChar (m * u) * reciprocalPhase q d u

/-- The integers in the interval are `A, A+1, ..., A+L-1`. -/
def incompleteReciprocal (q : ℕ) [NeZero q] (d A : ℤ) (L : ℕ) : ℂ :=
  ∑ j ∈ range L, reciprocalPhase q d ((A : ZMod q) + (j : ZMod q))

def intervalFourier (q : ℕ) [NeZero q] (A : ℤ) (L : ℕ) (m : ZMod q) : ℂ :=
  ∑ j ∈ range L, ZMod.stdAddChar (m * ((A : ZMod q) + (j : ZMod q)))

theorem completeKloosterman_eq (m : ZMod q) (d : ℤ) :
    completeKloosterman q m d =
      ∑ u : ZMod q, if IsUnit u then
        ZMod.stdAddChar (m * u + (d : ZMod q) * u⁻¹) else 0 := by
  classical
  simp only [completeKloosterman, reciprocalPhase, AddChar.map_add_eq_mul]
  apply sum_congr rfl
  intro u _
  split_ifs <;> simp

theorem dft_reciprocalPhase (d : ℤ) (m : ZMod q) :
    ZMod.dft (reciprocalPhase q d) m = completeKloosterman q (-m) d := by
  simp only [ZMod.dft_apply, completeKloosterman, smul_eq_mul, neg_mul]
  congr 1 with u
  rw [mul_comm u m]

theorem reciprocalPhase_fourier (d : ℤ) (u : ZMod q) :
    reciprocalPhase q d u = (q : ℂ)⁻¹ *
      ∑ m : ZMod q, ZMod.stdAddChar (m * u) * completeKloosterman q (-m) d := by
  have h := congrFun (ZMod.dft.symm_apply_apply (reciprocalPhase q d)) u
  simpa only [ZMod.invDFT_apply, smul_eq_mul, dft_reciprocalPhase] using h.symm

/-- Exact completion, even for intervals longer than a period. -/
theorem incompleteReciprocal_completion (d A : ℤ) (L : ℕ) :
    incompleteReciprocal q d A L = (q : ℂ)⁻¹ *
      ∑ m : ZMod q, intervalFourier q A L m * completeKloosterman q (-m) d := by
  unfold incompleteReciprocal
  simp_rw [reciprocalPhase_fourier]
  rw [← mul_sum, sum_comm]
  simp_rw [← sum_mul]
  rfl

theorem stdAddChar_norm (u : ZMod q) : ‖ZMod.stdAddChar u‖ = 1 := by
  exact Circle.norm_coe (ZMod.toCircle u)


theorem intervalFourier_norm_le_length (A : ℤ) (L : ℕ) (m : ZMod q) :
    ‖intervalFourier q A L m‖ ≤ L := by
  unfold intervalFourier
  simpa only [stdAddChar_norm, sum_const, card_range, nsmul_eq_mul, mul_one] using
    norm_sum_le (range L) (fun j ↦ ZMod.stdAddChar
      (m * ((A : ZMod q) + (j : ZMod q))))

theorem intervalFourier_eq_geom (A : ℤ) (L : ℕ) (m : ZMod q) :
    intervalFourier q A L m =
      ZMod.stdAddChar (m * (A : ZMod q)) *
        ∑ j ∈ range L, (ZMod.stdAddChar m) ^ j := by
  simp only [intervalFourier, mul_add, AddChar.map_add_eq_mul, mul_sum]
  apply sum_congr rfl
  intro j _
  rw [mul_comm m (j : ZMod q), ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]

theorem intervalFourier_norm_mul (A : ℤ) (L : ℕ) (m : ZMod q) :
    ‖intervalFourier q A L m‖ * ‖ZMod.stdAddChar m - 1‖ ≤ 2 := by
  rw [intervalFourier_eq_geom, norm_mul, stdAddChar_norm, one_mul, ← norm_mul,
    geom_sum_mul]
  calc
    ‖ZMod.stdAddChar m ^ L - 1‖ ≤ ‖ZMod.stdAddChar m ^ L‖ + ‖(1 : ℂ)‖ :=
      norm_sub_le _ _
    _ = 2 := by rw [norm_pow, stdAddChar_norm]; norm_num

theorem incompleteReciprocal_norm_le_completion (d A : ℤ) (L : ℕ) (B : ℝ)
    (hB : ∀ m : ZMod q, ‖completeKloosterman q m d‖ ≤ B) :
    ‖incompleteReciprocal q d A L‖ ≤
      (q : ℝ)⁻¹ * (∑ m : ZMod q, ‖intervalFourier q A L m‖) * B := by
  rw [incompleteReciprocal_completion, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    (q : ℝ)⁻¹ * ‖∑ m : ZMod q,
        intervalFourier q A L m * completeKloosterman q (-m) d‖
      ≤ (q : ℝ)⁻¹ * ∑ m : ZMod q,
        ‖intervalFourier q A L m‖ * B := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine (norm_sum_le _ _).trans (sum_le_sum fun m _ ↦ ?_)
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hB (-m)) (norm_nonneg _)
    _ = _ := by rw [← sum_mul]; ring

theorem completeKloosterman_modulus_one (m : ZMod 1) (d : ℤ) :
    completeKloosterman 1 m d = 1 := by
  have hu (u : ZMod 1) : IsUnit u := by
    rw [Subsingleton.elim u 1]; exact isUnit_one
  have he (u : ZMod 1) : ZMod.stdAddChar u = 1 := by
    rw [Subsingleton.elim u 0]; simp
  rw [completeKloosterman_eq]
  simp only [hu, if_true, he, sum_const, card_univ, ZMod.card, nsmul_eq_mul,
    Nat.cast_one, one_mul]


private theorem sin_pi_mul_lower {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    2 * min t (1 - t) ≤ Real.sin (Real.pi * t) := by
  have half (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
      2 * s ≤ Real.sin (Real.pi * s) := by
    have h := Real.mul_le_sin (mul_nonneg Real.pi_pos.le hs0)
      (show Real.pi * s ≤ Real.pi / 2 by nlinarith [Real.pi_pos])
    convert h using 1
    field_simp
  by_cases ht : t ≤ 1 / 2
  · rw [min_eq_left (by linarith)]
    exact half t h0 ht
  · rw [min_eq_right (by linarith)]
    have h := half (1 - t) (by linarith) (by linarith)
    simpa only [mul_sub, mul_one, Real.sin_pi_sub] using h

theorem stdAddChar_sub_one_lower (k : ℕ) (hk : k ≤ q) :
    4 * min (k : ℝ) ((q : ℝ) - k) ≤
      (q : ℝ) * ‖ZMod.stdAddChar (k : ZMod q) - 1‖ := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hkR : (k : ℝ) ≤ q := by exact_mod_cast hk
  have ht0 : 0 ≤ (k : ℝ) / q := by positivity
  have ht1 : (k : ℝ) / q ≤ 1 := (div_le_one hq).2 hkR
  have hs := sin_pi_mul_lower ht0 ht1
  have hs0 : 0 ≤ Real.sin (Real.pi * ((k : ℝ) / q)) :=
    (mul_nonneg (by norm_num) (le_min ht0 (by linarith))).trans hs
  have he : ZMod.stdAddChar (k : ZMod q) =
      Complex.exp (Complex.I * ((2 * Real.pi * ((k : ℝ) / q) : ℝ) : ℂ)) := by
    rw [← Int.cast_natCast k, ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2 * Real.pi * ((k : ℝ) / q) / 2 =
    Real.pi * ((k : ℝ) / q) by ring]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hs0)]
  have hmin : min ((k : ℝ) / q) (1 - (k : ℝ) / q) =
      min (k : ℝ) ((q : ℝ) - k) / q := by
    rw [← min_div_div_right hq.le, sub_div, div_self hq.ne']
  rw [hmin] at hs
  have hh := mul_le_mul_of_nonneg_left hs hq.le
  field_simp at hh
  rw [show Real.pi * ((k : ℝ) / q) = (k : ℝ) * Real.pi / q by ring]
  nlinarith

theorem intervalFourier_norm_le_reciprocals (A : ℤ) (L k : ℕ)
    (hk0 : 0 < k) (hkq : k < q) :
    ‖intervalFourier q A L (k : ZMod q)‖ ≤
      (q : ℝ) * ((k : ℝ)⁻¹ + ((q - k : ℕ) : ℝ)⁻¹) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hk : (0 : ℝ) < k := by exact_mod_cast hk0
  have hqk : (0 : ℝ) < (q : ℝ) - k := sub_pos.mpr (by exact_mod_cast hkq)
  have hlow := stdAddChar_sub_one_lower k hkq.le
  have hu := intervalFourier_norm_mul A L (k : ZMod q)
  have hm := mul_le_mul_of_nonneg_left hlow
    (norm_nonneg (intervalFourier q A L (k : ZMod q)))
  have huq := mul_le_mul_of_nonneg_left hu hq.le
  rw [Nat.cast_sub hkq.le]
  by_cases hhalf : (k : ℝ) ≤ (q : ℝ) - k
  · rw [min_eq_left hhalf] at hm
    have hb : ‖intervalFourier q A L (k : ZMod q)‖ ≤ (q : ℝ) / k := by
      apply (le_div_iff₀ hk).2
      nlinarith
    exact hb.trans (by
      rw [div_eq_mul_inv, mul_add]
      exact le_add_of_nonneg_right (by positivity))
  · rw [min_eq_right (le_of_not_ge hhalf)] at hm
    have hb : ‖intervalFourier q A L (k : ZMod q)‖ ≤ (q : ℝ) / ((q : ℝ) - k) := by
      apply (le_div_iff₀ hqk).2
      nlinarith
    exact hb.trans (by
      rw [div_eq_mul_inv, mul_add]
      exact le_add_of_nonneg_left (by positivity))

private theorem sum_zmod_eq_range (f : ZMod q → ℝ) :
    ∑ u : ZMod q, f u = ∑ k ∈ range q, f (k : ZMod q) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)
  rw [← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl (fun i _ => congrArg f (ZMod.natCast_zmod_val i).symm)


/-- The normalized interval Fourier L1 norm costs only one logarithm. -/
theorem intervalFourier_lone (A : ℤ) (L : ℕ) (hL : L ≤ q) :
    ∑ m : ZMod q, ‖intervalFourier q A L m‖ ≤
      (q : ℝ) * (3 + 2 * Real.log q) := by
  have hq : 0 < q := NeZero.pos q
  rw [sum_zmod_eq_range, sum_range_eq_add_Ico _ hq]
  have hs : ∑ k ∈ Ico 1 q, ‖intervalFourier q A L (k : ZMod q)‖ ≤
      (q : ℝ) * (2 * (harmonic q : ℝ)) := by
    calc
      _ ≤ ∑ k ∈ Ico 1 q,
          (q : ℝ) * ((k : ℝ)⁻¹ + ((q - k : ℕ) : ℝ)⁻¹) :=
        sum_le_sum fun k hk ↦ intervalFourier_norm_le_reciprocals A L k
          (mem_Ico.mp hk).1 (mem_Ico.mp hk).2
      _ = (q : ℝ) * (2 * ∑ k ∈ Ico 1 q, (k : ℝ)⁻¹) := by
        rw [← mul_sum, sum_add_distrib,
          sum_Ico_reflect (fun n : ℕ ↦ (n : ℝ)⁻¹) 1 (m := q) (n := q) (by omega)]
        simp only [Nat.add_sub_cancel_left, Nat.add_sub_cancel_right]
        ring
      _ ≤ _ := by
        gcongr
        rw [harmonic_eq_sum_Icc, Rat.cast_sum]
        simp only [Rat.cast_inv, Rat.cast_natCast]
        exact sum_le_sum_of_subset_of_nonneg
          (fun k hk ↦ mem_Icc.mpr ⟨(mem_Ico.mp hk).1, (mem_Ico.mp hk).2.le⟩)
          (fun _ _ _ ↦ by positivity)
  have hzero : ‖intervalFourier q A L (0 : ZMod q)‖ ≤ (q : ℝ) :=
    (intervalFourier_norm_le_length A L 0).trans (by exact_mod_cast hL)
  have hh := harmonic_le_one_add_log q
  have hp := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ q by positivity)
  simp only [Nat.cast_zero]
  nlinarith

theorem incompleteReciprocal_norm_le_log (d A : ℤ) (L : ℕ) (hL : L ≤ q)
    (B : ℝ) (hB : ∀ m : ZMod q, ‖completeKloosterman q m d‖ ≤ B) :
    ‖incompleteReciprocal q d A L‖ ≤ (3 + 2 * Real.log q) * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  refine (incompleteReciprocal_norm_le_completion d A L B hB).trans ?_
  calc
    _ ≤ (q : ℝ)⁻¹ * ((q : ℝ) * (3 + 2 * Real.log q)) * B := by
      gcongr
      exact intervalFourier_lone A L hL
    _ = _ := by field_simp

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKloostermanCRT -/

/-!
# Twisted Chinese remaindering for the actual complete Kloosterman sum

The two twists are the integer Bezout coefficients: `m * gcdA m n +
n * gcdB m n = 1`. Thus `gcdB m n` is the inverse of `n` modulo `m`.
No frequency is required to be a unit, and either coprime factor may be one.
These are exact arithmetic identities, not an invocation of a Weil bound.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem stdAddChar_mul_modulus (q r : ℕ) [NeZero q] [NeZero r] (z : ℤ) :
    ZMod.stdAddChar ((r : ZMod (q * r)) * (z : ZMod (q * r))) =
      ZMod.stdAddChar (z : ZMod q) := by
  rw [← Int.cast_natCast r, ← Int.cast_mul, ZMod.stdAddChar_coe,
    ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hr : (r : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne r
  field_simp

theorem zmod_map_inv_of_isUnit {q r : ℕ} (f : ZMod q →+* ZMod r)
    {u : ZMod q} (hu : IsUnit u) : f u⁻¹ = (f u)⁻¹ := by
  obtain ⟨v, rfl⟩ := hu
  rw [ZMod.inv_coe_unit]
  exact (Units.coe_map_inv f.toMonoidHom v).symm.trans
    (ZMod.inv_coe_unit (Units.map f.toMonoidHom v)).symm

theorem stdAddChar_crt (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (z : ZMod (m * n)) :
    ZMod.stdAddChar z =
      ZMod.stdAddChar ((m.gcdB n : ZMod m) * (ZMod.chineseRemainder h z).1) *
      ZMod.stdAddChar ((m.gcdA n : ZMod n) * (ZMod.chineseRemainder h z).2) := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective z
  have hab : (n : ℤ) * m.gcdB n + (m : ℤ) * m.gcdA n = 1 := by
    have hh := Nat.gcd_eq_gcd_ab m n
    rw [h.gcd_eq_one] at hh
    simpa only [Nat.cast_one, add_comm] using hh.symm
  have he : (a : ZMod (m * n)) =
      (n : ZMod (m * n)) * ((m.gcdB n * a : ℤ) : ZMod (m * n)) +
      (m : ZMod (m * n)) * ((m.gcdA n * a : ℤ) : ZMod (m * n)) := by
    have hh := congrArg (fun t : ℤ ↦ (t : ZMod (m * n))) (congrArg (· * a) hab)
    push_cast at hh
    push_cast
    linear_combination -hh
  have hn : ZMod.stdAddChar
      ((m : ZMod (m * n)) * ((m.gcdA n * a : ℤ) : ZMod (m * n))) =
      ZMod.stdAddChar ((m.gcdA n * a : ℤ) : ZMod n) := by
    rw [← Int.cast_natCast m, ← Int.cast_mul, ZMod.stdAddChar_coe,
      ZMod.stdAddChar_coe]
    congr 1
    push_cast
    have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
    field_simp
  calc
    _ = ZMod.stdAddChar
        ((n : ZMod (m * n)) * ((m.gcdB n * a : ℤ) : ZMod (m * n))) *
        ZMod.stdAddChar
        ((m : ZMod (m * n)) * ((m.gcdA n * a : ℤ) : ZMod (m * n))) := by
      rw [← AddChar.map_add_eq_mul, ← he]
    _ = _ := by
      rw [stdAddChar_mul_modulus, hn]
      simp only [map_intCast, Int.cast_mul, Prod.fst_intCast, Prod.snd_intCast]

/-- Multiplicativity with both frequencies twisted by the opposite modulus's inverse. -/
theorem completeKloosterman_crt (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (a d : ℤ) :
    completeKloosterman (m * n) (a : ZMod (m * n)) d =
      completeKloosterman m ((a * m.gcdB n : ℤ) : ZMod m) (d * m.gcdB n) *
      completeKloosterman n ((a * m.gcdA n : ℤ) : ZMod n) (d * m.gcdA n) := by
  classical
  let e := ZMod.chineseRemainder h
  let f : ZMod (m * n) →+* ZMod m := (RingHom.fst _ _).comp e.toRingHom
  let g : ZMod (m * n) →+* ZMod n := (RingHom.snd _ _).comp e.toRingHom
  have hu (u : ZMod (m * n)) : IsUnit u ↔ IsUnit (f u) ∧ IsUnit (g u) := by
    constructor
    · intro hh
      exact ⟨hh.map f, hh.map g⟩
    · intro hh
      have he : IsUnit (e u) := Prod.isUnit_iff.mpr hh
      simpa using he.map e.symm.toRingHom
  simp_rw [completeKloosterman_eq]
  rw [sum_mul]
  simp_rw [mul_sum]
  let F := fun p : ZMod m × ZMod n ↦
      (if IsUnit p.1 then ZMod.stdAddChar
        (((a * m.gcdB n : ℤ) : ZMod m) * p.1 +
          ((d * m.gcdB n : ℤ) : ZMod m) * p.1⁻¹) else 0) *
      (if IsUnit p.2 then ZMod.stdAddChar
        (((a * m.gcdA n : ℤ) : ZMod n) * p.2 +
          ((d * m.gcdA n : ℤ) : ZMod n) * p.2⁻¹) else 0)
  change _ = ∑ x : ZMod m, ∑ y : ZMod n, F (x, y)
  rw [← Fintype.sum_prod_type F]
  apply Fintype.sum_equiv e.toEquiv
  intro u
  change (if IsUnit u then _ else _) =
    (if IsUnit (f u) then _ else _) * (if IsUnit (g u) then _ else _)
  by_cases hunit : IsUnit u
  · have hfg := (hu u).mp hunit
    simp only [hunit, hfg.1, hfg.2, if_true]
    rw [stdAddChar_crt m n h]
    change ZMod.stdAddChar ((m.gcdB n : ZMod m) *
        f ((a : ZMod (m * n)) * u + (d : ZMod (m * n)) * u⁻¹)) *
      ZMod.stdAddChar ((m.gcdA n : ZMod n) *
        g ((a : ZMod (m * n)) * u + (d : ZMod (m * n)) * u⁻¹)) = _
    simp only [map_add, map_mul, map_intCast, zmod_map_inv_of_isUnit _ hunit,
      Int.cast_mul]
    rw [show f u = (e.toEquiv u).1 from rfl, show g u = (e.toEquiv u).2 from rfl]
    congr 2 <;> ring
  · have hfg := not_and_or.mp (mt (hu u).mpr hunit)
    rcases hfg with hf | hg
    · simp [hunit, hf]
    · simp [hunit, hg]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKloostermanDescent -/

/-!
# Common-frequency descent

Reduction of units is surjective even when the removed factor is not coprime
to the retained modulus. Its uniform fibers give a totient ratio, not in
general the removed factor. In particular the modulus-one endpoint is retained.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem completeKloosterman_eq_sum_units (q : ℕ) [NeZero q] (a : ZMod q) (d : ℤ) :
    completeKloosterman q a d =
      ∑ u : (ZMod q)ˣ, ZMod.stdAddChar (a * (u : ZMod q) +
        (d : ZMod q) * (↑u⁻¹ : ZMod q)) := by
  classical
  rw [completeKloosterman_eq]
  symm
  apply Fintype.sum_of_injective Units.val Units.val_injective
  · intro u hu
    have hn : ¬ IsUnit u := by
      rintro ⟨v, rfl⟩
      exact hu ⟨v, rfl⟩
    simp [hn]
  · intro u
    simp [u.isUnit, ZMod.inv_coe_unit]

private theorem sum_comp_surjective_mul_card {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (f : G →* H) (hf : Function.Surjective f) (F : H → ℂ) :
    (Fintype.card H : ℂ) * (∑ x : G, F (f x)) =
      (Fintype.card G : ℂ) * ∑ y : H, F y := by
  have shift (y : H) : ∑ x : G, F (y * f x) = ∑ x : G, F (f x) := by
    obtain ⟨v, rfl⟩ := hf y
    have ht := Equiv.sum_comp (Equiv.mulLeft v) (fun x : G ↦ F (f x))
    change ∑ x : G, F (f (v * x)) = _ at ht
    simpa only [map_mul] using ht
  have shiftR (x : H) : ∑ y : H, F (y * x) = ∑ y : H, F y :=
    Equiv.sum_comp (Equiv.mulRight x) F
  calc
    _ = ∑ y : H, ∑ x : G, F (y * f x) := by simp only [shift, sum_const,
      card_univ, nsmul_eq_mul]
    _ = ∑ x : G, ∑ y : H, F (y * f x) := sum_comm
    _ = _ := by
      simp_rw [shiftR]
      simp

theorem stdAddChar_mul_modulus_cast (q r : ℕ) [NeZero q] [NeZero r]
    (z : ZMod (q * r)) :
    ZMod.stdAddChar ((r : ZMod (q * r)) * z) =
      ZMod.stdAddChar (ZMod.castHom (Nat.dvd_mul_right q r) (ZMod q) z) := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective z
  simpa only [map_intCast] using stdAddChar_mul_modulus q r z

/-- Exact descent before division; valid also when `q=1` or either frequency vanishes. -/
theorem completeKloosterman_common_factor_mul (q r : ℕ) [NeZero q] [NeZero r]
    (a d : ℤ) :
    (q.totient : ℂ) *
        completeKloosterman (q * r) ((r * a : ℤ) : ZMod (q * r)) (r * d) =
      ((q * r).totient : ℂ) * completeKloosterman q (a : ZMod q) d := by
  let h : q ∣ q * r := Nat.dvd_mul_right q r
  let f := ZMod.unitsMap h
  let F : (ZMod q)ˣ → ℂ := fun u ↦
    ZMod.stdAddChar ((a : ZMod q) * (↑u : ZMod q) + (d : ZMod q) * (↑u⁻¹ : ZMod q))
  have phase (u : (ZMod (q * r))ˣ) :
      ZMod.stdAddChar (((r * a : ℤ) : ZMod (q * r)) * (↑u : ZMod (q * r)) +
        ((r * d : ℤ) : ZMod (q * r)) * (↑u⁻¹ : ZMod (q * r))) = F (f u) := by
    rw [show ((r * a : ℤ) : ZMod (q * r)) * (↑u : ZMod (q * r)) +
        ((r * d : ℤ) : ZMod (q * r)) * (↑u⁻¹ : ZMod (q * r)) =
        (r : ZMod (q * r)) * ((a : ZMod (q * r)) * (↑u : ZMod (q * r)) +
          (d : ZMod (q * r)) * (↑u⁻¹ : ZMod (q * r))) by push_cast; ring]
    rw [stdAddChar_mul_modulus_cast]
    simp only [map_add, map_mul, map_intCast]
    rfl
  simp_rw [completeKloosterman_eq_sum_units, phase]
  simpa only [ZMod.card_units_eq_totient] using
    sum_comp_surjective_mul_card f (ZMod.unitsMap_surjective h) F

theorem completeKloosterman_common_factor (q r : ℕ) [NeZero q] [NeZero r]
    (a d : ℤ) :
    completeKloosterman (q * r) ((r * a : ℤ) : ZMod (q * r)) (r * d) =
      (((q * r).totient : ℂ) / (q.totient : ℂ)) *
        completeKloosterman q (a : ZMod q) d := by
  have hq : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  apply (mul_left_cancel₀ hq)
  rw [completeKloosterman_common_factor_mul]
  field_simp


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKloostermanPrimePower -/

/-!
# Elementary prime-power cancellation

Translation by the last nonzero prime-power layer preserves units. If just
one frequency is divisible by the prime, it multiplies the complete sum by
a nontrivial constant character, forcing the sum to vanish. The argument
works in characteristic two as well; it uses no quadratic Gauss-sum formula.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem completeKloosterman_symm (q : ℕ) [NeZero q] (a d : ℤ) :
    completeKloosterman q (a : ZMod q) d =
      completeKloosterman q (d : ZMod q) a := by
  simp_rw [completeKloosterman_eq_sum_units]
  apply Fintype.sum_equiv (Equiv.inv (ZMod q)ˣ)
  intro u
  change ZMod.stdAddChar ((a : ZMod q) * (↑u : ZMod q) +
      (d : ZMod q) * (↑u⁻¹ : ZMod q)) =
    ZMod.stdAddChar ((d : ZMod q) * (↑u⁻¹ : ZMod q) +
      (a : ZMod q) * (↑(u⁻¹)⁻¹ : ZMod q))
  rw [inv_inv, add_comm]

private theorem shifted_inverse_product {q : ℕ} (u t : ZMod q) (hu : IsUnit u)
    (ht : t ^ 2 = 0) :
    (u + t) * (u⁻¹ - t * (u⁻¹) ^ 2) = 1 := by
  have hi := ZMod.mul_inv_of_unit u hu
  linear_combination (1 - t * u⁻¹) * hi - (u⁻¹) ^ 2 * ht

theorem zmod_isUnit_add_square_zero {q : ℕ} (u t : ZMod q) (ht : t ^ 2 = 0) :
    IsUnit (u + t) ↔ IsUnit u := by
  have step (v s : ZMod q) (hv : IsUnit v) (hs : s ^ 2 = 0) : IsUnit (v + s) :=
    isUnit_iff_exists_inv.mpr ⟨_, shifted_inverse_product v s hv hs⟩
  constructor
  · intro hu
    simpa only [add_neg_cancel_right] using step (u + t) (-t) hu (by simpa using ht)
  · intro hu
    exact step u t hu ht

theorem zmod_inv_add_square_zero {q : ℕ} (u t : ZMod q)
    (hu : IsUnit u) (ht : t ^ 2 = 0) :
    (u + t)⁻¹ = u⁻¹ - t * (u⁻¹) ^ 2 := by
  have hs := shifted_inverse_product u t hu ht
  have hi := ZMod.inv_mul_of_unit (u + t) ((zmod_isUnit_add_square_zero u t ht).mpr hu)
  calc
    _ = (u + t)⁻¹ * ((u + t) * (u⁻¹ - t * (u⁻¹) ^ 2)) := by rw [hs, mul_one]
    _ = _ := by rw [← mul_assoc, hi, one_mul]

theorem completeKloosterman_vanish_of_square_zero_shift (q : ℕ) [NeZero q]
    (a t : ZMod q) (d : ℤ) (ht : t ^ 2 = 0) (hdt : (d : ZMod q) * t = 0)
    (hat : ZMod.stdAddChar (a * t) ≠ 1) :
    completeKloosterman q a d = 0 := by
  classical
  let F : ZMod q → ℂ := fun u ↦
    if IsUnit u then ZMod.stdAddChar (a * u + (d : ZMod q) * u⁻¹) else 0
  have shift (u : ZMod q) : F (u + t) = ZMod.stdAddChar (a * t) * F u := by
    dsimp only [F]
    simp only [zmod_isUnit_add_square_zero u t ht]
    by_cases hu : IsUnit u
    · simp only [hu, if_true]
      rw [zmod_inv_add_square_zero u t hu ht]
      have he : a * (u + t) + (d : ZMod q) * (u⁻¹ - t * (u⁻¹) ^ 2) =
          a * t + (a * u + (d : ZMod q) * u⁻¹) := by
        linear_combination -(u⁻¹) ^ 2 * hdt
      rw [he, AddChar.map_add_eq_mul]
    · simp [hu]
  have hs : ∑ u : ZMod q, F (u + t) = ∑ u : ZMod q, F u :=
    Equiv.sum_comp (Equiv.addRight t) F
  simp_rw [shift, ← mul_sum] at hs
  have hz : (ZMod.stdAddChar (a * t) - 1) * (∑ u : ZMod q, F u) = 0 := by
    linear_combination hs
  rw [completeKloosterman_eq]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hat)

/-- For exponent at least two, unequal frequency valuations give zero after
common-factor descent. No odd-prime hypothesis is used. -/
theorem completeKloosterman_prime_power_vanish (p k : ℕ) [Fact p.Prime]
    (a d : ℤ) (ha : ¬ (p : ℤ) ∣ a) (hd : (p : ℤ) ∣ d) :
    completeKloosterman (p * p ^ (k + 1)) (a : ZMod (p * p ^ (k + 1))) d = 0 := by
  let t : ZMod (p * p ^ (k + 1)) := (p ^ (k + 1) : ℕ)
  have ht : t ^ 2 = 0 := by
    change ((p ^ (k + 1) : ℕ) : ZMod (p * p ^ (k + 1))) ^ 2 = 0
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    refine ⟨p ^ k, ?_⟩
    rw [pow_succ]
    ring
  have hdt : (d : ZMod (p * p ^ (k + 1))) * t = 0 := by
    obtain ⟨b, rfl⟩ := hd
    change ((p * b : ℤ) : ZMod (p * p ^ (k + 1))) * (p ^ (k + 1) : ℕ) = 0
    push_cast
    have hq : (p : ZMod (p * p ^ (k + 1))) * (p : ZMod (p * p ^ (k + 1))) ^ (k + 1) = 0 := by
      rw [← Nat.cast_pow, ← Nat.cast_mul, ZMod.natCast_self]
    linear_combination (b : ZMod (p * p ^ (k + 1))) * hq
  apply completeKloosterman_vanish_of_square_zero_shift _ _ t d ht hdt
  change ZMod.stdAddChar ((a : ZMod (p * p ^ (k + 1))) *
    ((p ^ (k + 1) : ℕ) : ZMod (p * p ^ (k + 1)))) ≠ 1
  rw [mul_comm (a : ZMod (p * p ^ (k + 1))), stdAddChar_mul_modulus]
  intro hh
  have hz : (a : ZMod p) = 0 :=
    ZMod.injective_stdAddChar (hh.trans (AddChar.map_zero_eq_one ZMod.stdAddChar).symm)
  exact ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp hz)

theorem completeKloosterman_prime_power_vanish_left (p k : ℕ) [Fact p.Prime]
    (a d : ℤ) (ha : (p : ℤ) ∣ a) (hd : ¬ (p : ℤ) ∣ d) :
    completeKloosterman (p * p ^ (k + 1)) (a : ZMod (p * p ^ (k + 1))) d = 0 := by
  rw [completeKloosterman_symm]
  exact completeKloosterman_prime_power_vanish p k d a hd ha

/-- At exponent one, a single zero frequency gives `-1`, not zero. -/
theorem completeKloosterman_prime_zero_frequency (p : ℕ) [Fact p.Prime]
    (a : ZMod p) (ha : a ≠ 0) :
    completeKloosterman p a 0 = -1 := by
  classical
  have hs : ∑ u : ZMod p, ZMod.stdAddChar (a * u) = 0 :=
    AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p ha)
  rw [completeKloosterman_eq]
  simp only [Int.cast_zero, zero_mul, add_zero]
  calc
    _ = ∑ u : ZMod p, (ZMod.stdAddChar (a * u) - if u = 0 then 1 else 0) := by
      apply sum_congr rfl
      intro u _
      by_cases hu : u = 0 <;> simp [hu, isUnit_iff_ne_zero]
    _ = -1 := by rw [sum_sub_distrib, hs]; simp

theorem completeKloosterman_prime_zero_left (p : ℕ) [Fact p.Prime]
    (d : ℤ) (hd : ¬ (p : ℤ) ∣ d) :
    completeKloosterman p 0 d = -1 := by
  have he := completeKloosterman_symm p 0 d
  simp only [Int.cast_zero] at he
  rw [he]
  exact completeKloosterman_prime_zero_frequency p _ (fun hz ↦
    hd ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp hz))

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKloostermanStationary -/

/-!
# Exact stationary-phase localization at square moduli

This is a finite cancellation identity, not a bound assumed on a remainder.
Translation by a square-zero layer removes every nonstationary residue.
The square-modulus specialization works for all positive moduli, including
powers of two, and leaves only the actual quadratic congruence.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem sum_localize_eigenvalue {ι : Type*} [Fintype ι]
    (e : ι ≃ ι) (F c : ι → ℂ) (hc : ∀ x, c (e x) = c x)
    (hF : ∀ x, F (e x) = c x * F x) :
    ∑ x, F x = ∑ x, if c x = 1 then F x else 0 := by
  classical
  let G : ι → ℂ := fun x ↦ if c x = 1 then 0 else F x / (c x - 1)
  have hg (x : ι) : G (e x) - G x = if c x = 1 then 0 else F x := by
    simp only [G, hc, hF]
    by_cases hx : c x = 1
    · simp [hx]
    · simp only [hx, if_false]
      field_simp
  have hz : (∑ x, if c x = 1 then 0 else F x) = 0 := by
    simp_rw [← hg]
    rw [sum_sub_distrib, Equiv.sum_comp, sub_self]
  calc
    _ = (∑ x, if c x = 1 then F x else 0) +
        (∑ x, if c x = 1 then 0 else F x) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro x _
      split_ifs <;> simp
    _ = _ := by rw [hz, add_zero]

theorem completeKloosterman_square_zero_localization (q : ℕ) [NeZero q]
    (a t : ZMod q) (d : ℤ) (ht : t ^ 2 = 0) :
    completeKloosterman q a d =
      ∑ u : ZMod q, if IsUnit u ∧ t * (a * u ^ 2 - (d : ZMod q)) = 0 then
        ZMod.stdAddChar (a * u + (d : ZMod q) * u⁻¹) else 0 := by
  classical
  let F : ZMod q → ℂ := fun u ↦
    if IsUnit u then ZMod.stdAddChar (a * u + (d : ZMod q) * u⁻¹) else 0
  let c : ZMod q → ℂ := fun u ↦
    if IsUnit u then ZMod.stdAddChar (t * (a - (d : ZMod q) * (u⁻¹) ^ 2)) else 1
  have hc (u : ZMod q) : c (u + t) = c u := by
    simp only [c, zmod_isUnit_add_square_zero u t ht]
    by_cases hu : IsUnit u
    · simp only [hu, if_true]
      rw [zmod_inv_add_square_zero u t hu ht]
      congr 1
      linear_combination (d : ZMod q) * (2 * (u⁻¹) ^ 3 - t * (u⁻¹) ^ 4) * ht
    · simp [hu]
  have hF (u : ZMod q) : F (u + t) = c u * F u := by
    simp only [F, c, zmod_isUnit_add_square_zero u t ht]
    by_cases hu : IsUnit u
    · simp only [hu, if_true]
      rw [zmod_inv_add_square_zero u t hu ht, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    · simp [hu]
  have hchar (u : ZMod q) (hu : IsUnit u) :
      c u = 1 ↔ t * (a * u ^ 2 - (d : ZMod q)) = 0 := by
    simp only [c, hu, if_true]
    have hi := ZMod.mul_inv_of_unit u hu
    have hzero : ZMod.stdAddChar (t * (a - (d : ZMod q) * (u⁻¹) ^ 2)) = 1 ↔
        t * (a - (d : ZMod q) * (u⁻¹) ^ 2) = 0 := by
      rw [← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := q)),
        ZMod.injective_stdAddChar.eq_iff]
    rw [hzero]
    constructor
    · intro hh
      calc
        _ = (t * (a - (d : ZMod q) * (u⁻¹) ^ 2)) * u ^ 2 := by
          calc
            _ = t * (a * u ^ 2 - (d : ZMod q) * (u * u⁻¹) ^ 2) := by rw [hi]; ring
            _ = _ := by ring
        _ = 0 := by rw [hh, zero_mul]
    · intro hh
      calc
        _ = (t * (a * u ^ 2 - (d : ZMod q))) * (u⁻¹) ^ 2 := by
          calc
            _ = t * (a * (u * u⁻¹) ^ 2 - (d : ZMod q) * (u⁻¹) ^ 2) := by rw [hi]; ring
            _ = _ := by ring
        _ = 0 := by rw [hh, zero_mul]
  rw [completeKloosterman_eq]
  change (∑ u, F u) = _
  rw [sum_localize_eigenvalue (Equiv.addRight t) F c hc hF]
  apply sum_congr rfl
  intro u _
  by_cases hu : IsUnit u
  · simp only [hchar u hu, F, hu, if_true, true_and]
  · simp [F, hu]

theorem zmod_mul_modulus_eq_zero_iff (q r : ℕ) [NeZero q] [NeZero r]
    (z : ZMod (q * r)) :
    (r : ZMod (q * r)) * z = 0 ↔
      ZMod.castHom (Nat.dvd_mul_right q r) (ZMod q) z = 0 := by
  have hq (x : ZMod q) : ZMod.stdAddChar x = 1 ↔ x = 0 := by
    rw [← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := q)),
      ZMod.injective_stdAddChar.eq_iff]
  have hqr (x : ZMod (q * r)) : ZMod.stdAddChar x = 1 ↔ x = 0 := by
    rw [← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := q * r)),
      ZMod.injective_stdAddChar.eq_iff]
  rw [← hqr, stdAddChar_mul_modulus_cast, hq]

/-- The remaining stationary condition is the actual quadratic congruence
`a u^2 = d (mod m)`. No primality, oddness, or unit-frequency assumption. -/
theorem completeKloosterman_square_modulus_localization (m : ℕ) [NeZero m]
    (a d : ℤ) :
    completeKloosterman (m * m) (a : ZMod (m * m)) d =
      ∑ u : ZMod (m * m),
        if IsUnit u ∧ (a : ZMod m) *
            (ZMod.castHom (Nat.dvd_mul_right m m) (ZMod m) u) ^ 2 = (d : ZMod m)
        then ZMod.stdAddChar ((a : ZMod (m * m)) * u + (d : ZMod (m * m)) * u⁻¹)
        else 0 := by
  have ht : (m : ZMod (m * m)) ^ 2 = 0 := by
    rw [pow_two, ← Nat.cast_mul, ZMod.natCast_self]
  rw [completeKloosterman_square_zero_localization _ _ (m : ZMod (m * m)) _ ht]
  simp only [zmod_mul_modulus_eq_zero_iff, map_sub, map_mul, map_pow, map_intCast,
    sub_eq_zero]

theorem completeKloosterman_square_modulus_norm_le (m : ℕ) [NeZero m] (a d : ℤ) :
    ‖completeKloosterman (m * m) (a : ZMod (m * m)) d‖ ≤
      ((univ.filter fun u : ZMod (m * m) ↦ IsUnit u ∧
        (a : ZMod m) * (ZMod.castHom (Nat.dvd_mul_right m m) (ZMod m) u) ^ 2 =
          (d : ZMod m)).card : ℝ) := by
  classical
  rw [completeKloosterman_square_modulus_localization]
  convert norm_sum_le univ (fun u : ZMod (m * m) ↦
    if IsUnit u ∧ (a : ZMod m) *
        (ZMod.castHom (Nat.dvd_mul_right m m) (ZMod m) u) ^ 2 = (d : ZMod m)
    then ZMod.stdAddChar ((a : ZMod (m * m)) * u + (d : ZMod (m * m)) * u⁻¹)
    else 0) using 1
  simp only [apply_ite norm, stdAddChar_norm, norm_zero, sum_boole]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKloostermanPrimeSquare -/

/-!
# Unconditional square-root cancellation at prime-square moduli

The stationary-phase identity is evaluated using equal-sized reduction
fibers and the two-root bound in a field. This proves the primitive
prime-square case, including `p=2`; the prime-modulus Weil theorem is not used.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem zmod_reduction_fiber_card (q r : ℕ) [NeZero q] [NeZero r] (v : ZMod q) :
    (univ.filter fun u : ZMod (q * r) ↦
      ZMod.castHom (Nat.dvd_mul_right q r) (ZMod q) u = v).card = r := by
  classical
  let f := ZMod.castHom (Nat.dvd_mul_right q r) (ZMod q)
  have hf := ZMod.castHom_surjective (Nat.dvd_mul_right q r)
  have hc (w : ZMod q) :
      (univ.filter fun u : ZMod (q * r) ↦ f u = w).card =
        (univ.filter fun u : ZMod (q * r) ↦ f u = v).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range f.toAddMonoidHom (hf w) (hf v)
  have hsum := sum_card_fiberwise_eq_card_filter
    (univ : Finset (ZMod (q * r))) (univ : Finset (ZMod q)) f
  simp only [hc, sum_const, card_univ, ZMod.card, nsmul_eq_mul, mem_univ,
    filter_true] at hsum
  exact Nat.eq_of_mul_eq_mul_left (NeZero.pos q) hsum

theorem zmod_reduction_preimage_card (q r : ℕ) [NeZero q] [NeZero r]
    (s : Finset (ZMod q)) :
    (univ.filter fun u : ZMod (q * r) ↦
      ZMod.castHom (Nat.dvd_mul_right q r) (ZMod q) u ∈ s).card = s.card * r := by
  classical
  rw [← sum_card_fiberwise_eq_card_filter, sum_congr rfl (fun v _ ↦
    zmod_reduction_fiber_card q r v), sum_const, nsmul_eq_mul]
  rfl

theorem completeKloosterman_square_modulus_norm_le_roots (m : ℕ) [NeZero m]
    (a d : ℤ) :
    ‖completeKloosterman (m * m) (a : ZMod (m * m)) d‖ ≤
      (m : ℝ) * ((univ.filter fun v : ZMod m ↦ (a : ZMod m) * v ^ 2 =
        (d : ZMod m)).card : ℝ) := by
  classical
  refine (completeKloosterman_square_modulus_norm_le m a d).trans ?_
  let s := univ.filter fun v : ZMod m ↦ (a : ZMod m) * v ^ 2 = (d : ZMod m)
  have hle : (univ.filter fun u : ZMod (m * m) ↦ IsUnit u ∧
      (a : ZMod m) * (ZMod.castHom (Nat.dvd_mul_right m m) (ZMod m) u) ^ 2 =
        (d : ZMod m)).card ≤
      (univ.filter fun u : ZMod (m * m) ↦
        ZMod.castHom (Nat.dvd_mul_right m m) (ZMod m) u ∈ s).card := by
    apply card_le_card
    intro u hu
    simp only [mem_filter, mem_univ, true_and, s] at hu ⊢
    exact hu.2
  rw [zmod_reduction_preimage_card] at hle
  exact_mod_cast (hle.trans_eq (Nat.mul_comm s.card m))


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryOddPrimePowerRoots -/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem oddPrimePower_isUnit_of_reduction_ne_zero (p k : ℕ) [Fact p.Prime]
    (hk : 1 ≤ k) (x : ZMod (p ^ k))
    (hx : ZMod.castHom (dvd_pow_self p (by omega : k ≠ 0)) (ZMod p) x ≠ 0) :
    IsUnit x := by
  rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime]
  apply Nat.Coprime.pow_right
  apply Nat.Coprime.symm
  apply (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr
  intro hd
  apply hx
  rw [← ZMod.natCast_zmod_val x, map_natCast, ZMod.natCast_eq_zero_iff]
  exact hd

theorem oddPrimePower_intCast_isUnit (p k : ℕ) [Fact p.Prime] (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) : IsUnit (a : ZMod (p ^ k)) := by
  rcases k with _ | k
  · change IsUnit (a : ZMod 1)
    rw [Subsingleton.elim (a : ZMod 1) 1]
    exact isUnit_one
  apply oddPrimePower_isUnit_of_reduction_ne_zero p (k + 1) (by omega)
  intro hz
  exact ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp (by
    simpa only [map_intCast] using hz))

theorem oddPrimePower_sq_eq_sq (p k : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hk : 1 ≤ k) (u v : ZMod (p ^ k)) (hu : IsUnit u)
    (he : u ^ 2 = v ^ 2) : u = v ∨ u = -v := by
  let f := ZMod.castHom (dvd_pow_self p (by omega : k ≠ 0)) (ZMod p)
  have hu0 : f u ≠ 0 := (hu.map f).ne_zero
  have hp0 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).elim (Fact.out : p.Prime).ne_one hp2
  have hprod : (u - v) * (u + v) = 0 := by linear_combination he
  by_cases hs : f (u + v) = 0
  · have ht : f (u - v) ≠ 0 := by
      intro ht
      have hh : (2 : ZMod p) * f u = 0 := by
        simp only [map_add] at hs
        simp only [map_sub] at ht
        linear_combination hs + ht
      exact (mul_ne_zero hp0 hu0) hh
    have hv := oddPrimePower_isUnit_of_reduction_ne_zero p k hk (u - v) ht
    right
    exact eq_neg_of_add_eq_zero_left ((hv.mul_right_eq_zero).mp hprod)
  · have hv := oddPrimePower_isUnit_of_reduction_ne_zero p k hk (u + v) hs
    left
    exact sub_eq_zero.mp ((hv.mul_left_eq_zero).mp hprod)

theorem oddPrimePower_quadratic_root_card_le_two (p k : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hk : 1 ≤ k) (a d : ZMod (p ^ k))
    (ha : IsUnit a) (hd : IsUnit d) :
    (univ.filter fun u : ZMod (p ^ k) ↦ a * u ^ 2 = d).card ≤ 2 := by
  classical
  let s := univ.filter fun u : ZMod (p ^ k) ↦ a * u ^ 2 = d
  by_cases hs : s.Nonempty
  · obtain ⟨v, hv⟩ := hs
    have hv' : a * v ^ 2 = d := (mem_filter.mp hv).2
    have hsub : s ⊆ {v, -v} := by
      intro u hu
      have hu' := (mem_filter.mp hu).2
      have huunit : IsUnit u := by
        have : IsUnit (a * u ^ 2) := hu'.symm ▸ hd
        exact (isUnit_pow_iff (by omega : 2 ≠ 0)).mp (isUnit_of_mul_isUnit_right this)
      have he : u ^ 2 = v ^ 2 := ha.mul_left_cancel (hu'.trans hv'.symm)
      simpa only [mem_insert, mem_singleton] using
        oddPrimePower_sq_eq_sq p k hp2 hk u v huunit he
    exact (card_le_card hsub).trans (card_insert_le _ _ |>.trans (by simp))
  · change s.card ≤ 2
    rw [not_nonempty_iff_eq_empty.mp hs]
    simp

theorem completeKloosterman_odd_even_power_norm_le (p r : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hr : 1 ≤ r) (a d : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (hd : ¬ (p : ℤ) ∣ d) :
    ‖completeKloosterman (p ^ r * p ^ r) (a : ZMod (p ^ r * p ^ r)) d‖ ≤
      2 * (p : ℝ) ^ r := by
  have hroot := oddPrimePower_quadratic_root_card_le_two p r hp2 hr
    (a : ZMod (p ^ r)) (d : ZMod (p ^ r))
    (oddPrimePower_intCast_isUnit p r a ha) (oddPrimePower_intCast_isUnit p r d hd)
  have hR : ((univ.filter fun u : ZMod (p ^ r) ↦ (a : ZMod (p ^ r)) * u ^ 2 =
      (d : ZMod (p ^ r))).card : ℝ) ≤ 2 := by exact_mod_cast hroot
  refine (completeKloosterman_square_modulus_norm_le_roots (p ^ r) a d).trans ?_
  simpa only [Nat.cast_pow, mul_comm] using
    mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg (p ^ r) : (0 : ℝ) ≤ (p ^ r : ℕ))

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryOddPrimePowerGauss -/

/-!
Elementary quadratic Gauss cancellation by translation and additive orthogonality.
The linear coefficient is unrestricted; no multiplicative character is used.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem oddPrimePower_quadratic_gauss_norm (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (A B : ZMod p) (hA : A ≠ 0) :
    ‖∑ x : ZMod p, ZMod.stdAddChar (A * x ^ 2 + B * x)‖ = Real.sqrt (p : ℝ) := by
  classical
  let ψ : AddChar (ZMod p) ℂ := ZMod.stdAddChar
  let S := ∑ x : ZMod p, ψ (A * x ^ 2 + B * x)
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).elim (Fact.out : p.Prime).ne_one hp2
  have hs : S * starRingEnd ℂ S = (p : ℂ) := by
    calc
      _ = ∑ x : ZMod p, ∑ y : ZMod p,
          ψ (A * x ^ 2 + B * x - (A * y ^ 2 + B * y)) := by
        simp only [S, map_sum, sum_mul, mul_sum, sub_eq_add_neg,
          AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]
        exact sum_comm
      _ = ∑ y : ZMod p, ∑ x : ZMod p,
          ψ (A * (x + y) ^ 2 + B * (x + y) - (A * y ^ 2 + B * y)) := by
        rw [sum_comm]
        apply sum_congr rfl
        intro y _
        exact (Equiv.sum_comp (Equiv.addRight y)
          (fun x ↦ ψ (A * x ^ 2 + B * x - (A * y ^ 2 + B * y)))).symm
      _ = ∑ x : ZMod p, ψ (A * x ^ 2 + B * x) *
          ∑ y : ZMod p, ψ ((2 * A * x) * y) := by
        rw [sum_comm]
        apply sum_congr rfl
        intro x _
        rw [mul_sum]
        apply sum_congr rfl
        intro y _
        rw [← AddChar.map_add_eq_mul]
        congr 1
        ring
      _ = (p : ℂ) := by
        rw [sum_eq_single 0]
        · simp only [mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), add_zero,
            AddChar.map_zero_eq_one, sum_const, card_univ, ZMod.card, nsmul_eq_mul,
            mul_one, one_mul]
        · intro x _ hx
          have hzero : ∑ y : ZMod p, ψ ((2 * A * x) * y) = 0 :=
            AddChar.sum_eq_zero_of_ne_one
              (ZMod.isPrimitive_stdAddChar p (mul_ne_zero (mul_ne_zero htwo hA) hx))
          rw [hzero, mul_zero]
        · simp
  have hsq : ‖S‖ ^ 2 = (p : ℝ) := by
    have he := (Complex.mul_conj S).symm.trans hs
    rw [Complex.normSq_eq_norm_sq] at he
    exact_mod_cast he
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (Nat.cast_nonneg p)]
  exact hsq

theorem oddPrimePower_sum_reduction (q r : ℕ) [NeZero q] [NeZero r]
    (F : ZMod q → ℂ) :
    (∑ x : ZMod (q * r), F (ZMod.castHom (Nat.dvd_mul_right q r) (ZMod q) x)) =
      (r : ℂ) * ∑ y : ZMod q, F y := by
  classical
  let f := ZMod.castHom (Nat.dvd_mul_right q r) (ZMod q)
  calc
    _ = ∑ y : ZMod q, ∑ x ∈ univ.filter (fun x ↦ f x = y), F (f x) :=
      (sum_fiberwise univ f (fun x ↦ F (f x))).symm
    _ = ∑ y : ZMod q, (r : ℂ) * F y := by
      apply sum_congr rfl
      intro y _
      rw [sum_congr rfl (fun x hx ↦ congrArg F (mem_filter.mp hx).2)]
      simp only [sum_const, nsmul_eq_mul, f, zmod_reduction_fiber_card]
    _ = _ := (mul_sum _ _ _).symm

private theorem oddPrimePower_shifted_inverse_product {q : ℕ} (u t : ZMod q)
    (hu : IsUnit u) (ht : t ^ 3 = 0) :
    (u + t) * (u⁻¹ - t * (u⁻¹) ^ 2 + t ^ 2 * (u⁻¹) ^ 3) = 1 := by
  have hi := ZMod.mul_inv_of_unit u hu
  linear_combination (1 - t * u⁻¹ + t ^ 2 * (u⁻¹) ^ 2) * hi + (u⁻¹) ^ 3 * ht

theorem oddPrimePower_isUnit_add_cube_zero {q : ℕ} (u t : ZMod q)
    (ht : t ^ 3 = 0) : IsUnit (u + t) ↔ IsUnit u := by
  have step (v s : ZMod q) (hv : IsUnit v) (hs : s ^ 3 = 0) : IsUnit (v + s) :=
    isUnit_iff_exists_inv.mpr ⟨_, oddPrimePower_shifted_inverse_product v s hv hs⟩
  constructor
  · intro hu
    simpa only [add_neg_cancel_right] using step (u + t) (-t) hu (by
      rw [neg_pow, ht, mul_zero])
  · exact fun hu ↦ step u t hu ht

theorem oddPrimePower_inv_add_cube_zero {q : ℕ} (u t : ZMod q)
    (hu : IsUnit u) (ht : t ^ 3 = 0) :
    (u + t)⁻¹ = u⁻¹ - t * (u⁻¹) ^ 2 + t ^ 2 * (u⁻¹) ^ 3 := by
  have hs := oddPrimePower_shifted_inverse_product u t hu ht
  have hi := ZMod.inv_mul_of_unit (u + t)
    ((oddPrimePower_isUnit_add_cube_zero u t ht).mpr hu)
  calc
    _ = (u + t)⁻¹ * ((u + t) * (u⁻¹ - t * (u⁻¹) ^ 2 + t ^ 2 * (u⁻¹) ^ 3)) := by
      rw [hs, mul_one]
    _ = _ := by rw [← mul_assoc, hi, one_mul]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryOddPrimePowerStationary -/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem oddPrimePower_annihilator (q m n : ℕ) [NeZero q] [NeZero m]
    [NeZero n] (hq : q = m * n) (h : m ∣ q) (z : ZMod q) :
    (n : ZMod q) * z = 0 ↔ ZMod.castHom h (ZMod m) z = 0 := by
  subst q
  exact zmod_mul_modulus_eq_zero_iff m n z

theorem oddPrimePower_localization (p m : ℕ) [NeZero p] [NeZero m] (a d : ℤ) :
    completeKloosterman (p * (m * m)) (a : ZMod (p * (m * m))) d =
      ∑ u : ZMod (p * (m * m)),
        if IsUnit u ∧ (a : ZMod m) *
          (ZMod.castHom (show m ∣ p * (m * m) from ⟨p * m, by ring⟩) (ZMod m) u) ^ 2 =
            (d : ZMod m)
        then ZMod.stdAddChar ((a : ZMod (p * (m * m))) * u +
          (d : ZMod (p * (m * m))) * u⁻¹) else 0 := by
  have ht : ((p * m : ℕ) : ZMod (p * (m * m))) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact ⟨p, by ring⟩
  rw [completeKloosterman_square_zero_localization _ _ (p * m : ℕ) _ ht]
  simp only [oddPrimePower_annihilator _ m (p * m) (by ring)
    (show m ∣ p * (m * m) from ⟨p * m, by ring⟩),
    map_sub, map_mul, map_pow, map_intCast, sub_eq_zero]

theorem oddPrimePower_layer_cube_zero (p m : ℕ) [NeZero p] [NeZero m]
    (hpm : p ∣ m) : (m : ZMod (p * (m * m))) ^ 3 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  obtain ⟨n, hn⟩ := hpm
  exact ⟨n, by rw [hn]; ring⟩

theorem oddPrimePower_stationary_shift (p m : ℕ) [NeZero p] [NeZero m]
    (hpm : p ∣ m) (a d : ℤ) (u t : ZMod (p * (m * m))) :
    (IsUnit (u + (m : ZMod (p * (m * m))) * t) ∧
      (a : ZMod m) *
        (ZMod.castHom (show m ∣ p * (m * m) from ⟨p * m, by ring⟩) (ZMod m)
          (u + (m : ZMod (p * (m * m))) * t)) ^ 2 = (d : ZMod m)) ↔
    (IsUnit u ∧ (a : ZMod m) *
      (ZMod.castHom (show m ∣ p * (m * m) from ⟨p * m, by ring⟩) (ZMod m) u) ^ 2 =
        (d : ZMod m)) := by
  have ht : ((m : ZMod (p * (m * m))) * t) ^ 3 = 0 := by
    rw [mul_pow, oddPrimePower_layer_cube_zero p m hpm, zero_mul]
  rw [oddPrimePower_isUnit_add_cube_zero _ _ ht]
  simp only [map_add, map_mul, map_natCast, ZMod.natCast_self, zero_mul, add_zero]

theorem oddPrimePower_stationary_linear_coefficient (p m : ℕ) [NeZero p] [NeZero m]
    (a d : ℤ) (u : ZMod (p * (m * m))) (hu : IsUnit u)
    (hs : (a : ZMod m) *
      (ZMod.castHom (show m ∣ p * (m * m) from ⟨p * m, by ring⟩) (ZMod m) u) ^ 2 =
        (d : ZMod m)) :
    ∃ c : ℕ, (a : ZMod (p * (m * m))) - (d : ZMod (p * (m * m))) * (u⁻¹) ^ 2 =
      (m : ZMod (p * (m * m))) * (c : ZMod (p * (m * m))) := by
  let f := ZMod.castHom (show m ∣ p * (m * m) from ⟨p * m, by ring⟩) (ZMod m)
  let L : ZMod (p * (m * m)) := (a : ZMod (p * (m * m))) -
    (d : ZMod (p * (m * m))) * (u⁻¹) ^ 2
  have hi : f u * f u⁻¹ = 1 := by
    rw [← map_mul, ZMod.mul_inv_of_unit u hu, map_one]
  have hL : f L = 0 := by
    simp only [L, map_sub, map_mul, map_pow, map_intCast]
    change (a : ZMod m) * f u ^ 2 = (d : ZMod m) at hs
    linear_combination (f u⁻¹) ^ 2 * hs - (a : ZMod m) * (f u * f u⁻¹ + 1) * hi
  have hval : m ∣ L.val := by
    apply (ZMod.natCast_eq_zero_iff L.val m).mp
    rw [← map_natCast f, ZMod.natCast_zmod_val]
    exact hL
  obtain ⟨c, hc⟩ := hval
  refine ⟨c, ?_⟩
  change L = _
  rw [← ZMod.natCast_zmod_val L, hc, Nat.cast_mul]

theorem oddPrimePower_stationary_phase (p m : ℕ) [NeZero p] [NeZero m]
    (hpm : p ∣ m) (a d : ℤ) (u t : ZMod (p * (m * m))) (hu : IsUnit u)
    (c : ℕ) (hc : (a : ZMod (p * (m * m))) -
      (d : ZMod (p * (m * m))) * (u⁻¹) ^ 2 =
        (m : ZMod (p * (m * m))) * (c : ZMod (p * (m * m)))) :
    ZMod.stdAddChar ((a : ZMod (p * (m * m))) * (u + (m : ZMod (p * (m * m))) * t) +
      (d : ZMod (p * (m * m))) * (u + (m : ZMod (p * (m * m))) * t)⁻¹) =
    ZMod.stdAddChar ((a : ZMod (p * (m * m))) * u +
      (d : ZMod (p * (m * m))) * u⁻¹) *
    ZMod.stdAddChar
      (ZMod.castHom (Nat.dvd_mul_right p (m * m)) (ZMod p)
          ((d : ZMod (p * (m * m))) * (u⁻¹) ^ 3) *
        (ZMod.castHom (Nat.dvd_mul_right p (m * m)) (ZMod p) t) ^ 2 +
      (c : ZMod p) * ZMod.castHom (Nat.dvd_mul_right p (m * m)) (ZMod p) t) := by
  have ht : ((m : ZMod (p * (m * m))) * t) ^ 3 = 0 := by
    rw [mul_pow, oddPrimePower_layer_cube_zero p m hpm, zero_mul]
  rw [oddPrimePower_inv_add_cube_zero u _ hu ht]
  have he :
      (a : ZMod (p * (m * m))) * (u + (m : ZMod (p * (m * m))) * t) +
        (d : ZMod (p * (m * m))) *
          (u⁻¹ - ((m : ZMod (p * (m * m))) * t) * (u⁻¹) ^ 2 +
            ((m : ZMod (p * (m * m))) * t) ^ 2 * (u⁻¹) ^ 3) =
      ((a : ZMod (p * (m * m))) * u + (d : ZMod (p * (m * m))) * u⁻¹) +
        ((m * m : ℕ) : ZMod (p * (m * m))) *
          ((d : ZMod (p * (m * m))) * (u⁻¹) ^ 3 * t ^ 2 +
            (c : ZMod (p * (m * m))) * t) := by
    push_cast
    linear_combination (m : ZMod (p * (m * m))) * t * hc
  rw [he, AddChar.map_add_eq_mul, stdAddChar_mul_modulus_cast]
  simp only [map_add, map_mul, map_pow, map_natCast]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryOddPrimePowerNorm -/

/-!
Average the localized complete sum over translations by `m`. Each stationary
orbit has a genuine quadratic Gauss norm. This retains the square-root saving
at moduli `p * m²`, rather than estimating the orbit term by term.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem oddPrimePower_stationary_orbit_norm (p m : ℕ) [Fact p.Prime] [NeZero m]
    (hp2 : p ≠ 2) (hpm : p ∣ m) (a d : ℤ) (hd : ¬ (p : ℤ) ∣ d)
    (u : ZMod (p * (m * m))) (hu : IsUnit u)
    (hs : (a : ZMod m) *
      (ZMod.castHom (show m ∣ p * (m * m) from ⟨p * m, by ring⟩) (ZMod m) u) ^ 2 =
        (d : ZMod m)) :
    ‖∑ t : ZMod (p * (m * m)),
      ZMod.stdAddChar ((a : ZMod (p * (m * m))) *
        (u + (m : ZMod (p * (m * m))) * t) +
        (d : ZMod (p * (m * m))) * (u + (m : ZMod (p * (m * m))) * t)⁻¹)‖ =
      ((m * m : ℕ) : ℝ) * Real.sqrt (p : ℝ) := by
  obtain ⟨c, hc⟩ := oddPrimePower_stationary_linear_coefficient p m a d u hu hs
  let f := ZMod.castHom (Nat.dvd_mul_right p (m * m)) (ZMod p)
  let A : ZMod p := f ((d : ZMod (p * (m * m))) * (u⁻¹) ^ 3)
  have hui : IsUnit u⁻¹ := by
    obtain ⟨v, rfl⟩ := hu
    simpa only [ZMod.inv_coe_unit] using (v⁻¹).isUnit
  have hA : A ≠ 0 := by
    simp only [A, map_mul, map_pow, map_intCast]
    exact mul_ne_zero
      (fun h ↦ hd ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp h))
      (pow_ne_zero _ ((hui.map f).ne_zero))
  simp_rw [oddPrimePower_stationary_phase p m hpm a d u _ hu c hc]
  change ‖∑ t : ZMod (p * (m * m)),
    ZMod.stdAddChar ((a : ZMod (p * (m * m))) * u +
      (d : ZMod (p * (m * m))) * u⁻¹) *
    ZMod.stdAddChar (A * f t ^ 2 + (c : ZMod p) * f t)‖ = _
  rw [← mul_sum, oddPrimePower_sum_reduction p (m * m)
    (fun t ↦ ZMod.stdAddChar (A * t ^ 2 + (c : ZMod p) * t))]
  rw [norm_mul, stdAddChar_norm, one_mul, norm_mul, Complex.norm_natCast,
    oddPrimePower_quadratic_gauss_norm p hp2 A (c : ZMod p) hA]

private theorem oddPrimePower_preimage_card (q m n : ℕ) [NeZero q] [NeZero m]
    [NeZero n] (hq : q = m * n) (h : m ∣ q) (s : Finset (ZMod m)) :
    (univ.filter fun u : ZMod q ↦ ZMod.castHom h (ZMod m) u ∈ s).card = s.card * n := by
  subst q
  exact zmod_reduction_preimage_card m n s

theorem completeKloosterman_odd_square_layer_norm_le_roots (p m : ℕ)
    [Fact p.Prime] [NeZero m] (hp2 : p ≠ 2) (hpm : p ∣ m)
    (a d : ℤ) (hd : ¬ (p : ℤ) ∣ d) :
    ‖completeKloosterman (p * (m * m)) (a : ZMod (p * (m * m))) d‖ ≤
      (m : ℝ) * Real.sqrt (p : ℝ) *
        ((univ.filter fun v : ZMod m ↦ (a : ZMod m) * v ^ 2 = (d : ZMod m)).card : ℝ) := by
  classical
  let q := p * (m * m)
  let f := ZMod.castHom (show m ∣ q from ⟨p * m, by dsimp [q]; ring⟩) (ZMod m)
  let S : ZMod q → Prop := fun u ↦ IsUnit u ∧ (a : ZMod m) * f u ^ 2 = (d : ZMod m)
  let F : ZMod q → ℂ := fun u ↦ if S u then
    ZMod.stdAddChar ((a : ZMod q) * u + (d : ZMod q) * u⁻¹) else 0
  let R := univ.filter fun v : ZMod m ↦ (a : ZMod m) * v ^ 2 = (d : ZMod m)
  have hloc : completeKloosterman q (a : ZMod q) d = ∑ u, F u :=
    oddPrimePower_localization p m a d
  have hS (u t : ZMod q) : S (u + (m : ZMod q) * t) ↔ S u :=
    oddPrimePower_stationary_shift p m hpm a d u t
  have horbit (u : ZMod q) :
      ‖∑ t : ZMod q, F (u + (m : ZMod q) * t)‖ =
        if S u then ((m * m : ℕ) : ℝ) * Real.sqrt (p : ℝ) else 0 := by
    simp only [F, hS]
    by_cases hu : S u
    · simp only [hu, if_true]
      exact oddPrimePower_stationary_orbit_norm p m hp2 hpm a d hd u hu.1 hu.2
    · simp only [hu, if_false, sum_const_zero, norm_zero]
  have havg : (q : ℂ) * completeKloosterman q (a : ZMod q) d =
      ∑ u : ZMod q, ∑ t : ZMod q, F (u + (m : ZMod q) * t) := by
    have ht (t : ZMod q) :
        ∑ u : ZMod q, F (u + (m : ZMod q) * t) =
          completeKloosterman q (a : ZMod q) d :=
      (Equiv.sum_comp (Equiv.addRight ((m : ZMod q) * t)) F).trans hloc.symm
    rw [sum_comm]
    simp only [ht, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  have hN : (q : ℝ) * ‖completeKloosterman q (a : ZMod q) d‖ ≤
      ((univ.filter S).card : ℝ) * (((m * m : ℕ) : ℝ) * Real.sqrt (p : ℝ)) := by
    have hn := norm_sum_le univ (fun u : ZMod q ↦ ∑ t : ZMod q,
      F (u + (m : ZMod q) * t))
    rw [← havg, norm_mul, Complex.norm_natCast] at hn
    simp_rw [horbit] at hn
    have he : (∑ u : ZMod q,
        if S u then ((m * m : ℕ) : ℝ) * Real.sqrt (p : ℝ) else 0) =
        ((univ.filter S).card : ℝ) * (((m * m : ℕ) : ℝ) * Real.sqrt (p : ℝ)) := by
      calc
        _ = (∑ u : ZMod q, if S u then (1 : ℝ) else 0) *
            (((m * m : ℕ) : ℝ) * Real.sqrt (p : ℝ)) := by
          rw [sum_mul]
          apply sum_congr rfl
          intro u _
          split_ifs <;> simp
        _ = _ := by rw [sum_boole]
    exact hn.trans_eq he
  have hcard : (univ.filter S).card ≤ R.card * (p * m) := by
    calc
      _ ≤ (univ.filter fun u : ZMod q ↦ f u ∈ R).card := by
        apply card_le_card
        intro u hu
        simp only [mem_filter, mem_univ, true_and, S, R] at hu ⊢
        exact hu.2
      _ = _ := oddPrimePower_preimage_card q m (p * m) (by dsimp [q]; ring) _ R
  have hbound : (q : ℝ) * ‖completeKloosterman q (a : ZMod q) d‖ ≤
      (q : ℝ) * ((m : ℝ) * Real.sqrt (p : ℝ) * (R.card : ℝ)) := by
    calc
      _ ≤ ((univ.filter S).card : ℝ) *
          (((m * m : ℕ) : ℝ) * Real.sqrt (p : ℝ)) := hN
      _ ≤ ((R.card * (p * m) : ℕ) : ℝ) *
          (((m * m : ℕ) : ℝ) * Real.sqrt (p : ℝ)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = _ := by dsimp [q]; push_cast; ring
  exact le_of_mul_le_mul_left hbound (show (0 : ℝ) < q by exact_mod_cast (NeZero.pos q))

theorem completeKloosterman_odd_odd_power_norm_le (p r : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hr : 1 ≤ r) (a d : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (hd : ¬ (p : ℤ) ∣ d) :
    ‖completeKloosterman (p * (p ^ r * p ^ r)) (a : ZMod (p * (p ^ r * p ^ r))) d‖ ≤
      2 * (p : ℝ) ^ r * Real.sqrt (p : ℝ) := by
  have hroot := oddPrimePower_quadratic_root_card_le_two p r hp2 hr
    (a : ZMod (p ^ r)) (d : ZMod (p ^ r))
    (oddPrimePower_intCast_isUnit p r a ha) (oddPrimePower_intCast_isUnit p r d hd)
  have hR : ((univ.filter fun u : ZMod (p ^ r) ↦ (a : ZMod (p ^ r)) * u ^ 2 =
      (d : ZMod (p ^ r))).card : ℝ) ≤ 2 := by exact_mod_cast hroot
  refine (completeKloosterman_odd_square_layer_norm_le_roots p (p ^ r) hp2
    (dvd_pow_self p (by omega)) a d hd).trans ?_
  calc
    _ ≤ ((p ^ r : ℕ) : ℝ) * Real.sqrt (p : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left hR (by positivity)
    _ = _ := by push_cast; ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryStepanovHasse -/

/-!
# Hasse differentiation in Stepanov's construction

The divisibility, linear operator, and degree estimates below formalize
Lemma 10 of Gergely Harcos, *Weil's bound for
Kloosterman sums*, printed page 10 (`harcos-weil.pdf`).

The operator is polynomial division of `hasseDeriv k (g * f ^ n)` by
`f ^ (n - k)`. Its factorization is proved, not assumed. No monicity or
characteristic restriction is needed.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Polynomial

/-- The power forced by Leibniz's rule divides the Hasse derivative.
The truncated exponent also makes the statement valid when `n < k`. -/
theorem stepanov_pow_dvd_hasseDeriv_mul_pow
    {R : Type*} [CommRing R] (f g : R[X]) (n k : ℕ) :
    f ^ (n - k) ∣ hasseDeriv k (g * f ^ n) := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
      by_cases hkn : n + 1 ≤ k
      · simp [Nat.sub_eq_zero_of_le hkn]
      have hkn' : k ≤ n := by omega
      rw [pow_succ, ← mul_assoc, hasseDeriv_mul]
      apply Finset.dvd_sum
      intro ij hij
      have hij' : ij.1 + ij.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      by_cases hj : ij.2 = 0
      · have hi : ij.1 = k := by omega
        simp only [hj, hi, hasseDeriv_zero, LinearMap.id_apply]
        have he : n + 1 - k = (n - k) + 1 := by omega
        rw [he, pow_succ]
        exact mul_dvd_mul_right (ih k) f
      · have he : n + 1 - k ≤ n - ij.1 := by omega
        exact dvd_mul_of_dvd_left ((pow_dvd_pow f he).trans (ih ij.1)) _

variable {F : Type*} [Field F]

private theorem stepanov_hasse_div_mul (f : F[X]) (hf : f ≠ 0)
    (n k : ℕ) (g : F[X]) :
    (hasseDeriv k (g * f ^ n) / f ^ (n - k)) * f ^ (n - k) =
      hasseDeriv k (g * f ^ n) := by
  rw [mul_comm]
  exact EuclideanDomain.mul_div_cancel' (pow_ne_zero _ hf)
    (stepanov_pow_dvd_hasseDeriv_mul_pow f g n k)

/-- Harcos's `g ↦ g⁽ᵏ⁾` as an actual linear map, for every nonzero `f`.
It is defined for all `k`; the degree estimate below uses `k ≤ n`. -/
def stepanovHasseOperator (f : F[X]) (hf : f ≠ 0) (n k : ℕ) :
    F[X] →ₗ[F] F[X] where
  toFun g := hasseDeriv k (g * f ^ n) / f ^ (n - k)
  map_add' g h := by
    apply mul_right_cancel₀ (pow_ne_zero (n - k) hf)
    rw [stepanov_hasse_div_mul f hf]
    simp only [add_mul, stepanov_hasse_div_mul f hf, map_add]
  map_smul' c g := by
    apply mul_right_cancel₀ (pow_ne_zero (n - k) hf)
    rw [stepanov_hasse_div_mul f hf]
    simp only [RingHom.id_apply, smul_mul_assoc, stepanov_hasse_div_mul f hf, map_smul]


/-- The factorization in Harcos Lemma 10, including the endpoint `k = n`. -/
theorem stepanovHasseOperator_spec (f : F[X]) (hf : f ≠ 0)
    (n k : ℕ) (g : F[X]) :
    hasseDeriv k (g * f ^ n) =
      stepanovHasseOperator f hf n k g * f ^ (n - k) :=
  (stepanov_hasse_div_mul f hf n k g).symm


/-- The natural-degree form of Harcos's estimate; valid also for `g = 0`. -/
theorem stepanovHasseOperator_natDegree_le (f : F[X]) (hf : f ≠ 0)
    (n k : ℕ) (hkn : k ≤ n) (hm : 1 ≤ f.natDegree) (g : F[X]) :
    (stepanovHasseOperator f hf n k g).natDegree ≤
      g.natDegree + k * (f.natDegree - 1) := by
  by_cases hq : stepanovHasseOperator f hf n k g = 0
  · simp only [hq, natDegree_zero, zero_le]
  have hg : g ≠ 0 := by
    intro hg
    apply hq
    rw [hg, map_zero]
  have hd := natDegree_hasseDeriv_le (g * f ^ n) k
  rw [stepanovHasseOperator_spec f hf n k g,
    natDegree_mul hq (pow_ne_zero _ hf),
    natDegree_mul hg (pow_ne_zero _ hf), natDegree_pow, natDegree_pow] at hd
  have hkm : k ≤ g.natDegree + n * f.natDegree := by nlinarith
  have hnm : (n - k) * f.natDegree + k * f.natDegree = n * f.natDegree := by
    rw [← add_mul, Nat.sub_add_cancel hkn]
  have hkm' : k * (f.natDegree - 1) + k = k * f.natDegree := by
    calc
      k * (f.natDegree - 1) + k = k * ((f.natDegree - 1) + 1) := by ring
      _ = k * f.natDegree := by rw [Nat.sub_add_cancel hm]
  have hsub := Nat.sub_add_cancel hkm
  omega

/-- The strict degree bound used to size Stepanov's coefficient system.
Unlike a `natDegree < B` hypothesis, `degree < B` handles `g = 0`, even
when `B = 0`. -/
theorem stepanovHasseOperator_degree_lt (f : F[X]) (hf : f ≠ 0)
    (n k B : ℕ) (hkn : k ≤ n) (hm : 1 ≤ f.natDegree)
    (g : F[X]) (hg : g.degree < (B : WithBot ℕ)) :
    (stepanovHasseOperator f hf n k g).degree <
      ((B + k * (f.natDegree - 1) : ℕ) : WithBot ℕ) := by
  by_cases hq : stepanovHasseOperator f hf n k g = 0
  · rw [hq, degree_zero]
    exact WithBot.bot_lt_coe _
  have hg0 : g ≠ 0 := by
    intro hg0
    apply hq
    rw [hg0, map_zero]
  rw [degree_eq_natDegree hg0] at hg
  rw [degree_eq_natDegree hq]
  exact_mod_cast lt_of_le_of_lt
    (stepanovHasseOperator_natDegree_le f hf n k hkn hm g)
    (Nat.add_lt_add_right (WithBot.coe_lt_coe.mp hg) _)

/-- Harcos Lemma 8: vanishing of the first Hasse derivatives is exactly
divisibility by the corresponding power of the linear factor. -/
theorem stepanov_hasse_vanishing_iff_pow_dvd
    {R : Type*} [CommRing R] (h : R[X]) (x : R) (ell : ℕ) :
    (∀ k < ell, (hasseDeriv k h).eval x = 0) ↔
      (X - C x) ^ ell ∣ h := by
  rw [X_sub_C_pow_dvd_iff, X_pow_dvd_iff]
  simp only [← taylor_apply, taylor_coeff]

/-- The sum of root multiplicities over any finite set is at most the degree. -/
theorem stepanov_sum_rootMultiplicity_le (h : F[X]) (s : Finset F) :
    ∑ x ∈ s, h.rootMultiplicity x ≤ h.natDegree := by
  classical
  calc
    ∑ x ∈ s, h.rootMultiplicity x = ∑ x ∈ s, h.roots.count x := by
      simp only [count_roots]
    _ ≤ ∑ x ∈ s ∪ h.roots.toFinset, h.roots.count x :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (by intros; exact Nat.zero_le _)
    _ = ∑ x ∈ h.roots.toFinset, h.roots.count x := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro x _ hx
      exact Multiset.count_eq_zero.mpr (by simpa only [Multiset.mem_toFinset] using hx)
    _ = h.roots.card := Multiset.toFinset_sum_count_eq _
    _ ≤ h.natDegree := card_roots' h

/-- Finite-root degree bound with a possibly different vanishing order at
each point. The nonzero hypothesis is essential here. -/
theorem stepanov_sum_hasse_orders_le (h : F[X]) (hh : h ≠ 0)
    (s : Finset F) (orders : F → ℕ)
    (hv : ∀ x ∈ s, ∀ k < orders x, (hasseDeriv k h).eval x = 0) :
    ∑ x ∈ s, orders x ≤ h.natDegree := by
  calc
    ∑ x ∈ s, orders x ≤ ∑ x ∈ s, h.rootMultiplicity x := by
      apply Finset.sum_le_sum
      intro x hx
      exact (le_rootMultiplicity_iff hh).mpr
        ((stepanov_hasse_vanishing_iff_pow_dvd h x (orders x)).mp (hv x hx))
    _ ≤ h.natDegree := stepanov_sum_rootMultiplicity_le h s

/-- If a nonzero polynomial vanishes to Hasse order at least `ell` at every
point of a finite set, then `ell` times the number of points is at most its degree. -/
theorem stepanov_card_mul_hasse_order_le (h : F[X]) (hh : h ≠ 0)
    (s : Finset F) (ell : ℕ)
    (hv : ∀ x ∈ s, ∀ k < ell, (hasseDeriv k h).eval x = 0) :
    s.card * ell ≤ h.natDegree := by
  simpa using
    stepanov_sum_hasse_orders_le h hh s (fun _ ↦ ell) hv

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryStepanovConstraints -/

/-!
# The actual finite-dimensional Stepanov equations

The two polynomial families have degree strictly less than the integer `B`.
The `k`th equation is Harcos (22), with its two distinct Hasse operators.
No rank or nonzero-solution hypothesis is imposed on the equation matrix.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Polynomial Finset Module

variable {F : Type*} [Field F]

def stepanovConstraint (f : F[X]) (hf : f ≠ 0) (ell e : ℕ) (a : F)
    (k : ℕ) {J : ℕ} (r s : Fin J → F[X]) : F[X] :=
  ∑ j, (stepanovHasseOperator f hf ell k (r j) +
    a • stepanovHasseOperator f hf (ell + e) k (s j)) * X ^ j.val

theorem stepanovConstraint_degree_lt (f : F[X]) (hf : f ≠ 0)
    (ell e B J k : ℕ) (a : F) (hk : k ≤ ell) (hm : 1 ≤ f.natDegree)
    (hJ : 0 < J) (r s : Fin J → F[X])
    (hr : ∀ j, (r j).degree < (B : WithBot ℕ))
    (hs : ∀ j, (s j).degree < (B : WithBot ℕ)) :
    (stepanovConstraint f hf ell e a k r s).degree <
      ((B + k * (f.natDegree - 1) + (J - 1) : ℕ) : WithBot ℕ) := by
  apply mem_degreeLT.mp
  apply Submodule.sum_mem
  intro j _
  apply mem_degreeLT.mpr
  rw [degree_mul_X_pow]
  have hr' := stepanovHasseOperator_degree_lt f hf ell k B hk hm (r j) (hr j)
  have hs' := stepanovHasseOperator_degree_lt f hf (ell + e) k B
    (by omega) hm (s j) (hs j)
  have hd := (degree_add_le _ _).trans_lt
    (max_lt hr' ((degree_smul_le a _).trans_lt hs'))
  calc
    _ < ((B + k * (f.natDegree - 1) : ℕ) : WithBot ℕ) + (j.val : WithBot ℕ) :=
      WithBot.add_lt_add_right (by simp) hd
    _ ≤ _ := by
      rw [← Nat.cast_add]
      exact_mod_cast Nat.add_le_add_left (show j.val ≤ J - 1 by omega) _

abbrev StepanovCoefficients (F : Type*) [Field F] (J B : ℕ) :=
  Fin J → degreeLT F B × degreeLT F B

def stepanovConstraintMap (f : F[X]) (hf : f ≠ 0)
    (ell e B J : ℕ) (a : F) (hm : 1 ≤ f.natDegree) (hJ : 0 < J) :
    StepanovCoefficients F J B →ₗ[F]
      (k : Fin ell) → degreeLT F (B + k.val * (f.natDegree - 1) + (J - 1)) where
  toFun v k := ⟨stepanovConstraint f hf ell e a k.val
      (fun j => (v j).1) (fun j => (v j).2),
    mem_degreeLT.mpr (stepanovConstraint_degree_lt f hf ell e B J k.val a
      (Nat.le_of_lt k.is_lt) hm hJ _ _
      (fun j => mem_degreeLT.mp (v j).1.property)
      (fun j => mem_degreeLT.mp (v j).2.property))⟩
  map_add' v w := by
    funext k
    apply Subtype.ext
    simp only [stepanovConstraint, Pi.add_apply, Prod.fst_add, Prod.snd_add,
      Submodule.coe_add, map_add, smul_add, add_mul, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  map_smul' c v := by
    funext k
    apply Subtype.ext
    simp only [stepanovConstraint, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd,
      Submodule.coe_smul, map_smul, RingHom.id_apply,
      Finset.smul_sum, smul_comm a c]
    apply sum_congr rfl
    intro j _
    rw [← smul_mul_assoc, smul_add]

theorem stepanovCoefficients_finrank (J B : ℕ) :
    finrank F (StepanovCoefficients F J B) = 2 * J * B := by
  have hB : finrank F (degreeLT F B) = B := by
    simpa using (finrank_eq_card_basis (degreeLT.basis F B))
  simp only [StepanovCoefficients, finrank_pi_fintype, finrank_prod, hB, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_cast
  ring

theorem stepanovConstraints_finrank (ell B J m : ℕ) :
    finrank F ((k : Fin ell) → degreeLT F (B + k.val * (m - 1) + (J - 1))) =
      ∑ k : Fin ell, (B + k.val * (m - 1) + (J - 1)) := by
  rw [finrank_pi_fintype]
  apply sum_congr rfl
  intro k _
  simpa using (finrank_eq_card_basis
    (degreeLT.basis F (B + k.val * (m - 1) + (J - 1))))

/-- The precise integer equation count, strictly smaller than the `2JB`
unknown coefficients, produces a nontrivial solution of Harcos (22). -/
theorem stepanov_exists_coefficients (f : F[X]) (hf : f ≠ 0)
    (ell e B J : ℕ) (a : F) (hm : 1 ≤ f.natDegree) (hJ : 0 < J)
    (hcount : (∑ k : Fin ell, (B + k.val * (f.natDegree - 1) + (J - 1))) <
      2 * J * B) :
    ∃ r s : Fin J → F[X],
      (∀ j, (r j).degree < (B : WithBot ℕ)) ∧
      (∀ j, (s j).degree < (B : WithBot ℕ)) ∧
      (∃ j, r j ≠ 0 ∨ s j ≠ 0) ∧
      ∀ k < ell, stepanovConstraint f hf ell e a k r s = 0 := by
  classical
  let L := stepanovConstraintMap f hf ell e B J a hm hJ
  have hn : ¬ Function.Injective L := by
    intro hi
    have hd := LinearMap.finrank_le_finrank_of_injective hi
    rw [stepanovCoefficients_finrank, stepanovConstraints_finrank] at hd
    exact (not_lt_of_ge hd) hcount
  have hex : ∃ v, L v = 0 ∧ v ≠ 0 := by
    by_contra h
    apply hn
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hv'
    exact h ⟨v, hv, hv'⟩
  obtain ⟨v, hv, hv0⟩ := hex
  refine ⟨(fun j => (v j).1), (fun j => (v j).2),
    (fun j => mem_degreeLT.mp (v j).1.property),
    (fun j => mem_degreeLT.mp (v j).2.property), ?_, ?_⟩
  · by_contra hn
    apply hv0
    funext j
    apply Prod.ext <;> apply Subtype.ext
    · by_contra h
      exact hn ⟨j, Or.inl h⟩
    · by_contra h
      exact hn ⟨j, Or.inr h⟩
  · intro k hk
    have he := congrArg (fun w => ((w ⟨k, hk⟩ :
      degreeLT F (B + k * (f.natDegree - 1) + (J - 1))) : F[X])) hv
    exact he

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryStepanovNonzero -/

/-!
# Nonvanishing of the Stepanov auxiliary polynomial

The argument is the first half of printed page 11 of Gergely Harcos,
*Weil's bound for Kloosterman sums*
(`pages/harcos-stepanov-11.png`).

The nonsquare hypothesis is geometric: it concerns the polynomial after
base change to the algebraic closure, not just squares over the finite field.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Polynomial

variable {F : Type*} [Field F]

/-- A square times a polynomial cannot be a square unless that polynomial
is a square. Unique factorization supplies the required polynomial quotient. -/
private theorem stepanov_isSquare_of_sq_mul_eq_sq
    {K : Type*} [Field K] (f r t : K[X]) (hr : r ≠ 0)
    (h : r ^ 2 * f = t ^ 2) : IsSquare f := by
  have hdiv : r ^ 2 ∣ t ^ 2 := ⟨f, h.symm⟩
  obtain ⟨u, hu⟩ :=
    (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp hdiv
  refine ⟨u, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 hr)
  rw [h, hu]
  ring

/-- The geometric nonsquare obstruction used after reducing modulo `X^q`. -/
theorem stepanov_sq_mul_eq_const_mul_sq
    (f r s : F[X]) (c : F) (hc : c ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (h : r ^ 2 * f = s ^ 2 * C c) : r = 0 ∧ s = 0 := by
  have hr : r = 0 := by
    by_contra hr
    obtain ⟨a, ha⟩ :=
      IsAlgClosed.exists_pow_nat_eq (algebraMap F (AlgebraicClosure F) c)
        (by decide : 0 < 2)
    apply hf
    apply stepanov_isSquare_of_sq_mul_eq_sq
      (f.map (algebraMap F (AlgebraicClosure F)))
      (r.map (algebraMap F (AlgebraicClosure F)))
      (s.map (algebraMap F (AlgebraicClosure F)) * C a)
      (by simpa using hr)
    have hm := congrArg (Polynomial.map (algebraMap F (AlgebraicClosure F))) h
    simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
      mul_pow, ← C_pow, ha] using hm
  refine ⟨hr, ?_⟩
  rw [hr, zero_pow (by decide : 2 ≠ 0), zero_mul] at h
  have hs : s ^ 2 = 0 := (mul_eq_zero.mp h.symm).resolve_right (by simpa using hc)
  by_contra hs0
  exact pow_ne_zero 2 hs0 hs

variable [Fintype F]

/-- Frobenius makes the constant term the entire residue of `f^q` modulo `X^q`. -/
theorem stepanov_X_card_dvd_pow_sub_const (f : F[X]) :
    X ^ Fintype.card F ∣ f ^ Fintype.card F - C (f.eval 0) := by
  obtain ⟨p, hp, n, hprime, hcard⟩ := FiniteField.card' F
  let : CharP F p := hp
  let : Fact p.Prime := ⟨hprime⟩
  have hd : (X : F[X]) ∣ f - C (f.eval 0) := by
    rw [X_dvd_iff]
    simp [coeff_zero_eq_eval_zero]
  have hpow := pow_dvd_pow_of_dvd hd (Fintype.card F)
  have he : (f - C (f.eval 0)) ^ Fintype.card F =
      f ^ Fintype.card F - C (f.eval 0) := by
    rw [hcard, sub_pow_char_pow, ← C_pow, ← hcard, FiniteField.pow_card]
  rwa [he] at hpow

omit [Fintype F] in
private theorem stepanov_natDegree_le_pred {r : F[X]} {B : ℕ}
    (hr : r.degree < (B : WithBot ℕ)) : r.natDegree ≤ B - 1 := by
  by_cases hzero : r = 0
  · simp [hzero]
  rw [degree_eq_natDegree hzero] at hr
  have hr' : r.natDegree < B := by exact_mod_cast hr
  omega

/-- Harcos's residue kernel lemma: a degree-bounded block cannot be divisible
by `X^q`. The degree convention includes zero polynomials even when `B = 0`. -/
theorem stepanov_block_eq_zero_of_X_card_dvd
    (f r s : F[X]) (B : ℕ)
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hr : r.degree < (B : WithBot ℕ)) (hs : s.degree < (B : WithBot ℕ))
    (hB : 2 * (B - 1) + f.natDegree < Fintype.card F)
    (hdiv : X ^ Fintype.card F ∣ r + s * f ^ ((Fintype.card F - 1) / 2)) :
    r = 0 ∧ s = 0 := by
  have he : 2 * ((Fintype.card F - 1) / 2) + 1 = Fintype.card F := by
    obtain ⟨k, hk⟩ := hq
    omega
  have hp : (f ^ ((Fintype.card F - 1) / 2)) ^ 2 * f =
      f ^ Fintype.card F := by
    rw [← pow_mul, ← pow_succ]
    congr 1
    omega
  have hd₁ : X ^ Fintype.card F ∣ r ^ 2 * f - s ^ 2 * f ^ Fintype.card F := by
    have hd := dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left hdiv (r - s * f ^ ((Fintype.card F - 1) / 2))) f
    convert hd using 1
    rw [← hp]
    ring
  have hd₂ := dvd_mul_of_dvd_right (stepanov_X_card_dvd_pow_sub_const f) (s ^ 2)
  have hd : X ^ Fintype.card F ∣ r ^ 2 * f - s ^ 2 * C (f.eval 0) := by
    convert dvd_add hd₁ hd₂ using 1
    ring
  have hrB := stepanov_natDegree_le_pred hr
  have hsB := stepanov_natDegree_le_pred hs
  have hdr : (r ^ 2 * f).natDegree ≤ 2 * (B - 1) + f.natDegree := by
    calc
      _ ≤ (r ^ 2).natDegree + f.natDegree := natDegree_mul_le
      _ ≤ _ := by rw [natDegree_pow]; omega
  have hds : (s ^ 2 * C (f.eval 0)).natDegree ≤ 2 * (B - 1) + f.natDegree := by
    calc
      _ ≤ (s ^ 2).natDegree + (C (f.eval 0)).natDegree := natDegree_mul_le
      _ ≤ _ := by rw [natDegree_pow, natDegree_C]; omega
  have hz : r ^ 2 * f - s ^ 2 * C (f.eval 0) = 0 := by
    apply eq_zero_of_dvd_of_natDegree_lt hd
    rw [natDegree_X_pow]
    exact lt_of_le_of_lt
      ((natDegree_sub_le _ _).trans (max_le hdr hds)) hB
  exact stepanov_sq_mul_eq_const_mul_sq f r s (f.eval 0) hf0 hf (sub_eq_zero.mp hz)

/-- The actual Stepanov block ansatz, before multiplication by `f^ell`. -/
def stepanovAnsatz (f : F[X]) {J : ℕ} (r s : Fin J → F[X]) : F[X] :=
  ∑ j : Fin J,
    (r j + s j * f ^ ((Fintype.card F - 1) / 2)) * X ^ (j.val * Fintype.card F)

private theorem stepanovAnsatz_succ (f : F[X]) {J : ℕ}
    (r s : Fin (J + 1) → F[X]) :
    stepanovAnsatz f r s =
      r 0 + s 0 * f ^ ((Fintype.card F - 1) / 2) +
        stepanovAnsatz f (fun j : Fin J => r j.succ) (fun j : Fin J => s j.succ) *
          X ^ Fintype.card F := by
  simp [stepanovAnsatz, Fin.sum_univ_succ, Nat.add_mul, pow_add, Finset.sum_mul,
    mul_assoc]

/-- All coefficients vanish if the actual Stepanov ansatz vanishes.
Successively removing the first block is equivalent to Harcos's choice
of the least nonzero block. -/
theorem stepanovAnsatz_coefficients_eq_zero
    (f : F[X]) {J B : ℕ} (r s : Fin J → F[X])
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hr : ∀ j, (r j).degree < (B : WithBot ℕ))
    (hs : ∀ j, (s j).degree < (B : WithBot ℕ))
    (hB : 2 * (B - 1) + f.natDegree < Fintype.card F)
    (hz : stepanovAnsatz f r s = 0) : ∀ j, r j = 0 ∧ s j = 0 := by
  induction J with
  | zero => intro j; exact Fin.elim0 j
  | succ J ih =>
      rw [stepanovAnsatz_succ] at hz
      have hdiv : X ^ Fintype.card F ∣
          r 0 + s 0 * f ^ ((Fintype.card F - 1) / 2) := by
        rw [eq_neg_of_add_eq_zero_left hz]
        exact dvd_neg.mpr (dvd_mul_left _ _)
      have hzero := stepanov_block_eq_zero_of_X_card_dvd
        f (r 0) (s 0) B hq hf0 hf (hr 0) (hs 0) hB hdiv
      have htail :
          stepanovAnsatz f (fun j : Fin J => r j.succ) (fun j : Fin J => s j.succ) = 0 := by
        have ht :
            stepanovAnsatz f (fun j : Fin J => r j.succ) (fun j : Fin J => s j.succ) *
              X ^ Fintype.card F = 0 := by
          simpa only [hzero.1, hzero.2, zero_mul, zero_add] using hz
        exact (mul_eq_zero.mp ht).resolve_right (pow_ne_zero _ X_ne_zero)
      have ht := ih (fun j : Fin J => r j.succ) (fun j : Fin J => s j.succ)
        (fun j => hr j.succ) (fun j => hs j.succ) htail
      intro j
      exact Fin.cases hzero (fun i => ht i) j


/-- Harcos page 11: a nontrivial bounded coefficient family gives a nonzero
auxiliary polynomial, under the geometric nonsquare hypothesis. -/
theorem stepanovAnsatz_ne_zero
    (f : F[X]) {J B : ℕ} (r s : Fin J → F[X])
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hr : ∀ j, (r j).degree < (B : WithBot ℕ))
    (hs : ∀ j, (s j).degree < (B : WithBot ℕ))
    (hB : 2 * (B - 1) + f.natDegree < Fintype.card F)
    (hne : ∃ j, r j ≠ 0 ∨ s j ≠ 0) : stepanovAnsatz f r s ≠ 0 := by
  intro hz
  have hall := stepanovAnsatz_coefficients_eq_zero f r s hq hf0 hf hr hs hB hz
  obtain ⟨j, hj⟩ := hne
  exact hj.elim (fun h => h (hall j).1) (fun h => h (hall j).2)

/-- The same nonvanishing conclusion after the multiplier in Harcos's ansatz. -/
theorem stepanov_pow_mul_ansatz_ne_zero
    (f : F[X]) (ell : ℕ) {J B : ℕ} (r s : Fin J → F[X])
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hr : ∀ j, (r j).degree < (B : WithBot ℕ))
    (hs : ∀ j, (s j).degree < (B : WithBot ℕ))
    (hB : 2 * (B - 1) + f.natDegree < Fintype.card F)
    (hne : ∃ j, r j ≠ 0 ∨ s j ≠ 0) :
    f ^ ell * stepanovAnsatz f r s ≠ 0 := by
  have hfne : f ≠ 0 := by
    intro hz
    apply hf0
    simp [hz]
  exact mul_ne_zero (pow_ne_zero ell hfne)
    (stepanovAnsatz_ne_zero f r s hq hf0 hf hr hs hB hne)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryStepanovVanishing -/

/-!
# Vanishing of the actual Stepanov auxiliary polynomial

This is the passage from (20) to (22) on printed page 11 of Harcos,
*Weil's bound for Kloosterman sums*
(`pages/harcos-stepanov-11.png`). Frobenius kills the positive Hasse
derivatives of `X^(jq)` below order `q`. Factoring out `f^(ell-k)`
additionally requires `k ≤ ell`; the vanishing application uses `k < ell ≤ q`.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Polynomial

variable {F : Type*} [Field F] [Fintype F]

/-- Frobenius forces every positive Hasse derivative of `X^(jq)` below
order `q` to vanish as a polynomial, not just as a function on the field.
The Frobenius residue of `((X + 1)^j)^q` determines its low Taylor
coefficients; evaluating a Hasse monomial at `1` recovers its sole coefficient. -/
theorem stepanov_hasseDeriv_X_card_mul (j k : ℕ)
    (hk : 0 < k) (hkq : k < Fintype.card F) :
    hasseDeriv k ((X : F[X]) ^ (j * Fintype.card F)) = 0 := by
  have hd := stepanov_X_card_dvd_pow_sub_const (((X : F[X]) + C 1) ^ j)
  have hc := (X_pow_dvd_iff.mp hd) k hkq
  have ht : (taylor (1 : F) (X ^ (j * Fintype.card F))).coeff k = 0 := by
    simpa [taylor_X_pow, pow_mul, coeff_sub, coeff_C, coeff_one, Nat.ne_of_gt hk]
      using hc
  have hchoose : ((j * Fintype.card F).choose k : F) = 0 := by
    rw [taylor_coeff, X_pow_eq_monomial, hasseDeriv_monomial] at ht
    simpa using ht
  rw [X_pow_eq_monomial, hasseDeriv_monomial, hchoose, zero_mul, monomial_zero_right]

/-- Below order `q`, a factor `X^(jq)` is constant for Hasse differentiation. -/
theorem stepanov_hasseDeriv_mul_X_card_mul (g : F[X]) (j k : ℕ)
    (hkq : k < Fintype.card F) :
    hasseDeriv k (g * X ^ (j * Fintype.card F)) =
      hasseDeriv k g * X ^ (j * Fintype.card F) := by
  classical
  rw [hasseDeriv_mul, Finset.sum_eq_single (k, 0)]
  · simp
  · intro ij hij hne
    have hij' := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hj : 0 < ij.2 := by
      by_contra hn
      have hz : ij.2 = 0 := by omega
      apply hne
      apply Prod.ext <;> simp_all
    rw [stepanov_hasseDeriv_X_card_mul j ij.2 hj (by omega), mul_zero]
  · simp

/-- Equation (20), with the necessary extraction range `k ≤ ell`. -/
theorem stepanov_hasseDeriv_pow_mul_ansatz
    (f : F[X]) (hf : f ≠ 0) (ell k : ℕ) {J : ℕ}
    (r s : Fin J → F[X]) (hk : k ≤ ell) (hkq : k < Fintype.card F) :
    hasseDeriv k (f ^ ell * stepanovAnsatz f r s) =
      f ^ (ell - k) *
        ∑ j : Fin J,
          (stepanovHasseOperator f hf ell k (r j) +
            stepanovHasseOperator f hf (ell + (Fintype.card F - 1) / 2) k (s j) *
              f ^ ((Fintype.card F - 1) / 2)) * X ^ (j.val * Fintype.card F) := by
  classical
  have he : ell + (Fintype.card F - 1) / 2 - k =
      ell - k + (Fintype.card F - 1) / 2 := by omega
  simp only [stepanovAnsatz, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hblock :
      f ^ ell * ((r j + s j * f ^ ((Fintype.card F - 1) / 2)) *
        X ^ (j.val * Fintype.card F)) =
      (r j * f ^ ell + s j * f ^ (ell + (Fintype.card F - 1) / 2)) *
        X ^ (j.val * Fintype.card F) := by
    rw [pow_add]
    ring
  rw [hblock, stepanov_hasseDeriv_mul_X_card_mul _ _ _ hkq, map_add,
    stepanovHasseOperator_spec f hf ell k,
    stepanovHasseOperator_spec f hf (ell + (Fintype.card F - 1) / 2) k,
    he, pow_add]
  ring

/-- Evaluating (20) at `f(x)^((q-1)/2) = a` gives precisely (22). -/
theorem stepanov_hasseDeriv_pow_mul_ansatz_eval
    (f : F[X]) (hf : f ≠ 0) (ell k : ℕ) {J : ℕ}
    (r s : Fin J → F[X]) (a x : F)
    (hk : k < ell) (hell : ell ≤ Fintype.card F)
    (hx : f.eval x ^ ((Fintype.card F - 1) / 2) = a) :
    (hasseDeriv k (f ^ ell * stepanovAnsatz f r s)).eval x =
      f.eval x ^ (ell - k) *
        (stepanovConstraint f hf ell ((Fintype.card F - 1) / 2) a k r s).eval x := by
  rw [stepanov_hasseDeriv_pow_mul_ansatz f hf ell k r s (Nat.le_of_lt hk)
    (lt_of_lt_of_le hk hell)]
  simp only [stepanovConstraint, eval_mul, eval_pow, eval_finsetSum, eval_add,
    eval_X, eval_smul, smul_eq_mul, hx]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Nat.mul_comm j.val, pow_mul, FiniteField.pow_card]
  ring

omit [Fintype F] in
/-- At a zero of `f`, the multiplier `f^ell` itself supplies all required
Hasse vanishing, independently of the coefficient equations. -/
theorem stepanov_hasseDeriv_pow_mul_eval_zero
    (f g : F[X]) (ell k : ℕ) (x : F) (hk : k < ell) (hx : f.eval x = 0) :
    (hasseDeriv k (f ^ ell * g)).eval x = 0 := by
  obtain ⟨u, hu⟩ := stepanov_pow_dvd_hasseDeriv_mul_pow f g ell k
  rw [mul_comm (f ^ ell) g, hu, eval_mul, eval_pow, hx,
    zero_pow (by omega : ell - k ≠ 0), zero_mul]

/-- The actual equation system (22) forces Hasse vanishing of the actual
auxiliary polynomial at the union of the two specified loci. -/
theorem stepanov_constraints_imply_hasse_vanishing
    (f : F[X]) (hf : f ≠ 0) (ell : ℕ) {J : ℕ}
    (r s : Fin J → F[X]) (a : F) (hell : ell ≤ Fintype.card F)
    (hc : ∀ k < ell,
      stepanovConstraint f hf ell ((Fintype.card F - 1) / 2) a k r s = 0) :
    ∀ x : F, f.eval x = 0 ∨ f.eval x ^ ((Fintype.card F - 1) / 2) = a →
      ∀ k < ell, (hasseDeriv k (f ^ ell * stepanovAnsatz f r s)).eval x = 0 := by
  intro x hx k hk
  rcases hx with hx | hx
  · exact stepanov_hasseDeriv_pow_mul_eval_zero f (stepanovAnsatz f r s) ell k x hk hx
  · rw [stepanov_hasseDeriv_pow_mul_ansatz_eval f hf ell k r s a x hk hell hx,
      hc k hk, eval_zero, mul_zero]

omit [Fintype F] in
private theorem stepanov_degree_mul_lt_add_natDegree
    (p g : F[X]) (B : ℕ) (hp : p.degree < (B : WithBot ℕ)) :
    (p * g).degree < ((B + g.natDegree : ℕ) : WithBot ℕ) := by
  calc
    (p * g).degree ≤ p.degree + g.degree := degree_mul_le p g
    _ ≤ p.degree + (g.natDegree : WithBot ℕ) := by
      exact add_le_add le_rfl degree_le_natDegree
    _ < (B : WithBot ℕ) + (g.natDegree : WithBot ℕ) :=
      WithBot.add_lt_add_right (by simp) hp
    _ = _ := by rw [Nat.cast_add]

/-- Degree of the block ansatz, including the empty family and zero
coefficients. The strict `degree` convention also covers `B = 0`. -/
theorem stepanovAnsatz_degree_lt
    (f : F[X]) {J B : ℕ} (r s : Fin J → F[X])
    (hr : ∀ j, (r j).degree < (B : WithBot ℕ))
    (hs : ∀ j, (s j).degree < (B : WithBot ℕ)) :
    (stepanovAnsatz f r s).degree <
      ((B + (Fintype.card F - 1) / 2 * f.natDegree +
        (J - 1) * Fintype.card F : ℕ) : WithBot ℕ) := by
  apply mem_degreeLT.mp
  apply Submodule.sum_mem
  intro j _
  apply mem_degreeLT.mpr
  have hr' : (r j).degree <
      ((B + (Fintype.card F - 1) / 2 * f.natDegree : ℕ) : WithBot ℕ) := by
    apply (hr j).trans_le
    exact_mod_cast Nat.le_add_right B ((Fintype.card F - 1) / 2 * f.natDegree)
  have hs' : (s j * f ^ ((Fintype.card F - 1) / 2)).degree <
      ((B + (Fintype.card F - 1) / 2 * f.natDegree : ℕ) : WithBot ℕ) := by
    simpa only [natDegree_pow] using
      stepanov_degree_mul_lt_add_natDegree (s j)
        (f ^ ((Fintype.card F - 1) / 2)) B (hs j)
  have hd := (degree_add_le _ _).trans_lt (max_lt hr' hs')
  rw [degree_mul_X_pow]
  calc
    _ < ((B + (Fintype.card F - 1) / 2 * f.natDegree : ℕ) : WithBot ℕ) +
        ((j.val * Fintype.card F : ℕ) : WithBot ℕ) :=
      WithBot.add_lt_add_right WithBot.coe_ne_bot hd
    _ ≤ _ := by
      rw [← Nat.cast_add]
      exact_mod_cast Nat.add_le_add_left
        (Nat.mul_le_mul_right (Fintype.card F) (show j.val ≤ J - 1 by omega)) _

/-- Degree budget for the actual auxiliary polynomial used in point counting. -/
theorem stepanov_pow_mul_ansatz_degree_lt
    (f : F[X]) (ell : ℕ) {J B : ℕ} (r s : Fin J → F[X])
    (hr : ∀ j, (r j).degree < (B : WithBot ℕ))
    (hs : ∀ j, (s j).degree < (B : WithBot ℕ)) :
    (f ^ ell * stepanovAnsatz f r s).degree <
      ((B + (Fintype.card F - 1) / 2 * f.natDegree +
        (J - 1) * Fintype.card F + ell * f.natDegree : ℕ) : WithBot ℕ) := by
  rw [mul_comm]
  simpa only [natDegree_pow] using
    stepanov_degree_mul_lt_add_natDegree (stepanovAnsatz f r s) (f ^ ell)
      (B + (Fintype.card F - 1) / 2 * f.natDegree + (J - 1) * Fintype.card F)
      (stepanovAnsatz_degree_lt f r s hr hs)

/-- Harcos's auxiliary polynomial exists from the actual dimension
inequality, with nonvanishing, degree control, and genuine Hasse vanishing. -/
theorem stepanov_exists_auxiliary_polynomial
    (f : F[X]) (ell B J : ℕ) (a : F)
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hm : 1 ≤ f.natDegree) (hJ : 0 < J) (hell : ell ≤ Fintype.card F)
    (hB : 2 * (B - 1) + f.natDegree < Fintype.card F)
    (hcount : (∑ k : Fin ell, (B + k.val * (f.natDegree - 1) + (J - 1))) <
      2 * J * B) :
    ∃ h : F[X], h ≠ 0 ∧
      h.degree < ((B + (Fintype.card F - 1) / 2 * f.natDegree +
        (J - 1) * Fintype.card F + ell * f.natDegree : ℕ) : WithBot ℕ) ∧
      ∀ x : F, f.eval x = 0 ∨ f.eval x ^ ((Fintype.card F - 1) / 2) = a →
        ∀ k < ell, (hasseDeriv k h).eval x = 0 := by
  have hfne : f ≠ 0 := by
    intro hz
    apply hf0
    simp [hz]
  obtain ⟨r, s, hr, hs, hne, hc⟩ :=
    stepanov_exists_coefficients f hfne ell ((Fintype.card F - 1) / 2) B J a hm hJ hcount
  exact ⟨f ^ ell * stepanovAnsatz f r s,
    stepanov_pow_mul_ansatz_ne_zero f ell r s hq hf0 hf hr hs hB hne,
    stepanov_pow_mul_ansatz_degree_lt f ell r s hr hs,
    stepanov_constraints_imply_hasse_vanishing f hfne ell r s a hell hc⟩

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryStepanovParameters -/

/-!
# Integer parameters for the Stepanov construction

Harcos, *Weil's bound for Kloosterman sums*, printed
page 12 (`pages/harcos-weil-12.png`). The coefficient spaces have integer
dimension `2 * J * B`; the equation space has the actual dimension
`∑ k : Fin ell, (B + k.val * (m - 1) + (J - 1))`.
The ceiling choices below prove the strict inequality between these dimensions.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Polynomial

/-- The multiplicity parameter on Harcos's printed page 12. -/
def stepanovEll (q : ℕ) : ℕ := ⌈Real.sqrt (q : ℝ)⌉₊

/-- The integer number of coefficients in each polynomial block. -/
def stepanovB (q m : ℕ) : ℕ := ⌈((q : ℝ) - m) / 2⌉₊

/-- The integer number of blocks in each of the two polynomial families. -/
def stepanovJ (q m ell : ℕ) : ℕ :=
  ⌈(ell : ℝ) / 2 + (ell : ℝ) ^ 2 * m / q⌉₊


/-- The real form of the exact count, with no rounding of dimensions. -/
theorem stepanov_equation_count_real (ell B J m : ℕ)
    (hell : 0 < ell) (hJ : 0 < J) (hm : 1 ≤ m) :
    ((∑ k : Fin ell, (B + k.val * (m - 1) + (J - 1)) : ℕ) : ℝ) =
      (ell : ℝ) * (B + J - 1) +
        (ell : ℝ) * (ell - 1) / 2 * (m - 1) := by
  have hsum : (∑ k : Fin ell, (k.val : ℝ)) * 2 =
      (ell : ℝ) * (ell - 1) := by
    have h := Finset.sum_range_id_mul_two ell
    rw [← Fin.sum_univ_eq_sum_range] at h
    have h' := congrArg (fun n : ℕ => (n : ℝ)) h
    simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat,
      Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hell)), Nat.cast_one] using h'
  push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hJ)),
    Nat.cast_sub hm]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  nlinarith

/-- For `q > 18`, the source's ceiling of the square root satisfies both
the construction's range restriction and the final square-root bound. -/
theorem stepanovEll_bounds {q : ℕ} (hq : 18 < q) :
    0 < stepanovEll q ∧ 3 * stepanovEll q ≤ q ∧ q ≤ stepanovEll q ^ 2 := by
  have hqR : (19 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  have hs2 := Real.sq_sqrt hq0
  have helo := Nat.le_ceil (Real.sqrt (q : ℝ))
  have hehi := Nat.ceil_lt_add_one hs0
  have hsbound : Real.sqrt (q : ℝ) + 1 ≤ (q : ℝ) / 3 := by
    have hsq : (q : ℝ) ≤ ((q : ℝ) / 3 - 1) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hqR) hq0]
    nlinarith
  have helpos : 0 < stepanovEll q := by
    apply Nat.ceil_pos.mpr
    positivity
  refine ⟨helpos, ?_, ?_⟩
  · have : (3 : ℝ) * stepanovEll q ≤ q := by
      dsimp [stepanovEll]
      linarith
    exact_mod_cast this
  · have : (q : ℝ) ≤ (stepanovEll q : ℝ) ^ 2 := by
      dsimp [stepanovEll]
      nlinarith
    exact_mod_cast this

/-- The ceiling defining the coefficient-block size respects the strict
nonvanishing restriction `2(B-1)+m < q`. -/
theorem stepanovB_bounds {q m : ℕ} (hmq : m < q) :
    0 < stepanovB q m ∧
      ((q : ℝ) - m) / 2 ≤ stepanovB q m ∧
      (stepanovB q m : ℝ) < ((q : ℝ) - m) / 2 + 1 ∧
      2 * (stepanovB q m - 1) + m < q := by
  have hmqR : (m : ℝ) < q := by exact_mod_cast hmq
  have ht : 0 < ((q : ℝ) - m) / 2 := by linarith
  have hpos : 0 < stepanovB q m := Nat.ceil_pos.mpr ht
  have hlo := Nat.le_ceil (((q : ℝ) - m) / 2)
  have hhi := Nat.ceil_lt_add_one (le_of_lt ht)
  refine ⟨hpos, hlo, hhi, ?_⟩
  have hcast : ((stepanovB q m - 1 : ℕ) : ℝ) = stepanovB q m - 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpos)), Nat.cast_one]
  have : (2 : ℝ) * ((stepanovB q m - 1 : ℕ) : ℝ) + m < q := by
    rw [hcast]
    dsimp [stepanovB]
    linarith
  exact_mod_cast this

/-- Integer rounding of the two block parameters gives strictly more
unknown coefficients than actual coefficient equations. -/
theorem stepanov_parameters_count {q m ell : ℕ}
    (hm : 3 ≤ m) (hmq : 6 * m < q)
    (hell : 0 < ell) (hellq : 3 * ell ≤ q) :
    0 < stepanovJ q m ell ∧
      (∑ k : Fin ell,
        (stepanovB q m + k.val * (m - 1) + (stepanovJ q m ell - 1))) <
        2 * stepanovJ q m ell * stepanovB q m := by
  let B := stepanovB q m
  let J := stepanovJ q m ell
  have hq : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hmqR : (6 : ℝ) * m < q := by exact_mod_cast hmq
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hellqR : (3 : ℝ) * ell ≤ q := by exact_mod_cast hellq
  have hu : 0 < (ell : ℝ) / 2 + (ell : ℝ) ^ 2 * m / q := by positivity
  have hJ : 0 < J := Nat.ceil_pos.mpr hu
  have hJlo : (ell : ℝ) / 2 + (ell : ℝ) ^ 2 * m / q ≤ J :=
    Nat.le_ceil _
  obtain ⟨_, hBlo, hBhi, _⟩ := stepanovB_bounds (show m < q by omega)
  change ((q : ℝ) - m) / 2 ≤ (B : ℝ) at hBlo
  change (B : ℝ) < ((q : ℝ) - m) / 2 + 1 at hBhi
  have hJshift : 0 ≤ (J : ℝ) - (ell : ℝ) / 2 := by
    have : 0 ≤ (ell : ℝ) ^ 2 * m / q := by positivity
    linarith
  have hhalf : (q : ℝ) / 2 ≤ q - m - ell := by linarith
  have hshiftq : (ell : ℝ) ^ 2 * m ≤ ((J : ℝ) - (ell : ℝ) / 2) * q :=
    (div_le_iff₀ hq).mp (by linarith)
  have hshift := mul_le_mul_of_nonneg_left hhalf hJshift
  have hdimension :
      (ell : ℝ) * (((q : ℝ) - m) / 2 + J) +
        (ell : ℝ) ^ 2 / 2 * (m - 1) ≤ (J : ℝ) * (q - m) := by
    nlinarith only [hshiftq, hshift]
  have hcountReal := stepanov_equation_count_real ell B J m hell hJ (by omega)
  have hupper :
      ((∑ k : Fin ell, (B + k.val * (m - 1) + (J - 1)) : ℕ) : ℝ) <
        (ell : ℝ) * (((q : ℝ) - m) / 2 + J) +
          (ell : ℝ) ^ 2 / 2 * (m - 1) := by
    have hmul := mul_lt_mul_of_pos_left hBhi hellR
    have hpay : 0 ≤ (ell : ℝ) * (m - 1) :=
      mul_nonneg (le_of_lt hellR) (by linarith)
    nlinarith only [hcountReal, hmul, hpay]
  have hlower : (J : ℝ) * (q - m) ≤ 2 * J * B := by
    have hmul := mul_le_mul_of_nonneg_left hBlo (show 0 ≤ (2 : ℝ) * J by positivity)
    nlinarith only [hmul]
  refine ⟨hJ, ?_⟩
  have := hupper.trans_le (hdimension.trans hlower)
  exact_mod_cast this

/-- The same rounded parameters meet the source's degree budget.
Only the final step uses `q ≤ ell²`; no parity assumption is needed here. -/
theorem stepanov_parameters_degree {q m ell : ℕ}
    (hm : 3 ≤ m) (hmq : 6 * m < q)
    (hell : 0 < ell) (hellq : 3 * ell ≤ q) (hqsq : q ≤ ell ^ 2) :
    ((stepanovB q m + (q - 1) / 2 * m + (stepanovJ q m ell - 1) * q +
      ell * m : ℕ) : ℝ) <
      (ell : ℝ) * ((q : ℝ) / 2 + 2 * m * ell) := by
  let B := stepanovB q m
  let J := stepanovJ q m ell
  have hq : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hellqR : (3 : ℝ) * ell ≤ q := by exact_mod_cast hellq
  have hqsqR : (q : ℝ) ≤ (ell : ℝ) ^ 2 := by exact_mod_cast hqsq
  have hu : 0 < (ell : ℝ) / 2 + (ell : ℝ) ^ 2 * m / q := by positivity
  have hJ : 0 < J := Nat.ceil_pos.mpr hu
  have hJhi : (J : ℝ) < (ell : ℝ) / 2 + (ell : ℝ) ^ 2 * m / q + 1 :=
    Nat.ceil_lt_add_one (le_of_lt hu)
  have hBhi : (B : ℝ) < ((q : ℝ) - m) / 2 + 1 :=
    (stepanovB_bounds (show m < q by omega)).2.2.1
  have hJmul : ((J : ℝ) - 1) * q <
      (ell : ℝ) / 2 * q + (ell : ℝ) ^ 2 * m := by
    have h := (lt_div_iff₀ hq).mp
      (show (J : ℝ) - 1 - (ell : ℝ) / 2 < (ell : ℝ) ^ 2 * m / q by linarith)
    nlinarith only [h]
  have hhalf : (2 : ℝ) * (((q - 1) / 2 : ℕ) : ℝ) ≤ q := by
    exact_mod_cast (show 2 * ((q - 1) / 2) ≤ q by omega)
  have hhalfM := mul_le_mul_of_nonneg_right hhalf (show (0 : ℝ) ≤ m by positivity)
  have hellM := mul_le_mul_of_nonneg_right hellqR (show (0 : ℝ) ≤ m by positivity)
  have hmqnonneg : 0 ≤ (q : ℝ) * (m - 3) := by positivity
  have hD :
      ((B + (q - 1) / 2 * m + (J - 1) * q + ell * m : ℕ) : ℝ) =
        (B : ℝ) + (((q - 1) / 2 : ℕ) : ℝ) * m +
          ((J : ℝ) - 1) * q + (ell : ℝ) * m := by
    push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hJ))]
    rfl
  have hbudget :
      ((B + (q - 1) / 2 * m + (J - 1) * q + ell * m : ℕ) : ℝ) <
        (m : ℝ) * q + (ell : ℝ) * q / 2 + (ell : ℝ) ^ 2 * m := by
    nlinarith only [hD, hBhi, hJmul, hhalfM, hellM, hmqnonneg, hmR]
  have hsqM := mul_le_mul_of_nonneg_right hqsqR (show (0 : ℝ) ≤ m by positivity)
  change ((B + (q - 1) / 2 * m + (J - 1) * q + ell * m : ℕ) : ℝ) < _
  nlinarith only [hbudget, hsqM]

/-- All numerical requirements for the genuine finite-dimensional construction,
including its exact equation count and a strict real degree budget. -/
structure StepanovParameterBounds (q m ell B J : ℕ) : Prop where
  ell_pos : 0 < ell
  ell_le_card : ell ≤ q
  three_mul_ell_le : 3 * ell ≤ q
  card_le_ell_sq : q ≤ ell ^ 2
  B_pos : 0 < B
  J_pos : 0 < J
  coefficient_bound : 2 * (B - 1) + m < q
  equation_count_lt :
    (∑ k : Fin ell, (B + k.val * (m - 1) + (J - 1))) < 2 * J * B
  degree_budget :
    ((B + (q - 1) / 2 * m + (J - 1) * q + ell * m : ℕ) : ℝ) <
      (ell : ℝ) * ((q : ℝ) / 2 + 2 * m * ell)

/-- Harcos's three ceiling choices satisfy every integer constraint.
This numerical theorem is valid even without assuming `q` odd. -/
theorem stepanov_integer_parameters (q m : ℕ) (hm : 3 ≤ m) (hmq : 6 * m < q) :
    StepanovParameterBounds q m (stepanovEll q) (stepanovB q m)
      (stepanovJ q m (stepanovEll q)) := by
  obtain ⟨hell, hellq, hqsq⟩ := stepanovEll_bounds (show 18 < q by omega)
  obtain ⟨hB, _, _, hBq⟩ := stepanovB_bounds (show m < q by omega)
  obtain ⟨hJ, hcount⟩ := stepanov_parameters_count hm hmq hell hellq
  exact ⟨hell, by omega, hellq, hqsq, hB, hJ, hBq, hcount,
    stepanov_parameters_degree hm hmq hell hellq hqsq⟩


/-- The actual auxiliary polynomial with no assumed dimension inequality:
the integer choices above discharge all numerical construction hypotheses.
Both the strict integer degree bound and its real budget are retained. -/
theorem stepanov_exists_auxiliary_polynomial_of_large_card
    {F : Type*} [Field F] [Fintype F] (f : F[X]) (a : F)
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hm : 3 ≤ f.natDegree) (hmq : 6 * f.natDegree < Fintype.card F) :
    let q := Fintype.card F
    let ell := stepanovEll q
    let B := stepanovB q f.natDegree
    let J := stepanovJ q f.natDegree ell
    ∃ h : F[X], h ≠ 0 ∧
      h.degree < ((B + (q - 1) / 2 * f.natDegree +
        (J - 1) * q + ell * f.natDegree : ℕ) : WithBot ℕ) ∧
      (h.natDegree : ℝ) < (ell : ℝ) * ((q : ℝ) / 2 + 2 * f.natDegree * ell) ∧
      ∀ x : F, f.eval x = 0 ∨ f.eval x ^ ((q - 1) / 2) = a →
        ∀ k < ell, (hasseDeriv k h).eval x = 0 := by
  dsimp only
  have hp := stepanov_integer_parameters (Fintype.card F) f.natDegree hm hmq
  obtain ⟨h, hnz, hdeg, hvan⟩ := stepanov_exists_auxiliary_polynomial f
    (stepanovEll (Fintype.card F)) (stepanovB (Fintype.card F) f.natDegree)
    (stepanovJ (Fintype.card F) f.natDegree (stepanovEll (Fintype.card F)))
    a hq hf0 hf (by omega) hp.J_pos hp.ell_le_card hp.coefficient_bound
    hp.equation_count_lt
  refine ⟨h, hnz, hdeg, ?_, hvan⟩
  have hnat := (natDegree_lt_iff_degree_lt hnz).mpr hdeg
  have hreal :
      (h.natDegree : ℝ) <
        ((stepanovB (Fintype.card F) f.natDegree +
          (Fintype.card F - 1) / 2 * f.natDegree +
          (stepanovJ (Fintype.card F) f.natDegree (stepanovEll (Fintype.card F)) - 1) *
            Fintype.card F + stepanovEll (Fintype.card F) * f.natDegree : ℕ) : ℝ) := by
    exact_mod_cast hnat
  exact hreal.trans hp.degree_budget

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryStepanovPointCount -/

/-!
# Stepanov's square-root point-count bound

The nonzero auxiliary polynomials and their proved Hasse multiplicities
give the one-sided counts in Harcos (13). The quadratic character then
converts these bounds into the affine point count in Theorem 7.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Polynomial Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def stepanovLocus (f : F[X]) (a : F) : Finset F :=
  Finset.univ.filter fun x => f.eval x = 0 ∨
    f.eval x ^ ((Fintype.card F - 1) / 2) = a

theorem stepanov_locus_card_lt (f : F[X]) (a : F)
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hm : 3 ≤ f.natDegree) (hmq : 6 * f.natDegree < Fintype.card F) :
    ((stepanovLocus f a).card : ℝ) < (Fintype.card F : ℝ) / 2 +
      2 * f.natDegree * stepanovEll (Fintype.card F) := by
  classical
  obtain ⟨h, hnz, _, hdeg, hvan⟩ :=
    stepanov_exists_auxiliary_polynomial_of_large_card f a hq hf0 hf hm hmq
  have hroot := stepanov_card_mul_hasse_order_le h hnz (stepanovLocus f a)
    (stepanovEll (Fintype.card F)) (fun x hx => hvan x
      (by simpa only [stepanovLocus, mem_filter, mem_univ, true_and] using hx))
  have hell := (stepanov_integer_parameters (Fintype.card F) f.natDegree hm hmq).ell_pos
  have hrootR : ((stepanovLocus f a).card : ℝ) *
      (stepanovEll (Fintype.card F) : ℝ) ≤ h.natDegree := by exact_mod_cast hroot
  have hellR : (0 : ℝ) < stepanovEll (Fintype.card F) := by exact_mod_cast hell
  nlinarith

omit [DecidableEq F] in
private theorem stepanov_char_ne_two (hq : Odd (Fintype.card F)) : ringChar F ≠ 2 := by
  intro h
  have hc := FiniteField.even_card_of_char_two h
  obtain ⟨k, hk⟩ := hq
  omega

private theorem stepanov_quadraticChar_locus_bounds (f : F[X])
    (hq : Odd (Fintype.card F)) (x : F) :
    (quadraticChar F (f.eval x) : ℝ) ≤
        2 * (if x ∈ stepanovLocus f 1 then 1 else 0 : ℝ) - 1 ∧
      1 - 2 * (if x ∈ stepanovLocus f (-1) then 1 else 0 : ℝ) ≤
        (quadraticChar F (f.eval x) : ℝ) := by
  classical
  have he : Fintype.card F / 2 = (Fintype.card F - 1) / 2 := by
    obtain ⟨k, hk⟩ := hq
    omega
  have hp := quadraticChar_eq_pow_of_char_ne_two' (stepanov_char_ne_two hq) (f.eval x)
  rw [he] at hp
  by_cases hz : f.eval x = 0
  · simp [stepanovLocus, hz]
  rcases quadraticChar_dichotomy hz with h | h
  · have hx : x ∈ stepanovLocus f 1 := by
      simp only [stepanovLocus, mem_filter, mem_univ, true_and]
      right
      simpa [h] using hp.symm
    rw [h, if_pos hx]
    norm_num
    split_ifs <;> norm_num
  · have hx : x ∈ stepanovLocus f (-1) := by
      simp only [stepanovLocus, mem_filter, mem_univ, true_and]
      right
      simpa [h] using hp.symm
    rw [h, if_pos hx]
    norm_num
    split_ifs <;> norm_num

theorem stepanov_quadraticChar_sum_bound_of_eval_zero_ne (f : F[X])
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hm : 3 ≤ f.natDegree) (hmq : 6 * f.natDegree < Fintype.card F) :
    |∑ x : F, (quadraticChar F (f.eval x) : ℝ)| <
      4 * f.natDegree * stepanovEll (Fintype.card F) := by
  classical
  have hp := stepanov_locus_card_lt f 1 hq hf0 hf hm hmq
  have hn := stepanov_locus_card_lt f (-1) hq hf0 hf hm hmq
  have hu := sum_le_sum (s := (univ : Finset F))
    (fun x _ => (stepanov_quadraticChar_locus_bounds f hq x).1)
  have hl := sum_le_sum (s := (univ : Finset F))
    (fun x _ => (stepanov_quadraticChar_locus_bounds f hq x).2)
  have hi (a : F) :
      (∑ x : F, (if x ∈ stepanovLocus f a then 1 else 0 : ℝ)) =
        (stepanovLocus f a).card := by simp
  simp only [sum_sub_distrib, ← mul_sum, hi, sum_const, card_univ, nsmul_eq_mul,
    mul_one] at hu hl
  rw [abs_lt]
  constructor <;> linarith

def stepanovPointCount (f : F[X]) : ℕ :=
  (Finset.univ.filter fun xy : F × F => xy.2 ^ 2 = f.eval xy.1).card

/-- The affine point count is exactly `q` plus the quadratic-character sum. -/
theorem stepanovPointCount_eq (f : F[X]) (hq : Odd (Fintype.card F)) :
    (stepanovPointCount f : ℝ) =
      Fintype.card F + ∑ x : F, (quadraticChar F (f.eval x) : ℝ) := by
  classical
  have hfiber (x : F) :
      ((univ.filter fun y : F => y ^ 2 = f.eval x).card : ℝ) =
        (quadraticChar F (f.eval x) : ℝ) + 1 := by
    have h := quadraticChar_card_sqrts (stepanov_char_ne_two hq) (f.eval x)
    simp only [Set.toFinset_ofPred] at h
    exact_mod_cast h
  have hsum : stepanovPointCount f =
      ∑ x : F, (univ.filter fun y : F => y ^ 2 = f.eval x).card := by
    simp only [stepanovPointCount, card_eq_sum_ones, sum_filter, Fintype.sum_prod_type]
  rw [hsum, Nat.cast_sum]
  simp only [hfiber, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one]
  ring

/-- Harcos Theorem 7 with the harmless normalization `f(0) ≠ 0` still explicit. -/
theorem stepanov_pointCount_bound_of_eval_zero_ne (f : F[X])
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hm : 3 ≤ f.natDegree) (hmq : 6 * f.natDegree < Fintype.card F) :
    |(stepanovPointCount f : ℝ) - Fintype.card F| <
      4 * f.natDegree * ⌈Real.sqrt (Fintype.card F : ℝ)⌉₊ := by
  rw [stepanovPointCount_eq f hq, add_sub_cancel_left]
  exact stepanov_quadraticChar_sum_bound_of_eval_zero_ne f hq hf0 hf hm hmq

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosCurve -/

/-!
# Harcos's affine curve

The final paragraph of Harcos, page 12 (`pages/harcos-weil-12.png`), applies
Theorem 7 to `(X^p - X)^2 - 4ab`.  The geometric nonsquareness below follows
the source's factorization argument, rather than assuming a curve estimate.
The count is the actual affine count, not the count of a projective completion.
The final section removes the auxiliary normalization `f(0) ≠ 0` by translation,
giving Theorem 7 in its original domain.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Polynomial Finset

section Algebra

variable {K : Type*} [Field K]

def harcosCurvePolynomial (p : ℕ) (a b : K) : K[X] :=
  (X ^ p - X) ^ 2 - C (4 * a * b)

theorem harcosCurvePolynomial_eval (p : ℕ) (a b x : K) :
    (harcosCurvePolynomial p a b).eval x = (x ^ p - x) ^ 2 - 4 * a * b := by
  simp [harcosCurvePolynomial]

theorem harcosCurvePolynomial_eval_zero (p : ℕ) (hp : 0 < p) (a b : K) :
    (harcosCurvePolynomial p a b).eval 0 = -(4 * a * b) := by
  simp [harcosCurvePolynomial_eval, hp.ne']

theorem harcosCurvePolynomial_natDegree (p : ℕ) (hp : 1 < p) (a b : K) :
    (harcosCurvePolynomial p a b).natDegree = 2 * p := by
  have hdeg : ((X : K[X]) ^ p - X).natDegree = p := by
    rw [natDegree_sub_eq_left_of_natDegree_lt]
    · simp
    · simpa using hp
  simp only [harcosCurvePolynomial, natDegree_sub_C, natDegree_pow, hdeg]

theorem harcosCurvePolynomial_eval_zero_ne (p : ℕ) (hp : 0 < p)
    (htwo : (2 : K) ≠ 0) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (harcosCurvePolynomial p a b).eval 0 ≠ 0 := by
  rw [harcosCurvePolynomial_eval_zero p hp]
  have hfour : (4 : K) ≠ 0 := by
    have := mul_ne_zero htwo htwo
    norm_num at this ⊢
    exact this
  exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hfour ha) hb)

/-- The source's two factors have degree zero, contradicting their `X^p`
coefficients: their sum has coefficient `2`, which is nonzero. -/
theorem harcosCurvePolynomial_not_isSquare (p : ℕ) (hp : 1 < p)
    (htwo : (2 : K) ≠ 0) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    ¬ IsSquare (harcosCurvePolynomial p a b) := by
  rintro ⟨g, hg⟩
  have hc : (4 * a * b : K) ≠ 0 := by
    have hfour : (4 : K) ≠ 0 := by
      have := mul_ne_zero htwo htwo
      norm_num at this ⊢
      exact this
    exact mul_ne_zero (mul_ne_zero hfour ha) hb
  have hprod : (X ^ p - X - g) * (X ^ p - X + g) = C (4 * a * b) := by
    have he : (X ^ p - X : K[X]) ^ 2 - C (4 * a * b) = g * g := hg
    linear_combination he
  have hnz : (X ^ p - X - g) * (X ^ p - X + g) ≠ 0 := by
    rw [hprod]
    exact C_ne_zero.mpr hc
  have hd := congrArg natDegree hprod
  rw [natDegree_mul (mul_ne_zero_iff.mp hnz).1 (mul_ne_zero_iff.mp hnz).2,
    natDegree_C] at hd
  have hm := coeff_eq_zero_of_natDegree_lt
    (p := X ^ p - X - g) (n := p) (by omega)
  have hp' := coeff_eq_zero_of_natDegree_lt
    (p := X ^ p - X + g) (n := p) (by omega)
  have hp1 : 1 ≠ p := by omega
  simp [coeff_sub, coeff_add, coeff_X_pow, coeff_X, hp1] at hm hp'
  apply htwo
  linear_combination hm + hp'

theorem harcosCurvePolynomial_geometrically_not_isSquare
    (p : ℕ) (hp : 1 < p) (htwo : (2 : K) ≠ 0)
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    ¬ IsSquare ((harcosCurvePolynomial p a b).map
      (algebraMap K (AlgebraicClosure K))) := by
  have hi := (algebraMap K (AlgebraicClosure K)).injective
  have ht : (2 : AlgebraicClosure K) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero_iff _ hi).mpr htwo
  simpa [harcosCurvePolynomial, map_ofNat] using
    harcosCurvePolynomial_not_isSquare p hp ht
      (algebraMap K (AlgebraicClosure K) a) (algebraMap K (AlgebraicClosure K) b)
      ((map_ne_zero_iff _ hi).mpr ha) ((map_ne_zero_iff _ hi).mpr hb)

end Algebra

section FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The actual affine count in the last paragraph of Harcos, page 12. -/
def harcosCurvePointCount (p : ℕ) (a b : F) : ℕ :=
  (univ.filter fun xy : F × F =>
    xy.2 ^ 2 = (xy.1 ^ p - xy.1) ^ 2 - 4 * a * b).card

theorem harcosCurvePointCount_eq_stepanovPointCount (p : ℕ) (a b : F) :
    harcosCurvePointCount p a b = stepanovPointCount (harcosCurvePolynomial p a b) := by
  simp only [harcosCurvePointCount, stepanovPointCount, harcosCurvePolynomial_eval]

/-- Harcos's specialization, with all polynomial hypotheses discharged. -/
theorem harcos_curve_pointCount_bound (p : ℕ) [CharP F p]
    (hp : p.Prime) (hp2 : p ≠ 2) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hq : 12 * p < Fintype.card F) :
    |(harcosCurvePointCount p a b : ℝ) - Fintype.card F| <
      8 * p * ⌈Real.sqrt (Fintype.card F : ℝ)⌉₊ := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have ht : (2 : F) ≠ 0 := by
    exact_mod_cast CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_two hp2
  have hodd : Odd (Fintype.card F) := by
    apply Nat.odd_iff.mpr
    apply FiniteField.odd_card_of_char_ne_two
    simpa only [ringChar.eq F p] using hp2
  have hdeg := harcosCurvePolynomial_natDegree p (by omega) a b
  have h := stepanov_pointCount_bound_of_eval_zero_ne (harcosCurvePolynomial p a b)
    hodd (harcosCurvePolynomial_eval_zero_ne p (by omega) ht a b ha hb)
    (harcosCurvePolynomial_geometrically_not_isSquare p (by omega) ht a b ha hb)
    (by omega) (by omega)
  rw [← harcosCurvePointCount_eq_stepanovPointCount, hdeg] at h
  convert h using 1
  push_cast
  ring

/-- The source's `n ≥ 4` range is inside the range `q > 12p`. -/
theorem harcos_twelve_mul_lt_pow (p n : ℕ) (hp : 3 ≤ p) (hn : 4 ≤ n) :
    12 * p < p ^ n := by
  have h2 : 9 ≤ p ^ 2 := by nlinarith
  have h3 : 27 ≤ p ^ 3 := by nlinarith
  have h4 : 12 * p < p ^ 4 := by nlinarith
  exact h4.trans_le (pow_le_pow_right₀ (by omega) hn)

/-- In characteristic `p`, every finite field of size `p^n`, `n ≥ 4`,
satisfies the specialized estimate, with no assumed curve bound. -/
theorem harcos_curve_pointCount_bound_of_card_eq_pow (p n : ℕ) [CharP F p]
    (hp : p.Prime) (hp2 : p ≠ 2) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcard : Fintype.card F = p ^ n) (hn : 4 ≤ n) :
    |(harcosCurvePointCount p a b : ℝ) - (p : ℝ) ^ n| <
      8 * p * ⌈Real.sqrt ((p : ℝ) ^ n)⌉₊ := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq : 12 * p < Fintype.card F := by
    rw [hcard]
    exact harcos_twelve_mul_lt_pow p n hp3 hn
  simpa only [hcard, Nat.cast_pow] using
    harcos_curve_pointCount_bound p hp hp2 a b ha hb hq

end FiniteField

section Translation

variable {K : Type*} [Field K]


end Translation

section FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]


end FiniteField

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosTrace -/

/-!
# Harcos's trace-zero count

The last six counting lines of Corollary 3 on Harcos, page 8
(`pages/harcos-stepanov-08.png`), use the actual field trace and the
change of variables `y = 2at - (x^p - x)`.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Polynomial Finset

section Trace

variable (K L : Type*) [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]

/-- The relative Artin--Schreier linear map for finite fields. -/
def harcosArtinSchreier : L →ₗ[K] L :=
  (FiniteField.frobeniusAlgHom K L).toLinearMap - LinearMap.id

omit [Fintype L] in
@[simp] theorem harcosArtinSchreier_apply (x : L) :
    harcosArtinSchreier K L x = x ^ Fintype.card K - x := rfl

/-- Frobenius invariance of the actual algebra trace. -/
theorem harcos_trace_pow_card (x : L) :
    Algebra.trace K L (x ^ Fintype.card K) = Algebra.trace K L x :=
  Algebra.trace_eq_of_algEquiv (FiniteField.frobeniusAlgEquivOfAlgebraic K L) x

theorem harcos_trace_artinSchreier (x : L) :
    Algebra.trace K L (harcosArtinSchreier K L x) = 0 := by
  rw [harcosArtinSchreier_apply, map_sub, harcos_trace_pow_card, sub_self]

omit [Fintype L] in
/-- The fixed points of the relative Frobenius are exactly the embedded base field. -/
theorem harcos_pow_card_eq_self_iff (x : L) :
    x ^ Fintype.card K = x ↔ ∃ c : K, algebraMap K L c = x := by
  classical
  have hr := Polynomial.roots_map_of_injective_of_card_eq_natDegree
    (p := (X ^ Fintype.card K - X : K[X])) (algebraMap K L).injective
    (by rw [FiniteField.roots_X_pow_card_sub_X,
      Polynomial.natDegree_X_pow_sub_X (R := K) Fintype.one_lt_card]; rfl)
  have hn := Polynomial.X_pow_sub_X_ne_zero (R := L) (Fintype.one_lt_card (α := K))
  have hm : (X ^ Fintype.card K - X : L[X]).roots =
      (univ.val : Multiset K).map (algebraMap K L) := by
    simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      FiniteField.roots_X_pow_card_sub_X] using hr.symm
  rw [← sub_eq_zero, ← show
    (X ^ Fintype.card K - X : L[X]).IsRoot x ↔
      x ^ Fintype.card K - x = 0 by simp [Polynomial.IsRoot],
    ← Polynomial.mem_roots hn, hm]
  simp

omit [Fintype L] in
theorem harcos_artinSchreier_ker :
    (harcosArtinSchreier K L).ker = (Algebra.linearMap K L).range := by
  ext x
  simp only [LinearMap.mem_ker, harcosArtinSchreier_apply, sub_eq_zero,
    LinearMap.mem_range, Algebra.linearMap_apply, harcos_pow_card_eq_self_iff]

omit [Fintype L] in
theorem harcos_artinSchreier_ker_finrank :
    Module.finrank K (harcosArtinSchreier K L).ker = 1 := by
  rw [harcos_artinSchreier_ker,
    LinearMap.finrank_range_of_inj (algebraMap K L).injective]
  exact Module.finrank_self K

/-- Rank-nullity and nondegeneracy of the trace give additive Hilbert 90 here,
without assuming any trace-zero solvability statement. -/
theorem harcos_artinSchreier_range :
    (harcosArtinSchreier K L).range = (Algebra.trace K L).ker := by
  have hle : (harcosArtinSchreier K L).range ≤ (Algebra.trace K L).ker := by
    rintro _ ⟨x, rfl⟩
    exact harcos_trace_artinSchreier K L x
  apply Submodule.eq_of_le_of_finrank_eq hle
  have ha := LinearMap.finrank_range_add_finrank_ker (harcosArtinSchreier K L)
  have ht := LinearMap.finrank_range_add_finrank_ker (Algebra.trace K L)
  rw [harcos_artinSchreier_ker_finrank] at ha
  rw [LinearMap.range_eq_top.mpr (Algebra.trace_surjective K L)] at ht
  simp only [finrank_top, Module.finrank_self] at ht
  omega

theorem harcos_artinSchreier_exists_iff (c : L) :
    (∃ x : L, x ^ Fintype.card K - x = c) ↔ Algebra.trace K L c = 0 := by
  change c ∈ (harcosArtinSchreier K L).range ↔ c ∈ (Algebra.trace K L).ker
  rw [harcos_artinSchreier_range]

/-- Every nonempty Artin--Schreier fiber has exactly `#K` elements; the empty
fibers are exactly those with nonzero field trace. -/
theorem harcos_artinSchreier_fiber_card [DecidableEq L] [DecidableEq K] (c : L) :
    (univ.filter fun x : L => x ^ Fintype.card K - x = c).card =
      if Algebra.trace K L c = 0 then Fintype.card K else 0 := by
  classical
  change (univ.filter fun x : L => harcosArtinSchreier K L x = c).card = _
  by_cases hc : Algebra.trace K L c = 0
  · rw [if_pos hc]
    obtain ⟨r, hr⟩ := (harcos_artinSchreier_exists_iff K L c).mpr hc
    change harcosArtinSchreier K L r = c at hr
    have hcard : (univ.filter fun x : L => harcosArtinSchreier K L x = 0).card =
        Fintype.card K := by
      simpa only [harcos_artinSchreier_ker_finrank, pow_one,
        Fintype.card_subtype, LinearMap.mem_ker] using
        (Module.card_eq_pow_finrank (K := K) (V := (harcosArtinSchreier K L).ker))
    calc
      _ = (univ.filter fun x : L => harcosArtinSchreier K L x = 0).card := by
        refine card_nbij' (fun x : L => x - r) (fun x : L => x + r) ?_ ?_ ?_ ?_
        · intro x hx
          simp only [mem_coe, mem_filter, mem_univ, true_and] at hx ⊢
          rw [map_sub, hx, hr, sub_self]
        · intro x hx
          simp only [mem_coe, mem_filter, mem_univ, true_and] at hx ⊢
          rw [map_add, hx, hr, zero_add]
        · intro x _
          exact sub_add_cancel x r
        · intro x _
          exact add_sub_cancel_right x r
      _ = Fintype.card K := hcard
  · rw [if_neg hc]
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    exact hc ((harcos_artinSchreier_exists_iff K L c).mp ⟨x, hx⟩)

end Trace

section ChangeOfVariables

variable {F : Type*} [Field F]

theorem harcos_artinSchreier_eq_iff_quadratic (s a b t : F) (ht : t ≠ 0) :
    s = a * t + b / t ↔ a * t ^ 2 - s * t + b = 0 := by
  constructor
  · intro h
    have h' := (eq_div_iff ht).mp (show s - a * t = b / t by rw [h]; ring)
    linear_combination -h'
  · intro h
    have h' : (s - a * t) * t = b := by linear_combination -h
    have := (eq_div_iff ht).mpr h'
    linear_combination this

theorem harcos_square_iff_quadratic (htwo : (2 : F) ≠ 0)
    (s a b t : F) (ha : a ≠ 0) :
    (2 * a * t - s) ^ 2 = s ^ 2 - 4 * a * b ↔
      a * t ^ 2 - s * t + b = 0 := by
  have hfour : (4 : F) ≠ 0 := by
    have h := mul_ne_zero htwo htwo
    norm_num at h ⊢
    exact h
  constructor
  · intro h
    have h' : (4 * a) * (a * t ^ 2 - s * t + b) = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp h').resolve_left (mul_ne_zero hfour ha)
  · intro h
    linear_combination 4 * a * h

theorem harcos_quadratic_parameter_nonzero (s a b t : F) (hb : b ≠ 0)
    (h : a * t ^ 2 - s * t + b = 0) : t ≠ 0 := by
  intro ht
  apply hb
  simpa only [ht, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, zero_add] using h

/-- The explicit inverse substitution `t = (y+s)/(2a)`. -/
theorem harcos_curve_parameter_inverse (htwo : (2 : F) ≠ 0)
    (s a y : F) (ha : a ≠ 0) :
    2 * a * ((y + s) / (2 * a)) - s = y := by
  field_simp [htwo, ha]
  ring

/-- Harcos's change of variables, with nonzero `t` represented by a unit.
Its forward map is exactly `(x,t) ↦ (x,2at-(x^p-x))`; the surjectivity proof
constructs the inverse parameter `(y+(x^p-x))/(2a)`. -/
def harcosCurveArtinSchreierEquiv (p : ℕ) (htwo : (2 : F) ≠ 0)
    (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    {xt : F × Fˣ // xt.1 ^ p - xt.1 = a * (xt.2 : F) + b / (xt.2 : F)} ≃
      {xy : F × F // xy.2 ^ 2 = (xy.1 ^ p - xy.1) ^ 2 - 4 * a * b} :=
  Equiv.ofBijective
    (fun xt => ⟨(xt.1.1, 2 * a * (xt.1.2 : F) - (xt.1.1 ^ p - xt.1.1)),
      (harcos_square_iff_quadratic htwo _ a b _ ha).mpr
        ((harcos_artinSchreier_eq_iff_quadratic _ a b _ (Units.ne_zero _)).mp xt.2)⟩)
    (by
      constructor
      · intro xt xu h
        apply Subtype.ext
        have hx := congrArg (fun z => z.1.1) h
        have hy := congrArg (fun z => z.1.2) h
        dsimp only at hx hy
        apply Prod.ext hx
        apply Units.val_injective
        rw [hx] at hy
        have hmul : (2 * a) * (xt.1.2 : F) = (2 * a) * (xu.1.2 : F) := by
          linear_combination hy
        exact mul_left_cancel₀ (mul_ne_zero htwo ha) hmul
      · intro xy
        let s := xy.1.1 ^ p - xy.1.1
        let t := (xy.1.2 + s) / (2 * a)
        have hinv : 2 * a * t - s = xy.1.2 :=
          harcos_curve_parameter_inverse htwo s a xy.1.2 ha
        have hquad : a * t ^ 2 - s * t + b = 0 := by
          apply (harcos_square_iff_quadratic htwo s a b t ha).mp
          rw [hinv]
          exact xy.2
        have ht := harcos_quadratic_parameter_nonzero s a b t hb hquad
        refine ⟨⟨(xy.1.1, Units.mk0 t ht), ?_⟩, ?_⟩
        · exact (harcos_artinSchreier_eq_iff_quadratic s a b t ht).mpr hquad
        · apply Subtype.ext
          exact Prod.ext rfl hinv)


end ChangeOfVariables

section Counts

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem harcosCurvePointCount_eq_artinSchreier_pairCount
    (p : ℕ) (htwo : (2 : F) ≠ 0) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    harcosCurvePointCount p a b =
      (univ.filter fun xt : F × Fˣ =>
        xt.1 ^ p - xt.1 = a * (xt.2 : F) + b / (xt.2 : F)).card := by
  classical
  simpa only [Fintype.card_subtype, harcosCurvePointCount] using
    (Fintype.card_congr (harcosCurveArtinSchreierEquiv p htwo a b ha hb)).symm

/-- The relative finite-field version of Harcos's trace-zero counting identity. -/
theorem harcosCurvePointCount_eq_card_mul_traceZero
    (K : Type*) [Field K] [Fintype K] [DecidableEq K] [Algebra K F]
    (htwo : (2 : F) ≠ 0) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    harcosCurvePointCount (Fintype.card K) a b =
      Fintype.card K *
        (univ.filter fun t : Fˣ =>
          Algebra.trace K F (a * (t : F) + b / (t : F)) = 0).card := by
  classical
  rw [harcosCurvePointCount_eq_artinSchreier_pairCount _ htwo a b ha hb]
  calc
    _ = ∑ t : Fˣ, (univ.filter fun x : F =>
        x ^ Fintype.card K - x = a * (t : F) + b / (t : F)).card := by
      simp only [card_filter, Fintype.sum_prod_type]
      exact sum_comm
    _ = ∑ t : Fˣ, if Algebra.trace K F (a * (t : F) + b / (t : F)) = 0
        then Fintype.card K else 0 := by
      apply sum_congr rfl
      intro t _
      exact harcos_artinSchreier_fiber_card K F _
    _ = _ := by
      rw [card_filter, mul_sum]
      apply sum_congr rfl
      intro t _
      split_ifs <;> simp


/-- The last six counting lines of Harcos, Corollary 3, page 8. -/
theorem harcosCurvePointCount_eq_prime_mul_traceZero (p : ℕ) [Fact p.Prime]
    [CharP F p] [Algebra (ZMod p) F] (hp2 : p ≠ 2)
    (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    harcosCurvePointCount p a b =
      p * (univ.filter fun t : Fˣ =>
        Algebra.trace (ZMod p) F (a * (t : F) + b * (t : F)⁻¹) = 0).card := by
  have htwo : (2 : F) ≠ 0 := by
    exact_mod_cast CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_two hp2
  simpa only [ZMod.card, div_eq_mul_inv] using
    harcosCurvePointCount_eq_card_mul_traceZero (ZMod p) htwo a b ha hb

end Counts

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosCharacter -/
/-!
# Harcos's extension-field character sums

The coefficients belong to the fixed prime field, not to a varying extension.
The trace is `Algebra.trace`; its Frobenius formula and additive-character
orthogonality identify the sum over frequencies with the actual affine count.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

variable (p : ℕ) [Fact p.Prime]
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F]

def harcosTraceKloosterman (a b m : ZMod p) : ℂ :=
  ∑ t : Fˣ, ZMod.stdAddChar (m * Algebra.trace (ZMod p) F
    (algebraMap (ZMod p) F a * (t : F) +
      algebraMap (ZMod p) F b * (t : F)⁻¹))


theorem harcosTraceKloosterman_zero (a b : ZMod p) :
    harcosTraceKloosterman p F a b 0 = Fintype.card Fˣ := by
  simp [harcosTraceKloosterman]

theorem harcosTraceKloosterman_frequency_sum (a b : ZMod p) :
    ∑ m : ZMod p, harcosTraceKloosterman p F a b m =
      (p : ℂ) * ((univ.filter fun t : Fˣ =>
        Algebra.trace (ZMod p) F
          (algebraMap (ZMod p) F a * (t : F) +
            algebraMap (ZMod p) F b * (t : F)⁻¹) = 0).card : ℂ) := by
  unfold harcosTraceKloosterman
  rw [sum_comm]
  simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar p), ZMod.card]
  rw [card_filter, Nat.cast_sum, mul_sum]
  apply sum_congr rfl
  intro t _
  split_ifs <;> simp

theorem harcosTraceKloosterman_sum_eq_curve [CharP F p]
    (hp2 : p ≠ 2) (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∑ m : ZMod p, harcosTraceKloosterman p F a b m =
      (harcosCurvePointCount p (algebraMap (ZMod p) F a)
        (algebraMap (ZMod p) F b) : ℂ) := by
  rw [harcosTraceKloosterman_frequency_sum,
    harcosCurvePointCount_eq_prime_mul_traceZero p hp2 _ _
      (fun h => ha ((algebraMap (ZMod p) F).injective (h.trans (map_zero _).symm)))
      (fun h => hb ((algebraMap (ZMod p) F).injective (h.trans (map_zero _).symm))),
    Nat.cast_mul]

theorem harcosTraceKloosterman_nonzero_sum_eq_curve [CharP F p]
    (hp2 : p ≠ 2) (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∑ m ∈ (univ : Finset (ZMod p)).erase 0, harcosTraceKloosterman p F a b m =
      (harcosCurvePointCount p (algebraMap (ZMod p) F a)
        (algebraMap (ZMod p) F b) : ℂ) - (Fintype.card F : ℂ) + 1 := by
  have h := sum_erase_add (univ : Finset (ZMod p))
    (fun m => harcosTraceKloosterman p F a b m) (mem_univ 0)
  rw [harcosTraceKloosterman_sum_eq_curve p F hp2 a b ha hb,
    harcosTraceKloosterman_zero, Fintype.card_units,
    Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Fintype.card F))),
    Nat.cast_one] at h
  linear_combination h


theorem harcosTraceKloosterman_nonzero_sum_bound [CharP F p]
    (hp2 : p ≠ 2) (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0)
    (n : ℕ) (hcard : Fintype.card F = p ^ n) (hn : 4 ≤ n) :
    ‖∑ m ∈ (univ : Finset (ZMod p)).erase 0,
      harcosTraceKloosterman p F a b m‖ ≤
        8 * (p : ℝ) * ⌈Real.sqrt ((p : ℝ) ^ n)⌉₊ + 1 := by
  have ha' : algebraMap (ZMod p) F a ≠ 0 :=
    fun h => ha ((algebraMap (ZMod p) F).injective (h.trans (map_zero _).symm))
  have hb' : algebraMap (ZMod p) F b ≠ 0 :=
    fun h => hb ((algebraMap (ZMod p) F).injective (h.trans (map_zero _).symm))
  have h := harcos_curve_pointCount_bound_of_card_eq_pow p n
    (Fact.out : p.Prime) hp2 _ _ ha' hb' hcard hn
  rw [harcosTraceKloosterman_nonzero_sum_eq_curve p F hp2 a b ha hb, hcard,
    Nat.cast_pow]
  calc
    _ ≤ ‖(harcosCurvePointCount p (algebraMap (ZMod p) F a)
      (algebraMap (ZMod p) F b) : ℂ) - (p : ℂ) ^ n‖ + ‖(1 : ℂ)‖ :=
        norm_add_le _ _
    _ = |(harcosCurvePointCount p (algebraMap (ZMod p) F a)
      (algebraMap (ZMod p) F b) : ℝ) - (p : ℝ) ^ n| + 1 := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast p,
          ← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, norm_one]
    _ ≤ _ := by linarith

def harcosExtensionKloosterman (a b m : ZMod p) (n : ℕ) : ℂ := by
  letI := Fintype.ofFinite (GaloisField p n)
  letI := Classical.decEq (GaloisField p n)
  exact harcosTraceKloosterman p (GaloisField p n) a b m


theorem harcosExtensionKloosterman_nonzero_sum_bound
    (hp2 : p ≠ 2) (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0)
    (n : ℕ) (hn : 4 ≤ n) :
    ‖∑ m ∈ (univ : Finset (ZMod p)).erase 0,
      harcosExtensionKloosterman p a b m n‖ ≤
        8 * (p : ℝ) * ⌈Real.sqrt ((p : ℝ) ^ n)⌉₊ + 1 := by
  let := Fintype.ofFinite (GaloisField p n)
  let := Classical.decEq (GaloisField p n)
  apply harcosTraceKloosterman_nonzero_sum_bound p (GaloisField p n) hp2 a b ha hb n
  · simpa only [Nat.card_eq_fintype_card] using GaloisField.card p n (by omega)
  · exact hn

/-- A single constant for all extension degrees. This bounds the sum over
nonzero frequencies, not any individual Kloosterman sum. -/
theorem harcosExtensionKloosterman_total_growth
    (hp2 : p ≠ 2) (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0)
    (n : ℕ) (hn : 4 ≤ n) :
    ‖∑ m ∈ (univ : Finset (ZMod p)).erase 0,
      harcosExtensionKloosterman p a b m n‖ ≤
        (16 * (p : ℝ) + 1) * Real.sqrt (p : ℝ) ^ n := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hroot : 1 ≤ Real.sqrt (p : ℝ) ^ n :=
    one_le_pow₀ (Real.one_le_sqrt.mpr hp)
  have hsqrt : Real.sqrt ((p : ℝ) ^ n) = Real.sqrt (p : ℝ) ^ n := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity), ← pow_mul, mul_comm n 2, pow_mul,
      Real.sq_sqrt (by positivity)]
  have hceil := Nat.ceil_lt_add_one (Real.sqrt_nonneg ((p : ℝ) ^ n))
  rw [hsqrt] at hceil
  have h := harcosExtensionKloosterman_nonzero_sum_bound p hp2 a b ha hb n hn
  rw [hsqrt] at h
  have hpay : (⌈Real.sqrt (p : ℝ) ^ n⌉₊ : ℝ) ≤ 2 * Real.sqrt (p : ℝ) ^ n := by
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hpay (show 0 ≤ 8 * (p : ℝ) by positivity)]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosEta -/

/-!
# Harcos's polynomial character

The coefficient formula in Harcos, §3, Definition 4 and Lemma 6
(`pages/harcos-lpolynomial-05.png`). `nextCoeff` is zero on constants;
this includes the degree-zero endpoint in the multiplicativity statement.
-/

noncomputable section

open Finset Polynomial

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

variable {p : ℕ} [Fact p.Prime]

/-- The actual polynomial character, with zero at polynomials divisible by `X`. -/
def harcosEta (a b : ZMod p) (f : (ZMod p)[X]) : ℂ :=
  if f.coeff 0 = 0 then 0 else
    ZMod.stdAddChar (-a * (f.nextCoeff / f.leadingCoeff) -
      b * (f.coeff 1 / f.coeff 0))

theorem harcosEta_zero (a b : ZMod p) : harcosEta a b 0 = 0 := by
  simp [harcosEta]

theorem harcosEta_C (a b c : ZMod p) :
    harcosEta a b (C c) = if c = 0 then 0 else 1 := by
  simp [harcosEta, nextCoeff_C_eq_zero]

theorem harcosEta_one (a b : ZMod p) : harcosEta a b 1 = 1 := by
  simpa using harcosEta_C a b 1


private theorem nextCoeff_div_leadingCoeff_mul (f g : (ZMod p)[X])
    (hf : f ≠ 0) (hg : g ≠ 0) :
    (f * g).nextCoeff / (f * g).leadingCoeff =
      f.nextCoeff / f.leadingCoeff + g.nextCoeff / g.leadingCoeff := by
  have h := (monic_mul_leadingCoeff_inv hf).nextCoeff_mul
    (monic_mul_leadingCoeff_inv hg)
  rw [show (f * C f.leadingCoeff⁻¹) * (g * C g.leadingCoeff⁻¹) =
      (f * g) * C (f.leadingCoeff⁻¹ * g.leadingCoeff⁻¹) by
        rw [map_mul]; ring] at h
  simpa only [nextCoeff_mul_C, leadingCoeff_mul, mul_inv_rev, div_eq_mul_inv,
    mul_comm g.leadingCoeff⁻¹ f.leadingCoeff⁻¹] using h

theorem harcosEta_mul (a b : ZMod p) (f g : (ZMod p)[X]) :
    harcosEta a b (f * g) = harcosEta a b f * harcosEta a b g := by
  by_cases hf : f.coeff 0 = 0
  · simp [harcosEta, mul_coeff_zero, hf]
  by_cases hg : g.coeff 0 = 0
  · simp [harcosEta, mul_coeff_zero, hg]
  have hf' : f ≠ 0 := by intro h; apply hf; simp [h]
  have hg' : g ≠ 0 := by intro h; apply hg; simp [h]
  have hc : (f * g).coeff 1 / (f * g).coeff 0 =
      f.coeff 1 / f.coeff 0 + g.coeff 1 / g.coeff 0 := by
    rw [mul_coeff_one, mul_coeff_zero]
    field_simp
    ring
  rw [mul_coeff_zero] at hc
  simp only [harcosEta, mul_coeff_zero, mul_ne_zero hf hg, hf, hg, if_false]
  rw [nextCoeff_div_leadingCoeff_mul f g hf' hg', hc,
    ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- The multiplicative source object for a later Euler-product construction. -/
def harcosEtaHom (a b : ZMod p) : (ZMod p)[X] →*₀ ℂ where
  toFun := harcosEta a b
  map_zero' := harcosEta_zero a b
  map_one' := harcosEta_one a b
  map_mul' := harcosEta_mul a b

theorem harcosEta_X_add_C (a b c : ZMod p) :
    harcosEta a b (X + C c) =
      if c = 0 then 0 else ZMod.stdAddChar (-a * c - b * c⁻¹) := by
  simp [harcosEta, nextCoeff_X_add_C]

theorem harcosEta_X_sub_C (a b t : ZMod p) :
    harcosEta a b (X - C t) =
      if t = 0 then 0 else ZMod.stdAddChar (a * t + b * t⁻¹) := by
  simpa [sub_eq_add_neg] using harcosEta_X_add_C a b (-t)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosLPolynomial -/

/-!
# Actual coefficient sums for Harcos's L-polynomial

The monic polynomials are parametrized by all their lower coefficients, not
by an assumed list of L-function coefficients. Source: Harcos, §3, Theorem 5,
`pages/harcos-lpolynomial-06.png`.
-/

noncomputable section

open Finset Polynomial

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

variable {p : ℕ} [Fact p.Prime]

/-- A monic polynomial with the given vector of lower coefficients. -/
def harcosMonic (n : ℕ) (v : Fin n → ZMod p) : (ZMod p)[X] :=
  X ^ n + Polynomial.ofFn n v

theorem harcosMonic_monic (n : ℕ) (v : Fin n → ZMod p) :
    (harcosMonic n v).Monic := by
  apply (monic_X_pow n).add_of_left
  simpa using Polynomial.ofFn_degree_lt v

theorem harcosMonic_natDegree (n : ℕ) (v : Fin n → ZMod p) :
    (harcosMonic n v).natDegree = n := by
  unfold harcosMonic
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  simpa using Polynomial.ofFn_degree_lt v

theorem harcosMonic_coeff_lt (n : ℕ) (v : Fin n → ZMod p) (i : ℕ)
    (hi : i < n) : (harcosMonic n v).coeff i = v ⟨i, hi⟩ := by
  simp [harcosMonic, Polynomial.ofFn_coeff_eq_val_of_lt v hi, ne_of_lt hi]

theorem harcosMonic_unique (n : ℕ) (f : (ZMod p)[X])
    (hm : f.Monic) (hd : f.natDegree = n) :
    ∃! v : Fin n → ZMod p, harcosMonic n v = f := by
  refine ⟨fun i ↦ f.coeff i, ?_, ?_⟩
  · ext i
    rcases lt_trichotomy i n with hi | hi | hi
    · exact harcosMonic_coeff_lt n _ i hi
    · subst i
      have he : (harcosMonic n (fun i ↦ f.coeff i)).coeff n = 1 := by
        simpa only [Polynomial.leadingCoeff, harcosMonic_natDegree] using
          (harcosMonic_monic n (fun i ↦ f.coeff i)).leadingCoeff
      rw [he, ← hd, coeff_natDegree, hm.leadingCoeff]
    · rw [coeff_eq_zero_of_natDegree_lt (by rwa [harcosMonic_natDegree]),
        coeff_eq_zero_of_natDegree_lt (by rwa [hd])]
  · intro v hv
    funext i
    have h := congrArg (fun g : (ZMod p)[X] ↦ g.coeff i) hv
    simpa only [harcosMonic_coeff_lt n v i i.isLt] using h

theorem harcosMonic_injective (n : ℕ) :
    Function.Injective (harcosMonic (p := p) n) := by
  intro v w h
  funext i
  have hc := congrArg (fun f : (ZMod p)[X] ↦ f.coeff i) h
  simpa only [harcosMonic_coeff_lt n v i i.isLt,
    harcosMonic_coeff_lt n w i i.isLt] using hc

/-- Exactly the finite set of monic polynomials of degree `n`. -/
def harcosMonicPolynomials (p n : ℕ) [Fact p.Prime] : Finset (ZMod p)[X] :=
  Finset.univ.image (harcosMonic n)

theorem mem_harcosMonicPolynomials (n : ℕ) (f : (ZMod p)[X]) :
    f ∈ harcosMonicPolynomials p n ↔ f.Monic ∧ f.natDegree = n := by
  classical
  constructor
  · intro hf
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hf
    exact ⟨harcosMonic_monic n v, harcosMonic_natDegree n v⟩
  · rintro ⟨hm, hd⟩
    obtain ⟨v, hv, _⟩ := harcosMonic_unique n f hm hd
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, hv⟩


theorem harcosMonic_zero (v : Fin 0 → ZMod p) : harcosMonic 0 v = 1 := by
  simp [harcosMonic]

theorem harcosMonic_one (v : Fin 1 → ZMod p) :
    harcosMonic 1 v = X + C (v 0) := by
  unfold harcosMonic
  rw [pow_one]
  congr 1
  ext i
  cases i with
  | zero => simp [Polynomial.ofFn_coeff_eq_val_of_lt]
  | succ i =>
    simp [Polynomial.ofFn_coeff_eq_zero_of_ge v (by omega : 1 ≤ i + 1)]

/-- The genuine finite monic-degree coefficient sum of the polynomial character. -/
def harcosCoefficient (a b : ZMod p) (n : ℕ) : ℂ :=
  ∑ v : Fin n → ZMod p, harcosEta a b (harcosMonic n v)

theorem harcosCoefficient_eq_sum_monic (a b : ZMod p) (n : ℕ) :
    harcosCoefficient a b n =
      ∑ f ∈ harcosMonicPolynomials p n, harcosEta a b f := by
  classical
  rw [harcosMonicPolynomials, Finset.sum_image]
  · rfl
  · intro v _ w _ h
    exact harcosMonic_injective n h


theorem harcosCoefficient_zero (a b : ZMod p) : harcosCoefficient a b 0 = 1 := by
  simp [harcosCoefficient, harcosMonic_zero, harcosEta_one]

theorem harcosCoefficient_one (a : ZMod p) (b : ℤ) :
    harcosCoefficient a (b : ZMod p) 1 = completeKloosterman p a b := by
  classical
  rw [harcosCoefficient, completeKloosterman_eq]
  calc
    ∑ v : Fin 1 → ZMod p, harcosEta a (b : ZMod p) (harcosMonic 1 v) =
        ∑ t : ZMod p, harcosEta a (b : ZMod p) (X - C t) := by
      apply Fintype.sum_bijective (fun v : Fin 1 → ZMod p ↦ -v 0)
      · constructor
        · intro v w h
          funext i
          have hi : i = 0 := Subsingleton.elim _ _
          simpa only [hi] using neg_injective h
        · intro t
          exact ⟨fun _ ↦ -t, neg_neg t⟩
      · intro v
        simp [harcosMonic_one, sub_eq_add_neg]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      rw [harcosEta_X_sub_C]
      by_cases ht : t = 0 <;> simp [ht, isUnit_iff_ne_zero]

theorem harcosEta_monic_coefficients (a b : ZMod p) (n : ℕ)
    (hn : 2 ≤ n) (v : Fin n → ZMod p) :
    harcosEta a b (harcosMonic n v) =
      if v ⟨0, by omega⟩ = 0 then 0 else
        ZMod.stdAddChar (-a * v ⟨n - 1, by omega⟩ -
          b * (v ⟨1, by omega⟩ / v ⟨0, by omega⟩)) := by
  have hn' : 0 < (harcosMonic n v).natDegree := by
    rw [harcosMonic_natDegree]; omega
  simp only [harcosEta, nextCoeff_of_natDegree_pos hn', harcosMonic_natDegree,
    (harcosMonic_monic n v).leadingCoeff, div_one,
    harcosMonic_coeff_lt n v 0 (by omega),
    harcosMonic_coeff_lt n v 1 (by omega),
    harcosMonic_coeff_lt n v (n - 1) (by omega)]

private theorem sum_snoc (n : ℕ) (f : (Fin (n + 1) → ZMod p) → ℂ) :
    ∑ v, f v = ∑ t : ZMod p, ∑ w : Fin n → ZMod p, f (Fin.snoc w t) := by
  calc
    _ = ∑ z : ZMod p × (Fin n → ZMod p), f (Fin.snoc z.2 z.1) :=
      Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (n + 1) ↦ ZMod p)).symm
        _ _ (fun _ ↦ by simp [Fin.snocEquiv])
    _ = _ := Fintype.sum_prod_type _

private theorem sum_char_mul (c : ZMod p) :
    ∑ t : ZMod p, ZMod.stdAddChar (c * t) = if c = 0 then (p : ℂ) else 0 := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [if_neg hc]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p hc)

theorem harcosCoefficient_ge_three (a b : ZMod p) (ha : a ≠ 0)
    (n : ℕ) (hn : 3 ≤ n) : harcosCoefficient a b n = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 3 + m = (m + 2) + 1 by omega, harcosCoefficient, sum_snoc, sum_comm]
  apply Finset.sum_eq_zero
  intro w _
  have he (t : ZMod p) :
      harcosEta a b (harcosMonic (m + 2 + 1) (Fin.snoc w t)) =
        if w ⟨0, by omega⟩ = 0 then 0 else
          ZMod.stdAddChar (-a * t) *
            ZMod.stdAddChar (-b * (w ⟨1, by omega⟩ / w ⟨0, by omega⟩)) := by
    rw [harcosEta_monic_coefficients a b _ (by omega)]
    simp [Fin.snoc, Fin.castLT, sub_eq_add_neg, AddChar.map_add_eq_mul]
  simp_rw [he]
  by_cases hw : w ⟨0, by omega⟩ = 0
  · simp only [hw, if_true, sum_const_zero]
  · simp only [hw, if_false, ← Finset.sum_mul, sum_char_mul, neg_ne_zero.mpr ha,
      if_false, zero_mul]

private theorem sum_fin_one (f : ZMod p → ℂ) :
    ∑ v : Fin 1 → ZMod p, f (v 0) = ∑ c : ZMod p, f c := by
  refine Fintype.sum_bijective (fun v : Fin 1 → ZMod p ↦ v 0) ?_ _ _ (fun _ ↦ rfl)
  constructor
  · intro v w h
    funext i
    simpa only [show i = 0 from Subsingleton.elim _ _] using h
  · intro c
    exact ⟨fun _ ↦ c, rfl⟩

theorem harcosCoefficient_two_sum (a b : ZMod p) :
    harcosCoefficient a b 2 =
      ∑ c : ZMod p, if c = 0 then 0 else
        ∑ t : ZMod p, ZMod.stdAddChar ((-a - b / c) * t) := by
  rw [harcosCoefficient, show 2 = 1 + 1 from rfl, sum_snoc]
  have he (t : ZMod p) (w : Fin 1 → ZMod p) :
      harcosEta a b (harcosMonic 2 (Fin.snoc w t)) =
        if w 0 = 0 then 0 else ZMod.stdAddChar ((-a - b / w 0) * t) := by
    rw [harcosEta_monic_coefficients a b 2 (by omega)]
    simp only [Fin.snoc, Fin.castLT, Fin.val_mk]
    simp
    congr 2
    ring
  simp_rw [he]
  conv_lhs =>
    arg 2
    ext t
    rw [sum_fin_one (fun c ↦ if c = 0 then 0 else
      ZMod.stdAddChar ((-a - b / c) * t))]
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  by_cases hc : c = 0 <;> simp [hc]

theorem harcosCoefficient_two (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) :
    harcosCoefficient a b 2 = (p : ℂ) := by
  classical
  rw [harcosCoefficient_two_sum]
  simp_rw [sum_char_mul]
  have hroot : -b / a ≠ 0 := div_ne_zero (neg_ne_zero.mpr hb) ha
  have hz (c : ZMod p) (hc : c ≠ 0) : -a - b / c = 0 ↔ c = -b / a := by
    field_simp
    constructor <;> intro h <;> linear_combination -h
  rw [Finset.sum_eq_single (-b / a)]
  · rw [if_neg hroot, if_pos ((hz _ hroot).2 rfl)]
  · intro c _ hc
    by_cases hc0 : c = 0
    · simp [hc0]
    · rw [if_neg hc0, if_neg (fun h ↦ hc ((hz c hc0).1 h))]
  · simp

/-- The formal generating series, before any coefficient evaluation. -/
def harcosLSeries (a b : ZMod p) : PowerSeries ℂ :=
  PowerSeries.mk (harcosCoefficient a b)

/-- The polynomial assembled from the actual degree-zero, one, and two sums. -/
def harcosLPolynomial (a b : ZMod p) : ℂ[X] :=
  ∑ n ∈ Finset.range 3, Polynomial.monomial n (harcosCoefficient a b n)

theorem harcosLPolynomial_coeff (a b : ZMod p) (ha : a ≠ 0) (n : ℕ) :
    (harcosLPolynomial a b).coeff n = harcosCoefficient a b n := by
  classical
  simp only [harcosLPolynomial, finsetSum_coeff, coeff_monomial, Finsupp.single_apply]
  by_cases hn : n < 3
  · simp [hn]
  · rw [harcosCoefficient_ge_three a b ha n (by omega)]
    apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg (by have := Finset.mem_range.mp hi; omega)]


theorem harcosLSeries_eq_polynomial (a b : ZMod p) (ha : a ≠ 0) :
    harcosLSeries a b = (harcosLPolynomial a b : PowerSeries ℂ) := by
  ext n
  simp [harcosLSeries, harcosLPolynomial_coeff a b ha]


theorem harcosLPolynomial_eq_coefficients (a b : ZMod p) :
    harcosLPolynomial a b =
      1 + C (harcosCoefficient a b 1) * X + C (harcosCoefficient a b 2) * X ^ 2 := by
  simp [harcosLPolynomial, Finset.sum_range_succ, harcosCoefficient_zero,
    ← C_mul_X_pow_eq_monomial]

/-- The first reciprocal root, constructed from the actual coefficient sums. -/
def harcosReciprocalRootPlus (a b : ZMod p) : ℂ :=
  (-harcosCoefficient a b 1 +
    Complex.sqrt ((harcosCoefficient a b 1) ^ 2 - 4 * harcosCoefficient a b 2)) / 2

/-- The second reciprocal root; the two choices may coincide. -/
def harcosReciprocalRootMinus (a b : ZMod p) : ℂ :=
  (-harcosCoefficient a b 1 -
    Complex.sqrt ((harcosCoefficient a b 1) ^ 2 - 4 * harcosCoefficient a b 2)) / 2

theorem harcosReciprocalRoots_add (a b : ZMod p) :
    harcosReciprocalRootPlus a b + harcosReciprocalRootMinus a b =
      -harcosCoefficient a b 1 := by
  unfold harcosReciprocalRootPlus harcosReciprocalRootMinus
  ring

theorem harcosReciprocalRoots_mul (a b : ZMod p) :
    harcosReciprocalRootPlus a b * harcosReciprocalRootMinus a b =
      harcosCoefficient a b 2 := by
  have hs : Complex.sqrt ((harcosCoefficient a b 1) ^ 2 -
      4 * harcosCoefficient a b 2) ^ 2 =
        (harcosCoefficient a b 1) ^ 2 - 4 * harcosCoefficient a b 2 := by
    exact Complex.cpow_nat_inv_pow _ (by norm_num : (2 : ℕ) ≠ 0)
  unfold harcosReciprocalRootPlus harcosReciprocalRootMinus
  linear_combination -hs / 4

/-- Factorization of the polynomial obtained from the monic-degree sums. -/
theorem harcosLPolynomial_factorization (a b : ZMod p) :
    harcosLPolynomial a b =
      (1 - C (harcosReciprocalRootPlus a b) * X) *
        (1 - C (harcosReciprocalRootMinus a b) * X) := by
  rw [harcosLPolynomial_eq_coefficients, ← harcosReciprocalRoots_mul,
    show harcosCoefficient a b 1 =
      -(harcosReciprocalRootPlus a b + harcosReciprocalRootMinus a b) by
        rw [harcosReciprocalRoots_add, neg_neg],
    map_neg, map_add, map_mul]
  ring

/-- The root factorization is an identity of the actual coefficient generating series. -/
theorem harcosLSeries_factorization (a b : ZMod p) (ha : a ≠ 0) :
    harcosLSeries a b =
      (1 - PowerSeries.C (harcosReciprocalRootPlus a b) * PowerSeries.X) *
        (1 - PowerSeries.C (harcosReciprocalRootMinus a b) * PowerSeries.X) := by
  rw [harcosLSeries_eq_polynomial a b ha, harcosLPolynomial_factorization]
  simp


theorem harcosReciprocalRoots_mul_prime (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) :
    harcosReciprocalRootPlus a b * harcosReciprocalRootMinus a b = (p : ℂ) := by
  rw [harcosReciprocalRoots_mul, harcosCoefficient_two a b ha hb]


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosEuler -/

/-!
# Finite Euler coefficient identities for actual monic polynomials

This is the algebraic, coefficientwise version of the Euler-product argument
in Harcos, §3, Lemma 7 and Theorem 6 (`pages/harcos-lpolynomial-05.png`–`07.png`).
The multiplicities below are those of the actual polynomial factorization.
-/

noncomputable section

open Finset Polynomial UniqueFactorizationMonoid

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

variable {p : ℕ} [Fact p.Prime]

/-- The coefficient obtained by summing a multiplicative weight over actual monics. -/
def harcosEulerCoefficient (η : (ZMod p)[X] →* ℂ) (n : ℕ) : ℂ :=
  ∑ f ∈ harcosMonicPolynomials p n, η f

/-- A coefficient with one marked occurrence of an irreducible factor. -/
def harcosEulerMarked (η : (ZMod p)[X] →* ℂ) (k : (ZMod p)[X]) (n : ℕ) : ℂ :=
  ∑ f ∈ harcosMonicPolynomials p n, ((normalizedFactors f).count k : ℂ) * η f

/-- Every monic irreducible of degree at most the cutoff, with no duplicates. -/
def harcosEulerPrimes (p n : ℕ) [Fact p.Prime] : Finset (ZMod p)[X] := by
  classical
  exact (range (n + 1)).biUnion fun d ↦
    (harcosMonicPolynomials p d).filter Irreducible

theorem mem_harcosEulerPrimes (n : ℕ) (k : (ZMod p)[X]) :
    k ∈ harcosEulerPrimes p n ↔ k.Monic ∧ Irreducible k ∧ k.natDegree ≤ n := by
  classical
  simp only [harcosEulerPrimes, mem_biUnion, mem_range, mem_filter,
    mem_harcosMonicPolynomials]
  constructor
  · rintro ⟨d, hd, ⟨hm, he⟩, hi⟩
    exact ⟨hm, hi, by omega⟩
  · rintro ⟨hm, hi, hd⟩
    exact ⟨k.natDegree, by omega, ⟨hm, rfl⟩, hi⟩

private theorem euler_count_eq_zero_of_not_dvd (k f : (ZMod p)[X]) (h : ¬ k ∣ f) :
    (normalizedFactors f).count k = 0 := by
  classical
  apply Multiset.count_eq_zero.mpr
  intro hm
  exact h (dvd_of_mem_normalizedFactors hm)

private theorem euler_count_mul (k f : (ZMod p)[X]) (hk : k.Monic)
    (hi : Irreducible k) (hf : f.Monic) :
    (normalizedFactors (k * f)).count k = 1 + (normalizedFactors f).count k := by
  classical
  rw [normalizedFactors_mul hk.ne_zero hf.ne_zero,
    normalizedFactors_irreducible hi, hk.normalize_eq_self, Multiset.count_add]
  simp

theorem harcosEulerMarked_eq_zero (η : (ZMod p)[X] →* ℂ)
    (k : (ZMod p)[X]) (n : ℕ) (hn : n < k.natDegree) :
    harcosEulerMarked η k n = 0 := by
  classical
  apply sum_eq_zero
  intro f hf
  obtain ⟨hm, hd⟩ := (mem_harcosMonicPolynomials n f).mp hf
  have hnd : ¬ k ∣ f := by
    intro h
    have := natDegree_le_of_dvd h hm.ne_zero
    omega
  simp [euler_count_eq_zero_of_not_dvd k f hnd]

theorem harcosEulerMarked_add_degree (η : (ZMod p)[X] →* ℂ)
    (k : (ZMod p)[X]) (hk : k.Monic) (hi : Irreducible k) (n : ℕ) :
    harcosEulerMarked η k (k.natDegree + n) =
      η k * (harcosEulerCoefficient η n + harcosEulerMarked η k n) := by
  classical
  unfold harcosEulerMarked harcosEulerCoefficient
  rw [← sum_add_distrib, mul_sum]
  have hfilter :
      (∑ f ∈ harcosMonicPolynomials p (k.natDegree + n),
          ((normalizedFactors f).count k : ℂ) * η f) =
        ∑ f ∈ (harcosMonicPolynomials p (k.natDegree + n)).filter (k ∣ ·),
          ((normalizedFactors f).count k : ℂ) * η f := by
    symm
    apply sum_subset (filter_subset _ _)
    intro f hf hnf
    have hnd : ¬ k ∣ f := by simpa [hf] using hnf
    simp [euler_count_eq_zero_of_not_dvd k f hnd]
  rw [hfilter]
  symm
  apply sum_bij (fun f _ ↦ k * f)
  · intro f hf
    obtain ⟨hm, hd⟩ := (mem_harcosMonicPolynomials n f).mp hf
    exact mem_filter.mpr ⟨(mem_harcosMonicPolynomials _ _).mpr
      ⟨hk.mul hm, by rw [hk.natDegree_mul hm, hd]⟩, dvd_mul_right k f⟩
  · intro f _ g _ he
    exact mul_left_cancel₀ hk.ne_zero he
  · intro f hf
    obtain ⟨hfm, hd⟩ := (mem_harcosMonicPolynomials _ _).mp (mem_filter.mp hf).1
    obtain ⟨g, rfl⟩ := (mem_filter.mp hf).2
    have hg := hk.of_mul_monic_left hfm
    refine ⟨g, (mem_harcosMonicPolynomials _ _).mpr ⟨hg, ?_⟩, rfl⟩
    rw [hk.natDegree_mul hg] at hd
    omega
  · intro f hf
    have hm := ((mem_harcosMonicPolynomials n f).mp hf).1
    rw [euler_count_mul k f hk hi hm, map_mul, Nat.cast_add, Nat.cast_one]
    ring

private theorem euler_degree_sum (f : (ZMod p)[X]) (hf : f.Monic) :
    ((normalizedFactors f).map natDegree).sum = f.natDegree := by
  have hprod : (normalizedFactors f).prod = f := by
    simpa [hf.leadingCoeff] using leadingCoeff_mul_prod_normalizedFactors f
  rw [← natDegree_multiset_prod _ (zero_notMem_normalizedFactors f), hprod]

theorem harcosEuler_degree_marked (η : (ZMod p)[X] →* ℂ) (n : ℕ) :
    (n : ℂ) * harcosEulerCoefficient η n =
      ∑ k ∈ harcosEulerPrimes p n, (k.natDegree : ℂ) * harcosEulerMarked η k n := by
  classical
  unfold harcosEulerCoefficient harcosEulerMarked
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro f hf
  obtain ⟨hm, hd⟩ := (mem_harcosMonicPolynomials n f).mp hf
  have hsub : (normalizedFactors f).toFinset ⊆ harcosEulerPrimes p n := by
    intro k hk
    obtain ⟨hi, hkm, hkd⟩ :=
      (Polynomial.mem_normalizedFactors_iff hm.ne_zero).mp (Multiset.mem_toFinset.mp hk)
    exact (mem_harcosEulerPrimes n k).mpr
      ⟨hkm, hi, hd ▸ natDegree_le_of_dvd hkd hm.ne_zero⟩
  have hs : ∑ k ∈ harcosEulerPrimes p n,
      k.natDegree * (normalizedFactors f).count k = n := by
    have hdeg := euler_degree_sum f hm
    rw [sum_multiset_map_count, hd] at hdeg
    calc
      _ = ∑ k ∈ (normalizedFactors f).toFinset,
          (normalizedFactors f).count k • k.natDegree := by
        simp only [nsmul_eq_mul, mul_comm]
        symm
        apply sum_subset hsub
        intro k _ hk
        have hn : k ∉ normalizedFactors f := by rwa [Multiset.mem_toFinset] at hk
        simp [Multiset.count_eq_zero.mpr hn]
      _ = n := hdeg
  have hsc := congrArg (fun x : ℕ ↦ (x : ℂ)) hs
  push_cast at hsc
  rw [← hsc, sum_mul]
  apply sum_congr rfl
  intro k _
  ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosEulerSeries -/

/-! # The coefficientwise Euler logarithmic derivative -/

noncomputable section

open Finset
open scoped Polynomial

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The geometric formal series in `c T^d`; no convergence is involved. -/
def harcosEulerGeometric (d : ℕ) (c : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n ↦ if d ∣ n then c ^ (n / d) else 0

theorem harcosEulerGeometric_step (d : ℕ) (hd : 0 < d) (c : ℂ) :
    harcosEulerGeometric d c =
      1 + PowerSeries.C c * PowerSeries.X ^ d * harcosEulerGeometric d c := by
  apply PowerSeries.ext
  intro n
  rw [map_add, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  by_cases hn : d ≤ n
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hne : d + m ≠ 0 := by omega
    simp only [harcosEulerGeometric, PowerSeries.coeff_mk, PowerSeries.coeff_one,
      if_neg hne, zero_add, Nat.le_add_right, if_true, Nat.add_sub_cancel_left,
      Nat.dvd_add_self_left, Nat.add_div_left _ hd]
    split_ifs <;> simp [pow_succ, mul_comm]
  · have hlt : n < d := by omega
    simp only [if_neg hn, mul_zero, add_zero, harcosEulerGeometric,
      PowerSeries.coeff_mk, PowerSeries.coeff_one]
    by_cases hz : n = 0
    · simp [hz]
    · rw [if_neg hz, if_neg]
      exact fun h ↦ (Nat.le_of_dvd (Nat.pos_of_ne_zero hz) h).not_gt hlt

theorem harcosEulerGeometric_mul (d : ℕ) (hd : 0 < d) (c : ℂ) :
    (1 - PowerSeries.C c * PowerSeries.X ^ d) * harcosEulerGeometric d c = 1 := by
  have h := harcosEulerGeometric_step d hd c
  linear_combination h

variable {p : ℕ} [Fact p.Prime]

/-- The formal series of the actual monic coefficient sums. -/
def harcosEulerSeries (η : (ZMod p)[X] →* ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (harcosEulerCoefficient η)

private def eulerMarkedSeries (η : (ZMod p)[X] →* ℂ) (k : (ZMod p)[X]) :
    PowerSeries ℂ :=
  PowerSeries.mk (harcosEulerMarked η k)

private theorem eulerMarkedSeries_step (η : (ZMod p)[X] →* ℂ)
    (k : (ZMod p)[X]) (hk : k.Monic) (hi : Irreducible k) :
    eulerMarkedSeries η k = PowerSeries.C (η k) * PowerSeries.X ^ k.natDegree *
      (harcosEulerSeries η + eulerMarkedSeries η k) := by
  apply PowerSeries.ext
  intro n
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  by_cases hn : k.natDegree ≤ n
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    simp only [Nat.le_add_right, if_true, Nat.add_sub_cancel_left,
      map_add, eulerMarkedSeries, harcosEulerSeries, PowerSeries.coeff_mk]
    exact harcosEulerMarked_add_degree η k hk hi m
  · simp only [if_neg hn, mul_zero, eulerMarkedSeries, PowerSeries.coeff_mk]
    exact harcosEulerMarked_eq_zero η k n (by omega)

theorem harcosEulerMarked_series (η : (ZMod p)[X] →* ℂ)
    (k : (ZMod p)[X]) (hk : k.Monic) (hi : Irreducible k) :
    PowerSeries.mk (harcosEulerMarked η k) =
      (harcosEulerGeometric k.natDegree (η k) - 1) * harcosEulerSeries η := by
  have hd : 0 < k.natDegree := hi.natDegree_pos
  have hs := eulerMarkedSeries_step η k hk hi
  have hg := harcosEulerGeometric_mul k.natDegree hd (η k)
  change eulerMarkedSeries η k = _
  calc
    eulerMarkedSeries η k =
        ((1 - PowerSeries.C (η k) * PowerSeries.X ^ k.natDegree) *
          harcosEulerGeometric k.natDegree (η k)) * eulerMarkedSeries η k := by rw [hg, one_mul]
    _ = (harcosEulerGeometric k.natDegree (η k) - 1) * harcosEulerSeries η := by
      linear_combination harcosEulerGeometric k.natDegree (η k) * hs -
        harcosEulerSeries η * hg

/-- A finite logarithmic-derivative series, containing all irreducibles up to the cutoff. -/
def harcosEulerLog (η : (ZMod p)[X] →* ℂ) (N : ℕ) : PowerSeries ℂ :=
  ∑ k ∈ harcosEulerPrimes p N, PowerSeries.C (k.natDegree : ℂ) *
    (harcosEulerGeometric k.natDegree (η k) - 1)

theorem harcosEulerLog_mul_coeff (η : (ZMod p)[X] →* ℂ) (N n : ℕ) (hn : n ≤ N) :
    PowerSeries.coeff n (harcosEulerLog η N * harcosEulerSeries η) =
      (n : ℂ) * harcosEulerCoefficient η n := by
  classical
  rw [harcosEulerLog, sum_mul, map_sum]
  calc
    _ = ∑ k ∈ harcosEulerPrimes p N,
        (k.natDegree : ℂ) * harcosEulerMarked η k n := by
      apply sum_congr rfl
      intro k hk
      obtain ⟨hkm, hki, _⟩ := (mem_harcosEulerPrimes N k).mp hk
      rw [mul_assoc, ← harcosEulerMarked_series η k hkm hki,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    _ = _ := by
      rw [harcosEuler_degree_marked η n]
      symm
      apply sum_subset
      · intro k hk
        obtain ⟨hkm, hki, hkd⟩ := (mem_harcosEulerPrimes n k).mp hk
        exact (mem_harcosEulerPrimes N k).mpr ⟨hkm, hki, hkd.trans hn⟩
      · intro k hk hkn
        obtain ⟨hkm, hki, _⟩ := (mem_harcosEulerPrimes N k).mp hk
        have hd : n < k.natDegree := by
          by_contra! h
          exact hkn ((mem_harcosEulerPrimes n k).mpr ⟨hkm, hki, h⟩)
        rw [harcosEulerMarked_eq_zero η k n hd, mul_zero]

/-- The actual irreducible divisor sum appearing in Harcos's equation (10). -/
def harcosEulerLogCoefficient (η : (ZMod p)[X] →* ℂ) (n : ℕ) : ℂ := by
  classical
  exact ∑ d ∈ n.divisors, (d : ℂ) *
    ∑ k ∈ (harcosMonicPolynomials p d).filter Irreducible, η k ^ (n / d)

theorem harcosEulerLog_coeff (η : (ZMod p)[X] →* ℂ) (N n : ℕ) (hn : n ≤ N) :
    PowerSeries.coeff n (harcosEulerLog η N) = harcosEulerLogCoefficient η n := by
  classical
  by_cases hz : n = 0
  · subst n
    simp [harcosEulerLog, harcosEulerGeometric, harcosEulerLogCoefficient]
  rw [harcosEulerLog, map_sum]
  simp_rw [PowerSeries.coeff_C_mul, map_sub, harcosEulerGeometric,
    PowerSeries.coeff_mk, PowerSeries.coeff_one, if_neg hz, sub_zero]
  rw [harcosEulerPrimes, sum_biUnion]
  · have hfilter : (range (N + 1)).filter (· ∣ n) = n.divisors := by
      ext d
      simp only [mem_filter, mem_range, Nat.mem_divisors]
      constructor
      · exact fun h ↦ ⟨h.2, hz⟩
      · intro h
        exact ⟨by have := Nat.le_of_dvd (Nat.pos_of_ne_zero hz) h.1; omega, h.1⟩
    calc
      _ = ∑ d ∈ range (N + 1), if d ∣ n then (d : ℂ) *
          ∑ k ∈ (harcosMonicPolynomials p d).filter Irreducible,
            η k ^ (n / d) else 0 := by
        apply sum_congr rfl
        intro d _
        by_cases hd : d ∣ n
        · rw [if_pos hd, mul_sum]
          apply sum_congr rfl
          intro k hk
          have hkdeg := ((mem_harcosMonicPolynomials d k).mp (mem_filter.mp hk).1).2
          rw [hkdeg, if_pos hd]
        · rw [if_neg hd]
          apply sum_eq_zero
          intro k hk
          have hkdeg := ((mem_harcosMonicPolynomials d k).mp (mem_filter.mp hk).1).2
          rw [hkdeg, if_neg hd, mul_zero]
      _ = _ := by rw [← sum_filter, hfilter]; rfl
  · intro d _ e _ hde
    apply disjoint_left.mpr
    intro k hk hk'
    have hd := ((mem_harcosMonicPolynomials d k).mp (mem_filter.mp hk).1).2
    have he := ((mem_harcosMonicPolynomials e k).mp (mem_filter.mp hk').1).2
    exact hde (hd.symm.trans he)


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosEulerRoots -/

/-!
# Harcos's irreducible sum equals the negative root power sum

The input character is the actual polynomial character. The Euler logarithmic
identity is produced by finite factorization, not assumed.
-/

noncomputable section

open Finset
open scoped Polynomial

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem euler_coeff_cancel (A F G : PowerSeries ℂ)
    (hA : PowerSeries.constantCoeff A = 1) (N : ℕ)
    (h : ∀ n ≤ N, PowerSeries.coeff n (F * A) = PowerSeries.coeff n (G * A)) :
    PowerSeries.coeff N F = PowerSeries.coeff N G := by
  obtain ⟨u, hu⟩ := PowerSeries.isUnit_iff_constantCoeff.mpr
    (show IsUnit (PowerSeries.constantCoeff A) by rw [hA]; exact isUnit_one)
  have he : PowerSeries.coeff N ((F * A) * (↑u⁻¹ : PowerSeries ℂ)) =
      PowerSeries.coeff N ((G * A) * (↑u⁻¹ : PowerSeries ℂ)) := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply sum_congr rfl
    intro ij hij
    rw [h ij.1 (by have := mem_antidiagonal.mp hij; omega)]
  simpa [mul_assoc, ← hu] using he

private def eulerRootLog (α β : ℂ) : PowerSeries ℂ :=
  -((harcosEulerGeometric 1 α - 1) + (harcosEulerGeometric 1 β - 1))

private theorem eulerRootLog_mul (α β : ℂ) :
    eulerRootLog α β *
        ((1 - PowerSeries.C α * PowerSeries.X) * (1 - PowerSeries.C β * PowerSeries.X)) =
      PowerSeries.X * (PowerSeries.derivative (R := ℂ))
        ((1 - PowerSeries.C α * PowerSeries.X) * (1 - PowerSeries.C β * PowerSeries.X)) := by
  have ha := harcosEulerGeometric_mul 1 (by omega) α
  have hb := harcosEulerGeometric_mul 1 (by omega) β
  simp only [pow_one] at ha hb
  simp only [eulerRootLog, Derivation.leibniz, map_sub, PowerSeries.derivative_one,
    PowerSeries.derivative_C, PowerSeries.derivative_X, smul_eq_mul,
    mul_zero, mul_one, zero_sub]
  linear_combination
    -(1 - PowerSeries.C β * PowerSeries.X) * ha -
    (1 - PowerSeries.C α * PowerSeries.X) * hb

private theorem eulerRootLog_coeff (α β : ℂ) (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff n (eulerRootLog α β) = -(α ^ n + β ^ n) := by
  simp [eulerRootLog, harcosEulerGeometric, PowerSeries.coeff_one, hn]

variable {p : ℕ} [Fact p.Prime]

theorem harcosEulerCoefficient_zero (η : (ZMod p)[X] →* ℂ) :
    harcosEulerCoefficient η 0 = 1 := by
  classical
  simp [harcosEulerCoefficient, harcosMonicPolynomials, harcosMonic_zero]

/-- A quadratic factorization of the actual monic series determines all prime-power sums. -/
theorem harcosEulerLogCoefficient_eq_powerSum (η : (ZMod p)[X] →* ℂ) (α β : ℂ)
    (hA : harcosEulerSeries η =
      (1 - PowerSeries.C α * PowerSeries.X) * (1 - PowerSeries.C β * PowerSeries.X))
    (n : ℕ) (hn : n ≠ 0) :
    harcosEulerLogCoefficient η n = -(α ^ n + β ^ n) := by
  have h0 : PowerSeries.constantCoeff (harcosEulerSeries η) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, harcosEulerSeries,
      PowerSeries.coeff_mk, harcosEulerCoefficient_zero]
  have he := euler_coeff_cancel (harcosEulerSeries η)
    (harcosEulerLog η n) (eulerRootLog α β) h0 n (by
      intro j hj
      rw [harcosEulerLog_mul_coeff η n j hj, hA, eulerRootLog_mul, ← hA]
      cases j with
      | zero => simp
      | succ j =>
          rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
            harcosEulerSeries, PowerSeries.coeff_mk]
          push_cast
          ring)
  rw [harcosEulerLog_coeff η n n le_rfl, eulerRootLog_coeff α β n hn] at he
  exact he

theorem harcosEulerSeries_character (a b : ZMod p) :
    harcosEulerSeries (harcosEtaHom a b).toMonoidHom = harcosLSeries a b := by
  apply PowerSeries.ext
  intro n
  rw [harcosEulerSeries, harcosLSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
    harcosCoefficient_eq_sum_monic]
  rfl


/-- The actual irreducible coefficients for the explicitly constructed reciprocal roots. -/
theorem harcosEuler_character_reciprocalRoots (a b : ZMod p) (ha : a ≠ 0)
    (n : ℕ) (hn : n ≠ 0) :
    harcosEulerLogCoefficient (harcosEtaHom a b).toMonoidHom n =
      -(harcosReciprocalRootPlus a b ^ n + harcosReciprocalRootMinus a b ^ n) := by
  apply harcosEulerLogCoefficient_eq_powerSum _ _ _ _ n hn
  rw [harcosEulerSeries_character]
  exact harcosLSeries_factorization a b ha

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosEulerIndex -/

/-! # The finite Euler index for comparison with minimal-polynomial orbits -/

noncomputable section

open Finset
open scoped Polynomial

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

variable {p : ℕ} [Fact p.Prime]

/-- Monic irreducibles with nonzero constant coefficient and degree dividing `n`. -/
def harcosEulerNonzeroPrimes (p n : ℕ) [Fact p.Prime] : Finset (ZMod p)[X] := by
  classical
  exact (harcosEulerPrimes p n).filter fun k ↦ k.coeff 0 ≠ 0 ∧ k.natDegree ∣ n

theorem mem_harcosEulerNonzeroPrimes (n : ℕ) (hn : n ≠ 0) (k : (ZMod p)[X]) :
    k ∈ harcosEulerNonzeroPrimes p n ↔
      k.Monic ∧ Irreducible k ∧ k.coeff 0 ≠ 0 ∧ k.natDegree ∣ n := by
  classical
  simp only [harcosEulerNonzeroPrimes, mem_filter, mem_harcosEulerPrimes]
  constructor
  · exact fun ⟨⟨hm, hi, _⟩, hc, hd⟩ ↦ ⟨hm, hi, hc, hd⟩
  · rintro ⟨hm, hi, hc, hd⟩
    exact ⟨⟨hm, hi, Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd⟩, hc, hd⟩

theorem harcosEulerLogCoefficient_eq_flat (η : (ZMod p)[X] →* ℂ) (n : ℕ) (hn : n ≠ 0) :
    harcosEulerLogCoefficient η n =
      ∑ k ∈ (harcosEulerPrimes p n).filter (fun k ↦ k.natDegree ∣ n),
        (k.natDegree : ℂ) * η k ^ (n / k.natDegree) := by
  classical
  rw [← harcosEulerLog_coeff η n n le_rfl, harcosEulerLog, map_sum, sum_filter]
  apply sum_congr rfl
  intro k _
  simp only [PowerSeries.coeff_C_mul, map_sub, harcosEulerGeometric,
    PowerSeries.coeff_mk, PowerSeries.coeff_one, if_neg hn, sub_zero]
  split_ifs <;> simp

/-- The exact flat, nonzero-root index used by the finite-field orbit sum. -/
theorem harcosEuler_character_eq_nonzeroPrime_sum (a b : ZMod p)
    (n : ℕ) (hn : n ≠ 0) :
    harcosEulerLogCoefficient (harcosEtaHom a b).toMonoidHom n =
      ∑ k ∈ harcosEulerNonzeroPrimes p n,
        (k.natDegree : ℂ) * harcosEta a b k ^ (n / k.natDegree) := by
  classical
  rw [harcosEulerLogCoefficient_eq_flat _ n hn]
  change (∑ k ∈ (harcosEulerPrimes p n).filter (fun k ↦ k.natDegree ∣ n),
    (k.natDegree : ℂ) * harcosEta a b k ^ (n / k.natDegree)) = _
  symm
  apply sum_subset
  · intro k hk
    obtain ⟨hkm, hki, hc, hd⟩ := (mem_harcosEulerNonzeroPrimes n hn k).mp hk
    exact mem_filter.mpr ⟨(mem_harcosEulerPrimes n k).mpr
      ⟨hkm, hki, Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd⟩, hd⟩
  · intro k hk hkn
    obtain ⟨hkp, hd⟩ := mem_filter.mp hk
    obtain ⟨hkm, hki, hle⟩ := (mem_harcosEulerPrimes n k).mp hkp
    have hc : k.coeff 0 = 0 := by
      by_contra h
      exact hkn ((mem_harcosEulerNonzeroPrimes n hn k).mpr ⟨hkm, hki, h, hd⟩)
    have he : n / k.natDegree ≠ 0 := by
      have := Nat.div_pos hle hki.natDegree_pos
      omega
    simp [harcosEta, hc, he]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosMinpoly -/

/-!
# Minimal-polynomial linkage in Harcos's Theorem 6

Harcos, §3, pages 7–8 (`pages/harcos-lpolynomial-07.png` and
`pages/harcos-stepanov-08.png`), identifies the character on each orbit
with a power of the polynomial character. The extension multiplicity is
a natural-number quotient, not division in the base field.
-/

noncomputable section

open Polynomial IntermediateField Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

section General

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L]

omit [FiniteDimensional K L] in
private theorem adjoin_inv_eq (t : L) : K⟮t⁻¹⟯ = K⟮t⟯ := by
  apply le_antisymm
  · exact adjoin_simple_le_iff.mpr ((K⟮t⟯).inv_mem (mem_adjoin_simple_self K t))
  · apply adjoin_simple_le_iff.mpr
    simpa only [inv_inv] using
      (K⟮t⁻¹⟯).inv_mem (mem_adjoin_simple_self K t⁻¹)

theorem harcos_minpoly_inv_natDegree (t : L) :
    (minpoly K t⁻¹).natDegree = (minpoly K t).natDegree := by
  rw [← adjoin.finrank (IsIntegral.of_finite K t⁻¹),
    ← adjoin.finrank (IsIntegral.of_finite K t), adjoin_inv_eq]

/-- The inverse minimal polynomial is the normalized coefficient reversal. -/
theorem harcos_minpoly_inv (t : L) (ht : t ≠ 0) :
    minpoly K t⁻¹ = (minpoly K t).reverse * C ((minpoly K t).coeff 0)⁻¹ := by
  have hc := minpoly.coeff_zero_ne_zero (IsIntegral.of_finite K t) ht
  have hl : (minpoly K t).reverse.leadingCoeff = (minpoly K t).coeff 0 := by
    rw [reverse_leadingCoeff, trailingCoeff_eq_coeff_zero hc]
  apply Eq.symm
  apply eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (IsIntegral.of_finite K t⁻¹))
  · rw [← hl]
    exact monic_mul_leadingCoeff_inv
      (reverse_eq_zero.not.mpr (minpoly.ne_zero (IsIntegral.of_finite K t)))
  · apply minpoly.dvd
    rw [map_mul]
    have hr : aeval t⁻¹ (minpoly K t).reverse = 0 := by
      let : Invertible t := invertibleOfNonzero ht
      simpa only [invOf_eq_inv, ← aeval_def] using
        (eval₂_reverse_eq_zero_iff (algebraMap K L) t (minpoly K t)).mpr
          (minpoly.aeval K t)
    rw [hr, zero_mul]
  · rw [natDegree_mul_C (inv_ne_zero hc), harcos_minpoly_inv_natDegree]
    exact reverse_natDegree_le _

theorem harcos_minpoly_inv_nextCoeff (t : L) (ht : t ≠ 0) :
    (minpoly K t⁻¹).nextCoeff = (minpoly K t).coeff 1 / (minpoly K t).coeff 0 := by
  have hc := minpoly.coeff_zero_ne_zero (IsIntegral.of_finite K t) ht
  have hd : (minpoly K t).reverse.natDegree = (minpoly K t).natDegree := by
    rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hc), Nat.sub_zero]
  have hp := minpoly.natDegree_pos (IsIntegral.of_finite K t)
  rw [harcos_minpoly_inv K t ht, nextCoeff_mul_C,
    nextCoeff_of_natDegree_pos (hd.symm ▸ hp), hd, coeff_reverse,
    revAt_le (Nat.sub_le _ _)]
  have hi : (minpoly K t).natDegree - ((minpoly K t).natDegree - 1) = 1 := by omega
  rw [hi, div_eq_mul_inv]

/-- The tower index is an integer quotient before casting to the base field. -/
theorem harcos_minpoly_extension_index (t : L) :
    Module.finrank K⟮t⟯ L = Module.finrank K L / (minpoly K t).natDegree := by
  rw [← Module.finrank_mul_finrank K K⟮t⟯ L,
    adjoin.finrank (IsIntegral.of_finite K t),
    Nat.mul_div_right _ (minpoly.natDegree_pos (IsIntegral.of_finite K t))]

theorem harcos_trace_inv_minpoly (t : L) (ht : t ≠ 0) :
    Algebra.trace K L t⁻¹ =
      ((Module.finrank K L / (minpoly K t).natDegree : ℕ) : K) *
        (-(minpoly K t).coeff 1 / (minpoly K t).coeff 0) := by
  rw [trace_eq_finrank_mul_minpoly_nextCoeff,
    harcos_minpoly_extension_index, harcos_minpoly_inv_natDegree,
    harcos_minpoly_inv_nextCoeff K t ht, neg_div]

/-- The actual trace of the Kloosterman phase, including inseparable tower indices
and indices divisible by the characteristic. -/
theorem harcos_trace_minpoly_phase (a b : K) (t : L) (ht : t ≠ 0) :
    Algebra.trace K L (algebraMap K L a * t + algebraMap K L b / t) =
      ((Module.finrank K L / (minpoly K t).natDegree : ℕ) : K) *
        (-a * (minpoly K t).nextCoeff -
          b * (minpoly K t).coeff 1 / (minpoly K t).coeff 0) := by
  rw [div_eq_mul_inv, ← Algebra.smul_def, ← Algebra.smul_def, map_add,
    map_smul, map_smul, trace_eq_finrank_mul_minpoly_nextCoeff,
    harcos_minpoly_extension_index, harcos_trace_inv_minpoly K t ht,
    smul_eq_mul, smul_eq_mul]
  ring

end General

section PrimeField

variable (p : ℕ) [Fact p.Prime]
variable (F : Type*) [Field F] [Fintype F] [Algebra (ZMod p) F]

/-- The character value is constant on the minimal-polynomial fiber.
The exponent is a natural number even when the characteristic divides the index. -/
theorem harcos_minpoly_eta_power (a b : ZMod p) (m : ℕ) (t : F) (ht : t ≠ 0) :
    ZMod.stdAddChar ((m : ZMod p) * Algebra.trace (ZMod p) F
      (algebraMap (ZMod p) F a * t + algebraMap (ZMod p) F b / t)) =
      harcosEta a b (minpoly (ZMod p) t) ^
        (m * (Module.finrank (ZMod p) F / (minpoly (ZMod p) t).natDegree)) := by
  have hc := minpoly.coeff_zero_ne_zero (IsIntegral.of_finite (ZMod p) t) ht
  rw [harcos_trace_minpoly_phase (ZMod p) a b t ht]
  simp only [harcosEta, hc, if_false,
    (minpoly.monic (IsIntegral.of_finite (ZMod p) t)).leadingCoeff, div_one]
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, Nat.cast_mul]
  congr 1
  ring

/-- The finite set of minimal polynomials of nonzero elements of the extension. -/
def harcosMinpolyOrbits : Finset (ZMod p)[X] := by
  classical
  exact univ.image fun t : Fˣ => minpoly (ZMod p) (t : F)

/-- Each orbit is represented by its actual nonzero roots in the given field. -/
def harcosMinpolyFiber (k : (ZMod p)[X]) : Finset Fˣ := by
  classical
  exact univ.filter fun t : Fˣ => minpoly (ZMod p) (t : F) = k

theorem harcos_mem_minpolyOrbits (k : (ZMod p)[X]) :
    k ∈ harcosMinpolyOrbits p F ↔ ∃ t : Fˣ, minpoly (ZMod p) (t : F) = k := by
  classical
  simp [harcosMinpolyOrbits]

theorem harcos_mem_minpolyFiber (k : (ZMod p)[X]) (t : Fˣ) :
    t ∈ harcosMinpolyFiber p F k ↔ minpoly (ZMod p) (t : F) = k := by
  classical
  simp [harcosMinpolyFiber]

private theorem irreducible_splits_of_degree_dvd (k : (ZMod p)[X])
    (hi : Irreducible k) (hd : k.natDegree ∣ Module.finrank (ZMod p) F) :
    (k.map (algebraMap (ZMod p) F)).Splits := by
  have hdiv := hi.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp hd
  have hc : Nat.card (ZMod p) ^ Module.finrank (ZMod p) F = Fintype.card F := by
    simpa only [Nat.card_eq_fintype_card] using
      (Module.card_eq_pow_finrank (K := ZMod p) (V := F)).symm
  rw [hc] at hdiv
  apply (FiniteField.splits_X_pow_card_sub_X p (K := F)).of_dvd
  · simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X] using
      Polynomial.X_pow_sub_X_ne_zero (R := F) (Fintype.one_lt_card (α := F))
  · exact Polynomial.map_dvd (algebraMap (ZMod p) F) hdiv

omit [Fintype F] in
private theorem root_ne_zero (k : (ZMod p)[X]) (hc : k.coeff 0 ≠ 0)
    (x : F) (hx : aeval x k = 0) : x ≠ 0 := by
  intro he
  subst x
  apply hc
  apply (algebraMap (ZMod p) F).injective
  simpa only [aeval_def, eval₂_at_zero, map_zero] using hx

/-- Harcos's orbit index set is exactly all monic irreducibles of degree dividing
the extension degree, except `X`, excluded by the nonzero constant coefficient. -/
theorem harcos_mem_minpolyOrbits_iff (k : (ZMod p)[X]) :
    k ∈ harcosMinpolyOrbits p F ↔ k.Monic ∧ Irreducible k ∧ k.coeff 0 ≠ 0 ∧
      k.natDegree ∣ Module.finrank (ZMod p) F := by
  rw [harcos_mem_minpolyOrbits]
  constructor
  · rintro ⟨t, rfl⟩
    have hi := IsIntegral.of_finite (ZMod p) (t : F)
    exact ⟨minpoly.monic hi, minpoly.irreducible hi,
      minpoly.coeff_zero_ne_zero hi t.ne_zero, minpoly.degree_dvd hi⟩
  · rintro ⟨hm, hi, hc, hd⟩
    have hs := irreducible_splits_of_degree_dvd p F k hi hd
    have hdeg : (k.map (algebraMap (ZMod p) F)).degree ≠ 0 := by
      rw [degree_map]
      exact hi.degree_pos.ne'
    obtain ⟨x, hx⟩ := hs.exists_eval_eq_zero hdeg
    rw [eval_map_algebraMap] at hx
    refine ⟨Units.mk0 x (root_ne_zero p F k hc x hx), ?_⟩
    exact (minpoly.eq_of_irreducible_of_monic hi hx hm).symm

/-- Each minimal-polynomial fiber has cardinality exactly its degree, with no
chosen algebraic closure and no assumption about orbit cardinalities. -/
theorem harcos_minpolyFiber_card (k : (ZMod p)[X])
    (hk : k ∈ harcosMinpolyOrbits p F) :
    (harcosMinpolyFiber p F k).card = k.natDegree := by
  classical
  obtain ⟨hm, hi, hc, hd⟩ := (harcos_mem_minpolyOrbits_iff p F k).mp hk
  let e : ↥(harcosMinpolyFiber p F k) ≃ k.rootSet F :=
    { toFun := fun t =>
        ⟨(t.1 : F), (mem_rootSet_of_ne hi.ne_zero).mpr (by
          have ht := (harcos_mem_minpolyFiber p F k t.1).mp t.2
          exact (congrArg (aeval (t.1 : F)) ht).symm.trans
            (minpoly.aeval (ZMod p) (t.1 : F)))⟩
      invFun := fun x =>
        ⟨Units.mk0 x.1 (root_ne_zero p F k hc x.1
          ((mem_rootSet_of_ne hi.ne_zero).mp x.2)),
          (harcos_mem_minpolyFiber p F k _).mpr
            (minpoly.eq_of_irreducible_of_monic hi
              ((mem_rootSet_of_ne hi.ne_zero).mp x.2) hm).symm⟩
      left_inv := fun t => by apply Subtype.ext; apply Units.ext; rfl
      right_inv := fun x => by apply Subtype.ext; rfl }
  calc
    (harcosMinpolyFiber p F k).card = Fintype.card ↥(harcosMinpolyFiber p F k) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card (k.rootSet F) := Fintype.card_congr e
    _ = k.natDegree := card_rootSet_eq_natDegree (PerfectField.separable_of_irreducible hi)
      (irreducible_splits_of_degree_dvd p F k hi hd)

/-- The contribution of a single orbit is its degree times its eta power. -/
theorem harcos_minpolyFiber_character_sum (a b : ZMod p) (m : ℕ)
    (k : (ZMod p)[X]) (hk : k ∈ harcosMinpolyOrbits p F) :
    ∑ t ∈ harcosMinpolyFiber p F k,
      ZMod.stdAddChar ((m : ZMod p) * Algebra.trace (ZMod p) F
        (algebraMap (ZMod p) F a * (t : F) + algebraMap (ZMod p) F b / (t : F))) =
      (k.natDegree : ℂ) *
        harcosEta a b k ^ (m * (Module.finrank (ZMod p) F / k.natDegree)) := by
  classical
  calc
    _ = ∑ _t ∈ harcosMinpolyFiber p F k,
        harcosEta a b k ^ (m * (Module.finrank (ZMod p) F / k.natDegree)) := by
      apply sum_congr rfl
      intro t ht
      rw [harcos_minpoly_eta_power p F a b m (t : F) t.ne_zero,
        (harcos_mem_minpolyFiber p F k t).mp ht]
    _ = _ := by rw [sum_const, harcos_minpolyFiber_card p F k hk, nsmul_eq_mul]

/-- The finite orbit-sum identity in the last step of Harcos's Theorem 6.
Together with `harcos_mem_minpolyOrbits_iff`, this is precisely the sum over
monic irreducibles of degrees dividing the extension degree, excluding `X`. -/
theorem harcos_trace_character_minpoly_sum [DecidableEq F] (a b : ZMod p) (m : ℕ) :
    ∑ t : Fˣ, ZMod.stdAddChar ((m : ZMod p) * Algebra.trace (ZMod p) F
      (algebraMap (ZMod p) F a * (t : F) + algebraMap (ZMod p) F b / (t : F))) =
      ∑ k ∈ harcosMinpolyOrbits p F, (k.natDegree : ℂ) *
        harcosEta a b k ^ (m * (Module.finrank (ZMod p) F / k.natDegree)) := by
  classical
  calc
    _ = ∑ k ∈ harcosMinpolyOrbits p F, ∑ t ∈ harcosMinpolyFiber p F k,
        ZMod.stdAddChar ((m : ZMod p) * Algebra.trace (ZMod p) F
          (algebraMap (ZMod p) F a * (t : F) +
            algebraMap (ZMod p) F b / (t : F))) := by
      have h := (sum_fiberwise_of_maps_to
        (s := univ) (t := harcosMinpolyOrbits p F)
        (g := fun t : Fˣ => minpoly (ZMod p) (t : F))
        (fun t _ => (harcos_mem_minpolyOrbits p F _).mpr ⟨t, rfl⟩)
        (fun t => ZMod.stdAddChar ((m : ZMod p) * Algebra.trace (ZMod p) F
          (algebraMap (ZMod p) F a * (t : F) +
            algebraMap (ZMod p) F b / (t : F))))).symm
      refine h.trans (sum_congr rfl fun k _ => sum_congr ?_ fun _ _ => rfl)
      ext t
      simp [harcos_mem_minpolyFiber]
    _ = _ := sum_congr rfl fun k hk => harcos_minpolyFiber_character_sum p F a b m k hk

/-- The orbit identity consumes the actual trace-character sum used in the
Artin–Schreier point-count bridge, for every prime-field frequency. -/
theorem harcosTraceKloosterman_minpoly_sum [DecidableEq F] (a b m : ZMod p) :
    harcosTraceKloosterman p F a b m =
      ∑ k ∈ harcosMinpolyOrbits p F, (k.natDegree : ℂ) *
        harcosEta a b k ^ (m.val * (Module.finrank (ZMod p) F / k.natDegree)) := by
  simpa only [harcosTraceKloosterman, ZMod.natCast_zmod_val, div_eq_mul_inv] using
    harcos_trace_character_minpoly_sum p F a b m.val

end PrimeField

section ExtensionSequence

variable (p : ℕ) [Fact p.Prime]

/-- Frequency scaling agrees with an eta power on polynomials not divisible by
`X`. The nonzero-constant condition matters at frequency zero. -/
theorem harcosEta_frequency_of_coeff_zero_ne (a b m : ZMod p)
    (k : (ZMod p)[X]) (hk : k.coeff 0 ≠ 0) :
    harcosEta (m * a) (m * b) k = harcosEta a b k ^ m.val := by
  simp only [harcosEta, hk, if_false]
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val]
  congr 1
  ring

/-- Orbit indices for the same fixed extension used by `harcosExtensionKloosterman`. -/
def harcosExtensionMinpolyOrbits (n : ℕ) : Finset (ZMod p)[X] := by
  letI := Fintype.ofFinite (GaloisField p n)
  exact harcosMinpolyOrbits p (GaloisField p n)

theorem harcos_mem_extensionMinpolyOrbits_iff (n : ℕ) (hn : 0 < n)
    (k : (ZMod p)[X]) :
    k ∈ harcosExtensionMinpolyOrbits p n ↔
      k.Monic ∧ Irreducible k ∧ k.coeff 0 ≠ 0 ∧ k.natDegree ∣ n := by
  let := Fintype.ofFinite (GaloisField p n)
  simpa only [harcosExtensionMinpolyOrbits, GaloisField.finrank p hn.ne'] using
    harcos_mem_minpolyOrbits_iff p (GaloisField p n) k

/-- The orbit identity for the actual extension sequence, only at positive
degrees: `GaloisField p 0` is not a field with one element. -/
theorem harcosExtensionKloosterman_minpoly_sum (a b m : ZMod p)
    (n : ℕ) (hn : 0 < n) :
    harcosExtensionKloosterman p a b m n =
      ∑ k ∈ harcosExtensionMinpolyOrbits p n, (k.natDegree : ℂ) *
        harcosEta a b k ^ (m.val * (n / k.natDegree)) := by
  let := Fintype.ofFinite (GaloisField p n)
  let := Classical.decEq (GaloisField p n)
  simpa only [harcosExtensionKloosterman, harcosExtensionMinpolyOrbits,
    GaloisField.finrank p hn.ne'] using
    harcosTraceKloosterman_minpoly_sum p (GaloisField p n) a b m

/-- Frequency-scaled form of the orbit identity, matching the finite Euler
coefficient for the actual polynomial character `harcosEta (m*a) (m*b)`. -/
theorem harcosExtensionKloosterman_minpoly_sum_scaled (a b m : ZMod p)
    (n : ℕ) (hn : 0 < n) :
    harcosExtensionKloosterman p a b m n =
      ∑ k ∈ harcosExtensionMinpolyOrbits p n, (k.natDegree : ℂ) *
        harcosEta (m * a) (m * b) k ^ (n / k.natDegree) := by
  rw [harcosExtensionKloosterman_minpoly_sum p a b m n hn]
  apply sum_congr rfl
  intro k hk
  have hc := ((harcos_mem_extensionMinpolyOrbits_iff p n hn k).mp hk).2.2.1
  rw [harcosEta_frequency_of_coeff_zero_ne p a b m k hc, pow_mul]

/-- The independently constructed Euler index and actual field-orbit index agree. -/
theorem harcosExtensionMinpolyOrbits_eq_euler (n : ℕ) (hn : 0 < n) :
    harcosExtensionMinpolyOrbits p n = harcosEulerNonzeroPrimes p n := by
  ext k
  rw [harcos_mem_extensionMinpolyOrbits_iff p n hn k,
    mem_harcosEulerNonzeroPrimes n hn.ne' k]

/-- Actual extension-field character sums are the logarithmic coefficients of
the actual polynomial-character Euler series. -/
theorem harcosExtensionKloosterman_eq_eulerLogCoefficient (a b m : ZMod p)
    (n : ℕ) (hn : 0 < n) :
    harcosExtensionKloosterman p a b m n =
      harcosEulerLogCoefficient (harcosEtaHom (m * a) (m * b)).toMonoidHom n := by
  rw [harcosExtensionKloosterman_minpoly_sum_scaled p a b m n hn,
    harcosExtensionMinpolyOrbits_eq_euler p n hn,
    harcosEuler_character_eq_nonzeroPrime_sum (m * a) (m * b) n hn.ne']

/-- Harcos's Theorem 6 with explicitly constructed reciprocal roots, not an
assumed power-sum or Euler identity. -/
theorem harcosExtensionKloosterman_eq_reciprocalRoots (a b m : ZMod p)
    (ha : a ≠ 0) (hm : m ≠ 0) (n : ℕ) (hn : 0 < n) :
    harcosExtensionKloosterman p a b m n =
      -(harcosReciprocalRootPlus (m * a) (m * b) ^ n +
        harcosReciprocalRootMinus (m * a) (m * b) ^ n) := by
  rw [harcosExtensionKloosterman_eq_eulerLogCoefficient p a b m n hn]
  exact harcosEuler_character_reciprocalRoots (m * a) (m * b) (mul_ne_zero hm ha) n hn.ne'

end ExtensionSequence

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosPowerSum -/

/-!
# Finite power sums detect the modulus of every root

This supplies the growth-to-root-modulus implication used on page 1 of
Harcos, *Weil's bound for Kloosterman sums* (`pages/harcos-weil-01.png`).
Cesàro averages isolate all copies of a maximal-modulus root simultaneously;
their positive multiplicity prevents cancellation. No distinctness is needed.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Filter Finset
open scoped Topology

/-- Away from `1`, the Cesàro averages of powers in the closed unit disk tend to zero. -/
theorem harcos_cesaro_powers_tendsto_zero {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) :
    Tendsto (fun n : ℕ ↦ ((n : ℝ)⁻¹) • ∑ k ∈ range n, z ^ k)
      atTop (𝓝 0) := by
  have hbound (n : ℕ) :
      ‖((n : ℝ)⁻¹) • ∑ k ∈ range n, z ^ k‖ ≤
        (n : ℝ)⁻¹ * (2 / ‖z - 1‖) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), geom_sum_eq hz1, norm_div]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    calc
      ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 := by
        rw [norm_pow, norm_one]
        have := pow_le_one₀ (n := n) (norm_nonneg z) hz
        linarith
  apply squeeze_zero_norm hbound
  simpa using
    ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const
      (2 / ‖z - 1‖))

/-- Cesàro averaging retains precisely the copies of the root `1`. -/
theorem harcos_cesaro_powers_tendsto {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Tendsto (fun n : ℕ ↦ ((n : ℝ)⁻¹) • ∑ k ∈ range n, z ^ k)
      atTop (𝓝 (if z = 1 then 1 else 0)) := by
  classical
  by_cases hz1 : z = 1
  · subst z
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℂ)) atTop (𝓝 1)).cesaro_smul
  · simpa only [if_neg hz1] using harcos_cesaro_powers_tendsto_zero hz hz1

/-- A geometric bound on all sufficiently large power sums bounds every root.
The indexing map may have repetitions: maximal equal roots contribute their
positive integer multiplicity to a Cesàro limit, rather than canceling. -/
theorem harcos_norm_le_of_finset_power_sum_bound {ι : Type*} (s : Finset ι)
    (z : ι → ℂ) {R C : ℝ} (hR : 0 < R)
    (hbound : ∀ᶠ n : ℕ in atTop, ‖∑ i ∈ s, z i ^ n‖ ≤ C * R ^ n) :
    ∀ i ∈ s, ‖z i‖ ≤ R := by
  classical
  intro i hi
  by_contra hbad
  have hiR : R < ‖z i‖ := lt_of_not_ge hbad
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun k ↦ ‖z k‖) ⟨i, hi⟩
  have hjR : R < ‖z j‖ := hiR.trans_le (hmax i hi)
  have hjpos : 0 < ‖z j‖ := hR.trans hjR
  have hj0 : z j ≠ 0 := norm_pos_iff.mp hjpos
  have hratio : 0 ≤ R / ‖z j‖ := div_nonneg hR.le (norm_nonneg _)
  have hratio1 : R / ‖z j‖ < 1 := (div_lt_one hjpos).mpr hjR
  have hdecay : Tendsto (fun n : ℕ ↦ C * (R / ‖z j‖) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hratio hratio1).const_mul C
  have hzero : Tendsto (fun n : ℕ ↦ ∑ k ∈ s, (z k / z j) ^ n)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hdecay
    filter_upwards [hbound] with n hn
    calc
      ‖∑ k ∈ s, (z k / z j) ^ n‖ = ‖∑ k ∈ s, z k ^ n‖ / ‖z j‖ ^ n := by
        simp_rw [div_pow, div_eq_mul_inv]
        rw [← Finset.sum_mul, norm_mul, norm_inv, norm_pow]
      _ ≤ C * R ^ n / ‖z j‖ ^ n :=
        div_le_div_of_nonneg_right hn (by positivity)
      _ = C * (R / ‖z j‖) ^ n := by rw [div_pow]; ring
  have hterm (k : ι) (hk : k ∈ s) :
      Tendsto (fun n : ℕ ↦ ((n : ℝ)⁻¹) • ∑ m ∈ range n, (z k / z j) ^ m)
        atTop (𝓝 (if z k / z j = 1 then 1 else 0)) := by
    apply harcos_cesaro_powers_tendsto
    rw [norm_div]
    exact (div_le_one hjpos).mpr (hmax k hk)
  have hlimit := tendsto_finsetSum s hterm
  have hmeans :
      (fun n : ℕ ↦ ((n : ℝ)⁻¹) • ∑ m ∈ range n, ∑ k ∈ s, (z k / z j) ^ m) =
      (fun n : ℕ ↦ ∑ k ∈ s, ((n : ℝ)⁻¹) • ∑ m ∈ range n, (z k / z j) ^ m) := by
    funext n
    rw [Finset.sum_comm, Finset.smul_sum]
  have heq := tendsto_nhds_unique (hmeans ▸ hzero.cesaro_smul) hlimit
  rw [Finset.sum_boole] at heq
  have hcard : 0 < (s.filter (fun k ↦ z k / z j = 1)).card :=
    Finset.card_pos.mpr ⟨j, by simp [hj, hj0]⟩
  exact (Nat.ne_of_gt hcard) (by exact_mod_cast heq.symm)


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosPrimeWeil -/

/-!
# The odd-prime Kloosterman bound

The polynomial character, its quadratic generating series, the finite Euler
identity, the actual extension trace identity, and the Stepanov point bound
are all proved in the imported modules. Cesaro averaging converts the bound
on the total root power sum into individual bounds without losing multiplicity.
-/

noncomputable section

open Finset Filter

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

variable (p : ℕ) [Fact p.Prime]

theorem harcosReciprocalRoots_norm_le (hp2 : p ≠ 2) (a b : ZMod p)
    (ha : a ≠ 0) (hb : b ≠ 0) (m : ZMod p) (hm : m ≠ 0) :
    ‖harcosReciprocalRootPlus (m * a) (m * b)‖ ≤ Real.sqrt (p : ℝ) ∧
      ‖harcosReciprocalRootMinus (m * a) (m * b)‖ ≤ Real.sqrt (p : ℝ) := by
  let s := (univ : Finset (ZMod p)).erase 0 ×ˢ (univ : Finset Bool)
  let z : ZMod p × Bool → ℂ := fun i =>
    if i.2 then harcosReciprocalRootPlus (i.1 * a) (i.1 * b)
      else harcosReciprocalRootMinus (i.1 * a) (i.1 * b)
  have hsum (n : ℕ) (hn : 4 ≤ n) :
      (∑ i ∈ s, z i ^ n) =
        -(∑ k ∈ (univ : Finset (ZMod p)).erase 0,
          harcosExtensionKloosterman p a b k n) := by
    simp only [s, z, sum_product, Fintype.sum_bool, Bool.false_eq_true,
      if_false, if_true]
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro k hk
    rw [harcosExtensionKloosterman_eq_reciprocalRoots p a b k ha
      (mem_erase.mp hk).1 n (by omega), neg_neg]
  have hg : ∀ᶠ n : ℕ in atTop,
      ‖∑ i ∈ s, z i ^ n‖ ≤ (16 * (p : ℝ) + 1) * Real.sqrt (p : ℝ) ^ n := by
    filter_upwards [eventually_ge_atTop 4] with n hn
    rw [hsum n hn, norm_neg]
    exact harcosExtensionKloosterman_total_growth p hp2 a b ha hb n hn
  have hz := harcos_norm_le_of_finset_power_sum_bound s z
    (Real.sqrt_pos.mpr (show (0 : ℝ) < p by
      exact_mod_cast (Fact.out : p.Prime).pos)) hg
  exact ⟨hz (m, true) (by simp [s, hm]), hz (m, false) (by simp [s, hm])⟩

theorem harcosReciprocalRoots_norm_eq (hp2 : p ≠ 2) (a b : ZMod p)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖harcosReciprocalRootPlus a b‖ = Real.sqrt (p : ℝ) ∧
      ‖harcosReciprocalRootMinus a b‖ = Real.sqrt (p : ℝ) := by
  have hle := harcosReciprocalRoots_norm_le p hp2 a b ha hb 1 one_ne_zero
  simp only [one_mul] at hle
  have hprod := congrArg norm (harcosReciprocalRoots_mul_prime a b ha hb)
  rw [norm_mul, Complex.norm_natCast] at hprod
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ p by positivity)
  have hpos : 0 < Real.sqrt (p : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast (Fact.out : p.Prime).pos)
  have hl := mul_le_mul_of_nonneg_left hle.2
    (norm_nonneg (harcosReciprocalRootPlus a b))
  have hr := mul_le_mul_of_nonneg_right hle.1
    (norm_nonneg (harcosReciprocalRootMinus a b))
  constructor <;> nlinarith [hle.1, hle.2]

/-- Harcos's Theorem 1 for the actual complete sum, with an arbitrary integer
second frequency and no unproved Weil or root-power premise. -/
theorem completeKloosterman_odd_prime_weil (hp2 : p ≠ 2)
    (a : ZMod p) (d : ℤ) (ha : a ≠ 0) (hd : (d : ZMod p) ≠ 0) :
    ‖completeKloosterman p a d‖ ≤ 2 * Real.sqrt (p : ℝ) := by
  have hs : harcosReciprocalRootPlus a (d : ZMod p) +
      harcosReciprocalRootMinus a (d : ZMod p) = -completeKloosterman p a d := by
    rw [harcosReciprocalRoots_add, harcosCoefficient_one]
  have hn := harcosReciprocalRoots_norm_eq p hp2 a (d : ZMod p) ha hd
  calc
    ‖completeKloosterman p a d‖ =
        ‖harcosReciprocalRootPlus a (d : ZMod p) +
          harcosReciprocalRootMinus a (d : ZMod p)‖ := by rw [hs, norm_neg]
    _ ≤ ‖harcosReciprocalRootPlus a (d : ZMod p)‖ +
        ‖harcosReciprocalRootMinus a (d : ZMod p)‖ := norm_add_le _ _
    _ = _ := by rw [hn.1, hn.2]; ring

/-- The prime-modulus estimate, including `p = 2` and one zero frequency.
Both frequencies may be arbitrary signed integers; only their simultaneous
vanishing modulo the prime is excluded. -/
theorem completeKloosterman_prime_primitive_weil (a d : ℤ)
    (hprimitive : ¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ d) :
    ‖completeKloosterman p (a : ZMod p) d‖ ≤ 2 * Real.sqrt (p : ℝ) := by
  have hone : 1 ≤ Real.sqrt (p : ℝ) := Real.one_le_sqrt.mpr (by
    exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  by_cases hp2 : p = 2
  · subst p
    rw [completeKloosterman_eq_sum_units]
    calc
      _ ≤ ∑ u : (ZMod 2)ˣ, ‖ZMod.stdAddChar
        ((a : ZMod 2) * (u : ZMod 2) + (d : ZMod 2) * (↑u⁻¹ : ZMod 2))‖ :=
          norm_sum_le _ _
      _ = 1 := by simp only [stdAddChar_norm, sum_const, card_univ,
        ZMod.card_units, nsmul_eq_mul]; norm_num
      _ ≤ _ := by linarith
  by_cases ha : (a : ZMod p) = 0
  · have hd : ¬ (p : ℤ) ∣ d :=
      hprimitive.resolve_left (not_not.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp ha))
    rw [ha, completeKloosterman_prime_zero_left p d hd, norm_neg, norm_one]
    linarith
  by_cases hd : (d : ZMod p) = 0
  · have he : completeKloosterman p (a : ZMod p) d =
        completeKloosterman p (a : ZMod p) 0 := by
      simp only [completeKloosterman_eq, hd, Int.cast_zero]
    rw [he, completeKloosterman_prime_zero_frequency p _ ha, norm_neg, norm_one]
    linarith
  exact completeKloosterman_odd_prime_weil p hp2 (a : ZMod p) d ha hd

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryOddPrimePower -/

/-!
# Primitive Weil bounds for every power of an odd prime

The prime endpoint uses the accepted prime Weil theorem. Higher even exponents
use square-zero localization and unit-root rigidity; higher odd exponents use
the proved quadratic Gauss cancellation. Unequal prime valuations vanish.
All frequencies are arbitrary signed integers.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem oddPrimePower_modulus_congr (q r : ℕ) [NeZero q] [NeZero r]
    (h : q = r) (a d : ℤ) :
    completeKloosterman q (a : ZMod q) d = completeKloosterman r (a : ZMod r) d := by
  subst r
  rfl

private theorem oddPrimePower_unit_frequencies_sqrt (p k : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hk : 2 ≤ k) (a d : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (hd : ¬ (p : ℤ) ∣ d) :
    ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ ≤
      2 * Real.sqrt ((p ^ k : ℕ) : ℝ) := by
  rcases Nat.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩
  · have hrpos : 1 ≤ r := by omega
    subst k
    rw [oddPrimePower_modulus_congr _ _ (pow_add p r r) a d]
    have hs : Real.sqrt (((p ^ r * p ^ r : ℕ) : ℝ)) = (p : ℝ) ^ r := by
      rw [Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul_self (by positivity)]
    rw [pow_add, hs]
    exact completeKloosterman_odd_even_power_norm_le p r hp2 hrpos a d ha hd
  · have hrpos : 1 ≤ r := by omega
    subst k
    have hq : p ^ (2 * r + 1) = p * (p ^ r * p ^ r) := by
      rw [pow_succ, mul_comm 2 r, pow_mul, pow_two]
      ring
    rw [oddPrimePower_modulus_congr _ _ hq a d]
    have hs : Real.sqrt (((p * (p ^ r * p ^ r) : ℕ) : ℝ)) =
        (p : ℝ) ^ r * Real.sqrt (p : ℝ) := by
      rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg p),
        Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul_self (by positivity)]
      ring
    rw [hq, hs]
    simpa only [mul_assoc] using
      completeKloosterman_odd_odd_power_norm_le p r hp2 hrpos a d ha hd

/-- The sharp primitive local estimate at every positive exponent. -/
theorem completeKloosterman_odd_prime_power_primitive_sqrt (p k : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hk : 1 ≤ k) (a d : ℤ)
    (hprimitive : ¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ d) :
    ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ ≤
      2 * Real.sqrt ((p ^ k : ℕ) : ℝ) := by
  by_cases hk1 : k = 1
  · subst k
    rw [oddPrimePower_modulus_congr _ _ (pow_one p) a d]
    simpa only [pow_one] using completeKloosterman_prime_primitive_weil p a d hprimitive
  have hk2 : 2 ≤ k := by omega
  have hq : p ^ k = p * p ^ ((k - 2) + 1) := by
    rw [← pow_succ']
    congr 1
    omega
  by_cases ha : (p : ℤ) ∣ a
  · have hd := hprimitive.resolve_left (not_not.mpr ha)
    rw [oddPrimePower_modulus_congr _ _ hq a d,
      completeKloosterman_prime_power_vanish_left p (k - 2) a d ha hd, norm_zero]
    positivity
  by_cases hd : (p : ℤ) ∣ d
  · rw [oddPrimePower_modulus_congr _ _ hq a d,
      completeKloosterman_prime_power_vanish p (k - 2) a d ha hd, norm_zero]
    positivity
  exact oddPrimePower_unit_frequencies_sqrt p k hp2 hk2 a d ha hd

/-- The divisor-factor envelope, including the modulus-one endpoint `k = 0`.
This is the complete Kloosterman sum, not a conditional local-bound interface. -/
theorem completeKloosterman_odd_prime_power_primitive_weil (p k : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (a d : ℤ)
    (hprimitive : ¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ d) :
    ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ ≤
      ((k + 1 : ℕ) : ℝ) * Real.sqrt ((p ^ k : ℕ) : ℝ) := by
  rcases k with _ | k
  · rw [oddPrimePower_modulus_congr _ _ (pow_zero p) a d,
      completeKloosterman_modulus_one, norm_one]
    norm_num
  · refine (completeKloosterman_odd_prime_power_primitive_sqrt p (k + 1) hp2
      (by omega) a d hprimitive).trans ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show 2 ≤ k + 1 + 1 by omega))
      (Real.sqrt_nonneg _)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryTwoPowerRoots -/

/-!
# Four-root bound over powers of two

If two unit roots have equal squares modulo `2^(n+1)`, their reductions
modulo `2^n` agree up to sign. Each of these two reduction fibers has size
two. The proof uses only divisibility of the difference of squares.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem two_power_dvd_factor (n : ℕ) (x y : ℤ)
    (hx : ¬ 4 ∣ x) (hxy : (2 : ℤ) ^ (n + 1) ∣ x * y) :
    (2 : ℤ) ^ n ∣ y := by
  by_cases hx2 : (2 : ℤ) ∣ x
  · obtain ⟨z, rfl⟩ := hx2
    have hz : ¬ (2 : ℤ) ∣ z := by
      rintro ⟨w, rfl⟩
      apply hx
      exact ⟨w, by ring⟩
    have hh : (2 : ℤ) ^ n ∣ z * y := by
      apply (mul_dvd_mul_iff_left (show (2 : ℤ) ≠ 0 by norm_num)).mp
      simpa only [pow_succ', mul_assoc] using hxy
    exact Int.prime_two.pow_dvd_of_dvd_mul_left n hz hh
  · exact (pow_dvd_pow 2 (Nat.le_succ n)).trans
      (Int.prime_two.pow_dvd_of_dvd_mul_left (n + 1) hx2 hxy)

private theorem two_power_square_congruence (n : ℕ) (x y : ℤ)
    (hy : ¬ (2 : ℤ) ∣ y) (hxy : (2 : ℤ) ^ (n + 1) ∣ x ^ 2 - y ^ 2) :
    (2 : ℤ) ^ n ∣ x - y ∨ (2 : ℤ) ^ n ∣ x + y := by
  have hp : (2 : ℤ) ^ (n + 1) ∣ (x - y) * (x + y) := by
    convert hxy using 1
    ring
  by_cases hm : (4 : ℤ) ∣ x - y
  · have hn : ¬ (4 : ℤ) ∣ x + y := by
      intro hn
      obtain ⟨u, hu⟩ := hm
      obtain ⟨v, hv⟩ := hn
      exact hy ⟨v - u, by omega⟩
    exact Or.inl (two_power_dvd_factor n (x + y) (x - y) hn
      (by simpa only [mul_comm] using hp))
  · exact Or.inr (two_power_dvd_factor n (x - y) (x + y) hm hp)

/-- A unit quadratic congruence with odd leading coefficient has at most four
roots modulo any positive power of two. -/
theorem two_power_unit_quadratic_root_card_le_four (n : ℕ) (a d : ℤ)
    (ha : ¬ (2 : ℤ) ∣ a) :
    (univ.filter fun v : ZMod (2 ^ n * 2) ↦
      IsUnit v ∧ (a : ZMod (2 ^ n * 2)) * v ^ 2 = (d : ZMod (2 ^ n * 2))).card ≤
      4 := by
  classical
  let s := univ.filter fun v : ZMod (2 ^ n * 2) ↦
    IsUnit v ∧ (a : ZMod (2 ^ n * 2)) * v ^ 2 = (d : ZMod (2 ^ n * 2))
  let f := ZMod.castHom (Nat.dvd_mul_right (2 ^ n) 2) (ZMod (2 ^ n))
  by_cases hs : s.Nonempty
  · obtain ⟨v, hv⟩ := hs
    obtain ⟨y, rfl⟩ := ZMod.intCast_surjective v
    have hv' := (mem_filter.mp hv).2
    have hy : ¬ (2 : ℤ) ∣ y := by
      intro hy
      have hunit := hv'.1.map
        (ZMod.castHom (show 2 ∣ 2 ^ n * 2 from dvd_mul_left 2 _) (ZMod 2))
      have hz : (y : ZMod 2) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd y 2).mpr hy
      exact hunit.ne_zero (by simpa only [map_intCast] using hz)
    have hsub : s ⊆ univ.filter fun u ↦ f u ∈ ({f (y : ZMod (2 ^ n * 2)),
        -f (y : ZMod (2 ^ n * 2))} : Finset (ZMod (2 ^ n))) := by
      intro u hu
      obtain ⟨x, rfl⟩ := ZMod.intCast_surjective u
      have hu' := (mem_filter.mp hu).2
      have hz : ((a * (x ^ 2 - y ^ 2) : ℤ) : ZMod (2 ^ n * 2)) = 0 := by
        push_cast
        linear_combination hu'.2 - hv'.2
      have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
      have hsq : (2 : ℤ) ^ (n + 1) ∣ x ^ 2 - y ^ 2 := by
        apply Int.prime_two.pow_dvd_of_dvd_mul_left (n + 1) ha
        simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_succ] using hdvd
      have he := two_power_square_congruence n x y hy hsq
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
        f, map_intCast]
      rcases he with hm | hp
      · left
        apply sub_eq_zero.mp
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd (x - y) (2 ^ n)).mpr
          (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hm)
        simpa only [Int.cast_sub] using this
      · right
        apply eq_neg_iff_add_eq_zero.mpr
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd (x + y) (2 ^ n)).mpr
          (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hp)
        simpa only [Int.cast_add] using this
    have hc := card_le_card hsub
    rw [zmod_reduction_preimage_card] at hc
    have hcard : ({f (y : ZMod (2 ^ n * 2)),
        -f (y : ZMod (2 ^ n * 2))} : Finset (ZMod (2 ^ n))).card ≤ 2 :=
      (card_insert_le _ _).trans (by simp)
    exact hc.trans (Nat.mul_le_mul_right 2 hcard)
  · change s.card ≤ 4
    rw [not_nonempty_iff_eq_empty.mp hs]
    simp

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryTwoPower -/

/-!
# Primitive Kloosterman estimates at powers of two

The square-zero layer localizes the sum to unit quadratic roots modulo the
smaller half-power. Four roots and the exact size of the reduction fibers
suffice: the factor `k+1` absorbs the elementary stationary-phase constant.
No odd-characteristic Gauss-sum identity is used.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem two_power_modulus_congr (q r : ℕ) [NeZero q] [NeZero r]
    (h : q = r) (a d : ℤ) :
    completeKloosterman q (a : ZMod q) d =
      completeKloosterman r (a : ZMod r) d := by
  subst r
  rfl

private theorem two_power_layer_norm_le (q r : ℕ) [NeZero q] [NeZero r]
    (hqr : q ∣ r) (a d : ℤ) :
    ‖completeKloosterman (q * r) (a : ZMod (q * r)) d‖ ≤
      (r : ℝ) * ((univ.filter fun v : ZMod q ↦
        IsUnit v ∧ (a : ZMod q) * v ^ 2 = (d : ZMod q)).card : ℝ) := by
  classical
  let f := ZMod.castHom (Nat.dvd_mul_right q r) (ZMod q)
  let s := univ.filter fun v : ZMod q ↦
    IsUnit v ∧ (a : ZMod q) * v ^ 2 = (d : ZMod q)
  have ht : (r : ZMod (q * r)) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    obtain ⟨c, hc⟩ := hqr
    exact ⟨c, by rw [hc]; ring⟩
  have hloc := completeKloosterman_square_zero_localization (q * r)
    (a : ZMod (q * r)) (r : ZMod (q * r)) d ht
  simp only [zmod_mul_modulus_eq_zero_iff, map_sub, map_mul, map_pow, map_intCast,
    sub_eq_zero] at hloc
  have hnorm :
      ‖completeKloosterman (q * r) (a : ZMod (q * r)) d‖ ≤
        ((univ.filter fun u : ZMod (q * r) ↦
          IsUnit u ∧ (a : ZMod q) * (f u) ^ 2 = (d : ZMod q)).card : ℝ) := by
    rw [hloc]
    convert norm_sum_le univ (fun u : ZMod (q * r) ↦
      if IsUnit u ∧ (a : ZMod q) * (f u) ^ 2 = (d : ZMod q)
      then ZMod.stdAddChar ((a : ZMod (q * r)) * u + (d : ZMod (q * r)) * u⁻¹)
      else 0) using 1
    simp only [apply_ite norm, stdAddChar_norm, norm_zero, sum_boole]
  have hcard :
      (univ.filter fun u : ZMod (q * r) ↦
        IsUnit u ∧ (a : ZMod q) * (f u) ^ 2 = (d : ZMod q)).card ≤ s.card * r := by
    rw [← zmod_reduction_preimage_card]
    apply card_le_card
    intro u hu
    simp only [mem_filter, mem_univ, true_and, s] at hu ⊢
    exact ⟨hu.1.map f, hu.2⟩
  exact hnorm.trans (by exact_mod_cast hcard.trans_eq (Nat.mul_comm s.card r))

private theorem two_power_stationary_bound (n m : ℕ) (hn : 0 < n) (hnm : n ≤ m)
    (a d : ℤ) (ha : ¬ (2 : ℤ) ∣ a) :
    ‖completeKloosterman (2 ^ (n + m)) (a : ZMod (2 ^ (n + m))) d‖ ≤
      4 * (2 : ℝ) ^ m := by
  have hroot :
      (univ.filter fun v : ZMod (2 ^ n) ↦
        IsUnit v ∧ (a : ZMod (2 ^ n)) * v ^ 2 = (d : ZMod (2 ^ n))).card ≤ 4 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    convert! two_power_unit_quadratic_root_card_le_four j a d ha using 1
  have hl := two_power_layer_norm_le (2 ^ n) (2 ^ m) (pow_dvd_pow 2 hnm) a d
  suffices h : ‖completeKloosterman (2 ^ n * 2 ^ m)
      (a : ZMod (2 ^ n * 2 ^ m)) d‖ ≤ 4 * (2 : ℝ) ^ m by
    convert! h using 1
    exact congrArg norm (two_power_modulus_congr _ _ (pow_add 2 n m) a d)
  refine hl.trans ?_
  have hr : ((univ.filter fun v : ZMod (2 ^ n) ↦
      IsUnit v ∧ (a : ZMod (2 ^ n)) * v ^ 2 = (d : ZMod (2 ^ n))).card : ℝ) ≤ 4 :=
    by exact_mod_cast hroot
  simpa only [Nat.cast_pow, Nat.cast_ofNat, mul_comm] using
    mul_le_mul_of_nonneg_left hr (show (0 : ℝ) ≤ (2 ^ m : ℕ) by positivity)

private theorem two_power_trivial_norm_le (q : ℕ) [NeZero q] (a d : ℤ) :
    ‖completeKloosterman q (a : ZMod q) d‖ ≤ (q : ℝ) := by
  classical
  rw [completeKloosterman_eq]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _u : ZMod q, (1 : ℝ) := by
      apply sum_le_sum
      intro u _
      split_ifs <;> simp
    _ = (q : ℝ) := by simp

private theorem two_power_sqrt_even (n : ℕ) :
    Real.sqrt ((2 : ℝ) ^ (2 * n)) = (2 : ℝ) ^ n := by
  rw [mul_comm 2 n, pow_mul, Real.sqrt_sq (by positivity)]

private theorem two_power_sqrt_odd (n : ℕ) :
    Real.sqrt ((2 : ℝ) ^ (2 * n + 1)) = (2 : ℝ) ^ n * Real.sqrt 2 := by
  rw [pow_succ, Real.sqrt_mul (by positivity), two_power_sqrt_even]

private theorem two_power_odd_coefficient_bound :
    (8 : ℝ) ≤ 6 * Real.sqrt 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

private theorem two_power_primitive_odd_left (k : ℕ) (a d : ℤ)
    (ha : ¬ (2 : ℤ) ∣ a) :
    ‖completeKloosterman (2 ^ k) (a : ZMod (2 ^ k)) d‖ ≤
      ((k + 1 : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ k) := by
  by_cases hk : k < 4
  · have ht := two_power_trivial_norm_le (2 ^ k) a d
    have hs : (2 : ℝ) ^ k ≤ ((k + 1 : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ k) := by
      have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases hk' with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num only [pow_one, Nat.cast_add, Nat.cast_one]
        have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
        have hp := Real.sqrt_nonneg (2 : ℝ)
        nlinarith
      · norm_num [show Real.sqrt (4 : ℝ) = 2 from by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      · norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, pow_succ,
          pow_zero, one_mul]
        have h := Real.sq_sqrt (show (0 : ℝ) ≤ 8 by norm_num)
        have hp := Real.sqrt_nonneg (8 : ℝ)
        nlinarith
    exact ht.trans (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hs)
  · have hk4 : 4 ≤ k := by omega
    obtain ⟨n, he | ho⟩ := Nat.even_or_odd' k
    · subst k
      have hn : 2 ≤ n := by omega
      have ht := two_power_stationary_bound n n (by omega) le_rfl a d ha
      rw [show n + n = 2 * n by omega] at ht
      rw [two_power_sqrt_even]
      refine ht.trans ?_
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (show 4 ≤ 2 * n + 1 by omega)
    · subst k
      have hn : 2 ≤ n := by omega
      have ht := two_power_stationary_bound n (n + 1) (by omega) (by omega) a d ha
      rw [show n + (n + 1) = 2 * n + 1 by omega] at ht
      rw [two_power_sqrt_odd]
      refine ht.trans ?_
      have hc : (6 : ℝ) ≤ ((2 * n + 1 + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 6 ≤ 2 * n + 1 + 1)
      have hcoef := two_power_odd_coefficient_bound.trans
        (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg 2))
      calc
        4 * (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ n * 8 := by rw [pow_succ]; ring
        _ ≤ (2 : ℝ) ^ n * (((2 * n + 1 + 1 : ℕ) : ℝ) * Real.sqrt 2) :=
          mul_le_mul_of_nonneg_left hcoef (by positivity)
        _ = _ := by ring

/-- Primitive Weil-type bound at every power of two, including modulus one.
The elementary stationary bound is absorbed by the divisor factor `k+1`. -/
theorem completeKloosterman_two_power_primitive_weil (k : ℕ) (a d : ℤ)
    (hprimitive : ¬ (2 : ℤ) ∣ a ∨ ¬ (2 : ℤ) ∣ d) :
    ‖completeKloosterman (2 ^ k) (a : ZMod (2 ^ k)) d‖ ≤
      ((k + 1 : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ k) := by
  rcases hprimitive with ha | hd
  · exact two_power_primitive_odd_left k a d ha
  · rw [completeKloosterman_symm]
    exact two_power_primitive_odd_left k d a hd

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryLocalGlobalPrimePower -/

/-!
# Removing common prime factors from signed frequencies

The only analytic input is the primitive prime-power estimate. The descent
retains the totient correction at modulus one, so both zero frequencies and
arbitrary signed nonprimitive frequencies are included.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem localGlobal_completeKloosterman_congr_modulus (q r : ℕ) [NeZero q] [NeZero r]
    (h : q = r) (a d : ℤ) :
    completeKloosterman q (a : ZMod q) d = completeKloosterman r (a : ZMod r) d := by
  subst r
  rfl

theorem localGlobal_completeKloosterman_one (a d : ℤ) :
    completeKloosterman 1 (a : ZMod 1) d = 1 := by
  rw [completeKloosterman_eq_sum_units]
  have hz (z : ZMod 1) : z = 0 := Subsingleton.elim _ _
  simp [hz]

theorem localGlobal_prime_power_descent_norm (p k : ℕ) [Fact p.Prime] (a d : ℤ) :
    ‖completeKloosterman (p ^ (k + 1)) ((p * a : ℤ) : ZMod (p ^ (k + 1)))
        (p * d)‖ ≤
      (p : ℝ) * ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ := by
  have hp : p.Prime := Fact.out
  have hφ : (p ^ (k + 1)).totient ≤ p * (p ^ k).totient := by
    cases k with
    | zero => simpa using Nat.totient_le p
    | succ k =>
      rw [Nat.totient_prime_pow_succ hp, Nat.totient_prime_pow_succ hp, pow_succ]
      exact le_of_eq (by ring)
  have hpos : (0 : ℝ) < (p ^ k).totient := by
    exact_mod_cast Nat.totient_pos.mpr (pow_pos hp.pos k)
  have hs : completeKloosterman (p ^ (k + 1)) ((p * a : ℤ) : ZMod (p ^ (k + 1)))
      (p * d) = ((p ^ (k + 1)).totient : ℂ) / ((p ^ k).totient : ℂ) *
        completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d := by
    rw [localGlobal_completeKloosterman_congr_modulus _ _ (pow_succ p k),
      completeKloosterman_common_factor]
    rw [pow_succ]
  rw [hs, norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply (div_le_iff₀ hpos).mpr
  exact_mod_cast hφ

theorem localGlobal_gcd_scale (p n : ℕ) (a d : ℤ) :
    (p * n).gcd ((p * a : ℤ).natAbs.gcd (p * d : ℤ).natAbs) =
      p * n.gcd (a.natAbs.gcd d.natAbs) := by
  simp only [Int.natAbs_mul, Int.natAbs_natCast, Nat.gcd_mul_left]

theorem localGlobal_sqrt_scale (p n g : ℕ) :
    Real.sqrt (p * g : ℕ) * Real.sqrt (p * n : ℕ) =
      (p : ℝ) * Real.sqrt g * Real.sqrt n := by
  simp only [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg p)]
  calc
    _ = (Real.sqrt p * Real.sqrt p) * (Real.sqrt g * Real.sqrt n) := by ring
    _ = _ := by rw [Real.mul_self_sqrt (Nat.cast_nonneg p)]; ring

/-- Exact all-frequency prime-power reduction. The primitive input is explicit,
and is not being asserted as an unconditional analytic theorem here. -/
theorem completeKloosterman_prime_power_weil_of_primitive
    (p : ℕ) [Fact p.Prime]
    (hlocal : ∀ (k : ℕ) (a d : ℤ), (¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ d) →
      ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ ≤
        ((k + 1 : ℕ) : ℝ) * Real.sqrt (p ^ k : ℕ))
    (k : ℕ) (a d : ℤ) :
    ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ ≤
      ((k + 1 : ℕ) : ℝ) * Real.sqrt ((p ^ k).gcd (a.natAbs.gcd d.natAbs)) *
        Real.sqrt (p ^ k : ℕ) := by
  induction k generalizing a d with
  | zero =>
    rw [localGlobal_completeKloosterman_congr_modulus _ _ (pow_zero p),
      localGlobal_completeKloosterman_one]
    simp
  | succ k ih =>
    by_cases hprimitive : ¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ d
    · apply (hlocal (k + 1) a d hprimitive).trans
      have hg : (1 : ℝ) ≤ Real.sqrt ((p ^ (k + 1)).gcd (a.natAbs.gcd d.natAbs)) :=
        Real.one_le_sqrt.mpr (by
          exact_mod_cast Nat.gcd_pos_of_pos_left (a.natAbs.gcd d.natAbs)
            (pow_pos (Fact.out : p.Prime).pos (k + 1)))
      have hs := mul_le_mul_of_nonneg_left hg
        (show (0 : ℝ) ≤ ((k + 1 + 1 : ℕ) : ℝ) by positivity)
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (p ^ (k + 1) : ℕ))
    · obtain ⟨a', rfl⟩ := (not_or.mp hprimitive).1 |> not_not.mp
      obtain ⟨d', rfl⟩ := (not_or.mp hprimitive).2 |> not_not.mp
      calc
        _ ≤ (p : ℝ) * ‖completeKloosterman (p ^ k) (a' : ZMod (p ^ k)) d'‖ :=
          localGlobal_prime_power_descent_norm p k a' d'
        _ ≤ (p : ℝ) * (((k + 1 : ℕ) : ℝ) *
            Real.sqrt ((p ^ k).gcd (a'.natAbs.gcd d'.natAbs)) *
            Real.sqrt (p ^ k : ℕ)) :=
          mul_le_mul_of_nonneg_left (ih a' d') (Nat.cast_nonneg p)
        _ = ((k + 1 : ℕ) : ℝ) *
            (Real.sqrt ((p ^ (k + 1)).gcd
              ((p * a' : ℤ).natAbs.gcd (p * d' : ℤ).natAbs)) *
              Real.sqrt (p ^ (k + 1) : ℕ)) := by
          rw [pow_succ', localGlobal_gcd_scale, localGlobal_sqrt_scale]
          ring
        _ ≤ _ := by
          rw [mul_assoc]
          gcongr
          exact_mod_cast Nat.le_succ k

theorem localGlobal_card_divisors_prime_power (p k : ℕ) [Fact p.Prime] :
    (p ^ k).divisors.card = k + 1 := by
  simp [Nat.divisors_prime_pow (Fact.out : p.Prime)]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryLocalGlobal -/

/-!
# From primitive prime powers to every nonzero modulus

Chinese remaindering twists both frequencies by a Bezout coefficient. Its
coprimality with the corresponding modulus preserves the full three-way gcd.
Together with exact common-factor descent this proves the all-modulus estimate
from a single explicitly quantified primitive prime-power input.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem localGlobal_bezout_coprime (m n : ℕ) (h : m.Coprime n) :
    m.Coprime (m.gcdB n).natAbs ∧ n.Coprime (m.gcdA n).natAbs := by
  have he : (m : ℤ) * m.gcdA n + (n : ℤ) * m.gcdB n = 1 := by
    simpa only [h.gcd_eq_one, Nat.cast_one] using (Nat.gcd_eq_gcd_ab m n).symm
  have hb : IsCoprime (m : ℤ) (m.gcdB n) :=
    ⟨m.gcdA n, (n : ℤ), by simpa only [mul_comm] using he⟩
  have ha : IsCoprime (n : ℤ) (m.gcdA n) :=
    ⟨m.gcdB n, (m : ℤ), by simpa only [mul_comm, add_comm] using he⟩
  constructor
  · simpa only [Nat.coprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast] using
      Int.isCoprime_iff_gcd_eq_one.mp hb
  · simpa only [Nat.coprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast] using
      Int.isCoprime_iff_gcd_eq_one.mp ha

theorem localGlobal_gcd_twist (q : ℕ) (b a d : ℤ) (hb : q.Coprime b.natAbs) :
    q.gcd ((a * b).natAbs.gcd (d * b).natAbs) = q.gcd (a.natAbs.gcd d.natAbs) := by
  rw [Int.natAbs_mul, Int.natAbs_mul, Nat.gcd_mul_right]
  exact hb.symm.gcd_mul_right_cancel_right _

theorem localGlobal_gcd_coprime_mul (m n g : ℕ) (h : m.Coprime n) :
    (m * n).gcd g = m.gcd g * n.gcd g := by
  simpa only [Nat.gcd_comm] using h.gcd_mul g

theorem localGlobal_weil_envelope_mul (m n g : ℕ) (h : m.Coprime n) :
    ((m * n).divisors.card : ℝ) * Real.sqrt ((m * n).gcd g) * Real.sqrt (m * n : ℕ) =
      ((m.divisors.card : ℝ) * Real.sqrt (m.gcd g) * Real.sqrt m) *
        ((n.divisors.card : ℝ) * Real.sqrt (n.gcd g) * Real.sqrt n) := by
  rw [h.card_divisors_mul, localGlobal_gcd_coprime_mul m n g h]
  simp only [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg (m.gcd g)),
    Real.sqrt_mul (Nat.cast_nonneg m)]
  ring

/-- Conditional all-modulus Weil bound, with signed frequencies, modulus one,
and zero or nonprimitive frequencies. Only primitive prime-power bounds are
assumed; coprime assembly and common-factor descent are proved. -/
theorem completeKloosterman_weil_of_primitive_prime_power
    (hlocal : ∀ (p k : ℕ) (_ : Fact p.Prime) (a d : ℤ),
      (¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ d) →
      ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ ≤
        ((k + 1 : ℕ) : ℝ) * Real.sqrt (p ^ k : ℕ))
    (q : ℕ) [NeZero q] (a d : ℤ) :
    ‖completeKloosterman q (a : ZMod q) d‖ ≤
      (q.divisors.card : ℝ) * Real.sqrt (q.gcd (a.natAbs.gcd d.natAbs)) * Real.sqrt q := by
  have hall : ∀ (q : ℕ) (_ : NeZero q) (a d : ℤ),
      ‖completeKloosterman q (a : ZMod q) d‖ ≤
        (q.divisors.card : ℝ) * Real.sqrt (q.gcd (a.natAbs.gcd d.natAbs)) *
          Real.sqrt q := by
    refine Nat.recOnPrimeCoprime ?_ ?_ ?_
    · intro hq
      exact False.elim (hq.out rfl)
    · intro p k hp hq a d
      let : Fact p.Prime := ⟨hp⟩
      rw [localGlobal_card_divisors_prime_power]
      exact completeKloosterman_prime_power_weil_of_primitive p
        (fun k a d ↦ hlocal p k inferInstance a d) k a d
    · intro m n hm hn hmn hmBound hnBound hq a d
      let : NeZero m := ⟨by omega⟩
      let : NeZero n := ⟨by omega⟩
      have htwist := localGlobal_bezout_coprime m n hmn
      rw [completeKloosterman_crt m n hmn, norm_mul]
      have hleft := hmBound inferInstance (a * m.gcdB n) (d * m.gcdB n)
      have hright := hnBound inferInstance (a * m.gcdA n) (d * m.gcdA n)
      rw [localGlobal_gcd_twist m _ a d htwist.1] at hleft
      rw [localGlobal_gcd_twist n _ a d htwist.2] at hright
      rw [localGlobal_weil_envelope_mul m n _ hmn]
      exact mul_le_mul hleft hright (norm_nonneg _) (by positivity)
  exact hall q inferInstance a d

/-- The residue-valued interface used by the existing Weil-to-Fouvry bridge. -/
theorem completeKloosterman_weil_zmod_of_primitive_prime_power
    (hlocal : ∀ (p k : ℕ) (_ : Fact p.Prime) (a d : ℤ),
      (¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ d) →
      ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ ≤
        ((k + 1 : ℕ) : ℝ) * Real.sqrt (p ^ k : ℕ))
    (q : ℕ) [NeZero q] (m : ZMod q) (d : ℤ) :
    ‖completeKloosterman q m d‖ ≤
      (q.divisors.card : ℝ) * Real.sqrt (q.gcd (m.val.gcd d.natAbs)) * Real.sqrt q := by
  simpa only [Int.natAbs_natCast, Int.cast_natCast, ZMod.natCast_zmod_val] using
    completeKloosterman_weil_of_primitive_prime_power hlocal q (m.val : ℤ) d

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDivisorMean -/

/-!
# Fixed-order divisor means and coefficient square sums

The actual ordered divisor function is the Dirichlet convolution power `ζ ^ k`.
The mean estimate uses only the elementary hyperbola identity and the harmonic
sum bound. The square majorant is unrestricted: no squarefree support is needed.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Finset

/-- The ordered `k`-fold divisor function, with the usual value zero at zero. -/
def fouvryTau (k : ℕ) : ArithmeticFunction ℕ := ArithmeticFunction.zeta ^ k

@[simp] theorem fouvryTau_zero (k : ℕ) : fouvryTau k 0 = 0 :=
  ArithmeticFunction.map_zero

theorem fouvryTau_multiplicative (k : ℕ) : (fouvryTau k).IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_zeta.pow

@[simp] theorem fouvryTau_one (k : ℕ) : fouvryTau k 1 = 1 :=
  (fouvryTau_multiplicative k).map_one

theorem fouvryTau_order_one {n : ℕ} (hn : n ≠ 0) : fouvryTau 1 n = 1 := by
  simp [fouvryTau, ArithmeticFunction.zeta_apply, hn]

theorem fouvryTau_succ (k n : ℕ) :
    fouvryTau (k + 1) n = ∑ d ∈ n.divisors, fouvryTau k d := by
  exact ArithmeticFunction.coe_mul_zeta_apply (f := fouvryTau k)

theorem fouvryTau_two (n : ℕ) : fouvryTau 2 n = n.divisors.card := by
  rw [show 2 = 1 + 1 from rfl, fouvryTau_succ]
  trans ∑ _d ∈ n.divisors, 1
  · exact sum_congr rfl (fun d hd => fouvryTau_order_one (Nat.pos_of_mem_divisors hd).ne')
  · simp

theorem fouvryTau_prime_pow {p : ℕ} (hp : p.Prime) (k a : ℕ) :
    fouvryTau k (p ^ a) = k.multichoose a := by
  induction k generalizing a with
  | zero =>
    cases a with
    | zero => simp
    | succ a =>
      simp [fouvryTau, hp.ne_one]
  | succ k ih =>
    rw [fouvryTau_succ, Nat.sum_divisors_prime_pow hp]
    simp_rw [ih]
    rw [Nat.sum_range_multichoose, Nat.multichoose_eq]
    rw [show k + 1 + a - 1 = a + k by omega]
    exact Nat.choose_symm_of_eq_add (by omega)

private theorem multichoose_step (k a : ℕ) :
    k.multichoose (a + 1) * (a + 1) = k.multichoose a * (k + a) := by
  cases k with
  | zero => cases a <;> simp
  | succ k =>
    simp only [Nat.multichoose_eq]
    rw [show k + 1 + (a + 1) - 1 = k + a + 1 by omega,
      show k + 1 + a - 1 = k + a by omega,
      show k + 1 + a = k + a + 1 by omega]
    exact (Nat.add_one_mul_choose_eq (k + a) a).symm.trans (Nat.mul_comm _ _)

private theorem multichoose_mul_le (k l a : ℕ) :
    k.multichoose a * l.multichoose a ≤ (k * l).multichoose a := by
  cases k with
  | zero => cases a <;> simp
  | succ k =>
    cases l with
    | zero => cases a <;> simp
    | succ l =>
    induction a with
    | zero => simp
    | succ a ih =>
      have hstep := multichoose_step (k + 1) a
      have hstep' := multichoose_step (l + 1) a
      have hstep'' := multichoose_step ((k + 1) * (l + 1)) a
      have hratio : (k + 1 + a) * (l + 1 + a) ≤
          ((k + 1) * (l + 1) + a) * (a + 1) := by
        nlinarith [Nat.zero_le (a * k * l)]
      apply le_of_mul_le_mul_right (a := (a + 1) ^ 2) _ (by positivity)
      calc
        (k + 1).multichoose (a + 1) * (l + 1).multichoose (a + 1) * (a + 1) ^ 2 =
            ((k + 1).multichoose a * (l + 1).multichoose a) *
              ((k + 1 + a) * (l + 1 + a)) := by
              calc
                _ = ((k + 1).multichoose (a + 1) * (a + 1)) *
                    ((l + 1).multichoose (a + 1) * (a + 1)) := by ring
                _ = _ := by rw [hstep, hstep']; ring
        _ ≤ ((k + 1) * (l + 1)).multichoose a *
            (((k + 1) * (l + 1) + a) * (a + 1)) := Nat.mul_le_mul ih hratio
        _ = ((k + 1) * (l + 1)).multichoose (a + 1) * (a + 1) ^ 2 := by
              rw [← mul_assoc, ← hstep'']
              ring
        _ ≤ _ := le_rfl

/-- Products of divisor coefficients are dominated with explicit multiplied
order. This holds without any squarefree restriction. -/
theorem fouvryTau_mul_le (k l n : ℕ) :
    fouvryTau k n * fouvryTau l n ≤ fouvryTau (k * l) n := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  rw [(fouvryTau_multiplicative k).multiplicative_factorization _ hn,
    (fouvryTau_multiplicative l).multiplicative_factorization _ hn,
    (fouvryTau_multiplicative (k * l)).multiplicative_factorization _ hn]
  simp only [Finsupp.prod, Nat.support_factorization]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod'
  intro p hp
  simp only [fouvryTau_prime_pow (Nat.prime_of_mem_primeFactors hp)]
  exact multichoose_mul_le _ _ _

/-- The sharp fixed-order square majorant holds for every integer, not merely
for squarefree integers. -/
theorem fouvryTau_sq_le (k n : ℕ) : fouvryTau k n ^ 2 ≤ fouvryTau (k ^ 2) n := by
  simpa only [pow_two] using fouvryTau_mul_le k k n

/-- All integral moments have an explicit divisor-function majorant. The
nonzero hypothesis is needed only for the zeroth moment. -/
theorem fouvryTau_pow_le (k r : ℕ) {n : ℕ} (hn : n ≠ 0) :
    fouvryTau k n ^ r ≤ fouvryTau (k ^ r) n := by
  induction r with
  | zero => simp [fouvryTau_order_one hn]
  | succ r ih =>
    calc
      _ = fouvryTau k n ^ r * fouvryTau k n := pow_succ _ _
      _ ≤ fouvryTau (k ^ r) n * fouvryTau k n := Nat.mul_le_mul_right _ ih
      _ ≤ fouvryTau (k ^ r * k) n := fouvryTau_mul_le _ _ _
      _ = _ := by rw [pow_succ]

/-- A divisor-sum consequence of `∑ d ∣ n, φ(d) = n`. -/
theorem le_totient_mul_fouvryTau_two (n : ℕ) :
    n ≤ n.totient * fouvryTau 2 n := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  calc
    n = ∑ d ∈ n.divisors, d.totient := (Nat.sum_totient n).symm
    _ ≤ ∑ _d ∈ n.divisors, n.totient := by
      apply sum_le_sum
      intro d hd
      exact Nat.le_of_dvd (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn))
        (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
    _ = n.totient * fouvryTau 2 n := by simp [fouvryTau_two, Nat.mul_comm]

/-- Replace a totient denominator by an ordinary reciprocal while doubling
the fixed divisor order. -/
theorem fouvryTau_div_totient_le (k n : ℕ) :
    (fouvryTau k n : ℝ) / n.totient ≤ (fouvryTau (2 * k) n : ℝ) / n := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hφpos : (0 : ℝ) < n.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)
  have hbound : (n : ℝ) ≤ (n.totient : ℝ) * fouvryTau 2 n := by
    exact_mod_cast le_totient_mul_fouvryTau_two n
  have hprod : (fouvryTau 2 n : ℝ) * fouvryTau k n ≤ fouvryTau (2 * k) n := by
    exact_mod_cast fouvryTau_mul_le 2 k n
  apply (div_le_div_iff₀ hφpos hnpos).mpr
  calc
    (fouvryTau k n : ℝ) * n ≤
        (fouvryTau k n : ℝ) * (n.totient * (fouvryTau 2 n : ℝ)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = ((fouvryTau 2 n : ℝ) * fouvryTau k n) * n.totient := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hprod hφpos.le

private noncomputable def reciprocalSum (N : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 N, (d : ℝ)⁻¹

private theorem reciprocalSum_nonneg (N : ℕ) : 0 ≤ reciprocalSum N :=
  Finset.sum_nonneg (fun _ _ => by positivity)

private theorem reciprocalSum_mono {M N : ℕ} (h : M ≤ N) :
    reciprocalSum M ≤ reciprocalSum N :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right h)
    (fun _ _ _ => by positivity)

private theorem reciprocalSum_le_log (N : ℕ) :
    reciprocalSum N ≤ 1 + Real.log N := by
  convert harmonic_le_one_add_log N using 1
  have heq : Ioc 0 N = Icc 1 N := by ext; simp only [mem_Ioc, mem_Icc]; omega
  simp [reciprocalSum, harmonic_eq_sum_Icc, heq]

private noncomputable def reciprocalTau (k : ℕ) : ArithmeticFunction ℝ where
  toFun n := (fouvryTau k n : ℝ) / n
  map_zero' := by simp

private theorem reciprocalTau_succ (k : ℕ) :
    reciprocalTau (k + 1) = reciprocalTau k * reciprocalTau 1 := by
  ext n
  change (fouvryTau (k + 1) n : ℝ) / n = _
  rw [show fouvryTau (k + 1) = fouvryTau k * fouvryTau 1 by
    change ArithmeticFunction.zeta ^ (k + 1) =
      ArithmeticFunction.zeta ^ k * ArithmeticFunction.zeta ^ 1
    rw [pow_one, pow_succ]]
  rw [ArithmeticFunction.mul_apply, Nat.cast_sum, sum_div, ArithmeticFunction.mul_apply]
  apply sum_congr rfl
  intro d hd
  have heq : (n : ℝ) = (d.1 : ℝ) * d.2 := by
    exact_mod_cast (Nat.mem_divisorsAntidiagonal.mp hd).1.symm
  change ((fouvryTau k d.1 * fouvryTau 1 d.2 : ℕ) : ℝ) / n =
    ((fouvryTau k d.1 : ℝ) / d.1) * ((fouvryTau 1 d.2 : ℝ) / d.2)
  rw [heq, Nat.cast_mul, div_mul_div_comm]

private theorem sum_reciprocalTau_le (k N : ℕ) :
    (∑ n ∈ Ioc 0 N, reciprocalTau k n) ≤ reciprocalSum N ^ k := by
  induction k with
  | zero =>
    simp only [reciprocalTau, fouvryTau, pow_zero, ArithmeticFunction.one_apply]
    simp [ite_div]
    split_ifs <;> norm_num
  | succ k ih =>
    rw [reciprocalTau_succ, ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter]
    calc
      _ ≤ ∑ d ∈ Ioc 0 N ×ˢ Ioc 0 N, reciprocalTau k d.1 * reciprocalTau 1 d.2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun d _ _ => by
            change 0 ≤ ((fouvryTau k d.1 : ℝ) / d.1) *
              ((fouvryTau 1 d.2 : ℝ) / d.2)
            positivity)
      _ = (∑ d ∈ Ioc 0 N, reciprocalTau k d) * reciprocalSum N := by
        rw [sum_product, reciprocalSum, sum_mul_sum]
        apply sum_congr rfl
        intro d _
        apply sum_congr rfl
        intro e he
        change _ * ((fouvryTau 1 e : ℝ) / e) = _ * (e : ℝ)⁻¹
        rw [fouvryTau_order_one (mem_Ioc.mp he).1.ne', Nat.cast_one, one_div]
      _ ≤ reciprocalSum N ^ (k + 1) := by
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_right ih (reciprocalSum_nonneg _)


/-- Reciprocal divisor means at a real endpoint. -/
theorem sum_fouvryTau_div_le_real (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, (fouvryTau k n : ℝ) / n) ≤ (1 + Real.log x) ^ k := by
  have heq : reciprocalSum ⌊x⌋₊ = (harmonic ⌊x⌋₊ : ℝ) := by
    have hI : Ioc 0 ⌊x⌋₊ = Icc 1 ⌊x⌋₊ := by
      ext; simp only [mem_Ioc, mem_Icc]; omega
    simp [reciprocalSum, harmonic_eq_sum_Icc, hI]
  exact (sum_reciprocalTau_le k ⌊x⌋₊).trans
    (pow_le_pow_left₀ (reciprocalSum_nonneg _)
      (heq ▸ harmonic_floor_le_one_add_log x hx) _)

/-- A global totient-weighted divisor mean, with no order-dependent
implicit constant. -/
theorem sum_fouvryTau_div_totient_le_real (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, (fouvryTau k n : ℝ) / n.totient) ≤
      (1 + Real.log x) ^ (2 * k) := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, (fouvryTau (2 * k) n : ℝ) / n :=
      sum_le_sum (fun n _ => fouvryTau_div_totient_le k n)
    _ ≤ _ := sum_fouvryTau_div_le_real _ hx


private theorem sum_fouvryTau_le_harmonic (k N : ℕ) :
    (∑ n ∈ Ioc 0 N, (fouvryTau (k + 1) n : ℝ)) ≤
      N * reciprocalSum N ^ k := by
  induction k generalizing N with
  | zero =>
    simp only [zero_add, pow_zero, mul_one]
    have : ∑ n ∈ Ioc 0 N, fouvryTau 1 n = N := by
      simpa [fouvryTau] using ArithmeticFunction.sum_Ioc_zeta N
    exact_mod_cast this.le
  | succ k ih =>
    have hrec : ∑ n ∈ Ioc 0 N, fouvryTau (k + 1 + 1) n =
        ∑ d ∈ Ioc 0 N, ∑ n ∈ Ioc 0 (N / d), fouvryTau (k + 1) n := by
      change (∑ n ∈ Ioc 0 N,
        (ArithmeticFunction.zeta ^ (k + 1 + 1)) n) = _
      rw [pow_succ', ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
      apply sum_congr rfl
      intro d hd
      rw [ArithmeticFunction.zeta_apply_ne (mem_Ioc.mp hd).1.ne', one_mul]
      rfl
    rw [show (∑ n ∈ Ioc 0 N, (fouvryTau (k + 1 + 1) n : ℝ)) =
        ∑ d ∈ Ioc 0 N, ∑ n ∈ Ioc 0 (N / d), (fouvryTau (k + 1) n : ℝ) by
          exact_mod_cast hrec]
    calc
      _ ≤ ∑ d ∈ Ioc 0 N, (N / d : ℕ) * reciprocalSum (N / d) ^ k :=
        sum_le_sum (fun d _ => ih (N / d))
      _ ≤ ∑ d ∈ Ioc 0 N, ((N : ℝ) / d) * reciprocalSum N ^ k := by
        apply sum_le_sum
        intro d hd
        apply mul_le_mul
        · exact Nat.cast_div_le
        · exact pow_le_pow_left₀ (reciprocalSum_nonneg _) (reciprocalSum_mono (Nat.div_le_self _ _)) _
        · exact pow_nonneg (reciprocalSum_nonneg _) _
        · positivity
      _ = N * reciprocalSum N ^ (k + 1) := by
        simp only [div_eq_mul_inv, ← sum_mul, ← mul_sum, reciprocalSum, pow_succ]
        ring

/-- The global mean has logarithm exponent exactly one less than the order. -/
theorem sum_fouvryTau_le (k N : ℕ) :
    (∑ n ∈ Ioc 0 N, (fouvryTau (k + 1) n : ℝ)) ≤
      N * (1 + Real.log N) ^ k := by
  refine (sum_fouvryTau_le_harmonic k N).trans ?_
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (reciprocalSum_nonneg _) (reciprocalSum_le_log _) _) (by positivity)

/-- Real-endpoint form, uniform in `x`, with the order kept explicit. -/
theorem sum_fouvryTau_le_real {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, (fouvryTau k n : ℝ)) ≤
      x * (1 + Real.log x) ^ (k - 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hfloor : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  have hlog : 1 + Real.log (⌊x⌋₊ : ℝ) ≤ 1 + Real.log x := by
    have := Real.log_le_log (by exact_mod_cast (show 0 < ⌊x⌋₊ by omega))
      (Nat.floor_le (by linarith : 0 ≤ x))
    linarith
  have hnonneg : 0 ≤ 1 + Real.log (⌊x⌋₊ : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast hfloor)
    linarith
  simpa only [Nat.succ_sub_one] using
    (sum_fouvryTau_le j ⌊x⌋₊).trans
      (mul_le_mul (Nat.floor_le (by linarith)) (pow_le_pow_left₀ hnonneg hlog j)
        (pow_nonneg hnonneg j) (by linarith : 0 ≤ x))

/-- Every fixed integral moment has a global logarithmic bound. -/
theorem sum_fouvryTau_pow_le_real {k : ℕ} (hk : 1 ≤ k) (r : ℕ)
    {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, (fouvryTau k n : ℝ) ^ r) ≤
      x * (1 + Real.log x) ^ (k ^ r - 1) := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, (fouvryTau (k ^ r) n : ℝ) := by
      apply sum_le_sum
      intro n hn
      exact_mod_cast fouvryTau_pow_le k r (mem_Ioc.mp hn).1.ne'
    _ ≤ _ := sum_fouvryTau_le_real (Nat.one_le_pow r k hk) hx

/-- Unrestricted second moment with logarithm exponent `k² - 1`. -/
theorem sum_fouvryTau_sq_le_real {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, (fouvryTau k n : ℝ) ^ 2) ≤
      x * (1 + Real.log x) ^ (k ^ 2 - 1) := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, (fouvryTau (k ^ 2) n : ℝ) := by
      apply sum_le_sum
      intro n _
      exact_mod_cast fouvryTau_sq_le k n
    _ ≤ _ := sum_fouvryTau_le_real (by nlinarith) hx

/-- The coefficient square sum required by dispersion, for arbitrary finite
support and signed coefficients dominated by the actual divisor function. -/
theorem sum_alpha_sq_le_fouvryTau {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 1 ≤ x)
    (S : Finset ℕ) (hS : S ⊆ Ioc 0 ⌊x⌋₊) (α : ℕ → ℝ)
    (hα : ∀ n ∈ S, |α n| ≤ (fouvryTau k n : ℝ)) :
    (∑ n ∈ S, α n ^ 2) ≤ x * (1 + Real.log x) ^ (k ^ 2 - 1) := by
  calc
    _ ≤ ∑ n ∈ S, (fouvryTau k n : ℝ) ^ 2 := by
      apply sum_le_sum
      intro n hn
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (α n)) (hα n hn) 2
    _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, (fouvryTau k n : ℝ) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => sq_nonneg _)
    _ ≤ _ := sum_fouvryTau_sq_le_real hk hx

/-- Direct dyadic alpha payment; the constant is independent of the scale,
the finite support, and the coefficients. -/
theorem sum_alpha_sq_dyadic_le {k : ℕ} (hk : 1 ≤ k) {M : ℝ} (hM : 1 ≤ M)
    (S : Finset ℕ) (hS : ∀ n ∈ S, M ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * M)
    (α : ℕ → ℝ) (hα : ∀ n ∈ S, |α n| ≤ (fouvryTau k n : ℝ)) :
    (∑ n ∈ S, α n ^ 2) ≤ 2 * M * (1 + Real.log (2 * M)) ^ (k ^ 2 - 1) := by
  apply sum_alpha_sq_le_fouvryTau hk (by linarith : 1 ≤ 2 * M) S _ α hα
  intro n hn
  have h := hS n hn
  apply mem_Ioc.mpr
  constructor
  · have : (0 : ℝ) < n := by linarith
    exact_mod_cast this
  · exact Nat.le_floor h.2

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWeilBridge -/

/-!
# The exact interval and gcd form of the conditional Weil-to-Fouvry bridge

The complete Kloosterman estimate is an explicit hypothesis, not a proved
input. The interval conversion and the divisor/logarithm payment are proved.
-/

noncomputable section

open Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

variable {q : ℕ} [NeZero q]

def reciprocalInterval (q : ℕ) [NeZero q] (d : ℤ) (X Y : ℝ) : ℂ :=
  ∑ c ∈ Ioc ⌊X⌋ ⌊Y⌋, reciprocalPhase q d (c : ZMod q)


theorem reciprocalInterval_eq_incomplete (d : ℤ) {X Y : ℝ} (hXY : X ≤ Y) :
    reciprocalInterval q d X Y =
      incompleteReciprocal q d (⌊X⌋ + 1) (⌊Y⌋ - ⌊X⌋).toNat := by
  have hfloor : ⌊X⌋ ≤ ⌊Y⌋ := Int.floor_mono hXY
  unfold reciprocalInterval incompleteReciprocal
  symm
  refine sum_bij (fun j _ ↦ ⌊X⌋ + 1 + (j : ℤ)) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [mem_range] at hj
    simp only [mem_Ioc]
    omega
  · intro a _ b _ hab
    omega
  · intro c hc
    simp only [mem_Ioc] at hc
    refine ⟨(c - (⌊X⌋ + 1)).toNat, ?_, ?_⟩
    · simp only [mem_range]
      omega
    · omega
  · intro j _
    congr 1
    push_cast
    rfl

omit [NeZero q] in
theorem reciprocalInterval_length_le {X Y : ℝ} (h : Y - X ≤ q) :
    (⌊Y⌋ - ⌊X⌋).toNat ≤ q := by
  have hf := Int.floor_mono (show Y ≤ X + (q : ℝ) by linarith)
  rw [Int.floor_add_natCast] at hf
  omega

/-- A pointwise fixed-order moment bound extracted from the proved full mean. -/
theorem fouvryTau_pow_pointwise (k r : ℕ) (hk : 1 ≤ k) {n : ℕ} (hn : 0 < n) :
    (fouvryTau k n : ℝ) ^ r ≤
      (n : ℝ) * (1 + Real.log n) ^ (k ^ r - 1) := by
  calc
    _ ≤ ∑ m ∈ Ioc 0 n, (fouvryTau k m : ℝ) ^ r :=
      single_le_sum (fun _ _ ↦ by positivity) (mem_Ioc.mpr ⟨hn, le_rfl⟩)
    _ ≤ _ := by
      simpa only [Nat.floor_natCast] using
        sum_fouvryTau_pow_le_real (r := r) hk (show (1 : ℝ) ≤ n by exact_mod_cast hn)

/-- Arbitrarily high fixed moments pay the exact divisor/logarithm completion
loss. The threshold is uniform in the positive integer argument. -/
theorem eventually_divisors_completion_loss {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (n.divisors.card : ℝ) * (3 + 2 * Real.log n) ≤ (n : ℝ) ^ ε := by
  obtain ⟨r, hr⟩ := exists_nat_gt (1 / ε)
  have hr0 : r ≠ 0 := by
    intro h
    subst r
    simp only [Nat.cast_zero] at hr
    have := one_div_pos.mpr hε
    linarith
  have hgap : 0 < ε * r - 1 := by
    have := (div_lt_iff₀ hε).mp hr
    nlinarith
  let K := 2 ^ r - 1
  have hs : (fun x : ℝ ↦ Real.log x ^ (K + r)) =o[atTop]
      (fun x ↦ x ^ (ε * r - 1)) := by
    simpa only [Real.rpow_natCast] using
      isLittleO_log_rpow_rpow_atTop (K + r : ℕ) hgap
  have hb := (hs.const_mul_left ((2 : ℝ) ^ K * 5 ^ r)).bound
    (by norm_num : (0 : ℝ) < 1)
  have hevent : ∀ᶠ x : ℝ in atTop,
      1 ≤ Real.log x ∧ 1 ≤ x ∧
      2 ^ K * 5 ^ r * Real.log x ^ (K + r) ≤ x ^ (ε * r - 1) := by
    filter_upwards [hb, Real.tendsto_log_atTop.eventually_ge_atTop 1,
      eventually_ge_atTop (1 : ℝ)] with x hx hl hx1
    refine ⟨hl, hx1, ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ (2 : ℝ) ^ K * 5 ^ r * Real.log x ^ (K + r)),
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) _), one_mul] using hx
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hevent,
    eventually_ge_atTop (1 : ℕ)] with n hn hn1
  rcases hn with ⟨hlog, hnR, hpay⟩
  have hn0 : (0 : ℝ) < n := by positivity
  have hm := fouvryTau_pow_pointwise 2 r (by norm_num) (by omega : 0 < n)
  rw [fouvryTau_two] at hm
  apply le_of_pow_le_pow_left₀ hr0 (Real.rpow_nonneg hn0.le ε)
  calc
    ((n.divisors.card : ℝ) * (3 + 2 * Real.log n)) ^ r
      ≤ ((n : ℝ) * (1 + Real.log n) ^ K) * (3 + 2 * Real.log n) ^ r := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right hm (by positivity)
    _ ≤ ((n : ℝ) * (2 * Real.log n) ^ K) * (5 * Real.log n) ^ r := by
      gcongr <;> linarith
    _ = (n : ℝ) * (2 ^ K * 5 ^ r * Real.log n ^ (K + r)) := by
      rw [pow_add, mul_pow, mul_pow]
      ring
    _ ≤ (n : ℝ) * (n : ℝ) ^ (ε * r - 1) :=
      mul_le_mul_of_nonneg_left hpay hn0.le
    _ = ((n : ℝ) ^ ε) ^ r := by
      rw [← Real.rpow_mul_natCast hn0.le, mul_comm (n : ℝ),
        ← Real.rpow_add_one hn0.ne', sub_add_cancel]

/-- A single constant covers all moduli, not merely sufficiently large ones. -/
theorem divisors_completion_loss {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (n.divisors.card : ℝ) * (3 + 2 * Real.log n) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨N, hN⟩ := (eventually_atTop.mp (eventually_divisors_completion_loss hε))
  let C : ℝ := 1 + (N : ℝ) * (3 + 2 * N)
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (by positivity)
  refine ⟨C, lt_of_lt_of_le zero_lt_one hC, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 1 ≤ (n : ℝ) ^ ε := Real.one_le_rpow hn1 hε.le
  by_cases hlarge : N ≤ n
  · exact (hN n hlarge).trans (le_mul_of_one_le_left (by positivity) hC)
  · have hnN : (n : ℝ) ≤ N := by exact_mod_cast (le_of_lt (lt_of_not_ge hlarge))
    have hdiv : (n.divisors.card : ℝ) ≤ N :=
      (by exact_mod_cast Nat.card_divisors_le_self n : (n.divisors.card : ℝ) ≤ n).trans hnN
    have hlog : Real.log n ≤ N := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < n)
      linarith
    calc
      _ ≤ (N : ℝ) * (3 + 2 * N) := by
        gcongr
      _ ≤ C := by dsimp [C]; linarith
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hp

theorem completeKloosterman_gcd_envelope (d : ℤ)
    (hWeil : ∀ m : ZMod q, ‖completeKloosterman q m d‖ ≤
      (q.divisors.card : ℝ) *
        Real.sqrt (q.gcd (m.val.gcd d.natAbs)) * Real.sqrt q) :
    ∀ m : ZMod q, ‖completeKloosterman q m d‖ ≤
      (q.divisors.card : ℝ) * Real.sqrt (q.gcd d.natAbs) * Real.sqrt q := by
  intro m
  apply (hWeil m).trans
  gcongr
  exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (NeZero.pos q))
    (Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
      ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)))

/-- The complete Weil estimate implies the F87 Lemma 3 bound over its full
interval and frequency domain. The complete estimate is established below. -/
theorem reciprocalInterval_weil_to_fouvry
    (hWeil : ∀ (q : ℕ) (_ : NeZero q) (m : ZMod q) (d : ℤ),
      ‖completeKloosterman q m d‖ ≤ (q.divisors.card : ℝ) *
        Real.sqrt (q.gcd (m.val.gcd d.natAbs)) * Real.sqrt q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (_ : NeZero q) (d : ℤ) (X Y : ℝ),
      X ≤ Y → Y - X ≤ q →
      ‖reciprocalInterval q d X Y‖ ≤
        C * Real.sqrt (q.gcd d.natAbs) * (q : ℝ) ^ (1 / 2 + ε : ℝ) := by
  obtain ⟨C, hC, hpay⟩ := divisors_completion_loss hε
  refine ⟨C, hC, ?_⟩
  intro q hq d X Y hXY hlen
  have hqR : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  rw [reciprocalInterval_eq_incomplete d hXY]
  calc
    _ ≤ (3 + 2 * Real.log q) *
        ((q.divisors.card : ℝ) * Real.sqrt (q.gcd d.natAbs) * Real.sqrt q) :=
      incompleteReciprocal_norm_le_log d (⌊X⌋ + 1) _ (reciprocalInterval_length_le hlen) _
        (completeKloosterman_gcd_envelope d (hWeil q hq · d))
    _ = ((q.divisors.card : ℝ) * (3 + 2 * Real.log q)) *
        Real.sqrt (q.gcd d.natAbs) * Real.sqrt q := by ring
    _ ≤ (C * (q : ℝ) ^ ε) * Real.sqrt (q.gcd d.natAbs) * Real.sqrt q :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hpay q (NeZero.pos q)) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
    _ = _ := by
      simp only [Real.sqrt_eq_rpow]
      rw [Real.rpow_add hqR]
      ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryCompleteWeil -/


/-!
# Unconditional complete Weil and Fouvry interval estimates

The odd-prime-power Gauss argument and the separate two-power stationary bound
supply every primitive local estimate. Exact frequency descent and twisted CRT
then give the divisor/gcd envelope for every positive modulus. The existing
Fourier completion yields Fouvry's Lemma 3, uniformly in signed frequencies and
real interval endpoints; no complete-sum estimate remains as a hypothesis.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem completeKloosterman_prime_power_primitive_weil (p k : ℕ) [Fact p.Prime]
    (a d : ℤ) (hprimitive : ¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ d) :
    ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ ≤
      ((k + 1 : ℕ) : ℝ) * Real.sqrt (p ^ k : ℕ) := by
  by_cases hp : p = 2
  · subst p
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      completeKloosterman_two_power_primitive_weil k a d hprimitive
  · exact completeKloosterman_odd_prime_power_primitive_weil p k hp a d hprimitive


theorem completeKloosterman_weil_zmod (q : ℕ) [NeZero q] (m : ZMod q) (d : ℤ) :
    ‖completeKloosterman q m d‖ ≤
      (q.divisors.card : ℝ) * Real.sqrt (q.gcd (m.val.gcd d.natAbs)) *
        Real.sqrt q := by
  exact completeKloosterman_weil_zmod_of_primitive_prime_power
    (fun p k _ a d ↦ completeKloosterman_prime_power_primitive_weil p k a d) q m d

/-- F87 Lemma 3 for the actual reciprocal sum over `X < c ≤ Y`, with a single
constant for all positive moduli, signed frequencies, and intervals of length
at most the modulus. -/
theorem reciprocalInterval_fouvry {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (_ : NeZero q) (d : ℤ) (X Y : ℝ),
      X ≤ Y → Y - X ≤ q →
      ‖reciprocalInterval q d X Y‖ ≤
        C * Real.sqrt (q.gcd d.natAbs) * (q : ℝ) ^ (1 / 2 + ε : ℝ) := by
  exact reciprocalInterval_weil_to_fouvry
    (fun q _ m d ↦ completeKloosterman_weil_zmod q m d) hε

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

namespace FareyHD8006
open Finset
open scoped BigOperators

theorem gcd_harmonic_sum (q : ℕ) (hq : 0 < q) :
    ∑ k ∈ Ico 1 q, (q.gcd k : ℝ) * (k:ℝ)⁻¹ ≤ q.divisors.card * (harmonic q : ℝ) := by
  classical
  let f (k : ℕ) : ℕ × ℕ := (q.gcd k, k/(q.gcd k))
  have fmul (k : ℕ) : (f k).1 * (f k).2 = k := Nat.mul_div_cancel' (Nat.gcd_dvd_right q k)
  have hinj : Set.InjOn f ↑(Ico 1 q) := by
    intro k hk l hl e
    calc k = (f k).1 * (f k).2 := (fmul k).symm
         _ = (f l).1 * (f l).2 := by rw [e]
         _ = l := fmul l
  have hsub : (Ico 1 q).image f ⊆ q.divisors.product (Icc 1 q) := by
    intro a ha
    obtain ⟨k,hk,rfl⟩ := mem_image.mp ha
    have hk' := mem_Ico.mp hk
    apply mem_product.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left q k, hq.ne'⟩, mem_Icc.mpr ⟨?_,?_⟩⟩
    · have hh := fmul k
      by_contra! hh'
      have h0 : (f k).2=0 := by omega
      rw [h0,mul_zero] at hh
      omega
    · exact (Nat.div_le_self _ _).trans hk'.2.le
  calc
    _ = ∑ k ∈ Ico 1 q, ((f k).2:ℝ)⁻¹ := by
      apply sum_congr rfl; intro k hk
      have hpos := Nat.gcd_pos_of_pos_left k hq
      have hnon : (q.gcd k:ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
      have eq' : ((f k).2:ℝ)=(k:ℝ)/(q.gcd k:ℝ) := Nat.cast_div (Nat.gcd_dvd_right q k) hnon
      rw [eq', inv_div,div_eq_mul_inv]
    _ = ∑ p ∈ (Ico 1 q).image f, (p.2:ℝ)⁻¹ := (sum_image (f := fun p : ℕ × ℕ => (p.2 : ℝ)⁻¹) hinj).symm
    _ ≤ ∑ p ∈ q.divisors.product (Icc 1 q), (p.2:ℝ)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ = _ := by
      change ∑ p ∈ q.divisors ×ˢ Icc 1 q, (p.2:ℝ)⁻¹ = _
      rw [sum_product (f:=fun p : ℕ × ℕ => (p.2 : ℝ)⁻¹), harmonic_eq_sum_Icc, Rat.cast_sum]
      simp [Rat.cast_inv, Rat.cast_natCast]

theorem sum_weighted_intervalFourier (q : ℕ) [NeZero q] (F : ZMod q → ℝ)
    (hF : ∀ k : ℕ, 0 < k → k < q → F (k : ZMod q) ≤
      (q:ℝ) * ((k:ℝ)⁻¹ + ((q-k:ℕ):ℝ)⁻¹)) :
    ∑ m ∈ univ.erase (0:ZMod q), F m * Real.sqrt (q.gcd m.val:ℝ) ≤
      2*(q:ℝ)*q.divisors.card*(1 + Real.log q) := by
  classical
  have hq := NeZero.pos q
  let W (m : ZMod q) : ℝ := F m * Real.sqrt (q.gcd m.val:ℝ)
  have conv : ∑ m ∈ univ.erase (0:ZMod q), W m =
      ∑ k ∈ Ico 1 q, W (k:ZMod q) := by
    have hfull : ∑ m : ZMod q, W m = ∑ k ∈ range q, W (k:ZMod q) := by
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)
      rw [← Fin.sum_univ_eq_sum_range]
      exact sum_congr rfl (fun i _ => congrArg W (ZMod.natCast_zmod_val i).symm)
    rw [sum_range_eq_add_Ico _ hq] at hfull
    have hleft := Finset.sum_erase_add (univ : Finset (ZMod q)) W (Finset.mem_univ (0:ZMod q))
    simp only [Nat.cast_zero] at hfull
    linarith
  rw [show (∑ m ∈ univ.erase (0:ZMod q), F m * Real.sqrt (q.gcd m.val:ℝ)) = _ from conv]
  calc
    _ ≤ ∑ k ∈ Ico 1 q, (q:ℝ) * ((q.gcd k:ℝ)*(k:ℝ)⁻¹ + (q.gcd (q-k):ℝ)*((q-k:ℕ):ℝ)⁻¹) := by
      apply sum_le_sum; intro k hk
      have h := mem_Ico.mp hk
      have hs : Real.sqrt (q.gcd k : ℝ) ≤ (q.gcd k:ℝ) := by
        apply Real.sqrt_le_iff.mpr
        exact ⟨by positivity, by simpa [sq] using (Nat.cast_le (α:=ℝ)).mpr (Nat.le_mul_self (q.gcd k))⟩
      have hg : q.gcd (q-k) = q.gcd k := by
        exact Nat.gcd_self_sub_right h.2.le
      dsimp only [W]
      rw [ZMod.val_natCast_of_lt h.2, hg]
      calc
        _ ≤ ((q:ℝ)*((k:ℝ)⁻¹ + ((q-k:ℕ):ℝ)⁻¹))*(q.gcd k:ℝ) :=
          mul_le_mul (hF k h.1 h.2) hs (Real.sqrt_nonneg _) (by positivity)
        _ = _ := by ring
    _ = (q:ℝ)*(2* ∑ k ∈ Ico 1 q, (q.gcd k:ℝ)*(k:ℝ)⁻¹) := by
      rw [← mul_sum, sum_add_distrib,
        sum_Ico_reflect (fun k : ℕ => (q.gcd k:ℝ)*(k:ℝ)⁻¹) 1 (m:=q) (n:=q) (by omega)]
      simp only [Nat.add_sub_cancel_left, Nat.add_sub_cancel_right]
      ring
    _ ≤ (q:ℝ)*(2*((q.divisors.card:ℝ)*(1+Real.log q))) := by
      gcongr
      exact (gcd_harmonic_sum q hq).trans
        (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log q) (Nat.cast_nonneg _))
    _ = _ := by ring
end FareyHD8006

open Finset
open scoped BigOperators

namespace FareyHD8006
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem intervalFourier_sqrtGcd_lone {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (A : ℤ) (L : ℕ),
      ∑ m ∈ univ.erase (0:ZMod q), ‖intervalFourier q A L m‖ * Real.sqrt (q.gcd m.val:ℝ) ≤
          C*(q:ℝ)^(1+ε) := by
  obtain ⟨C,hC,H⟩ := divisors_completion_loss hε
  refine ⟨C,hC,?_⟩
  intro q inst A L
  have hq := NeZero.pos q
  have hqR : (0:ℝ)<q := Nat.cast_pos.mpr hq
  calc
    _ ≤ 2*(q:ℝ)*q.divisors.card*(1+Real.log q) := sum_weighted_intervalFourier q
      (fun m => ‖intervalFourier q A L m‖) (intervalFourier_norm_le_reciprocals A L)
    _ = (q:ℝ)*((q.divisors.card:ℝ)*(2+2*Real.log q)) := by ring
    _ ≤ (q:ℝ)*((q.divisors.card:ℝ)*(3+2*Real.log q)) := by gcongr; norm_num
    _ ≤ (q:ℝ)*(C*(q:ℝ)^ε) := mul_le_mul_of_nonneg_left (H q hq) hqR.le
    _ = _ := by rw [Real.rpow_add hqR, Real.rpow_one]; ring
end FareyHD8006

namespace HD8006
open Finset MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open scoped BigOperators

/-- Summing the nonconstant Fourier modes of the second interval against the
completed reciprocal sum gives the square-root error after Fourier inversion. -/
theorem spectral_error (ε : ℝ) (hε : 0 < ε)
    :
    ∃ C : ℝ, 0<C ∧ ∀ (q:ℕ) [NeZero q] (c:ℕ), c.Coprime q → ∀ (A l:ℤ) (J I:ℕ), I≤q →
      ‖(q:ℂ)⁻¹ * ∑ m ∈ univ.erase (0:ZMod q),
         intervalFourier q A J m * incompleteReciprocal q (-((m.val:ℤ)*(c:ℤ))) l I‖
       ≤ C*(q:ℝ)^(1/2+ε:ℝ) := by
  classical
  obtain ⟨C, hC, hpay⟩ := divisors_completion_loss (ε := ε/2) (by linarith)
  refine ⟨2*C^2, by positivity, ?_⟩
  intro q inst c hc A l J I hI
  have hq : 0 < (q:ℝ) := by exact_mod_cast NeZero.pos q
  have hlog : 0 ≤ Real.log (q:ℝ) := Real.log_nonneg (by exact_mod_cast NeZero.pos q)
  let D := (q.divisors.card:ℝ)*(3+2*Real.log q)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let t := D * Real.sqrt (q : ℝ)
  have ht : 0 ≤ t := mul_nonneg hD (Real.sqrt_nonneg _)
  have hterm (m : ZMod q) :
      ‖incompleteReciprocal q (-((m.val:ℤ)*(c:ℤ))) l I‖ ≤
        Real.sqrt (q.gcd m.val : ℝ) * t := by
    let d := -((m.val:ℤ)*(c:ℤ))
    have hg : q.gcd d.natAbs = q.gcd m.val := by
      simp only [d, Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_natCast]
      exact hc.gcd_mul_right_cancel_right _
    have h := incompleteReciprocal_norm_le_log d l I hI _
      (completeKloosterman_gcd_envelope d (fun a => completeKloosterman_weil_zmod q a d))
    rw [hg] at h
    apply h.trans_eq
    dsimp [t,D]; ring
  have hsum := Finset.sum_le_sum (s:=univ.erase (0:ZMod q)) (fun m _ =>
    mul_le_mul_of_nonneg_left (hterm m) (norm_nonneg (intervalFourier q A J m)))
  simp_rw [← mul_assoc] at hsum
  rw [← Finset.sum_mul] at hsum
  have hmass : (∑ m ∈ univ.erase (0:ZMod q), ‖intervalFourier q A J m‖ * Real.sqrt (q.gcd m.val:ℝ)) ≤
      2*(q:ℝ)*D := by
    apply (FareyHD8006.sum_weighted_intervalFourier q
      (fun m => ‖intervalFourier q A J m‖) (intervalFourier_norm_le_reciprocals A J)).trans
    dsimp only [D]
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have herr : ‖∑ m ∈ univ.erase (0:ZMod q),
       intervalFourier q A J m * incompleteReciprocal q (-((m.val:ℤ)*(c:ℤ))) l I‖ ≤
         (2*q*D)*t := by
    apply (norm_sum_le _ _).trans
    simp_rw [norm_mul]
    exact hsum.trans (mul_le_mul_of_nonneg_right hmass ht)
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left herr (inv_nonneg.mpr hq.le)).trans
  dsimp only [t]
  have he := hpay q (NeZero.pos q)
  change D ≤ C*(q:ℝ)^(ε/2) at he
  calc
    (q:ℝ)⁻¹ * (2*q*D * (D*Real.sqrt q)) = 2 * D^2 * Real.sqrt q := by field_simp
    _ ≤ 2*(C*(q:ℝ)^(ε/2))^2 * Real.sqrt q := by
      gcongr
    _ = _ := by
      rw [Real.sqrt_eq_rpow, Real.rpow_add hq]
      have hp : (q:ℝ)^(ε:ℝ) = ((q:ℝ)^(ε/2))^2 := by
        rw [← Real.rpow_mul_natCast hq.le]
        congr 1
        push_cast
        ring
      rw [hp]
      ring

end HD8006

open Finset MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open scoped BigOperators
namespace HD8006
noncomputable section
variable {q : ℕ} [NeZero q]

def rectCount (q c l h a b : ℕ) : ℕ :=
  (((Icc l h).product (Icc a b)).filter (fun xy => (xy.1 * xy.2) % q = c % q)).card

def unitCount (q l h : ℕ) : ℕ := ((Icc l h).filter (fun x => x.Coprime q)).card

theorem modular_indicator (c : ℕ) (hc : c.Coprime q) (x y : ℕ) :
  (if (x*y) % q=c % q then (1:ℂ) else 0) = (q:ℂ)⁻¹ *
    ∑ m : ZMod q, ZMod.stdAddChar (m*(y:ZMod q)) *
      reciprocalPhase q (-((m.val:ℤ)*(c:ℤ))) (x:ZMod q) := by
  classical
  have hyp : (x*y) % q=c % q ↔ (x:ZMod q)*(y:ZMod q)=(c:ZMod q) := by
    rw [←Nat.cast_mul, ZMod.natCast_eq_natCast_iff']
  simp only [hyp]
  by_cases hx : IsUnit (x:ZMod q)
  · have hx' := ZMod.coe_mul_inv_eq_one x ((ZMod.isUnit_iff_coprime _ _).mp hx)
    have heq : (x:ZMod q)*(y:ZMod q)=(c:ZMod q) ↔ (y:ZMod q)-(c:ZMod q)*(x:ZMod q)⁻¹=0 := by
      rw [sub_eq_zero]
      constructor
      · intro h
        rw [←h, mul_right_comm, hx', one_mul]
      · intro h
        rw [h, mul_left_comm, hx', mul_one]
    simp only [heq]
    let t : ZMod q := (y:ZMod q)-(c:ZMod q)*(x:ZMod q)⁻¹
    have hsum : (∑ m : ZMod q, ZMod.stdAddChar (t*m)) = if t=0 then (q:ℂ) else 0 := by
      by_cases ht : t=0
      · simp [ht]
      · simp only [ht, ↓reduceIte]
        exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q ht)
    have hterm (m:ZMod q) : ZMod.stdAddChar (m*(y:ZMod q)) *
         reciprocalPhase q (-((m.val:ℤ)*(c:ℤ))) (x:ZMod q) = ZMod.stdAddChar (t*m) := by
      simp only [reciprocalPhase, hx, ↓reduceIte, ←AddChar.map_add_eq_mul]
      push_cast
      rw [ZMod.natCast_zmod_val]
      congr 1
      unfold t
      ring
    simp_rw [hterm]
    rw [hsum]
    change (if t=0 then _ else _) = _
    split_ifs <;> simp [NeZero.ne q]
  · have hn : (x:ZMod q)*(y:ZMod q)≠(c:ZMod q) := by
      intro h
      apply hx
      exact isUnit_of_mul_isUnit_left (h ▸ (ZMod.isUnit_iff_coprime _ _).mpr hc)
    simp [hn, reciprocalPhase, hx]

omit [NeZero q] in
theorem sum_interval_cast {M : Type*} [AddCommMonoid M] (l h : ℕ) (F : ZMod q → M) :
    (∑ x ∈ Icc l h, F (x:ZMod q)) =
      ∑ j ∈ range (Icc l h).card, F ((l:ZMod q)+(j:ZMod q)) := by
  rw [Nat.card_Icc, ←Ico_succ_right_eq_Icc, sum_Ico_eq_sum_range]
  simp

theorem rectangle_fourier (c l h a b : ℕ) (hc : c.Coprime q) :
    (rectCount q c l h a b:ℂ) = (q:ℂ)⁻¹ * ∑ m : ZMod q,
      intervalFourier q (a:ℤ) (Icc a b).card m *
      incompleteReciprocal q (-((m.val:ℤ)*(c:ℤ))) (l:ℤ) (Icc l h).card := by
  classical
  unfold rectCount
  rw [←sum_boole, Finset.product_eq_sprod]
  rw [sum_product (Icc l h) (Icc a b) (fun xy : ℕ × ℕ => if (xy.1 * xy.2) % q = c % q then (1:ℂ) else 0)]
  simp_rw [modular_indicator c hc]
  simp_rw [←mul_sum]
  congr 1
  calc
    _ = ∑ x ∈ Icc l h, ∑ m : ZMod q, ∑ y ∈ Icc a b, ZMod.stdAddChar (m*(y:ZMod q)) *
           reciprocalPhase q (-((m.val:ℤ)*(c:ℤ))) (x:ZMod q) := by
      apply sum_congr rfl
      intro x _
      rw [sum_comm]
    _ = ∑ m : ZMod q, ∑ x ∈ Icc l h, ∑ y ∈ Icc a b, ZMod.stdAddChar (m*(y:ZMod q)) *
           reciprocalPhase q (-((m.val:ℤ)*(c:ℤ))) (x:ZMod q) := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro m _
      simp_rw [←sum_mul, ←mul_sum]
      have h1 := sum_interval_cast a b (fun y : ZMod q => ZMod.stdAddChar (m*y))
      have h2 := sum_interval_cast l h (fun x : ZMod q => reciprocalPhase q (-((m.val:ℤ)*(c:ℤ))) x)
      simp only [Int.cast_natCast, intervalFourier, incompleteReciprocal, h1, h2]

theorem zero_mode (c l h a b : ℕ) :
    intervalFourier q (a:ℤ) (Icc a b).card 0 *
      incompleteReciprocal q (-(((0:ZMod q).val:ℤ)*(c:ℤ))) (l:ℤ) (Icc l h).card =
      ((Icc a b).card:ℂ)*(unitCount q l h:ℂ) := by
  classical
  simp only [intervalFourier, zero_mul, AddChar.map_zero_eq_one, sum_const, card_range, nsmul_eq_mul,
    mul_one, ZMod.val_zero, Nat.cast_zero, neg_zero, incompleteReciprocal, Int.cast_natCast]
  congr 1
  rw [←sum_interval_cast l h (reciprocalPhase q 0)]
  simp only [reciprocalPhase, Int.cast_zero, zero_mul, AddChar.map_zero_eq_one, ZMod.isUnit_iff_coprime,
    sum_boole, unitCount]

theorem rect_erase (c l h a b : ℕ) (hc : c.Coprime q) :
    ‖(q:ℂ)⁻¹ * ∑ m ∈ univ.erase (0:ZMod q), intervalFourier q (a:ℤ) (Icc a b).card m *
      incompleteReciprocal q (-((m.val:ℤ)*(c:ℤ))) (l:ℤ) (Icc l h).card‖ =
      |(rectCount q c l h a b:ℝ) - ((Icc a b).card:ℝ)*(unitCount q l h:ℝ)/q| := by
  classical
  have ht := rectangle_fourier c l h a b hc
  rw [←sum_erase_add _ _ (mem_univ (0:ZMod q)), zero_mode, mul_add] at ht
  have hh : (q:ℂ)⁻¹ * ∑ m ∈ univ.erase (0:ZMod q), intervalFourier q (a:ℤ) (Icc a b).card m *
       incompleteReciprocal q (-((m.val:ℤ)*(c:ℤ))) (l:ℤ) (Icc l h).card =
       ((rectCount q c l h a b:ℝ) - ((Icc a b).card:ℝ)*(unitCount q l h:ℝ)/(q:ℝ):ℝ) := by
    push_cast
    linear_combination -ht
  rw [hh, Complex.norm_real, Real.norm_eq_abs]

end
end HD8006

open Finset MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open scoped BigOperators
namespace HD8006
noncomputable section
variable {q : ℕ} [NeZero q]

theorem full_window : Icc 0 (q-1) = range q := by
  have hp := NeZero.pos q
  ext x
  simp only [mem_Icc, Nat.zero_le, true_and, mem_range]
  omega

theorem units_full : unitCount q 0 (q-1) = q.totient := by
  unfold unitCount
  rw [full_window, Nat.totient_eq_card_coprime]
  congr 1
  exact filter_congr (fun _ _ => Nat.coprime_comm)

theorem full_rectangle (c l h : ℕ) (hc : c.Coprime q) :
    rectCount q c 0 (q-1) l h = unitCount q l h := by
  classical
  unfold rectCount unitCount
  rw [full_window]
  let v (y : ℕ) := ((c:ZMod q)*(y:ZMod q)⁻¹).val
  have hv (y : ℕ) (hy : y.Coprime q) :
      (v y * y) % q = c % q := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ _).mp
    rw [Nat.cast_mul]
    dsimp [v]
    rw [ZMod.natCast_zmod_val, mul_assoc, mul_comm _ (y:ZMod q),
        ZMod.coe_mul_inv_eq_one y hy, mul_one]
  have hcast (xy : ℕ × ℕ) (hxy : xy.1*xy.2 % q=c % q) :
      (xy.1:ZMod q)*(xy.2:ZMod q)=(c:ZMod q) := by
    rw [←Nat.cast_mul]
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hxy
  have hyv (xy : ℕ × ℕ) (hxy : xy.1*xy.2 % q=c % q) : xy.2.Coprime q := by
    apply (ZMod.isUnit_iff_coprime _ _).mp
    apply isUnit_of_mul_isUnit_right (x := (xy.1:ZMod q))
    rw [hcast xy hxy]
    exact (ZMod.isUnit_iff_coprime _ _).mpr hc
  refine card_bij' (fun xy _ => xy.2) (fun y _ => (v y,y)) ?_ ?_ ?_ ?_
  · intro xy hxy
    obtain ⟨hi, he⟩ := mem_filter.mp hxy
    exact mem_filter.mpr ⟨(mem_product.mp hi).2,hyv xy he⟩
  · intro y hy
    obtain ⟨hi,hcp⟩ := mem_filter.mp hy
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (ZMod.val_lt _),hi⟩,hv y hcp⟩
  · intro xy hxy
    obtain ⟨hi,he⟩ := mem_filter.mp hxy
    have h1 := ZMod.coe_mul_inv_eq_one xy.2 (hyv xy he)
    have h2 := hcast xy he
    refine Prod.ext ?_ rfl
    dsimp [v]
    rw [←h2, mul_assoc, h1, mul_one, ZMod.val_natCast_of_lt (mem_range.mp (mem_product.mp hi).1)]
  · intros; rfl

theorem rectangle_two_errors (c l h a b : ℕ) (hc : c.Coprime q)
    (hh : h < q) (hb : b < q) (B : ℝ)
    (hspec : ∀ (l h a b : ℕ), h < q → b < q →
      ‖(q:ℂ)⁻¹ * ∑ m ∈ univ.erase (0:ZMod q), intervalFourier q (a:ℤ) (Icc a b).card m *
        incompleteReciprocal q (-((m.val:ℤ)*(c:ℤ))) (l:ℤ) (Icc l h).card‖ ≤ B) :
    |(rectCount q c l h a b:ℝ) - ((Icc l h).card:ℝ)*(Icc a b).card*q.totient/(q:ℝ)^2| ≤ 2*B := by
  classical
  have hq := NeZero.pos q
  have hA := hspec l h a b hh hb
  rw [rect_erase _ _ _ _ _ hc] at hA
  have hB := hspec 0 (q-1) l h (by omega) hh
  rw [rect_erase _ _ _ _ _ hc, full_rectangle c l h hc, units_full] at hB
  have hqp : (0:ℝ)<q := by exact_mod_cast hq
  let ratio := ((Icc a b).card:ℝ)/(q:ℝ)
  have hr0 : 0≤ratio := by dsimp [ratio]; positivity
  have hr1 : ratio≤1 := by
    apply (div_le_one hqp).mpr
    exact_mod_cast (show (Icc a b).card ≤ q by rw [Nat.card_Icc]; omega)
  have hBn : 0 ≤ B := (norm_nonneg _).trans (hspec l h a b hh hb)
  calc
    _ = |((rectCount q c l h a b:ℝ) - ((Icc a b).card:ℝ)*(unitCount q l h:ℝ)/q) +
       ratio * ((unitCount q l h:ℝ)- ((Icc l h).card:ℝ)*q.totient/q)| := by
        congr 1
        unfold ratio
        ring
    _ ≤ _ := (abs_add_le _ _).trans (by
      rw [abs_mul,abs_of_nonneg hr0]
      linarith [mul_le_mul hr1 hB (abs_nonneg _) zero_le_one])
end
end HD8006

open Finset

theorem Conjectures.Goldbach.FareyHyperbolaRectangles :
∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 < n → ∀ c l h a b : ℕ, c.Coprime n → h < n → b < n → let I := Finset.Icc l h; let J := Finset.Icc a b; |((((I.product J).filter (fun (x : ℕ × ℕ) => (x.1*x.2) % n = c % n)).card : ℝ) - (I.card:ℝ)*(J.card:ℝ)*(n.totient:ℝ)/(n:ℝ)^2)| ≤ C*(n:ℝ)^((1/2:ℝ)+ε) := by
  intro ε hε
  obtain ⟨K,hK,hbound⟩ := HD8006.spectral_error ε hε
  refine ⟨2*K, by positivity, ?_⟩
  intro q hq c l h a b hc hh hb
  letI : NeZero q := ⟨by omega⟩
  have bounds (l h a b : ℕ) (hx : h < q) (_ : b < q) :=
    hbound q c hc (a:ℤ) (l:ℤ) (Icc a b).card (Icc l h).card (by rw [Nat.card_Icc]; omega)
  have result := HD8006.rectangle_two_errors c l h a b hc hh hb _ bounds
  simpa only [HD8006.rectCount, mul_assoc] using result

