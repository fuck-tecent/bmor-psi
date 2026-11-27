import Mathlib

/-!
# Large-base higher-power convolution tail

Bound `∑_{Y^(1/10) < p ≤ 3Y} Σ_{2 ≤ a ≤ log₂(3Y)} (Σ_{t ≤ 3Y/p^a} τ(t)) log p / Y`
by `C log³(2+Y) / Y^(1/10)`.

Method (no hypothesis on the primes is needed):
* harmonic kernel bound `Σ_{t ≤ N} τ(t) ≤ N (1 + log N)`, adapted from
  `Conjectures.Goldbach.FareySieveRootTotal`;
* for `a ≥ 2` and `p ≥ 1`, `p^2 ≤ p^a`, so the `a`-sum is at most `(log₂ 3Y) / p²`;
* the primality filter is dropped (all terms are nonnegative) and `log p ≤ log (3Y)`;
* the telescoping tail `Σ_{n > m} n⁻² ≤ 1/m` with `m = ⌊Y^(1/10)⌋`, and `1/m ≤ 2 Y^(-1/10)`.

The constants `1 + log (3Y) ≤ 3 log (2+Y)` and `log₂ (3Y) ≤ 4 log (2+Y)` for `Y ≥ 2` give `C = 216`.
-/

open scoped BigOperators
open Finset

namespace Conjectures.TwinPrimes.LongDivisorLargeBasePowerTail_aux

/-- adapted from Conjectures.Goldbach.FareySieveRootTotal -/
private lemma icc_one_eq_ioc_zero (D : ℕ) : Finset.Icc 1 D = Finset.Ioc 0 D :=
  Finset.Icc_succ_left_eq_Ioc 0 D

private lemma icc_one_filter_dvd_card (D e : ℕ) :
    ((Finset.Icc 1 D).filter (e ∣ ·)).card = D / e := by
  rw [icc_one_eq_ioc_zero, Nat.Ioc_filter_dvd_card_eq_div]

private lemma divisor_indicator (D d : ℕ) (hd : d ∈ Finset.Icc 1 D) :
    (d.divisors.card : ℝ) = ∑ e ∈ Finset.Icc 1 D, (if e ∣ d then (1 : ℝ) else 0) := by
  have hdD : d ≤ D := (Finset.mem_Icc.mp hd).2
  have hd0 : d ≠ 0 := by have := (Finset.mem_Icc.mp hd).1; omega
  have hset : (Finset.Icc 1 D).filter (· ∣ d) = d.divisors := by
    ext e
    constructor
    · intro he
      exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp he).2, hd0⟩
    · intro he
      have hed : e ∣ d := (Nat.mem_divisors.mp he).1
      have he1 : 1 ≤ e := Nat.pos_of_dvd_of_pos hed (by omega)
      have heD : e ≤ D := (Nat.le_of_dvd (by omega) hed).trans hdD
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨he1, heD⟩, hed⟩
  have hsum : (∑ e ∈ Finset.Icc 1 D, (if e ∣ d then (1 : ℝ) else 0))
      = (((Finset.Icc 1 D).filter (· ∣ d)).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  rw [hsum, hset]

private lemma harmonic_cast_eq_sum (D : ℕ) :
    (harmonic D : ℝ) = ∑ e ∈ Finset.Icc 1 D, ((e : ℝ))⁻¹ := by
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp

private lemma sum_card_divisors_le_harmonic (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ)) ≤ (D : ℝ) * (harmonic D : ℝ) := by
  calc (∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ))
      = ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D, (if e ∣ d then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro d hd
        exact divisor_indicator D d hd
    _ = ∑ e ∈ Finset.Icc 1 D, ∑ d ∈ Finset.Icc 1 D, (if e ∣ d then (1 : ℝ) else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ e ∈ Finset.Icc 1 D, ((D / e : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro e _
        have hinner : (∑ d ∈ Finset.Icc 1 D, (if e ∣ d then (1 : ℝ) else 0))
            = (((Finset.Icc 1 D).filter (e ∣ ·)).card : ℝ) := by
          rw [← Finset.sum_filter]
          simp
        rw [hinner, icc_one_filter_dvd_card]
    _ ≤ ∑ e ∈ Finset.Icc 1 D, (D : ℝ) / e := by
        apply Finset.sum_le_sum
        intro e _
        exact Nat.cast_div_le
    _ = (D : ℝ) * ∑ e ∈ Finset.Icc 1 D, ((e : ℝ))⁻¹ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        field_simp
    _ = (D : ℝ) * (harmonic D : ℝ) := by rw [harmonic_cast_eq_sum]

/-- The harmonic kernel bound: `∑_{t ≤ N} τ(t) ≤ N (1 + log N)`. -/
lemma sum_card_divisors_le (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ)) ≤ (D : ℝ) * (1 + Real.log D) :=
  (sum_card_divisors_le_harmonic D).trans
    (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log D) (Nat.cast_nonneg D))

/-- The same bound with an arbitrary logarithmic majorant `B`. -/
lemma sum_card_divisors_le_mul (N : ℕ) (B : ℝ) (h : 1 + Real.log (N : ℝ) ≤ B) :
    (∑ t ∈ Finset.Icc 1 N, ((t.divisors.card : ℕ) : ℝ)) ≤ (N : ℝ) * B :=
  (sum_card_divisors_le N).trans (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg N))

end Conjectures.TwinPrimes.LongDivisorLargeBasePowerTail_aux

theorem Conjectures.TwinPrimes.LongDivisorLargeBasePowerTail :
    ∃ C : ℝ, 0<C ∧ ∀ Y : ℕ, 2≤Y → (∑ p ∈ (Finset.Ioc (Nat.nthRoot 10 Y) (3*Y)).filter Nat.Prime, ∑ a ∈ Finset.Icc 2 (Nat.log 2 (3*Y)), (∑ t ∈ Finset.Icc 1 (3*Y/p^a), ((t.divisors.card : ℕ) : ℝ)) * Real.log p / Y) ≤ C*(Real.log (2+Y))^3 / (Y:ℝ)^(1/10:ℝ) := by
  refine ⟨216, by norm_num, ?_⟩
  intro Y hY
  classical
  set m : ℕ := Nat.nthRoot 10 Y with hmdef
  set A : ℕ := Nat.log 2 (3*Y) with hAdef
  set L : ℝ := Real.log (2 + (Y:ℝ)) with hLdef
  set L3 : ℝ := 1 + Real.log (3*(Y:ℝ)) with hL3def
  have hY2 : (2:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hY
  have hYpos : (0:ℝ) < (Y:ℝ) := by linarith
  have hY1 : (1:ℝ) ≤ (Y:ℝ) := by linarith
  have hlog2 : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2pos : (0:ℝ) < Real.log 2 := by linarith
  have hlog4 : (1:ℝ) ≤ Real.log 4 := by
    have h : Real.log 4 = 2 * Real.log 2 := by
      have h' := Real.log_pow (2:ℝ) 2
      norm_num at h'
      linarith
    linarith
  have hL1 : (1:ℝ) ≤ L := by
    have hle : Real.log 4 ≤ L := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hLpos : (0:ℝ) < L := by linarith
  have hlog3Y : Real.log (3*(Y:ℝ)) ≤ 2 * L := by
    have h1 : Real.log (3*(Y:ℝ)) = Real.log 3 + Real.log (Y:ℝ) :=
      Real.log_mul (by norm_num) hYpos.ne'
    have h2 : Real.log 3 ≤ L := Real.log_le_log (by norm_num) (by linarith)
    have h3 : Real.log (Y:ℝ) ≤ L := Real.log_le_log hYpos (by linarith)
    linarith
  have hL3le : L3 ≤ 3 * L := by linarith
  have hL3ge1 : (1:ℝ) ≤ L3 := by
    rw [hL3def]
    have : 0 ≤ Real.log (3*(Y:ℝ)) := Real.log_nonneg (by linarith)
    linarith
  have hL3pos : (0:ℝ) < L3 := by linarith
  -- the exponent count `A = log 2 (3Y)` is at most `4 L`
  have hpowA : (2:ℕ)^A ≤ 3*Y := by
    rw [hAdef]; exact Nat.pow_log_le_self 2 (by omega)
  have hpowA' : (2:ℝ)^A ≤ 3*(Y:ℝ) := by exact_mod_cast hpowA
  have hlogA : (A:ℝ) * Real.log 2 ≤ Real.log (3*(Y:ℝ)) := by
    have h := Real.log_le_log (by positivity) hpowA'
    rwa [Real.log_pow] at h
  have hA : (A:ℝ) ≤ 4 * L := by
    have hmul : 4 * L * (0.6931471803:ℝ) ≤ 4 * L * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlog2) (by linarith)
    nlinarith [hlogA, hlog3Y, hmul]
  -- the base cutoff `m = Y^(1/10)` satisfies `1/m ≤ 2 / Y^(1/10)`
  have hm1 : 1 ≤ m := by
    rw [hmdef, Nat.le_nthRoot_iff (by norm_num)]
    omega
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hmY : m ≤ Y := by
    have h1 : m ^ 10 ≤ Y := by
      rw [hmdef]; exact Nat.pow_nthRoot_le (Or.inl (by norm_num))
    have h2 : m ≤ m ^ 10 := by
      calc m = m ^ 1 := (pow_one m).symm
        _ ≤ m ^ 10 := pow_le_pow_right₀ (by omega) (by omega)
    omega
  have hlt : Y < (m+1)^10 := by
    rw [hmdef]; exact Nat.lt_pow_nthRoot_add_one (by norm_num) Y
  have hltR : (Y:ℝ) < ((m:ℝ)+1)^10 := by exact_mod_cast hlt
  have h2m : (m:ℝ) + 1 ≤ 2 * (m:ℝ) := by
    have : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
    linarith
  have hbound10 : ((m:ℝ)+1)^10 ≤ (2*(m:ℝ))^10 := pow_le_pow_left₀ (by positivity) h2m 10
  have hYlt : (Y:ℝ) < (2*(m:ℝ))^10 := lt_of_lt_of_le hltR hbound10
  have hrpow : (Y:ℝ)^(1/10:ℝ) ≤ 2*(m:ℝ) := by
    have h := Real.rpow_le_rpow hYpos.le (le_of_lt hYlt) (by norm_num : (0:ℝ) ≤ (1/10:ℝ))
    have hpow : ((2*(m:ℝ))^10)^(1/10:ℝ) = 2*(m:ℝ) := by
      rw [← Real.rpow_natCast (2*(m:ℝ)) 10, ← Real.rpow_mul (by positivity)]
      norm_num
    rwa [hpow] at h
  have hYrp_pos : (0:ℝ) < (Y:ℝ)^(1/10:ℝ) := Real.rpow_pos_of_pos hYpos _
  have hm_inv : (m:ℝ)⁻¹ ≤ 2 * ((Y:ℝ)^(1/10:ℝ))⁻¹ := by
    have hkey : (m:ℝ)⁻¹ * (Y:ℝ)^(1/10:ℝ) ≤ 2 := by
      calc (m:ℝ)⁻¹ * (Y:ℝ)^(1/10:ℝ) ≤ (m:ℝ)⁻¹ * (2*(m:ℝ)) :=
            mul_le_mul_of_nonneg_left hrpow (le_of_lt (inv_pos.mpr hmpos))
        _ = 2 := by field_simp
    have hdiv : (m:ℝ)⁻¹ ≤ 2 / (Y:ℝ)^(1/10:ℝ) := by
      rw [le_div_iff₀ hYrp_pos]; linarith
    rwa [div_eq_mul_inv] at hdiv
  -- logarithmic majorant for the divisor sum arguments
  have hlogN : ∀ p a : ℕ, 1 + Real.log (((3*Y/p^a : ℕ) : ℝ)) ≤ L3 := by
    intro p a
    have hNle : 3*Y/p^a ≤ 3*Y := Nat.div_le_self _ _
    rcases Nat.eq_zero_or_pos (3*Y/p^a) with h0 | hpos
    · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]; linarith
    · have hle : Real.log (((3*Y/p^a : ℕ) : ℝ)) ≤ Real.log (3*(Y:ℝ)) := by
        apply Real.log_le_log (by exact_mod_cast hpos)
        have hcast : (((3*Y/p^a : ℕ) : ℝ)) ≤ ((3*Y : ℕ) : ℝ) := by exact_mod_cast hNle
        push_cast at hcast
        linarith
      linarith
  -- per-base estimate
  have hper : ∀ p ∈ Finset.Ioc m (3*Y),
      (∑ a ∈ Finset.Icc 2 A, (∑ t ∈ Finset.Icc 1 (3*Y/p^a),
          ((t.divisors.card : ℕ) : ℝ)) * Real.log (p:ℝ) / (Y:ℝ))
      ≤ 3 * L3 * Real.log (p:ℝ) * ((A:ℝ) / (p:ℝ)^2) := by
    intro p hp
    obtain ⟨hmp, hp3Y⟩ := Finset.mem_Ioc.mp hp
    have hp1 : 1 ≤ p := by omega
    have hpp : (0:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
    have hlogp : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp1)
    have hterm : ∀ a ∈ Finset.Icc 2 A,
        (∑ t ∈ Finset.Icc 1 (3*Y/p^a), ((t.divisors.card : ℕ) : ℝ)) * Real.log (p:ℝ) / (Y:ℝ)
        ≤ 3 * L3 * Real.log (p:ℝ) / (p:ℝ)^a := by
      intro a ha
      have hD : (∑ t ∈ Finset.Icc 1 (3*Y/p^a), ((t.divisors.card : ℕ) : ℝ))
          ≤ ((3*Y/p^a : ℕ) : ℝ) * L3 :=
        Conjectures.TwinPrimes.LongDivisorLargeBasePowerTail_aux.sum_card_divisors_le_mul _ _ (hlogN p a)
      have hcast : ((3*Y/p^a : ℕ) : ℝ) ≤ 3*(Y:ℝ) / (p:ℝ)^a := by
        have := Nat.cast_div_le (α := ℝ) (m := 3*Y) (n := p^a)
        push_cast at this
        linarith
      have hpos_pow : (0:ℝ) < (p:ℝ)^a := pow_pos hpp a
      calc (∑ t ∈ Finset.Icc 1 (3*Y/p^a), ((t.divisors.card : ℕ) : ℝ)) * Real.log (p:ℝ) / (Y:ℝ)
          ≤ (((3*Y/p^a : ℕ) : ℝ) * L3) * Real.log (p:ℝ) / (Y:ℝ) := by
            apply div_le_div_of_nonneg_right
            · exact mul_le_mul_of_nonneg_right hD hlogp
            · exact le_of_lt hYpos
        _ ≤ (3*(Y:ℝ) / (p:ℝ)^a * L3) * Real.log (p:ℝ) / (Y:ℝ) := by
            apply div_le_div_of_nonneg_right
            · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcast (le_of_lt hL3pos)) hlogp
            · exact le_of_lt hYpos
        _ = 3 * L3 * Real.log (p:ℝ) / (p:ℝ)^a := by
            field_simp
    calc (∑ a ∈ Finset.Icc 2 A, (∑ t ∈ Finset.Icc 1 (3*Y/p^a),
            ((t.divisors.card : ℕ) : ℝ)) * Real.log (p:ℝ) / (Y:ℝ))
        ≤ ∑ a ∈ Finset.Icc 2 A, 3 * L3 * Real.log (p:ℝ) / (p:ℝ)^a :=
          Finset.sum_le_sum hterm
      _ ≤ ∑ a ∈ Finset.Icc 2 A, 3 * L3 * Real.log (p:ℝ) / (p:ℝ)^2 := by
          apply Finset.sum_le_sum
          intro a ha
          have ha2 : 2 ≤ a := (Finset.mem_Icc.mp ha).1
          have hpowle : (p:ℝ)^2 ≤ (p:ℝ)^a := pow_le_pow_right₀ (by exact_mod_cast hp1) ha2
          have hinv : ((p:ℝ)^a)⁻¹ ≤ ((p:ℝ)^2)⁻¹ :=
            inv_anti₀ (by positivity) hpowle
          have hfac : 0 ≤ 3 * L3 * Real.log (p:ℝ) := by positivity
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left hinv hfac
      _ = ((Finset.Icc 2 A).card : ℝ) * (3 * L3 * Real.log (p:ℝ) / (p:ℝ)^2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (A:ℝ) * (3 * L3 * Real.log (p:ℝ) / (p:ℝ)^2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hcard : (Finset.Icc 2 A).card ≤ A := by
            rw [Nat.card_Icc]; omega
          exact_mod_cast hcard
      _ = 3 * L3 * Real.log (p:ℝ) * ((A:ℝ) / (p:ℝ)^2) := by ring
  -- sum over bases
  have htail : (∑ p ∈ Finset.Ioc m (3*Y), ((p:ℝ)^2)⁻¹) ≤ (m:ℝ)⁻¹ := by
    have h := sum_Ioc_inv_sq_le_sub (α := ℝ) (by omega : m ≠ 0) (by omega : m ≤ 3 * Y)
    have hnn : (0:ℝ) ≤ (((3*Y : ℕ) : ℝ))⁻¹ := by positivity
    linarith
  have hlogsum : (∑ p ∈ Finset.Ioc m (3*Y), Real.log (p:ℝ) * ((p:ℝ)^2)⁻¹)
      ≤ L3 * ∑ p ∈ Finset.Ioc m (3*Y), ((p:ℝ)^2)⁻¹ := by
    calc (∑ p ∈ Finset.Ioc m (3*Y), Real.log (p:ℝ) * ((p:ℝ)^2)⁻¹)
        ≤ ∑ p ∈ Finset.Ioc m (3*Y), L3 * ((p:ℝ)^2)⁻¹ := by
          apply Finset.sum_le_sum
          intro p hp
          have hp1 : 1 ≤ p := by have := (Finset.mem_Ioc.mp hp).1; omega
          have hle : Real.log (p:ℝ) ≤ Real.log (3*(Y:ℝ)) := by
            apply Real.log_le_log (by exact_mod_cast (by omega : 0 < p))
            have : (p:ℝ) ≤ ((3*Y : ℕ) : ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp hp).2
            push_cast at this
            linarith
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = L3 * ∑ p ∈ Finset.Ioc m (3*Y), ((p:ℝ)^2)⁻¹ := (Finset.mul_sum ..).symm
  have hmain : (∑ p ∈ Finset.Ioc m (3*Y), ∑ a ∈ Finset.Icc 2 A,
      (∑ t ∈ Finset.Icc 1 (3*Y/p^a), ((t.divisors.card : ℕ) : ℝ)) * Real.log (p:ℝ) / (Y:ℝ))
      ≤ (3 * L3 * (A:ℝ)) * (L3 * (m:ℝ)⁻¹) := by
    calc (∑ p ∈ Finset.Ioc m (3*Y), ∑ a ∈ Finset.Icc 2 A,
          (∑ t ∈ Finset.Icc 1 (3*Y/p^a), ((t.divisors.card : ℕ) : ℝ)) * Real.log (p:ℝ) / (Y:ℝ))
        ≤ ∑ p ∈ Finset.Ioc m (3*Y), 3 * L3 * Real.log (p:ℝ) * ((A:ℝ) / (p:ℝ)^2) :=
          Finset.sum_le_sum hper
      _ = (3 * L3 * (A:ℝ)) * ∑ p ∈ Finset.Ioc m (3*Y), Real.log (p:ℝ) * ((p:ℝ)^2)⁻¹ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _
          ring
      _ ≤ (3 * L3 * (A:ℝ)) * (L3 * (m:ℝ)⁻¹) := by
          apply mul_le_mul_of_nonneg_left
          · exact hlogsum.trans (mul_le_mul_of_nonneg_left htail (le_of_lt hL3pos))
          · positivity
  -- drop the primality condition
  have hfilter : (∑ p ∈ (Finset.Ioc m (3*Y)).filter Nat.Prime, ∑ a ∈ Finset.Icc 2 A,
      (∑ t ∈ Finset.Icc 1 (3*Y/p^a), ((t.divisors.card : ℕ) : ℝ)) * Real.log (p:ℝ) / (Y:ℝ))
      ≤ ∑ p ∈ Finset.Ioc m (3*Y), ∑ a ∈ Finset.Icc 2 A,
          (∑ t ∈ Finset.Icc 1 (3*Y/p^a), ((t.divisors.card : ℕ) : ℝ)) * Real.log (p:ℝ) / (Y:ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro p hp _
    apply Finset.sum_nonneg
    intro a _
    apply div_nonneg
    · apply mul_nonneg
      · exact Finset.sum_nonneg (fun t _ => Nat.cast_nonneg _)
      · exact Real.log_nonneg (by have := (Finset.mem_Ioc.mp hp).1; exact_mod_cast (by omega : 1 ≤ p))
    · exact le_of_lt hYpos
  -- final assembly
  have hL3A : L3 * (A:ℝ) ≤ (3*L) * (4*L) :=
    mul_le_mul hL3le hA (Nat.cast_nonneg A) (by linarith)
  calc (∑ p ∈ (Finset.Ioc m (3*Y)).filter Nat.Prime, ∑ a ∈ Finset.Icc 2 A,
        (∑ t ∈ Finset.Icc 1 (3*Y/p^a), ((t.divisors.card : ℕ) : ℝ)) * Real.log (p:ℝ) / (Y:ℝ))
      ≤ ∑ p ∈ Finset.Ioc m (3*Y), ∑ a ∈ Finset.Icc 2 A,
          (∑ t ∈ Finset.Icc 1 (3*Y/p^a), ((t.divisors.card : ℕ) : ℝ)) * Real.log (p:ℝ) / (Y:ℝ) :=
        hfilter
    _ ≤ (3 * L3 * (A:ℝ)) * (L3 * (m:ℝ)⁻¹) := hmain
    _ = 3 * (L3 * (A:ℝ)) * (L3 * (m:ℝ)⁻¹) := by ring
    _ ≤ 3 * ((3*L) * (4*L)) * ((3*L) * (2 * ((Y:ℝ)^(1/10:ℝ))⁻¹)) := by
        apply mul_le_mul
        · exact mul_le_mul (by linarith) hL3A (by positivity) (by positivity)
        · exact mul_le_mul hL3le hm_inv (by positivity) (by linarith)
        · positivity
        · positivity
    _ = 216 * L^3 * ((Y:ℝ)^(1/10:ℝ))⁻¹ := by ring
    _ = 216 * L^3 / (Y:ℝ)^(1/10:ℝ) := by ring
