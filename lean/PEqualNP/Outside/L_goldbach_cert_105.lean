import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace GoldbachCert105

open Finset
open scoped Real

private noncomputable def center (q a b : ℕ) : ℂ :=
  Complex.exp (((2 * π * (a : ℝ) * b / q : ℝ) : ℂ) * Complex.I)

private def units (q : ℕ) := (range q).filter (fun b => q.Coprime b)

private theorem complete_center (m a : ℕ) (hm : 0 < m) :
    ∑ j ∈ range m, center m a j = if m ∣ a then (m:ℂ) else 0 := by
  let z : ℂ := Complex.exp (2*π*Complex.I*a/m)
  have hz : z = 1 ↔ m ∣ a := Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hm.ne'
  have hm' : (m:ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpow (j : ℕ) : center m a j = z^j := by
    rw [← Complex.exp_nat_mul]
    unfold center
    push_cast
    congr 1
    ring
  simp_rw [hpow]
  by_cases h : m ∣ a
  · simp [h, hz.mpr h]
  · simp only [h, ite_false]
    have hzm : z^m = 1 := by
      rw [← Complex.exp_nat_mul, show (m:ℂ)*(2*π*Complex.I*a/m) = a*(2*π*Complex.I) by field_simp]
      exact Complex.exp_nat_mul_two_pi_mul_I a
    have H := geom_sum_mul z m
    rw [hzm, sub_self] at H
    exact (mul_eq_zero.mp H).resolve_right (sub_ne_zero.mpr (fun H => h (hz.mp H)))

private theorem gcd_indicator (q b : ℕ) (hq : 0 < q) :
    (∑ d ∈ q.divisors, if d ∣ b then (ArithmeticFunction.moebius d : ℂ) else 0) =
      if q.Coprime b then 1 else 0 := by
  have hg : q.gcd b ≠ 0 := (Nat.gcd_pos_of_pos_left b hq).ne'
  have hs : q.divisors.filter (fun d => d ∣ b) = (q.gcd b).divisors := by
    ext d
    simp [Nat.mem_divisors, hq.ne', hg, Nat.dvd_gcd_iff]
  rw [← sum_filter, hs]
  have H := DFunLike.congr_fun (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℂ)) (q.gcd b)
  simpa only [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.one_apply,
    ArithmeticFunction.intCoe_apply, Nat.Coprime] using H

private theorem multiples_center (q a d : ℕ) (hq : 0 < q) (hd : d ∣ q) :
    ∑ b ∈ (range q).filter (fun b => d ∣ b), center q a b =
      if q/d ∣ a then ((q/d:ℕ):ℂ) else 0 := by
  obtain ⟨m,rfl⟩ := hd
  have hd : 0 < d := Nat.pos_of_mul_pos_right hq
  have hm : 0 < m := Nat.pos_of_mul_pos_left hq
  rw [Nat.mul_div_cancel_left _ hd, ← complete_center m a hm]
  symm
  apply sum_nbij' (d*·) (·/d)
  · intro j hj
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.mul_lt_mul_of_pos_left (mem_range.mp hj) hd), dvd_mul_right ..⟩
  · intro k hk
    apply mem_range.mpr
    exact (Nat.div_lt_iff_lt_mul hd).mpr (by simpa [Nat.mul_comm] using mem_range.mp (mem_filter.mp hk).1)
  · intro j _
    exact Nat.mul_div_cancel_left j hd
  · intro k hk
    exact Nat.mul_div_cancel' (mem_filter.mp hk).2
  · intro j _
    unfold center
    push_cast
    congr 1
    have hd' : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hm' : (m:ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp

/-- Exact Ramanujan sum at every natural frequency, including frequency zero. -/
private theorem center_divisor_formula (q a : ℕ) (hq : 0 < q) :
    ∑ b ∈ units q, center q a b =
      ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d:ℂ) *
        (if q/d ∣ a then ((q/d:ℕ):ℂ) else 0) := by
  calc
    _ = ∑ b ∈ range q, (∑ d ∈ q.divisors,
        if d ∣ b then (ArithmeticFunction.moebius d:ℂ) else 0)*center q a b := by
      simp only [gcd_indicator q _ hq, units, sum_filter]
      apply sum_congr rfl
      intro b _
      by_cases h : q.Coprime b <;> simp [h]
    _ = ∑ d ∈ q.divisors, ∑ b ∈ range q,
        (if d ∣ b then (ArithmeticFunction.moebius d:ℂ) else 0)*center q a b := by
      simp only [sum_mul]; rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      rw [← multiples_center q a d hq (Nat.dvd_of_mem_divisors hd), mul_sum, sum_filter]
      apply sum_congr rfl
      intro b _
      by_cases h : d ∣ b <;> simp [h]

private theorem reduced_center_eq_moebius (q a : ℕ) (hq : 0 < q) (ha : a.Coprime q) :
    ∑ b ∈ units q, center q a b = (ArithmeticFunction.moebius q:ℂ) := by
  rw [center_divisor_formula q a hq, sum_eq_single q]
  · simp [Nat.div_self hq]
  · intro d hd hne
    have hdq := Nat.dvd_of_mem_divisors hd
    have hnot : ¬ q/d ∣ a := by
      intro h
      have hone : q/d = 1 := Nat.eq_one_of_dvd_one (ha ▸ Nat.dvd_gcd h (Nat.div_dvd_of_dvd hdq))
      have H := Nat.mul_div_cancel' hdq
      rw [hone, mul_one] at H
      exact hne H
    simp [hnot]
  · simp [hq.ne']

private theorem mu_105 : ArithmeticFunction.moebius 105 = -1 := by
  rw [show 105 = 3 * (5 * 7) by decide,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (by decide : Nat.Coprime 3 (5 * 7)),
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (by decide : Nat.Coprime 5 7)]
  rw [ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 7)]
  norm_num

end GoldbachCert105

open GoldbachCert105 Finset

theorem PEqualNP.Outside.L_goldbach_cert_105 :
    ∀ a:ℕ, Nat.Coprime a 105 → (∑ b ∈ (Finset.range 105).filter (fun b => Nat.Coprime b 105),
      Complex.exp (((2*Real.pi*(a:ℝ)*b/105:ℝ):ℂ)*Complex.I))/(48:ℂ)=(-1:ℂ)/48 := by
  intro a ha
  have H := reduced_center_eq_moebius 105 a (by decide) ha
  rw [mu_105] at H
  have hfilter : units 105 = (range 105).filter (fun b => b.Coprime 105) := by
    ext b
    simp only [units, mem_filter]
    exact and_congr_right (fun _ => Nat.coprime_comm)
  simpa only [hfilter, center, Nat.cast_ofNat, Int.cast_neg, Int.cast_one] using
    congrArg (fun z : ℂ => z/48) H
