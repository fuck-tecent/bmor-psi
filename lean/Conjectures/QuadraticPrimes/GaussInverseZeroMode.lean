import Mathlib

open Finset

namespace Conjectures.QuadraticPrimes.GaussInverseZeroMode_aux

theorem charSum (n : ℕ) [NeZero n] (t : ZMod n) :
    ∑ x : ZMod n, ZMod.stdAddChar (t * x) = if t = 0 then (n : ℂ) else 0 := by
  split_ifs with h
  · simp only [h, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul, mul_one]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar n h)

theorem charSumRange (n : ℕ) [NeZero n] (k : ℤ) :
    ∑ j ∈ range n, ZMod.stdAddChar ((k : ZMod n) * (j : ZMod n)) =
      if (n : ℤ) ∣ k then (n : ℂ) else 0 := by
  calc ∑ j ∈ range n, ZMod.stdAddChar ((k : ZMod n) * (j : ZMod n))
      = ∑ x : ZMod n, ZMod.stdAddChar ((k : ZMod n) * x) := by
        apply Finset.sum_bij (fun (a : ℕ) _ => (a : ZMod n))
        · intro a _
          exact Finset.mem_univ _
        · intro a ha b hb hab
          simpa only [ZMod.val_natCast_of_lt (Finset.mem_range.mp ha),
            ZMod.val_natCast_of_lt (Finset.mem_range.mp hb)] using congrArg ZMod.val hab
        · intro x _
          exact ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
        · intro a _
          rfl
    _ = if (k : ZMod n) = 0 then (n : ℂ) else 0 := charSum n (k : ZMod n)
    _ = if (n : ℤ) ∣ k then (n : ℂ) else 0 := by
        by_cases h : (k : ZMod n) = 0
        · have h2 : (n : ℤ) ∣ k := (ZMod.intCast_zmod_eq_zero_iff_dvd k n).mp h
          simp [h, h2]
        · have h2 : ¬ (n : ℤ) ∣ k :=
            fun hc => h ((ZMod.intCast_zmod_eq_zero_iff_dvd k n).mpr hc)
          simp [h, h2]

theorem multiplesChar (q : ℕ) [NeZero q] (d : ℕ) (hd : d ∣ q) (k : ℤ) :
    ∑ r ∈ (range q).filter (fun r => d ∣ r), ZMod.stdAddChar ((k : ZMod q) * (r : ZMod q)) =
      if ((q / d : ℕ) : ℤ) ∣ k then ((q / d : ℕ) : ℂ) else 0 := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  obtain ⟨m, rfl⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_mul_pos_right hq
  have hm0 : 0 < m := Nat.pos_of_mul_pos_left hq
  haveI : NeZero m := ⟨hm0.ne'⟩
  rw [Nat.mul_div_cancel_left _ hd0, ← charSumRange m k]
  symm
  apply Finset.sum_nbij' (d * ·) (· / d)
  · intro j hj
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp hj) hd0), ⟨j, rfl⟩⟩
  · intro r hr
    apply Finset.mem_range.mpr
    exact (Nat.div_lt_iff_lt_mul hd0).mpr
      (by simpa [Nat.mul_comm] using Finset.mem_range.mp (Finset.mem_filter.mp hr).1)
  · intro j _
    exact Nat.mul_div_cancel_left j hd0
  · intro r hr
    exact Nat.mul_div_cancel' (Finset.mem_filter.mp hr).2
  · intro j _
    have e1 : (k : ZMod m) * (j : ZMod m) = ((k * (j : ℤ) : ℤ) : ZMod m) := by
      push_cast; ring
    have e2 : (k : ZMod (d * m)) * ((d * j : ℕ) : ZMod (d * m))
        = ((k * ((d * j : ℕ) : ℤ) : ℤ) : ZMod (d * m)) := by
      push_cast; ring
    rw [e1, e2, ZMod.stdAddChar_coe (N := m) (k * (j : ℤ)),
      ZMod.stdAddChar_coe (N := d * m) (k * ((d * j : ℕ) : ℤ))]
    congr 1
    push_cast
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
    field_simp

theorem gcdIndicator (q r : ℕ) (hq : 0 < q) :
    (∑ d ∈ q.divisors, if d ∣ r then (ArithmeticFunction.moebius d : ℂ) else 0) =
      if q.Coprime r then 1 else 0 := by
  have hg : q.gcd r ≠ 0 := (Nat.gcd_pos_of_pos_left r hq).ne'
  have hs : q.divisors.filter (fun d => d ∣ r) = (q.gcd r).divisors := by
    ext d
    simp [Nat.mem_divisors, hq.ne', hg, Nat.dvd_gcd_iff]
  rw [← Finset.sum_filter, hs]
  have H := DFunLike.congr_fun (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℂ)) (q.gcd r)
  simpa only [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.one_apply,
    ArithmeticFunction.intCoe_apply, Nat.Coprime] using H

theorem sumUnitsRange (q : ℕ) [NeZero q] (G : ZMod q → ℂ) :
    (∑ u : (ZMod q)ˣ, G (u : ZMod q)) =
      ∑ r ∈ (range q).filter (fun r => Nat.Coprime r q), G (r : ZMod q) := by
  refine Finset.sum_bij (fun (u : (ZMod q)ˣ) _ => (u : ZMod q).val) ?_ ?_ ?_ ?_
  · intro u _
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (ZMod.val_lt (u : ZMod q)), ZMod.val_coe_unit_coprime u⟩
  · intro u _ v _ h
    apply Units.ext
    calc (u : ZMod q) = (((u : ZMod q).val : ℕ) : ZMod q) := (ZMod.natCast_zmod_val _).symm
      _ = (((v : ZMod q).val : ℕ) : ZMod q) := by rw [h]
      _ = (v : ZMod q) := ZMod.natCast_zmod_val _
  · intro r hr
    obtain ⟨hqr, hcop⟩ := Finset.mem_filter.mp hr
    refine ⟨ZMod.unitOfCoprime r hcop, Finset.mem_univ _, ?_⟩
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hqr)
  · intro u _
    rw [ZMod.natCast_zmod_val]

end Conjectures.QuadraticPrimes.GaussInverseZeroMode_aux

open Conjectures.QuadraticPrimes.GaussInverseZeroMode_aux

theorem Conjectures.QuadraticPrimes.GaussInverseZeroMode :
    ∀ (b : ℕ) [NeZero b] (k : ℤ),
  (∑ u : (ZMod b)ˣ, ZMod.stdAddChar ((k : ZMod b) * (↑(u⁻¹) : ZMod b))) =
    ∑ d ∈ (Nat.gcd b k.natAbs).divisors, (d : ℂ) * (ArithmeticFunction.moebius (b/d) : ℂ) := by
  intro b hb0inst k
  classical
  have hb : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
  have hset : b.divisors.filter (fun e => e ∣ k.natAbs) = (Nat.gcd b k.natAbs).divisors := by
    rw [← Nat.divisors_filter_dvd_of_dvd (n := b) (m := Nat.gcd b k.natAbs) hb.ne'
      (Nat.gcd_dvd_left b k.natAbs)]
    apply Finset.filter_congr
    intro e he
    rw [Nat.mem_divisors] at he
    constructor
    · intro h
      exact Nat.dvd_gcd he.1 h
    · intro h
      exact Nat.dvd_trans h (Nat.gcd_dvd_right b k.natAbs)
  have hinv : (∑ u : (ZMod b)ˣ, ZMod.stdAddChar ((k : ZMod b) * (↑(u⁻¹) : ZMod b))) =
      ∑ u : (ZMod b)ˣ, ZMod.stdAddChar ((k : ZMod b) * (↑u : ZMod b)) := by
    refine Finset.sum_bij (fun (u : (ZMod b)ˣ) _ => u⁻¹) ?_ ?_ ?_ ?_
    · intro u _
      exact Finset.mem_univ _
    · intro u _ v _ h
      exact inv_injective h
    · intro v _
      exact ⟨v⁻¹, Finset.mem_univ _, inv_inv v⟩
    · intro u _
      rfl
  calc (∑ u : (ZMod b)ˣ, ZMod.stdAddChar ((k : ZMod b) * (↑(u⁻¹) : ZMod b)))
      = ∑ u : (ZMod b)ˣ, ZMod.stdAddChar ((k : ZMod b) * (↑u : ZMod b)) := hinv
    _ = ∑ r ∈ (range b).filter (fun r => Nat.Coprime r b),
          ZMod.stdAddChar ((k : ZMod b) * (r : ZMod b)) :=
        sumUnitsRange b (fun a : ZMod b => ZMod.stdAddChar ((k : ZMod b) * a))
    _ = ∑ r ∈ range b, (∑ d ∈ b.divisors,
          if d ∣ r then (ArithmeticFunction.moebius d : ℂ) else 0) *
          ZMod.stdAddChar ((k : ZMod b) * (r : ZMod b)) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro r _
        rw [gcdIndicator b r hb]
        by_cases h : Nat.Coprime r b
        · rw [if_pos (Nat.coprime_comm.mpr h), if_pos h, one_mul]
        · rw [if_neg (fun hc => h (Nat.coprime_comm.mp hc)), if_neg h, zero_mul]
    _ = ∑ d ∈ b.divisors, ∑ r ∈ range b,
          (if d ∣ r then (ArithmeticFunction.moebius d : ℂ) else 0) *
            ZMod.stdAddChar ((k : ZMod b) * (r : ZMod b)) := by
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
    _ = ∑ d ∈ b.divisors, (ArithmeticFunction.moebius d : ℂ) *
          ∑ r ∈ (range b).filter (fun r => d ∣ r),
            ZMod.stdAddChar ((k : ZMod b) * (r : ZMod b)) := by
        apply Finset.sum_congr rfl
        intro d _
        rw [Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro r _
        by_cases h : d ∣ r <;> simp [h]
    _ = ∑ d ∈ b.divisors, (ArithmeticFunction.moebius d : ℂ) *
          (if ((b / d : ℕ) : ℤ) ∣ k then ((b / d : ℕ) : ℂ) else 0) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [multiplesChar b d (Nat.dvd_of_mem_divisors hd) k]
    _ = ∑ d ∈ b.divisors, (ArithmeticFunction.moebius d : ℂ) *
          (if b / d ∣ k.natAbs then ((b / d : ℕ) : ℂ) else 0) := by
        apply Finset.sum_congr rfl
        intro d _
        have hconv : ((b / d : ℕ) : ℤ) ∣ k ↔ b / d ∣ k.natAbs := Int.natCast_dvd
        by_cases h : b / d ∣ k.natAbs
        · have h2 : ((b / d : ℕ) : ℤ) ∣ k := hconv.mpr h
          simp only [h, h2, if_true]
        · have h2 : ¬ ((b / d : ℕ) : ℤ) ∣ k := fun hc => h (hconv.mp hc)
          simp only [h, h2, if_false]
    _ = ∑ e ∈ b.divisors, (ArithmeticFunction.moebius (b / e) : ℂ) *
          (if e ∣ k.natAbs then (e : ℂ) else 0) := by
        rw [← Nat.sum_div_divisors b
          (fun e => (ArithmeticFunction.moebius (b / e) : ℂ) *
            (if e ∣ k.natAbs then (e : ℂ) else 0))]
        apply Finset.sum_congr rfl
        intro d hd
        have hdvd : d ∣ b := Nat.dvd_of_mem_divisors hd
        have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd hb
        have hbd0 : 0 < b / d := Nat.div_pos (Nat.le_of_dvd hb hdvd) hd0
        have hkey : b / (b / d) = d := by
          calc b / (b / d) = (d * (b / d)) / (b / d) := by rw [Nat.mul_div_cancel' hdvd]
            _ = d := by rw [Nat.mul_comm d (b / d), Nat.mul_div_cancel_left _ hbd0]
        rw [hkey]
    _ = ∑ e ∈ b.divisors.filter (fun e => e ∣ k.natAbs),
          (ArithmeticFunction.moebius (b / e) : ℂ) * (e : ℂ) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro e _
        by_cases h : e ∣ k.natAbs <;> simp [h]
    _ = ∑ e ∈ (Nat.gcd b k.natAbs).divisors, (e : ℂ) * (ArithmeticFunction.moebius (b/e) : ℂ) := by
        rw [hset]
        apply Finset.sum_congr rfl
        intro e _
        exact mul_comm _ _
