import Mathlib

open Finset

namespace Conjectures.Goldbach.FiniteMajorSignedErrorDivisorFold_aux

noncomputable def phase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def units (q : ℕ) := (range q).filter (fun a => Nat.Coprime a q)

private theorem complete_phase_sum (m a : ℕ) (hm : 0 < m) :
    ∑ b ∈ range m, phase ((a : ℝ) * (b : ℝ) / m) =
      if m ∣ a then (m : ℂ) else 0 := by
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I * a / m)
  have hz : z = 1 ↔ m ∣ a :=
    Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hm.ne'
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpow (b : ℕ) : phase ((a : ℝ) * (b : ℝ) / m) = z ^ b := by
    rw [← Complex.exp_nat_mul]
    unfold phase
    push_cast
    congr 1
    field_simp
  simp_rw [hpow]
  by_cases h : m ∣ a
  · simp [h, hz.mpr h]
  · simp only [h, ite_false]
    have hzm : z ^ m = 1 := by
      rw [← Complex.exp_nat_mul]
      have harg : (m : ℂ) * (2 * Real.pi * Complex.I * a / m) =
          a * (2 * Real.pi * Complex.I) := by
        field_simp
      rw [harg]
      exact Complex.exp_nat_mul_two_pi_mul_I a
    have hsum := geom_sum_mul z m
    rw [hzm, sub_self] at hsum
    exact (mul_eq_zero.mp hsum).resolve_right
      (sub_ne_zero.mpr (fun hz1 => h (hz.mp hz1)))

private theorem coprime_indicator (q b : ℕ) (hq : 0 < q) :
    (∑ d ∈ q.divisors, if d ∣ b then (ArithmeticFunction.moebius d : ℂ) else 0) =
      if Nat.Coprime b q then 1 else 0 := by
  have hg : Nat.gcd b q ≠ 0 := (Nat.gcd_pos_of_pos_right b hq).ne'
  have hs : q.divisors.filter (fun d => d ∣ b) = (Nat.gcd b q).divisors := by
    ext d
    simp [Nat.mem_divisors, hq.ne', hg, Nat.dvd_gcd_iff, and_comm]
  rw [← sum_filter, hs]
  have h := DFunLike.congr_fun
    (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℂ)) (Nat.gcd b q)
  simpa only [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.one_apply,
    ArithmeticFunction.intCoe_apply, Nat.Coprime] using h

private theorem multiples_phase_sum (q a d : ℕ) (hq : 0 < q) (hd : d ∣ q) :
    ∑ b ∈ (range q).filter (fun b => d ∣ b), phase ((a : ℝ) * (b : ℝ) / q) =
      if q / d ∣ a then ((q / d : ℕ) : ℂ) else 0 := by
  obtain ⟨m, rfl⟩ := hd
  have hd : 0 < d := Nat.pos_of_mul_pos_right hq
  have hm : 0 < m := Nat.pos_of_mul_pos_left hq
  rw [Nat.mul_div_cancel_left _ hd, ← complete_phase_sum m a hm]
  symm
  apply sum_nbij' (d * ·) (· / d)
  · intro j hj
    exact mem_filter.mpr
      ⟨mem_range.mpr (Nat.mul_lt_mul_of_pos_left (mem_range.mp hj) hd),
        dvd_mul_right d j⟩
  · intro k hk
    apply mem_range.mpr
    exact (Nat.div_lt_iff_lt_mul hd).mpr
      (by simpa [Nat.mul_comm] using mem_range.mp (mem_filter.mp hk).1)
  · intro j _
    exact Nat.mul_div_cancel_left j hd
  · intro k hk
    exact Nat.mul_div_cancel' (mem_filter.mp hk).2
  · intro j _
    unfold phase
    push_cast
    congr 1
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp

private theorem ramanujan_sum (q a : ℕ) (hq : 0 < q) :
    ∑ b ∈ units q, phase ((a : ℝ) * (b : ℝ) / q) =
      ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        (if q / d ∣ a then ((q / d : ℕ) : ℂ) else 0) := by
  calc
    _ = ∑ b ∈ range q,
        (∑ d ∈ q.divisors,
          if d ∣ b then (ArithmeticFunction.moebius d : ℂ) else 0) *
          phase ((a : ℝ) * (b : ℝ) / q) := by
      simp only [coprime_indicator q _ hq, units, sum_filter]
      apply sum_congr rfl
      intro b _
      by_cases h : Nat.Coprime b q <;> simp [h]
    _ = ∑ d ∈ q.divisors, ∑ b ∈ range q,
        (if d ∣ b then (ArithmeticFunction.moebius d : ℂ) else 0) *
          phase ((a : ℝ) * (b : ℝ) / q) := by
      simp only [sum_mul]
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      rw [← multiples_phase_sum q a d hq (Nat.dvd_of_mem_divisors hd),
        mul_sum, sum_filter]
      apply sum_congr rfl
      intro b _
      by_cases h : d ∣ b <;> simp [h]

private theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  have harg : (((2 * Real.pi * (x + y) : ℝ) : ℂ) * Complex.I) =
      (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) +
        (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_add]

private theorem phase_nat_period (x : ℝ) (m : ℕ) : phase (x + m) = phase x := by
  unfold phase
  have harg : (((2 * Real.pi * (x + (m : ℝ)) : ℝ) : ℂ) * Complex.I) =
      (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) +
        (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_add]
  rw [Complex.exp_nat_mul_two_pi_mul_I, mul_one]

private def lift (q n : ℕ) : ℕ := (q - 1) * n + q

private def frequency (q n r s : ℕ) : ℕ := r + s + lift q n

private theorem lift_add (q n : ℕ) (hq : 0 < q) :
    lift q n + n = q * (n + 1) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  simp [lift, Nat.succ_sub_one, Nat.succ_mul, Nat.succ_add]
  ring

private theorem frequency_add (q n r s : ℕ) (hq : 0 < q) :
    frequency q n r s + n = r + s + q * (n + 1) := by
  unfold frequency
  rw [add_assoc, add_assoc, lift_add q n hq]
  simp only [add_assoc]

set_option maxHeartbeats 800000 in
private theorem signed_phase_fold (q n a r s : ℕ) (hq : 0 < q) :
    phase (-(n : ℝ) * (a : ℝ) / q) *
        (phase ((r : ℝ) * (a : ℝ) / q) * phase ((s : ℝ) * (a : ℝ) / q)) =
      phase ((frequency q n r s : ℝ) * (a : ℝ) / q) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hfreq :
      (frequency q n r s : ℝ) + (n : ℝ) =
        (r : ℝ) + (s : ℝ) + (q : ℝ) * ((n : ℝ) + 1) := by
    exact_mod_cast frequency_add q n r s hq
  have htarget :
      (frequency q n r s : ℝ) * (a : ℝ) / q =
        (-(n : ℝ) * (a : ℝ) / q + (r : ℝ) * (a : ℝ) / q +
          (s : ℝ) * (a : ℝ) / q) + ((a * (n + 1) : ℕ) : ℝ) := by
    push_cast
    field_simp [hqR]
    linear_combination (a : ℝ) * hfreq
  calc
    phase (-(n : ℝ) * (a : ℝ) / q) *
        (phase ((r : ℝ) * (a : ℝ) / q) * phase ((s : ℝ) * (a : ℝ) / q)) =
      (phase (-(n : ℝ) * (a : ℝ) / q) * phase ((r : ℝ) * (a : ℝ) / q)) *
        phase ((s : ℝ) * (a : ℝ) / q) := by ring
    _ = phase (-(n : ℝ) * (a : ℝ) / q + (r : ℝ) * (a : ℝ) / q) *
        phase ((s : ℝ) * (a : ℝ) / q) := by rw [← phase_add]
    _ = phase (-(n : ℝ) * (a : ℝ) / q + (r : ℝ) * (a : ℝ) / q +
        (s : ℝ) * (a : ℝ) / q) := by rw [← phase_add]
    _ = phase ((frequency q n r s : ℝ) * (a : ℝ) / q) := by
      have hper := phase_nat_period
        (-(n : ℝ) * (a : ℝ) / q + (r : ℝ) * (a : ℝ) / q +
          (s : ℝ) * (a : ℝ) / q) (a * (n + 1))
      rw [htarget]
      exact hper.symm

private theorem ramanujan_divisor_formula (q a : ℕ) (hq : 0 < q) :
    ∑ b ∈ units q, phase ((a : ℝ) * (b : ℝ) / q) =
      ∑ d ∈ q.divisors,
        if d ∣ a then
          (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)
        else 0 := by
  rw [ramanujan_sum q a hq]
  let f : ℕ → ℂ := fun d =>
    if d ∣ a then (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) else 0
  calc
    (∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        (if q / d ∣ a then ((q / d : ℕ) : ℂ) else 0)) =
        ∑ d ∈ q.divisors, f (q / d) := by
      apply sum_congr rfl
      intro d hd
      have hcomp : q / (q / d) = d :=
        Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hq.ne'
      unfold f
      rw [hcomp]
      by_cases ha : q / d ∣ a <;> simp [ha]
      ring
    _ = ∑ d ∈ q.divisors, f d := Nat.sum_div_divisors q f
    _ = ∑ d ∈ q.divisors,
        if d ∣ a then
          (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)
        else 0 := rfl

private theorem frequency_dvd_iff_modEq (q n r s d : ℕ) (hq : 0 < q)
    (hdq : d ∣ q) :
    d ∣ frequency q n r s ↔ Nat.ModEq d (r + s) n := by
  have hprod : d ∣ q * (n + 1) := hdq.mul_right (n + 1)
  have hprod0 : Nat.ModEq d (q * (n + 1)) 0 := hprod.modEq_zero_nat
  constructor
  · intro hfreq
    have hsum : Nat.ModEq d (frequency q n r s + n) n := by
      simpa using hfreq.modEq_zero_nat.add_right n
    rw [frequency_add q n r s hq] at hsum
    have hleft : Nat.ModEq d (r + s + q * (n + 1)) (r + s) := by
      simpa [add_comm] using hprod0.add_right (r + s)
    exact hleft.symm.trans hsum
  · intro hmod
    have hleft : Nat.ModEq d (r + s) (r + s + q * (n + 1)) := by
      have h := hprod0.add_right (r + s)
      simpa [add_comm] using h.symm
    have hsum : Nat.ModEq d (r + s + q * (n + 1)) n := hleft.symm.trans hmod
    have hfreqmod : Nat.ModEq d (frequency q n r s + n) n := by
      rw [frequency_add q n r s hq]
      exact hsum
    have hzero : Nat.ModEq d (frequency q n r s) 0 := by
      have hcancel : Nat.ModEq d (frequency q n r s + n) (0 + n) := by
        simpa using hfreqmod
      exact Nat.ModEq.add_right_cancel' n hcancel
    exact Nat.modEq_zero_iff_dvd.mp hzero

private theorem reflected_residue_iff (d n r s : ℕ) (hd : 0 < d) :
    s % d = (n + d - r % d) % d ↔ Nat.ModEq d (r + s) n := by
  change Nat.ModEq d s (n + d - r % d) ↔ Nat.ModEq d (r + s) n
  constructor
  · intro hs
    have hr : Nat.ModEq d r (r % d) := (Nat.mod_modEq r d).symm
    have h := hr.add hs
    have hy : r % d < d := Nat.mod_lt r hd
    have heq : r % d + (n + d - r % d) = n + d := by omega
    rw [heq] at h
    exact h.trans (show Nat.ModEq d (n + d) n from Nat.add_modEq_right)
  · intro hmod
    have hsum : Nat.ModEq d (r + s) (n + d) :=
      hmod.trans (show Nat.ModEq d (n + d) n from Nat.add_modEq_right).symm
    have hys : Nat.ModEq d (r % d + s) (n + d) :=
      (Nat.mod_modEq r d).add_right s |>.trans hsum
    have hy : r % d < d := Nat.mod_lt r hd
    have heq : r % d + (n + d - r % d) = n + d := by omega
    have htarget :
        Nat.ModEq d (r % d + s) (r % d + (n + d - r % d)) := by
      rw [heq]
      exact hys
    exact Nat.ModEq.add_left_cancel' (r % d) htarget

private theorem fiber_reflection (d n : ℕ) (hd : 0 < d) (U : Finset ℕ)
    (F : ℕ → ℂ) :
    (∑ y ∈ range d,
        (∑ r ∈ U.filter (fun r => r % d = y), F r) *
          (∑ s ∈ U.filter (fun s => s % d = (n + d - y) % d), F s)) =
      ∑ r ∈ U, ∑ s ∈ U,
        if s % d = (n + d - r % d) % d then F r * F s else 0 := by
  classical
  let B : ℕ → ℂ := fun y =>
    ∑ s ∈ U.filter (fun s => s % d = (n + d - y) % d), F s
  calc
    (∑ y ∈ range d,
        (∑ r ∈ U.filter (fun r => r % d = y), F r) *
          (∑ s ∈ U.filter (fun s => s % d = (n + d - y) % d), F s)) =
        ∑ y ∈ range d, ∑ r ∈ U.filter (fun r => r % d = y), F r * B y := by
      apply sum_congr rfl
      intro y _
      rw [sum_mul]
    _ = ∑ y ∈ range d, ∑ r ∈ U.filter (fun r => r % d = y),
        F r * B (r % d) := by
      apply sum_congr rfl
      intro y _
      apply sum_congr rfl
      intro r hr
      rw [(mem_filter.mp hr).2]
    _ = ∑ r ∈ U, F r * B (r % d) := by
      rw [sum_fiberwise_of_maps_to
        (s := U) (t := range d) (g := fun r => r % d)
        (fun r _ => mem_range.mpr (Nat.mod_lt r hd))]
    _ = ∑ r ∈ U, ∑ s ∈ U,
        if s % d = (n + d - r % d) % d then F r * F s else 0 := by
      apply sum_congr rfl
      intro r _
      dsimp only [B]
      rw [sum_filter, mul_sum]
      apply sum_congr rfl
      intro s _
      by_cases hs : s % d = (n + d - r % d) % d <;> simp [hs]

private theorem fiber_correlation (S : Finset ℕ) (q n d : ℕ) (F : ℕ → ℂ)
    (hq : 0 < q) (hdq : d ∣ q) :
    (∑ y ∈ range d,
        (∑ r ∈ S.filter (fun r => r % d = y), F r) *
          (∑ s ∈ S.filter (fun s => s % d = (n + d - y) % d), F s)) =
      ∑ r ∈ S, ∑ s ∈ S,
        if d ∣ frequency q n r s then F r * F s else 0 := by
  classical
  have hd : 0 < d := Nat.pos_of_dvd_of_pos hdq hq
  calc
    (∑ y ∈ range d,
        (∑ r ∈ S.filter (fun r => r % d = y), F r) *
          (∑ s ∈ S.filter (fun s => s % d = (n + d - y) % d), F s)) =
        ∑ r ∈ S, ∑ s ∈ S,
          if s % d = (n + d - r % d) % d then F r * F s else 0 :=
      fiber_reflection d n hd S F
    _ = ∑ r ∈ S, ∑ s ∈ S,
        if d ∣ frequency q n r s then F r * F s else 0 := by
      apply sum_congr rfl
      intro r _
      apply sum_congr rfl
      intro s _
      have hiff := frequency_dvd_iff_modEq q n r s d hq hdq
      have hres := reflected_residue_iff d n r s hd
      by_cases hfreq : d ∣ frequency q n r s
      · have hs : s % d = (n + d - r % d) % d := hres.mpr (hiff.mp hfreq)
        simp [hfreq, hs]
      · have hs : s % d ≠ (n + d - r % d) % d := fun hs =>
          hfreq (hiff.mpr (hres.mp hs))
        simp [hfreq, hs]

private theorem lhs_expansion (q n : ℕ) (F : ℕ → ℂ) (hq : 0 < q) :
    (∑ a ∈ units q,
        phase (-(n : ℝ) * (a : ℝ) / q) *
          (∑ r ∈ units q, F r * phase ((r : ℝ) * (a : ℝ) / q)) ^ 2) =
      ∑ r ∈ units q, ∑ s ∈ units q, F r * F s *
        ∑ a ∈ units q, phase ((frequency q n r s : ℝ) * (a : ℝ) / q) := by
  classical
  calc
    (∑ a ∈ units q,
        phase (-(n : ℝ) * (a : ℝ) / q) *
          (∑ r ∈ units q, F r * phase ((r : ℝ) * (a : ℝ) / q)) ^ 2) =
        ∑ a ∈ units q, ∑ r ∈ units q, ∑ s ∈ units q,
          phase (-(n : ℝ) * (a : ℝ) / q) *
            ((F r * phase ((r : ℝ) * (a : ℝ) / q)) *
              (F s * phase ((s : ℝ) * (a : ℝ) / q))) := by
      apply sum_congr rfl
      intro a _
      rw [pow_two, sum_mul_sum]
      simp_rw [mul_sum]
    _ = ∑ a ∈ units q, ∑ r ∈ units q, ∑ s ∈ units q,
        (F r * F s) *
          phase ((frequency q n r s : ℝ) * (a : ℝ) / q) := by
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro r _
      apply sum_congr rfl
      intro s _
      calc
        phase (-(n : ℝ) * (a : ℝ) / q) *
            ((F r * phase ((r : ℝ) * (a : ℝ) / q)) *
              (F s * phase ((s : ℝ) * (a : ℝ) / q))) =
            (F r * F s) *
              (phase (-(n : ℝ) * (a : ℝ) / q) *
                (phase ((r : ℝ) * (a : ℝ) / q) *
                  phase ((s : ℝ) * (a : ℝ) / q))) := by ring
        _ = (F r * F s) *
            phase ((frequency q n r s : ℝ) * (a : ℝ) / q) := by
          rw [signed_phase_fold q n a r s hq]
    _ = ∑ r ∈ units q, ∑ a ∈ units q, ∑ s ∈ units q,
        (F r * F s) *
          phase ((frequency q n r s : ℝ) * (a : ℝ) / q) := by
      rw [sum_comm]
    _ = ∑ r ∈ units q, ∑ s ∈ units q, ∑ a ∈ units q,
        (F r * F s) *
          phase ((frequency q n r s : ℝ) * (a : ℝ) / q) := by
      apply sum_congr rfl
      intro r _
      rw [sum_comm]
    _ = ∑ r ∈ units q, ∑ s ∈ units q, F r * F s *
        ∑ a ∈ units q, phase ((frequency q n r s : ℝ) * (a : ℝ) / q) := by
      apply sum_congr rfl
      intro r _
      apply sum_congr rfl
      intro s _
      rw [← mul_sum]

private theorem rhs_expansion (q n : ℕ) (F : ℕ → ℂ) (hq : 0 < q) :
    (∑ d ∈ q.divisors,
        (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) *
          ∑ y ∈ range d,
            (∑ r ∈ (units q).filter (fun r => r % d = y), F r) *
              (∑ s ∈ (units q).filter
                (fun s => s % d = (n + d - y) % d), F s)) =
      ∑ r ∈ units q, ∑ s ∈ units q, F r * F s *
        ∑ d ∈ q.divisors,
          if d ∣ frequency q n r s then
            (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)
          else 0 := by
  classical
  calc
    (∑ d ∈ q.divisors,
        (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) *
          ∑ y ∈ range d,
            (∑ r ∈ (units q).filter (fun r => r % d = y), F r) *
              (∑ s ∈ (units q).filter
                (fun s => s % d = (n + d - y) % d), F s)) =
        ∑ d ∈ q.divisors,
          (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) *
            ∑ r ∈ units q, ∑ s ∈ units q,
              if d ∣ frequency q n r s then F r * F s else 0 := by
      apply sum_congr rfl
      intro d hd
      rw [fiber_correlation (units q) q n d F hq (Nat.dvd_of_mem_divisors hd)]
    _ = ∑ d ∈ q.divisors, ∑ r ∈ units q, ∑ s ∈ units q,
        (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) *
          (if d ∣ frequency q n r s then F r * F s else 0) := by
      apply sum_congr rfl
      intro d _
      rw [mul_sum]
      apply sum_congr rfl
      intro r _
      rw [mul_sum]
    _ = ∑ r ∈ units q, ∑ d ∈ q.divisors, ∑ s ∈ units q,
        (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) *
          (if d ∣ frequency q n r s then F r * F s else 0) := by
      rw [sum_comm]
    _ = ∑ r ∈ units q, ∑ s ∈ units q, ∑ d ∈ q.divisors,
        (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) *
          (if d ∣ frequency q n r s then F r * F s else 0) := by
      apply sum_congr rfl
      intro r _
      rw [sum_comm]
    _ = ∑ r ∈ units q, ∑ s ∈ units q, ∑ d ∈ q.divisors,
        (F r * F s) *
          (if d ∣ frequency q n r s then
            (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)
          else 0) := by
      apply sum_congr rfl
      intro r _
      apply sum_congr rfl
      intro s _
      apply sum_congr rfl
      intro d _
      by_cases h : d ∣ frequency q n r s <;> simp [h]
      ring
    _ = ∑ r ∈ units q, ∑ s ∈ units q, F r * F s *
        ∑ d ∈ q.divisors,
          if d ∣ frequency q n r s then
            (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)
          else 0 := by
      apply sum_congr rfl
      intro r _
      apply sum_congr rfl
      intro s _
      rw [← mul_sum]

theorem finite_major_signed_error_divisor_fold (q n : ℕ) (F : ℕ → ℂ)
    (hq : 0 < q) :
    (∑ a ∈ units q,
        phase (-(n : ℝ) * (a : ℝ) / q) *
          (∑ r ∈ units q, F r * phase ((r : ℝ) * (a : ℝ) / q)) ^ 2) =
      ∑ d ∈ q.divisors,
        (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) *
          ∑ y ∈ range d,
            (∑ r ∈ (units q).filter (fun r => r % d = y), F r) *
              (∑ s ∈ (units q).filter
                (fun s => s % d = (n + d - y) % d), F s) := by
  calc
    _ = ∑ r ∈ units q, ∑ s ∈ units q, F r * F s *
        ∑ a ∈ units q, phase ((frequency q n r s : ℝ) * (a : ℝ) / q) :=
      lhs_expansion q n F hq
    _ = ∑ r ∈ units q, ∑ s ∈ units q, F r * F s *
        ∑ d ∈ q.divisors,
          if d ∣ frequency q n r s then
            (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)
          else 0 := by
      apply sum_congr rfl
      intro r _
      apply sum_congr rfl
      intro s _
      rw [ramanujan_divisor_formula q (frequency q n r s) hq]
    _ = _ := (rhs_expansion q n F hq).symm

end Conjectures.Goldbach.FiniteMajorSignedErrorDivisorFold_aux

theorem Conjectures.Goldbach.FiniteMajorSignedErrorDivisorFold :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); ∀ (q n : ℕ) (F : ℕ → ℂ), 0<q → let U := (Finset.range q).filter (fun r => Nat.Coprime r q); let G := fun (d y : ℕ) => ∑ r ∈ U.filter (fun r => r % d = y), F r; (∑ a ∈ U, E (-(n:ℝ)*(a:ℝ)/q) * (∑ r ∈ U, F r*E ((a:ℝ)*(r:ℝ)/q))^2) = ∑ d ∈ q.divisors, (d:ℂ)*((ArithmeticFunction.moebius (q/d):ℤ):ℂ) * (∑ y ∈ Finset.range d, G d y * G d ((n+d-y)%d)) := by
  dsimp only
  intro q n F hq
  simpa only [Conjectures.Goldbach.FiniteMajorSignedErrorDivisorFold_aux.phase, Conjectures.Goldbach.FiniteMajorSignedErrorDivisorFold_aux.units, mul_comm] using
    Conjectures.Goldbach.FiniteMajorSignedErrorDivisorFold_aux.finite_major_signed_error_divisor_fold q n F hq
