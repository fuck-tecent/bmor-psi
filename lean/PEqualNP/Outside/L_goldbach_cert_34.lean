import Mathlib

open Finset

namespace PEqualNP.Outside

/-- The divisor sum of the Möbius function: `1` at `1`, `0` elsewhere. -/
theorem LGoldbachCertMobiusDivisorSum (n : ℕ) :
    (∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ)) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact h

/-- A geometric sum of roots of unity of order `m`, averaged over one period. -/
theorem LGoldbachCertGeomSum (m : ℕ) (hm : 0 < m) (a : ℕ) (ha : Nat.Coprime a m) :
    (∑ k ∈ Finset.range m, Complex.exp ((2 * Real.pi * (a : ℝ) * k / m : ℝ) * Complex.I))
      = if m = 1 then 1 else 0 := by
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hm.ne') with h1 | hm1
  · subst h1
    simp
  · rw [ite_eq_right (show ¬(m = 1) by omega)]
    have hterm : ∀ k : ℕ,
        Complex.exp ((2 * Real.pi * (a : ℝ) * k / m : ℝ) * Complex.I)
          = ((Complex.exp (2 * Real.pi * Complex.I / (m : ℂ))) ^ a) ^ k := by
      intro k
      have hexp : ((2 * Real.pi * (a : ℝ) * k / m : ℝ) : ℂ) * Complex.I
          = ((a * k : ℕ) : ℂ) * (2 * Real.pi * Complex.I / (m : ℂ)) := by
        push_cast
        field_simp
      rw [hexp, Complex.exp_nat_mul, pow_mul]
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    exact (Complex.isPrimitiveRoot_exp m hm.ne').pow_of_coprime a ha |>.geom_sum_eq_zero hm1

/-- The multiples of a divisor below `q`, reindexed. -/
theorem LGoldbachCertMultiples (q d : ℕ) (hd : d ∈ q.divisors) :
    (Finset.range q).filter (fun b => d ∣ b) = (Finset.range (q / d)).image (fun k => d * k) := by
  obtain ⟨hdvd, hq0⟩ := Nat.mem_divisors.mp hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hq0)
  have hkey : d * (q / d) = q := Nat.mul_div_cancel' hdvd
  ext b
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hbq, ⟨k, rfl⟩⟩
    refine ⟨k, ?_, rfl⟩
    have hlt : d * k < d * (q / d) := by rwa [hkey]
    exact Nat.lt_of_mul_lt_mul_left hlt
  · rintro ⟨k, hk, rfl⟩
    refine ⟨?_, dvd_mul_right d k⟩
    have hlt : d * k < d * (q / d) := (Nat.mul_lt_mul_left hd0).mpr hk
    rwa [hkey] at hlt

/-- The sum over the multiples of one divisor, collapsed to a root of unity sum. -/
theorem LGoldbachCertDivisorSlice (q d : ℕ) (hq : 0 < q) (hd : d ∈ q.divisors) (a : ℕ)
    (ha : Nat.Coprime a q) :
    (∑ b ∈ (Finset.range q).filter (fun b => d ∣ b),
        Complex.exp ((2 * Real.pi * (a : ℝ) * b / q : ℝ) * Complex.I))
      = if q / d = 1 then 1 else 0 := by
  obtain ⟨hdvd, hq0⟩ := Nat.mem_divisors.mp hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hq0)
  have hkey : d * (q / d) = q := Nat.mul_div_cancel' hdvd
  have hm0 : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hdvd) hd0
  have hcop : Nat.Coprime a (q / d) :=
    ha.coprime_dvd_right ⟨d, by rw [Nat.mul_comm]; exact hkey.symm⟩
  have hqcast : ((q : ℕ) : ℂ) = (d : ℂ) * ((q / d : ℕ) : ℂ) := by
    have h1 : (d : ℂ) * ((q / d : ℕ) : ℂ) = ((d * (q / d) : ℕ) : ℂ) := by push_cast; ring
    rw [h1, hkey]
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  have hmC : ((q / d : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
  rw [LGoldbachCertMultiples q d hd,
    Finset.sum_image (g := fun k => d * k) (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hd0 h)]
  refine Eq.trans (Finset.sum_congr rfl ?_) (LGoldbachCertGeomSum (q / d) hm0 a hcop)
  intro k _
  congr 1
  push_cast
  rw [hqcast]
  field_simp

/-- The normalized sum of a rational additive character over the units modulo `q`. -/
theorem LGoldbachCertUnitSum (q : ℕ) (hq : 0 < q) (a : ℕ) (ha : Nat.Coprime a q) :
    (∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
        Complex.exp ((2 * Real.pi * (a : ℝ) * b / q : ℝ) * Complex.I))
      = ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  classical
  have hgcd0 : ∀ b : ℕ, b < q → Nat.gcd b q ≠ 0 := by
    intro b _
    exact (Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_right b q) hq).ne'
  have hind : ∀ b < q, (if Nat.Coprime b q then (1 : ℂ) else 0)
      = ∑ d ∈ q.divisors, if d ∣ b then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0 := by
    intro b hb
    have hdiv : (Nat.gcd b q).divisors = q.divisors.filter (fun d => d ∣ b) := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, -⟩
        exact ⟨⟨h2, hq.ne'⟩, h1⟩
      · rintro ⟨⟨h1, -⟩, h2⟩
        exact ⟨⟨h2, h1⟩, hgcd0 b hb⟩
    have hsum := LGoldbachCertMobiusDivisorSum (Nat.gcd b q)
    rw [hdiv, Finset.sum_filter] at hsum
    rw [hsum]
  calc (∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
          Complex.exp ((2 * Real.pi * (a : ℝ) * b / q : ℝ) * Complex.I))
      = ∑ b ∈ Finset.range q, (if Nat.Coprime b q then (1 : ℂ) else 0) *
          Complex.exp ((2 * Real.pi * (a : ℝ) * b / q : ℝ) * Complex.I) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro b _
        by_cases hc : Nat.Coprime b q <;> simp [hc]
    _ = ∑ b ∈ Finset.range q, Complex.exp ((2 * Real.pi * (a : ℝ) * b / q : ℝ) * Complex.I) *
          (∑ d ∈ q.divisors, if d ∣ b then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [hind b (Finset.mem_range.mp hb), mul_comm]
    _ = ∑ b ∈ Finset.range q, ∑ d ∈ q.divisors,
          Complex.exp ((2 * Real.pi * (a : ℝ) * b / q : ℝ) * Complex.I) *
            (if d ∣ b then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.mul_sum]
    _ = ∑ d ∈ q.divisors, ∑ b ∈ Finset.range q,
          Complex.exp ((2 * Real.pi * (a : ℝ) * b / q : ℝ) * Complex.I) *
            (if d ∣ b then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
          ∑ b ∈ (Finset.range q).filter (fun b => d ∣ b),
            Complex.exp ((2 * Real.pi * (a : ℝ) * b / q : ℝ) * Complex.I) := by
        apply Finset.sum_congr rfl
        intro d _
        rw [Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro b _
        by_cases hdb : d ∣ b <;> simp [hdb, mul_comm]
    _ = ∑ d ∈ q.divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℂ) * (if q / d = 1 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [LGoldbachCertDivisorSlice q d hq hd a ha]
    _ = ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
        have hmem : q ∈ q.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hq.ne'⟩
        rw [Finset.sum_eq_single q]
        · rw [Nat.div_self hq]; simp
        · intro d hd hdq
          have hdvd : d ∣ q := (Nat.mem_divisors.mp hd).1
          have hne : q / d ≠ 1 := by
            intro h1
            refine hdq ?_
            have h2 : d * (q / d) = q := Nat.mul_div_cancel' hdvd
            rw [h1, Nat.mul_one] at h2
            exact h2
          simp [hne]
        · intro hqnot
          exact absurd hmem hqnot

end PEqualNP.Outside

theorem PEqualNP.Outside.L_goldbach_cert_34 :
    ∀ a:ℕ, Nat.Coprime a 34 → (∑ b ∈ (Finset.range 34).filter (fun b => Nat.Coprime b 34), Complex.exp (((2*Real.pi*(a:ℝ)*b/34:ℝ):ℂ)*Complex.I))/(16:ℂ)=(1:ℂ)/16 := by
  intro a ha
  have hS := PEqualNP.Outside.LGoldbachCertUnitSum 34 (by norm_num) a ha
  simp only [Nat.cast_ofNat] at hS
  rw [hS]
  have hmu : ((ArithmeticFunction.moebius 34 : ℤ) : ℂ) = (1 : ℂ) := by
    rw [show (34 : Nat) = 2 * 17 by norm_num,
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (m := 2) (n := 17) (by norm_num),
        ArithmeticFunction.moebius_apply_prime (p := 2) (by norm_num),
        ArithmeticFunction.moebius_apply_prime (p := 17) (by norm_num)]
    norm_num
  rw [hmu]
