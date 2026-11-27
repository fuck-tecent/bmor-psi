import Mathlib

theorem PEqualNP.Outside.L_goldbach_finite_fixed_chi_constant_mode :
    ∀ a q : ℕ, 0 < q → Nat.Coprime a q → (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), Complex.exp (Complex.I*((2*Real.pi*(a:ℝ)*(r:ℝ)/(q:ℝ):ℝ):ℂ))) = (ArithmeticFunction.moebius q:ℂ) := by
  intro a q hq haq
  let E : ℕ → ℂ := fun r =>
    Complex.exp (Complex.I * ((2 * Real.pi * (a : ℝ) * (r : ℝ) / (q : ℝ) : ℝ) : ℂ))
  have hq0 : q ≠ 0 := hq.ne'
  have hind : ∀ r : ℕ, (if Nat.Coprime r q then (1 : ℂ) else 0) =
      ∑ d ∈ q.divisors, if d ∣ r then (ArithmeticFunction.moebius d : ℂ) else 0 := by
    intro r
    have hg0 : Nat.gcd r q ≠ 0 := (Nat.gcd_pos_of_pos_right r hq).ne'
    have hdiv : (Nat.gcd r q).divisors = q.divisors.filter (fun d => d ∣ r) := by
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff, hq0, hg0,
        ne_eq, not_false_eq_true, and_true]
      tauto
    have hmz : ((ArithmeticFunction.moebius * ArithmeticFunction.zeta : ArithmeticFunction ℤ) (Nat.gcd r q)) =
        (1 : ArithmeticFunction ℤ) (Nat.gcd r q) := by
      rw [ArithmeticFunction.moebius_mul_coe_zeta]
    rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at hmz
    have hmzC : (∑ d ∈ (Nat.gcd r q).divisors, (ArithmeticFunction.moebius d : ℂ)) =
        if Nat.gcd r q = 1 then (1 : ℂ) else 0 := by
      have hc := congrArg (Int.cast (R := ℂ)) hmz
      rw [Int.cast_sum] at hc
      rw [hc]
      split_ifs <;> simp
    rw [hdiv, Finset.sum_filter] at hmzC
    simpa only [Nat.coprime_iff_gcd_eq_one] using hmzC.symm
  have hswap : ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), E r =
      ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) *
        ∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), E r := by
    calc
      ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), E r
        = ∑ r ∈ Finset.range q, (if Nat.Coprime r q then (1 : ℂ) else 0) * E r := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun r _ => ?_
          split_ifs <;> simp [E]
      _ = ∑ r ∈ Finset.range q,
            (∑ d ∈ q.divisors, if d ∣ r then (ArithmeticFunction.moebius d : ℂ) else 0) * E r := by
          refine Finset.sum_congr rfl fun r _ => by rw [hind r]
      _ = ∑ r ∈ Finset.range q, ∑ d ∈ q.divisors,
            (if d ∣ r then (ArithmeticFunction.moebius d : ℂ) * E r else 0) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun d _ => ?_
          split_ifs <;> simp
      _ = ∑ d ∈ q.divisors, ∑ r ∈ Finset.range q,
            (if d ∣ r then (ArithmeticFunction.moebius d : ℂ) * E r else 0) := Finset.sum_comm
      _ = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) *
            ∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), E r := by
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.mul_sum, Finset.sum_filter]
  have hinner : ∀ d ∈ q.divisors,
      (∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), E r) = if d = q then (1 : ℂ) else 0 := by
    intro d hd
    have hd_dvd : d ∣ q := Nat.dvd_of_mem_divisors hd
    have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
    let m : ℕ := q / d
    have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd hq hd_dvd) hd_pos
    have hdm : d * m = q := Nat.mul_div_cancel' hd_dvd
    let z : ℂ := Complex.exp (((2 * Real.pi * (a : ℝ) / (m : ℝ) : ℝ) : ℂ) * Complex.I)
    have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
    have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm_pos.ne'
    have hbij : (∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), E r) =
        ∑ k ∈ Finset.range m, z ^ k := by
      symm
      refine Finset.sum_bij (fun k _ => d * k) ?_ ?_ ?_ ?_
      · intro k hk
        rw [Finset.mem_filter, Finset.mem_range]
        rw [Finset.mem_range] at hk
        refine ⟨?_, dvd_mul_right d k⟩
        rw [← hdm]
        exact Nat.mul_lt_mul_of_pos_left hk hd_pos
      · intro k₁ _ k₂ _ hkeq
        exact Nat.eq_of_mul_eq_mul_left hd_pos hkeq
      · intro r hr
        rw [Finset.mem_filter, Finset.mem_range] at hr
        rcases hr with ⟨hrq, ⟨k, rfl⟩⟩
        refine ⟨k, Finset.mem_range.mpr ?_, rfl⟩
        rw [← hdm] at hrq
        exact Nat.lt_of_mul_lt_mul_left hrq
      · intro k _
        simp only [z, E, ← Complex.exp_nat_mul]
        apply congrArg Complex.exp
        have hqC : (q : ℂ) = (d : ℂ) * (m : ℂ) := by
          rw [← hdm, Nat.cast_mul]
        simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat,
          Complex.ofReal_natCast, Nat.cast_mul]
        rw [hqC]
        field_simp [hd0, hm0]
    rw [hbij]
    by_cases hdq : d = q
    · rw [ite_eq_left_iff.mpr fun h => False.elim (h hdq)]
      have hm1 : m = 1 := by
        dsimp [m]
        rw [hdq, Nat.div_self hq]
      rw [hm1, Finset.range_one, Finset.sum_singleton, pow_zero]
    · rw [ite_eq_right_iff.mpr fun h => False.elim (hdq h)]
      have hm_ne1 : m ≠ 1 := by
        intro hm1
        apply hdq
        have := hdm
        rw [hm1, mul_one] at this
        exact this
      have hz_ne1 : z ≠ 1 := by
        intro hz1
        have hz1' : Complex.exp (2 * ↑Real.pi * Complex.I * (a : ℂ) / (m : ℂ)) = 1 := by
          rw [← hz1]
          apply congrArg Complex.exp
          simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat,
            Complex.ofReal_natCast]
          ring
        have hma : m ∣ a :=
          (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (k := a) (N := m) hm_pos.ne').mp hz1'
        have hmq : m ∣ q := ⟨d, by rw [mul_comm, hdm]⟩
        have hmg : m ∣ Nat.gcd a q := Nat.dvd_gcd hma hmq
        rw [haq.gcd_eq_one] at hmg
        exact hm_ne1 (Nat.eq_one_of_dvd_one hmg)
      rw [geom_sum_eq hz_ne1 m]
      have hzm : z ^ m = 1 := by
        have hexp : z ^ m = Complex.exp ((a : ℕ) * (2 * ↑Real.pi * Complex.I)) := by
          dsimp [z]
          rw [← Complex.exp_nat_mul]
          apply congrArg Complex.exp
          simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat,
            Complex.ofReal_natCast]
          field_simp [hm0]
        rw [hexp, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]
      rw [hzm, sub_self, zero_div]
  rw [hswap]
  have hq_mem : q ∈ q.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hq0⟩
  calc
    ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) *
        ∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), E r
      = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) * (if d = q then (1 : ℂ) else 0) := by
        refine Finset.sum_congr rfl fun d hd => by rw [hinner d hd]
    _ = ∑ d ∈ q.divisors, if d = q then (ArithmeticFunction.moebius d : ℂ) else 0 := by
        refine Finset.sum_congr rfl fun d _ => by split_ifs <;> simp
    _ = (ArithmeticFunction.moebius q : ℂ) := by
        rw [Finset.sum_ite_eq']
        simp [hq_mem]
