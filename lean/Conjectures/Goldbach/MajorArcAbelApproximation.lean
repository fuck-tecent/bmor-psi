import Mathlib

noncomputable def abelW (k : ℕ) : ℝ := if Nat.Prime k then Real.log (k : ℝ) else 0

noncomputable def abelE (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

noncomputable def abelC (n q r : ℕ) (β : ℝ) : ℂ :=
  ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % q = r), (abelW k : ℂ) * abelE ((k : ℝ) * β)

noncomputable def abelK (n : ℕ) (β : ℝ) : ℂ := ∑ k ∈ Finset.Icc 1 n, abelE ((k : ℝ) * β)

-- @helper class_split
lemma class_split_aux_norm_abelE (x : ℝ) : ‖abelE x‖ = 1 := by
  unfold abelE
  have hre : (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I).re = 0 := by simp
  rw [Complex.norm_exp, hre, Real.exp_zero]

lemma class_split_aux_abelE_add (x y : ℝ) :
    abelE (x + y) = abelE x * abelE y := by
  unfold abelE
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma class_split_aux_abelE_int_shift (x : ℝ) (m : ℕ) :
    abelE (x + (m : ℝ)) = abelE x := by
  rw [class_split_aux_abelE_add]
  have h1 : abelE (m : ℝ) = 1 := by
    unfold abelE
    have h2 : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I)
        = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [h2]
    exact Complex.exp_nat_mul_two_pi_mul_I m
  rw [h1, mul_one]

lemma class_split_aux_phase_mod (k q a : ℕ) (hq : 1 ≤ q) :
    abelE ((k : ℝ) * (a : ℝ) / q) = abelE (((k % q : ℕ) : ℝ) * (a : ℝ) / q) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hk : (k : ℝ) = (q : ℝ) * ((k / q : ℕ) : ℝ) + ((k % q : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod k q).symm
  have hkey : (k : ℝ) * (a : ℝ) / q
      = ((k % q : ℕ) : ℝ) * (a : ℝ) / q + (((k / q) * a : ℕ) : ℝ) := by
    rw [hk]
    push_cast
    field_simp
    ring
  rw [hkey, class_split_aux_abelE_int_shift]

lemma class_split_aux_w_nonneg (k : ℕ) : 0 ≤ abelW k := by
  unfold abelW
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_le)
  · exact le_rfl

lemma class_split_aux_norm_abelC (n q r : ℕ) (β : ℝ) :
    ‖abelC n q r β‖
      ≤ ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % q = r), abelW k := by
  unfold abelC
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum ?_
  intro k _
  have h1 : ‖(abelW k : ℂ) * abelE ((k : ℝ) * β)‖ = abelW k := by
    rw [norm_mul, class_split_aux_norm_abelE, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (class_split_aux_w_nonneg k)]
  exact le_of_eq h1

lemma class_split_aux_complete_phase_sum (m a : ℕ) (hm : 0 < m) :
    ∑ b ∈ Finset.range m, abelE ((a : ℝ) * (b : ℝ) / m) =
      if m ∣ a then (m : ℂ) else 0 := by
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I * a / m)
  have hz : z = 1 ↔ m ∣ a :=
    Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hm.ne'
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpow (b : ℕ) : abelE ((a : ℝ) * (b : ℝ) / m) = z ^ b := by
    rw [← Complex.exp_nat_mul]
    unfold abelE
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

lemma class_split_aux_coprime_indicator (q b : ℕ) (hq : 0 < q) :
    (∑ d ∈ q.divisors, if d ∣ b then (ArithmeticFunction.moebius d : ℂ) else 0) =
      if Nat.Coprime b q then 1 else 0 := by
  have hg : Nat.gcd b q ≠ 0 := (Nat.gcd_pos_of_pos_right b hq).ne'
  have hs : q.divisors.filter (fun d => d ∣ b) = (Nat.gcd b q).divisors := by
    ext d
    simp [Nat.mem_divisors, hq.ne', hg, Nat.dvd_gcd_iff, and_comm]
  rw [← Finset.sum_filter, hs]
  have h := DFunLike.congr_fun
    (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℂ)) (Nat.gcd b q)
  simpa only [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.one_apply,
    ArithmeticFunction.intCoe_apply, Nat.Coprime] using h

lemma class_split_aux_multiples_phase_sum (q a d : ℕ) (hq : 0 < q) (hd : d ∣ q) :
    ∑ b ∈ (Finset.range q).filter (fun b => d ∣ b),
        abelE ((a : ℝ) * (b : ℝ) / q) =
      if q / d ∣ a then ((q / d : ℕ) : ℂ) else 0 := by
  obtain ⟨m, rfl⟩ := hd
  have hd : 0 < d := Nat.pos_of_mul_pos_right hq
  have hm : 0 < m := Nat.pos_of_mul_pos_left hq
  rw [Nat.mul_div_cancel_left _ hd, ← class_split_aux_complete_phase_sum m a hm]
  symm
  apply Finset.sum_nbij' (d * ·) (· / d)
  · intro j hj
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp hj) hd),
        dvd_mul_right d j⟩
  · intro k hk
    apply Finset.mem_range.mpr
    exact (Nat.div_lt_iff_lt_mul hd).mpr
      (by simpa [Nat.mul_comm] using Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
  · intro j _
    exact Nat.mul_div_cancel_left j hd
  · intro k hk
    exact Nat.mul_div_cancel' (Finset.mem_filter.mp hk).2
  · intro j _
    unfold abelE
    push_cast
    congr 1
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp

lemma class_split_aux_ramanujan_sum (q a : ℕ) (hq : 0 < q) :
    ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
        abelE ((a : ℝ) * (b : ℝ) / q) =
      ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        (if q / d ∣ a then ((q / d : ℕ) : ℂ) else 0) := by
  calc
    _ = ∑ b ∈ Finset.range q,
        (∑ d ∈ q.divisors,
          if d ∣ b then (ArithmeticFunction.moebius d : ℂ) else 0) *
          abelE ((a : ℝ) * (b : ℝ) / q) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      rw [class_split_aux_coprime_indicator q b hq]
      by_cases h : Nat.Coprime b q <;> simp [h]
    _ = ∑ d ∈ q.divisors, ∑ b ∈ Finset.range q,
        (if d ∣ b then (ArithmeticFunction.moebius d : ℂ) else 0) *
          abelE ((a : ℝ) * (b : ℝ) / q) := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← class_split_aux_multiples_phase_sum q a d hq (Nat.dvd_of_mem_divisors hd),
        Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : d ∣ b <;> simp [h]

lemma class_split_aux_ramanujan_divisor_formula (q a : ℕ) (hq : 0 < q) :
    ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
        abelE ((a : ℝ) * (b : ℝ) / q) =
      ∑ d ∈ q.divisors,
        if d ∣ a then
          (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)
        else 0 := by
  rw [class_split_aux_ramanujan_sum q a hq]
  let f : ℕ → ℂ := fun d =>
    if d ∣ a then (d : ℂ) * ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) else 0
  calc
    (∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        (if q / d ∣ a then ((q / d : ℕ) : ℂ) else 0)) =
        ∑ d ∈ q.divisors, f (q / d) := by
      apply Finset.sum_congr rfl
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

lemma class_split_aux_ramanujan (q a : ℕ) (hq : 1 ≤ q) (ha : Nat.Coprime a q) :
    ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
        abelE ((r : ℝ) * (a : ℝ) / q) = (ArithmeticFunction.moebius q : ℂ) := by
  have hqpos : 0 < q := by omega
  have hcomm : ∀ r : ℕ, abelE ((r : ℝ) * (a : ℝ) / q) = abelE ((a : ℝ) * (r : ℝ) / q) := by
    intro r
    unfold abelE
    congr 1
    push_cast
    ring
  simp_rw [hcomm]
  rw [class_split_aux_ramanujan_divisor_formula q a hqpos]
  have h_one : 1 ∈ q.divisors := by
    simp [Nat.mem_divisors, hqpos.ne']
  rw [Finset.sum_eq_single_of_mem 1 h_one]
  · simp
  · intro d hd hne
    by_cases hdh : d ∣ a
    · have hd_one : d = 1 :=
        Nat.eq_one_of_dvd_coprimes ha hdh (Nat.dvd_of_mem_divisors hd)
      exact (hne hd_one).elim
    · simp [hdh]

theorem class_split (n q a : ℕ) (β : ℝ) (hq : 1 ≤ q) (ha : Nat.Coprime a q) :
    ‖(∑ k ∈ Finset.range (n + 1), (abelW k : ℂ) * abelE ((k : ℝ) * ((a : ℝ) / q + β)))
        - ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) * abelK n β‖
      ≤ (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
          ‖abelC n q r β - (1 / (Nat.totient q : ℂ)) * abelK n β‖)
        + ∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime r q),
          ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % q = r), abelW k := by
  have hqpos : 0 < q := by omega
  have hq0 : q ≠ 0 := hqpos.ne'
  have hfiber : (∑ k ∈ Finset.range (n + 1),
        (abelW k : ℂ) * abelE ((k : ℝ) * ((a : ℝ) / q + β)))
      = ∑ r ∈ Finset.range q, abelE ((r : ℝ) * (a : ℝ) / q) * abelC n q r β := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.range (n + 1))
      (t := Finset.range q) (g := fun k => k % q)
      (fun k _ => Finset.mem_range.mpr (Nat.mod_lt k hqpos))]
    simp only [abelC]
    refine Finset.sum_congr rfl ?_
    intro r _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [Finset.mem_filter] at hk
    have hkr : k % q = r := hk.2
    have h1 : abelE ((k : ℝ) * ((a : ℝ) / q + β))
        = abelE ((k : ℝ) * (a : ℝ) / q) * abelE ((k : ℝ) * β) := by
      rw [← class_split_aux_abelE_add]
      congr 1
      ring
    rw [h1, class_split_aux_phase_mod k q a hq, hkr]
    ring
  have hram := class_split_aux_ramanujan q a hq ha
  have hcop : (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
        abelE ((r : ℝ) * (a : ℝ) / q) * abelC n q r β)
      = (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
          abelE ((r : ℝ) * (a : ℝ) / q)
            * (abelC n q r β - (1 / (Nat.totient q : ℂ)) * abelK n β))
        + ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) * abelK n β := by
    have h1 : (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
          abelE ((r : ℝ) * (a : ℝ) / q)
            * (abelC n q r β - (1 / (Nat.totient q : ℂ)) * abelK n β))
        = (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
            abelE ((r : ℝ) * (a : ℝ) / q) * abelC n q r β)
          - (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
              abelE ((r : ℝ) * (a : ℝ) / q)) * ((1 / (Nat.totient q : ℂ)) * abelK n β) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro r _
      ring
    rw [h1, hram]
    ring
  have hdecomp : (∑ r ∈ Finset.range q, abelE ((r : ℝ) * (a : ℝ) / q) * abelC n q r β)
        - ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) * abelK n β
      = (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
          abelE ((r : ℝ) * (a : ℝ) / q)
            * (abelC n q r β - (1 / (Nat.totient q : ℂ)) * abelK n β))
        + ∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime r q),
          abelE ((r : ℝ) * (a : ℝ) / q) * abelC n q r β := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range q) (fun r => Nat.Coprime r q)
      (fun r => abelE ((r : ℝ) * (a : ℝ) / q) * abelC n q r β)]
    rw [hcop]
    ring
  rw [hfiber, hdecomp]
  refine le_trans (norm_add_le _ _) ?_
  refine add_le_add ?_ ?_
  · refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum ?_
    intro r _
    refine le_of_eq ?_
    rw [norm_mul, class_split_aux_norm_abelE, one_mul]
  · refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum ?_
    intro r _
    calc ‖abelE ((r : ℝ) * (a : ℝ) / q) * abelC n q r β‖
        = ‖abelE ((r : ℝ) * (a : ℝ) / q)‖ * ‖abelC n q r β‖ := norm_mul _ _
      _ = ‖abelC n q r β‖ := by rw [class_split_aux_norm_abelE, one_mul]
      _ ≤ ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % q = r), abelW k :=
          class_split_aux_norm_abelC n q r β
-- @end class_split

-- @helper abel_class
theorem abel_class_aux_summation (d z : ℕ → ℂ) (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, d k * z k)
      = (∑ k ∈ Finset.Icc 1 n, d k) * z n
        - ∑ m ∈ Finset.range n, (∑ k ∈ Finset.Icc 1 m, d k) * (z (m + 1) - z m) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
      Finset.sum_range_succ, ih]
    ring

theorem abel_class (n q r : ℕ) (β e : ℝ) (hq : 1 ≤ q) (he : 0 ≤ e)
    (h : ∀ m : ℕ, 1 ≤ m → m ≤ n →
      |(∑ k ∈ (Finset.range (m + 1)).filter (fun k => k % q = r), abelW k)
        - (m : ℝ) / (Nat.totient q : ℝ)| ≤ e) :
    ‖abelC n q r β - (1 / (Nat.totient q : ℂ)) * abelK n β‖
      ≤ e * (1 + 2 * Real.pi * (n : ℝ) * |β|) := by
  have hrange : ∀ m : ℕ, Finset.range (m + 1) = insert 0 (Finset.Icc 1 m) := by
    intro m
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hzero : (0 : ℕ) ∉ Finset.Icc 1 n := by simp
  have hW0 : abelW 0 = 0 := by simp [abelW]
  have hsum_eq : ∀ m : ℕ,
      (∑ k ∈ (Finset.range (m + 1)).filter (fun k => k % q = r), abelW k)
        = ∑ k ∈ Finset.Icc 1 m, (if k % q = r then abelW k else 0) := by
    intro m
    rw [Finset.sum_filter, hrange m, Finset.sum_insert (by simp [Finset.mem_Icc])]
    have h0 : (if (0 : ℕ) % q = r then abelW 0 else 0) = 0 := by
      split_ifs with hz
      · exact hW0
      · rfl
    rw [h0, zero_add]
  have hC : (∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % q = r),
        (abelW k : ℂ) * abelE ((k : ℝ) * β))
      = ∑ k ∈ Finset.Icc 1 n, ((if k % q = r then abelW k else 0 : ℝ) : ℂ)
          * abelE ((k : ℝ) * β) := by
    rw [Finset.sum_filter, hrange n, Finset.sum_insert hzero]
    have h0 : (if (0 : ℕ) % q = r then (abelW 0 : ℂ) * abelE (((0 : ℕ) : ℝ) * β) else 0) = 0 := by
      split_ifs with hz
      · simp [hW0]
      · rfl
    rw [h0, zero_add]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k % q = r <;> simp [hk]
  have hterm : ∀ k : ℕ,
      (((if k % q = r then abelW k else 0) - 1 / (Nat.totient q : ℝ) : ℝ) : ℂ)
          * abelE ((k : ℝ) * β)
        = ((if k % q = r then abelW k else 0 : ℝ) : ℂ) * abelE ((k : ℝ) * β)
          - (1 / (Nat.totient q : ℂ)) * abelE ((k : ℝ) * β) := by
    intro k
    have hsplit : (((if k % q = r then abelW k else 0) - 1 / (Nat.totient q : ℝ) : ℝ) : ℂ)
        = ((if k % q = r then abelW k else 0 : ℝ) : ℂ) - (1 / (Nat.totient q : ℂ)) := by
      rw [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
    rw [hsplit, sub_mul]
  have key : abelC n q r β - (1 / (Nat.totient q : ℂ)) * abelK n β
      = ∑ k ∈ Finset.Icc 1 n,
          (((if k % q = r then abelW k else 0) - 1 / (Nat.totient q : ℝ) : ℝ) : ℂ)
            * abelE ((k : ℝ) * β) := by
    simp only [abelC, abelK]
    rw [hC, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    exact (hterm k).symm
  have hcard : ∀ m : ℕ, (Finset.Icc 1 m).card = m := by
    intro m
    rw [Nat.card_Icc]
    omega
  have hD : ∀ m : ℕ,
      (∑ k ∈ Finset.Icc 1 m,
        (((if k % q = r then abelW k else 0) - 1 / (Nat.totient q : ℝ) : ℝ) : ℂ))
        = (((∑ k ∈ Finset.Icc 1 m, (if k % q = r then abelW k else 0))
            - (m : ℝ) / (Nat.totient q : ℝ) : ℝ) : ℂ) := by
    intro m
    rw [← Complex.ofReal_sum, Complex.ofReal_inj]
    rw [Finset.sum_sub_distrib, Finset.sum_const, hcard m, nsmul_eq_mul]
    ring
  have hDnorm : ∀ m : ℕ, m ≤ n →
      ‖∑ k ∈ Finset.Icc 1 m,
        (((if k % q = r then abelW k else 0) - 1 / (Nat.totient q : ℝ) : ℝ) : ℂ)‖ ≤ e := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hm1
    · rw [Finset.Icc_eq_empty_of_lt (by omega), Finset.sum_empty, norm_zero]
      exact he
    · rw [hD m, Complex.norm_real, Real.norm_eq_abs]
      have hh := h m hm1 hm
      rwa [hsum_eq m] at hh
  have hE : ∀ x : ℝ, ‖abelE x‖ = 1 := by
    intro x
    rw [abelE, Complex.norm_exp_ofReal_mul_I]
  have hEadd : ∀ x y : ℝ, abelE (x + y) = abelE x * abelE y := by
    intro x y
    simp only [abelE, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hEsub : ‖abelE β - 1‖ ≤ 2 * Real.pi * |β| := by
    have h2 : abelE β - 1
        = Complex.exp (Complex.I * ((2 * Real.pi * β : ℝ) : ℂ)) - 1 := by
      rw [abelE, mul_comm]
    have h3 : |2 * Real.pi * β| = 2 * Real.pi * |β| := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos]
    calc ‖abelE β - 1‖
        = ‖Complex.exp (Complex.I * ((2 * Real.pi * β : ℝ) : ℂ)) - 1‖ := by rw [h2]
      _ ≤ ‖(2 * Real.pi * β : ℝ)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
      _ = 2 * Real.pi * |β| := by rw [Real.norm_eq_abs, h3]
  have hzdiff : ∀ m : ℕ,
      ‖abelE (((m + 1 : ℕ) : ℝ) * β) - abelE ((m : ℝ) * β)‖ ≤ 2 * Real.pi * |β| := by
    intro m
    have h1 : (((m + 1 : ℕ) : ℝ) * β) = (m : ℝ) * β + β := by
      push_cast
      ring
    rw [h1, hEadd]
    have h2 : abelE ((m : ℝ) * β) * abelE β - abelE ((m : ℝ) * β)
        = abelE ((m : ℝ) * β) * (abelE β - 1) := by ring
    rw [h2, norm_mul, hE, one_mul]
    exact hEsub
  rw [key, abel_class_aux_summation]
  have hb1 : ‖(∑ k ∈ Finset.Icc 1 n,
        (((if k % q = r then abelW k else 0) - 1 / (Nat.totient q : ℝ) : ℝ) : ℂ))
      * abelE ((n : ℝ) * β)‖ ≤ e := by
    rw [norm_mul, hE, mul_one]
    exact hDnorm n le_rfl
  have hb2 : ‖∑ m ∈ Finset.range n, (∑ k ∈ Finset.Icc 1 m,
        (((if k % q = r then abelW k else 0) - 1 / (Nat.totient q : ℝ) : ℝ) : ℂ))
      * (abelE (((m + 1 : ℕ) : ℝ) * β) - abelE ((m : ℝ) * β))‖
      ≤ (n : ℝ) * (e * (2 * Real.pi * |β|)) := by
    calc ‖∑ m ∈ Finset.range n, (∑ k ∈ Finset.Icc 1 m,
          (((if k % q = r then abelW k else 0) - 1 / (Nat.totient q : ℝ) : ℝ) : ℂ))
        * (abelE (((m + 1 : ℕ) : ℝ) * β) - abelE ((m : ℝ) * β))‖
        ≤ ∑ m ∈ Finset.range n, ‖(∑ k ∈ Finset.Icc 1 m,
            (((if k % q = r then abelW k else 0) - 1 / (Nat.totient q : ℝ) : ℝ) : ℂ))
          * (abelE (((m + 1 : ℕ) : ℝ) * β) - abelE ((m : ℝ) * β))‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ Finset.range n, e * (2 * Real.pi * |β|) := by
          apply Finset.sum_le_sum
          intro m hm
          rw [Finset.mem_range] at hm
          rw [norm_mul]
          exact mul_le_mul (hDnorm m (le_of_lt hm)) (hzdiff m) (norm_nonneg _) he
      _ = (n : ℝ) * (e * (2 * Real.pi * |β|)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc ‖(∑ k ∈ Finset.Icc 1 n,
        (((if k % q = r then abelW k else 0) - 1 / (Nat.totient q : ℝ) : ℝ) : ℂ))
      * abelE ((n : ℝ) * β)
      - ∑ m ∈ Finset.range n, (∑ k ∈ Finset.Icc 1 m,
        (((if k % q = r then abelW k else 0) - 1 / (Nat.totient q : ℝ) : ℝ) : ℂ))
      * (abelE (((m + 1 : ℕ) : ℝ) * β) - abelE ((m : ℝ) * β))‖
      ≤ ‖(∑ k ∈ Finset.Icc 1 n,
        (((if k % q = r then abelW k else 0) - 1 / (Nat.totient q : ℝ) : ℝ) : ℂ))
      * abelE ((n : ℝ) * β)‖
        + ‖∑ m ∈ Finset.range n, (∑ k ∈ Finset.Icc 1 m,
        (((if k % q = r then abelW k else 0) - 1 / (Nat.totient q : ℝ) : ℝ) : ℂ))
      * (abelE (((m + 1 : ℕ) : ℝ) * β) - abelE ((m : ℝ) * β))‖ := norm_sub_le _ _
    _ ≤ e + (n : ℝ) * (e * (2 * Real.pi * |β|)) := add_le_add hb1 hb2
    _ = e * (1 + 2 * Real.pi * (n : ℝ) * |β|) := by ring
-- @end abel_class

-- @helper noncoprime_weight
theorem noncoprime_weight_aux_reindex (n q : ℕ) (hq : 1 ≤ q) :
    (∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime r q),
      ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % q = r), abelW k)
      = ∑ k ∈ (Finset.range (n + 1)).filter (fun k => ¬ Nat.Coprime (k % q) q), abelW k := by
  have hq0 : 0 < q := hq
  have hswap : (∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime r q),
        ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % q = r), abelW k)
      = ∑ k ∈ Finset.range (n + 1), ∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime r q),
          if k % q = r then abelW k else 0 := by
    calc (∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime r q),
          ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % q = r), abelW k)
        = ∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime r q),
          ∑ k ∈ Finset.range (n + 1), if k % q = r then abelW k else 0 := by
          apply Finset.sum_congr rfl
          intro r hr
          exact Finset.sum_filter (s := Finset.range (n + 1)) (fun k => k % q = r) abelW
      _ = ∑ k ∈ Finset.range (n + 1), ∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime r q),
          if k % q = r then abelW k else 0 := Finset.sum_comm
  rw [hswap]
  have hinner : ∀ k ∈ Finset.range (n + 1),
      (∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime r q),
        if k % q = r then abelW k else 0)
        = if ¬ Nat.Coprime (k % q) q then abelW k else 0 := by
    intro k hk
    have hlt : k % q < q := Nat.mod_lt k hq0
    by_cases hc : Nat.Coprime (k % q) q
    · rw [ite_eq_right (fun h => h hc)]
      apply Finset.sum_eq_zero
      intro r hr
      have hrn : ¬ Nat.Coprime r q := (Finset.mem_filter.mp hr).2
      rw [ite_eq_right (fun h => hrn (by rw [← h]; exact hc))]
    · rw [ite_eq_left hc]
      have hmem : k % q ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime r q) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hc⟩
      have hsingle := Finset.sum_eq_single
        (s := (Finset.range q).filter (fun r => ¬ Nat.Coprime r q))
        (f := fun r => if k % q = r then abelW k else 0) (k % q)
        (fun b hb hne => ite_eq_right (fun h => hne h.symm))
        (fun hnot => absurd hmem hnot)
      simpa using hsingle
  calc (∑ k ∈ Finset.range (n + 1), ∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime r q),
          if k % q = r then abelW k else 0)
      = ∑ k ∈ Finset.range (n + 1), if ¬ Nat.Coprime (k % q) q then abelW k else 0 :=
        Finset.sum_congr rfl hinner
    _ = ∑ k ∈ (Finset.range (n + 1)).filter (fun k => ¬ Nat.Coprime (k % q) q), abelW k :=
        (Finset.sum_filter (s := Finset.range (n + 1))
          (fun k => ¬ Nat.Coprime (k % q) q) abelW).symm

theorem noncoprime_weight_aux_primes (n q : ℕ) (hq : 1 ≤ q) :
    (∑ k ∈ (Finset.range (n + 1)).filter (fun k => ¬ Nat.Coprime (k % q) q), abelW k)
      ≤ ∑ p ∈ q.primeFactors, Real.log (p : ℝ) := by
  have hq0 : 0 < q := hq
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hsub : ((Finset.range (n + 1)).filter (fun k => ¬ Nat.Coprime (k % q) q)).filter Nat.Prime
      ⊆ q.primeFactors := by
    intro k hk
    have hk1 : k ∈ (Finset.range (n + 1)).filter (fun k => ¬ Nat.Coprime (k % q) q) :=
      (Finset.mem_filter.mp hk).1
    have hkp : Nat.Prime k := (Finset.mem_filter.mp hk).2
    have hknc : ¬ Nat.Coprime (k % q) q := (Finset.mem_filter.mp hk1).2
    have hcop : Nat.Coprime k q → Nat.Coprime (k % q) q := by
      intro h
      rw [Nat.coprime_iff_gcd_eq_one] at h ⊢
      rw [Nat.gcd_comm] at h
      rw [Nat.gcd_rec q k] at h
      exact h
    have hdv : k ∣ q := by
      by_contra hcon
      exact hknc (hcop ((Nat.Prime.coprime_iff_not_dvd hkp).mpr hcon))
    exact Nat.mem_primeFactors.mpr ⟨hkp, hdv, hqne⟩
  have hnonneg : ∀ p ∈ q.primeFactors, (0 : ℝ) ≤ Real.log (p : ℝ) := by
    intro p hp
    have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
    exact Real.log_nonneg (by exact_mod_cast (Nat.Prime.one_lt hpp).le)
  calc (∑ k ∈ (Finset.range (n + 1)).filter (fun k => ¬ Nat.Coprime (k % q) q), abelW k)
      = ∑ k ∈ (Finset.range (n + 1)).filter (fun k => ¬ Nat.Coprime (k % q) q),
          if Nat.Prime k then Real.log (k : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        rfl
    _ = ∑ k ∈ ((Finset.range (n + 1)).filter (fun k => ¬ Nat.Coprime (k % q) q)).filter Nat.Prime,
          Real.log (k : ℝ) :=
        (Finset.sum_filter (s := (Finset.range (n + 1)).filter (fun k => ¬ Nat.Coprime (k % q) q))
          Nat.Prime (fun k => Real.log (k : ℝ))).symm
    _ ≤ ∑ p ∈ q.primeFactors, Real.log (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi hnot => hnonneg i hi)

theorem noncoprime_weight_aux_log (q : ℕ) (hq : 1 ≤ q) :
    (∑ p ∈ q.primeFactors, Real.log (p : ℝ)) ≤ Real.log (q : ℝ) := by
  have hq0 : 0 < q := hq
  have hpos : ∀ p ∈ q.primeFactors, (0 : ℝ) < (p : ℝ) := by
    intro p hp
    have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
    exact_mod_cast Nat.Prime.pos hpp
  have hle : (∏ p ∈ q.primeFactors, p) ≤ q :=
    Nat.le_of_dvd hq0 (Nat.prod_primeFactors_dvd q)
  have hcast : (∏ p ∈ q.primeFactors, (p : ℝ)) ≤ (q : ℝ) := by
    rw [← Nat.cast_prod]
    exact Nat.cast_le.mpr hle
  calc (∑ p ∈ q.primeFactors, Real.log (p : ℝ))
      = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) :=
        (Real.log_prod (s := q.primeFactors) (f := fun p => (p : ℝ))
          (fun p hp => ne_of_gt (hpos p hp))).symm
    _ ≤ Real.log (q : ℝ) := Real.log_le_log (Finset.prod_pos hpos) hcast

theorem noncoprime_weight (n q : ℕ) (hq : 1 ≤ q) :
    (∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime r q),
      ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % q = r), abelW k)
      ≤ Real.log (q : ℝ) := by
  rw [noncoprime_weight_aux_reindex n q hq]
  exact (noncoprime_weight_aux_primes n q hq).trans (noncoprime_weight_aux_log q hq)
-- @end noncoprime_weight

theorem Conjectures.Goldbach.MajorArcAbelApproximation :
    let w (k : ℕ) := if Nat.Prime k then Real.log (k : ℝ) else 0; let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let S (n : ℕ) (t : ℝ) := ∑ k ∈ Finset.range (n + 1), (w k : ℂ) * E ((k : ℝ) * t); let ap (q r m : ℕ) := ∑ k ∈ (Finset.range (m + 1)).filter (fun k => k % q = r), w k; let K1 (n : ℕ) (b : ℝ) := ∑ k ∈ Finset.Icc 1 n, E ((k : ℝ) * b); ∀ (n q a : ℕ) (β e : ℝ), 1 ≤ q → Nat.Coprime a q → 0 ≤ e → (∀ m : ℕ, 1 ≤ m → m ≤ n → ∀ r < q, Nat.Coprime r q → |ap q r m - (m : ℝ) / (Nat.totient q : ℝ)| ≤ e) → ‖S n ((a : ℝ) / q + β) - ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) * K1 n β‖ ≤ Real.log (q : ℝ) + (Nat.totient q : ℝ) * e * (1 + 2 * Real.pi * (n : ℝ) * |β|)
 := by
  intro w E S ap K1 n q a β e hq ha he hap
  have hsplit := class_split n q a β hq ha
  have hnc := noncoprime_weight n q hq
  have hab : ∀ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
      ‖abelC n q r β - (1 / (Nat.totient q : ℂ)) * abelK n β‖
        ≤ e * (1 + 2 * Real.pi * (n : ℝ) * |β|) := by
    intro r hr
    rw [Finset.mem_filter, Finset.mem_range] at hr
    exact abel_class n q r β e hq he (fun m h1 h2 => hap m h1 h2 r hr.1 hr.2)
  have hcard : ((Finset.range q).filter (fun r => Nat.Coprime r q)).card = Nat.totient q := by
    rw [Nat.totient_eq_card_coprime]
    congr 1
    apply Finset.filter_congr
    intro r _
    exact Nat.coprime_comm
  have hsum := Finset.sum_le_card_nsmul _ _ _ hab
  rw [hcard, nsmul_eq_mul] at hsum
  have hmul : (Nat.totient q : ℝ) * (e * (1 + 2 * Real.pi * (n : ℝ) * |β|))
      = (Nat.totient q : ℝ) * e * (1 + 2 * Real.pi * (n : ℝ) * |β|) := by ring
  refine le_trans hsplit ?_
  linarith
