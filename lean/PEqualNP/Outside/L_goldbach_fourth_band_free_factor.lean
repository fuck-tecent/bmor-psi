import Mathlib

open Finset

/-- Write `m = a*b`, retaining the lower bounds on both factors. -/
private theorem factorOuter (n U B : ℕ) (f : ℕ → ℕ → ℂ) :
    (∑ m ∈ range (n+1), ∑ a ∈ m.divisors.filter (fun a => B < a ∧ U < m/a), f m a) =
    ∑ b ∈ Ioc U (n/(B+1)), ∑ a ∈ Ioc B (n/b), f (a*b) a := by
  rw [sum_sigma', sum_sigma']
  refine sum_bij' (fun x _ => ⟨x.1/x.2, x.2⟩) (fun y _ => ⟨y.2*y.1, y.2⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨m, a⟩ hx
    simp only [mem_sigma, mem_range, mem_filter, mem_Ioc] at hx ⊢
    obtain ⟨hm, ha, hBa, hU⟩ := hx
    have hab := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors ha)
    refine ⟨⟨hU, (Nat.le_div_iff_mul_le (by omega)).2 ?_⟩, hBa,
      (Nat.le_div_iff_mul_le (by omega)).2 (by omega)⟩
    calc m / a * (B+1) ≤ m / a * a := Nat.mul_le_mul_left _ hBa
         _ = m := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors ha)
         _ ≤ n := by omega
  · rintro ⟨b, a⟩ hy
    simp only [mem_sigma, mem_range, mem_filter, mem_Ioc] at hy ⊢
    obtain ⟨⟨hU, _⟩, hB, hn⟩ := hy
    have ha : 0 < a := by omega
    have hb : 0 < b := by omega
    refine ⟨Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hb).1 hn),
      Nat.mem_divisors.mpr ⟨Nat.dvd_mul_right _ _, Nat.ne_of_gt (Nat.mul_pos ha hb)⟩, hB, ?_⟩
    simpa [Nat.mul_div_cancel_left b ha] using hU
  · rintro ⟨m, a⟩ hx
    have ha := (mem_filter.mp (mem_sigma.mp hx).2).1
    simp [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors ha)]
  · rintro ⟨b, a⟩ hy
    have hBa : B < a := (mem_Ioc.mp (mem_sigma.mp hy).2).1
    simp [Nat.mul_div_cancel_left b (show 0 < a by omega)]
  · rintro ⟨m, a⟩ hx
    have ha := (mem_filter.mp (mem_sigma.mp hx).2).1
    simp [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors ha)]

/-- Inside `B < a ≤ z`, exchange a short divisor `d` for its free cofactor. -/
private theorem factorInner (B z U : ℕ) (f : ℕ → ℕ → ℂ) :
    (∑ a ∈ Ioc B z, ∑ d ∈ a.divisors.filter (fun d => d ≤ U), f a d) =
    ∑ d ∈ Icc 1 U, ∑ l ∈ Ioc (B/d) (z/d), f (d*l) d := by
  rw [sum_sigma', sum_sigma']
  refine sum_bij' (fun x _ => ⟨x.2, x.1/x.2⟩) (fun y _ => ⟨y.1*y.2, y.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, d⟩ hx
    simp only [mem_sigma, mem_Ioc, mem_Icc, mem_filter] at hx ⊢
    obtain ⟨⟨hB, hz⟩, hd, hU⟩ := hx
    have hp := Nat.pos_of_mem_divisors hd
    have heq := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
    exact ⟨⟨hp, hU⟩, (Nat.div_lt_iff_lt_mul hp).2 (by omega),
      (Nat.le_div_iff_mul_le hp).2 (by omega)⟩
  · rintro ⟨d, l⟩ hy
    simp only [mem_sigma, mem_Ioc, mem_Icc, mem_filter] at hy ⊢
    obtain ⟨⟨hd, hU⟩, hB, hz⟩ := hy
    have hlo : B < d*l := by simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hd).1 hB
    have hhi : d*l ≤ z := by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).1 hz
    exact ⟨⟨hlo, hhi⟩, Nat.mem_divisors.mpr ⟨Nat.dvd_mul_right _ _, by omega⟩, hU⟩
  · rintro ⟨a, d⟩ hx
    have hd := (mem_filter.mp (mem_sigma.mp hx).2).1
    simp [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
  · rintro ⟨d, l⟩ hy
    have hd := (mem_Icc.mp (mem_sigma.mp hy).1).1
    simp [Nat.mul_div_cancel_left l hd]
  · rintro ⟨a, d⟩ hx
    have hd := (mem_filter.mp (mem_sigma.mp hx).2).1
    simp [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]

private theorem moebiusTail (a U : ℕ) (ha : 1 < a) :
    (∑ d ∈ a.divisors.filter (fun d => U < d), (ArithmeticFunction.moebius d : ℝ)) =
    -(∑ d ∈ a.divisors.filter (fun d => d ≤ U), (ArithmeticFunction.moebius d : ℝ)) := by
  have hz : ∑ d ∈ a.divisors, ArithmeticFunction.moebius d = 0 := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta,
      ArithmeticFunction.one_apply_ne (by omega)]
  have hr : ∑ d ∈ a.divisors, (ArithmeticFunction.moebius d : ℝ) = 0 := by exact_mod_cast hz
  apply eq_neg_of_add_eq_zero_left
  simpa only [not_lt] using (sum_filter_add_sum_filter_not a.divisors (fun d => U < d)
    (fun d => (ArithmeticFunction.moebius d : ℝ))).trans hr

theorem PEqualNP.Outside.L_goldbach_fourth_band_free_factor :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let Λ := ArithmeticFunction.vonMangoldt; ∀ (n U B : ℕ) (t : ℝ), 1 ≤ B → let T := fun m : ℕ => ∑ a ∈ (Nat.divisors m).filter (fun a => B < a ∧ U < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U < d), μ d) * Λ (m/a); (∑ m ∈ Finset.range (n+1), (T m:ℂ)*E ((m:ℝ)*t)) = -(∑ b ∈ Finset.Ioc U (n/(B+1)), ∑ d ∈ Finset.Icc 1 U, ((Λ b * μ d:ℝ):ℂ) * ∑ l ∈ Finset.Ioc (B/d) ((n/b)/d), E ((b*d*l:ℕ)*t)) := by
  intro E μ Λ n U B t hB T
  classical
  let band (m : ℕ) := m.divisors.filter (fun a => B < a ∧ U < m/a)
  let coeff (m a : ℕ) : ℂ :=
    ((∑ d ∈ a.divisors.filter (fun d => U < d), μ d) * Λ (m/a) : ℝ)
  calc
    _ = ∑ m ∈ range (n+1), ∑ a ∈ band m, coeff m a * E ((m:ℝ)*t) := by
      simp only [T, band, coeff, Complex.ofReal_sum, sum_mul]
    _ = ∑ b ∈ Ioc U (n/(B+1)), ∑ a ∈ Ioc B (n/b),
        coeff (a*b) a * E (((a*b:ℕ):ℝ)*t) :=
      factorOuter n U B (fun m a => coeff m a * E ((m:ℝ)*t))
    _ = _ := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro b hb
      let term (a d : ℕ) := ((Λ b * μ d : ℝ) : ℂ) * E (((a*b:ℕ):ℝ)*t)
      calc
        _ = -(∑ a ∈ Ioc B (n/b), ∑ d ∈ a.divisors.filter (fun d => d ≤ U), term a d) := by
          rw [← sum_neg_distrib]
          apply sum_congr rfl
          intro a ha
          have hBa := (mem_Ioc.mp ha).1
          have htail : (∑ d ∈ a.divisors.filter (fun d => U < d), μ d) =
              -(∑ d ∈ a.divisors.filter (fun d => d ≤ U), μ d) := moebiusTail a U (by omega)
          dsimp only [coeff]
          rw [htail, Nat.mul_div_cancel_left b (show 0 < a by omega)]
          simp only [neg_mul,
            Complex.ofReal_neg, term, Complex.ofReal_mul, Complex.ofReal_sum, sum_mul]
          congr 1
          apply sum_congr rfl
          intro d hd
          ring
        _ = _ := by
          rw [factorInner]
          simp only [term, mul_sum, Nat.mul_comm, Nat.mul_left_comm]
