import Mathlib
open scoped BigOperators

noncomputable section
namespace B1B1


def E (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)

lemma E_int (h : ℤ) : E ((h:ℝ)) = 1 := by
  unfold E
  rw [show (((2 * Real.pi * (h:ℝ) : ℝ) : ℂ) * Complex.I)
      = (h:ℂ) * (2*Real.pi*Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I h

lemma E_nat_mul (x : ℝ) (a : ℕ) : E ((a:ℝ)*x) = E x ^ a := by
  unfold E
  rw [show (((2*Real.pi*((a:ℝ)*x):ℝ):ℂ)*Complex.I)
      = (a:ℂ) * (((2*Real.pi*x:ℝ):ℂ)*Complex.I) by push_cast; ring]
  exact Complex.exp_nat_mul _ a

/-- The geometric sum over a full denominator period. -/
lemma geom_sum_E (h : ℤ) (q : ℕ) (hq : 0 < q) :
    ∑ a ∈ Finset.range q, E ((h:ℝ)*(a:ℝ)/(q:ℝ)) =
      if E ((h:ℝ)/(q:ℝ)) = 1 then (q:ℂ) else 0 := by
  set ω : ℂ := E ((h:ℝ)/(q:ℝ)) with hω
  have hpow : ∀ a : ℕ, E ((h:ℝ)*(a:ℝ)/(q:ℝ)) = ω ^ a := by
    intro a
    rw [hω]
    rw [show (h:ℝ)*(a:ℝ)/(q:ℝ) = (a:ℝ)*((h:ℝ)/(q:ℝ)) by ring]
    exact E_nat_mul _ a
  simp_rw [hpow]
  have hωq : ω ^ q = 1 := by
    rw [hω]
    rw [← E_nat_mul]
    have hqR : (q:ℝ) ≠ 0 := by positivity
    rw [show (q:ℝ) * ((h:ℝ)/(q:ℝ)) = (h:ℝ) by field_simp]
    exact E_int h
  by_cases hω1 : ω = 1
  · rw [if_pos hω1]
    simp [hω1]
  · rw [if_neg hω1, geom_sum_eq hω1 q, hωq, sub_self, zero_div]



/-- Pointwise Möbius inversion: the sum of `μ` over the divisors of `n` is `1`
at `n = 1` and `0` otherwise. -/
lemma sum_moebius_divisors_eq (n : ℕ) :
    (∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ)) =
      if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  rw [ArithmeticFunction.mul_apply] at h
  have hreindex : (∑ x ∈ n.divisorsAntidiagonal,
        (↑(ArithmeticFunction.moebius x.1) * ↑(ArithmeticFunction.zeta x.2) : ℂ))
      = ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) := by
    refine Finset.sum_nbij' (fun x : ℕ × ℕ => x.1) (fun d : ℕ => (d, n / d)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      have hx' := Nat.mem_divisorsAntidiagonal.mp hx
      exact Nat.mem_divisors.mpr ⟨⟨x.2, hx'.1.symm⟩, hx'.2⟩
    · intro d hd
      have hd' := Nat.mem_divisors.mp hd
      exact Nat.mem_divisorsAntidiagonal.mpr ⟨Nat.mul_div_cancel' hd'.1, hd'.2⟩
    · intro x hx
      have hx' := Nat.mem_divisorsAntidiagonal.mp hx
      have hxpos : 0 < x.1 := by
        rcases Nat.eq_zero_or_pos x.1 with h0 | hpos
        · rw [h0, zero_mul] at hx'; omega
        · exact hpos
      have hdiv : n / x.1 = x.2 := by
        rw [← hx'.1, Nat.mul_comm x.1 x.2, Nat.mul_div_left x.2 hxpos]
      exact Prod.ext rfl hdiv
    · intro d _
      rfl
    · intro x hx
      have hx' := Nat.mem_divisorsAntidiagonal.mp hx
      have hx2 : x.2 ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hx'
        exact hx'.2 hx'.1.symm
      rw [ArithmeticFunction.zeta_apply, if_neg hx2]
      push_cast
      ring
  have h' : (∑ x ∈ n.divisorsAntidiagonal,
      (↑(ArithmeticFunction.moebius x.1) * ↑(ArithmeticFunction.zeta x.2) : ℂ))
      = (1 : ArithmeticFunction ℂ) n := h
  rw [hreindex] at h'
  rw [ArithmeticFunction.one_apply] at h'
  exact h'

/-- The divisors of `q` that divide `a` are exactly the divisors of `gcd a q`. -/
lemma divisors_filter_dvd_eq_gcd (a q : ℕ) (hq : 0 < q) :
    q.divisors.filter (fun d => d ∣ a) = (Nat.gcd a q).divisors := by
  ext d
  rw [Finset.mem_filter, Nat.mem_divisors, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdq, _hqne⟩, hda⟩
    exact ⟨Nat.dvd_gcd hda hdq, (Nat.gcd_pos_of_pos_right a hq).ne'⟩
  · rintro ⟨hdg, _⟩
    exact ⟨⟨hdg.trans (Nat.gcd_dvd_right a q), by omega⟩,
      hdg.trans (Nat.gcd_dvd_left a q)⟩

/-- Pointwise Möbius sieve: the Möbius sum over the divisors of `q` that divide
`a` is the coprimality indicator. -/
lemma sum_mu_filter_eq (a q : ℕ) (hq : 0 < q) :
    (∑ d ∈ q.divisors.filter (fun d => d ∣ a),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ)) =
      if Nat.Coprime a q then 1 else 0 := by
  rw [divisors_filter_dvd_eq_gcd a q hq, sum_moebius_divisors_eq]

/-- Möbius sieve: the coprime-weighted sum is a Möbius combination of
divisibility sums. -/
lemma sum_coprime_eq_sum_mu (q : ℕ) (hq : 0 < q) (f : ℕ → ℂ) :
    (∑ a ∈ Finset.range q, if Nat.Coprime a q then f a else 0)
      = ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
          ∑ a ∈ Finset.range q, if d ∣ a then f a else 0 := by
  have hprod : (∑ p ∈ q.divisors ×ˢ Finset.range q,
        (if p.1 ∣ p.2 then ((ArithmeticFunction.moebius p.1 : ℤ) : ℂ) * f p.2 else 0))
      = ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
          ∑ a ∈ Finset.range q, if d ∣ a then f a else 0 := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : d ∣ a <;> simp [h]
  rw [← hprod]
  rw [Finset.sum_product, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  calc (if Nat.Coprime a q then f a else 0)
      = (if Nat.Coprime a q then 1 else 0) * f a := by by_cases h : Nat.Coprime a q <;> simp [h]
    _ = (∑ d ∈ q.divisors.filter (fun d => d ∣ a),
          ((ArithmeticFunction.moebius d : ℤ) : ℂ)) * f a := by rw [sum_mu_filter_eq a q hq]
    _ = ∑ d ∈ q.divisors.filter (fun d => d ∣ a),
          ((ArithmeticFunction.moebius d : ℤ) : ℂ) * f a := by rw [Finset.sum_mul]
    _ = ∑ d ∈ q.divisors, (if d ∣ a then ((ArithmeticFunction.moebius d : ℤ) : ℂ) * f a else 0) := by
        rw [Finset.sum_filter]

/-- The divisor-restricted phase sum is a full-period geometric sum of length
`q / d`. -/
lemma sum_filter_dvd_phase (h : ℤ) (q d : ℕ) (hq : 0 < q) (hd : 0 < d) (hdq : d ∣ q) :
    (∑ a ∈ (Finset.range q).filter (fun a => d ∣ a), E ((h:ℝ)*(a:ℝ)/(q:ℝ)))
      = if E ((h:ℝ)/((q/d:ℕ):ℝ)) = 1 then ((q/d:ℕ):ℂ) else 0 := by
  have hq'pos : 0 < q / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdq) hd
  have hreindex : (∑ a ∈ (Finset.range q).filter (fun a => d ∣ a),
        E ((h:ℝ)*(a:ℝ)/(q:ℝ)))
      = ∑ a' ∈ Finset.range (q/d), E ((h:ℝ)*((a':ℝ)/((q/d:ℕ):ℝ))) := by
    refine Finset.sum_nbij' (fun a => a / d) (fun a' => d * a') ?_ ?_ ?_ ?_ ?_
    · intro a ha
      obtain ⟨haq, hda⟩ := Finset.mem_filter.mp ha
      have ha' : d * (a/d) = a := Nat.mul_div_cancel' hda
      have hq' : d * (q/d) = q := Nat.mul_div_cancel' hdq
      have hlt : d * (a/d) < d * (q/d) := by
        rw [ha', hq']
        exact Finset.mem_range.mp haq
      exact Finset.mem_range.mpr (Nat.lt_of_mul_lt_mul_left hlt)
    · intro a' ha'
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_, ⟨a', rfl⟩⟩
      have hq' : d * (q/d) = q := Nat.mul_div_cancel' hdq
      rw [← hq']
      exact Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp ha') hd
    · intro a ha
      exact Nat.mul_div_cancel' (Finset.mem_filter.mp ha).2
    · intro a' _
      rfl
    · intro a ha
      congr 1
      have hda : d ∣ a := (Finset.mem_filter.mp ha).2
      have ha' : (a:ℝ) = (d:ℝ) * ((a/d:ℕ):ℝ) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hda]
      have hq' : (q:ℝ) = (d:ℝ) * ((q/d:ℕ):ℝ) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hdq]
      rw [ha', hq']
      field_simp
      ring
  rw [hreindex]
  simpa [mul_div_assoc] using geom_sum_E h (q/d) hq'pos


end B1B1
