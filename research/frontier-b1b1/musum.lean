import Mathlib
open scoped BigOperators

noncomputable section
namespace B1B1

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

end B1B1
