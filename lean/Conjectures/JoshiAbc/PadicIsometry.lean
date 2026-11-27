import Mathlib

namespace Conjectures.JoshiAbc.PadicIsometry_aux

variable {p : ℕ} [hp : Fact p.Prime]

noncomputable def term (c x : Padic p) (k : ℕ) : Padic p :=
  (-1 : Padic p) ^ k * (c * x) ^ (k + 1) / ((k + 1 : ℕ) : Padic p)

theorem multSelf (q : ℕ) (hq : q.Prime) : multiplicity q q = 1 :=
  Irreducible.multiplicity_self hq

theorem multTwoFour : multiplicity 2 4 = 2 := by
  apply multiplicity_eq_of_dvd_of_not_dvd (k := 2)
  · norm_num
  · norm_num

theorem addTwoLePowThree : ∀ k : ℕ, 1 ≤ k → k + 2 ≤ 3 ^ k := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ m ih =>
    intro hk
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; norm_num
    · have ih' := ih (by omega)
      have hstep : 3 ^ (m + 1) = 3 * 3 ^ m := by ring
      omega

theorem log_domination (q n : ℕ) (hq : q.Prime) (hn : 2 ≤ n) :
    multiplicity q n < (n - 1) * multiplicity q (if q = 2 then 4 else q) := by
  by_cases hq2 : q = 2
  · subst hq2
    have hc : (if (2 : ℕ) = 2 then 4 else 2) = 4 := by simp
    rw [hc, multTwoFour]
    have hdvd : 2 ^ multiplicity 2 n ∣ n := pow_multiplicity_dvd 2 n
    have hle : 2 ^ multiplicity 2 n ≤ n := Nat.le_of_dvd (by omega) hdvd
    have hlt : multiplicity 2 n < 2 ^ multiplicity 2 n := Nat.lt_two_pow_self
    omega
  · have hc : (if q = 2 then 4 else q) = q := by simp [hq2]
    rw [hc, multSelf q hq, mul_one]
    have hdvd : q ^ multiplicity q n ∣ n := pow_multiplicity_dvd q n
    have hle : q ^ multiplicity q n ≤ n := Nat.le_of_dvd (by omega) hdvd
    have hq3 : 3 ≤ q := by have h := hq.two_le; omega
    have hpow : 3 ^ multiplicity q n ≤ q ^ multiplicity q n :=
      Nat.pow_le_pow_left hq3 _
    rcases Nat.eq_zero_or_pos (multiplicity q n) with hk0 | hk0
    · omega
    · have h3 := addTwoLePowThree _ hk0
      omega

theorem mult_c : multiplicity p (if p = 2 then (4 : ℕ) else p) = if p = 2 then 2 else 1 := by
  by_cases h2 : p = 2
  · rw [if_pos h2, if_pos h2, h2]
    exact multTwoFour
  · rw [if_neg h2, if_neg h2]
    exact multSelf p hp.out

theorem norm_natCast_mult (n : ℕ) (hn : n ≠ 0) :
    ‖(n : Padic p)‖ = ((p : ℝ)⁻¹) ^ (multiplicity p n) := by
  rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hn), Padic.valuation_natCast,
    zpow_neg, zpow_natCast, inv_pow]

theorem inv_norm_natCast (n : ℕ) (hn : 1 ≤ n) : ‖((n : ℕ) : Padic p)‖⁻¹ ≤ (n : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  have hdvd : p ^ multiplicity p n ∣ n := pow_multiplicity_dvd p n
  have hle : p ^ multiplicity p n ≤ n := Nat.le_of_dvd hn hdvd
  have hinv : ‖((n : ℕ) : Padic p)‖⁻¹ = (p : ℝ) ^ multiplicity p n := by
    rw [norm_natCast_mult n hn0, ← inv_pow, inv_inv]
  have hcast : ((p : ℝ) ^ multiplicity p n) = ((p ^ multiplicity p n : ℕ) : ℝ) := by
    rw [Nat.cast_pow]
  rw [hinv, hcast]
  exact_mod_cast hle

theorem norm_c (c : Padic p)
    (hc : c = if p = 2 then (4 : Padic p) else (p : Padic p)) :
    ‖c‖ = ((p : ℝ)⁻¹) ^ (if p = 2 then 2 else 1) := by
  rw [hc]
  by_cases h2 : p = 2
  · subst h2
    rw [if_pos (rfl : (2 : ℕ) = 2)]
    have h4 : (4 : Padic 2) = (((2 : ℕ) : Padic 2)) ^ 2 := by push_cast; ring
    rw [h4, norm_pow, Padic.norm_p, if_pos (rfl : (2 : ℕ) = 2)]
  · rw [if_neg h2, if_neg h2, Padic.norm_p, pow_one]

theorem norm_c_le (c : Padic p)
    (hc : c = if p = 2 then (4 : Padic p) else (p : Padic p)) : ‖c‖ ≤ 1 / 3 := by
  rw [norm_c c hc]
  by_cases h2 : p = 2
  · rw [if_pos h2, h2]
    norm_num
  · rw [if_neg h2, pow_one]
    have hp3 : (3 : ℕ) ≤ p := by have h := hp.out.two_le; omega
    have hp3r : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) hp3r
    calc ((p : ℝ)⁻¹) = 1 / (p : ℝ) := (one_div _).symm
      _ ≤ 1 / 3 := h

theorem term_norm (c x : Padic p) (k : ℕ) :
    ‖term c x k‖ = ‖c‖ ^ (k + 1) * ‖x‖ ^ (k + 1) / ‖((k + 1 : ℕ) : Padic p)‖ := by
  simp only [term, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, mul_pow]

theorem term_bound (c x : Padic p)
    (hc : c = if p = 2 then (4 : Padic p) else (p : Padic p)) (hx : ‖x‖ ≤ 1) (k : ℕ)
    (hk : 1 ≤ k) : ‖term c x k‖ ≤ ‖c * x‖ / (p : ℝ) := by
  have hr0 : (0 : ℝ) < ((p : ℝ)⁻¹) := inv_pos.mpr (by exact_mod_cast hp.out.pos)
  have hr1 : ((p : ℝ)⁻¹) ≤ 1 := by
    have h := Padic.norm_p_lt_one (p := p)
    rw [Padic.norm_p] at h
    exact h.le
  have hcn : ‖c‖ = ((p : ℝ)⁻¹) ^ (if p = 2 then 2 else 1) := norm_c c hc
  have hn1 : ‖((k + 1 : ℕ) : Padic p)‖ = ((p : ℝ)⁻¹) ^ multiplicity p (k + 1) :=
    norm_natCast_mult (k + 1) (by omega)
  have hdom : multiplicity p (k + 1) + 1 ≤ k * (if p = 2 then 2 else 1) := by
    have h := log_domination p (k + 1) hp.out (by omega)
    rw [mult_c] at h
    have hsub : (k + 1 - 1) = k := by omega
    rw [hsub] at h
    omega
  have hexp : (if p = 2 then 2 else 1) + 1 + multiplicity p (k + 1)
      ≤ (if p = 2 then 2 else 1) * (k + 1) := by
    have h1 : (if p = 2 then 2 else 1) + 1 + multiplicity p (k + 1)
        = multiplicity p (k + 1) + 1 + (if p = 2 then 2 else 1) := by ring
    have h2 : (if p = 2 then 2 else 1) * (k + 1)
        = k * (if p = 2 then 2 else 1) + (if p = 2 then 2 else 1) := by ring
    rw [h1, h2]
    exact Nat.add_le_add_right hdom _
  have hxpow : ‖x‖ ^ (k + 1) ≤ ‖x‖ := pow_le_of_le_one (norm_nonneg x) hx (by omega)
  calc ‖term c x k‖ = ‖c‖ ^ (k + 1) * ‖x‖ ^ (k + 1) / ‖((k + 1 : ℕ) : Padic p)‖ :=
      term_norm c x k
    _ = ((p : ℝ)⁻¹) ^ ((if p = 2 then 2 else 1) * (k + 1)) * ‖x‖ ^ (k + 1)
        / ((p : ℝ)⁻¹) ^ multiplicity p (k + 1) := by
      rw [hcn, hn1, pow_mul]
    _ ≤ ((p : ℝ)⁻¹) ^ ((if p = 2 then 2 else 1) + 1) * ‖x‖ ^ (k + 1) := by
      rw [div_le_iff₀ (by positivity)]
      calc ((p : ℝ)⁻¹) ^ ((if p = 2 then 2 else 1) * (k + 1)) * ‖x‖ ^ (k + 1)
          ≤ ((p : ℝ)⁻¹) ^ ((if p = 2 then 2 else 1) + 1 + multiplicity p (k + 1))
              * ‖x‖ ^ (k + 1) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hr0.le hr1 hexp) (by positivity)
        _ = (((p : ℝ)⁻¹) ^ ((if p = 2 then 2 else 1) + 1) * ‖x‖ ^ (k + 1))
              * ((p : ℝ)⁻¹) ^ multiplicity p (k + 1) := by rw [pow_add]; ring
    _ ≤ ((p : ℝ)⁻¹) ^ ((if p = 2 then 2 else 1) + 1) * ‖x‖ :=
        mul_le_mul_of_nonneg_left hxpow (by positivity)
    _ = ‖c * x‖ / (p : ℝ) := by
      rw [norm_mul, hcn, pow_succ]
      ring

theorem term_bound_geo (c x : Padic p)
    (hc : c = if p = 2 then (4 : Padic p) else (p : Padic p)) (hx : ‖x‖ ≤ 1) (k : ℕ) :
    ‖term c x k‖ ≤ ((2 : ℝ) / 3) ^ k := by
  have hcn : ‖c‖ ≤ 1 / 3 := norm_c_le c hc
  have hinv : ‖((k + 1 : ℕ) : Padic p)‖⁻¹ ≤ ((k + 1 : ℕ) : ℝ) :=
    inv_norm_natCast (k + 1) (by omega)
  have hx1 : ‖x‖ ^ (k + 1) ≤ 1 := pow_le_one₀ (norm_nonneg x) hx
  have h2k : ((k + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ k := by
    have h : k + 1 ≤ 2 ^ k := by have h2 := Nat.lt_two_pow_self (n := k); omega
    exact_mod_cast h
  calc ‖term c x k‖ = ‖c‖ ^ (k + 1) * ‖x‖ ^ (k + 1) / ‖((k + 1 : ℕ) : Padic p)‖ :=
      term_norm c x k
    _ = ‖c‖ ^ (k + 1) * ‖x‖ ^ (k + 1) * ‖((k + 1 : ℕ) : Padic p)‖⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ (‖c‖ ^ (k + 1) * 1) * ((k + 1 : ℕ) : ℝ) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hx1 (by positivity)) hinv (by positivity)
        (by positivity)
    _ = ‖c‖ * ‖c‖ ^ k * ((k + 1 : ℕ) : ℝ) := by rw [pow_succ, mul_one]; ring
    _ ≤ ‖c‖ * ((1 : ℝ) / 3) ^ k * (2 : ℝ) ^ k := by
      refine mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg c) hcn k) (norm_nonneg c))
        h2k (by positivity) (by positivity)
    _ = ‖c‖ * (((1 : ℝ) / 3) ^ k * (2 : ℝ) ^ k) := by ring
    _ = ‖c‖ * ((2 : ℝ) / 3) ^ k := by rw [← mul_pow]; norm_num
    _ ≤ ((2 : ℝ) / 3) ^ k := by
      refine mul_le_of_le_one_left (by positivity) ?_
      linarith

end Conjectures.JoshiAbc.PadicIsometry_aux

theorem Conjectures.JoshiAbc.PadicIsometry :
    ∀ (p : ℕ) [Fact p.Prime], let c : Padic p := if p=2 then 4 else (p:Padic p); let tau := fun (x : Padic p) => (∑' k : ℕ, (-1:Padic p)^k*(c*x)^(k+1)/((k+1:ℕ):Padic p))/c; ∀ x : Padic p, ‖x‖ ≤ 1 → ‖tau x‖ = ‖x‖ := by
  intro p _
  have hpp : p.Prime := Fact.out
  dsimp only
  set c : Padic p := if p = 2 then (4 : Padic p) else (p : Padic p) with hcdef
  intro x hx
  change ‖(∑' k, Conjectures.JoshiAbc.PadicIsometry_aux.term c x k) / c‖ = ‖x‖
  have hsum : Summable (Conjectures.JoshiAbc.PadicIsometry_aux.term c x) :=
    Summable.of_norm_bounded
      (summable_geometric_of_norm_lt_one (x := (2 : ℝ) / 3) (by norm_num))
      (fun k => Conjectures.JoshiAbc.PadicIsometry_aux.term_bound_geo c x hcdef hx k)
  rcases eq_or_ne x 0 with rfl | hx0
  · have hz : ∀ k : ℕ, Conjectures.JoshiAbc.PadicIsometry_aux.term c 0 k = 0 := by
      intro k
      simp [Conjectures.JoshiAbc.PadicIsometry_aux.term]
    simp [hz]
  · have hcpos : 0 < ‖c‖ := by
      rw [Conjectures.JoshiAbc.PadicIsometry_aux.norm_c c hcdef]
      exact pow_pos (inv_pos.mpr (by exact_mod_cast hpp.pos)) _
    have hcx : 0 < ‖c * x‖ := by
      rw [norm_mul]
      exact mul_pos hcpos (norm_pos_iff.mpr hx0)
    have htail : ‖∑' k, Conjectures.JoshiAbc.PadicIsometry_aux.term c x (k + 1)‖
        ≤ ‖c * x‖ / (p : ℝ) :=
      IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity)
        (fun k => Conjectures.JoshiAbc.PadicIsometry_aux.term_bound c x hcdef hx (k + 1)
          (by omega))
    have hlt : ‖c * x‖ / (p : ℝ) < ‖c * x‖ := by
      have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.one_lt
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    have hzero : Conjectures.JoshiAbc.PadicIsometry_aux.term c x 0 = c * x := by
      simp [Conjectures.JoshiAbc.PadicIsometry_aux.term]
    have hsplit : ∑' k, Conjectures.JoshiAbc.PadicIsometry_aux.term c x k
        = Conjectures.JoshiAbc.PadicIsometry_aux.term c x 0
          + ∑' k, Conjectures.JoshiAbc.PadicIsometry_aux.term c x (k + 1) :=
      hsum.tsum_eq_zero_add
    have hne : ‖Conjectures.JoshiAbc.PadicIsometry_aux.term c x 0‖
        ≠ ‖∑' k, Conjectures.JoshiAbc.PadicIsometry_aux.term c x (k + 1)‖ := by
      rw [hzero]
      have hlt2 : ‖∑' k, Conjectures.JoshiAbc.PadicIsometry_aux.term c x (k + 1)‖ < ‖c * x‖ :=
        lt_of_le_of_lt htail hlt
      exact (ne_of_lt hlt2).symm
    have hS : ‖∑' k, Conjectures.JoshiAbc.PadicIsometry_aux.term c x k‖ = ‖c * x‖ := by
      have h1 : ‖Conjectures.JoshiAbc.PadicIsometry_aux.term c x 0
            + ∑' k, Conjectures.JoshiAbc.PadicIsometry_aux.term c x (k + 1)‖
          = max ‖Conjectures.JoshiAbc.PadicIsometry_aux.term c x 0‖
              ‖∑' k, Conjectures.JoshiAbc.PadicIsometry_aux.term c x (k + 1)‖ :=
        Padic.add_eq_max_of_ne hne
      rw [hsplit, h1, hzero]
      exact max_eq_left (le_of_lt (lt_of_le_of_lt htail hlt))
    calc ‖(∑' k, Conjectures.JoshiAbc.PadicIsometry_aux.term c x k) / c‖
        = ‖∑' k, Conjectures.JoshiAbc.PadicIsometry_aux.term c x k‖ / ‖c‖ := norm_div _ _
      _ = ‖c * x‖ / ‖c‖ := by rw [hS]
      _ = ‖x‖ := by rw [norm_mul, mul_div_cancel_left₀ _ hcpos.ne']
