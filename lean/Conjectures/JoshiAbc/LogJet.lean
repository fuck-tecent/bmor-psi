import Mathlib

namespace Conjectures.JoshiAbc.LogJet_aux

lemma mult14_le (n : ℕ) : 14 * multiplicity 29 n ≤ n := by
  have h := mul_multiplicity_le (p := 29) (n := n)
  omega

end Conjectures.JoshiAbc.LogJet_aux

theorem Conjectures.JoshiAbc.LogJet :
    ∀ (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K] (r : K), r^14=(29:K) → 0 < ‖r‖ → ‖r‖<1 → (∀ n : ℕ, 0<n → ‖(n:K)‖ = ‖r‖^(14*multiplicity 29 n)) → ∀ x : K, ‖x‖ ≤ ‖r‖ → ‖(∑' k : ℕ, (-1:K)^k*((29:K)*x)^(k+1)/((k+1:ℕ):K))/(29:K)-x‖ ≤ ‖r‖^4 := by
  intro K _ _ _ _ r hr14 hr0 hr1 hcast x hx
  have h29 : ‖(29 : K)‖ = ‖r‖ ^ 14 := by rw [← hr14, norm_pow]
  have h29ne : (29 : K) ≠ 0 := by norm_num
  set f : ℕ → K := fun k => (-1 : K) ^ k * ((29 : K) * x) ^ (k + 1) / ((k + 1 : ℕ) : K) with hfdef
  have hbase : ‖r‖ ^ 14 * ‖x‖ ≤ ‖r‖ ^ 15 := by
    calc ‖r‖ ^ 14 * ‖x‖ ≤ ‖r‖ ^ 14 * ‖r‖ := mul_le_mul_of_nonneg_left hx (pow_nonneg hr0.le 14)
      _ = ‖r‖ ^ 15 := by ring
  have hnum : ∀ m : ℕ, (‖r‖ ^ 14 * ‖x‖) ^ (m + 1)
      ≤ ‖r‖ ^ (14 * (m + 1)) * ‖r‖ ^ (14 * multiplicity 29 (m + 1)) := by
    intro m
    have hv : 14 * multiplicity 29 (m + 1) ≤ m + 1 :=
      Conjectures.JoshiAbc.LogJet_aux.mult14_le (m + 1)
    calc (‖r‖ ^ 14 * ‖x‖) ^ (m + 1) ≤ (‖r‖ ^ 15) ^ (m + 1) :=
          pow_le_pow_left₀ (mul_nonneg (pow_nonneg hr0.le 14) (norm_nonneg x)) hbase _
      _ = ‖r‖ ^ (15 * (m + 1)) := by rw [← pow_mul]
      _ ≤ ‖r‖ ^ (14 * (m + 1)) * ‖r‖ ^ (14 * multiplicity 29 (m + 1)) := by
          rw [← pow_add]
          exact pow_le_pow_of_le_one hr0.le hr1.le (by omega)
  have hkey : ∀ m : ℕ, ‖f m‖ ≤ ‖r‖ ^ (14 * (m + 1)) := by
    intro m
    have hn : ‖((m + 1 : ℕ) : K)‖ = ‖r‖ ^ (14 * multiplicity 29 (m + 1)) := hcast (m + 1) (by omega)
    have hnorm : ‖f m‖ = (‖r‖ ^ 14 * ‖x‖) ^ (m + 1) / ‖r‖ ^ (14 * multiplicity 29 (m + 1)) := by
      rw [hfdef, norm_div, norm_mul, norm_pow, norm_pow, norm_mul, norm_neg, norm_one, one_pow,
        one_mul, h29, hn]
    rw [hnorm]
    exact (div_le_iff₀ (pow_pos hr0 _)).2 (hnum m)
  have hgeom : Summable (fun m : ℕ => (‖r‖ ^ 14) ^ m) :=
    summable_geometric_of_lt_one (pow_nonneg hr0.le 14) (pow_lt_one₀ hr0.le hr1 (by norm_num))
  have hsumf : Summable f := by
    refine Summable.of_norm_bounded (g := fun m : ℕ => ‖r‖ ^ (14 * (m + 1))) ?_ hkey
    have h2 : Summable (fun m : ℕ => (‖r‖ ^ 14) ^ m * (‖r‖ ^ 14)) := hgeom.mul_right _
    simpa only [pow_mul, pow_succ] using h2
  have htail : ∀ k : ℕ, ‖f (k + 1) / (29 : K)‖ ≤ ‖r‖ ^ 4 := by
    intro k
    have hstep : ‖r‖ ^ (14 * (k + 2)) ≤ ‖r‖ ^ 4 * ‖r‖ ^ 14 := by
      rw [← pow_add]
      exact pow_le_pow_of_le_one hr0.le hr1.le (by omega)
    rw [norm_div, h29, div_le_iff₀ (pow_pos hr0 14)]
    exact (hkey (k + 1)).trans hstep
  have hsplit : (∑' k : ℕ, f k) = f 0 + ∑' k : ℕ, f (k + 1) := hsumf.tsum_eq_zero_add
  have hf0 : f 0 = (29 : K) * x := by
    rw [hfdef]
    norm_num
  have hcancel : (29 : K) * x / (29 : K) = x := by
    rw [div_eq_iff h29ne, mul_comm]
  have hmain : (∑' k : ℕ, f k) / (29 : K) - x = ∑' k : ℕ, f (k + 1) / (29 : K) := by
    rw [hsplit, hf0, add_div, hcancel, tsum_div_const]
    ring
  rw [hmain]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (pow_nonneg hr0.le 4) htail
