import Mathlib
open scoped BigOperators
theorem PEqualNP.Outside.L_goldbach_coset_mean_square_rounding :
let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q=r); let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; let μ := fun q r : ℕ => if r.Coprime q then (q:ℝ)/(q.totient:ℝ) else 0; let v := fun n q r : ℕ => A n q r-((F n q r).card:ℝ)*μ q r; ∀ n q : ℕ, 0<q → let t := fun r : ℕ => if r.Coprime q then ((n+1:ℕ):ℝ)/(q.totient:ℝ) else 0; (∑ r ∈ Finset.range q, (v n q r)^2) ≤ 2*(∑ r ∈ Finset.range q, (A n q r-t r)^2) + 2*((q:ℝ)/(q.totient:ℝ))^2*(q:ℝ) := by
  classical
  intro F w A μ v n q hq t
  let d : ℝ := (q : ℝ) / (q.totient : ℝ)
  have hp : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hterm : ∀ r ∈ Finset.range q, (v n q r)^2 ≤ 2 * (A n q r-t r)^2 + 2*d^2 := by
    intro r hr
    have hrq : r < q := Finset.mem_range.mp hr
    have hcard : (F n q r).card = (n+1)/q + if r < (n+1) % q then 1 else 0 := by
      simpa only [F, Nat.count_eq_card_filter_range, Nat.ModEq, Nat.mod_eq_of_lt hrq] using (Nat.count_modEq_card (n+1) hq r)
    have hmod := Nat.mod_lt (n+1) hq
    have hdiv := Nat.div_add_mod (n+1) q
    have hdivR : (q : ℝ) * ((n+1)/q : ℕ) + ((n+1) % q : ℕ) = (n+1 : ℕ) := by exact_mod_cast hdiv
    push_cast at hdivR
    have hmod0 : (0 : ℝ) ≤ ((n+1) % q : ℕ) := Nat.cast_nonneg _
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hmodR : (((n+1) % q : ℕ) : ℝ) < (q : ℝ) := by exact_mod_cast hmod
    have hlo : -(q : ℝ) ≤ ((n+1 : ℕ) : ℝ) - ((F n q r).card : ℝ) * (q : ℝ) := by
      rw [hcard]
      split_ifs <;> push_cast <;> nlinarith
    have hhi : ((n+1 : ℕ) : ℝ) - ((F n q r).card : ℝ) * (q : ℝ) ≤ (q : ℝ) := by
      rw [hcard]
      split_ifs <;> push_cast <;> nlinarith
    by_cases hc : r.Coprime q
    · have hδ : (q.totient : ℝ) * (t r - ((F n q r).card : ℝ) * μ q r) =
          ((n+1 : ℕ) : ℝ) - ((F n q r).card : ℝ) * (q : ℝ) := by
        dsimp [t, μ]
        simp only [ite_eq_left hc]
        field_simp [ne_of_gt hp]
      have hqd : (q.totient : ℝ) * d = q := by dsimp [d]; field_simp [ne_of_gt hp]
      have hel : -d ≤ t r - ((F n q r).card : ℝ) * μ q r := by nlinarith
      have heu : t r - ((F n q r).card : ℝ) * μ q r ≤ d := by nlinarith
      have hs : (t r - ((F n q r).card : ℝ) * μ q r)^2 ≤ d^2 := by nlinarith
      dsimp [v]
      nlinarith [sq_nonneg ((A n q r-t r) - (t r-((F n q r).card : ℝ)*μ q r))]
    · simp only [t, μ, ite_eq_right hc, mul_zero, sub_zero, v]
      nlinarith [sq_nonneg (A n q r), sq_nonneg d]
  have hsum := Finset.sum_le_sum hterm
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, d] at hsum
  nlinarith [hsum]
