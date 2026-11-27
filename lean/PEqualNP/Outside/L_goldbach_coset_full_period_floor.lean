import Mathlib

private theorem fullPeriodEnergy (n q : ℕ) (hq : 0 < q) (hn : 2 * q ≤ n) (v : ℕ → ℝ) :
    (∑ r ∈ Finset.range q, (v r)^2 / (((Finset.range (n+1)).filter (fun k => k % q = r)).card : ℝ)) ≤
      (2 * (q : ℝ) / (n : ℝ)) * ∑ r ∈ Finset.range q, (v r)^2 := by
  classical
  have hquot : 1 ≤ n / q := (Nat.le_div_iff_mul_le hq).2 (by omega)
  have hqmul : q ≤ q * (n / q) := by
    simpa using Nat.mul_le_mul_left q hquot
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have hrq : r < q := Finset.mem_range.mp hr
  let F := (Finset.range (n+1)).filter (fun k => k % q = r)
  have hcard : n / q ≤ F.card := by
    have hinj : (Finset.range (n / q)).card ≤ F.card := by
      apply Finset.card_le_card_of_injOn (fun j : ℕ => j * q + r)
      · intro j hj
        have hj' : j + 1 ≤ n / q := Finset.mem_range.mp hj
        have hmul := Nat.mul_le_mul_right q hj'
        rw [Nat.add_mul, Nat.one_mul] at hmul
        have hdiv := Nat.div_mul_le_self n q
        apply Finset.mem_filter.mpr
        have hlt : j * q + r < n + 1 := by omega
        exact ⟨Finset.mem_range.mpr hlt, by simp [Nat.add_mod, Nat.mod_eq_of_lt hrq]⟩
      · intro i hi j hj heq
        exact Nat.mul_right_cancel hq (Nat.add_right_cancel heq)
    simpa using hinj
  have hpos : (0 : ℝ) < (F.card : ℝ) := by exact_mod_cast (show 0 < F.card by omega)
  have hbound : n ≤ 2 * q * F.card := calc
    n ≤ 2 * (q * (n / q)) := by
      have := Nat.mod_lt n hq
      have := Nat.mod_add_div n q
      omega
    _ = (2 * q) * (n / q) := by ring
    _ ≤ (2 * q) * F.card := Nat.mul_le_mul_left _ hcard
  have hbound' : (n : ℝ) ≤ 2 * (q : ℝ) * (F.card : ℝ) := by exact_mod_cast hbound
  have hweight : 1 / (F.card : ℝ) ≤ 2 * (q : ℝ) / (n : ℝ) :=
    (div_le_div_iff₀ hpos hnpos).2 (by simpa using hbound')
  change (v r)^2 / (F.card : ℝ) ≤ _
  calc
    (v r)^2 / (F.card : ℝ) = (v r)^2 * (1 / (F.card : ℝ)) := by ring
    _ ≤ (v r)^2 * (2 * (q : ℝ) / (n : ℝ)) := mul_le_mul_of_nonneg_left hweight (sq_nonneg _)
    _ = _ := mul_comm _ _

theorem PEqualNP.Outside.L_goldbach_coset_full_period_floor : let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q = r); let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; let μ := fun q r : ℕ => if r.Coprime q then (q:ℝ)/(q.totient:ℝ) else 0; let v := fun n q r : ℕ => A n q r-((F n q r).card:ℝ)*μ q r; let E := fun n q => ∑ r ∈ Finset.range q, (v n q r)^2/((F n q r).card:ℝ); ∀ n q : ℕ, 0<q → 2*q≤n → E n q ≤ (2*(q:ℝ)/(n:ℝ))*∑ r ∈ Finset.range q, (v n q r)^2 := by
  dsimp only
  intro n q hq hn
  apply fullPeriodEnergy n q hq hn
