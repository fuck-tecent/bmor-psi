import Mathlib

theorem PEqualNP.Outside.L_twin_primes_positive_product :
    let f := fun (p : ℕ) => if p.Prime ∧ 2 < p then 1-1/((p:ℝ)-1)^2 else 1
    let twinC := ∏' p : ℕ, f p
    0 < twinC := by
  dsimp only
  let a : ℕ → ℝ := fun p => if p.Prime ∧ 2 < p then 1/((p:ℝ)-1)^2 else 0
  have hf_eq : (fun p : ℕ => if p.Prime ∧ 2 < p then 1-1/((p:ℝ)-1)^2 else 1)
      = fun p : ℕ => 1 - a p := by
    funext p
    by_cases h : p.Prime ∧ 2 < p <;> simp [a, h]
  rw [hf_eq]
  have hpos : ∀ p : ℕ, 0 < 1 - a p := by
    intro p
    simp only [a]
    by_cases h : p.Prime ∧ 2 < p
    · rw [if_pos h]
      have hp3 : (3:ℝ) ≤ (p:ℝ) := by
        have hp : 3 ≤ p := by have := h.2; omega
        exact_mod_cast hp
      have hbig : (1:ℝ) < ((p:ℝ)-1)^2 := by nlinarith
      have hlt : 1/((p:ℝ)-1)^2 < 1 := by
        rw [div_lt_one (by nlinarith)]
        exact hbig
      linarith
    · rw [if_neg h]
      norm_num
  have ha_nonneg : ∀ p : ℕ, 0 ≤ a p := by
    intro p
    simp only [a]
    by_cases h : p.Prime ∧ 2 < p
    · rw [if_pos h]; positivity
    · simp [h]
  have ha_le : ∀ p : ℕ, a p ≤ 4/((p:ℝ)^2) := by
    intro p
    simp only [a]
    by_cases h : p.Prime ∧ 2 < p
    · rw [if_pos h]
      have hp3 : (3:ℝ) ≤ (p:ℝ) := by
        have hp : 3 ≤ p := by have := h.2; omega
        exact_mod_cast hp
      have hden1 : (0:ℝ) < ((p:ℝ)-1)^2 := by nlinarith
      have hden2 : (0:ℝ) < ((p:ℝ)^2) := by positivity
      rw [div_le_div_iff₀ hden1 hden2]
      nlinarith
    · rw [if_neg h]
      positivity
  have hg : Summable (fun p : ℕ => 4/((p:ℝ)^2)) := by
    have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num : (1:ℕ) < 2)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h.mul_left 4
  have hsum_a : Summable a := Summable.of_nonneg_of_le ha_nonneg ha_le hg
  have hlog : Summable (fun p : ℕ => Real.log (1 - a p)) := by
    have hneg : Summable (fun p : ℕ => -a p) := hsum_a.neg
    have := Real.summable_log_one_add_of_summable hneg
    simpa [sub_eq_add_neg] using this
  have h := Real.rexp_tsum_eq_tprod (f := fun p : ℕ => 1 - a p) hpos hlog
  rw [← h]
  exact Real.exp_pos _
