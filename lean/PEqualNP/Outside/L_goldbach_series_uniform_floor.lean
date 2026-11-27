import Mathlib

theorem PEqualNP.Outside.L_goldbach_series_uniform_floor : let fac := fun p n : ℕ => if p ∣ n then (p:ℝ)/((p:ℝ)-1) else 1-1/((p:ℝ)-1)^2; let P := fun Q : ℕ => (Finset.range (Q+1)).filter (fun p => Nat.Prime p ∧ 2<p); ∀ Q n, 1 ≤ 2*Finset.prod (P Q) (fun p => fac p n) := by
  dsimp only
  intro Q n
  let f := fun i : ℕ => 1 - 1 / ((i : ℝ) - 1)^2
  let b := fun i : ℕ => (1 / 2 : ℝ) * ((i : ℝ) / (i - 1))

  have hbound (r : ℕ) (hr : 2 ≤ r) (S : Finset ℕ)
      (hS : ∀ i ∈ S, 2 < i ∧ i ≤ r) : b r ≤ S.prod f := by
    induction r, hr using Nat.le_induction generalizing S with
    | base =>
      have hempty : S = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        obtain ⟨hlt, hle⟩ := hS i hi
        omega
      rw [hempty, Finset.prod_empty]
      norm_num [b]
    | succ r hr ih =>
      have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
      have hr0 : (0 : ℝ) < r := by linarith
      have hr1 : (0 : ℝ) < r - 1 := by linarith
      have hf : f (r + 1) = 1 - 1 / (r : ℝ)^2 := by simp [f]
      have hpos : 0 ≤ f (r + 1) := by
        rw [hf, sub_nonneg, div_le_one₀ (by positivity)]
        nlinarith
      have hone : f (r + 1) ≤ 1 := by rw [hf]; exact sub_le_self _ (by positivity)
      have htel : b (r + 1) = f (r + 1) * b r := by
        rw [hf]
        simp only [b, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
        field_simp [ne_of_gt hr0, ne_of_gt hr1]
        ring
      have hprev : b r ≤ (S.erase (r + 1)).prod f := by
        apply ih
        intro i hi
        obtain ⟨hne, hin⟩ := Finset.mem_erase.mp hi
        obtain ⟨hlt, hle⟩ := hS i hin
        exact ⟨hlt, by omega⟩
      rw [htel]
      refine (mul_le_mul_of_nonneg_left hprev hpos).trans ?_
      by_cases hm : r + 1 ∈ S
      · exact (Finset.mul_prod_erase S f hm).le
      · rw [Finset.erase_eq_of_notMem hm] at *
        have hb : 0 ≤ b r := by
          dsimp [b]
          exact mul_nonneg (by norm_num)
            (div_nonneg hr0.le hr1.le)
        exact mul_le_of_le_one_left (hb.trans hprev) hone
  let P := (Finset.range (Q+1)).filter (fun p => Nat.Prime p ∧ 2 < p)
  by_cases hQ : 2 ≤ Q
  · have hS : ∀ i ∈ P, 2 < i ∧ i ≤ Q := by
      intro i hi
      obtain ⟨hil, _, hlt⟩ := Finset.mem_filter.mp hi
      exact ⟨hlt, Nat.le_of_lt_succ (Finset.mem_range.mp hil)⟩
    have hbase := hbound Q hQ P hS
    let fac := fun p : ℕ => if p ∣ n then (p : ℝ) / ((p : ℝ) - 1) else f p
    have hcomp : P.prod f ≤ P.prod fac := by
      apply Finset.prod_le_prod₀
      · intro p hp
        have hp' : (2 : ℝ) < p := by exact_mod_cast (hS p hp).1
        have hp₁ : (0 : ℝ) < p - 1 := by linarith
        change 0 ≤ 1 - 1 / ((p : ℝ) - 1)^2
        rw [sub_nonneg, div_le_one₀ (by positivity)]
        nlinarith
      · intro p hp
        have hp' : (2 : ℝ) < p := by exact_mod_cast (hS p hp).1
        change f p ≤ if p ∣ n then (p : ℝ) / ((p : ℝ) - 1) else f p
        split_ifs
        · have h₁ : f p ≤ 1 := sub_le_self _ (by positivity)
          have h₂ : (1 : ℝ) ≤ p / ((p : ℝ) - 1) := (one_le_div (by linarith)).mpr (by linarith)
          exact h₁.trans h₂
        · exact le_rfl
    have hq' : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hratio : (1 : ℝ) ≤ Q / ((Q : ℝ) - 1) := (one_le_div (by linarith)).mpr (by linarith)
    dsimp [b] at hbase
    change 1 ≤ 2 * P.prod fac
    linarith
  · have hempty : P = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      obtain ⟨hin, _, hlt⟩ := Finset.mem_filter.mp hi
      have := Finset.mem_range.mp hin
      omega
    change 1 ≤ 2 * P.prod _
    rw [hempty, Finset.prod_empty]
    norm_num
