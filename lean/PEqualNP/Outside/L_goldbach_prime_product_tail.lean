import Mathlib

theorem PEqualNP.Outside.L_goldbach_prime_product_tail : let P := fun Q : ℕ => (Finset.range (Q+1)).filter (fun p => Nat.Prime p ∧ 2<p); ∀ Q R : ℕ, 3≤Q → Q≤R → let T := P R \ P Q; 1-Finset.prod T (fun p => 1-1/((p:ℝ)-1)^2) ≤ 1/((Q:ℝ)-1) := by
  dsimp only
  intro Q R hQ hQR
  let f := fun i : ℕ => 1 - 1 / ((i : ℝ) - 1)^2
  let b := fun i : ℕ => (((Q : ℝ) - 1) / Q) * ((i : ℝ) / (i - 1))
  have hq : (3 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hbound (r : ℕ) (hr : Q ≤ r) (S : Finset ℕ)
      (hS : ∀ i ∈ S, Q < i ∧ i ≤ r) : b r ≤ S.prod f := by
    induction r, hr using Nat.le_induction generalizing S with
    | base =>
      have hempty : S = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        obtain ⟨hlt, hle⟩ := hS i hi
        omega
      rw [hempty, Finset.prod_empty]
      dsimp [b]
      have hq0 : (Q : ℝ) ≠ 0 := by linarith
      have hq1 : (Q : ℝ) - 1 ≠ 0 := by linarith
      apply le_of_eq
      field_simp
    | succ r hr ih =>
      have hr' : (Q : ℝ) ≤ r := by exact_mod_cast hr
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
          exact mul_nonneg (div_nonneg (by linarith) (by positivity))
            (div_nonneg hr0.le hr1.le)
        exact mul_le_of_le_one_left (hb.trans hprev) hone
  let T := ((Finset.range (R + 1)).filter fun p => Nat.Prime p ∧ 2 < p) \
    ((Finset.range (Q + 1)).filter fun p => Nat.Prime p ∧ 2 < p)
  have hT : ∀ i ∈ T, Q < i ∧ i ≤ R := by
    intro i hi
    obtain ⟨hhi, hlo⟩ := Finset.mem_sdiff.mp hi
    obtain ⟨hin, hp⟩ := Finset.mem_filter.mp hhi
    have hout : ¬ i < Q + 1 := fun h => hlo (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h, hp⟩)
    have h := Finset.mem_range.mp hin
    omega
  have hprod := hbound R hQR T hT
  have hr' : (Q : ℝ) ≤ R := by exact_mod_cast hQR
  have hfrac : 1 ≤ (R : ℝ) / (R - 1) := (one_le_div (by linarith)).mpr (by linarith)
  have hfloor : ((Q : ℝ) - 1) / Q ≤ b R := by
    exact le_mul_of_one_le_right (div_nonneg (by linarith) (by positivity)) hfrac
  change 1 - T.prod f ≤ _
  have hsmall : 1 / (Q : ℝ) ≤ 1 / ((Q : ℝ) - 1) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have hid : ((Q : ℝ) - 1) / Q = 1 - 1 / Q := by
    field_simp [show (Q : ℝ) ≠ 0 by linarith]
  linarith
