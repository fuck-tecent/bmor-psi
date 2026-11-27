import Mathlib

private lemma log_one_add_div_lower (n j : ℝ) (hn : 0 < n) (hj : 0 ≤ j) :
    j / (n + j) ≤ Real.log (1 + j / n) := by
  have hpos : 0 < 1 + j / n := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have e : 1 - (1 + j / n)⁻¹ = j / (n + j) := by
    field_simp
    ring
  linarith

private lemma log_one_add_div_upper (n j : ℝ) (hn : 0 < n) (hj : 0 ≤ j) :
    Real.log (1 + j / n) ≤ j / n := by
  have hpos : 0 < 1 + j / n := by positivity
  have h := Real.log_le_sub_one_of_pos hpos
  linarith

private lemma band_off (x n j : ℝ) (hx : 1000 ≤ x) (hxn : x ≤ n) (hn : 50*n ≤ 51*x)
    (hj : j = 1 ∨ 3 ≤ j) : 1/4 ≤ |x * Real.log (1 + j/n) - 2| := by
  have hn0 : 0 < n := by linarith
  have hx0 : 0 ≤ x := by linarith
  rcases hj with rfl | hj
  · have hup := log_one_add_div_upper n 1 hn0 zero_le_one
    have h1 : x * Real.log (1 + 1/n) ≤ x * (1 / n) := mul_le_mul_of_nonneg_left hup hx0
    have h2 : x * (1 / n) ≤ 1 := by
      rw [mul_one_div, div_le_one hn0]
      exact hxn
    rw [abs_sub_comm]
    apply le_abs.mpr
    left
    linarith
  · have hj0 : (0:ℝ) ≤ j := by linarith
    have hlow := log_one_add_div_lower n j hn0 hj0
    have h1 : x * (j / (n + j)) ≤ x * Real.log (1 + j/n) := mul_le_mul_of_nonneg_left hlow hx0
    have h2 : 9/4 < x * (j / (n + j)) := by
      rw [← mul_div_assoc, lt_div_iff₀ (by linarith)]
      nlinarith
    apply le_abs.mpr
    left
    linarith

theorem PEqualNP.Outside.L_twin_primes_finite_band_sum :
    let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let f := fun (x n j : ℝ) => x * Real.log (1+j/n); ∀ (X : ℕ) (u : ℕ → ℝ) (H : ℝ → ℝ), 1000 ≤ X → (∀ v, 1/4 ≤ |v| → H v = 0) → (w X).sum (fun n => ((w X).filter (fun m => n < m)).sum (fun m => u n*u m*H (f X n (m-n) - 2))) = ((w X).filter (fun n => n+2 ∈ w X)).sum (fun n => u n*u (n+2)*H (f X n 2 - 2)) := by
  intro w f X u H hX hH
  have hmem : ∀ n, n ∈ w X ↔ n < 2*X+1 ∧ X < n ∧ 50*n < 51*X := by
    intro n
    simp only [w, Finset.mem_filter, Finset.mem_range]
  have key : ∀ n ∈ w X, ∀ m ∈ w X, n < m → m ≠ n + 2 → H (f X n ((m:ℝ) - n) - 2) = 0 := by
    intro n hn m hm hnm hne
    apply hH
    rw [hmem] at hn
    obtain ⟨-, hn1, hn2⟩ := hn
    have hXr : (1000:ℝ) ≤ X := by exact_mod_cast hX
    have hxn : (X:ℝ) ≤ n := by exact_mod_cast hn1.le
    have hn' : 50*(n:ℝ) ≤ 51*X := by exact_mod_cast hn2.le
    have hj : ((m:ℝ) - n) = 1 ∨ 3 ≤ ((m:ℝ) - n) := by
      rcases (show m = n+1 ∨ n + 3 ≤ m by omega) with h | h
      · left
        rw [h]
        push_cast
        ring
      · right
        have : ((n+3 : ℕ):ℝ) ≤ m := by exact_mod_cast h
        push_cast at this
        linarith
    exact band_off X n _ hXr hxn hn' hj
  rw [Finset.sum_filter (fun n => n + 2 ∈ w X)]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs with h2
  · rw [Finset.sum_eq_single (n+2)]
    · have e : ((n+2 : ℕ):ℝ) - n = 2 := by
        push_cast
        ring
      rw [e]
    · intro m hm hne
      rw [Finset.mem_filter] at hm
      rw [key n hn m hm.1 hm.2 hne, mul_zero]
    · intro hnot
      exfalso
      apply hnot
      rw [Finset.mem_filter]
      exact ⟨h2, by omega⟩
  · apply Finset.sum_eq_zero
    intro m hm
    rw [Finset.mem_filter] at hm
    have hne : m ≠ n + 2 := by
      rintro rfl
      exact h2 hm.1
    rw [key n hn m hm.1 hm.2 hne, mul_zero]
