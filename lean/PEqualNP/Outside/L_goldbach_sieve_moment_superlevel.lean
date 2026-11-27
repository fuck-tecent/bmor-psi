import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem PEqualNP.Outside.L_goldbach_sieve_moment_superlevel :
    ∀ (s : Finset ℕ) (a : ℕ → ℝ) (t : ℝ), (∀ i ∈ s, 0≤a i) → 0≤t → (s.card:ℝ)*t ≤ ∑ i ∈ s, a i → ((∑ i ∈ s, a i)-(s.card:ℝ)*t)^2 ≤ ((s.filter (fun i => t≤a i)).card:ℝ)*(∑ i ∈ s, (a i)^2) := by
  intro s a t ha ht hle
  set F := s.filter (fun i => t ≤ a i) with hF
  have hFs : F ⊆ s := Finset.filter_subset _ _
  have h1 : (∑ i ∈ s, a i) - (s.card : ℝ) * t = ∑ i ∈ s, (a i - t) := by
    rw [Finset.sum_sub_distrib]; simp
  have h2 : ∑ i ∈ s, (a i - t) ≤ ∑ i ∈ F, (a i - t) := by
    rw [hF, Finset.sum_filter]
    refine Finset.sum_le_sum fun i hi => ?_
    split_ifs with h
    · exact le_rfl
    · have := not_le.1 h; linarith
  have h3 : ∑ i ∈ F, (a i - t) ≤ ∑ i ∈ F, a i := by
    refine Finset.sum_le_sum fun i _ => ?_
    linarith
  have h4 : 0 ≤ (∑ i ∈ s, a i) - (s.card : ℝ) * t := by linarith
  have h5 : (∑ i ∈ s, a i) - (s.card : ℝ) * t ≤ ∑ i ∈ F, a i := by linarith
  have h6 : ((∑ i ∈ s, a i) - (s.card : ℝ) * t) ^ 2 ≤ (∑ i ∈ F, a i) ^ 2 := by
    exact pow_le_pow_left₀ h4 h5 2
  have h7 : (∑ i ∈ F, a i) ^ 2 ≤ (F.card : ℝ) * ∑ i ∈ F, (a i) ^ 2 :=
    by
    have := Finset.sum_mul_sq_le_sq_mul_sq F (fun _ => (1 : ℝ)) a
    simpa using this
  have h8 : ∑ i ∈ F, (a i) ^ 2 ≤ ∑ i ∈ s, (a i) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hFs fun i _ _ => sq_nonneg _
  have h9 : (0 : ℝ) ≤ F.card := Nat.cast_nonneg _
  calc _ ≤ _ := h6
    _ ≤ _ := h7
    _ ≤ _ := mul_le_mul_of_nonneg_left h8 h9
