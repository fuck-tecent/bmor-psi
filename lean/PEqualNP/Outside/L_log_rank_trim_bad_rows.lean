import Mathlib

theorem PEqualNP.Outside.L_log_rank_trim_bad_rows :
    ∀ (m n : ℕ) (A : Fin m → Fin n → Bool) (R : Finset (Fin m)) (C : Finset (Fin n)), let bad := fun i => C.filter (fun j => A i j=false); ∀ t:ℕ,(t+1)*(R.filter (fun i => t<(bad i).card)).card≤∑ i ∈ R,(bad i).card := by
  intro m n A R C
  dsimp only
  intro t
  set T : Finset (Fin m) := R.filter (fun i => t < (C.filter (fun j => A i j = false)).card) with hT
  have h1 : (t + 1) * T.card = ∑ i ∈ T, (t + 1) := by
    rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have h2 : ∑ i ∈ T, (t + 1) ≤ ∑ i ∈ T, (C.filter (fun j => A i j = false)).card := by
    apply Finset.sum_le_sum
    intro i hi
    rw [hT] at hi
    exact Nat.succ_le_of_lt (Finset.mem_filter.mp hi).2
  have h3 : ∑ i ∈ T, (C.filter (fun j => A i j = false)).card
      ≤ ∑ i ∈ R, (C.filter (fun j => A i j = false)).card := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · rw [hT]
      exact Finset.filter_subset _ _
    · intro i _ _
      exact Nat.zero_le _
  rw [h1]
  exact le_trans h2 h3
