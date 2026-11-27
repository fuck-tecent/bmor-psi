import Mathlib

theorem PEqualNP.Outside.L_log_rank_minority_double_count : ∀ (m n : ℕ) (A : Fin m → Fin n → Bool) (R : Finset (Fin m)) (C : Finset (Fin n)), let bad := fun i => C.filter (fun j => A i j=false); (∑ i ∈ R,(bad i).card)=∑ j ∈ C,(R.filter (fun i => A i j=false)).card := by
  intro m n A R C bad
  simp only [bad, Finset.card_filter]
  exact Finset.sum_comm
