import Mathlib

theorem PEqualNP.Outside.L_log_rank_row_pattern :
    ∀ (m n:ℕ) (A:Fin m→Fin n→Bool) (I U:Finset (Fin m)) (J:Finset (Fin n)) (b:Bool), (∀ i∈I,∀ j∈J,A i j=b) → (∀ i∈U,∀ j∈J,A i j=b) → ∀ i∈I∪U,∀ j∈J,A i j=b := by
  intro m n A I U J b h1 h2 i hi j hj
  rcases Finset.mem_union.mp hi with hiI | hiU
  · exact h1 i hiI j hj
  · exact h2 i hiU j hj
