import Mathlib

theorem PEqualNP.Outside.L_log_rank_opposite_disjoint :
    ∀ (m n:ℕ) (A:Fin m→Fin n→Bool) (I U:Finset (Fin m)) (J V:Finset (Fin n)), (∀ i∈I,∀ j∈J,A i j=true) → (∀ i∈U,∀ j∈V,A i j=false) → Disjoint I U ∨ Disjoint J V := by
  intro m n A I U J V htrue hfalse
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hIU, hJV⟩ := hcon
  rw [Finset.not_disjoint_iff] at hIU hJV
  obtain ⟨i, hiI, hiU⟩ := hIU
  obtain ⟨j, hjJ, hjV⟩ := hJV
  have ht : A i j = true := htrue i hiI j hjJ
  have hf : A i j = false := hfalse i hiU j hjV
  rw [hf] at ht
  exact Bool.noConfusion ht
