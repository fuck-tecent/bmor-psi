import Mathlib

theorem PEqualNP.Outside.L_log_rank_rectangle_restrict :
    ∀ (m n:ℕ) (A:Fin m→Fin n→Bool) (I U:Finset (Fin m)) (J V:Finset (Fin n)) (b:Bool), U⊆I → V⊆J → (∀ i∈I,∀ j∈J,A i j=b) → ∀ i∈U,∀ j∈V,A i j=b := by
  intro m n A I U J V b hUI hVJ h i hiU j hjV
  exact h i (hUI hiU) j (hVJ hjV)
