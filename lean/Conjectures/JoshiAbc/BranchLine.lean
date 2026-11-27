import Mathlib

theorem Conjectures.JoshiAbc.BranchLine :
    let g := fun (u : ZMod 29) => (![u,0,0] : Fin 3 → ZMod 29); let S := {v | ∃ u : ZMod 29, u^14=1 ∧ v=g u}; Submodule.span (ZMod 29) S = Submodule.span (ZMod 29) ({g 1} : Set (Fin 3 → ZMod 29)) := by
  refine (let g := fun (u : ZMod 29) => (![u,0,0] : Fin 3 → ZMod 29)
        let S := {v | ∃ u : ZMod 29, u^14=1 ∧ v=g u}
        ?_)
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro v ⟨u, _, rfl⟩
    have key : g u = u • g 1 := by
      funext i
      fin_cases i <;> simp [g]
    have hmem : g u ∈ Submodule.span (ZMod 29) ({g 1} : Set (Fin 3 → ZMod 29)) := by
      rw [key]
      exact Submodule.smul_mem _ u (Submodule.subset_span (Set.mem_singleton _))
    exact hmem
  · refine Submodule.span_mono ?_
    exact Set.singleton_subset_iff.2 ⟨1, one_pow 14, rfl⟩
