import Mathlib

theorem Conjectures.JoshiAbc.ThreeJetSpan :
    let z : ZMod 29 := 7; let v : Fin 3 → Fin 3 → ZMod 29 := ![![1,0,0],![0,1+z^2,0],![1,0,z^2]]; Submodule.span (ZMod 29) (Set.range v) = ⊤ := by
  intro z v
  rw [eq_top_iff]
  rintro w -
  have hw : w =
      (w 0 - 16 * w 2) • v 0 +
      (18 * w 1) • v 1 +
      (16 * w 2) • v 2 := by
    funext i
    fin_cases i <;>
      simp [v, z] <;>
      ring_nf <;>
      reduce_mod_char
  rw [hw]
  exact add_mem
    (add_mem
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩))
