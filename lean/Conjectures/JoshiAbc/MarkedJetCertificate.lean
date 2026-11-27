import Mathlib

theorem Conjectures.JoshiAbc.MarkedJetCertificate :
    let z : ZMod 29 := 7; let v : Fin 3 → Fin 3 → ZMod 29 := ![![1,0,0],![0,1+z^2,0],![1,0,z^2]]; ∀ (I : Type) (allowed : I → Set (Fin 3 → ZMod 29)) (i : I), (∀ j, v j ∈ allowed i) → Submodule.span (ZMod 29) (allowed i)=⊤ := by
  intro z v I allowed i h
  have h1 : (18 : ZMod 29) * (1 + z ^ 2) = 1 := by decide
  have h2 : (16 : ZMod 29) * z ^ 2 = 1 := by decide
  have hle : Submodule.span (ZMod 29) (Set.range v) ≤ Submodule.span (ZMod 29) (allowed i) :=
    Submodule.span_mono (Set.range_subset_iff.mpr h)
  have memv : ∀ j : Fin 3, v j ∈ Submodule.span (ZMod 29) (Set.range v) :=
    fun j => Submodule.subset_span ⟨j, rfl⟩
  have key : ∀ w : Fin 3 → ZMod 29, w ∈ Submodule.span (ZMod 29) (Set.range v) := by
    intro w
    have s0 := Submodule.smul_mem (Submodule.span (ZMod 29) (Set.range v)) (w 0 - 16 * w 2) (memv 0)
    have s1 := Submodule.smul_mem (Submodule.span (ZMod 29) (Set.range v)) (18 * w 1) (memv 1)
    have s2 := Submodule.smul_mem (Submodule.span (ZMod 29) (Set.range v)) (16 * w 2) (memv 2)
    have ssum := Submodule.add_mem (Submodule.span (ZMod 29) (Set.range v))
      (Submodule.add_mem (Submodule.span (ZMod 29) (Set.range v)) s0 s1) s2
    have heq : ((w 0 - 16 * w 2) • v 0 + (18 * w 1) • v 1) + (16 * w 2) • v 2 = w := by
      funext k
      fin_cases k
      · simp [v]
      · simp [v]
        linear_combination (w 1) * h1
      · simp [v]
        linear_combination (w 2) * h2
    rw [heq] at ssum
    exact ssum
  refine le_antisymm le_top ?_
  intro w _
  exact hle (key w)
