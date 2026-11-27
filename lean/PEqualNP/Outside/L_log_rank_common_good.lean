import Mathlib

theorem PEqualNP.Outside.L_log_rank_common_good :
    ∀ (m n : ℕ) (A : Fin m → Fin n → Bool) (R : Finset (Fin m)) (C : Finset (Fin n)), let bad := fun i => C.filter (fun j => A i j=false); let D:=R.biUnion bad; C.card≤(C \ D).card+(∑ i ∈ R,(bad i).card) := by
  intro m n A R C
  dsimp only
  have hsub : R.biUnion (fun i => C.filter (fun j => A i j = false)) ⊆ C := by
    intro j hj
    obtain ⟨i, _, hji⟩ := Finset.mem_biUnion.mp hj
    exact (Finset.mem_filter.mp hji).1
  have h1 : (C \ R.biUnion (fun i => C.filter (fun j => A i j = false))).card
      + (R.biUnion (fun i => C.filter (fun j => A i j = false))).card = C.card :=
    Finset.card_sdiff_add_card_eq_card hsub
  have h2 : (R.biUnion (fun i => C.filter (fun j => A i j = false))).card
      ≤ ∑ i ∈ R, (C.filter (fun j => A i j = false)).card := Finset.card_biUnion_le
  omega
