import Mathlib

theorem Conjectures.Cuts.Taske94b78f29bbb55ecf8c0597e :
    (∀ (x1 x2 : ℕ) (x3 : Matrix (Fin x1) (Fin x2) ℝ) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)) (x6 : ℝ), (∀ (x7 : Fin x1) (x8 : Fin x2), x3 x7 x8 = (0 : ℝ) ∨ x3 x7 x8 = (1 : ℝ)) → x6 = (0 : ℝ) ∨ x6 = (1 : ℝ) → (4 : ℕ) * (x3.rank + (1 : ℕ)) * {x9 ∈ x4.product x5 | x3 x9.1 x9.2 ≠ x6}.card ≤ x4.card * x5.card → ∃ (x10 : Finset (Fin x1)) (x11 : Finset (Fin x2)), x10 ⊆ x4 ∧ x11 ⊆ x5 ∧ (∀ x12 ∈ x10, ∀ x14 ∈ x11, x3 x12 x14 = x6) ∧ x4.card * x5.card ≤ (4 : ℕ) * (x10.card * x11.card)) := by
  classical
  intro m n M A B v _hBoolean _hv herr
  by_cases hB : B.card = 0
  · refine ⟨∅, ∅, by simp, by simp, by simp, ?_⟩
    simp [hB]
  let k := M.rank + 1
  have hk : 0 < k := by dsimp [k]; omega
  let err (i : Fin m) := B.filter (fun j => M i j ≠ v)
  let G := A.filter (fun i => 2 * k * (err i).card ≤ B.card)
  let bad := A \ G
  have hGA : G ⊆ A := Finset.filter_subset _ _
  have hbadA : bad ⊆ A := Finset.sdiff_subset
  have hTotal :
      ∑ i ∈ A, (err i).card = ((A.product B).filter (fun ij => M ij.1 ij.2 ≠ v)).card := by
    calc
      ∑ i ∈ A, (err i).card = ∑ i ∈ A, ∑ j ∈ B, (if M i j ≠ v then 1 else 0 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact Finset.natCast_card_filter (R:=ℕ) (fun j => M i j ≠ v) B
      _ = ∑ ij ∈ A.product B, (if M ij.1 ij.2 ≠ v then 1 else 0 : ℕ) := by
        exact (Finset.sum_product' A B _).symm
      _ = _ := Finset.sum_boole (R:=ℕ) (fun ij => M ij.1 ij.2 ≠ v) (A.product B)
  have hbadRow : ∀ i ∈ bad, B.card ≤ 2 * k * (err i).card := by
    intro i hi
    obtain ⟨hiA, hiG⟩ := Finset.mem_sdiff.mp hi
    have : ¬ 2 * k * (err i).card ≤ B.card :=
      fun h => hiG (Finset.mem_filter.mpr ⟨hiA,h⟩)
    omega
  have hbadMass : bad.card * B.card ≤ 2 * k * (∑ i ∈ A, (err i).card) := by
    calc
      bad.card * B.card = ∑ _i ∈ bad, B.card := by simp
      _ ≤ ∑ i ∈ bad, 2 * k * (err i).card := Finset.sum_le_sum hbadRow
      _ = 2 * k * (∑ i ∈ bad, (err i).card) := (Finset.mul_sum ..).symm
      _ ≤ _ := Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset_of_nonneg hbadA (by simp))
  have hbadTwice : 2 * bad.card ≤ A.card := by
    apply Nat.le_of_mul_le_mul_right _ (Nat.pos_of_ne_zero hB)
    calc
      2 * bad.card * B.card = 2 * (bad.card * B.card) := by ring
      _ ≤ 2 * (2 * k * (∑ i ∈ A, (err i).card)) := Nat.mul_le_mul_left _ hbadMass
      _ = 4 * k * ((A.product B).filter (fun ij => M ij.1 ij.2 ≠ v)).card := by
        rw [hTotal]; ring
      _ ≤ _ := herr
  have hG : A.card ≤ 2 * G.card := by
    have ha : bad.card + G.card = A.card := Finset.card_sdiff_add_card_eq_card hGA
    omega
  let u : Fin n → ℝ := fun _ => v
  let row : Fin m → Fin n → ℝ := fun i j => M i j - v
  let S : Set (Fin n → ℝ) := row '' (G : Set (Fin m))
  let W := Submodule.span ℝ (Set.range M.row)
  let V := Submodule.span ℝ ({u} : Set (Fin n → ℝ))
  have hIncl : Submodule.span ℝ S ≤ W ⊔ V := by
    apply Submodule.span_le.mpr
    rintro f ⟨i, _hi, rfl⟩
    have hw : M.row i ∈ W := Submodule.subset_span ⟨i,rfl⟩
    have hu : u ∈ V := Submodule.subset_span (by simp)
    exact (W ⊔ V).sub_mem (show M.row i ∈ W ⊔ V from (show W ≤ W ⊔ V from le_sup_left) hw)
      (show u ∈ W ⊔ V from (show V ≤ W ⊔ V from le_sup_right) hu)
  obtain ⟨T, hTS, hTc, hTspan, _hTI⟩ := Submodule.exists_finset_span_eq_linearIndepOn ℝ S
  have hT : T.card ≤ k := by
    have hV : Module.finrank ℝ V ≤ 1 := by
      simpa [V] using (finrank_span_le_card (R:=ℝ) ({u} : Set (Fin n → ℝ)))
    calc
      T.card = Module.finrank ℝ (Submodule.span ℝ S) := hTc
      _ ≤ Module.finrank ℝ (W ⊔ V : Submodule ℝ (Fin n → ℝ)) := Submodule.finrank_mono hIncl
      _ ≤ Module.finrank ℝ W + Module.finrank ℝ V := Submodule.finrank_add_le_finrank_add_finrank W V
      _ ≤ _ := by
        have hW : Module.finrank ℝ W = M.rank := M.rank_eq_finrank_span_row.symm
        dsimp [k]
        omega
  let errs (f : Fin n → ℝ) := B.filter (fun j => f j ≠ 0)
  have hTRow : ∀ f ∈ T, 2 * k * (errs f).card ≤ B.card := by
    intro f hf
    obtain ⟨i, hi, rfl⟩ := hTS hf
    have hGood := (Finset.mem_filter.mp (show i ∈ G from hi)).2
    simpa [errs, row, err, sub_ne_zero] using hGood
  let U := T.biUnion errs
  let D := B \ U
  have hUB : U ⊆ B := by
    intro j hj
    obtain ⟨f, _, hf⟩ := Finset.mem_biUnion.mp hj
    exact (Finset.mem_filter.mp hf).1
  have hU : 2 * U.card ≤ B.card := by
    apply Nat.le_of_mul_le_mul_left _ hk
    calc
      k * (2 * U.card) = (2 * k) * U.card := by ring
      _ ≤ (2 * k) * (∑ f ∈ T, (errs f).card) := Nat.mul_le_mul_left _ Finset.card_biUnion_le
      _ = ∑ f ∈ T, 2 * k * (errs f).card := Finset.mul_sum ..
      _ ≤ ∑ _f ∈ T, B.card := Finset.sum_le_sum hTRow
      _ = T.card * B.card := by simp
      _ ≤ k * B.card := Nat.mul_le_mul_right _ hT
  have hD : B.card ≤ 2 * D.card := by
    have hb : D.card + U.card = B.card := Finset.card_sdiff_add_card_eq_card hUB
    omega
  refine ⟨G, D, hGA, Finset.sdiff_subset, ?_, ?_⟩
  · intro i hi j hj
    obtain ⟨hjB, hjU⟩ := Finset.mem_sdiff.mp hj
    let E : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj j
    have hKernel : Submodule.span ℝ (T : Set (Fin n → ℝ)) ≤ E.ker := by
      apply Submodule.span_le.mpr
      intro f hf
      apply LinearMap.mem_ker.mpr
      change f j = 0
      by_contra h
      exact hjU (Finset.mem_biUnion.mpr ⟨f,hf,Finset.mem_filter.mpr ⟨hjB,h⟩⟩)
    have hRowSpan : row i ∈ Submodule.span ℝ (T : Set (Fin n → ℝ)) := by
      rw [hTspan]; exact Submodule.subset_span ⟨i,hi,rfl⟩
    exact sub_eq_zero.mp (show row i j = 0 from LinearMap.mem_ker.mp (hKernel hRowSpan))
  · calc
      A.card * B.card ≤ (2 * G.card) * (2 * D.card) := Nat.mul_le_mul hG hD
      _ = 4 * (G.card * D.card) := by ring
