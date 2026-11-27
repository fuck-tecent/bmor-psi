import Mathlib

private lemma cm_aux (q : ℕ) [NeZero q] :
    ((Finset.range q).filter (fun n => Nat.Coprime n q ∧ Nat.Coprime (n+2) q)).card =
    ((Finset.univ : Finset (ZMod q)).filter (fun x => IsUnit x ∧ IsUnit (x+2))).card := by
  refine Finset.card_nbij' (fun n => (n : ZMod q)) (fun x => x.val) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, Finset.mem_univ,
      true_and] at hn ⊢
    refine ⟨(ZMod.isUnit_iff_coprime n q).mpr hn.2.1, ?_⟩
    have := (ZMod.isUnit_iff_coprime (n+2) q).mpr hn.2.2
    push_cast at this
    exact this
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, Finset.mem_univ,
      true_and] at hx ⊢
    refine ⟨ZMod.val_lt x, ?_, ?_⟩
    · rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
      exact hx.1
    · rw [← ZMod.isUnit_iff_coprime]
      push_cast
      rw [ZMod.natCast_zmod_val]
      exact hx.2
  · intro n hn
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hn
    exact ZMod.val_cast_of_lt hn.1
  · intro x _
    exact ZMod.natCast_zmod_val x

theorem PEqualNP.Outside.L_twin_primes_crt_mask :
    let A := fun (q : ℕ) => ((Finset.range q).filter (fun n => Nat.Coprime n q ∧ Nat.Coprime (n+2) q)).card; ∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b → A (a*b) = A a*A b := by
  dsimp only
  intro a b ha hb hab
  have : NeZero a := ⟨by omega⟩
  have : NeZero b := ⟨by omega⟩
  have : NeZero (a*b) := ⟨by positivity⟩
  rw [cm_aux, cm_aux, cm_aux, ← Finset.card_product]
  let e := ZMod.chineseRemainder hab
  have he2 : ∀ x : ZMod (a*b), e (x + 2) = e x + 2 := by
    intro x
    rw [map_add, map_ofNat]
  refine Finset.card_nbij' (fun x => e x) (fun y => e.symm y) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
      Finset.coe_product, Set.mem_prod] at hx ⊢
    have h1 : IsUnit (e x) := (isUnit_map_iff e x).mpr hx.1
    have h2 : IsUnit (e x + 2) := by
      rw [← he2]
      exact (isUnit_map_iff e _).mpr hx.2
    rw [Prod.isUnit_iff] at h1 h2
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_ofNat, Prod.snd_ofNat] at h2
    exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
      Finset.coe_product, Set.mem_prod] at hy ⊢
    have h1 : IsUnit y := Prod.isUnit_iff.mpr ⟨hy.1.1, hy.2.1⟩
    have h2 : IsUnit (y + 2) := by
      rw [Prod.isUnit_iff]
      simp only [Prod.fst_add, Prod.snd_add, Prod.fst_ofNat, Prod.snd_ofNat]
      exact ⟨hy.1.2, hy.2.2⟩
    refine ⟨(isUnit_map_iff e _).mp ?_, (isUnit_map_iff e _).mp ?_⟩
    · simpa using h1
    · rw [he2]
      simpa using h2
  · intro x _
    simp
  · intro y _
    simp
