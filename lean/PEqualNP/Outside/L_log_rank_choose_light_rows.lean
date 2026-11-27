import Mathlib

private theorem lr_light (m : ℕ) (f : Fin m → ℕ) (R : Finset (Fin m)) (k : ℕ) (hk : k ≤ R.card) :
    ∃ U : Finset (Fin m), U ⊆ R ∧ U.card = k ∧
      R.card * (∑ i ∈ U, f i) ≤ k * (∑ i ∈ R, f i) := by
  classical
  obtain ⟨U₀, hU₀sub, hU₀card⟩ := Finset.exists_subset_card_eq hk
  have hne : (R.powersetCard k).Nonempty :=
    ⟨U₀, Finset.mem_powersetCard.mpr ⟨hU₀sub, hU₀card⟩⟩
  obtain ⟨U, hUmem, hUmin⟩ :=
    Finset.exists_min_image (R.powersetCard k) (fun U => ∑ i ∈ U, f i) hne
  obtain ⟨hUsub, hUcard⟩ := Finset.mem_powersetCard.mp hUmem
  have hTcard : (R \ U).card = R.card - k := by
    have h := Finset.card_sdiff_add_card_eq_card hUsub
    rw [hUcard] at h
    omega
  have hex : ∀ a ∈ U, ∀ b ∈ R \ U, f a ≤ f b := by
    intro a ha b hb
    rw [Finset.mem_sdiff] at hb
    obtain ⟨hbR, hbU⟩ := hb
    have hbnot : b ∉ U.erase a := fun h => hbU (Finset.mem_of_mem_erase h)
    have hpos : 0 < k := by
      rw [← hUcard]
      exact Finset.card_pos.mpr ⟨a, ha⟩
    have hU'card : (insert b (U.erase a)).card = k := by
      rw [Finset.card_insert_of_notMem hbnot, Finset.card_erase_of_mem ha, hUcard]
      omega
    have hU'sub : insert b (U.erase a) ⊆ R := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hbR
      · exact hUsub (Finset.mem_of_mem_erase hx)
    have hmem' : insert b (U.erase a) ∈ R.powersetCard k :=
      Finset.mem_powersetCard.mpr ⟨hU'sub, hU'card⟩
    have hle := hUmin _ hmem'
    have hs1 : ∑ i ∈ U, f i = ∑ i ∈ U.erase a, f i + f a := by
      rw [← Finset.sum_erase_add U f ha]
    have hs2 : ∑ i ∈ insert b (U.erase a), f i = f b + ∑ i ∈ U.erase a, f i := by
      rw [Finset.sum_insert hbnot]
    rw [hs1, hs2] at hle
    omega
  have hdc : (R.card - k) * (∑ i ∈ U, f i) ≤ k * (∑ i ∈ R \ U, f i) := by
    have hle : ∑ a ∈ U, ∑ b ∈ R \ U, f a ≤ ∑ a ∈ U, ∑ b ∈ R \ U, f b := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact hex a ha b hb
    have e1 : (∑ a ∈ U, ∑ b ∈ R \ U, f a) = (R.card - k) * (∑ a ∈ U, f a) := by
      rw [Finset.mul_sum, ← hTcard]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_const, smul_eq_mul]
    have e2 : (∑ a ∈ U, ∑ b ∈ R \ U, f b) = k * (∑ b ∈ R \ U, f b) := by
      rw [Finset.sum_const, smul_eq_mul, hUcard]
    rw [e1, e2] at hle
    exact hle
  have hsplit : (∑ i ∈ R \ U, f i) + (∑ i ∈ U, f i) = ∑ i ∈ R, f i := Finset.sum_sdiff hUsub
  refine ⟨U, hUsub, hUcard, ?_⟩
  calc R.card * (∑ i ∈ U, f i)
      = ((R.card - k) + k) * (∑ i ∈ U, f i) := by rw [Nat.sub_add_cancel hk]
    _ = (R.card - k) * (∑ i ∈ U, f i) + k * (∑ i ∈ U, f i) := Nat.add_mul _ _ _
    _ ≤ k * (∑ i ∈ R \ U, f i) + k * (∑ i ∈ U, f i) := Nat.add_le_add_right hdc _
    _ = k * ((∑ i ∈ R \ U, f i) + ∑ i ∈ U, f i) := (Nat.mul_add _ _ _).symm
    _ = k * (∑ i ∈ R, f i) := by rw [hsplit]

theorem PEqualNP.Outside.L_log_rank_choose_light_rows :
    ∀ (m n : ℕ) (A : Fin m → Fin n → Bool) (R : Finset (Fin m)) (C : Finset (Fin n)), let bad := fun i => C.filter (fun j => A i j=false); ∀ k:ℕ,k≤R.card → ∃ U:Finset (Fin m), U⊆R ∧ U.card=k ∧ R.card*(∑ i ∈ U,(bad i).card)≤k*(∑ i ∈ R,(bad i).card) := by
  intro m n A R C
  dsimp only
  intro k hk
  exact lr_light m (fun i => (C.filter (fun j => A i j = false)).card) R k hk
