import Mathlib

private lemma lrcsr_disj (k : ℕ) (S : Finset (Fin (3*k+1))) (hS : S.card = k)
    (B : Finset (Fin (3*k+1))) (hB : B.card ≤ 3) :
    ∃ t : Fin (3*k+1), B ∩ S.image (fun i => i + t) = ∅ := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin (3*k+1))) ⊆
      B.biUnion (fun b => S.image (fun s => b - s)) := by
    intro t _
    obtain ⟨b, hb⟩ := h t
    rw [Finset.mem_inter, Finset.mem_image] at hb
    obtain ⟨hbB, s, hs, hst⟩ := hb
    rw [Finset.mem_biUnion]
    refine ⟨b, hbB, ?_⟩
    rw [Finset.mem_image]
    exact ⟨s, hs, by show b - s = t; rw [← hst]; abel⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_biUnion_le (s := B) (t := fun b => S.image (fun s => b - s))
  have h3 : ∑ b ∈ B, (S.image (fun s => b - s)).card ≤ ∑ b ∈ B, k := by
    apply Finset.sum_le_sum
    intro b _
    exact (Finset.card_image_le).trans hS.le
  rw [Finset.sum_const, smul_eq_mul] at h3
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have : B.card * k ≤ 3 * k := Nat.mul_le_mul_right k hB
  omega

private lemma lrcsr_pair (k : ℕ) (S : Finset (Fin (3*k+1)))
    (hd : ∀ d : Fin (3*k+1), d ≠ 0 → ∃ s1 ∈ S, ∃ s2 ∈ S, s1 = d + s2)
    (B : Finset (Fin (3*k+1))) (hB : 2 ≤ B.card) :
    ∃ t : Fin (3*k+1), 2 ≤ (B ∩ S.image (fun i => i + t)).card := by
  obtain ⟨b1, hb1, b2, hb2, hne⟩ := Finset.one_lt_card.mp hB
  obtain ⟨s1, hs1, s2, hs2, h12⟩ := hd (b1 - b2) (sub_ne_zero.mpr hne)
  refine ⟨b2 - s2, ?_⟩
  have hsub : ({b1, b2} : Finset (Fin (3*k+1))) ⊆ B ∩ S.image (fun i => i + (b2 - s2)) := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_inter, Finset.mem_image]
    rcases hx with hx | hx <;> rw [hx]
    · exact ⟨hb1, s1, hs1, by show s1 + (b2 - s2) = _; rw [h12]; abel⟩
    · exact ⟨hb2, s2, hs2, by show s2 + (b2 - s2) = _; abel⟩
  have := Finset.card_le_card hsub
  rwa [Finset.card_pair hne] at this

private lemma lrcsr_diff (k : ℕ) (hk : 6 ≤ k) (d : Fin (3*k+1)) (hd : d ≠ 0) :
    ∃ s1 s2 : Fin (3*k+1),
      (s1.val ≤ k-2 ∨ s1.val = 2*k-3) ∧ (s2.val ≤ k-2 ∨ s2.val = 2*k-3) ∧ s1 = d + s2 := by
  have hv : 1 ≤ d.val := by
    rcases Nat.eq_zero_or_pos d.val with h | h
    · exact absurd (Fin.ext (by simpa using h)) hd
    · exact h
  have hlt := d.isLt
  by_cases ha : d.val ≤ k - 2
  · refine ⟨d, 0, Or.inl ha, Or.inl (by simp), by simp⟩
  by_cases hb : d.val ≤ 2*k-3
  · refine ⟨⟨2*k-3, by omega⟩, ⟨2*k-3-d.val, by omega⟩, Or.inr rfl, Or.inl (by simp; omega), ?_⟩
    apply Fin.ext
    rw [Fin.val_add]
    simp only
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  by_cases hc : d.val ≤ 2*k+2
  · refine ⟨⟨2*k-3-(3*k+1-d.val), by omega⟩, ⟨2*k-3, by omega⟩, Or.inl (by simp; omega), Or.inr rfl, ?_⟩
    apply Fin.ext
    rw [Fin.val_add]
    simp only
    have : d.val + (2*k-3) = (3*k+1) + (2*k-3-(3*k+1-d.val)) := by omega
    rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  · refine ⟨0, ⟨3*k+1-d.val, by omega⟩, Or.inl (by simp), Or.inl (by simp; omega), ?_⟩
    apply Fin.ext
    rw [Fin.val_add]
    simp only
    have : d.val + (3*k+1-d.val) = 3*k+1 := by omega
    rw [this, Nat.mod_self]
    simp

theorem Conjectures.LogRank.CyclicSmallRows :
    ∀ k : ℕ, 6 ≤ k → let n := 3*k+1; let S := (Finset.univ : Finset (Fin n)).filter (fun i => i.val ≤ k-2 ∨ i.val = 2*k-3); let shift := fun (t : Fin n) => S.image (fun i => i+t); S.card = k ∧ ∀ A : Finset (Fin n), (A.card = 2 ∨ A.card = 3 ∨ Aᶜ.card = 2 ∨ Aᶜ.card = 3) → ∀ a : ℤ, ∃ t : Fin n, ¬ (((A ∩ shift t).card : ℤ) = a ∨ ((A ∩ shift t).card : ℤ) = a+1) := by
  intro k hk n S shift
  have hcard : S.card = k := by
    have hmap : S.map Fin.valEmbedding = Finset.range (k-1) ∪ {2*k-3} := by
      ext x
      simp only [Finset.mem_map, Fin.valEmbedding_apply, Finset.mem_union, Finset.mem_range,
        Finset.mem_singleton, S, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨a, ha, rfl⟩
        omega
      · intro hx
        exact ⟨⟨x, by omega⟩, by simp only; omega, rfl⟩
    have := congrArg Finset.card hmap
    rw [Finset.card_map, Finset.card_union_of_disjoint (by
      rw [Finset.disjoint_left]; intro x hx hx'
      simp only [Finset.mem_range, Finset.mem_singleton] at hx hx'
      omega)] at this
    simp at this
    omega
  refine ⟨hcard, ?_⟩
  intro A hA a
  have hinj : ∀ t : Fin n, (shift t).card = k := by
    intro t
    show (S.image (fun i => i + t)).card = k
    rw [Finset.card_image_of_injective _ (add_left_injective t), hcard]
  have hd : ∀ d : Fin (3*k+1), d ≠ 0 → ∃ s1 ∈ S, ∃ s2 ∈ S, s1 = d + s2 := by
    intro d hd
    obtain ⟨s1, s2, h1, h2, h⟩ := lrcsr_diff k hk d hd
    exact ⟨s1, by simp [S, h1], s2, by simp [S, h2], h⟩
  have key : ∀ B : Finset (Fin n), (B.card = 2 ∨ B.card = 3) →
      (∃ t, (B ∩ shift t).card = 0) ∧ ∃ t, 2 ≤ (B ∩ shift t).card := by
    intro B hB
    constructor
    · obtain ⟨t, ht⟩ := lrcsr_disj k S hcard B (by omega)
      exact ⟨t, by simp only [shift]; rw [ht]; rfl⟩
    · exact lrcsr_pair k S hd B (by omega)
  rcases hA with h | h | h | h
  · obtain ⟨⟨t0, h0⟩, t1, h1⟩ := key A (Or.inl h)
    by_cases hh : ((A ∩ shift t0).card : ℤ) = a ∨ ((A ∩ shift t0).card : ℤ) = a+1
    · refine ⟨t1, ?_⟩
      omega
    · exact ⟨t0, hh⟩
  · obtain ⟨⟨t0, h0⟩, t1, h1⟩ := key A (Or.inr h)
    by_cases hh : ((A ∩ shift t0).card : ℤ) = a ∨ ((A ∩ shift t0).card : ℤ) = a+1
    · refine ⟨t1, ?_⟩
      omega
    · exact ⟨t0, hh⟩
  all_goals
    obtain ⟨⟨t0, h0⟩, t1, h1⟩ := key Aᶜ (by omega)
    have e : ∀ t, (A ∩ shift t).card + (Aᶜ ∩ shift t).card = k := by
      intro t
      rw [← hinj t, ← Finset.card_union_of_disjoint]
      · congr 1
        ext x
        simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_compl]
        tauto
      · rw [Finset.disjoint_left]
        intro x hx hx'
        simp only [Finset.mem_inter, Finset.mem_compl] at hx hx'
        exact hx'.1 hx.1
    have e0 := e t0
    have e1 := e t1
    by_cases hh : ((A ∩ shift t0).card : ℤ) = a ∨ ((A ∩ shift t0).card : ℤ) = a+1
    · refine ⟨t1, ?_⟩
      omega
    · exact ⟨t0, hh⟩
