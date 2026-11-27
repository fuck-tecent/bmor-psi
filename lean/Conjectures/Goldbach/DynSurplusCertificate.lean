import Mathlib

theorem Conjectures.Goldbach.DynSurplusCertificate :
    let W := fun (A B : Finset ℕ) (n : ℕ) => ((A ×ˢ B).filter (fun t => t.1+t.2=n)).card; ∀ (m n : ℕ) (A B : Finset ℕ), n < m → (∀ a ∈ A, a < m) → (∀ b ∈ B, b < m) → min ((A.filter (fun a => n < a)).card) ((B.filter (fun b => n < b)).card) < ((A ×ˢ B).filter (fun t => (t.1+t.2) % m=n)).card → 0 < W A B n := by
  intro W m n A B hn hA hB h
  show 0 < ((A ×ˢ B).filter (fun t => t.1+t.2=n)).card
  by_contra h0
  have h0' : ((A ×ˢ B).filter (fun t => t.1+t.2=n)).card = 0 := by omega
  rw [Finset.card_eq_zero] at h0'
  have hsub : (A ×ˢ B).filter (fun t => (t.1+t.2) % m=n) ⊆
      (A.filter (fun a => n < a)).image (fun a => (a, n + m - a)) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_product] at ht
    obtain ⟨⟨ha, hb⟩, he⟩ := ht
    have ha' := hA _ ha
    have hb' := hB _ hb
    have hne : ¬ t.1 + t.2 = n := by
      intro hh
      have : t ∈ (A ×ˢ B).filter (fun t => t.1+t.2=n) := by
        simp only [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨ha, hb⟩, hh⟩
      rw [h0'] at this; simp at this
    have : t.1 + t.2 = n + m := by
      have := Nat.mod_add_div (t.1+t.2) m
      have hq : (t.1+t.2)/m < 2 := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
      interval_cases hq' : (t.1+t.2)/m <;> omega
    simp only [Finset.mem_image, Finset.mem_filter]
    refine ⟨t.1, ⟨ha, by omega⟩, ?_⟩
    ext <;> simp <;> omega
  have hsub2 : (A ×ˢ B).filter (fun t => (t.1+t.2) % m=n) ⊆
      (B.filter (fun b => n < b)).image (fun b => (n + m - b, b)) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_product] at ht
    obtain ⟨⟨ha, hb⟩, he⟩ := ht
    have ha' := hA _ ha
    have hb' := hB _ hb
    have hne : ¬ t.1 + t.2 = n := by
      intro hh
      have : t ∈ (A ×ˢ B).filter (fun t => t.1+t.2=n) := by
        simp only [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨ha, hb⟩, hh⟩
      rw [h0'] at this; simp at this
    have : t.1 + t.2 = n + m := by
      have := Nat.mod_add_div (t.1+t.2) m
      have hq : (t.1+t.2)/m < 2 := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
      interval_cases hq' : (t.1+t.2)/m <;> omega
    simp only [Finset.mem_image, Finset.mem_filter]
    refine ⟨t.2, ⟨hb, by omega⟩, ?_⟩
    ext <;> simp <;> omega
  have c1 := (Finset.card_le_card hsub).trans Finset.card_image_le
  have c2 := (Finset.card_le_card hsub2).trans Finset.card_image_le
  omega
