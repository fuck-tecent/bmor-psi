import Mathlib

theorem PEqualNP.Outside.L_goldbach_theta_coset_factor :
    ∀ (p n : ℕ), p.Prime → ((Finset.range p).filter (fun k => k % p≠0 ∧ k % p≠n % p)).card = if p∣n then p-1 else p-2 := by
  intro p n hp
  have hz : 0 ∈ Finset.range p := Finset.mem_range.mpr hp.pos
  have hr : n % p ∈ Finset.range p := Finset.mem_range.mpr (Nat.mod_lt n hp.pos)
  by_cases hd : p ∣ n
  · have hmod : n % p = 0 := Nat.mod_eq_zero_of_dvd hd
    have he : (Finset.range p).filter (fun k => k % p ≠ 0 ∧ k % p ≠ n % p) =
        (Finset.range p).erase 0 := by
      ext k
      rw [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hk, h, _⟩
        exact ⟨by simpa only [Nat.mod_eq_of_lt (Finset.mem_range.mp hk)] using h, hk⟩
      · rintro ⟨h, hk⟩
        exact ⟨hk, by simpa only [hmod, Nat.mod_eq_of_lt (Finset.mem_range.mp hk)] using And.intro h h⟩
    rw [if_pos hd, he, Finset.card_erase_of_mem hz, Finset.card_range]
  · have hmod : n % p ≠ 0 := fun h => hd (Nat.dvd_of_mod_eq_zero h)
    have hr' : n % p ∈ (Finset.range p).erase 0 := Finset.mem_erase.mpr ⟨hmod, hr⟩
    have he : (Finset.range p).filter (fun k => k % p ≠ 0 ∧ k % p ≠ n % p) =
        ((Finset.range p).erase 0).erase (n % p) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hk, h0, hn⟩
        rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hk)] at h0 hn
        exact ⟨hn, h0, hk⟩
      · rintro ⟨hn, h0, hk⟩
        rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hk)]
        exact ⟨hk, h0, hn⟩
    rw [if_neg hd, he, Finset.card_erase_of_mem hr', Finset.card_erase_of_mem hz,
      Finset.card_range] <;> omega
