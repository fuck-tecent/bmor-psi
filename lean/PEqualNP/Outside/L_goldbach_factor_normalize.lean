import Mathlib

/-- Local factor normalisation for the odd primes: the number of admissible residues modulo `p`
divided by the density of the independent model reproduces the singular-series factor. -/
theorem PEqualNP.Outside.L_goldbach_factor_normalize :
    let fac := fun p n : ℕ => if p ∣ n then (p:ℝ)/((p:ℝ)-1) else 1-1/((p:ℝ)-1)^2
    let U := fun q n : ℕ => (Finset.range q).filter (fun a => Nat.Coprime a q ∧ Nat.Coprime (n+q-a) q)
    ∀ p n, Nat.Prime p → 2<p → fac p n = (p:ℝ)*((U p n).card:ℝ)/((p:ℝ)-1)^2 := by
  dsimp only
  intro p n hp hp2
  have hp3 : 3 ≤ p := hp2
  have hmod : n % p < p := Nat.mod_lt n hp.pos
  -- membership: `a` is admissible iff `a` is nonzero and not congruent to `n` modulo `p`
  have hmem : ∀ a, a < p → (Nat.Coprime a p ∧ Nat.Coprime (n + p - a) p ↔ a ≠ 0 ∧ a ≠ n % p) := by
    intro a ha
    have h1 : Nat.Coprime a p ↔ a ≠ 0 := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      constructor
      · intro h h0
        exact h (by rw [h0]; exact dvd_zero p)
      · intro h hd
        exact h (Nat.eq_zero_of_dvd_of_lt hd ha)
    have h2 : Nat.Coprime (n + p - a) p ↔ a ≠ n % p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd, Nat.dvd_iff_mod_eq_zero]
      have hsub : n + p - a = n + (p - a) := Nat.add_sub_assoc ha.le n
      rw [hsub, Nat.add_mod]
      by_cases ha0 : a = 0
      · subst ha0
        simp [eq_comm]
      · have hpa_lt : p - a < p := by omega
        have hpa_pos : 0 < p - a := by omega
        rw [Nat.mod_eq_of_lt hpa_lt]
        have key : (n % p + (p - a)) % p = 0 ↔ n % p + (p - a) = p := by
          constructor
          · intro h0
            rcases lt_or_ge (n % p + (p - a)) p with hlt | hge
            · rw [Nat.mod_eq_of_lt hlt] at h0
              omega
            · have hstep : (n % p + (p - a)) % p = (n % p + (p - a)) - p := by
                rw [Nat.mod_eq_sub_mod hge]
                exact Nat.mod_eq_of_lt (by omega)
              rw [hstep] at h0
              omega
          · intro h
            rw [h]
            exact Nat.mod_self p
        constructor
        · intro h hc
          have hx : n % p + (p - a) = p := by omega
          exact h (key.mpr hx)
        · intro h hc
          have hx : n % p + (p - a) = p := key.mp hc
          exact h (by omega)
    rw [h1, h2]

  have hUset : (Finset.range p).filter (fun a => Nat.Coprime a p ∧ Nat.Coprime (n + p - a) p)
      = (Finset.range p).filter (fun a => a ≠ 0 ∧ a ≠ n % p) := by
    refine Finset.filter_congr (fun a ha => ?_)
    exact hmem a (Finset.mem_range.mp ha)

  have hcard : ((Finset.range p).filter (fun a => Nat.Coprime a p ∧ Nat.Coprime (n + p - a) p)).card
      = if p ∣ n then p - 1 else p - 2 := by
    rw [hUset]
    by_cases hd : p ∣ n
    · rw [if_pos hd]
      have hz : n % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
      rw [hz]
      have hsim : (Finset.range p).filter (fun a => a ≠ 0 ∧ a ≠ 0) = (Finset.range p).erase 0 := by
        ext a
        simp [Finset.mem_erase, and_comm]
      rw [hsim, Finset.card_erase_of_mem (Finset.mem_range.mpr hp.pos), Finset.card_range]
    · rw [if_neg hd]
      have hne0 : n % p ≠ 0 := fun h0 => hd (Nat.dvd_iff_mod_eq_zero.mpr h0)
      have hmem0 : n % p ∈ Finset.range p := Finset.mem_range.mpr hmod
      have hsim : (Finset.range p).filter (fun a => a ≠ 0 ∧ a ≠ n % p) = ((Finset.range p).erase 0).erase (n % p) := by
        rw [← Finset.filter_filter, Finset.filter_ne', Finset.filter_ne']
      have h0mem : (0 : ℕ) ∈ Finset.range p := Finset.mem_range.mpr hp.pos
      have hcmem : n % p ∈ (Finset.range p).erase 0 := Finset.mem_erase.mpr ⟨hne0, hmem0⟩
      rw [hsim, Finset.card_erase_of_mem hcmem, Finset.card_erase_of_mem h0mem, Finset.card_range]
      omega

  rw [hcard]
  by_cases hd : p ∣ n
  · simp only [if_pos hd]
    have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have hne : (p : ℝ) - 1 ≠ 0 := by linarith
    have hc1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
    rw [hc1]
    field_simp
  · simp only [if_neg hd]
    have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have hne : (p : ℝ) - 1 ≠ 0 := by linarith
    have hc2 : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ p), Nat.cast_ofNat]
    rw [hc2]
    field_simp; ring
