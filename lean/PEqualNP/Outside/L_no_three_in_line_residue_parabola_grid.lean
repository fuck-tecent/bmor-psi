import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_residue_parabola_grid :
    let valid := fun (n : ℕ) (S : Finset (ℕ × ℕ)) => (∀ z ∈ S, z.1 < n ∧ z.2 < n) ∧ (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c → ((b.1 : ℤ) - (a.1 : ℤ)) * ((c.2 : ℤ) - (a.2 : ℤ)) ≠ ((b.2 : ℤ) - (a.2 : ℤ)) * ((c.1 : ℤ) - (a.1 : ℤ))); ∀ p : ℕ, Nat.Prime p → let S := (Finset.range p).image (fun x => (x, x^2 % p)); valid p S ∧ S.card = p := by
  dsimp only
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z hz
    simp only [Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨hx, Nat.mod_lt _ hp.pos⟩
  · have key : ∀ xa xb xc : ℕ, xa < p → xb < p → xc < p → xa ≠ xb → xa ≠ xc → xb ≠ xc →
        ((xb : ℤ) - (xa : ℤ)) * (((xc ^ 2 % p : ℕ) : ℤ) - ((xa ^ 2 % p : ℕ) : ℤ)) ≠
        (((xb ^ 2 % p : ℕ) : ℤ) - ((xa ^ 2 % p : ℕ) : ℤ)) * ((xc : ℤ) - (xa : ℤ)) := by
      intro xa xb xc hxa hxb hxc hxab hxac hxbc hD
      have hD' := congrArg (fun t : ℤ => (t : ZMod p)) hD
      push_cast at hD'
      have hzero : ((xb : ZMod p) - (xa : ZMod p)) * ((xc : ZMod p) ^ 2 - (xa : ZMod p) ^ 2) -
          ((xb : ZMod p) ^ 2 - (xa : ZMod p) ^ 2) * ((xc : ZMod p) - (xa : ZMod p)) = 0 := by
        rw [hD']
        ring
      have hfac : ((xb : ZMod p) - (xa : ZMod p)) * ((xc : ZMod p) - (xa : ZMod p)) *
          ((xc : ZMod p) - (xb : ZMod p)) = 0 := by
        rw [← hzero]
        ring
      have hne : ∀ u v : ℕ, u < p → v < p → u ≠ v → (u : ZMod p) - (v : ZMod p) ≠ 0 := by
        intro u v hu hv huv h
        have hc : (u : ZMod p) = (v : ZMod p) := sub_eq_zero.mp h
        have hm : u ≡ v [MOD p] := (ZMod.natCast_eq_natCast_iff u v p).mp hc
        have hm' : u % p = v % p := hm
        rw [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] at hm'
        exact huv hm'
      exact (mul_ne_zero (mul_ne_zero (hne xb xa hxb hxa hxab.symm) (hne xc xa hxc hxa hxac.symm))
        (hne xc xb hxc hxb hxbc.symm)) hfac
    intro a ha b hb c hc hab hac hbc
    simp only [Finset.mem_image, Finset.mem_range] at ha hb hc
    obtain ⟨xa, hxa, rfl⟩ := ha
    obtain ⟨xb, hxb, rfl⟩ := hb
    obtain ⟨xc, hxc, rfl⟩ := hc
    exact key xa xb xc hxa hxb hxc
      (by intro h; exact hab (by rw [h]))
      (by intro h; exact hac (by rw [h]))
      (by intro h; exact hbc (by rw [h]))
  · have hinj : Function.Injective (fun x : ℕ => (x, x ^ 2 % p)) := by
      intro x y hxy
      simpa using congrArg Prod.fst hxy
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
