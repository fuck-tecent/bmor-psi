import Mathlib

theorem PEqualNP.Outside.L_goldbach_sieve_residue_dimension :
    ∀ n p : ℕ, p.Prime → ((Finset.range p).filter (fun k => k % p=0 ∨ k % p=n % p)).card = if p∣n then 1 else 2 := by
  intro n p hp
  have hres : n % p < p := Nat.mod_lt n hp.pos
  have hclasses : (Finset.range p).filter (fun k => k % p = 0 ∨ k % p = n % p) =
      ({0, n % p} : Finset ℕ) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, h⟩
      simpa only [Nat.mod_eq_of_lt hk] using h
    · rintro (rfl | rfl)
      · exact ⟨hp.pos, Or.inl (Nat.zero_mod p)⟩
      · exact ⟨hres, Or.inr (Nat.mod_eq_of_lt hres)⟩
  rw [hclasses]
  by_cases hdiv : p ∣ n
  · simp [hdiv, Nat.mod_eq_zero_of_dvd hdiv]
  · have hne : 0 ≠ n % p := fun h => hdiv (Nat.dvd_of_mod_eq_zero h.symm)
    simp [hdiv, hne]
