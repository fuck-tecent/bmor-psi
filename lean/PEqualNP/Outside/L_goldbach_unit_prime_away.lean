import Mathlib

theorem PEqualNP.Outside.L_goldbach_unit_prime_away :
    let U := fun q n : ℕ => (Finset.range q).filter (fun a => Nat.Coprime a q ∧ Nat.Coprime (n+q-a) q); ∀ p n, Nat.Prime p → ¬ p ∣ n → (U p n).card=p-2 := by
  dsimp only
  intro p n hp hpn
  have hzero : 0 ∈ Finset.range p := Finset.mem_range.mpr hp.pos
  have hres : n % p ∈ (Finset.range p).erase 0 :=
    Finset.mem_erase.mpr ⟨fun h => hpn (Nat.dvd_of_mod_eq_zero h),
      Finset.mem_range.mpr (Nat.mod_lt n hp.pos)⟩
  have hcop (k : ℕ) : Nat.Coprime k p ↔ ¬ p ∣ k :=
    Nat.coprime_comm.trans hp.coprime_iff_not_dvd
  have hset : (Finset.range p).filter (fun a => Nat.Coprime a p ∧ Nat.Coprime (n+p-a) p) =
      ((Finset.range p).erase 0).erase (n % p) := by
    ext a
    by_cases ha : a < p
    · have hfirst : p ∣ a ↔ a = 0 := by
        rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt ha]
      have hsecond : p ∣ n + p - a ↔ a = n % p := by
        rw [← Nat.modEq_iff_dvd' (show a ≤ n + p by omega)]
        simp [Nat.ModEq, Nat.mod_eq_of_lt ha]
      simp [Finset.mem_erase, ha, hcop, hfirst, hsecond, and_comm]
    · simp [Finset.mem_erase, ha]
  rw [hset, Finset.card_erase_of_mem hres, Finset.card_erase_of_mem hzero, Finset.card_range]
  omega
