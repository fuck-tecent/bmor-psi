import Mathlib

theorem PEqualNP.Outside.L_goldbach_unit_nonempty_even :
    let U := fun q n : ℕ => (Finset.range q).filter (fun a => Nat.Coprime a q ∧ Nat.Coprime (n+q-a) q); ∀ q n, 0<q → Even n → (U q n).Nonempty := by
  intro U q n hq hn
  classical
  let r (p : ℕ) := if n % p = 1 then 2 else 1
  have local_bounds (p : ℕ) (hp : Nat.Prime p) :
      0 < r p ∧ r p < p ∧ r p ≠ n % p := by
    have htwo := hp.two_le
    dsimp [r]
    split_ifs with h
    · have hne : p ≠ 2 := by
        rintro rfl
        obtain ⟨k, hk⟩ := hn
        omega
      omega
    · omega
  have hprime (p : ℕ) (hp : p ∈ q.primeFactors) : Nat.Prime p :=
    (Nat.mem_primeFactors.mp hp).1
  let x := Nat.chineseRemainderOfFinset r (fun p : ℕ => p) q.primeFactors
    (fun p hp => (hprime p hp).ne_zero)
    (by
      intro p hp s hs hne
      exact (Nat.coprime_primes (hprime p hp) (hprime s hs)).mpr hne)
  let a := x.val % q
  have ha : a < q := Nat.mod_lt _ hq
  have hres (p : ℕ) (hp : Nat.Prime p) (hd : p ∣ q) : a % p = r p := by
    have hm := x.property p (Nat.mem_primeFactors.mpr ⟨hp, hd, by omega⟩)
    change x.val % p = r p % p at hm
    rw [Nat.mod_eq_of_lt (local_bounds p hp).2.1] at hm
    simpa [a, Nat.mod_mod_of_dvd _ hd] using hm
  refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha, ?_, ?_⟩⟩
  · by_contra h
    obtain ⟨p, hp, hd, hq'⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    have := hres p hp hq'
    have := Nat.mod_eq_zero_of_dvd hd
    have := (local_bounds p hp).1
    omega
  · by_contra h
    obtain ⟨p, hp, hd, hq'⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    have heq : (n + q - a) + a = n + q := by omega
    have hm := congrArg (fun t => t % p) heq
    change ((n + q - a) + a) % p = (n + q) % p at hm
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, zero_add, Nat.mod_mod,
      Nat.add_mod n q, Nat.mod_eq_zero_of_dvd hq', add_zero, Nat.mod_mod] at hm
    exact (local_bounds p hp).2.2 ((hres p hp hq').symm.trans hm)
