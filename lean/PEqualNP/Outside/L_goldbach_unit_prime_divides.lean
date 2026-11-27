import Mathlib

theorem PEqualNP.Outside.L_goldbach_unit_prime_divides :
    let U := fun q n : ℕ => (Finset.range q).filter
      (fun a => Nat.Coprime a q ∧ Nat.Coprime (n + q - a) q)
    ∀ p n, Nat.Prime p → p ∣ n → (U p n).card = p - 1 := by
  dsimp only
  intro p n hp hpn
  rw [← Nat.totient_prime hp, Nat.totient_eq_card_coprime]
  congr 1
  apply Finset.filter_congr
  intro a ha
  constructor
  · exact fun h => h.1.symm
  · intro h
    refine ⟨h.symm, (hp.coprime_iff_not_dvd.mpr ?_).symm⟩
    intro hbad
    have ha' : a < p := Finset.mem_range.mp ha
    have hd := Nat.dvd_sub (dvd_add hpn (dvd_refl p)) hbad
    have hdiff : n + p - (n + p - a) = a := by omega
    rw [hdiff] at hd
    exact (hp.coprime_iff_not_dvd.mp h) hd
