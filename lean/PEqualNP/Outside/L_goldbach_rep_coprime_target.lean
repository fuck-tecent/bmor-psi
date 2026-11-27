import Mathlib

theorem PEqualNP.Outside.L_goldbach_rep_coprime_target :
    ∀ n : ℕ, let reps := fun n : ℕ => (Finset.range (n+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n-p)); ∀ p ∈ reps n, ¬ Nat.Coprime p n → n=2*p := by
  intro n
  dsimp only
  intro p hmem hnoncoprime
  obtain ⟨hrange, hp, hq⟩ := Finset.mem_filter.mp hmem
  have hle : p ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hrange)
  have hdvd : p ∣ n := hp.dvd_iff_not_coprime.mpr hnoncoprime
  have heq : p = n - p :=
    (Nat.prime_dvd_prime_iff_eq hp hq).mp (Nat.dvd_sub hdvd (dvd_refl p))
  omega
