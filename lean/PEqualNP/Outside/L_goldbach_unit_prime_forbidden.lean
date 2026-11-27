import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs

theorem PEqualNP.Outside.L_goldbach_unit_prime_forbidden :
    let U := fun q n : ℕ =>
      (Finset.range q).filter (fun a => Nat.Coprime a q ∧ Nat.Coprime (n + q - a) q)
    ∀ p n a, Nat.Prime p → a < p → (a ∈ U p n ↔ a ≠ 0 ∧ a ≠ n % p) := by
  dsimp only
  intro p n a hp ha
  have hfirst : p ∣ a ↔ a = 0 := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt ha]
  have hsecond : p ∣ n + p - a ↔ a = n % p := by
    rw [← Nat.modEq_iff_dvd' (show a ≤ n + p by omega)]
    simp [Nat.ModEq, Nat.mod_eq_of_lt ha]
  simp only [Finset.mem_filter, Finset.mem_range, ha, true_and]
  have hcop (k : ℕ) : Nat.Coprime k p ↔ ¬ p ∣ k :=
    Nat.coprime_comm.trans hp.coprime_iff_not_dvd
  rw [hcop, hcop, hfirst, hsecond]
