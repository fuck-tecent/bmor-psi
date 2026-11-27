import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

theorem PEqualNP.Outside.L_quadratic_primes_prime_divisors_mod_four :
    ∀ (n p : ℕ), Nat.Prime p → p ∣ n ^ 2 + 1 → p = 2 ∨ p % 4 = 1 := by
  intro n p hp hdvd
  by_cases hp2 : p = 2
  · exact Or.inl hp2
  · right
    have hodd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · exact absurd h hp2
      · exact h
    have hzero : ((n ^ 2 + 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) p).mpr hdvd
    have hzero' : (n : ZMod p) ^ 2 + 1 = 0 := by simpa using hzero
    have hsq : (n : ZMod p) ^ 2 = -((1 : ZMod p) ^ 2) := by
      calc (n : ZMod p) ^ 2 = (n : ZMod p) ^ 2 + 1 - 1 := by ring
        _ = -((1 : ZMod p) ^ 2) := by rw [hzero']; ring
    have hne3 : p % 4 ≠ 3 := by
      intro h3
      haveI : Fact p.Prime := ⟨hp⟩
      exact (ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (p := p)
        (x := (n : ZMod p)) (y := 1) one_ne_zero hsq) h3
    have h4lt : p % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have hpar : (p % 4) % 2 = 1 := by
      rw [Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 4)]
      exact hodd
    omega
