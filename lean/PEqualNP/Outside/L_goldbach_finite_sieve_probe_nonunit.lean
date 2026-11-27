import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.GCD.Prime

theorem PEqualNP.Outside.L_goldbach_finite_sieve_probe_nonunit :
    ∀ n d e p : ℕ, Nat.Prime p → p % d = n % d → p % e = 1 % e → p ∣ Nat.lcm d e → p ∣ d ∧ p ∣ n := by
  intro n d e p hp hpd hpe hl
  have hd : p ∣ d := by
    rcases hp.dvd_lcm.mp hl with hd | he
    · exact hd
    · have hc := Nat.ModEq.of_dvd he hpe
      change p % p = 1 % p at hc
      rw [Nat.mod_self, Nat.mod_eq_of_lt hp.one_lt] at hc
      omega
  have hc := Nat.ModEq.of_dvd hd hpd
  change p % p = n % p at hc
  rw [Nat.mod_self] at hc
  exact ⟨hd, Nat.dvd_of_mod_eq_zero hc.symm⟩
