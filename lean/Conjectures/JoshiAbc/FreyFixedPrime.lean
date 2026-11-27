import Mathlib

namespace Conjectures.JoshiAbc

theorem FreyFixedPrime :
    ∀ p N : ℕ, p.Prime → Odd p → 0 < N →
      multiplicity p (16 * (p ^ N) ^ 2 * (p ^ N + 1) ^ 2) = 2 * N := by
  intro p N hp hodd hN
  have hfactor :
      16 * (p ^ N) ^ 2 * (p ^ N + 1) ^ 2 =
        p ^ (2 * N) * (16 * (p ^ N + 1) ^ 2) := by
    rw [← pow_mul]
    ring
  apply multiplicity_eq_of_dvd_of_not_dvd (k := 2 * N)
  · rw [hfactor]
    exact Dvd.intro _ rfl
  · intro hdiv
    have hmuldiv :
        p ^ (2 * N) * p ∣ p ^ (2 * N) * (16 * (p ^ N + 1) ^ 2) := by
      rw [← pow_succ, ← hfactor]
      exact hdiv
    have hpY : p ∣ 16 * (p ^ N + 1) ^ 2 :=
      Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos _) hmuldiv
    rcases hp.dvd_mul.1 hpY with hp16 | hpsquare
    · have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow (n := 4) (by simpa using hp16)
      have hpeq : p = 2 :=
        (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hp2
      subst p
      exact hodd.not_two_dvd_nat (dvd_refl 2)
    · have hpsum : p ∣ p ^ N + 1 := hp.dvd_of_dvd_pow hpsquare
      have hppow : p ∣ p ^ N := dvd_pow_self p hN.ne'
      exact hp.not_dvd_one ((Nat.dvd_add_right hppow).1 hpsum)

end Conjectures.JoshiAbc
