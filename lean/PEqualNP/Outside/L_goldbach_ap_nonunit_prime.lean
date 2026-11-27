import Mathlib

theorem PEqualNP.Outside.L_goldbach_ap_nonunit_prime :
    ∀ q k : ℕ, Nat.Prime k → ¬ Nat.Coprime (k % q) q → k ∣ q := by
  intro q k hk h
  apply (hk.dvd_iff_not_coprime).2
  intro hc
  apply h
  change Nat.gcd (k % q) q = 1
  change Nat.gcd k q = 1 at hc
  calc
    Nat.gcd (k % q) q = Nat.gcd q k := (Nat.gcd_rec q k).symm
    _ = Nat.gcd k q := Nat.gcd_comm q k
    _ = 1 := hc
