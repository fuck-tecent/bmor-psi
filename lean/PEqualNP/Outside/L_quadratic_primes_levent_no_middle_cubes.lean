import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_no_middle_cubes :
    let block := fun x : ℕ => Finset.Ioc x (2*x); ∀ x n p : ℕ, 5≤x → n ∈ block x → x<p → ¬ p^3 ∣ n^2+1 := by
  intro block x n p hx hn hp
  have hn_upper : n ≤ 2 * x := (Finset.mem_Ioc.mp hn).2
  have hcube : (x + 1) ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp 3
  have hsquare : n ^ 2 ≤ (2 * x) ^ 2 := Nat.pow_le_pow_left hn_upper 2
  have hlarge : (2 * x) ^ 2 + 1 < (x + 1) ^ 3 := by
    have hxsq : 5 * x ≤ x ^ 2 := by nlinarith
    have hxcube : 5 * x ^ 2 ≤ x ^ 3 := by nlinarith [sq_nonneg (x : ℤ)]
    nlinarith
  intro hdvd
  have hle : p ^ 3 ≤ n ^ 2 + 1 := Nat.le_of_dvd (by positivity) hdvd
  omega
