import Mathlib

/-- For every bound `B` there is an `n > B` such that `n ^ 2 + 1` has a prime divisor `p` with
`n < p`.

Take a prime `q ≡ 1 [MOD 4]` above `B ^ 2 + 2` (`Nat.exists_prime_gt_modEq_one`, the cyclotomic
argument) and a square root `x` of `-1` in `ZMod q`. Its representative `n = x.val` obeys
`n < q` and `q ∣ n ^ 2 + 1`. Should `n ≤ B` hold then `n ^ 2 + 1` is a positive multiple of `q`
bounded by `B ^ 2 + 1 < q`, impossible; hence `B < n < p`. -/
theorem Conjectures.QuadraticPrimes.LpfLinear :
    ∀ B : ℕ, ∃ n p : ℕ, B < n ∧ Nat.Prime p ∧ p ∣ n ^ 2 + 1 ∧ n ^ 1 < p ^ 1 := by
  intro B
  obtain ⟨q, hq, hqB, hq1⟩ :=
    Nat.exists_prime_gt_modEq_one (B ^ 2 + 2) (by decide : (4 : ℕ) ≠ 0)
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨Nat.Prime.ne_zero hq⟩
  obtain ⟨x, hx⟩ : IsSquare (-1 : ZMod q) :=
    ZMod.exists_sq_eq_neg_one_iff.2 (by
      have hq4 : q % 4 = 1 := by simpa [Nat.ModEq] using hq1
      omega)
  have hx2 : x ^ 2 = -1 := (pow_two x).trans hx.symm
  set n : ℕ := x.val with hn
  have hnq : n < q := ZMod.val_lt x
  have hdvd : q ∣ n ^ 2 + 1 := by
    have hxv : (n : ZMod q) = x := by rw [hn]; exact ZMod.natCast_zmod_val x
    have h0 : ((n ^ 2 + 1 : ℕ) : ZMod q) = 0 := by
      rw [show ((n ^ 2 + 1 : ℕ) : ZMod q) = (n : ZMod q) ^ 2 + 1 by push_cast; rfl, hxv, hx2]
      abel
    exact (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) q).mp h0
  have hnB : B < n := by
    by_contra hle
    have hn1 : 0 < n := by
      by_contra hz
      have : n = 0 := Nat.eq_zero_of_le_zero (by omega : n ≤ 0)
      rw [this, pow_two, zero_mul, zero_add] at hdvd
      exact absurd hdvd (Nat.Prime.not_dvd_one hq)
    have hle2 : q ≤ n ^ 2 + 1 := Nat.le_of_dvd (by positivity) hdvd
    have hle3 : n ^ 2 + 1 ≤ B ^ 2 + 1 :=
      Nat.add_le_add_right (pow_le_pow_left' (by omega : n ≤ B) 2) 1
    omega
  exact ⟨n, q, hnB, hq, hdvd, by simpa [pow_one] using hnq⟩
