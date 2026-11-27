import Mathlib

namespace Conjectures.QuadraticPrimes.SemiprimeGapConicBijection_aux

/-- An odd prime dividing a square plus one is `1 mod 4`. -/
private lemma mod_four_eq_one_of_prime_dvd_sq_add_one {r m : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hd : r ∣ m ^ 2 + 1) : r % 4 = 1 := by
  have _ : Fact r.Prime := Fact.mk hr
  have hz : ((m : ZMod r)) ^ 2 = -1 := by
    have h1 : ((m ^ 2 + 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    push_cast at h1
    linear_combination h1
  have h3 : r % 4 ≠ 3 := ZMod.mod_four_ne_three_of_sq_eq_neg_one hz
  obtain ⟨k, hk⟩ := hr.odd_of_ne_two hr2
  omega

end Conjectures.QuadraticPrimes.SemiprimeGapConicBijection_aux

theorem Conjectures.QuadraticPrimes.SemiprimeGapConicBijection :
    ∀ n p q : ℕ, Even n → p.Prime → q.Prime → p < q → n^2+1 = p*q →
      ∃ h v : ℕ, Even h ∧ Odd v ∧ v*(2*n+v)=h^2+1 ∧ p+h=n+v ∧ q=n+v+h ∧ 2*n ≤ h^2 := by
  intro n p q hn hp hq hpq hnpq
  have hneven : n % 2 = 0 := by
    obtain ⟨k, hk⟩ := hn
    omega
  have hodd : (n ^ 2 + 1) % 2 = 1 := by
    obtain ⟨k, hk⟩ := hn
    have hk2 : n ^ 2 + 1 = 2 * (2 * k ^ 2) + 1 := by rw [hk]; ring
    omega
  have hp2 : p ≠ 2 := by
    intro h
    have hd : 2 ∣ n ^ 2 + 1 := by
      rw [hnpq, h]
      exact dvd_mul_right 2 q
    omega
  have hq2 : q ≠ 2 := by
    intro h
    have hd : 2 ∣ n ^ 2 + 1 := by
      rw [hnpq, h]
      exact dvd_mul_left 2 p
    omega
  have hpd : p ∣ n ^ 2 + 1 := by rw [hnpq]; exact dvd_mul_right p q
  have hqd : q ∣ n ^ 2 + 1 := by rw [hnpq]; exact dvd_mul_left q p
  have hp4 : p % 4 = 1 :=
    Conjectures.QuadraticPrimes.SemiprimeGapConicBijection_aux.mod_four_eq_one_of_prime_dvd_sq_add_one
      hp hp2 hpd
  have hq4 : q % 4 = 1 :=
    Conjectures.QuadraticPrimes.SemiprimeGapConicBijection_aux.mod_four_eq_one_of_prime_dvd_sq_add_one
      hq hq2 hqd
  -- the midpoint lies strictly above `n`, so the excess is a natural number
  have hsum : 2 * n + 2 ≤ p + q := by
    have hgt : 2 * n < p + q := by
      have hval : (p : ℤ) * (q : ℤ) = (n : ℤ) ^ 2 + 1 := by exact_mod_cast hnpq.symm
      have hz : ((p : ℤ) + (q : ℤ)) ^ 2 = 4 * ((p : ℤ) * (q : ℤ)) + ((q : ℤ) - (p : ℤ)) ^ 2 := by
        ring
      have hpos : (2 * (n : ℤ)) ^ 2 < ((p : ℤ) + (q : ℤ)) ^ 2 := by
        rw [hz, hval]
        nlinarith [sq_nonneg ((q : ℤ) - (p : ℤ))]
      by_contra hle
      have h3 : p + q ≤ 2 * n := by omega
      have h4 : (p : ℤ) + (q : ℤ) ≤ 2 * (n : ℤ) := by exact_mod_cast h3
      have key : (2 * (n : ℤ)) ^ 2 - ((p : ℤ) + (q : ℤ)) ^ 2 =
          ((2 * (n : ℤ)) - ((p : ℤ) + (q : ℤ))) * ((2 * (n : ℤ)) + ((p : ℤ) + (q : ℤ))) := by
        ring
      have nn1 : 0 ≤ (2 * (n : ℤ)) - ((p : ℤ) + (q : ℤ)) := by linarith
      have nn2 : 0 ≤ (2 * (n : ℤ)) + ((p : ℤ) + (q : ℤ)) := by positivity
      have h5 : 0 ≤ (2 * (n : ℤ)) ^ 2 - ((p : ℤ) + (q : ℤ)) ^ 2 := by
        rw [key]; exact mul_nonneg nn1 nn2
      linarith
    have hpar : (p + q) % 2 = 0 := by omega
    omega
  refine ⟨(q - p) / 2, (p + q) / 2 - n, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `h` is even
    have h1 : 2 * ((q - p) / 2) = q - p := by omega
    have h2 : (q - p) % 4 = 0 := by omega
    refine ⟨(q - p) / 4, ?_⟩
    omega
  · -- `v` is odd
    have h1 : (p + q) % 4 = 2 := by omega
    refine ⟨((p + q) / 2 - n - 1) / 2, ?_⟩
    omega
  · -- the conic equation
    have hhh : 2 * ((q - p) / 2) = q - p := by omega
    have hvv : 2 * ((p + q) / 2 - n) = p + q - 2 * n := by omega
    have hpz : (p : ℤ) = (n : ℤ) + ((p + q) / 2 - n : ℕ) - ((q - p) / 2 : ℕ) := by omega
    have hqz : (q : ℤ) = (n : ℤ) + ((p + q) / 2 - n : ℕ) + ((q - p) / 2 : ℕ) := by omega
    have hconic : (((p + q) / 2 - n : ℕ) : ℤ) * (2 * (n : ℤ) + ((p + q) / 2 - n : ℕ)) =
        ((q - p) / 2 : ℕ) ^ 2 + 1 := by
      have hmul : (p : ℤ) * (q : ℤ) = ((n : ℤ) + ((p + q) / 2 - n : ℕ)) ^ 2 -
          ((q - p) / 2 : ℕ) ^ 2 := by
        rw [hpz, hqz]
        ring
      have hval : (p : ℤ) * (q : ℤ) = (n : ℤ) ^ 2 + 1 := by
        exact_mod_cast hnpq.symm
      linarith
    exact_mod_cast hconic
  · -- `p + h = n + v`
    have hhh : 2 * ((q - p) / 2) = q - p := by omega
    have hvv : 2 * ((p + q) / 2 - n) = p + q - 2 * n := by omega
    omega
  · -- `q = n + v + h`
    have hhh : 2 * ((q - p) / 2) = q - p := by omega
    have hvv : 2 * ((p + q) / 2 - n) = p + q - 2 * n := by omega
    omega
  · -- `2 * n ≤ h ^ 2`
    have hvpos : 1 ≤ (p + q) / 2 - n := by omega
    have hconic : ((p + q) / 2 - n) * (2 * n + ((p + q) / 2 - n)) = ((q - p) / 2) ^ 2 + 1 := by
      have hhh : 2 * ((q - p) / 2) = q - p := by omega
      have hvv : 2 * ((p + q) / 2 - n) = p + q - 2 * n := by omega
      have hpz : (p : ℤ) = (n : ℤ) + ((p + q) / 2 - n : ℕ) - ((q - p) / 2 : ℕ) := by omega
      have hqz : (q : ℤ) = (n : ℤ) + ((p + q) / 2 - n : ℕ) + ((q - p) / 2 : ℕ) := by omega
      have hmul : (p : ℤ) * (q : ℤ) = ((n : ℤ) + ((p + q) / 2 - n : ℕ)) ^ 2 -
          ((q - p) / 2 : ℕ) ^ 2 := by
        rw [hpz, hqz]
        ring
      have hval : (p : ℤ) * (q : ℤ) = (n : ℤ) ^ 2 + 1 := by
        exact_mod_cast hnpq.symm
      have hc : (((p + q) / 2 - n : ℕ) : ℤ) * (2 * (n : ℤ) + ((p + q) / 2 - n : ℕ)) =
          ((q - p) / 2 : ℕ) ^ 2 + 1 := by linarith
      exact_mod_cast hc
    have hlow : 2 * n + 1 ≤ ((p + q) / 2 - n) * (2 * n + ((p + q) / 2 - n)) := by
      have := Nat.mul_le_mul hvpos (le_refl (2 * n + ((p + q) / 2 - n)))
      omega
    omega
