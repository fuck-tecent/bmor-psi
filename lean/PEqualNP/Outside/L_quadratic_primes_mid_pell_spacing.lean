import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_mid_pell_spacing :
    ∀ a b u v:ℕ,0<a → a<b → a^2+1=2*u^2 → b^2+1=2*v^2 → 2*a<b := by
  intro a b u v ha hab hA hB
  have hAZ : (a : ℤ) ^ 2 + 1 = 2 * (u : ℤ) ^ 2 := by exact_mod_cast hA
  have hBZ : (b : ℤ) ^ 2 + 1 = 2 * (v : ℤ) ^ 2 := by exact_mod_cast hB
  have ha0 : (0 : ℤ) ≤ a := Nat.cast_nonneg a
  have hb0 : (0 : ℤ) ≤ b := Nat.cast_nonneg b
  have hu0 : (0 : ℤ) ≤ u := Nat.cast_nonneg u
  have hv0 : (0 : ℤ) ≤ v := Nat.cast_nonneg v
  have htwo : (0 : ℤ) ≤ 2 := Nat.cast_nonneg 2
  have habZ : (a : ℤ) < b := by exact_mod_cast hab
  have h2uZ : (a : ℤ) < 2 * u := by
    have heq : (2 * (u : ℤ)) ^ 2 = 2 * ((a : ℤ) ^ 2 + 1) := by
      calc
        (2 * (u : ℤ)) ^ 2 = 2 * (2 * (u : ℤ) ^ 2) := by ring
        _ = 2 * ((a : ℤ) ^ 2 + 1) := by rw [← hAZ]
    have hpos : (0 : ℤ) < (a : ℤ) ^ 2 + 2 := by
      have hnn : (0 : ℤ) ≤ (a : ℤ) ^ 2 := sq_nonneg (a : ℤ)
      exact lt_of_le_of_lt hnn (lt_add_of_pos_right _ two_pos)
    have hsum : (a : ℤ) ^ 2 + ((a : ℤ) ^ 2 + 2) = 2 * ((a : ℤ) ^ 2 + 1) := by ring
    have hsq : (a : ℤ) ^ 2 < (2 * (u : ℤ)) ^ 2 := by
      have hlt : (a : ℤ) ^ 2 < (a : ℤ) ^ 2 + ((a : ℤ) ^ 2 + 2) :=
        lt_add_of_pos_right _ hpos
      rw [hsum, ← heq] at hlt
      exact hlt
    exact (sq_lt_sq₀ ha0 (mul_nonneg htwo hu0)).mp hsq
  have huvZ : (a : ℤ) * b < 2 * u * v := by
    have heq :
        (2 * (u : ℤ) * v) ^ 2 =
          ((a : ℤ) * b) ^ 2 + ((a : ℤ) ^ 2 + (b : ℤ) ^ 2 + 1) := by
      calc
        (2 * (u : ℤ) * v) ^ 2 = (2 * (u : ℤ) ^ 2) * (2 * (v : ℤ) ^ 2) := by ring
        _ = ((a : ℤ) ^ 2 + 1) * ((b : ℤ) ^ 2 + 1) := by rw [← hAZ, ← hBZ]
        _ = ((a : ℤ) * b) ^ 2 + ((a : ℤ) ^ 2 + (b : ℤ) ^ 2 + 1) := by ring
    have hpos : (0 : ℤ) < (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + 1 := by
      have hnn : (0 : ℤ) ≤ (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := add_nonneg (sq_nonneg (a : ℤ)) (sq_nonneg (b : ℤ))
      exact lt_of_le_of_lt hnn (lt_add_of_pos_right _ one_pos)
    have hsq : ((a : ℤ) * b) ^ 2 < (2 * (u : ℤ) * v) ^ 2 := by
      have hlt :
          ((a : ℤ) * b) ^ 2 <
            ((a : ℤ) * b) ^ 2 + ((a : ℤ) ^ 2 + (b : ℤ) ^ 2 + 1) :=
        lt_add_of_pos_right _ hpos
      rw [← heq] at hlt
      exact hlt
    exact (sq_lt_sq₀ (mul_nonneg ha0 hb0) (mul_nonneg (mul_nonneg htwo hu0) hv0)).mp hsq
  have hbuZ : (a : ℤ) * v < b * u := by
    have heq :
        2 * (((b : ℤ) * u) ^ 2 - ((a : ℤ) * v) ^ 2) = (b : ℤ) ^ 2 - (a : ℤ) ^ 2 := by
      calc
        2 * (((b : ℤ) * u) ^ 2 - ((a : ℤ) * v) ^ 2) =
            (b : ℤ) ^ 2 * (2 * (u : ℤ) ^ 2) - (a : ℤ) ^ 2 * (2 * (v : ℤ) ^ 2) := by ring
        _ = (b : ℤ) ^ 2 * ((a : ℤ) ^ 2 + 1) - (a : ℤ) ^ 2 * ((b : ℤ) ^ 2 + 1) := by
            rw [← hAZ, ← hBZ]
        _ = (b : ℤ) ^ 2 - (a : ℤ) ^ 2 := by ring
    have hsqab : (a : ℤ) ^ 2 < (b : ℤ) ^ 2 := (sq_lt_sq₀ ha0 hb0).mpr habZ
    have hpos : (0 : ℤ) < (b : ℤ) ^ 2 - (a : ℤ) ^ 2 := sub_pos.mpr hsqab
    have hdiff : (0 : ℤ) < ((b : ℤ) * u) ^ 2 - ((a : ℤ) * v) ^ 2 := by
      have hmul : (2 : ℤ) * 0 < 2 * (((b : ℤ) * u) ^ 2 - ((a : ℤ) * v) ^ 2) := by
        rw [mul_zero, heq]
        exact hpos
      exact lt_of_mul_lt_mul_left hmul htwo
    have hsq : ((a : ℤ) * v) ^ 2 < ((b : ℤ) * u) ^ 2 := sub_pos.mp hdiff
    exact (sq_lt_sq₀ (mul_nonneg ha0 hv0) (mul_nonneg hb0 hu0)).mp hsq
  have h2u : a < 2 * u := by exact_mod_cast h2uZ
  have huv : a * b < 2 * u * v := by exact_mod_cast huvZ
  have hbu : a * v < b * u := by exact_mod_cast hbuZ
  have hC : 1 ≤ 2 * u * v - a * b := Nat.succ_le_of_lt (Nat.sub_pos_of_lt huv)
  have hD : 1 ≤ b * u - a * v := Nat.succ_le_of_lt (Nat.sub_pos_of_lt hbu)
  have hrec : a * (2 * u * v - a * b) + 2 * u * (b * u - a * v) = b := by
    rw [← Nat.cast_inj (R := ℤ)]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (Nat.le_of_lt huv),
      Nat.cast_sub (Nat.le_of_lt hbu)]
    push_cast
    have hkey : (2 : ℤ) * (u : ℤ) ^ 2 = (a : ℤ) ^ 2 + 1 := hAZ.symm
    calc
      (a : ℤ) * (2 * u * v - a * b) + 2 * u * (b * u - a * v) =
          a * (2 * u * v) - a * (a * b) + 2 * u * (b * u) - 2 * u * (a * v) := by ring
      _ = 2 * b * u ^ 2 - a ^ 2 * b := by ring
      _ = b * (2 * u ^ 2 - a ^ 2) := by ring
      _ = b * ((a ^ 2 + 1) - a ^ 2) := by rw [hkey]
      _ = b := by ring
  have hlow : a + 2 * u ≤ a * (2 * u * v - a * b) + 2 * u * (b * u - a * v) := by
    have h1 : a * 1 ≤ a * (2 * u * v - a * b) := Nat.mul_le_mul_left a hC
    have h2 : 2 * u * 1 ≤ 2 * u * (b * u - a * v) := Nat.mul_le_mul_left (2 * u) hD
    simpa [Nat.mul_one] using Nat.add_le_add h1 h2
  have hge : a + 2 * u ≤ b := le_trans hlow (le_of_eq hrec)
  have hstrict : 2 * a < a + 2 * u := by
    rw [Nat.two_mul]
    exact Nat.add_lt_add_left h2u a
  exact lt_of_lt_of_le hstrict hge
