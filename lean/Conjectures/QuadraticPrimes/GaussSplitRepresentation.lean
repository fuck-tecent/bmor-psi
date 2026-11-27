import Mathlib

namespace Conjectures.QuadraticPrimes.GaussSplitRepresentation_aux

theorem prime_not_sq (p y : ℕ) (hp : p.Prime) (h : p = y ^ 2) : False := by
  have hd : y ∣ p := by
    refine ⟨y, ?_⟩
    rw [h, pow_two]
  rcases hp.eq_one_or_self_of_dvd y hd with h1 | h1
  · have h2 : p = 1 := by rw [h, h1, one_pow]
    exact hp.ne_one h2
  · have h2 : p = p * p := by
      calc p = y ^ 2 := h
        _ = p ^ 2 := by rw [h1]
        _ = p * p := pow_two p
    have h3 : p * 1 = p * p := (h2.symm.trans (mul_one p).symm).symm
    have h4 : 1 = p := Nat.mul_left_cancel hp.pos h3
    exact hp.ne_one h4.symm

theorem exists_ordered {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    ∃ a b : ℕ, 0 < a ∧ a ≤ b ∧ a ^ 2 + b ^ 2 = p := by
  have hne : p % 4 ≠ 3 := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, y, hxy⟩ := Nat.Prime.sq_add_sq (p := p) hne
  have hx : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · exfalso
      exact prime_not_sq p y hp (by rw [← hxy, h]; ring)
    · exact h
  have hy : 0 < y := by
    rcases Nat.eq_zero_or_pos y with h | h
    · exfalso
      exact prime_not_sq p x hp (by rw [← hxy, h]; ring)
    · exact h
  refine ⟨min x y, max x y, lt_min hx hy, min_le_max, ?_⟩
  rcases le_total x y with h | h
  · rw [min_eq_left h, max_eq_right h]
    exact hxy
  · rw [min_eq_right h, max_eq_left h]
    rw [add_comm]
    exact hxy

theorem coord_unique {p a b c d : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1)
    (ha : 0 < a) (hab : a ≤ b) (hsq : a ^ 2 + b ^ 2 = p)
    (hc : 0 < c) (hcd : c ≤ d) (hsq2 : c ^ 2 + d ^ 2 = p) :
    a = c ∧ b = d := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hd : 0 < d := lt_of_lt_of_le hc hcd
  have ha2 : a ^ 2 < p := by nlinarith [hsq, hb]
  have hb2 : b ^ 2 < p := by nlinarith [hsq, ha]
  have hc2 : c ^ 2 < p := by nlinarith [hsq2, hd]
  have hd2 : d ^ 2 < p := by nlinarith [hsq2, hc]
  have had : a * d < p := by
    rcases le_total a d with h | h
    · calc a * d ≤ d * d := Nat.mul_le_mul_right d h
        _ = d ^ 2 := by ring
        _ < p := hd2
    · calc a * d ≤ a * a := Nat.mul_le_mul_left a h
        _ = a ^ 2 := by ring
        _ < p := ha2
  have hcb : c * b < p := by
    rcases le_total c b with h | h
    · calc c * b ≤ b * b := Nat.mul_le_mul_right b h
        _ = b ^ 2 := by ring
        _ < p := hb2
    · calc c * b ≤ c * c := Nat.mul_le_mul_left c h
        _ = c ^ 2 := by ring
        _ < p := hc2
  have e1 : ((a : ℤ)) ^ 2 + ((b : ℤ)) ^ 2 = ((p : ℕ) : ℤ) := by exact_mod_cast hsq
  have e2 : ((c : ℤ)) ^ 2 + ((d : ℤ)) ^ 2 = ((p : ℕ) : ℤ) := by exact_mod_cast hsq2
  have hmul : (((a : ℤ)) * ((d : ℤ)) - ((c : ℤ)) * ((b : ℤ))) *
      (((a : ℤ)) * ((d : ℤ)) + ((c : ℤ)) * ((b : ℤ))) =
      ((p : ℕ) : ℤ) * (((a : ℤ)) ^ 2 - ((c : ℤ)) ^ 2) := by
    have f1 : ((d : ℤ)) ^ 2 = ((p : ℕ) : ℤ) - ((c : ℤ)) ^ 2 := by linarith [e2]
    have f2 : ((b : ℤ)) ^ 2 = ((p : ℕ) : ℤ) - ((a : ℤ)) ^ 2 := by linarith [e1]
    calc (((a : ℤ)) * ((d : ℤ)) - ((c : ℤ)) * ((b : ℤ))) *
          (((a : ℤ)) * ((d : ℤ)) + ((c : ℤ)) * ((b : ℤ)))
        = ((a : ℤ)) ^ 2 * ((d : ℤ)) ^ 2 - ((c : ℤ)) ^ 2 * ((b : ℤ)) ^ 2 := by ring
      _ = ((p : ℕ) : ℤ) * (((a : ℤ)) ^ 2 - ((c : ℤ)) ^ 2) := by rw [f1, f2]; ring
  have hdvd : (((p : ℕ) : ℤ)) ∣ ((((a : ℤ)) * ((d : ℤ)) - ((c : ℤ)) * ((b : ℤ))) *
      (((a : ℤ)) * ((d : ℤ)) + ((c : ℤ)) * ((b : ℤ)))) := ⟨_, hmul⟩
  rcases (Nat.prime_iff_prime_int.mp hp).dvd_mul.mp hdvd with hcase | hcase
  · have hbound : |((a : ℤ)) * ((d : ℤ)) - ((c : ℤ)) * ((b : ℤ))| < ((p : ℕ) : ℤ) := by
      have h1 : ((a : ℤ)) * ((d : ℤ)) - ((c : ℤ)) * ((b : ℤ)) =
          ((a * d : ℕ) : ℤ) - ((c * b : ℕ) : ℤ) := by push_cast; ring
      rw [h1]
      exact Int.abs_sub_lt_of_lt_lt hcb had
    have hz : ((a : ℤ)) * ((d : ℤ)) - ((c : ℤ)) * ((b : ℤ)) = 0 :=
      Int.eq_zero_of_abs_lt_dvd hcase hbound
    have hnat : a * d = c * b := by
      have h2 : ((a : ℤ)) * ((d : ℤ)) = ((c : ℤ)) * ((b : ℤ)) := by linarith [hz]
      exact_mod_cast h2
    have hkey : a ^ 2 * p = c ^ 2 * p := by
      calc a ^ 2 * p = a ^ 2 * (c ^ 2 + d ^ 2) := by rw [hsq2]
        _ = (a * c) ^ 2 + (a * d) ^ 2 := by ring
        _ = (a * c) ^ 2 + (c * b) ^ 2 := by rw [hnat]
        _ = c ^ 2 * (a ^ 2 + b ^ 2) := by ring
        _ = c ^ 2 * p := by rw [hsq]
    have h5 : a ^ 2 = c ^ 2 := Nat.mul_left_cancel hp.pos (by simpa [mul_comm] using hkey)
    have hac : a = c := Nat.pow_left_injective (by norm_num) h5
    subst hac
    have h6 : b ^ 2 = d ^ 2 := by linarith [hsq, hsq2]
    exact ⟨rfl, Nat.pow_left_injective (by norm_num) h6⟩
  · have hpos : (0 : ℤ) < ((a : ℤ)) * ((d : ℤ)) + ((c : ℤ)) * ((b : ℤ)) := by
      have h1 : (0 : ℤ) < ((a : ℕ) : ℤ) := by exact_mod_cast ha
      have h2 : (0 : ℤ) < ((d : ℕ) : ℤ) := by exact_mod_cast hd
      have h3 : (0 : ℤ) < ((c : ℕ) : ℤ) := by exact_mod_cast hc
      have h4 : (0 : ℤ) < ((b : ℕ) : ℤ) := by exact_mod_cast hb
      exact add_pos (mul_pos h1 h2) (mul_pos h3 h4)
    have hdvdN : p ∣ (a * d + c * b) := by
      have h5 : ((a * d + c * b : ℕ) : ℤ) =
          ((a : ℤ)) * ((d : ℤ)) + ((c : ℤ)) * ((b : ℤ)) := by push_cast; ring
      have h6 : p ∣ (((a : ℤ)) * ((d : ℤ)) + ((c : ℤ)) * ((b : ℤ))).natAbs :=
        Int.natCast_dvd.mp hcase
      rwa [← h5, Int.natAbs_natCast] at h6
    have hlt : a * d + c * b < 2 * p := by
      have h7 : a * d + c * b < p + p := Nat.add_lt_add had hcb
      omega
    have hsum : a * d + c * b = p := by
      obtain ⟨t, ht⟩ := hdvdN
      have h8 : 0 < a * d + c * b := by
        have h9 : 0 < a * d := Nat.mul_pos ha hd
        nlinarith [h9, Nat.zero_le (c * b)]
      have h10 : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with h | h
        · exfalso
          rw [h, mul_zero] at ht
          omega
        · exact h
      have h11 : t ≤ 1 := by
        by_contra hc2
        have h12 : 2 ≤ t := by omega
        have h13 : p * 2 ≤ p * t := Nat.mul_le_mul_left p h12
        have h14 : p * t < 2 * p := by rw [← ht]; exact hlt
        have h15 : 2 * p ≤ p * t := by
          calc 2 * p = p * 2 := by ring
            _ ≤ p * t := h13
        exact (Nat.not_le.mpr h14) h15
      have h16 : t = 1 := by omega
      rw [h16, mul_one] at ht
      exact ht
    have hXe : ((a : ℤ)) * ((d : ℤ)) + ((c : ℤ)) * ((b : ℤ)) = ((p : ℕ) : ℤ) := by
      have h17 : ((a * d + c * b : ℕ) : ℤ) = ((p : ℕ) : ℤ) := by exact_mod_cast hsum
      have h18 : ((a * d + c * b : ℕ) : ℤ) =
          ((a : ℤ)) * ((d : ℤ)) + ((c : ℤ)) * ((b : ℤ)) := by push_cast; ring
      linarith [h17, h18]
    have hid : (((a : ℤ)) * ((d : ℤ)) + ((c : ℤ)) * ((b : ℤ))) ^ 2 +
        (((a : ℤ)) * ((c : ℤ)) - ((b : ℤ)) * ((d : ℤ))) ^ 2 = ((p : ℕ) : ℤ) ^ 2 := by
      calc (((a : ℤ)) * ((d : ℤ)) + ((c : ℤ)) * ((b : ℤ))) ^ 2 +
            (((a : ℤ)) * ((c : ℤ)) - ((b : ℤ)) * ((d : ℤ))) ^ 2
          = (((a : ℤ)) ^ 2 + ((b : ℤ)) ^ 2) * (((c : ℤ)) ^ 2 + ((d : ℤ)) ^ 2) := by ring
        _ = ((p : ℕ) : ℤ) * ((p : ℕ) : ℤ) := by rw [e1, e2]
        _ = ((p : ℕ) : ℤ) ^ 2 := by ring
    have hsq0 : (((a : ℤ)) * ((c : ℤ)) - ((b : ℤ)) * ((d : ℤ))) ^ 2 = 0 := by
      have h20 := hid
      rw [hXe] at h20
      linarith [h20]
    have hzero : ((a : ℤ)) * ((c : ℤ)) - ((b : ℤ)) * ((d : ℤ)) = 0 := by
      nlinarith [hsq0]
    have hnat2 : a * c = b * d := by
      have h19 : ((a : ℤ)) * ((c : ℤ)) = ((b : ℤ)) * ((d : ℤ)) := by linarith [hzero]
      exact_mod_cast h19
    have hba : b ≤ a := by
      have h21 : b * d ≤ a * d := by
        calc b * d = a * c := hnat2.symm
          _ ≤ a * d := Nat.mul_le_mul_left a hcd
      exact Nat.le_of_mul_le_mul_right h21 hd
    have hab2 : a = b := le_antisymm hab hba
    exfalso
    have h22 : (2 : ℕ) ∣ p := ⟨a ^ 2, by rw [← hsq, hab2]; ring⟩
    rcases hp.eq_one_or_self_of_dvd 2 h22 with h23 | h23
    · omega
    · omega

end Conjectures.QuadraticPrimes.GaussSplitRepresentation_aux

theorem Conjectures.QuadraticPrimes.GaussSplitRepresentation :
    ∀ p : ℕ, p.Prime → p % 4 = 1 →
      ∃ a b : ℕ, (0 < a ∧ a ≤ b ∧ a ^ 2 + b ^ 2 = p) ∧
        ∀ a' b' : ℕ, 0 < a' → a' ≤ b' → a' ^ 2 + b' ^ 2 = p → a' = a ∧ b' = b := by
  intro p hp hp4
  obtain ⟨a, b, ha, hab, habp⟩ :=
    Conjectures.QuadraticPrimes.GaussSplitRepresentation_aux.exists_ordered hp hp4
  refine ⟨a, b, ⟨ha, hab, habp⟩, ?_⟩
  intro a' b' ha' hab' habp'
  exact Conjectures.QuadraticPrimes.GaussSplitRepresentation_aux.coord_unique hp hp4 ha' hab'
    habp' ha hab habp
