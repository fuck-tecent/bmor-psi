import Mathlib

theorem Conjectures.QuadraticPrimes.SieveTerminalGaussian :
    ∀ n p : ℕ, 0 < n → p.Prime → 2 < p → p ∣ n ^ 2 + 1 →
      ∃ a b c d : ℤ, a ^ 2 + b ^ 2 = (p : ℤ) ∧ 0 < a ∧ b ≠ 0 ∧
        (n : ℤ) = a * c - b * d ∧ 1 = a * d + b * c ∧
        c ^ 2 + d ^ 2 = ((n ^ 2 + 1) / p : ℕ) := by
  intro n p hn hp hp2 hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  have hzero : ((n ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
    obtain ⟨k, hk⟩ := hdvd
    rw [hk]
    push_cast
    rw [ZMod.natCast_self]
    ring
  have hn1 : (n : ZMod p) ^ 2 = -1 := by
    have h' : (n : ZMod p) ^ 2 + 1 = 0 := by
      have h2 := hzero
      push_cast at h2
      simpa using h2
    linear_combination h'
  have hs : IsSquare (-1 : ZMod p) := ⟨(n : ZMod p), by rw [pow_two] at hn1; exact hn1.symm⟩
  obtain ⟨x, y, hxy⟩ := Nat.eq_sq_add_sq_of_isSquare_mod_neg_one hs
  have hsqne : ∀ z : ℕ, p = z ^ 2 → False := by
    intro z hz
    have hd : z ∣ p := ⟨z, by rw [pow_two] at hz; exact hz⟩
    rcases hp.eq_one_or_self_of_dvd z hd with h | h
    · rw [h] at hz
      norm_num at hz
      omega
    · rw [h, pow_two] at hz
      have h3 : p * 1 = p * p := by rw [mul_one]; exact hz
      have h4 := Nat.mul_left_cancel (by omega : 0 < p) h3
      omega
  have hx0 : x ≠ 0 := by
    intro h
    exact hsqne y (by rw [h, zero_pow (by norm_num), zero_add] at hxy; exact hxy)
  have hy0 : y ≠ 0 := by
    intro h
    exact hsqne x (by rw [h, zero_pow (by norm_num), add_zero] at hxy; exact hxy)
  have hZ : (x : ℤ) ^ 2 + (y : ℤ) ^ 2 = (p : ℤ) := by
    have h : ((x ^ 2 + y ^ 2 : ℕ) : ℤ) = (p : ℤ) := by rw [← hxy]
    push_cast at h
    exact h
  have hpZ : ((p : ℤ)) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hyZ : ((y : ℤ)) ≠ 0 := by exact_mod_cast hy0
  have hdvdZ : (p : ℤ) ∣ ((n : ℤ) ^ 2 + 1) := by
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨(k : ℤ), ?_⟩
    have hcast : ((n ^ 2 + 1 : ℕ) : ℤ) = ((p * k : ℕ) : ℤ) := by rw [hk]
    push_cast at hcast
    exact hcast
  have hder : (p : ℤ) ∣ ((x : ℤ) - (n : ℤ) * (y : ℤ)) * ((x : ℤ) + (n : ℤ) * (y : ℤ)) := by
    have hfac : ((x : ℤ) - (n : ℤ) * (y : ℤ)) * ((x : ℤ) + (n : ℤ) * (y : ℤ))
        = ((x : ℤ) ^ 2 + (y : ℤ) ^ 2) - (y : ℤ) ^ 2 * ((n : ℤ) ^ 2 + 1) := by ring
    rw [hfac]
    exact dvd_sub (by rw [hZ]) (dvd_mul_of_dvd_right hdvdZ _)
  have main : ∀ b : ℤ, b ^ 2 = (y : ℤ) ^ 2 → b ≠ 0 →
      (p : ℤ) ∣ ((x : ℤ) - (n : ℤ) * b) →
      ∃ a c d : ℤ, a ^ 2 + b ^ 2 = (p : ℤ) ∧ 0 < a ∧
        (n : ℤ) = a * c - b * d ∧ 1 = a * d + b * c ∧
        c ^ 2 + d ^ 2 = ((n ^ 2 + 1) / p : ℕ) := by
    intro b hbsq _ hbdiv
    have hpb : (p : ℤ) ∣ ((n : ℤ) * (x : ℤ) + b) := by
      have h1 : (p : ℤ) ∣ (n : ℤ) * ((x : ℤ) - (n : ℤ) * b) := dvd_mul_of_dvd_right hbdiv _
      have h2 : (p : ℤ) ∣ b * ((n : ℤ) ^ 2 + 1) := dvd_mul_of_dvd_right hdvdZ b
      have hsum := dvd_add h1 h2
      have heq : (n : ℤ) * ((x : ℤ) - (n : ℤ) * b) + b * ((n : ℤ) ^ 2 + 1)
          = (n : ℤ) * (x : ℤ) + b := by ring
      rwa [heq] at hsum
    obtain ⟨c, hc⟩ := hpb
    obtain ⟨d, hd⟩ := hbdiv
    refine ⟨(x : ℤ), c, d, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hbsq]; exact hZ
    · exact_mod_cast (Nat.pos_of_ne_zero hx0)
    · have hkey : (p : ℤ) * ((x : ℤ) * c - b * d) = (p : ℤ) * (n : ℤ) := by
        calc (p : ℤ) * ((x : ℤ) * c - b * d)
            = (x : ℤ) * ((p : ℤ) * c) - b * ((p : ℤ) * d) := by ring
          _ = (x : ℤ) * ((n : ℤ) * (x : ℤ) + b) - b * ((x : ℤ) - (n : ℤ) * b) := by rw [hc, hd]
          _ = (p : ℤ) * (n : ℤ) := by
              have hstep : (x : ℤ) * ((n : ℤ) * (x : ℤ) + b) - b * ((x : ℤ) - (n : ℤ) * b)
                  = (n : ℤ) * ((x : ℤ) ^ 2 + b ^ 2) := by ring
              rw [hstep, hbsq, hZ]; ring
      exact (mul_left_cancel₀ hpZ hkey).symm
    · have hkey : (p : ℤ) * ((x : ℤ) * d + b * c) = (p : ℤ) * 1 := by
        calc (p : ℤ) * ((x : ℤ) * d + b * c)
            = (x : ℤ) * ((p : ℤ) * d) + b * ((p : ℤ) * c) := by ring
          _ = (x : ℤ) * ((x : ℤ) - (n : ℤ) * b) + b * ((n : ℤ) * (x : ℤ) + b) := by rw [hc, hd]
          _ = (p : ℤ) * 1 := by
              have hstep2 : (x : ℤ) * ((x : ℤ) - (n : ℤ) * b) + b * ((n : ℤ) * (x : ℤ) + b)
                  = (x : ℤ) ^ 2 + b ^ 2 := by ring
              rw [hstep2, hbsq, hZ]; ring
      exact (mul_left_cancel₀ hpZ hkey).symm
    · have hkey : (p : ℤ) ^ 2 * (c ^ 2 + d ^ 2) = (p : ℤ) * ((n : ℤ) ^ 2 + 1) := by
        calc (p : ℤ) ^ 2 * (c ^ 2 + d ^ 2)
            = ((p : ℤ) * c) ^ 2 + ((p : ℤ) * d) ^ 2 := by ring
          _ = ((n : ℤ) * (x : ℤ) + b) ^ 2 + ((x : ℤ) - (n : ℤ) * b) ^ 2 := by rw [hc, hd]
          _ = ((n : ℤ) ^ 2 + 1) * ((x : ℤ) ^ 2 + b ^ 2) := by ring
          _ = ((n : ℤ) ^ 2 + 1) * (p : ℤ) := by rw [hbsq, hZ]
          _ = (p : ℤ) * ((n : ℤ) ^ 2 + 1) := by ring
      have hpp : (p : ℤ) * ((p : ℤ) * (c ^ 2 + d ^ 2)) = (p : ℤ) * ((n : ℤ) ^ 2 + 1) := by
        rw [← hkey]; ring
      have hpc : (p : ℤ) * (c ^ 2 + d ^ 2) = ((n : ℤ) ^ 2 + 1) := mul_left_cancel₀ hpZ hpp
      have hnat : (p : ℤ) * (((n ^ 2 + 1) / p : ℕ) : ℤ) = ((n : ℤ) ^ 2 + 1) := by
        have h := Nat.div_mul_cancel hdvd
        have hc2 : (((n ^ 2 + 1) / p : ℕ) : ℤ) * (p : ℤ) = ((n ^ 2 + 1 : ℕ) : ℤ) := by
          exact_mod_cast h
        push_cast at hc2
        rw [mul_comm]
        exact hc2
      have he : (p : ℤ) * (c ^ 2 + d ^ 2) = (p : ℤ) * (((n ^ 2 + 1) / p : ℕ) : ℤ) := by
        rw [hpc, hnat]
      exact mul_left_cancel₀ hpZ he
  rcases Int.Prime.dvd_mul' hp hder with hA | hB
  · obtain ⟨a, c, d, h1, h2, h3, h4, h5⟩ := main (y : ℤ) (by ring) hyZ hA
    exact ⟨a, (y : ℤ), c, d, h1, h2, hyZ, h3, h4, h5⟩
  · obtain ⟨a, c, d, h1, h2, h3, h4, h5⟩ :=
      main (-(y : ℤ)) (by ring) (neg_ne_zero.mpr hyZ)
        (by rw [mul_neg, sub_neg_eq_add]; exact hB)
    exact ⟨a, -(y : ℤ), c, d, h1, h2, (neg_ne_zero.mpr hyZ), h3, h4, h5⟩
