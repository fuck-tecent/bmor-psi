import Mathlib

theorem PEqualNP.Outside.L_goldbach_finite_sieve_probe_crt_positive :
    ∀ n d e : ℕ, 0 < d → 0 < e → ((∃ p : ℕ, p % d = n % d ∧ p % e = 1 % e) ↔ n % (Nat.gcd d e) = 1 % (Nat.gcd d e)) := by
  intro n d e _ _
  constructor
  · rintro ⟨p, h1, h2⟩
    have h1' : p ≡ n [MOD d] := h1
    have h2' : p ≡ 1 [MOD e] := h2
    exact (h1'.of_dvd (Nat.gcd_dvd_left d e)).symm.trans (h2'.of_dvd (Nat.gcd_dvd_right d e))
  · intro h
    obtain ⟨k, hk⟩ := Nat.chineseRemainder' (h : n ≡ 1 [MOD Nat.gcd d e])
    exact ⟨k, hk.1, hk.2⟩
