import Mathlib

theorem PEqualNP.Outside.L_goldbach_cert_45 :
    ∀ a:ℕ, Nat.Coprime a 45 → (∑ b ∈ (Finset.range 45).filter (fun b => Nat.Coprime b 45), Complex.exp (((2*Real.pi*(a:ℝ)*b/45:ℝ):ℂ)*Complex.I))/(24:ℂ)=(0:ℂ)/24 := by
  intro a ha
  let s : Finset ℕ := (Finset.range 45).filter (fun b => Nat.Coprime b 45)
  let f : ℕ → ℂ := fun b => Complex.exp (((2 * Real.pi * (a : ℝ) * (b : ℝ) / 45 : ℝ) : ℂ) * Complex.I)
  let ω : ℂ := Complex.exp (((2 * Real.pi * (a : ℝ) / 3 : ℝ) : ℂ) * Complex.I)
  have hω_ne : ω ≠ 1 := by
    have hω_eq : ω = Complex.exp (2 * Real.pi * Complex.I * ((a : ℕ) : ℂ) / ((3 : ℕ) : ℂ)) := by
      simp only [ω]
      congr 1
      push_cast
      ring
    rw [hω_eq, ne_eq, Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (k := a) (N := 3) (by decide)]
    intro h3
    have hgcd : 3 ∣ Nat.gcd a 45 := Nat.dvd_gcd h3 (by decide)
    rw [ha] at hgcd
    omega
  have hshift_coprime : ∀ (k : ℕ), 45 ∣ k * k → ∀ {b : ℕ}, Nat.Coprime b 45 → Nat.Coprime ((b + k) % 45) 45 := by
    intro k hk b hb
    refine Nat.coprime_of_dvd fun p hp hpdvd h45 => ?_
    have hpb_add : p ∣ b + k := by
      have hdiv : 45 * ((b + k) / 45) + (b + k) % 45 = b + k := Nat.div_add_mod (b + k) 45
      rw [← hdiv]
      exact Nat.dvd_add (dvd_mul_of_dvd_left h45 _) hpdvd
    have hpk : p ∣ k := (hp.dvd_mul.mp (dvd_trans h45 hk)).elim id id
    have hpb : p ∣ b := (Nat.dvd_add_left hpk).mp hpb_add
    exact hp.not_dvd_one (hb ▸ Nat.dvd_gcd hpb h45)
  have hmem_shift : ∀ (k : ℕ), 45 ∣ k * k → ∀ b ∈ s, (b + k) % 45 ∈ s := by
    intro k hk b hb
    rw [Finset.mem_filter, Finset.mem_range] at hb ⊢
    exact ⟨Nat.mod_lt _ (by decide), hshift_coprime k hk hb.2⟩
  have hsum_eq : ω * (∑ b ∈ s, f b) = ∑ b ∈ s, f b := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij' (fun b _ => (b + 15) % 45) (fun b _ => (b + 30) % 45)
      (fun b hb => hmem_shift 15 (by decide) b hb)
      (fun b hb => hmem_shift 30 (by decide) b hb)
      (fun b hb => ?_) (fun b hb => ?_) (fun b _ => ?_)
    · have hlt : b < 45 := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
      omega
    · have hlt : b < 45 := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
      omega
    · simp only [ω, f, ← Complex.exp_add, Complex.ofReal_div, Complex.ofReal_mul,
        Complex.ofReal_ofNat, Complex.ofReal_natCast]
      refine Complex.exp_eq_exp_iff_exists_int.mpr ⟨((a * ((b + 15) / 45) : ℕ) : ℤ), ?_⟩
      have hmod : (b : ℂ) + 15 = 45 * (((b + 15) / 45 : ℕ) : ℂ) + (((b + 15) % 45 : ℕ) : ℂ) := by
        have h := congrArg (Nat.cast (R := ℂ)) (Nat.div_add_mod (b + 15) 45).symm
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h
      have hq : (((a * ((b + 15) / 45) : ℕ) : ℤ) : ℂ) = (a : ℂ) * (((b + 15) / 45 : ℕ) : ℂ) := by
        rw [Int.cast_natCast, Nat.cast_mul]
      rw [hq]
      linear_combination (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / 45) * hmod
  have hmul : (ω - 1) * (∑ b ∈ s, f b) = 0 := by
    rw [sub_mul, one_mul, hsum_eq, sub_self]
  have hS : (∑ b ∈ s, f b) = 0 := (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hω_ne)
  change (∑ b ∈ s, f b) / (24 : ℂ) = (0 : ℂ) / 24
  rw [hS]
