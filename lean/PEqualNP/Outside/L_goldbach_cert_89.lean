import Mathlib

/-!
# L-goldbach-cert-89

The Ramanujan certificate for the prime modulus 89: raising the primitive root
`exp(2πi/89)` to a coprime power `a` keeps it primitive, hence the geometric sum
over all eighty-nine residues vanishes; the only non-unit residue is `0`, so the
sum over the units is `-1`. Dividing by the totient `φ(89) = 88` gives `-1/88`.
-/

theorem PEqualNP.Outside.L_goldbach_cert_89 :
    ∀ a:ℕ, Nat.Coprime a 89 → (∑ b ∈ (Finset.range 89).filter (fun b => Nat.Coprime b 89), Complex.exp (((2*Real.pi*(a:ℝ)*b/89:ℝ):ℂ)*Complex.I))/(88:ℂ)=(-1:ℂ)/88 := by
  intro a hca
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((a:ℚ)/(89:ℚ))) with hω
  have hterm : ∀ b:ℕ, Complex.exp (((2*Real.pi*(a:ℝ)*b/89:ℝ):ℂ)*Complex.I) = ω^b := by
    intro b
    have hb : ((2*Real.pi*(a:ℝ)*b/89:ℝ):ℂ) * Complex.I = ((b:ℂ)) * (2 * Real.pi * Complex.I * ((a:ℚ)/(89:ℚ))) := by
      push_cast
      ring_nf
    rw [hb, Complex.exp_nat_mul, hω]
  have hprim : IsPrimitiveRoot ω 89 := by
    rw [hω]
    exact Complex.isPrimitiveRoot_exp_of_coprime a 89 (by norm_num) hca
  have hgeo : ∑ b ∈ Finset.range 89, ω^b = 0 := hprim.geom_sum_eq_zero (by norm_num)
  have hsum : ∑ b ∈ Finset.range 89, Complex.exp (((2*Real.pi*(a:ℝ)*b/89:ℝ):ℂ)*Complex.I) = 0 := by
    calc (∑ b ∈ Finset.range 89, Complex.exp (((2*Real.pi*(a:ℝ)*b/89:ℝ):ℂ)*Complex.I))
        = ∑ b ∈ Finset.range 89, ω^b := Finset.sum_congr rfl (fun b _ => hterm b)
      _ = 0 := hgeo
  have hp : Nat.Prime 89 := by decide
  have hins : (Finset.range 89) = insert 0 ((Finset.range 89).filter (fun b => Nat.Coprime b 89)) := by
    ext b
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h
      rcases Nat.eq_zero_or_pos b with hb | hb
      · exact Or.inl hb
      · refine Or.inr ⟨h, ?_⟩
        have hndvd : ¬ ((89:ℕ) ∣ b) := by
          intro hd
          obtain ⟨k, hk⟩ := hd
          omega
        exact ((hp.coprime_iff_not_dvd).mpr hndvd).symm
    · rintro (rfl | ⟨h, -⟩)
      · omega
      · omega
  have h0n : (0:ℕ) ∉ (Finset.range 89).filter (fun b => Nat.Coprime b 89) := by
    simp [Finset.mem_filter]
  rw [hins, Finset.sum_insert h0n] at hsum
  have h0 : Complex.exp (((2*Real.pi*(a:ℝ)*((0:ℕ):ℝ)/89:ℝ):ℂ)*Complex.I) = 1 := by
    push_cast
    norm_num
  rw [h0] at hsum
  have hunits : (∑ b ∈ (Finset.range 89).filter (fun b => Nat.Coprime b 89), Complex.exp (((2*Real.pi*(a:ℝ)*b/89:ℝ):ℂ)*Complex.I)) = -1 := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hsum
  rw [hunits]
