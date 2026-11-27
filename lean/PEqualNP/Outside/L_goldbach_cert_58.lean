import Mathlib

theorem PEqualNP.Outside.L_goldbach_cert_58 :
    ∀ a:ℕ, Nat.Coprime a 58 → (∑ b ∈ (Finset.range 58).filter (fun b => Nat.Coprime b 58), Complex.exp (((2*Real.pi*(a:ℝ)*b/58:ℝ):ℂ)*Complex.I))/(28:ℂ)=(1:ℂ)/28 := by
  intro a ha
  let s_coprime : Finset ℕ := (Finset.range 58).filter (fun b => Nat.Coprime b 58)
  let s_even : Finset ℕ := (Finset.range 58).filter (fun b => 2 ∣ b)
  let s_rest : Finset ℕ := (Finset.range 58).filter (fun b => ¬ Nat.Coprime b 58)
  let f : ℕ → ℂ := fun b => Complex.exp (((2 * Real.pi * (a : ℝ) * (b : ℝ) / 58 : ℝ) : ℂ) * Complex.I)
  have hshift : ∀ b k : ℕ,
      Complex.exp (((2 * Real.pi * (a : ℝ) * (k : ℝ) / 58 : ℝ) : ℂ) * Complex.I) * f b = f ((b + k) % 58) := by
    intro b k
    simp only [f, ← Complex.exp_add, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_ofNat, Complex.ofReal_natCast]
    refine Complex.exp_eq_exp_iff_exists_int.mpr ⟨((a * ((b + k) / 58) : ℕ) : ℤ), ?_⟩
    have hmod : (b : ℂ) + (k : ℂ) = 58 * (((b + k) / 58 : ℕ) : ℂ) + (((b + k) % 58 : ℕ) : ℂ) := by
      have h := congrArg (Nat.cast (R := ℂ)) (Nat.div_add_mod (b + k) 58).symm
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h
    have hq : (((a * ((b + k) / 58) : ℕ) : ℤ) : ℂ) = (a : ℂ) * (((b + k) / 58 : ℕ) : ℂ) := by
      rw [Int.cast_natCast, Nat.cast_mul]
    rw [hq]
    linear_combination (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / 58) * hmod
  have hsum_all : ∑ b ∈ Finset.range 58, f b = 0 := by
    let ω₁ : ℂ := Complex.exp (((2 * Real.pi * (a : ℝ) * (1 : ℝ) / 58 : ℝ) : ℂ) * Complex.I)
    have hω₁_ne : ω₁ ≠ 1 := by
      have hω₁_eq : ω₁ = Complex.exp (2 * Real.pi * Complex.I * ((a : ℕ) : ℂ) / ((58 : ℕ) : ℂ)) := by
        simp only [ω₁]
        congr 1
        push_cast
        ring
      rw [hω₁_eq, ne_eq, Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (k := a) (N := 58) (by decide)]
      intro h58
      have hgcd : 58 ∣ Nat.gcd a 58 := Nat.dvd_gcd h58 (dvd_refl 58)
      rw [ha] at hgcd
      omega
    have hmul_eq : ω₁ * (∑ b ∈ Finset.range 58, f b) = ∑ b ∈ Finset.range 58, f b := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij' (fun b _ => (b + 1) % 58) (fun b _ => (b + 57) % 58)
        (fun b _ => Finset.mem_range.mpr (Nat.mod_lt _ (by decide)))
        (fun b _ => Finset.mem_range.mpr (Nat.mod_lt _ (by decide)))
        (fun b hb => ?_) (fun b hb => ?_) (fun b _ => ?_)
      · have hlt : b < 58 := Finset.mem_range.mp hb
        omega
      · have hlt : b < 58 := Finset.mem_range.mp hb
        omega
      · simpa only [ω₁, Nat.cast_one] using hshift b 1
    have hmul : (ω₁ - 1) * (∑ b ∈ Finset.range 58, f b) = 0 := by
      rw [sub_mul, one_mul, hmul_eq, sub_self]
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hω₁_ne)
  have hsum_even : ∑ b ∈ s_even, f b = 0 := by
    let ω₂ : ℂ := Complex.exp (((2 * Real.pi * (a : ℝ) * (2 : ℝ) / 58 : ℝ) : ℂ) * Complex.I)
    have hω₂_ne : ω₂ ≠ 1 := by
      have hω₂_eq : ω₂ = Complex.exp (2 * Real.pi * Complex.I * ((a : ℕ) : ℂ) / ((29 : ℕ) : ℂ)) := by
        simp only [ω₂]
        congr 1
        push_cast
        ring
      rw [hω₂_eq, ne_eq, Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (k := a) (N := 29) (by decide)]
      intro h29
      have hgcd : 29 ∣ Nat.gcd a 58 := Nat.dvd_gcd h29 (by decide)
      rw [ha] at hgcd
      omega
    have hmem_even : ∀ k : ℕ, 2 ∣ k → ∀ b ∈ s_even, (b + k) % 58 ∈ s_even := by
      intro k hk b hb
      rw [Finset.mem_filter, Finset.mem_range] at hb ⊢
      refine ⟨Nat.mod_lt _ (by decide), ?_⟩
      rcases hb.2 with ⟨m, hm⟩
      rcases hk with ⟨j, hj⟩
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    have hmul_eq : ω₂ * (∑ b ∈ s_even, f b) = ∑ b ∈ s_even, f b := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij' (fun b _ => (b + 2) % 58) (fun b _ => (b + 56) % 58)
        (fun b hb => hmem_even 2 (by decide) b hb)
        (fun b hb => hmem_even 56 (by decide) b hb)
        (fun b hb => ?_) (fun b hb => ?_) (fun b _ => ?_)
      · have hlt : b < 58 := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
        omega
      · have hlt : b < 58 := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
        omega
      · simpa only [ω₂, Nat.cast_ofNat] using hshift b 2
    have hmul : (ω₂ - 1) * (∑ b ∈ s_even, f b) = 0 := by
      rw [sub_mul, one_mul, hmul_eq, sub_self]
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hω₂_ne)
  have hf29 : f 29 = -1 := by
    have hodd : a % 2 = 1 := by
      by_contra h
      have h2 : 2 ∣ a := Nat.dvd_of_mod_eq_zero (by omega)
      have hgcd : 2 ∣ Nat.gcd a 58 := Nat.dvd_gcd h2 (by decide)
      rw [ha] at hgcd
      omega
    have ha_eq : (a : ℂ) = 2 * ((a / 2 : ℕ) : ℂ) + 1 := by
      have hnat : a = 2 * (a / 2) + 1 := by omega
      have hc := congrArg (Nat.cast (R := ℂ)) hnat
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hc
    have hexp : f 29 = Complex.exp ((Real.pi : ℂ) * Complex.I) := by
      simp only [f, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast]
      refine Complex.exp_eq_exp_iff_exists_int.mpr ⟨((a / 2 : ℕ) : ℤ), ?_⟩
      rw [Int.cast_natCast]
      linear_combination ((Real.pi : ℂ) * Complex.I) * ha_eq
    rw [hexp, Complex.exp_pi_mul_I]
  have hrest : s_rest = insert 29 s_even := by
    ext b
    simp only [s_rest, s_even, Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hlt, hnc⟩
      obtain ⟨p, hp, hpb, hp58⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
      have hp_cases : p = 2 ∨ p = 29 := by
        have hmul : p ∣ 2 * 29 := by simpa using hp58
        rcases hp.dvd_mul.mp hmul with h2 | h29
        · left
          exact (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h2
        · right
          exact (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h29
      rcases hp_cases with rfl | rfl
      · exact Or.inr ⟨hlt, hpb⟩
      · rcases hpb with ⟨m, hm⟩
        by_cases hm0 : m = 0
        · refine Or.inr ⟨hlt, ⟨0, by omega⟩⟩
        · exact Or.inl (by omega)
    · rintro (rfl | ⟨hlt, h2b⟩)
      · refine ⟨by decide, ?_⟩
        decide
      · refine ⟨hlt, ?_⟩
        intro hc
        have hgcd : 2 ∣ Nat.gcd b 58 := Nat.dvd_gcd h2b (by decide)
        rw [hc] at hgcd
        omega
  have h29_not_mem : (29 : ℕ) ∉ s_even := by
    simp only [s_even, Finset.mem_filter, Finset.mem_range]
    intro h
    rcases h.2 with ⟨m, hm⟩
    omega
  have hpart : (∑ b ∈ s_coprime, f b) + (∑ b ∈ s_rest, f b) = ∑ b ∈ Finset.range 58, f b :=
    Finset.sum_filter_add_sum_filter_not (Finset.range 58) (fun b => Nat.Coprime b 58) f
  rw [hrest, Finset.sum_insert h29_not_mem, hf29, hsum_even, hsum_all] at hpart
  have hS : ∑ b ∈ s_coprime, f b = 1 := by linear_combination hpart
  change (∑ b ∈ s_coprime, f b) / (28 : ℂ) = (1 : ℂ) / 28
  rw [hS]
