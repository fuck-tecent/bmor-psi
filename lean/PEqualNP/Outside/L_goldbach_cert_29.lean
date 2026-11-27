import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_cert_29 :
    ∀ a:ℕ, Nat.Coprime a 29 → (∑ b ∈ (Finset.range 29).filter (fun b => Nat.Coprime b 29), Complex.exp (((2*Real.pi*(a:ℝ)*b/29:ℝ):ℂ)*Complex.I))/(28:ℂ)=(-1:ℂ)/28 := by
  intro a ha
  let ζ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) / 29))
  have hζ : IsPrimitiveRoot ζ 29 := Complex.isPrimitiveRoot_exp_of_coprime a 29 (by decide) ha
  have hexp (b : ℕ) : Complex.exp (((2 * Real.pi * (a : ℝ) * b / 29 : ℝ) : ℂ) * Complex.I) =
      ζ ^ b := by
    dsimp only [ζ]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hp : Nat.Prime 29 := by decide
  have hfilter : (Finset.range 29).filter (fun b => Nat.Coprime b 29) =
      (Finset.range 29).erase 0 := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range]
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    constructor
    · rintro ⟨hlt, hn⟩
      exact ⟨fun hb => hn (hb ▸ dvd_zero 29), hlt⟩
    · rintro ⟨hb, hlt⟩
      exact ⟨hlt, Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hb) hlt⟩
  have hsum := hζ.geom_sum_eq_zero (by decide : 1 < 29)
  rw [← Finset.sum_erase_add (Finset.range 29) (fun b => ζ ^ b)
    (by decide : 0 ∈ Finset.range 29), pow_zero] at hsum
  rw [hfilter]
  simp_rw [hexp]
  rw [eq_neg_of_add_eq_zero_left hsum]
