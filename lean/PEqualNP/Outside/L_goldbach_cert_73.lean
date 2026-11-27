import Mathlib

/-!
SPDX-License-Identifier: Apache-2.0

The prime-modulus argument below is by 26day from Goldbach PR #455,
commit c46a616a409fd17d43cef0900bd35c5bf8fedf1a. This file applies it to modulus 73.
-/

open scoped BigOperators

/-- For a prime modulus, deleting the zero residue from the full geometric sum leaves `-1`. -/
private theorem primeRamanujanSum {p a : ℕ} (hp : p.Prime) (ha : a.Coprime p) :
    (∑ b ∈ (Finset.range p).filter (fun b => b.Coprime p),
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / p : ℝ) : ℂ) * Complex.I)) = -1 := by
  let t : ℂ := 2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) / p)
  let ζ := Complex.exp t
  have hζ : IsPrimitiveRoot ζ p := by
    simpa [ζ, t] using Complex.isPrimitiveRoot_exp_of_coprime a p hp.ne_zero ha
  have hterm (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / p : ℝ) : ℂ) * Complex.I) = ζ ^ b := by
    change _ = Complex.exp t ^ b
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    dsimp [t]
    ring
  have hres : (Finset.range p).filter (fun b => b.Coprime p) = (Finset.range p).erase 0 := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range]
    constructor
    · rintro ⟨hb, hc⟩
      refine ⟨?_, hb⟩
      rintro rfl
      exact (hp.coprime_iff_not_dvd.mp hc.symm) (dvd_zero p)
    · rintro ⟨hb, hbp⟩
      exact ⟨hbp, (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hb) hbp)).symm⟩
  have hzero : 0 ∈ Finset.range p := Finset.mem_range.mpr hp.pos
  have hdel := Finset.add_sum_erase (Finset.range p) (fun b => ζ ^ b) hzero
  rw [hζ.geom_sum_eq_zero hp.one_lt] at hdel
  simp only [pow_zero] at hdel
  simp_rw [hterm]
  rw [hres]
  linear_combination hdel

theorem PEqualNP.Outside.L_goldbach_cert_73 :
    ∀ a:ℕ, Nat.Coprime a 73 → (∑ b ∈ (Finset.range 73).filter (fun b => Nat.Coprime b 73), Complex.exp (((2*Real.pi*(a:ℝ)*b/73:ℝ):ℂ)*Complex.I))/(72:ℂ)=(-1:ℂ)/72 := by
  intro a ha
  exact congrArg (fun x : ℂ => x / 72) (primeRamanujanSum (p := 73) (by decide) ha)
