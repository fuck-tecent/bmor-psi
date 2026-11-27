import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_cert_147 :
    ∀ a:ℕ, Nat.Coprime a 147 → (∑ b ∈ (Finset.range 147).filter (fun b => Nat.Coprime b 147), Complex.exp (((2*Real.pi*(a:ℝ)*b/147:ℝ):ℂ)*Complex.I))/(84:ℂ)=(0:ℂ)/84 := by
  intro a ha
  let residues := (Finset.range 21).filter (fun r => Nat.Coprime r 21)
  let units := (Finset.range 147).filter (fun b => Nat.Coprime b 147)
  let term (b : ℕ) := Complex.exp (((2 * Real.pi * (a : ℝ) * b / 147 : ℝ) : ℂ) * Complex.I)
  let step := 2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) / 7)
  change (∑ b ∈ units, term b) / (84 : ℂ) = (0 : ℂ) / 84
  -- The prime divisors of 147 are already the prime divisors of 21.
  have hperiod (r k : ℕ) : Nat.Coprime (r + k * 21) 147 ↔ Nat.Coprime r 21 := by
    have hrad (n : ℕ) : Nat.Coprime n 147 ↔ Nat.Coprime n 21 := by
      change Nat.Coprime n (21 * 7) ↔ Nat.Coprime n 21
      rw [Nat.coprime_mul_iff_right]
      exact ⟨And.left, fun h => ⟨h, Nat.Coprime.of_dvd_right (by decide) h⟩⟩
    rw [hrad, Nat.coprime_add_mul_right_left]
  -- Write each unit b modulo 147 uniquely as r + 21k with r < 21 and k < 7.
  have hreindex :
      (∑ b ∈ units, term b) = ∑ p ∈ residues.product (Finset.range 7), term (p.1 + p.2 * 21) := by
    symm
    refine Finset.sum_bij (fun p _ => p.1 + p.2 * 21) ?_ ?_ ?_ ?_
    · rintro ⟨r, k⟩ hp
      have ⟨hr, hk⟩ := Finset.mem_product.mp hp
      have ⟨hrRange, hrCoprime⟩ := Finset.mem_filter.mp hr
      have hrLt := Finset.mem_range.mp hrRange
      have hkLt := Finset.mem_range.mp hk
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), (hperiod r k).mpr hrCoprime⟩
    · rintro ⟨r, k⟩ hp ⟨s, j⟩ hq he
      have hrLt := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).1
      have hsLt := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_product.mp hq).1).1
      change r + k * 21 = s + j * 21 at he
      have hrs : r = s := by omega
      have hkj : k = j := by omega
      simp [hrs, hkj]
    · intro b hb
      have ⟨hbRange, hbCoprime⟩ := Finset.mem_filter.mp hb
      have hbLt := Finset.mem_range.mp hbRange
      have hrepr : b % 21 + b / 21 * 21 = b := by omega
      refine ⟨(b % 21, b / 21), Finset.mem_product.mpr ⟨?_, ?_⟩, hrepr⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
          (hperiod (b % 21) (b / 21)).mp (by simpa only [hrepr] using hbCoprime)⟩
      · exact Finset.mem_range.mpr (by omega)
    · intro p hp
      rfl
  have ha7 : Nat.Coprime a 7 := Nat.Coprime.of_dvd_right (by decide) ha
  have hroot : IsPrimitiveRoot (Complex.exp step) 7 :=
    Complex.isPrimitiveRoot_exp_of_coprime a 7 (by decide) ha7
  have hphase (r k : ℕ) : term (r + k * 21) = term r * Complex.exp step ^ k := by
    dsimp only [term, step]
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    apply congrArg Complex.exp
    push_cast
    ring
  have hsum : (∑ b ∈ units, term b) = 0 := by
    rw [hreindex, Finset.product_eq_sprod]
    rw [Finset.sum_product' residues (Finset.range 7) (fun r k => term (r + k * 21))]
    apply Finset.sum_eq_zero
    intro r _
    simp_rw [hphase]
    rw [← Finset.mul_sum, hroot.geom_sum_eq_zero (by decide), mul_zero]
  rw [hsum]
