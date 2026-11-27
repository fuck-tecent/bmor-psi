import Mathlib

namespace QuadraticMangoldtProof

private def gaussianI : GaussianInt := ⟨0, 1⟩

private theorem gaussian_norm_formula (z : GaussianInt) :
    z.norm = z.re^2 + z.im^2 := by
  rw [Zsqrtd.norm_def]
  ring

/-- The elementary Bézout identity also proves the neighbouring coprimality lemma. -/
private theorem gaussian_conjugates_coprime (n : ℕ) (hn : Even n) :
    IsCoprime ((n : GaussianInt) + gaussianI) ((n : GaussianInt) - gaussianI) := by
  obtain ⟨k, rfl⟩ := hn
  have hi : gaussianI * gaussianI = (-1 : GaussianInt) := by decide +kernel
  rw [Nat.cast_add]
  refine ⟨(k : GaussianInt) - gaussianI, -(k : GaussianInt), ?_⟩
  calc
    _ = -(gaussianI * gaussianI) := by ring
    _ = 1 := by rw [hi, neg_neg]

private theorem gaussian_unit_fourth {z : GaussianInt} (hz : IsUnit z) : z^4 = 1 := by
  have hAbs := Zsqrtd.norm_eq_one_iff.mpr hz
  have hNorm : z.norm = 1 := by
    have h : (z.norm.natAbs : ℤ) = 1 := by exact_mod_cast hAbs
    rwa [GaussianInt.abs_natCast_norm z] at h
  have hSquares : z.re^2 + z.im^2 = 1 := (gaussian_norm_formula z).symm.trans hNorm
  have hAxis : z.re = 0 ∨ z.im = 0 := by
    by_contra! h
    have hr := sq_pos_of_ne_zero h.1
    have hi := sq_pos_of_ne_zero h.2
    omega
  have hProd : z * star z = 1 := by
    rw [← Zsqrtd.norm_eq_mul_conj, hNorm, Int.cast_one]
  have hPower : z^4 = (z^2)^2 := by rw [← pow_mul]
  rw [hPower]
  rcases hAxis with hReal | hImag
  · have hStar : star z = -z := by
      apply Zsqrtd.ext <;> simp [hReal]
    rw [hStar, mul_neg] at hProd
    have hSquare : z^2 = -1 := by
      rw [pow_two]
      exact neg_eq_iff_eq_neg.mp hProd
    rw [hSquare]
    norm_num
  · have hStar : star z = z := by
      apply Zsqrtd.ext <;> simp [hImag]
    rw [hStar] at hProd
    rw [pow_two z, hProd]
    norm_num

private theorem gaussian_odd_root_of_unit (u : GaussianIntˣ) {j : ℕ} (hj : Odd j) :
    (((u : GaussianInt)^j)^j) = (u : GaussianInt) := by
  have hFourth := gaussian_unit_fourth u.isUnit
  obtain ⟨k, hk⟩ := hj
  have hSquare : j * j = 4 * (k * (k + 1)) + 1 := by
    rw [hk]
    ring
  calc
    _ = (u : GaussianInt)^(j * j) := (pow_mul _ _ _).symm
    _ = ((u : GaussianInt)^4)^(k * (k + 1)) * (u : GaussianInt) := by
      rw [hSquare, pow_add, pow_mul, pow_one]
    _ = _ := by rw [hFourth, one_pow, one_mul]

private theorem gaussian_exact_odd_power {n y j : ℕ} (hn : Even n) (hj : Odd j)
    (hEq : n^2 + 1 = y^j) :
    ∃ z : GaussianInt, z^j = (n : GaussianInt) + gaussianI := by
  let _ : GCDMonoid GaussianInt := EuclideanDomain.gcdMonoid GaussianInt
  have hISq : gaussianI^2 = (-1 : GaussianInt) := by decide +kernel
  have hProd : ((n : GaussianInt) + gaussianI) * ((n : GaussianInt) - gaussianI) =
      (y : GaussianInt)^j := by
    calc
      _ = (n : GaussianInt)^2 - gaussianI^2 := by ring
      _ = _ := by
        rw [hISq, sub_neg_eq_add]
        simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using
          congrArg (fun k : ℕ => (k : GaussianInt)) hEq
  have hGcd : IsUnit (gcd ((n : GaussianInt) + gaussianI) ((n : GaussianInt) - gaussianI)) := by
    apply isUnit_of_dvd_one
    obtain ⟨u, v, huv⟩ := gaussian_conjugates_coprime n hn
    rw [← huv]
    exact dvd_add (dvd_mul_of_dvd_right (gcd_dvd_left _ _) _)
      (dvd_mul_of_dvd_right (gcd_dvd_right _ _) _)
  obtain ⟨w, u, hu⟩ := exists_associated_pow_of_mul_eq_pow hGcd hProd
  refine ⟨w * (u : GaussianInt)^j, ?_⟩
  rw [mul_pow, gaussian_odd_root_of_unit u hj]
  exact hu

private theorem gaussian_im_dvd_im_pow (z : GaussianInt) (j : ℕ) : z.im ∣ (z^j).im := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Zsqrtd.im_mul]
    exact dvd_add (dvd_mul_of_dvd_right (dvd_refl _) _) (dvd_mul_of_dvd_left ih _)

/-- Coprimality gives a Gaussian power up to a unit. Since its exponent is
odd, that unit can be absorbed before reading the imaginary coordinate. -/
private theorem oddPowerImaginaryUnit :
    ∀ n y j : ℕ, 0 < n → Even n → 3 ≤ j → Odd j → n^2+1 = y^j → ∃ a : ℤ, a ≠ 0 ∧ Even a ∧ Int.natAbs (((⟨a,1⟩ : GaussianInt)^j).im) = 1 := by
  intro n y j hnPos hn hj3 hj hEq
  obtain ⟨z, hz⟩ := gaussian_exact_odd_power hn hj hEq
  have hIm : ((n : GaussianInt) + gaussianI).im = 1 := by
    change (0 : ℤ) + 1 = 1
    norm_num
  have hDvd := gaussian_im_dvd_im_pow z j
  rw [hz, hIm] at hDvd
  have hSign : z.im = 1 ∨ z.im = -1 := Int.isUnit_iff.mp (isUnit_of_dvd_one hDvd)
  have hImSq : z.im^2 = 1 := by
    rcases hSign with h | h <;> norm_num [h]
  have hNorm : z.norm^j = (n : ℤ)^2 + 1 := by
    calc
      _ = (z^j).norm := (map_pow (Zsqrtd.normMonoidHom (d := (-1 : ℤ))) z j).symm
      _ = _ := by
        rw [hz, gaussian_norm_formula]
        change ((n : ℤ) + 0)^2 + ((0 : ℤ) + 1)^2 = _
        norm_num
  have hRealNe : z.re ≠ 0 := by
    intro h
    have hUnitNorm : z.norm = 1 := by rw [gaussian_norm_formula, h, hImSq]; norm_num
    have hnIntPos : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hnPos
    rw [hUnitNorm, one_pow] at hNorm
    nlinarith only [hNorm, sq_pos_of_ne_zero hnIntPos.ne']
  have hRealEven : Even z.re := by
    by_contra hEven
    have hOdd : Odd z.re := Int.not_even_iff_odd.mp hEven
    have hNormEven : Even z.norm := by
      rw [gaussian_norm_formula, hImSq]
      exact (hOdd.pow (n := 2)).add_odd odd_one
    have hPowerEven : Even (z.norm^j) := hNormEven.pow_of_ne_zero (by omega)
    have hNEven : Even (n : ℤ) := (Int.even_natCast n).mpr hn
    have hNormOdd : Odd ((n : ℤ)^2 + 1) :=
      (hNEven.pow_of_ne_zero (by decide : (2 : ℕ) ≠ 0)).add_odd odd_one
    rw [hNorm] at hPowerEven
    exact (Int.not_even_iff_odd.mpr hNormOdd) hPowerEven
  refine ⟨z.re, hRealNe, hRealEven, ?_⟩
  rcases hSign with hPos | hNeg
  · have hZ : (⟨z.re, 1⟩ : GaussianInt) = z := by
      apply Zsqrtd.ext
      · rfl
      · exact hPos.symm
    rw [hZ, hz, hIm]
    decide
  · have hZ : (⟨z.re, 1⟩ : GaussianInt) = star z := by
      apply Zsqrtd.ext
      · rfl
      · simp [hNeg]
    rw [hZ, ← star_pow, hz, Zsqrtd.im_star, hIm]
    decide


end QuadraticMangoldtProof

namespace QuadraticMangoldtProof

open Finset

private theorem self_le_choose_two {n : ℕ} (hn : 3 ≤ n) : n ≤ n.choose 2 := by
  rw [Nat.choose_two_right]
  exact (Nat.le_div_iff_mul_le (by decide : 0 < (2 : ℕ))).mpr
    (Nat.mul_le_mul_left n (by omega))

private theorem choose_two_lt_binary_power {n : ℕ} (hn : 6 ≤ n) :
    n.choose 2 < (2 : ℕ)^(n - 2) := by
  induction n, hn using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
      have hNext : (n + 1).choose 2 = n + n.choose 2 := by
        simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' n 1
      have hShift : n + 1 - 2 = (n - 2) + 1 := by omega
      rw [hNext, hShift, pow_succ]
      have hSize := self_le_choose_two (n := n) (by omega)
      omega

private theorem multiplicity_choose_two_le_gap {r : ℕ} (hr : 3 ≤ r) :
    multiplicity (2 : ℕ) (r.choose 2) ≤ r - 3 := by
  have hChoose : 0 < r.choose 2 := Nat.choose_pos (by omega)
  have hNo : ¬ (2 : ℕ)^(r - 2) ∣ r.choose 2 := by
    by_cases hLarge : 6 ≤ r
    · intro h
      exact (not_le_of_gt (choose_two_lt_binary_power hLarge)) (Nat.le_of_dvd hChoose h)
    · interval_cases r <;> decide +kernel
  have hNot : ¬ r - 2 ≤ multiplicity (2 : ℕ) (r.choose 2) := fun h =>
    hNo ((Nat.pow_dvd_iff_le_multiplicity (by decide : (2 : ℕ) ≠ 1) hChoose.ne').mpr h)
  omega

private theorem multiplicity_binomial_compare {j r : ℕ} (hThree : 3 ≤ r) (hRange : r ≤ j) :
    multiplicity (2 : ℕ) (j.choose 2) ≤ multiplicity (2 : ℕ) (j.choose r) + (r - 3) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hChooseR : j.choose r ≠ 0 := (Nat.choose_pos hRange).ne'
  have hChooseR2 : r.choose 2 ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hChooseJ2 : j.choose 2 ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hChoosePart : (j - 2).choose (r - 2) ≠ 0 :=
    (Nat.choose_pos (Nat.sub_le_sub_right hRange 2)).ne'
  have hIdentity := congrArg (multiplicity (2 : ℕ))
    (Nat.choose_mul (n := j) (k := r) (s := 2) (by omega))
  rw [Nat.multiplicity_mul hChooseR hChooseR2, Nat.multiplicity_mul hChooseJ2 hChoosePart] at hIdentity
  have hGap := multiplicity_choose_two_le_gap hThree
  omega

private noncomputable def leadingMultiplicity (a : ℤ) (j : ℕ) : ℕ :=
  multiplicity (2 : ℕ) (j.choose 2) + 2 * multiplicity (2 : ℕ) a.natAbs

private theorem higher_binomial_divisibility {a : ℤ} {j r : ℕ}
    (ha : a ≠ 0) (hEven : Even a) (hThree : 3 ≤ r) (hRange : r ≤ j) :
    (2 : ℤ)^(leadingMultiplicity a j + 1) ∣ a^r * (j.choose r : ℤ) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAbs : a.natAbs ≠ 0 := by simpa using ha
  have hEvenAbs : 2 ∣ a.natAbs := Int.natCast_dvd.mp (even_iff_two_dvd.mp hEven)
  have hV : 1 ≤ multiplicity (2 : ℕ) a.natAbs := one_le_multiplicity_of_dvd hAbs hEvenAbs
  have hChoose : j.choose r ≠ 0 := (Nat.choose_pos hRange).ne'
  have hSplit : r * multiplicity (2 : ℕ) a.natAbs =
      2 * multiplicity (2 : ℕ) a.natAbs + (r - 2) * multiplicity (2 : ℕ) a.natAbs := by
    rw [← add_mul]
    rw [show 2 + (r - 2) = r by omega]
  have hPow : r - 2 ≤ (r - 2) * multiplicity (2 : ℕ) a.natAbs := by
    simpa only [mul_one] using Nat.mul_le_mul_left (r - 2) hV
  have hComp := multiplicity_binomial_compare hThree hRange
  have hVal : leadingMultiplicity a j + 1 ≤ multiplicity (2 : ℕ) (a.natAbs^r * j.choose r) := by
    rw [leadingMultiplicity, Nat.multiplicity_mul (pow_ne_zero _ hAbs) hChoose,
      Nat.multiplicity_pow, hSplit]
    omega
  change (((2 : ℕ) : ℤ))^(leadingMultiplicity a j + 1) ∣ a^r * (j.choose r : ℤ)
  rw [← Nat.cast_pow, Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  exact (multiplicity_dvd_iff_le (mul_ne_zero (pow_ne_zero _ hAbs) hChoose)).mpr hVal

private def gaussianUnitI : GaussianInt := ⟨0, 1⟩

private theorem gaussian_i_square :
    gaussianUnitI^2 = ((-1 : ℤ) : GaussianInt) := by decide +kernel

private theorem gaussian_i_even_im (k : ℕ) :
    (gaussianUnitI^(2 * k)).im = 0 := by
  rw [pow_mul, gaussian_i_square, ← Int.cast_pow, Zsqrtd.im_intCast]

private theorem gaussian_i_odd_im (k : ℕ) :
    (gaussianUnitI^(2 * k + 1)).im = (-1 : ℤ)^k := by
  rw [pow_add, pow_one, pow_mul, gaussian_i_square, ← Int.cast_pow, Zsqrtd.im_mul]
  change (-1 : ℤ)^k * 1 + 0 * 0 = (-1 : ℤ)^k
  simp

private def gaussianImaginary : GaussianInt →+ ℤ where
  toFun z := z.im
  map_zero' := rfl
  map_add' _ _ := rfl

private def imaginaryBinomialTerm (a : ℤ) (j r : ℕ) : ℤ :=
  (gaussianUnitI^(j - r)).im * (a^r * (j.choose r : ℤ))

private theorem imaginary_binomial (a : ℤ) (j : ℕ) :
    ((⟨a, 1⟩ : GaussianInt)^j).im = ∑ r ∈ range (j + 1), imaginaryBinomialTerm a j r := by
  have hAdd : (a : GaussianInt) + gaussianUnitI = (⟨a, 1⟩ : GaussianInt) := by
    apply Zsqrtd.ext <;> simp [gaussianUnitI]
  change gaussianImaginary ((⟨a, 1⟩ : GaussianInt)^j) = _
  rw [← hAdd, add_pow, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  change (((a : GaussianInt)^r * gaussianUnitI^(j - r) *
    (j.choose r : GaussianInt)).im) = _
  rw [← Int.cast_pow]
  simp only [imaginaryBinomialTerm, Zsqrtd.im_mul, Zsqrtd.im_natCast, Zsqrtd.re_natCast,
    Zsqrtd.im_intCast, Zsqrtd.re_intCast, zero_mul, mul_zero, zero_add, add_zero]
  ring

private theorem two_power_dvd_nat_abs (x : ℤ) (t : ℕ) :
    (2 : ℤ)^t ∣ x ↔ (2 : ℕ)^t ∣ x.natAbs := by
  change (((2 : ℕ) : ℤ)^t ∣ x) ↔ _
  rw [← Nat.cast_pow, Int.natCast_dvd]

private theorem multiplicity_of_leading_term {lead rest : ℤ} {t : ℕ}
    (hLead : lead.natAbs ≠ 0) (hVal : multiplicity (2 : ℕ) lead.natAbs = t)
    (hTail : (2 : ℤ)^(t + 1) ∣ rest) :
    lead + rest ≠ 0 ∧ multiplicity (2 : ℕ) (lead + rest).natAbs = t := by
  have hLeadExact (k : ℕ) : (2 : ℤ)^k ∣ lead ↔ k ≤ t := by
    rw [two_power_dvd_nat_abs, Nat.pow_dvd_iff_le_multiplicity (by decide : (2 : ℕ) ≠ 1) hLead, hVal]
  have hNot : ¬ (2 : ℤ)^(t + 1) ∣ lead + rest := by
    intro h
    have hDvd := dvd_sub h hTail
    rw [add_sub_cancel_right] at hDvd
    exact (Nat.not_succ_le_self t) ((hLeadExact (t + 1)).mp hDvd)
  have hNZ : lead + rest ≠ 0 := by
    intro h
    exact hNot (h.symm ▸ dvd_zero _)
  have hAbs : (lead + rest).natAbs ≠ 0 := by simpa using hNZ
  have hSumExact (k : ℕ) :
      (2 : ℤ)^k ∣ lead + rest ↔ k ≤ multiplicity (2 : ℕ) (lead + rest).natAbs := by
    rw [two_power_dvd_nat_abs, Nat.pow_dvd_iff_le_multiplicity (by decide : (2 : ℕ) ≠ 1) hAbs]
  have hPowDvd : (2 : ℤ)^t ∣ (2 : ℤ)^(t + 1) := ⟨2, pow_succ _ _⟩
  have hlo := (hSumExact t).mp (dvd_add ((hLeadExact t).mpr le_rfl) (hPowDvd.trans hTail))
  have hhi : ¬ t + 1 ≤ multiplicity (2 : ℕ) (lead + rest).natAbs := fun h =>
    hNot ((hSumExact (t + 1)).mpr h)
  exact ⟨hNZ, by omega⟩

/-- Higher binomial terms have an extra factor of two after accounting for
the first nonconstant term. This gives the exact valuation of the difference. -/
private theorem binomialImaginaryTwoAdicGap :
    ∀ (a : ℤ) (j : ℕ), a ≠ 0 → Even a → Odd j → 3 ≤ j → let d := ((⟨a,1⟩ : GaussianInt)^j).im - (-1 : ℤ)^((j-1)/2); d ≠ 0 ∧ padicValNat 2 d.natAbs = padicValNat 2 (j.choose 2) + 2 * padicValNat 2 a.natAbs := by
  intro a j ha hEven hj hj3
  let d : ℤ := ((⟨a, 1⟩ : GaussianInt)^j).im - (-1 : ℤ)^((j - 1) / 2)
  obtain ⟨k, hk⟩ := hj
  have hI0 : (gaussianUnitI^j).im = (-1 : ℤ)^((j - 1) / 2) := by
    have ht : (j - 1) / 2 = k := by omega
    rw [ht, hk]
    exact gaussian_i_odd_im k
  have hI1 : (gaussianUnitI^(j - 1)).im = 0 := by
    rw [show j - 1 = 2 * k by omega]
    exact gaussian_i_even_im k
  have hI2 : (gaussianUnitI^(j - 2)).im = (-1 : ℤ)^(k - 1) := by
    rw [show j - 2 = 2 * (k - 1) + 1 by omega]
    exact gaussian_i_odd_im (k - 1)
  have hZero : imaginaryBinomialTerm a j 0 = (-1 : ℤ)^((j - 1) / 2) := by
    simp [imaginaryBinomialTerm, hI0]
  have hOne : imaginaryBinomialTerm a j 1 = 0 := by
    simp [imaginaryBinomialTerm, hI1]
  have hSmall : (∑ r ∈ range 3, imaginaryBinomialTerm a j r) =
      (-1 : ℤ)^((j - 1) / 2) + imaginaryBinomialTerm a j 2 := by
    norm_num [Finset.sum_range_succ, hZero, hOne]
  have hDecomp : d = imaginaryBinomialTerm a j 2 +
      ∑ r ∈ Ico 3 (j + 1), imaginaryBinomialTerm a j r := by
    dsimp only [d]
    rw [imaginary_binomial,
      ← Finset.sum_range_add_sum_Ico (imaginaryBinomialTerm a j) (show 3 ≤ j + 1 by omega),
      hSmall]
    ring
  have hLeadAbs : (imaginaryBinomialTerm a j 2).natAbs = a.natAbs^2 * j.choose 2 := by
    simp [imaginaryBinomialTerm, hI2, Int.natAbs_mul, Int.natAbs_pow]
  have hAbsA : a.natAbs ≠ 0 := by simpa using ha
  have hChoose : j.choose 2 ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hLead : (imaginaryBinomialTerm a j 2).natAbs ≠ 0 := by
    rw [hLeadAbs]
    exact mul_ne_zero (pow_ne_zero _ hAbsA) hChoose
  have hVal : multiplicity (2 : ℕ) (imaginaryBinomialTerm a j 2).natAbs =
      leadingMultiplicity a j := by
    let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [hLeadAbs, Nat.multiplicity_mul (pow_ne_zero _ hAbsA) hChoose,
      Nat.multiplicity_pow, leadingMultiplicity]
    omega
  have hTail : (2 : ℤ)^(leadingMultiplicity a j + 1) ∣
      ∑ r ∈ Ico 3 (j + 1), imaginaryBinomialTerm a j r := by
    apply Finset.dvd_sum
    intro r hr
    obtain ⟨hrLo, hrHi⟩ := mem_Ico.mp hr
    exact dvd_mul_of_dvd_right (higher_binomial_divisibility ha hEven hrLo (by omega)) _
  simp only [Nat.padicValNat_def]
  change d ≠ 0 ∧ multiplicity (2 : ℕ) d.natAbs = leadingMultiplicity a j
  rw [hDecomp]
  exact multiplicity_of_leading_term hLead hVal hTail


end QuadraticMangoldtProof

namespace QuadraticPrimePowerReduction

private theorem gaussian_imaginary_mod_four (a : ℤ) (ha : Even a) (k : ℕ) :
    ((⟨a,1⟩ : GaussianInt) ^ (2*k+1)).im ≡ (-1 : ℤ)^k [ZMOD 4] := by
  let z : GaussianInt := ⟨a,1⟩
  obtain ⟨t, ht⟩ := ha
  have hr : (z^2).re ≡ -1 [ZMOD 4] := by
    change (z^2).re % 4 = (-1) % 4
    have heq : (z^2).re = 4*t^2-1 := by
      simp [z, pow_two, Zsqrtd.re_mul, ht]
      ring
    omega
  have hi : (z^2).im ≡ 0 [ZMOD 4] := by
    change (z^2).im % 4 = 0 % 4
    have heq : (z^2).im = 4*t := by
      simp [z, pow_two, Zsqrtd.im_mul, ht]
      ring
    omega
  change (z^(2*k+1)).im ≡ _ [ZMOD 4]
  induction k with
  | zero => simp [z, Int.ModEq]
  | succ k ih =>
    have hpow : z^(2*(k+1)+1) = z^(2*k+1)*z^2 := by
      rw [← pow_add]
      congr 1
    rw [hpow, Zsqrtd.im_mul]
    simpa [pow_succ] using ((Int.ModEq.refl ((z^(2*k+1)).re)).mul hi).add (ih.mul hr)

theorem gaussian_imaginary_eq_sign {a : ℤ} {j : ℕ} (ha : Even a) (hj : Odd j)
    (hab : ((⟨a,1⟩ : GaussianInt)^j).im.natAbs = 1) :
    ((⟨a,1⟩ : GaussianInt)^j).im = (-1 : ℤ)^((j-1)/2) := by
  obtain ⟨k, hk⟩ := hj
  have hj' : (j-1)/2 = k := by omega
  rw [hj', hk]
  have ht : ((⟨a,1⟩ : GaussianInt)^(2*k+1)).im ≡ (-1 : ℤ)^k [ZMOD 4] :=
    gaussian_imaginary_mod_four a ha k
  rw [hk] at hab
  generalize ((⟨a,1⟩ : GaussianInt)^(2*k+1)).im = m at hab ht ⊢
  have hm : m = 1 ∨ m = -1 := by omega
  have hs : (-1 : ℤ)^k = 1 ∨ (-1 : ℤ)^k = -1 := by
    rw [neg_one_pow_eq_ite]
    split_ifs <;> simp
  rcases hm with hm | hm <;> rcases hs with hs | hs <;>
    rw [hm, hs] at ht ⊢ <;> norm_num [Int.ModEq] at ht

private theorem not_odd_input_power {n y j : ℕ} (hn : Odd n) (hj : 2 ≤ j) :
    n^2+1 ≠ y^j := by
  intro h
  have hn4 : (n^2+1)%4 = 2 := by
    obtain ⟨t,ht⟩ := hn
    have heq : n^2+1 = 4*(t^2+t)+2 := by rw [ht]; ring
    omega
  have hy : Even y := by
    by_contra hy
    have hOdd : Odd (y^j) := (Nat.not_even_iff_odd.mp hy).pow
    have hEven : Even (y^j) := ⟨y^j/2, by omega⟩
    exact (Nat.not_even_iff_odd.mpr hOdd) hEven
  obtain ⟨t,ht⟩ := hy
  have hdiv : 4 ∣ y^2 := ⟨t^2, by rw [ht]; ring⟩
  have hdiv' : 4 ∣ y^j := hdiv.trans (pow_dvd_pow y hj)
  rw [← h] at hdiv'
  have hm := Nat.mod_eq_zero_of_dvd hdiv'
  omega

private theorem not_even_exponent_power {n y j : ℕ} (hn : 0 < n) (hj : Even j) :
    n^2+1 ≠ y^j := by
  intro h
  obtain ⟨k,hk⟩ := hj
  have heq : y^j = (y^k)^2 := by rw [hk, ← two_mul, mul_comm 2 k, pow_mul]
  rw [heq] at h
  have hlt : n < y^k := by
    by_contra! hl
    have hpow := pow_le_pow_left' hl 2
    omega
  have hle := pow_le_pow_left' (show n+1 ≤ y^k by omega) 2
  nlinarith

private theorem exact_support_of_gaussian
    (root : ∀ n y j : ℕ, 0 < n → Even n → 3 ≤ j → Odd j → n^2+1 = y^j →
      ∃ a : ℤ, a ≠ 0 ∧ Even a ∧ Int.natAbs (((⟨a,1⟩ : GaussianInt)^j).im) = 1)
    (imaginary_gap : ∀ (a : ℤ) (j : ℕ), a ≠ 0 → Even a → Odd j → 3 ≤ j →
      ((⟨a,1⟩ : GaussianInt)^j).im - (-1 : ℤ)^((j-1)/2) ≠ 0) :
    ∀ n : ℕ, 0<n → ArithmeticFunction.vonMangoldt (n^2+1) =
      if (n^2+1).Prime then Real.log (n^2+1) else 0 := by
  intro n hn
  split_ifs with hp
  · simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using ArithmeticFunction.vonMangoldt_apply_prime hp
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
    intro hpow
    obtain ⟨p,j, hPrime,hj, heq⟩ := (isPrimePow_nat_iff _).mp hpow
    have hne : j ≠ 1 := by
      intro hj1
      rw [hj1, pow_one] at heq
      exact hp (heq ▸ hPrime)
    have htwo : 2 ≤ j := by omega
    have hnEven : Even n := by
      by_contra hnot
      exact not_odd_input_power (Nat.not_even_iff_odd.mp hnot) htwo heq.symm
    have hjOdd : Odd j := by
      by_contra hnot
      exact not_even_exponent_power hn (Nat.not_odd_iff_even.mp hnot) heq.symm
    have hthree : 3 ≤ j := by
      have hmod := Nat.odd_iff.mp hjOdd
      omega
    obtain ⟨a, ha, hae, haim⟩ := root n p j hn hnEven hthree hjOdd heq.symm
    exact (imaginary_gap a j ha hae hjOdd hthree) (sub_eq_zero.mpr (gaussian_imaginary_eq_sign hae hjOdd haim))


end QuadraticPrimePowerReduction

theorem Conjectures.QuadraticPrimes.QuadraticMangoldtExactSupport :
    (∀ n : ℕ, 0 < n → ArithmeticFunction.vonMangoldt (n^2+1) = if (n^2+1).Prime then Real.log (n^2+1) else 0) := by
  refine QuadraticPrimePowerReduction.exact_support_of_gaussian
    QuadraticMangoldtProof.oddPowerImaginaryUnit ?_
  intro a j ha hEven hOdd hThree
  exact (QuadraticMangoldtProof.binomialImaginaryTwoAdicGap a j ha hEven hOdd hThree).1
