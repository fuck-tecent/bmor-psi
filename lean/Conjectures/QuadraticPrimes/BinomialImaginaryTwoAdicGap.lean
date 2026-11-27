import Mathlib

open Finset

namespace Conjectures.QuadraticPrimes.BinomialImaginaryTwoAdicGap_aux

lemma im_sum_zsqrtd {d : ℤ} (s : Finset ℕ) (f : ℕ → Zsqrtd d) :
    (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, Zsqrtd.im_add, ih]

lemma im_I_pow (n : ℕ) :
    ((⟨0,1⟩ : GaussianInt)^n).im = if Odd n then (-1 : ℤ)^((n-1)/2) else 0 := by
  have hsq : ((⟨0,1⟩ : GaussianInt)^2) = ⟨-1, 0⟩ := by
    ext
    · rw [pow_two, Zsqrtd.re_mul]; norm_num
    · rw [pow_two, Zsqrtd.im_mul]; norm_num
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih0 ih1 =>
    have hstep : ((⟨0,1⟩ : GaussianInt)^(n+2)).im = -(((⟨0,1⟩ : GaussianInt)^n).im) := by
      rw [pow_add, hsq, Zsqrtd.im_mul]
      simp
    rw [hstep, ih0]
    by_cases hn : Odd n
    · rcases hn with ⟨k, rfl⟩
      have hn2 : Odd (2 * k + 1 + 2) := ⟨k + 1, by ring⟩
      have hn1 : Odd (2 * k + 1) := ⟨k, rfl⟩
      simp only [hn2, hn1, ↓reduceIte]
      have hex : (2 * k + 1 + 2 - 1) / 2 = (2 * k + 1 - 1) / 2 + 1 := by omega
      rw [hex, pow_succ]
      ring
    · have hn2 : ¬ Odd (n + 2) := by
        intro h
        apply hn
        rcases h with ⟨k, hk⟩
        refine ⟨k - 1, ?_⟩
        omega
      simp only [hn2, hn, ↓reduceIte, neg_zero]

lemma im_pow_expand (a : ℤ) (j : ℕ) (hj : Odd j) :
    ((⟨a,1⟩ : GaussianInt)^j).im =
      ∑ m ∈ Finset.range (j+1),
        (if Even m then (-1 : ℤ)^((j-m-1)/2) * (j.choose m : ℤ) * a^m else 0) := by
  have hsplit : ((⟨a,1⟩ : GaussianInt)^j) = ((a : GaussianInt) + ⟨0,1⟩)^j := by
    congr 1
    ext <;> simp [Zsqrtd.intCast_val]
  rw [hsplit, add_pow, im_sum_zsqrtd]
  apply Finset.sum_congr rfl
  intro m hm
  have hmm : m ≤ j := by simp at hm; omega
  have hxre : (((a : GaussianInt)^m).re = a^m) := by
    rw [← Int.cast_pow, Zsqrtd.intCast_val]
  have hxim : (((a : GaussianInt)^m).im = 0) := by
    rw [← Int.cast_pow, Zsqrtd.intCast_val]
  rw [Zsqrtd.im_mul, Zsqrtd.im_natCast, Zsqrtd.re_natCast, mul_zero, zero_add,
    Zsqrtd.im_mul, hxre, hxim, zero_mul, add_zero, im_I_pow]
  by_cases hE : Even m
  · have hO : Odd (j - m) := by
      rcases hj with ⟨p, rfl⟩
      rcases hE with ⟨q, rfl⟩
      refine ⟨p - q, ?_⟩
      omega
    simp only [hO, hE, ↓reduceIte]
    ring
  · have hO : ¬ Odd (j - m) := by
      intro h
      apply hE
      rcases hj with ⟨p, rfl⟩
      rcases h with ⟨q, hq⟩
      refine ⟨p - q, ?_⟩
      omega
    simp only [hO, hE, ↓reduceIte]
    ring

lemma choose_pow_dvd (j m : ℕ) (a : ℤ) (hj : 2 ≤ j) (hme : Even m) (hm : 4 ≤ m) (hmj : m ≤ j)
    (ha : a ≠ 0) (hEven : Even a) :
    (2 : ℕ) ^ (padicValNat 2 (j.choose 2) + 2 * padicValNat 2 a.natAbs + 1) ∣
      j.choose m * a.natAbs ^ m := by
  have han : a.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ha
  have ha2 : (2 : ℕ) ∣ a.natAbs := by
    rw [← Int.natCast_dvd]
    exact even_iff_two_dvd.mp hEven
  have hα : 1 ≤ padicValNat 2 a.natAbs := by
    rw [Nat.padicValNat_def]
    have h5 := (Nat.pow_dvd_iff_le_multiplicity (p := 2) (k := 1) (by norm_num) han).mp ha2
    simpa using h5
  obtain ⟨t, rfl⟩ : ∃ t, m = 2 * t := by
    rcases hme with ⟨s, hs⟩
    exact ⟨s, by omega⟩
  have ht : 2 ≤ t := by omega
  have hid : j.choose (2 * t) * (2 * t).choose 2 = j.choose 2 * (j - 2).choose (2 * t - 2) :=
    Nat.choose_mul (by omega)
  have hx0 : j.choose (2 * t) ≠ 0 := Nat.choose_ne_zero (by omega)
  have hm2 : (2 * t).choose 2 ≠ 0 := Nat.choose_ne_zero (by omega)
  have hj2 : j.choose 2 ≠ 0 := Nat.choose_ne_zero (by omega)
  have hres : (j - 2).choose (2 * t - 2) ≠ 0 := Nat.choose_ne_zero (by omega)
  have hch : (2 * t).choose 2 = t * (2 * t - 1) := by
    rw [Nat.choose_two_right]
    have h3 : 2 * t * (2 * t - 1) = 2 * (t * (2 * t - 1)) := by ring
    rw [h3, Nat.mul_div_cancel_left _ (by norm_num)]
  have hodd : ¬ (2 : ℕ) ∣ 2 * t - 1 := by omega
  have hval1 : multiplicity 2 (j.choose (2 * t)) + multiplicity 2 ((2 * t).choose 2)
      = multiplicity 2 (j.choose 2) + multiplicity 2 ((j - 2).choose (2 * t - 2)) := by
    have h4 := congrArg (multiplicity 2) hid
    rwa [Nat.multiplicity_mul hx0 hm2, Nat.multiplicity_mul hj2 hres] at h4
  have hval2 : multiplicity 2 ((2 * t).choose 2) = multiplicity 2 t := by
    rw [hch, Nat.multiplicity_mul (by omega) (by omega),
      multiplicity_eq_zero_of_not_dvd hodd, add_zero]
  have hkey : multiplicity 2 (j.choose 2) ≤
      multiplicity 2 (j.choose (2 * t)) + multiplicity 2 t := by
    rw [← hval2]
    omega
  have hvle : multiplicity 2 t + 1 ≤ t := by
    have hp : 2 ^ multiplicity 2 t ∣ t := pow_multiplicity_dvd 2 t
    have hle : 2 ^ multiplicity 2 t ≤ t := Nat.le_of_dvd (by omega) hp
    have hlt : multiplicity 2 t < 2 ^ multiplicity 2 t := Nat.lt_two_pow_self
    omega
  have h1 : t ≤ t * padicValNat 2 a.natAbs := by
    calc t = t * 1 := (Nat.mul_one t).symm
      _ ≤ t * padicValNat 2 a.natAbs := Nat.mul_le_mul_left t hα
  have h2 : 2 * padicValNat 2 a.natAbs ≤ t * padicValNat 2 a.natAbs :=
    Nat.mul_le_mul_right (padicValNat 2 a.natAbs) ht
  have hfin : multiplicity 2 t + 2 * padicValNat 2 a.natAbs + 1 ≤
      2 * (t * padicValNat 2 a.natAbs) := by omega
  have htotal : multiplicity 2 (j.choose (2 * t) * a.natAbs ^ (2 * t))
      = multiplicity 2 (j.choose (2 * t)) + 2 * (t * padicValNat 2 a.natAbs) := by
    rw [Nat.multiplicity_mul hx0 (by positivity), Nat.multiplicity_pow, Nat.padicValNat_def]
    ring
  rw [Nat.pow_dvd_iff_le_multiplicity (by norm_num) (by positivity), htotal,
    Nat.padicValNat_def]
  have h5 : multiplicity 2 (j.choose 2) + 2 * padicValNat 2 a.natAbs + 1 ≤
      multiplicity 2 (j.choose (2 * t)) + 2 * (t * padicValNat 2 a.natAbs) := by omega
  exact h5

end Conjectures.QuadraticPrimes.BinomialImaginaryTwoAdicGap_aux

theorem Conjectures.QuadraticPrimes.BinomialImaginaryTwoAdicGap :
    ∀ (a : ℤ) (j : ℕ), a ≠ 0 → Even a → Odd j → 3 ≤ j → let d := ((⟨a,1⟩ : GaussianInt)^j).im - (-1 : ℤ)^((j-1)/2); d ≠ 0 ∧ padicValNat 2 d.natAbs = padicValNat 2 (j.choose 2) + 2 * padicValNat 2 a.natAbs := by
  intro a j ha hEven hOdd hj
  dsimp only
  set E := padicValNat 2 (j.choose 2) + 2 * padicValNat 2 a.natAbs with hE
  set d := ((⟨a,1⟩ : GaussianInt)^j).im - (-1 : ℤ)^((j-1)/2) with hd_def
  set g : ℕ → ℤ := fun m => if Even m then (-1 : ℤ)^((j-m-1)/2) * (j.choose m : ℤ) * a^m else 0
    with hg_def
  have hg : ∀ m, g m = if Even m then (-1 : ℤ)^((j-m-1)/2) * (j.choose m : ℤ) * a^m else 0 :=
    fun m => rfl
  have hexp : ((⟨a,1⟩ : GaussianInt)^j).im = ∑ m ∈ Finset.range (j+1), g m := by
    rw [Conjectures.QuadraticPrimes.BinomialImaginaryTwoAdicGap_aux.im_pow_expand a j hOdd]
  have hg0 : g 0 = (-1 : ℤ)^((j-1)/2) := by
    rw [hg]; simp
  have h0mem : (0 : ℕ) ∈ Finset.range (j+1) := Finset.mem_range.mpr (by omega)
  have hd1 : d = ∑ m ∈ (Finset.range (j+1)).erase 0, g m := by
    rw [hd_def, hexp, ← Finset.add_sum_erase _ _ h0mem, hg0]
    ring
  have h2mem : (2 : ℕ) ∈ (Finset.range (j+1)).erase 0 :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
  have hd2 : d = g 2 + ∑ m ∈ ((Finset.range (j+1)).erase 0).erase 2, g m := by
    rw [hd1]
    exact (Finset.add_sum_erase _ _ h2mem).symm
  have hEv2 : Even (2 : ℕ) := ⟨1, rfl⟩
  have hT : g 2 = (-1 : ℤ)^((j-3)/2) * (j.choose 2 : ℤ) * a^2 := by
    rw [hg]
    simp only [hEv2, ↓reduceIte]
    have h6 : (j - 2 - 1) / 2 = (j - 3) / 2 := by omega
    rw [h6]
  have hTnat : (g 2).natAbs = j.choose 2 * a.natAbs ^ 2 := by
    rw [hT]; simp [Int.natAbs_mul, Int.natAbs_pow]
  have hcho : j.choose 2 ≠ 0 := Nat.choose_ne_zero (by omega)
  have hapow : a.natAbs ^ 2 ≠ 0 := pow_ne_zero 2 (Int.natAbs_ne_zero.mpr ha)
  have hTval : padicValNat 2 (g 2).natAbs = E := by
    rw [hE, hTnat]
    simp only [Nat.padicValNat_def]
    rw [Nat.multiplicity_mul hcho hapow, Nat.multiplicity_pow]
  have hTne : (g 2).natAbs ≠ 0 := by
    rw [hTnat]; exact mul_ne_zero hcho hapow
  have hTdvd : ((2 : ℕ) ^ E : ℤ) ∣ g 2 := by
    refine (Int.natCast_dvd).mpr ?_
    exact (Nat.pow_dvd_iff_le_multiplicity (by norm_num) hTne).mpr
      (by rw [← Nat.padicValNat_def, hTval])
  have hTndvd : ¬ ((2 : ℕ) ^ (E+1) : ℤ) ∣ g 2 := by
    intro h
    have h1 : (2 : ℕ) ^ (E+1) ∣ (g 2).natAbs := (Int.natCast_dvd).mp h
    have h2 : E + 1 ≤ multiplicity 2 (g 2).natAbs :=
      (Nat.pow_dvd_iff_le_multiplicity (by norm_num) hTne).mp h1
    have h3 : multiplicity 2 (g 2).natAbs = E := by rw [← Nat.padicValNat_def, hTval]
    omega
  have hterm : ∀ m ∈ ((Finset.range (j+1)).erase 0).erase 2,
      ((2 : ℕ) ^ (E+1) : ℤ) ∣ g m := by
    intro m hm
    have hmS : m ∈ (Finset.range (j+1)).erase 0 := Finset.mem_of_mem_erase hm
    have hm2 : m ≠ 2 := (Finset.mem_erase.mp hm).1
    have hm0 : m ≠ 0 := (Finset.mem_erase.mp hmS).1
    have hmr : m ≤ j := by
      have h5 := (Finset.mem_erase.mp hmS).2
      simp only [Finset.mem_range] at h5
      omega
    by_cases hEm : Even m
    · have hm4 : 4 ≤ m := by
        rcases hEm with ⟨q, hq⟩
        omega
      have hnat := Conjectures.QuadraticPrimes.BinomialImaginaryTwoAdicGap_aux.choose_pow_dvd j m a (by omega) hEm hm4 hmr ha hEven
      have hgm : g m = (-1 : ℤ)^((j-m-1)/2) * (j.choose m : ℤ) * a^m := by
        rw [hg]; simp [hEm]
      have hna : ((-1 : ℤ)^((j-m-1)/2) * (j.choose m : ℤ) * a^m).natAbs
          = j.choose m * a.natAbs ^ m := by
        simp [Int.natAbs_mul, Int.natAbs_pow]
      rw [hgm]
      refine (Int.natCast_dvd).mpr ?_
      rw [hna]
      exact hnat
    · have hgm : g m = 0 := by
        rw [hg]; simp [hEm]
      rw [hgm]
      exact dvd_zero _
  have hR : ((2 : ℕ) ^ (E+1) : ℤ) ∣ ∑ m ∈ ((Finset.range (j+1)).erase 0).erase 2, g m :=
    Finset.dvd_sum (fun m hm => hterm m hm)
  have hstep : ((2 : ℕ) ^ E : ℤ) ∣ ((2 : ℕ) ^ (E+1) : ℤ) := by
    refine (Int.natCast_dvd).mpr ?_
    simpa using pow_dvd_pow 2 (Nat.le_succ E)
  have hddvd : ((2 : ℕ) ^ E : ℤ) ∣ d := by
    rw [hd2]
    exact dvd_add hTdvd (dvd_trans hstep hR)
  have hdndvd : ¬ ((2 : ℕ) ^ (E+1) : ℤ) ∣ d := by
    intro h
    apply hTndvd
    have hsub : ((2 : ℕ) ^ (E+1) : ℤ) ∣
        d - ∑ m ∈ ((Finset.range (j+1)).erase 0).erase 2, g m := dvd_sub h hR
    rw [hd2, add_sub_cancel_right] at hsub
    exact hsub
  have hd0 : d ≠ 0 := by
    intro h
    apply hdndvd
    rw [h]
    exact dvd_zero _
  have hfinal : padicValNat 2 d.natAbs = E := by
    have hne : d.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hd0
    have hge : E ≤ multiplicity 2 d.natAbs :=
      (Nat.pow_dvd_iff_le_multiplicity (by norm_num) hne).mp ((Int.natCast_dvd).mp hddvd)
    have hlt : ¬ (E + 1 ≤ multiplicity 2 d.natAbs) := by
      intro h
      exact hdndvd ((Int.natCast_dvd).mpr
        ((Nat.pow_dvd_iff_le_multiplicity (by norm_num) hne).mpr h))
    rw [Nat.padicValNat_def]
    omega
  exact ⟨hd0, hfinal⟩
