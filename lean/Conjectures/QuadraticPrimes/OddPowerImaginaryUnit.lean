import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic

namespace Conjectures.QuadraticPrimes.OddPowerImaginaryUnit_aux

private def Ig : GaussianInt := ⟨0, 1⟩

private lemma Ig_sq : Ig ^ 2 = -1 := by decide

private lemma Ig_pow_odd (j : ℕ) (hj : Odd j) : Ig ^ j = Ig ∨ Ig ^ j = -Ig := by
  rcases hj with ⟨m, rfl⟩
  rw [pow_succ, pow_mul, Ig_sq]
  rcases Nat.even_or_odd m with hm | hm
  · left; rw [Even.neg_one_pow hm, one_mul]
  · right; rw [Odd.neg_one_pow hm, neg_one_mul]

private lemma normPow (z : GaussianInt) (j : ℕ) : (z ^ j).norm = (z.norm) ^ j :=
  map_pow Zsqrtd.normMonoidHom z j

private lemma norm_mk (a b : ℤ) : (⟨a, b⟩ : GaussianInt).norm = a * a + b * b := by
  simp [Zsqrtd.norm_def]

private lemma im_dvd_im_pow (z : GaussianInt) (j : ℕ) : z.im ∣ (z ^ j).im := by
  induction j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Zsqrtd.im_mul]
    exact dvd_add (dvd_mul_left z.im (z ^ k).re) (dvd_mul_of_dvd_left ih z.re)

private lemma mul_xx (n : ℕ) :
    (⟨(n : ℤ), 1⟩ : GaussianInt) * ⟨(n : ℤ), -1⟩ = ((n ^ 2 + 1 : ℕ) : GaussianInt) := by
  ext
  · change (n : ℤ) * (n : ℤ) + (-1) * 1 * (-1) = ((n ^ 2 + 1 : ℕ) : ℤ)
    push_cast
    ring
  · change (n : ℤ) * (-1) + 1 * (n : ℤ) = 0
    ring

private lemma coprime_mk (n : ℤ) (hn : Even n) :
    IsCoprime (⟨n, 1⟩ : GaussianInt) ⟨n, -1⟩ := by
  refine isCoprime_of_dvd _ _ ?_ ?_
  · rintro ⟨h1, -⟩
    have h : (⟨n, 1⟩ : GaussianInt).im = 1 := rfl
    rw [h1] at h
    exact absurd h (by simp)
  · intro z hz _ hd1 hd2
    rw [mem_nonunits_iff] at hz
    have hnx : (⟨n, 1⟩ : GaussianInt).norm = n * n + 1 := by
      have h := norm_mk n 1; norm_num at h; exact h
    have hnorm_x : z.norm ∣ n * n + 1 := by
      have h : z.norm ∣ (⟨n, 1⟩ : GaussianInt).norm := by
        obtain ⟨c, hc⟩ := hd1; rw [hc, Zsqrtd.norm_mul]; exact dvd_mul_right _ _
      rwa [hnx] at h
    have hsub : ((⟨n, 1⟩ : GaussianInt) - ⟨n, -1⟩) = ⟨0, 2⟩ := by ext <;> simp
    have hns : ((⟨n, 1⟩ : GaussianInt) - ⟨n, -1⟩).norm = 4 := by
      rw [hsub]
      have h := norm_mk (0 : ℤ) 2; norm_num at h; exact h
    have h4 : z.norm ∣ 4 := by
      have h : z.norm ∣ ((⟨n, 1⟩ : GaussianInt) - ⟨n, -1⟩).norm := by
        obtain ⟨c, hc⟩ := dvd_sub hd1 hd2; rw [hc, Zsqrtd.norm_mul]; exact dvd_mul_right _ _
      rwa [hns] at h
    obtain ⟨k, hk⟩ := hn
    have h4k : z.norm ∣ 4 * (k * k) := dvd_mul_of_dvd_left h4 _
    have hnk : n * n + 1 = 4 * (k * k) + 1 := by rw [hk]; ring
    rw [hnk] at hnorm_x
    have h1 : z.norm ∣ 1 := by
      have h := dvd_sub hnorm_x h4k
      simpa using h
    exact hz ((Zsqrtd.norm_eq_one_iff' (d := -1) (by norm_num) z).mp
      (Int.eq_one_of_dvd_one (GaussianInt.norm_nonneg z) h1))

private lemma unit_absorb (v : GaussianInt) (hv : IsUnit v) (j : ℕ) (hj : Odd j) :
    ∃ w : GaussianInt, (w ^ j * v = 1 ∨ w ^ j * v = -1) := by
  have hvnorm : v.norm = 1 :=
    (Zsqrtd.norm_eq_one_iff' (d := -1) (by norm_num) v).mpr hv
  have hvsum : v.re * v.re + v.im * v.im = 1 := by
    have h := norm_mk v.re v.im
    rw [h] at hvnorm
    exact hvnorm
  have hre : v.re = -1 ∨ v.re = 0 ∨ v.re = 1 := by
    have h1 : v.re * v.re ≤ 1 := by nlinarith [mul_self_nonneg v.im]
    have h2 : -1 ≤ v.re := by
      by_contra h
      have h' : v.re ≤ -2 := by omega
      nlinarith
    have h3 : v.re ≤ 1 := by
      by_contra h
      have h' : 2 ≤ v.re := by omega
      nlinarith
    omega
  have him : v.im = -1 ∨ v.im = 0 ∨ v.im = 1 := by
    have h1 : v.im * v.im ≤ 1 := by nlinarith [mul_self_nonneg v.re]
    have h2 : -1 ≤ v.im := by
      by_contra h
      have h' : v.im ≤ -2 := by omega
      nlinarith
    have h3 : v.im ≤ 1 := by
      by_contra h
      have h' : 2 ≤ v.im := by omega
      nlinarith
    omega
  rcases hre with hr | hr | hr <;> rcases him with hi | hi | hi
  · exfalso; rw [hr, hi] at hvsum; omega
  · refine ⟨1, Or.inr ?_⟩
    have hv1 : v = -1 := by ext <;> simp [hr, hi]
    rw [hv1, one_pow]; ext <;> simp
  · exfalso; rw [hr, hi] at hvsum; omega
  · refine ⟨Ig, ?_⟩
    have hv1 : v = -Ig := by ext <;> simp [hr, hi, Ig]
    rw [hv1]
    rcases Ig_pow_odd j hj with h | h
    · left; rw [h]; ext <;> simp [Ig]
    · right; rw [h]; ext <;> simp [Ig]
  · exfalso; rw [hr, hi] at hvsum; omega
  · refine ⟨Ig, ?_⟩
    have hv1 : v = Ig := by ext <;> simp [hr, hi, Ig]
    rw [hv1]
    rcases Ig_pow_odd j hj with h | h
    · right; rw [h]; ext <;> simp [Ig]
    · left; rw [h]; ext <;> simp [Ig]
  · exfalso; rw [hr, hi] at hvsum; omega
  · refine ⟨1, Or.inl ?_⟩
    have hv1 : v = 1 := by ext <;> simp [hr, hi]
    rw [hv1, one_pow]; ext <;> simp
  · exfalso; rw [hr, hi] at hvsum; omega

end Conjectures.QuadraticPrimes.OddPowerImaginaryUnit_aux

open Conjectures.QuadraticPrimes.OddPowerImaginaryUnit_aux in
theorem Conjectures.QuadraticPrimes.OddPowerImaginaryUnit :
    ∀ n y j : ℕ, 0 < n → Even n → 3 ≤ j → Odd j → n^2+1 = y^j → ∃ a : ℤ, a ≠ 0 ∧ Even a ∧ Int.natAbs (((⟨a,1⟩ : GaussianInt)^j).im) = 1 := by

  intro n y j hn hne h3 hj hpow
  have hne' : Even (n : ℤ) := by
    obtain ⟨k, hk⟩ := hne
    refine ⟨(k : ℤ), ?_⟩
    rw [hk]; push_cast; ring
  have hmul : (⟨(n : ℤ), 1⟩ : GaussianInt) * ⟨(n : ℤ), -1⟩ = ((y : GaussianInt) ^ j) := by
    rw [← Nat.cast_pow (α := GaussianInt), ← hpow]
    exact mul_xx n
  have hcop : IsCoprime (⟨(n : ℤ), 1⟩ : GaussianInt) ⟨(n : ℤ), -1⟩ := coprime_mk (n : ℤ) hne'
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' hcop hmul
  obtain ⟨u, hu⟩ := hd
  have hd' : d ^ j = (⟨(n : ℤ), 1⟩ : GaussianInt) * ((↑(u⁻¹) : GaussianInt)) := by
    calc d ^ j = d ^ j * 1 := (mul_one _).symm
      _ = d ^ j * ((↑u : GaussianInt) * ↑(u⁻¹)) := by rw [Units.mul_inv]
      _ = (d ^ j * (↑u : GaussianInt)) * ↑(u⁻¹) := (mul_assoc _ _ _).symm
      _ = _ := by rw [hu]
  obtain ⟨w, hw⟩ := unit_absorb ((↑(u⁻¹) : GaussianInt)) (u⁻¹).isUnit j hj
  have hz : (w * d) ^ j = (⟨(n : ℤ), 1⟩ : GaussianInt) ∨
      (w * d) ^ j = -(⟨(n : ℤ), 1⟩ : GaussianInt) := by
    have hkey : (w * d) ^ j =
        (w ^ j * ((↑(u⁻¹) : GaussianInt))) * (⟨(n : ℤ), 1⟩ : GaussianInt) := by
      rw [mul_pow, hd']; ring
    rcases hw with hw | hw
    · left; rw [hkey, hw]; ring
    · right; rw [hkey, hw]; ring
  have him : ((w * d) ^ j).im = 1 ∨ ((w * d) ^ j).im = -1 := by
    rcases hz with h | h
    · left; rw [h]
    · right; rw [h]; simp
  have hdiv : (w * d).im ∣ ((w * d) ^ j).im := im_dvd_im_pow (w * d) j
  have himz : (w * d).im = 1 ∨ (w * d).im = -1 := by
    have hdv : (w * d).im ∣ 1 := by
      rcases him with h | h
      · rw [h] at hdiv; exact hdiv
      · rw [h] at hdiv; simpa using hdiv
    have hu : IsUnit (w * d).im := isUnit_iff_dvd_one.mpr hdv
    exact Int.isUnit_iff.mp hu
  obtain ⟨e, he1, hej⟩ : ∃ e : GaussianInt, e.im = 1 ∧
      (e ^ j = (⟨(n : ℤ), 1⟩ : GaussianInt) ∨
       e ^ j = -(⟨(n : ℤ), 1⟩ : GaussianInt)) := by
    rcases himz with h1 | h1
    · exact ⟨w * d, h1, hz⟩
    · refine ⟨-(w * d), ?_, ?_⟩
      · simp [h1]
      · have hp : (-(w * d)) ^ j = -((w * d) ^ j) := by
          rw [neg_pow, Odd.neg_one_pow hj, neg_one_mul]
        rw [hp]; rcases hz with h | h
        · right; rw [h]
        · left; rw [h]; ring
  have heeq : e = ⟨e.re, 1⟩ := by ext <;> simp [he1]
  have hx : ((⟨(n : ℤ), 1⟩ : GaussianInt)).norm = (n : ℤ) * (n : ℤ) + 1 := by
    have h := norm_mk (n : ℤ) 1; norm_num at h; exact h
  have he1n : (⟨e.re, 1⟩ : GaussianInt).norm = e.re * e.re + 1 := by
    have h := norm_mk e.re 1; norm_num at h; exact h
  have hej' := hej
  have hnrm : (e.re * e.re + 1) ^ j = (n : ℤ) * (n : ℤ) + 1 := by
    rcases hej with h | h
    · have h' : (⟨e.re, 1⟩ : GaussianInt) ^ j = (⟨(n : ℤ), 1⟩ : GaussianInt) := by
        rw [← heeq]; exact h
      have hh := congrArg Zsqrtd.norm h'
      rw [normPow, he1n, hx] at hh
      exact hh
    · have h' : (⟨e.re, 1⟩ : GaussianInt) ^ j = -(⟨(n : ℤ), 1⟩ : GaussianInt) := by
        rw [← heeq]; exact h
      have hh := congrArg Zsqrtd.norm h'
      rw [normPow, he1n, Zsqrtd.norm_neg, hx] at hh
      exact hh
  refine ⟨e.re, ?_, ?_, ?_⟩
  · intro h0
    rw [h0] at hnrm
    have h1 : (1 : ℤ) = (n : ℤ) * (n : ℤ) + 1 := by simpa using hnrm
    have h2 : (n : ℤ) * (n : ℤ) = 0 := by omega
    have h3' : (n : ℤ) = 0 := mul_self_eq_zero.mp h2
    have h4 : n = 0 := by exact_mod_cast h3'
    omega
  · by_contra hodd
    rcases Int.even_or_odd e.re with hev | hod
    · exact hodd hev
    · obtain ⟨c, hc⟩ := hod
      have h2 : (2 : ℤ) ∣ e.re * e.re + 1 := by
        refine ⟨2 * c * c + 2 * c + 1, ?_⟩
        rw [hc]; ring
      have hj0 : j ≠ 0 := by rcases hj with ⟨m, hm⟩; omega
      have h2p : (2 : ℤ) ∣ (e.re * e.re + 1) ^ j := dvd_pow h2 hj0
      rw [hnrm] at h2p
      have hn2 : (2 : ℤ) ∣ (n : ℤ) := by
        obtain ⟨k, hk⟩ := hne'
        refine ⟨k, ?_⟩
        rw [hk]; ring
      have hn2p : (2 : ℤ) ∣ (n : ℤ) * (n : ℤ) := dvd_mul_of_dvd_left hn2 _
      have h1 : (2 : ℤ) ∣ 1 := by
        have h := dvd_sub h2p hn2p
        simpa using h
      obtain ⟨c2, hc2⟩ := h1
      omega
  · rcases hej' with h | h
    · have hh : ((⟨e.re, 1⟩ : GaussianInt) ^ j).im = 1 := by rw [← heeq, h]
      rw [hh]; exact Int.natAbs_one
    · have hh : ((⟨e.re, 1⟩ : GaussianInt) ^ j).im = -1 := by rw [← heeq, h]; simp
      rw [hh]; simp
