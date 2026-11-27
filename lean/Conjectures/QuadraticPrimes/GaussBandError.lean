import Mathlib

/- The private single-mode estimate is adapted from GaussModeError at
   commit e8d741a9b34c0bffeb515d781e2c12f4da77d43a (Apache-2.0). -/

namespace Conjectures.QuadraticPrimes.GaussModeError_aux

private lemma filter_Ioc_eq_Ioc {P : ℕ → Prop} [DecidablePred P]
    (hP : ∀ m n : ℕ, m ≤ n → P m → P n) (x z : ℕ) :
    ∃ M : ℕ, M ≤ z ∧ (Finset.Ioc x z).filter P = Finset.Ioc M z := by
  by_cases h : ((Finset.Ioc x z).filter P).Nonempty
  · obtain ⟨w, hw⟩ := h
    have hmin := Finset.min'_mem ((Finset.Ioc x z).filter P) ⟨w, hw⟩
    have hmin' : ((Finset.Ioc x z).filter P).min' ⟨w, hw⟩ ∈ Finset.Ioc x z ∧
        P (((Finset.Ioc x z).filter P).min' ⟨w, hw⟩) := Finset.mem_filter.mp hmin
    refine ⟨((Finset.Ioc x z).filter P).min' ⟨w, hw⟩ - 1, by
      have h2 := (Finset.mem_Ioc.mp hmin'.1).2
      omega, ?_⟩
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hxn, hnz⟩, hPn⟩
      have hle : ((Finset.Ioc x z).filter P).min' ⟨w, hw⟩ ≤ n := by
        by_contra hcon
        have hmem : n ∈ (Finset.Ioc x z).filter P :=
          Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hxn, hnz⟩, hPn⟩
        have h2 := Finset.min'_le _ n hmem
        omega
      exact ⟨by omega, hnz⟩
    · rintro ⟨h1, h2⟩
      have h3 := (Finset.mem_Ioc.mp hmin'.1).1
      have hle : ((Finset.Ioc x z).filter P).min' ⟨w, hw⟩ ≤ n := by omega
      exact ⟨⟨by omega, h2⟩, hP _ _ hle hmin'.2⟩
  · refine ⟨z, le_refl z, ?_⟩
    have h0 : (Finset.Ioc x z).filter P = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [h0]
    exact (Finset.Ioc_eq_empty (by omega)).symm

private lemma abs_sin_mul_sum_cos_Ioc (φ : ℝ) (M N : ℕ) (hMN : M ≤ N) :
    |Real.sin (φ / 2)| * |∑ n ∈ Finset.Ioc M N, Real.cos (φ * (n : ℝ))| ≤ 1 := by
  have himg : Finset.Ioc M N = (Finset.range (N - M)).image (fun i => M + 1 + i) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨n - (M + 1), by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  have hinj : ∀ a ∈ Finset.range (N - M), ∀ b ∈ Finset.range (N - M),
      (fun i => M + 1 + i) a = (fun i => M + 1 + i) b → a = b := by
    intro a _ b _ hab
    have hab' : M + 1 + a = M + 1 + b := hab
    omega
  have hsum : ∑ n ∈ Finset.Ioc M N, Real.cos (φ * (n : ℝ)) =
      ∑ i ∈ Finset.range (N - M), Real.cos (φ * ((M + 1 + i : ℕ) : ℝ)) := by
    rw [himg, Finset.sum_image hinj]
  have hcos : ∀ i : ℕ, Real.cos (φ * ((M + 1 + i : ℕ) : ℝ)) =
      Real.cos (φ * (i : ℝ) + φ * ((M + 1 : ℕ) : ℝ)) := by
    intro i
    congr 1
    push_cast
    ring
  rw [hsum]
  simp_rw [hcos]
  have key := Real.sin_mul_sum_cos (N - M) φ (φ * ((M + 1 : ℕ) : ℝ))
  rw [← abs_mul, key, abs_mul]
  calc |Real.sin ((N - M : ℕ) * φ / 2)| *
        |Real.cos (((N - M : ℕ) - 1) * φ / 2 + φ * ((M + 1 : ℕ) : ℝ))|
      ≤ 1 * 1 := mul_le_mul (Real.abs_sin_le_one _) (Real.abs_cos_le_one _) (abs_nonneg _)
          (by norm_num)
    _ = 1 := by ring

set_option maxHeartbeats 800000 in
private lemma root_wave_le (p a b r v k : ℕ) (hb : 0 < b) (hp : 0 < p) (hab : a ≤ b)
    (hrel : (r : ℝ) / (p : ℝ) + (v : ℝ) / (b : ℝ) = 1 + (a : ℝ) / ((b : ℝ) * (p : ℝ))) :
    |2 * Real.cos (2 * Real.pi * (k : ℝ) * (r : ℝ) / (p : ℝ)) -
      2 * Real.cos (2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ))| ≤
      4 * Real.pi * (k : ℝ) / (p : ℝ) := by
  have hb0 : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb
  have hp0 : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
  have hab' : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr hab
  have hnum : (0 : ℝ) ≤ 2 * Real.pi * (k : ℝ) * (a : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (Nat.cast_nonneg k))
      (Nat.cast_nonneg a)
  have hden : (0 : ℝ) ≤ (b : ℝ) * (p : ℝ) :=
    mul_nonneg (Nat.cast_nonneg b) (Nat.cast_nonneg p)
  have hdef : (0 : ℝ) ≤ 2 * Real.pi * (k : ℝ) * (a : ℝ) / ((b : ℝ) * (p : ℝ)) :=
    div_nonneg hnum hden
  have hcoef : (0 : ℝ) ≤ 2 * (2 * Real.pi * (k : ℝ)) :=
    mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      (Nat.cast_nonneg k))
  have hA : 2 * Real.pi * (k : ℝ) * (r : ℝ) / (p : ℝ) =
      2 * Real.pi * (k : ℝ) + 2 * Real.pi * (k : ℝ) * (a : ℝ) / ((b : ℝ) * (p : ℝ)) -
        2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ) := by
    have h := congrArg (fun t : ℝ => 2 * Real.pi * (k : ℝ) * t) hrel
    linear_combination h
  have hper : ∀ w : ℝ, Real.cos (2 * Real.pi * (k : ℝ) + w) = Real.cos w := by
    intro w
    have hk2 : (2 * Real.pi * (k : ℝ) : ℝ) = ((k : ℤ) : ℝ) * (2 * Real.pi) := by
      push_cast
      ring
    rw [hk2, add_comm]
    exact Real.cos_add_int_mul_two_pi w k
  have hcos : Real.cos (2 * Real.pi * (k : ℝ) * (r : ℝ) / (p : ℝ)) =
      Real.cos (2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ) -
        2 * Real.pi * (k : ℝ) * (a : ℝ) / ((b : ℝ) * (p : ℝ))) := by
    rw [hA]
    have e1 : (2 * Real.pi * (k : ℝ) + 2 * Real.pi * (k : ℝ) * (a : ℝ) / ((b : ℝ) * (p : ℝ)) -
        2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ)) =
        2 * Real.pi * (k : ℝ) + (2 * Real.pi * (k : ℝ) * (a : ℝ) / ((b : ℝ) * (p : ℝ)) -
        2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ)) := by ring
    rw [e1, hper]
    have e2 : (2 * Real.pi * (k : ℝ) * (a : ℝ) / ((b : ℝ) * (p : ℝ)) -
        2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ)) =
        -(2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ) -
        2 * Real.pi * (k : ℝ) * (a : ℝ) / ((b : ℝ) * (p : ℝ))) := by ring
    rw [e2, Real.cos_neg]
  rw [hcos]
  have h1 := Real.abs_cos_sub_cos_le
    (2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ) -
      2 * Real.pi * (k : ℝ) * (a : ℝ) / ((b : ℝ) * (p : ℝ)))
    (2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ))
  have h2 : |(2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ) -
      2 * Real.pi * (k : ℝ) * (a : ℝ) / ((b : ℝ) * (p : ℝ))) -
      2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ)| =
      2 * Real.pi * (k : ℝ) * (a : ℝ) / ((b : ℝ) * (p : ℝ)) := by
    have e3 : (2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ) -
        2 * Real.pi * (k : ℝ) * (a : ℝ) / ((b : ℝ) * (p : ℝ))) -
        2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ) =
        -(2 * Real.pi * (k : ℝ) * (a : ℝ) / ((b : ℝ) * (p : ℝ))) := by ring
    rw [e3, abs_neg, abs_of_nonneg hdef]
  have h3 : |Real.cos (2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ) -
      2 * Real.pi * (k : ℝ) * (a : ℝ) / ((b : ℝ) * (p : ℝ))) -
      Real.cos (2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ))| ≤
      2 * Real.pi * (k : ℝ) * (a : ℝ) / ((b : ℝ) * (p : ℝ)) := h1.trans_eq h2
  have e4 : (2 * Real.cos (2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ) -
      2 * Real.pi * (k : ℝ) * (a : ℝ) / ((b : ℝ) * (p : ℝ))) -
      2 * Real.cos (2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ))) =
      2 * (Real.cos (2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ) -
        2 * Real.pi * (k : ℝ) * (a : ℝ) / ((b : ℝ) * (p : ℝ))) -
        Real.cos (2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ))) := by ring
  have h4 : |2 * Real.cos (2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ) -
      2 * Real.pi * (k : ℝ) * (a : ℝ) / ((b : ℝ) * (p : ℝ))) -
      2 * Real.cos (2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ))| ≤
      2 * (2 * Real.pi * (k : ℝ) * (a : ℝ) / ((b : ℝ) * (p : ℝ))) := by
    rw [e4, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left h3 (by norm_num)
  have h5 : (a : ℝ) / ((b : ℝ) * (p : ℝ)) ≤ 1 / (p : ℝ) := by
    rw [div_le_div_iff₀ (mul_pos hb0 hp0) hp0]
    have h6 : (a : ℝ) * (p : ℝ) ≤ (b : ℝ) * (p : ℝ) :=
      mul_le_mul_of_nonneg_right hab' (le_of_lt hp0)
    linarith [h6]
  calc |2 * Real.cos (2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ) -
        2 * Real.pi * (k : ℝ) * (a : ℝ) / ((b : ℝ) * (p : ℝ))) -
        2 * Real.cos (2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ))|
      ≤ 2 * (2 * Real.pi * (k : ℝ) * (a : ℝ) / ((b : ℝ) * (p : ℝ))) := h4
    _ = (2 * (2 * Real.pi * (k : ℝ))) * ((a : ℝ) / ((b : ℝ) * (p : ℝ))) := by ring
    _ ≤ (2 * (2 * Real.pi * (k : ℝ))) * (1 / (p : ℝ)) :=
        mul_le_mul_of_nonneg_left h5 hcoef
    _ = 4 * Real.pi * (k : ℝ) / (p : ℝ) := by ring

set_option maxHeartbeats 800000 in
private lemma interval_sum_le (p k : ℕ) (hp : 0 < p) (hk : 0 < k) (h2k : 2 * k ≤ p) (M N : ℕ)
    (hMN : M ≤ N) :
    |∑ n ∈ Finset.Ioc M N, Real.cos (2 * Real.pi * (k : ℝ) * (n : ℝ) / (p : ℝ))| ≤
      (p : ℝ) / (2 * (k : ℝ)) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
  have hk0 : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hp0' : ((p : ℝ)) ≠ 0 := ne_of_gt hp0
  have h2k' : (2 : ℝ) * (k : ℝ) ≤ (p : ℝ) := by
    have h : ((2 * k : ℕ) : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.cast_le.mpr h2k
    simpa using h
  have hconv : ∀ n : ℕ, Real.cos (2 * Real.pi * (k : ℝ) * (n : ℝ) / (p : ℝ)) =
      Real.cos ((2 * Real.pi * (k : ℝ) / (p : ℝ)) * (n : ℝ)) := by
    intro n
    congr 1
    ring
  have hsumrw : (∑ n ∈ Finset.Ioc M N,
      Real.cos (2 * Real.pi * (k : ℝ) * (n : ℝ) / (p : ℝ))) =
      ∑ n ∈ Finset.Ioc M N,
        Real.cos ((2 * Real.pi * (k : ℝ) / (p : ℝ)) * (n : ℝ)) :=
    Finset.sum_congr rfl (fun n _ => hconv n)
  rw [hsumrw]
  have hkey := abs_sin_mul_sum_cos_Ioc (2 * Real.pi * (k : ℝ) / (p : ℝ)) M N hMN
  have hx' : Real.pi * (k : ℝ) / (p : ℝ) ≤ Real.pi / 2 := by
    rw [div_le_div_iff₀ hp0 (by norm_num)]
    calc (Real.pi * (k : ℝ)) * 2 = Real.pi * (2 * (k : ℝ)) := by ring
      _ ≤ Real.pi * (p : ℝ) := mul_le_mul_of_nonneg_left h2k' Real.pi_pos.le
  have hx0 : (0 : ℝ) ≤ Real.pi * (k : ℝ) / (p : ℝ) :=
    div_nonneg (mul_nonneg Real.pi_pos.le (Nat.cast_nonneg k)) (Nat.cast_nonneg p)
  have hsin0 : (2 : ℝ) * (k : ℝ) / (p : ℝ) ≤ Real.sin (Real.pi * (k : ℝ) / (p : ℝ)) := by
    have h := Real.mul_le_sin (x := Real.pi * (k : ℝ) / (p : ℝ)) hx0 hx'
    have he : (2 : ℝ) / Real.pi * (Real.pi * (k : ℝ) / (p : ℝ)) =
        2 * (k : ℝ) / (p : ℝ) := by
      field_simp [Real.pi_ne_zero, hp0'] <;> ring
    rwa [he] at h
  have htwo : (0 : ℝ) ≤ 2 * (k : ℝ) / (p : ℝ) :=
    div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg k)) (Nat.cast_nonneg p)
  have hsin : (2 : ℝ) * (k : ℝ) / (p : ℝ) ≤
      |Real.sin ((2 * Real.pi * (k : ℝ) / (p : ℝ)) / 2)| := by
    have he : (2 * Real.pi * (k : ℝ) / (p : ℝ)) / 2 = Real.pi * (k : ℝ) / (p : ℝ) := by ring
    have hpos' : (0 : ℝ) ≤ Real.sin ((2 * Real.pi * (k : ℝ) / (p : ℝ)) / 2) := by
      rw [he]
      exact le_trans htwo hsin0
    calc (2 : ℝ) * (k : ℝ) / (p : ℝ) ≤ Real.sin (Real.pi * (k : ℝ) / (p : ℝ)) := hsin0
      _ = Real.sin ((2 * Real.pi * (k : ℝ) / (p : ℝ)) / 2) := by rw [he]
      _ = |Real.sin ((2 * Real.pi * (k : ℝ) / (p : ℝ)) / 2)| := (abs_of_nonneg hpos').symm
  have hkey2 : (2 : ℝ) * (k : ℝ) / (p : ℝ) *
      |∑ n ∈ Finset.Ioc M N,
        Real.cos ((2 * Real.pi * (k : ℝ) / (p : ℝ)) * (n : ℝ))| ≤ 1 := by
    calc _ ≤ |Real.sin ((2 * Real.pi * (k : ℝ) / (p : ℝ)) / 2)| *
          |∑ n ∈ Finset.Ioc M N,
            Real.cos ((2 * Real.pi * (k : ℝ) / (p : ℝ)) * (n : ℝ))| :=
          mul_le_mul_of_nonneg_right hsin (abs_nonneg _)
      _ ≤ 1 := hkey
  have hpos : (0 : ℝ) < 2 * (k : ℝ) := mul_pos (by norm_num) hk0
  refine (le_div_iff₀ hpos).mpr ?_
  have h1 : ((2 : ℝ) * (k : ℝ) / (p : ℝ)) * (p : ℝ) *
      |∑ n ∈ Finset.Ioc M N,
        Real.cos ((2 * Real.pi * (k : ℝ) / (p : ℝ)) * (n : ℝ))| ≤ 1 * (p : ℝ) := by
    calc _ = ((2 : ℝ) * (k : ℝ) / (p : ℝ)) *
          |∑ n ∈ Finset.Ioc M N,
            Real.cos ((2 * Real.pi * (k : ℝ) / (p : ℝ)) * (n : ℝ))| * (p : ℝ) := by ring
      _ ≤ 1 * (p : ℝ) := mul_le_mul_of_nonneg_right hkey2 (le_of_lt hp0)
  calc |∑ n ∈ Finset.Ioc M N,
        Real.cos ((2 * Real.pi * (k : ℝ) / (p : ℝ)) * (n : ℝ))| * ((2 : ℝ) * (k : ℝ))
      = ((2 : ℝ) * (k : ℝ) / (p : ℝ)) * (p : ℝ) *
        |∑ n ∈ Finset.Ioc M N,
          Real.cos ((2 * Real.pi * (k : ℝ) / (p : ℝ)) * (n : ℝ))| := by
          field_simp [hp0'] <;> ring
    _ ≤ 1 * (p : ℝ) := h1
    _ = (p : ℝ) := one_mul _

end Conjectures.QuadraticPrimes.GaussModeError_aux

set_option maxHeartbeats 800000 in
private theorem Conjectures.QuadraticPrimes.GaussModeError :
    let block := fun x : ℕ => Finset.Ioc x (2 * x); let window := fun x p : ℕ => (block x).filter (fun n => p ^ 100000 ≤ n ^ 132301); let phase := fun p k (t : ℕ) => 2 * Real.pi * (k : ℝ) * (t : ℝ) / (p : ℝ); let rootWave := fun q k t : ℕ => 2 * Real.cos (phase q k t); let good := fun p a b r v : ℕ => p.Prime ∧ 2 < p ∧ 0 < a ∧ a ≤ b ∧ p = a ^ 2 + b ^ 2 ∧ r < p ∧ v < b ∧ (b * r) % p = a % p ∧ (a * v) % b = 1 % b; ∀ x p a b r v k : ℕ, good p a b r v → 0 < k → k ≤ Nat.sqrt p →
  |(rootWave p k r - rootWave b k v) * (∑ n ∈ window x p, Real.cos (phase p k n)) / (p : ℝ)| ≤
  2 * Real.pi / p := by
  intro block window phase rootWave good x p a b r v k hgood hk hksq
  dsimp only [block, window, phase, rootWave, good] at *
  obtain ⟨hprime, hp2, ha, hab, hsum, hrp, hvb, hbr, hav⟩ := hgood
  generalize hW : (Finset.Ioc x (2 * x)).filter (fun n => p ^ 100000 ≤ n ^ 132301) = W
  have ha1 : 1 ≤ a := ha
  have hb1 : 1 ≤ b := le_trans ha1 hab
  have hb2 : 2 ≤ b := by
    by_contra hcon
    have hbe : b = 1 := by omega
    have hae : a = 1 := by omega
    have hpe : p = 2 := by
      calc p = a ^ 2 + b ^ 2 := hsum
        _ = 1 ^ 2 + 1 ^ 2 := by rw [hae, hbe]
        _ = 2 := by norm_num
    omega
  have ha2 : 1 ≤ a ^ 2 := by
    have h := Nat.pow_le_pow_left ha1 2
    simpa using h
  have hb2' : (2 : ℕ) ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hb2 2
  have hp5 : 5 ≤ p := by
    calc 5 = 1 ^ 2 + 2 ^ 2 := by norm_num
      _ ≤ a ^ 2 + b ^ 2 := Nat.add_le_add ha2 hb2'
      _ = p := hsum.symm
  have hbsq : b ≤ b ^ 2 := by
    calc b = b * 1 := (Nat.mul_one b).symm
      _ ≤ b * b := Nat.mul_le_mul_left b hb1
      _ = b ^ 2 := by ring
  have hblp : b < p := by
    calc b < b + 1 := by omega
      _ ≤ b ^ 2 + a ^ 2 := Nat.add_le_add hbsq ha2
      _ = a ^ 2 + b ^ 2 := by ring
      _ = p := hsum.symm
  have halp : a < p := lt_of_le_of_lt hab hblp
  have hmod : (b * r) % p = a := by
    rw [hbr, Nat.mod_eq_of_lt halp]
  have hmkey : b * r = p * (b * r / p) + a := by
    have h := Nat.div_add_mod (b * r) p
    rw [hmod] at h
    omega
  have hmlt : b * r / p < b := by
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < p)]
    exact Nat.mul_lt_mul_of_pos_left hrp (by omega)
  have hv1 : 1 ≤ v := by
    by_contra hcon
    have hv0 : v = 0 := by omega
    rw [hv0, Nat.mul_zero, Nat.zero_mod] at hav
    have h1 : 1 % b = 0 := hav.symm
    have h2 : b ∣ 1 := Nat.dvd_of_mod_eq_zero h1
    have h3 : b = 1 := Nat.dvd_one.mp h2
    omega
  have hav1 : (a * v) % b = 1 := hav.trans (Nat.mod_eq_of_lt (by omega : 1 < b))
  have havn : a * v = b * (a * v / b) + 1 := by
    have h := Nat.div_add_mod (a * v) b
    rw [hav1] at h
    omega
  have hbr2 : b * r = a ^ 2 * (b * r / p) + b ^ 2 * (b * r / p) + a := by
    calc b * r = p * (b * r / p) + a := hmkey
      _ = (a ^ 2 + b ^ 2) * (b * r / p) + a := by rw [hsum]
      _ = a ^ 2 * (b * r / p) + b ^ 2 * (b * r / p) + a := by ring
  have hz1 : (b : ℤ) * (r : ℤ) =
      (a : ℤ) ^ 2 * ((b * r / p : ℕ) : ℤ) + (b : ℤ) ^ 2 * ((b * r / p : ℕ) : ℤ) + (a : ℤ) := by
    have h := congrArg (fun t : ℕ => (t : ℤ)) hbr2
    simpa using h
  have hz2 : (a : ℤ) * (v : ℤ) = (b : ℤ) * ((a * v / b : ℕ) : ℤ) + 1 := by
    have h := congrArg (fun t : ℕ => (t : ℤ)) havn
    simpa using h
  have hD1 : (b : ℤ) ∣ (a : ℤ) * (1 + (a : ℤ) * ((b * r / p : ℕ) : ℤ)) :=
    ⟨(r : ℤ) - (b : ℤ) * ((b * r / p : ℕ) : ℤ), by linarith [hz1]⟩
  have hD3 : (b : ℤ) ∣ (a : ℤ) * (v : ℤ) - 1 :=
    ⟨((a * v / b : ℕ) : ℤ), by linarith [hz2]⟩
  have hD4 : (b : ℤ) ∣ 1 + (a : ℤ) * ((b * r / p : ℕ) : ℤ) := by
    obtain ⟨c1, hc1⟩ := hD1
    obtain ⟨c3, hc3⟩ := hD3
    refine ⟨c1 * (v : ℤ) - c3 * (1 + (a : ℤ) * ((b * r / p : ℕ) : ℤ)), ?_⟩
    have e1 : (b : ℤ) * (c1 * (v : ℤ) - c3 * (1 + (a : ℤ) * ((b * r / p : ℕ) : ℤ))) =
        (b : ℤ) * c1 * (v : ℤ) -
          (b : ℤ) * c3 * (1 + (a : ℤ) * ((b * r / p : ℕ) : ℤ)) := by ring
    rw [e1, ← hc1, ← hc3]
    ring
  have hD5 : (b : ℤ) ∣ (a : ℤ) * (((b * r / p : ℕ) : ℤ) + (v : ℤ)) := by
    obtain ⟨c4, hc4⟩ := hD4
    obtain ⟨c3, hc3⟩ := hD3
    refine ⟨c4 + c3, ?_⟩
    have e1 : (b : ℤ) * (c4 + c3) = (b : ℤ) * c4 + (b : ℤ) * c3 := by ring
    rw [e1, ← hc4, ← hc3]
    ring
  have hD8 : (b : ℤ) ∣ ((b * r / p : ℕ) : ℤ) + (v : ℤ) := by
    obtain ⟨c5, hc5⟩ := hD5
    obtain ⟨c3, hc3⟩ := hD3
    refine ⟨c5 * (v : ℤ) - c3 * (((b * r / p : ℕ) : ℤ) + (v : ℤ)), ?_⟩
    have e1 : (b : ℤ) * (c5 * (v : ℤ) - c3 * (((b * r / p : ℕ) : ℤ) + (v : ℤ))) =
        (b : ℤ) * c5 * (v : ℤ) -
          (b : ℤ) * c3 * (((b * r / p : ℕ) : ℤ) + (v : ℤ)) := by ring
    rw [e1, ← hc5, ← hc3]
    ring
  obtain ⟨c, hc⟩ := hD8
  have hc1 : c = 1 := by
    have hbZ : (0 : ℤ) < (b : ℤ) := Nat.cast_pos.mpr (by omega)
    have hmZ : ((b * r / p : ℕ) : ℤ) < (b : ℤ) := Nat.cast_lt.mpr hmlt
    have hvZ : (v : ℤ) < (b : ℤ) := Nat.cast_lt.mpr hvb
    have hv1Z : (1 : ℤ) ≤ (v : ℤ) := by
      have h : ((1 : ℕ) : ℤ) ≤ ((v : ℕ) : ℤ) := Nat.cast_le.mpr hv1
      simpa using h
    have hpos : (0 : ℤ) < ((b * r / p : ℕ) : ℤ) + (v : ℤ) := by
      have hm0 : (0 : ℤ) ≤ ((b * r / p : ℕ) : ℤ) := Nat.cast_nonneg _
      linarith
    have hlt : ((b * r / p : ℕ) : ℤ) + (v : ℤ) < 2 * (b : ℤ) := by linarith
    have hcpos : 0 < c := by
      by_contra hcon
      have hcon' : c ≤ 0 := by omega
      have h4 : (b : ℤ) * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hbZ) hcon'
      linarith [hc]
    have hclt : c < 2 := by
      by_contra hcon
      have hcon' : 2 ≤ c := by omega
      have h4 : (b : ℤ) * 2 ≤ (b : ℤ) * c := mul_le_mul_of_nonneg_left hcon' (le_of_lt hbZ)
      have h5 : (2 : ℤ) * (b : ℤ) ≤ (b : ℤ) * c := by linarith [h4]
      linarith [hc]
    omega
  have hmvZ : ((b * r / p : ℕ) : ℤ) + (v : ℤ) = (b : ℤ) := by
    rw [hc, hc1]
    ring
  have hmvf : b * r / p + v = b := by
    have h : ((b * r / p + v : ℕ) : ℤ) = ((b : ℕ) : ℤ) := by simpa using hmvZ
    exact Nat.cast_inj.mp h
  have hfinal : b * r + p * v = a + b * p := by
    calc b * r + p * v = (p * (b * r / p) + a) + p * v :=
            congrArg (fun t : ℕ => t + p * v) hmkey
      _ = p * (b * r / p + v) + a := by ring
      _ = p * b + a := by rw [hmvf]
      _ = a + b * p := by ring
  have hrel : (b : ℝ) * (r : ℝ) + (p : ℝ) * (v : ℝ) = (a : ℝ) + (b : ℝ) * (p : ℝ) := by
    have h := congrArg (fun t : ℕ => (t : ℝ)) hfinal
    simpa using h
  have hb0r : ((b : ℝ)) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have hp0r : ((p : ℝ)) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hbpr : ((b : ℝ) * (p : ℝ)) ≠ 0 := mul_ne_zero hb0r hp0r
  have hrel2 : (r : ℝ) / (p : ℝ) + (v : ℝ) / (b : ℝ) =
      1 + (a : ℝ) / ((b : ℝ) * (p : ℝ)) := by
    field_simp [hb0r, hp0r, hbpr]
    linear_combination hrel
  have hkk : k * k ≤ p := by
    calc k * k ≤ Nat.sqrt p * Nat.sqrt p := Nat.mul_le_mul hksq hksq
      _ = Nat.sqrt p ^ 2 := by ring
      _ ≤ p := Nat.sqrt_le' p
  have h2k : 2 * k ≤ p := by
    rcases Nat.lt_or_ge k 2 with h | h
    · omega
    · have hmul : 2 * k ≤ k * k := Nat.mul_le_mul h (le_refl k)
      exact le_trans hmul hkk
  have hroot := Conjectures.QuadraticPrimes.GaussModeError_aux.root_wave_le p a b r v k
    (by omega) (by omega) hab hrel2
  have hP : ∀ m n : ℕ, m ≤ n → p ^ 100000 ≤ m ^ 132301 → p ^ 100000 ≤ n ^ 132301 := by
    intro m n hmn h
    exact le_trans h (Nat.pow_le_pow_left hmn 132301)
  have hWint : ∃ M : ℕ, M ≤ 2 * x ∧ W = Finset.Ioc M (2 * x) := by
    rw [← hW]
    exact Conjectures.QuadraticPrimes.GaussModeError_aux.filter_Ioc_eq_Ioc hP x (2 * x)
  obtain ⟨M, hMle, hWM⟩ := hWint
  have hwsum : |∑ n ∈ W, Real.cos (2 * Real.pi * (k : ℝ) * (n : ℝ) / (p : ℝ))| ≤
      (p : ℝ) / (2 * (k : ℝ)) := by
    rw [hWM]
    exact Conjectures.QuadraticPrimes.GaussModeError_aux.interval_sum_le p k (by omega) hk h2k
      M (2 * x) hMle
  have hp0 : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (by omega)
  have hk0r : ((k : ℝ)) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have h9 : (0 : ℝ) ≤ 4 * Real.pi * (k : ℝ) / (p : ℝ) :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (Nat.cast_nonneg k))
      (le_of_lt hp0)
  have h8 : (4 * Real.pi * (k : ℝ) / (p : ℝ)) * ((p : ℝ) / (2 * (k : ℝ))) = 2 * Real.pi := by
    field_simp [hp0r, mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hk0r] <;> ring
  have hfinal2 : |2 * Real.cos (2 * Real.pi * (k : ℝ) * (r : ℝ) / (p : ℝ)) -
      2 * Real.cos (2 * Real.pi * (k : ℝ) * (v : ℝ) / (b : ℝ))| *
      |∑ n ∈ W, Real.cos (2 * Real.pi * (k : ℝ) * (n : ℝ) / (p : ℝ))| ≤
      2 * Real.pi := by
    calc _ ≤ (4 * Real.pi * (k : ℝ) / (p : ℝ)) * ((p : ℝ) / (2 * (k : ℝ))) :=
          mul_le_mul hroot hwsum (abs_nonneg _) h9
      _ = 2 * Real.pi := h8
  rw [abs_div, abs_mul, abs_of_pos hp0]
  exact div_le_div_of_nonneg_right hfinal2 (le_of_lt hp0)


private lemma low_count (p : ℕ) :
    ((Finset.Ico 1 p).filter (fun k => min k (p-k) ≤ Nat.sqrt p)).card ≤ 2 * Nat.sqrt p := by
  let A := Finset.Ico 1 (Nat.sqrt p + 1)
  let B := Finset.Ico (p - Nat.sqrt p) p
  have hsub : (Finset.Ico 1 p).filter (fun k => min k (p-k) ≤ Nat.sqrt p) ⊆ A ∪ B := by
    intro k hk
    have hk' := Finset.mem_filter.mp hk
    have hi := Finset.mem_Ico.mp hk'.1
    have hh : k ≤ Nat.sqrt p ∨ p-k ≤ Nat.sqrt p := (min_le_iff).mp hk'.2
    apply Finset.mem_union.mpr
    rcases hh with h | h
    · left; simp only [A, Finset.mem_Ico]; omega
    · right; simp only [B, Finset.mem_Ico]; omega
  have ha : A.card = Nat.sqrt p := by simp [A, Nat.card_Ico]
  have hb : B.card ≤ Nat.sqrt p := by simp only [B, Nat.card_Ico]; omega
  have hu := Finset.card_union_le A B
  have hc := Finset.card_le_card hsub
  omega

private lemma sqrt_power_bound (x p : ℕ) (hx : 0 < x)
    (hp : p^100000 ≤ (2*x)^132301) :
    Real.sqrt (p:ℝ) ≤ (2*(x:ℝ))^(132301/200000:ℝ) := by
  have hxp : 0 < (2*(x:ℝ)) := by positivity
  have hpR : (p:ℝ)^100000 ≤ (2*(x:ℝ))^132301 := by exact_mod_cast hp
  have h1 : (p:ℝ) ≤ (2*(x:ℝ))^(132301/100000:ℝ) := by
    apply (Real.rpow_le_rpow_iff (by positivity) (by positivity) (by norm_num : (0:ℝ)<100000)).mp
    change (p:ℝ) ^ (100000:ℝ) ≤ ((2*(x:ℝ))^(132301/100000:ℝ)) ^ (100000:ℝ)
    rw [← Real.rpow_mul (le_of_lt hxp)]
    have he : (132301 / 100000 : ℝ) * 100000 = 132301 := by norm_num
    rw [he]
    change (p:ℝ) ^ ((100000:ℕ):ℝ) ≤ (2*(x:ℝ)) ^ ((132301:ℕ):ℝ)
    rw [Real.rpow_natCast, Real.rpow_natCast]
    exact hpR
  rw [Real.sqrt_eq_rpow]
  calc
    (p:ℝ) ^ (1/2:ℝ) ≤ ((2*(x:ℝ))^(132301/100000:ℝ)) ^ (1/2:ℝ) :=
      Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    _ = (2*(x:ℝ))^(132301/200000:ℝ) := by rw [← Real.rpow_mul (le_of_lt hxp)]; norm_num1; rfl


private lemma log_bounds (x p : ℕ) (hx : 4 ≤ x) (hp : p ≤ (2*x)^2+1) (hp0 : 0<p) :
    let L := Real.log (2*(x:ℝ));
    Real.log (p:ℝ) ≤ 3*L ∧
    1 + Real.log (((2*x)^2+1:ℕ):ℝ) ≤ (3 + 1/Real.log 2)*L := by
  dsimp only
  let z : ℝ := 2*(x:ℝ)
  let U : ℕ := (2*x)^2+1
  have hz : 2 ≤ z := by dsimp [z]; exact_mod_cast (show 2 ≤ 2*x by omega)
  have hz0 : 0 < z := by linarith
  have hz1 : 1 ≤ z := by linarith
  have hsq : 1 ≤ z^2 := one_le_pow₀ hz1
  have hzu : (U:ℝ) ≤ z^3 := by
    have hm : 2*z^2 ≤ z*z^2 := mul_le_mul_of_nonneg_right hz (sq_nonneg z)
    have hu : (U:ℝ) = z^2+1 := by simp [U,z]
    rw [hu]
    nlinarith
  have hlog : Real.log (U:ℝ) ≤ 3*Real.log z := by
    have hu0 : (0:ℝ)<U := by positivity
    have h := Real.log_le_log hu0 hzu
    rw [Real.log_pow] at h
    norm_num at h
    exact h
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : Real.log 2 ≤ Real.log z := Real.log_le_log (by norm_num) hz
  have h1 : 1 ≤ (1/Real.log 2)*Real.log z := by
    have h := mul_le_mul_of_nonneg_left hL (show 0 ≤ 1 / Real.log 2 by positivity)
    have hc : (1 / Real.log 2) * Real.log 2 = 1 := by field_simp
    linarith
  have hlogp : Real.log (p:ℝ) ≤ Real.log (U:ℝ) :=
    Real.log_le_log (by exact_mod_cast hp0) (by exact_mod_cast hp)
  constructor
  · exact le_trans hlogp hlog
  · nlinarith

private lemma harmonic_set_bound (x : ℕ) (S : Finset ℕ) (hx : 4 ≤ x)
    (hS : S ⊆ Finset.Icc 1 ((2*x)^2+1)) :
    (∑ p ∈ S, (1:ℝ)/(p:ℝ)) ≤ (3 + 1/Real.log 2)*Real.log (2*(x:ℝ)) := by
  let U : ℕ := (2*x)^2+1
  have hsub : (∑ p ∈ S, (1:ℝ)/(p:ℝ)) ≤ ∑ p ∈ Finset.Icc 1 U, (1:ℝ)/(p:ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hS
    intro p hp hpS
    positivity
  have hh : (∑ p ∈ Finset.Icc 1 U, (1:ℝ)/(p:ℝ)) ≤ 1 + Real.log (U:ℝ) := by
    have h := harmonic_le_one_add_log U
    rw [harmonic_eq_sum_Icc] at h
    simpa only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div] using h
  exact hsub.trans (hh.trans (log_bounds x 1 hx (by omega) (by omega)).2)


set_option maxHeartbeats 800000 in
theorem Conjectures.QuadraticPrimes.GaussBandError :
let block := fun x : ℕ => Finset.Ioc x (2*x); let window := fun x p : ℕ => (block x).filter (fun n => p^100000≤n^132301); let phase := fun p k (t : ℕ) => 2*Real.pi*(k : ℝ)*(t : ℝ)/(p : ℝ); let rootWave := fun q k t : ℕ => 2*Real.cos (phase q k t); let good := fun p a b r v : ℕ => p.Prime ∧ 2<p ∧ 0<a ∧ a≤b ∧ p=a^2+b^2 ∧ r<p ∧ v<b ∧ (b*r) % p=a % p ∧ (a*v) % b=1 % b; let low := fun p : ℕ => (Finset.Ico 1 p).filter (fun k => min k (p-k)≤Nat.sqrt p); let amp := fun x p q t : ℕ => (∑ k ∈ low p, rootWave q (min k (p-k)) t * (∑ n ∈ window x p, Real.cos (phase p (min k (p-k)) n)) / (p : ℝ)) * Real.log p; let split := fun x : ℕ => (Finset.Ioc x ((2*x)^2+1)).filter (fun p => p.Prime ∧ p % 4=1 ∧ p^100000≤(2*x)^132301); ∃ C : ℝ, 0<C ∧ ∀ x : ℕ, 4≤x → ∀ S : Finset ℕ, S⊆split x →
  ∀ a b r v : ℕ → ℕ, (∀ p ∈ S, good p (a p) (b p) (r p) (v p)) →
  |∑ p ∈ S, (amp x p p (r p) - amp x p (b p) (v p))| ≤
    C * (x : ℝ)^(132301/200000 : ℝ) * (Real.log (2*(x : ℝ)))^2 := by
  intro block window phase rootWave good low amp split
  let K : ℝ := 3 + 1 / Real.log 2
  let C : ℝ := 24 * Real.pi * K
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 < K := by dsimp [K]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro x hx S hS a b r v hgood
  let X : ℝ := (2 * (x : ℝ))^(132301/200000 : ℝ)
  let L : ℝ := Real.log (2*(x:ℝ))
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hL : 0 ≤ L := by
    have hxR : (4:ℝ) ≤ x := by exact_mod_cast hx
    dsimp [L]
    apply Real.log_nonneg
    linarith
  have hpdata (p : ℕ) (hp : p ∈ S) : x < p ∧ p ≤ (2*x)^2+1 ∧ p.Prime ∧ p^100000 ≤ (2*x)^132301 := by
    have h := hS hp
    dsimp only [split] at h
    simp only [Finset.mem_filter, Finset.mem_Ioc] at h
    exact ⟨h.1.1,h.1.2,h.2.1,h.2.2.2⟩
  have hmode (p : ℕ) (hp : p ∈ S) (k : ℕ) (hk : k ∈ low p) :
      |(rootWave p (min k (p-k)) (r p) - rootWave (b p) (min k (p-k)) (v p)) *
        (∑ n ∈ window x p, Real.cos (phase p (min k (p-k)) n)) / (p:ℝ)| ≤ 2*Real.pi/(p:ℝ) := by
    have hp' := hpdata p hp
    have hk' := hk
    dsimp only [low] at hk'
    simp only [Finset.mem_filter, Finset.mem_Ico] at hk'
    have hminpos : 0 < min k (p-k) := by omega
    have hminle : min k (p-k) ≤ Nat.sqrt p := hk'.2
    have hgm := Conjectures.QuadraticPrimes.GaussModeError
    dsimp only at hgm
    have hg := hgood p hp
    dsimp only [good] at hg
    have h := hgm x p (a p) (b p) (r p) (v p) (min k (p-k)) hg hminpos hminle
    have hcast : ((min k (p-k):ℕ):ℝ) = min (k:ℝ) ((p:ℝ)-k) := by
      rw [Nat.cast_min, Nat.cast_sub (by omega : k ≤ p)]
    dsimp only [phase]
    rw [← hcast]
    exact h
  have hper (p : ℕ) (hp : p ∈ S) :
      |amp x p p (r p) - amp x p (b p) (v p)| ≤
        (4*Real.pi*X) * (Real.log (p:ℝ)/(p:ℝ)) := by
    have hp' := hpdata p hp
    have hp0 : 0 < (p:ℝ) := by exact_mod_cast (show 0 < p by omega)
    have hlogp : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
    have hcount : ((low p).card : ℝ) ≤ 2*(Nat.sqrt p:ℝ) := by
      have h := low_count p
      dsimp only [low]
      exact_mod_cast h
    have hsqrtnat : (Nat.sqrt p : ℝ) ≤ Real.sqrt (p:ℝ) := by
      apply (Real.le_sqrt (by positivity) (by positivity)).2
      exact_mod_cast Nat.sqrt_le' p
    have hsqrt : (Nat.sqrt p : ℝ) ≤ X := by
      exact hsqrtnat.trans (sqrt_power_bound x p (by omega) hp'.2.2.2)
    have hrew : amp x p p (r p) - amp x p (b p) (v p) =
        (∑ k ∈ low p, (rootWave p (min k (p-k)) (r p) - rootWave (b p) (min k (p-k)) (v p)) *
          (∑ n ∈ window x p, Real.cos (phase p (min k (p-k)) n)) / (p:ℝ)) * Real.log p := by
      dsimp only [amp]
      rw [← sub_mul, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hrew, abs_mul, abs_of_nonneg hlogp]
    have hsum : |∑ k ∈ low p, (rootWave p (min k (p-k)) (r p) - rootWave (b p) (min k (p-k)) (v p)) *
        (∑ n ∈ window x p, Real.cos (phase p (min k (p-k)) n)) / (p:ℝ)| ≤
        (2*X)*(2*Real.pi/(p:ℝ)) := by
      calc
        _ ≤ ∑ k ∈ low p, |(rootWave p (min k (p-k)) (r p) - rootWave (b p) (min k (p-k)) (v p)) *
          (∑ n ∈ window x p, Real.cos (phase p (min k (p-k)) n)) / (p:ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ((low p).card:ℝ) * (2*Real.pi/(p:ℝ)) := by
          simpa using (Finset.sum_le_card_nsmul (low p) _ (2*Real.pi/(p:ℝ)) (by intro k hk; exact hmode p hp k hk))
        _ ≤ (2*X)*(2*Real.pi/(p:ℝ)) := by
          gcongr
          linarith
    have hf := mul_le_mul_of_nonneg_right hsum hlogp
    convert hf using 1 <;> ring
  have hsub : S ⊆ Finset.Icc 1 ((2*x)^2+1) := by
    intro p hp
    have h := hpdata p hp
    exact Finset.mem_Icc.mpr ⟨by omega, h.2.1⟩
  have hharm : (∑ p ∈ S, (1:ℝ)/(p:ℝ)) ≤ K*L := by
    exact harmonic_set_bound x S hx hsub
  have hlogsum : (∑ p ∈ S, Real.log (p:ℝ)/(p:ℝ)) ≤ (3*L)*(K*L) := by
    calc
      _ ≤ ∑ p ∈ S, (3*L) * ((1:ℝ)/(p:ℝ)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' := hpdata p hp
        have hp0 : 0 < (p:ℝ) := by exact_mod_cast (show 0 < p by omega)
        have hl := (log_bounds x p hx hp'.2.1 (by omega)).1
        dsimp only [L] at *
        have ht := div_le_div_of_nonneg_right hl (le_of_lt hp0)
        convert ht using 1 <;> ring
      _ = (3*L) * (∑ p ∈ S, (1:ℝ)/(p:ℝ)) := by rw [Finset.mul_sum]
      _ ≤ (3*L)*(K*L) := mul_le_mul_of_nonneg_left hharm (by positivity)
  have hxpow : 0 ≤ (x:ℝ)^(132301/200000:ℝ) := Real.rpow_nonneg (by positivity) _
  have h2pow : (2:ℝ)^(132301/200000:ℝ) ≤ 2 := by
    calc
      _ ≤ (2:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have hXbound : X ≤ 2 * (x:ℝ)^(132301/200000:ℝ) := by
    dsimp [X]
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    exact mul_le_mul_of_nonneg_right h2pow hxpow
  calc
    |∑ p ∈ S, (amp x p p (r p) - amp x p (b p) (v p))| ≤
        ∑ p ∈ S, |amp x p p (r p) - amp x p (b p) (v p)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ S, (4*Real.pi*X)*(Real.log (p:ℝ)/(p:ℝ)) := Finset.sum_le_sum (fun p hp => hper p hp)
    _ = (4*Real.pi*X) * (∑ p ∈ S, Real.log (p:ℝ)/(p:ℝ)) := by rw [Finset.mul_sum]
    _ ≤ (4*Real.pi*X) * ((3*L)*(K*L)) := mul_le_mul_of_nonneg_left hlogsum (by positivity)
    _ ≤ C * (x:ℝ)^(132301/200000:ℝ) * L^2 := by
      dsimp [C]
      calc
        _ = (12*Real.pi*K*L^2)*X := by ring
        _ ≤ (12*Real.pi*K*L^2)*(2*(x:ℝ)^(132301/200000:ℝ)) :=
          mul_le_mul_of_nonneg_left hXbound (by positivity)
        _ = _ := by ring
