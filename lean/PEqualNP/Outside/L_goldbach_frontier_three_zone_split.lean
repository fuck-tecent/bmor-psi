import Mathlib

noncomputable section

open MeasureTheory

private lemma six_le_two_pow (k : ℕ) (hk : 30 ≤ k) : k ^ 6 + 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hratio : (k : ℝ) ≥ 30 := by exact_mod_cast hk
    have hkpos : (0 : ℝ) < k := by linarith
    have h1R : ((k : ℝ) + 1) ^ 6 ≤ 2 * (k : ℝ) ^ 6 := by
      have hquot : ((k : ℝ) + 1) / (k : ℝ) ≤ 11 / 10 := by
        rw [div_le_iff₀ hkpos]
        linarith
      have hpow : (((k : ℝ) + 1) / (k : ℝ)) ^ 6 ≤ ((11 : ℝ) / 10) ^ 6 :=
        pow_le_pow_left₀ (by positivity) hquot 6
      have h2 : ((11 : ℝ) / 10) ^ 6 ≤ 2 := by norm_num
      have hkey : (((k : ℝ) + 1) ^ 6) / (k : ℝ) ^ 6 ≤ 2 := by
        rw [← div_pow]
        exact hpow.trans h2
      have := mul_le_mul_of_nonneg_right hkey (pow_nonneg hkpos.le 6)
      rwa [div_mul_cancel₀ _ (pow_ne_zero 6 hkpos.ne')] at this
    have h1 : (k + 1) ^ 6 ≤ 2 * k ^ 6 := by
      have h1R' : ((k : ℝ) + 1) ^ 6 ≤ 2 * (k : ℝ) ^ 6 := h1R
      exact_mod_cast h1R'
    calc (k + 1) ^ 6 + 2 ≤ 2 * k ^ 6 + 2 := by omega
      _ ≤ 2 * (k ^ 6 + 2) := by omega
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (k + 1) := by rw [Nat.pow_succ]; ring

private lemma cube_le_floor (n Q : ℕ) (h : Q ^ 3 ≤ n) : Q ≤ ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ := by
  have hR : ((Q : ℝ)) ^ 3 ≤ (n : ℝ) := by exact_mod_cast h
  have hpow : (((Q : ℝ)) ^ 3) ^ (1 / 3 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hR (by norm_num)
  have hQid : (((Q : ℝ)) ^ 3) ^ (1 / 3 : ℝ) = (Q : ℝ) := by
    rw [← Real.rpow_natCast (x := (Q : ℝ)) 3]
    rw [← Real.rpow_mul (by positivity)]
    norm_num
  rw [hQid] at hpow
  exact Nat.le_floor hpow

private lemma indicator_three_zone (A B C : Set ℝ) (g : ℝ → ℂ)
    (hAB : A ⊆ B) (hBC : B ⊆ C) (t : ℝ) :
    Aᶜ.indicator g t = ((B \ A).indicator g t + (C \ B).indicator g t) + Cᶜ.indicator g t := by
  by_cases hA : t ∈ A
  · have hB : t ∈ B := hAB hA
    have hC : t ∈ C := hBC hB
    simp [Set.indicator_of_notMem, hA, hB, hC]
  · by_cases hB : t ∈ B
    · have hC : t ∈ C := hBC hB
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hA, hB, hC]
    · by_cases hC : t ∈ C
      · simp [Set.indicator_of_mem, Set.indicator_of_notMem, hA, hB, hC]
      · simp [Set.indicator_of_notMem, hA, hB, hC]

private def arcBand (K K' n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ K ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / (q : ℝ)| ≤ (K' : ℝ) / ((q : ℝ) * (n : ℝ))}

private lemma measurableSet_arcBand (K K' n : ℕ) : MeasurableSet (arcBand K K' n) := by
  have hEq : arcBand K K' n =
      ⋃ (p : {p : ℕ × ℕ // 1 ≤ p.1 ∧ p.1 ≤ K ∧ p.2 ≤ p.1 ∧ Nat.Coprime p.2 p.1}),
        {t : ℝ | |t - (p.1.2 : ℝ) / (p.1.1 : ℝ)| ≤ (K' : ℝ) / ((p.1.1 : ℝ) * (n : ℝ))} := by
    ext t
    simp only [arcBand, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨q, a, h1, h2, h3, h4, h5⟩
      exact ⟨⟨(q, a), h1, h2, h3, h4⟩, h5⟩
    · rintro ⟨⟨⟨q, a⟩, h1, h2, h3, h4⟩, h5⟩
      exact ⟨q, a, h1, h2, h3, h4, h5⟩
  rw [hEq]
  exact MeasurableSet.iUnion (fun p =>
    measurableSet_le (Continuous.measurable (by continuity)) measurable_const)

private lemma arcBand_mono_K {K1 K2 K' n : ℕ} (h : K1 ≤ K2) :
    arcBand K1 K' n ⊆ arcBand K2 K' n := by
  rintro t ⟨q, a, h1, h2, h3, h4, h5⟩
  exact ⟨q, a, h1, h2.trans h, h3, h4, h5⟩

private lemma arcBand_mono_radius {K K1 K2 n : ℕ} (h : K1 ≤ K2) (hn : 0 < n) :
    arcBand K K1 n ⊆ arcBand K K2 n := by
  rintro t ⟨q, a, h1, h2, h3, h4, h5⟩
  refine ⟨q, a, h1, h2, h3, h4, ?_⟩
  have hden : (0 : ℝ) < (q : ℝ) * (n : ℝ) := by
    have hq : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity
  have hcast : (K1 : ℝ) ≤ (K2 : ℝ) := by exact_mod_cast h
  exact h5.trans (by
    rw [div_le_div_iff_of_pos_right hden]
    exact hcast)

private def wfun (k : ℕ) : ℝ := if Nat.Prime k then Real.log (k : ℝ) else 0

private def Efun (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

private def Sfun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) : ℂ :=
  Finset.sum (Finset.range (n + 1)) (fun k => (u k : ℂ) * Efun ((k : ℝ) * t))

private def Ffun (n : ℕ) (t : ℝ) : ℂ := (Sfun n wfun t) ^ 2 * Efun (-(n : ℝ) * t)

private lemma continuous_Efun : Continuous Efun := by
  unfold Efun
  fun_prop

private lemma continuous_Ffun (n : ℕ) : Continuous (Ffun n) := by
  unfold Ffun
  apply Continuous.mul
  · apply Continuous.pow
    unfold Sfun
    exact continuous_finsetSum _ (fun k hk =>
      Continuous.mul continuous_const (continuous_Efun.comp (by fun_prop)))
  · exact continuous_Efun.comp (by fun_prop)

private lemma zone_split (A B C : Set ℝ) (F : ℝ → ℂ)
    (hAB : A ⊆ B) (hBC : B ⊆ C)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hF : Continuous F) :
    intervalIntegral (fun t => Aᶜ.indicator F t) (0 : ℝ) 1 MeasureTheory.volume =
      (intervalIntegral (fun t => (B \ A).indicator F t) (0 : ℝ) 1 MeasureTheory.volume +
       intervalIntegral (fun t => (C \ B).indicator F t) (0 : ℝ) 1 MeasureTheory.volume) +
      intervalIntegral (fun t => Cᶜ.indicator F t) (0 : ℝ) 1 MeasureTheory.volume := by
  have hFint : IntervalIntegrable F MeasureTheory.volume (0 : ℝ) 1 :=
    hF.intervalIntegrable 0 1
  have h1 : IntervalIntegrable (fun t => (B \ A).indicator F t) MeasureTheory.volume (0 : ℝ) 1 :=
    ⟨hFint.1.indicator (hB.diff hA), hFint.2.indicator (hB.diff hA)⟩
  have h2 : IntervalIntegrable (fun t => (C \ B).indicator F t) MeasureTheory.volume (0 : ℝ) 1 :=
    ⟨hFint.1.indicator (hC.diff hB), hFint.2.indicator (hC.diff hB)⟩
  have h3 : IntervalIntegrable (fun t => Cᶜ.indicator F t) MeasureTheory.volume (0 : ℝ) 1 :=
    ⟨hFint.1.indicator hC.compl, hFint.2.indicator hC.compl⟩
  have h12 : IntervalIntegrable
      (fun t => (B \ A).indicator F t + (C \ B).indicator F t) MeasureTheory.volume (0 : ℝ) 1 :=
    h1.add h2
  calc intervalIntegral (fun t => Aᶜ.indicator F t) (0 : ℝ) 1 MeasureTheory.volume
      = intervalIntegral
          (fun t => ((B \ A).indicator F t + (C \ B).indicator F t) + Cᶜ.indicator F t)
          (0 : ℝ) 1 MeasureTheory.volume := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact indicator_three_zone A B C F hAB hBC t
    _ = intervalIntegral (fun t => (B \ A).indicator F t + (C \ B).indicator F t)
          (0 : ℝ) 1 MeasureTheory.volume +
        intervalIntegral (fun t => Cᶜ.indicator F t) (0 : ℝ) 1 MeasureTheory.volume :=
        intervalIntegral.integral_add h12 h3
    _ = (intervalIntegral (fun t => (B \ A).indicator F t) (0 : ℝ) 1 MeasureTheory.volume +
         intervalIntegral (fun t => (C \ B).indicator F t) (0 : ℝ) 1 MeasureTheory.volume) +
        intervalIntegral (fun t => Cᶜ.indicator F t) (0 : ℝ) 1 MeasureTheory.volume := by
        rw [intervalIntegral.integral_add h1 h2]

theorem PEqualNP.Outside.L_goldbach_frontier_three_zone_split :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let minor := fun n : ℕ => intervalIntegral (fun t => (arcs n)ᶜ.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let midArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let medCore := fun n : ℕ => intervalIntegral (fun t => (midArcs n \ arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let medSkirt := fun n : ℕ => intervalIntegral (fun t => (wideArcs n \ midArcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let deepMinor := fun n : ℕ => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → minor n = (medCore n + medSkirt n) + deepMinor n := by
  dsimp only
  refine ⟨2 ^ 30, fun n hn => ?_⟩
  have hnpos : 0 < n := by
    have h2 : (0 : ℕ) < 2 ^ 30 := by norm_num
    omega
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hQ1ge : 1 ≤ ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ :=
    Nat.le_floor (Real.one_le_rpow hn1R (by norm_num))
  have hk30 : 30 ≤ Nat.log 2 (n + 2) := by
    apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
    omega
  have hk6 : (Nat.log 2 (n + 2)) ^ 6 ≤ n := by
    have h1 : (Nat.log 2 (n + 2)) ^ 6 + 2 ≤ 2 ^ (Nat.log 2 (n + 2)) :=
      six_le_two_pow (Nat.log 2 (n + 2)) hk30
    have h2 : 2 ^ (Nat.log 2 (n + 2)) ≤ n + 2 :=
      Nat.pow_log_le_self 2 (by omega)
    omega
  have hcube : ((Nat.log 2 (n + 2)) ^ 2) ^ 3 ≤ n := by
    have hpow : ((Nat.log 2 (n + 2)) ^ 2) ^ 3 = (Nat.log 2 (n + 2)) ^ 6 := by ring
    rw [hpow]
    exact hk6
  have hQ : (Nat.log 2 (n + 2)) ^ 2 ≤ ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ :=
    cube_le_floor n ((Nat.log 2 (n + 2)) ^ 2) hcube
  have hQH : (Nat.log 2 (n + 2)) ^ 2 ≤ 256 * ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ * (Nat.log 2 (n + 2)) ^ 2 := by
    have h1 : 1 ≤ 256 * ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ := by omega
    calc (Nat.log 2 (n + 2)) ^ 2 = 1 * (Nat.log 2 (n + 2)) ^ 2 := by rw [one_mul]
      _ ≤ (256 * ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊) * (Nat.log 2 (n + 2)) ^ 2 :=
          Nat.mul_le_mul_right _ h1
  exact zone_split (arcBand ((Nat.log 2 (n + 2)) ^ 2) ((Nat.log 2 (n + 2)) ^ 2) n)
    (arcBand ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ ((Nat.log 2 (n + 2)) ^ 2) n)
    (arcBand ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
      (256 * ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ * (Nat.log 2 (n + 2)) ^ 2) n)
    (Ffun n)
    (arcBand_mono_K hQ) (arcBand_mono_radius hQH hnpos)
    (measurableSet_arcBand _ _ _) (measurableSet_arcBand _ _ _) (measurableSet_arcBand _ _ _)
    (continuous_Ffun n)
