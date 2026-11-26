import Mathlib

theorem PEqualNP.Outside.L_goldbach_liouville_dilation_bessel_aux.sum_filter_dvd (d m : ℕ) (hd : 0 < d) (g : ℕ → ℝ) :
    ∑ t ∈ (Finset.range (d*m)).filter (fun t => d ∣ t), g t = ∑ s ∈ Finset.range m, g (d*s) := by
  have hset : (Finset.range (d*m)).filter (fun t => d ∣ t) = (Finset.range m).image (fun s => d * s) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨ht, ⟨s, rfl⟩⟩
      exact ⟨s, Nat.lt_of_mul_lt_mul_left ht, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨Nat.mul_lt_mul_of_pos_left hs hd, dvd_mul_right d s⟩
  rw [hset, Finset.sum_image]
  intro x _ y _ hxy
  exact Nat.eq_of_mul_eq_mul_left hd hxy

theorem PEqualNP.Outside.L_goldbach_liouville_dilation_bessel_aux.ind_sum (d N : ℕ) (hd : 0 < d) (hdN : d ∣ N) :
    (d:ℝ) * ∑ t ∈ Finset.range N, (if d ∣ t then (1:ℝ) else 0) = N := by
  obtain ⟨m, rfl⟩ := hdN
  rw [← Finset.sum_filter, PEqualNP.Outside.L_goldbach_liouville_dilation_bessel_aux.sum_filter_dvd d m hd]
  simp

theorem PEqualNP.Outside.L_goldbach_liouville_dilation_bessel_aux.len_mul (p s : ℕ) (hp : Nat.Prime p) (hs : s ≠ 0) :
    (p*s).primeFactorsList.length = s.primeFactorsList.length + 1 := by
  have h := (Nat.perm_primeFactorsList_mul hp.ne_zero hs).length_eq
  rw [h, List.length_append, Nat.primeFactorsList_prime hp]
  simp only [List.length_singleton]
  omega

theorem PEqualNP.Outside.L_goldbach_liouville_dilation_bessel_aux.cov (N p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpN : p ∣ N) (hqN : q ∣ N) :
    ∑ t ∈ Finset.range N, ((p:ℝ)*(if p ∣ t then 1 else 0)-1) * ((q:ℝ)*(if q ∣ t then 1 else 0)-1)
      = if p = q then (N:ℝ)*((p:ℝ)-1) else 0 := by
  have hSp := PEqualNP.Outside.L_goldbach_liouville_dilation_bessel_aux.ind_sum p N hp.pos hpN
  have hSq := PEqualNP.Outside.L_goldbach_liouville_dilation_bessel_aux.ind_sum q N hq.pos hqN
  by_cases hpq : p = q
  · subst hpq
    rw [show (if p = p then (N:ℝ)*((p:ℝ)-1) else 0) = (N:ℝ)*((p:ℝ)-1) from by simp]
    have hpt : ∀ t, ((p:ℝ)*(if p ∣ t then 1 else 0)-1) * ((p:ℝ)*(if p ∣ t then 1 else 0)-1)
        = ((p:ℝ)^2 - 2*p) * (if p ∣ t then 1 else 0) + 1 := by
      intro t
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun t _ => hpt t), Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    linear_combination ((p:ℝ) - 2) * hSp
  · rw [show (if p = q then (N:ℝ)*((p:ℝ)-1) else 0) = 0 from by simp [hpq]]
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
    have hpqN : p*q ∣ N := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpN hqN
    have hSpq := PEqualNP.Outside.L_goldbach_liouville_dilation_bessel_aux.ind_sum (p*q) N (Nat.mul_pos hp.pos hq.pos) hpqN
    push_cast at hSpq
    have hpt : ∀ t, ((p:ℝ)*(if p ∣ t then 1 else 0)-1) * ((q:ℝ)*(if q ∣ t then 1 else 0)-1)
        = ((p:ℝ)*q) * (if p*q ∣ t then 1 else 0)
        - (p:ℝ) * (if p ∣ t then 1 else 0) - (q:ℝ) * (if q ∣ t then 1 else 0) + 1 := by
      intro t
      by_cases ha : p ∣ t
      · by_cases hb : q ∣ t
        · have h3 : p*q ∣ t := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop ha hb
          simp only [ha, hb, h3, ↓reduceIte]
          ring
        · have h3 : ¬ p*q ∣ t := fun h => hb (dvd_trans (dvd_mul_left q p) h)
          simp only [ha, hb, h3, ↓reduceIte]
          ring
      · have h3 : ¬ p*q ∣ t := fun h => ha (dvd_trans (dvd_mul_right p q) h)
        by_cases hb : q ∣ t
        · simp only [ha, hb, h3, ↓reduceIte]
          ring
        · simp only [ha, hb, h3, ↓reduceIte]
          ring
    rw [Finset.sum_congr rfl (fun t _ => hpt t)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
    linear_combination hSpq - hSp - hSq

theorem PEqualNP.Outside.L_goldbach_liouville_dilation_bessel_aux.bessel (P T : Finset ℕ) (φ : ℕ → ℕ → ℝ)
    (w g a : ℕ → ℝ)
    (horth : ∀ i ∈ P, ∀ j ∈ P, ∑ t ∈ T, φ i t * φ j t = if i = j then w i else 0)
    (hw : ∀ i ∈ P, 0 < w i) (ha : ∀ i ∈ P, ∑ t ∈ T, g t * φ i t = a i) :
    ∑ i ∈ P, a i ^ 2 / w i ≤ ∑ t ∈ T, g t ^ 2 := by
  have h0 : 0 ≤ ∑ t ∈ T, (g t - ∑ i ∈ P, a i / w i * φ i t) ^ 2 :=
    Finset.sum_nonneg (fun t _ => sq_nonneg _)
  have hK : ∀ (K : ℝ) (i : ℕ), ∑ t ∈ T, g t * (K * φ i t) = K * ∑ t ∈ T, g t * φ i t := by
    intro K i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun t _ => by ring)
  have e1 : ∑ t ∈ T, g t * (∑ i ∈ P, a i / w i * φ i t) = ∑ i ∈ P, a i / w i * a i := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [hK, ha i hi]
  have e2 : ∑ t ∈ T, (∑ i ∈ P, a i / w i * φ i t) ^ 2 = ∑ i ∈ P, a i / w i * (a i / w i) * w i := by
    simp only [sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.sum_comm]
    have hj : ∀ j ∈ P, ∑ t ∈ T, a i / w i * φ i t * (a j / w j * φ j t)
        = if i = j then a i / w i * (a i / w i) * w i else 0 := by
      intro j hj
      have h := horth i hi j hj
      have h2 : ∑ t ∈ T, a i / w i * φ i t * (a j / w j * φ j t)
          = a i / w i * (a j / w j) * ∑ t ∈ T, φ i t * φ j t := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun t _ => by ring)
      rw [h2, h]
      split_ifs with hij
      · subst hij
        ring
      · ring
    rw [Finset.sum_congr rfl hj]
    simp [hi]
  have e3 : ∀ t, (g t - ∑ i ∈ P, a i / w i * φ i t) ^ 2
      = g t ^ 2 - 2 * (g t * ∑ i ∈ P, a i / w i * φ i t) + (∑ i ∈ P, a i / w i * φ i t) ^ 2 := by
    intro t
    ring
  rw [Finset.sum_congr rfl (fun t _ => e3 t), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, e1, e2] at h0
  have e4 : ∀ i ∈ P, a i / w i * a i = a i ^ 2 / w i := by
    intro i _
    ring
  have e5 : ∀ i ∈ P, a i / w i * (a i / w i) * w i = a i ^ 2 / w i := by
    intro i hi
    have := (hw i hi).ne'
    field_simp
  rw [Finset.sum_congr rfl e4, Finset.sum_congr rfl e5] at h0
  linarith

open PEqualNP.Outside.L_goldbach_liouville_dilation_bessel_aux in
theorem PEqualNP.Outside.L_goldbach_liouville_dilation_bessel :
    let L := fun n : ℕ => if n=0 then (0:ℝ) else (-1:ℝ)^n.primeFactorsList.length; let C := fun n : ℕ => (∑ t ∈ Finset.range n, L t * L (n-t))/(n:ℝ); ∀ N : ℕ, 0 < N → (∑ p ∈ N.divisors.filter Nat.Prime, (C (N/p)-C N)^2/((p:ℝ)-1)) ≤ ((N-1:ℕ):ℝ)/(N:ℝ)-(C N)^2 := by
  intro L C N hN
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hL0 : L 0 = 0 := by simp [L]
  have hLsq : ∀ n, n ≠ 0 → L n ^ 2 = 1 := by
    intro n hn
    simp only [L, hn, ↓reduceIte]
    rw [← pow_mul, mul_comm, pow_mul]
    simp
  have hLp : ∀ p s, Nat.Prime p → L (p*s) = -L s := by
    intro p s hp
    by_cases hs : s = 0
    · subst hs
      simp [L]
    · have hps : p * s ≠ 0 := Nat.mul_ne_zero hp.ne_zero hs
      simp only [L, hs, hps, ↓reduceIte, len_mul p s hp hs, pow_succ]
      ring
  have hMA : ∀ p, Nat.Prime p → p ∣ N →
      ∑ t ∈ (Finset.range N).filter (fun t => p ∣ t), L t * L (N-t) = ((N/p:ℕ):ℝ) * C (N/p) := by
    intro p hp hpN
    obtain ⟨M, rfl⟩ := hpN
    rw [Nat.mul_div_cancel_left M hp.pos, sum_filter_dvd p M hp.pos]
    have hM0 : M ≠ 0 := by
      rintro rfl
      simp at hN
    have hM : (M:ℝ) ≠ 0 := by exact_mod_cast hM0
    have key : ∑ s ∈ Finset.range M, L (p*s) * L (p*M - p*s) = ∑ s ∈ Finset.range M, L s * L (M-s) := by
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [← Nat.mul_sub, hLp p s hp, hLp p (M-s) hp]
      ring
    rw [key]
    show _ = (M:ℝ) * ((∑ t ∈ Finset.range M, L t * L (M-t))/(M:ℝ))
    field_simp
  have hCN : ∑ t ∈ Finset.range N, L t * L (N-t) = (N:ℝ) * C N := by
    show _ = (N:ℝ) * ((∑ t ∈ Finset.range N, L t * L (N-t))/(N:ℝ))
    field_simp
  have hX0 : ∀ p, Nat.Prime p → p ∣ N →
      ∑ t ∈ Finset.range N, ((p:ℝ)*(if p ∣ t then 1 else 0)-1) = 0 := by
    intro p hp hpN
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ind_sum p N hp.pos hpN]
    simp
  have hfX : ∀ p, Nat.Prime p → p ∣ N →
      ∑ t ∈ Finset.range N, (L t * L (N-t) - C N) * ((p:ℝ)*(if p ∣ t then 1 else 0)-1)
        = (N:ℝ) * (C (N/p) - C N) := by
    intro p hp hpN
    have e : ∀ t, (L t * L (N-t) - C N) * ((p:ℝ)*(if p ∣ t then 1 else 0)-1)
        = (p:ℝ) * (if p ∣ t then L t * L (N-t) else 0) - L t * L (N-t)
          - C N * ((p:ℝ)*(if p ∣ t then 1 else 0)-1) := by
      intro t
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun t _ => e t), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hX0 p hp hpN, ← Finset.sum_filter, hMA p hp hpN, hCN]
    have hc : ((N/p:ℕ):ℝ) * p = N := by exact_mod_cast Nat.div_mul_cancel hpN
    linear_combination C (N/p) * hc
  have hf2 : ∑ t ∈ Finset.range N, (L t * L (N-t)) ^ 2 = ((N-1:ℕ):ℝ) := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [Finset.sum_range_succ']
    have h1 : ∀ i ∈ Finset.range M, (L (i+1) * L (M+1-(i+1))) ^ 2 = 1 := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [mul_pow, hLsq _ (by omega), hLsq _ (by omega)]
      ring
    rw [Finset.sum_congr rfl h1]
    simp [hL0]
  have hff : ∑ t ∈ Finset.range N, (L t * L (N-t) - C N) ^ 2 = ((N-1:ℕ):ℝ) - (N:ℝ) * C N ^ 2 := by
    have e : ∀ t, (L t * L (N-t) - C N) ^ 2 = (L t * L (N-t)) ^ 2 - 2 * C N * (L t * L (N-t)) + C N ^ 2 := by
      intro t
      ring
    rw [Finset.sum_congr rfl (fun t _ => e t), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hf2, hCN]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hP : ∀ p ∈ N.divisors.filter Nat.Prime, Nat.Prime p ∧ p ∣ N := by
    intro p hp
    rw [Finset.mem_filter, Nat.mem_divisors] at hp
    exact ⟨hp.2, hp.1.1⟩
  have hB := bessel (N.divisors.filter Nat.Prime) (Finset.range N)
    (fun p t => (p:ℝ)*(if p ∣ t then 1 else 0)-1) (fun p => (N:ℝ) * ((p:ℝ) - 1))
    (fun t => L t * L (N-t) - C N) (fun p => (N:ℝ) * (C (N/p) - C N))
    (fun i hi j hj => cov N i j (hP i hi).1 (hP j hj).1 (hP i hi).2 (hP j hj).2)
    (fun i hi => by
      have h2 : (2:ℝ) ≤ i := by exact_mod_cast (hP i hi).1.two_le
      exact mul_pos hNr (by linarith))
    (fun i hi => hfX i (hP i hi).1 (hP i hi).2)
  rw [hff] at hB
  have e : ∀ p ∈ N.divisors.filter Nat.Prime, ((N:ℝ) * (C (N/p) - C N)) ^ 2 / ((N:ℝ) * ((p:ℝ) - 1))
      = (N:ℝ) * ((C (N/p) - C N) ^ 2 / ((p:ℝ) - 1)) := by
    intro p hp
    have h2 : (2:ℝ) ≤ p := by exact_mod_cast (hP p hp).1.two_le
    have h3 : (p:ℝ) - 1 ≠ 0 := by linarith
    field_simp
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum] at hB
  rw [show ((N-1:ℕ):ℝ)/(N:ℝ) - C N ^ 2 = (((N-1:ℕ):ℝ) - (N:ℝ) * C N ^ 2)/(N:ℝ) by field_simp]
  rw [le_div_iff₀ hNr]
  linarith
