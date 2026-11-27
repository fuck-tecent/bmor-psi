import BandReduction

namespace GoldbachMinor

open Finset GoldbachWeight

/-- Total ordered pair weight at a given absolute frequency, with both signs included. -/
noncomputable def pairMass (n k : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ p ∈ range (n+1), ∑ r ∈ range (n+1),
    if (offset n p r).natAbs = k then w p * w r else 0

/-- Signed numerator of the nonzero major-arc coefficient, including the pair mass. -/
noncomputable def tailWave (Q n k : ℕ) (w : ℕ → ℝ) : ℝ :=
  pairMass n k w * ∑ q ∈ Icc 1 Q, ram q k *
    Real.sin (2*Real.pi*(k:ℝ)*((Q:ℝ)/(q*n)))

private theorem wave_quotient (Q n k : ℕ) (w : ℕ → ℝ) :
    (Real.pi * k)⁻¹ * tailWave Q n k w = pairMass n k w * majorCoefficient Q n k := by
  unfold tailWave majorCoefficient
  simp_rw [div_eq_mul_inv, ← mul_assoc]
  rw [← sum_mul]
  ring

private theorem group_modes (n : ℕ) (w f : ℕ → ℝ) :
    ∑ k ∈ range (n+1), pairMass n k w * f k =
    ∑ p ∈ range (n+1), ∑ r ∈ range (n+1), w p * w r * f (offset n p r).natAbs := by
  unfold pairMass
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  rw [sum_comm]
  apply sum_congr rfl
  intro r hr
  have hb : (offset n p r).natAbs ∈ range (n+1) := by
    simp only [mem_range] at *
    unfold offset
    omega
  simp_rw [ite_mul, zero_mul]
  simp [hb]

theorem trimmed_frequency_sum (Q n K : ℕ) (w : ℕ → ℝ) :
    trimmedBulk Q n K w =
      pairMass n 0 w * (1 - arcLength Q n) -
        ∑ k ∈ Ioc K n, (Real.pi*k)⁻¹ * tailWave Q n k w := by
  let f (k : ℕ) := if k = 0 ∨ K < k then minorCoefficient Q n k else 0
  have hg := group_modes n w f
  have ht : trimmedBulk Q n K w = ∑ k ∈ range (n+1), pairMass n k w * f k := by
    rw [hg]
    unfold trimmedBulk
    simp only [f, mul_ite, mul_zero, Int.natAbs_eq_zero]
  rw [ht]
  have split (k : ℕ) : pairMass n k w * f k =
      (if k = 0 then pairMass n 0 w * (1-arcLength Q n) else 0) -
      (if K < k then (Real.pi*k)⁻¹ * tailWave Q n k w else 0) := by
    rw [wave_quotient]
    by_cases hz : k = 0
    · subst k; simp [f,minorCoefficient]
    · by_cases hk : K < k <;> simp [f,minorCoefficient,hz,hk]
  simp_rw [split, sum_sub_distrib]
  simp only [sum_ite_eq', mem_range, Nat.zero_lt_succ, ite_true]
  rw [← sum_filter]
  congr 2
  ext k
  simp [and_comm]

/-- Prefix of the oscillatory numerator strictly above the removed band. -/
noncomputable def tailPrefix (Q n K t : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Ioc K t, tailWave Q n k w

/-- Summation by parts with prefixes starting strictly after K, including the last endpoint. -/
private theorem harmonic_prefix_identity (a : ℕ → ℝ) (K n : ℕ) :
    let S := fun t => ∑ k ∈ Ioc K t, a k
    (∑ k ∈ Ioc K n, (k:ℝ)⁻¹ * a k) =
      (n:ℝ)⁻¹ * S n + ∑ k ∈ Ioo K n, ((k:ℝ)⁻¹ - ((k+1:ℕ):ℝ)⁻¹) * S k := by
  dsimp only
  by_cases hn : K < n
  · induction n, hn using Nat.le_induction with
    | base =>
      simp [show Ioc K (K+1) = {K+1} by ext; simp,
        show Ioo K (K+1) = ∅ by ext; simp]
    | succ t ht ih =>
      have hc : Ioc K (t+1) = insert (t+1) (Ioc K t) := by ext; simp; omega
      have ho : Ioo K (t+1) = insert t (Ioo K t) := by ext; simp; omega
      rw [hc,ho]
      simp only [mem_Ioc,mem_Ioo,not_lt_of_ge le_rfl,Nat.not_succ_le_self,
        and_false,not_false_eq_true,sum_insert]
      rw [ih]
      ring
  · have hc := Ioc_eq_empty_of_le (Nat.le_of_not_gt hn)
    have ho : Ioo K n = ∅ := by ext; simp; omega
    simp [hc,ho]

/-- Signed loss as an endpoint and a positive-weighted sum of the signed prefixes. -/
noncomputable def prefixLoss (Q n K : ℕ) (w : ℕ → ℝ) : ℝ :=
  Real.pi⁻¹ * ((n:ℝ)⁻¹ * tailPrefix Q n K n w +
    ∑ k ∈ Ioo K n, ((k:ℝ)⁻¹ - ((k+1:ℕ):ℝ)⁻¹) * tailPrefix Q n K k w)

theorem trimmed_prefix_identity (Q n K : ℕ) (w : ℕ → ℝ) :
    trimmedBulk Q n K w = pairMass n 0 w * (1-arcLength Q n) - prefixLoss Q n K w := by
  rw [trimmed_frequency_sum]
  unfold prefixLoss tailPrefix
  rw [← harmonic_prefix_identity, mul_sum]
  simp only [mul_inv, mul_assoc]

/-- Exact signed prefix criterion; no supremum bound on individual prefixes is assumed. -/
theorem catalogue_prefix_loss_iff : FrozenBulk.BulkFloor ↔
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, Even n →
      let Q := catalogueCutoff n
      prefixLoss Q n (primeBandWidth n) (high n) ≤
        pairMass n 0 (high n) * (1-arcLength Q n) + ε*n := by
  rw [catalogue_prime_band_iff]
  simp_rw [trimmed_prefix_identity]
  constructor <;> intro h ε he <;> obtain ⟨N,hN⟩ := h ε he <;>
    refine ⟨N,fun n hn hev => ?_⟩ <;> have h' := hN n hn hev <;>
    linarith only [h']

private theorem harmonic_prefix_bound (a : ℕ → ℝ) (K m : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (h : ∀ t ∈ Ioc K m, (∑ k ∈ Ioc K t, a k) ≤ B) :
    (∑ k ∈ Ioc K m, (k:ℝ)⁻¹ * a k) ≤ ((K:ℝ)+1)⁻¹ * B := by
  let S (t : ℕ) := ∑ k ∈ Ioc K t, a k
  have step : ∀ t, K < t → (∀ j ∈ Ioc K t, S j ≤ B) →
      (∑ k ∈ Ioc K t, (k:ℝ)⁻¹ * a k) ≤
      ((K:ℝ)+1)⁻¹ * B + (t:ℝ)⁻¹ * (S t - B) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base =>
      intro _
      simp [S, show Ioc K (K+1) = {K+1} by ext; simp]
      ring_nf
      exact le_rfl
    | succ t ht ih =>
      intro hst
      have hp := ih (fun j hj => hst j (mem_Ioc.mpr ⟨(mem_Ioc.mp hj).1,(mem_Ioc.mp hj).2.trans (Nat.le_succ _)⟩))
      have hs := hst t (mem_Ioc.mpr ⟨ht, Nat.le_succ _⟩)
      have hd : ((t+1:ℕ):ℝ)⁻¹ ≤ (t:ℝ)⁻¹ := by
        apply inv_anti₀ <;> exact_mod_cast (by omega : _)
      have hx := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hd) (sub_nonpos.mpr hs)
      have hrec : Ioc K (t+1) = insert (t+1) (Ioc K t) := by ext; simp; omega
      have hnot : t+1 ∉ Ioc K t := by simp
      have heq : S (t+1) = a (t+1) + S t := by simp [S,hrec,hnot]
      rw [hrec,sum_insert hnot,heq]
      nlinarith only [hx,hp]
  by_cases ht : K < m
  · have hx := step m ht h
    have hs := h m (mem_Ioc.mpr ⟨ht,le_rfl⟩)
    have hneg : (m:ℝ)⁻¹ * (S m - B) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hs)
    exact hx.trans (by linarith)
  · simp only [Ioc_eq_empty_of_le (Nat.le_of_not_gt ht), sum_empty]
    positivity

/-- A one-sided prefix bound controls the signed loss from the diagonal. -/
theorem trimmed_of_prefix (Q n K : ℕ) (w : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ t ∈ Ioc K n, tailPrefix Q n K t w ≤ B) :
    pairMass n 0 w * (1-arcLength Q n) - B / (Real.pi*((K:ℝ)+1)) ≤
      trimmedBulk Q n K w := by
  rw [trimmed_frequency_sum]
  have hh := harmonic_prefix_bound (fun k => tailWave Q n k w) K n B hB h
  have key := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr Real.pi_pos.le)
  rw [mul_sum] at key
  simp_rw [← mul_assoc, ← mul_inv] at key
  convert sub_le_sub_left key (pairMass n 0 w * (1-arcLength Q n)) using 1
  simp only [div_eq_mul_inv]
  ring

/-- A sufficient cancellation estimate with the exact diagonal allowance at each even target. -/
theorem catalogue_bulk_of_prefix_budget
    (bound : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, Even n →
      let K := primeBandWidth n
      let Q := catalogueCutoff n
      ∀ t ∈ Icc K n, tailPrefix Q n K t (high n) ≤
        Real.pi * ((K:ℝ)+1) * (pairMass n 0 (high n) * (1-arcLength Q n) + ε*n)) :
    FrozenBulk.BulkFloor := by
  apply catalogue_prime_band_iff.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := bound ε hε
  refine ⟨N,fun n hn heven => ?_⟩
  let K := primeBandWidth n
  let Q := catalogueCutoff n
  let D := pairMass n 0 (high n) * (1-arcLength Q n)
  let B := Real.pi * ((K:ℝ)+1) * (D+ε*n)
  have hK : K ≤ n := Nat.div_le_self _ _
  have hp : ∀ t ∈ Icc K n, tailPrefix Q n K t (high n) ≤ B := hN n hn heven
  have hz := hp K (mem_Icc.mpr ⟨le_rfl,hK⟩)
  have hB : 0 ≤ B := by simpa [tailPrefix] using hz
  have htail := trimmed_of_prefix Q n K (high n) B hB (fun t ht =>
    hp t (mem_Icc.mpr ⟨(mem_Ioc.mp ht).1.le,(mem_Ioc.mp ht).2⟩))
  have cancel : B / (Real.pi*((K:ℝ)+1)) = D+ε*n := by
    dsimp only [B]
    field_simp [Real.pi_ne_zero,show (K:ℝ)+1 ≠ 0 by positivity]
  rw [cancel] at htail
  change -(ε*(n:ℝ)) ≤ trimmedBulk Q n K (high n)
  change D - (D + ε*n) ≤ _ at htail
  linarith only [htail]

#print axioms catalogue_prefix_loss_iff
#print axioms catalogue_bulk_of_prefix_budget

end GoldbachMinor
