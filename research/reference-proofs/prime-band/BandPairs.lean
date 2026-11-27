import BandMask

/-! Expand the prime-weighted integral and bound the contribution of its nonzero near-diagonal modes. -/

namespace GoldbachWeight

open Finset

noncomputable def high (n k : ℕ) : ℝ :=
  if k ^ 3 ≤ n then 0 else if k.Prime then Real.log k else 0

noncomputable def phase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

noncomputable def spectrum (n : ℕ) (w : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n+1), (w k : ℂ) * phase ((k : ℝ)*t)

end GoldbachWeight

namespace GoldbachMinor

open Finset Set MeasureTheory GoldbachWeight

def offset (n p r : ℕ) : ℤ := (p:ℤ)+r-n

noncomputable def arithmeticBulk (Q n : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ p ∈ range (n+1), ∑ r ∈ range (n+1),
    w p * w r * minorCoefficient Q n (offset n p r).natAbs

private theorem expand_spectrum (n : ℕ) (w : ℕ → ℝ) (t : ℝ) :
    GoldbachWeight.spectrum n w t * GoldbachWeight.spectrum n w t * phase (-(n:ℝ)*t) =
    ∑ p ∈ range (n+1), ∑ r ∈ range (n+1), (↑(w p*w r):ℂ)*mode (offset n p r) t := by
  unfold GoldbachWeight.spectrum
  simp only [sum_mul,mul_sum]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro r _
  have hph : phase ((p:ℝ)*t) * phase ((r:ℝ)*t) * phase (-(n:ℝ)*t) = mode (offset n p r) t := by
    unfold phase mode offset
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  push_cast
  rw [← hph]
  ring

private theorem integrate_sum {ι : Type*} (s : Finset ι) (A : Set ℝ) (hA : MeasurableSet A)
    (f : ι → ℝ → ℂ) (hc : ∀ i ∈ s, Continuous (f i)) :
    (∫ t in (0:ℝ)..1, A.indicator (fun u => ∑ i ∈ s, f i u) t) =
      ∑ i ∈ s, ∫ t in (0:ℝ)..1, A.indicator (f i) t := by
  have point (t : ℝ) : A.indicator (fun u => ∑ i ∈ s, f i u) t = ∑ i ∈ s, A.indicator (f i) t := by
    by_cases h : t ∈ A <;> simp [h]
  simp_rw [point]
  apply intervalIntegral.integral_finsetSum
  intro i hi
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact ((hc i hi).integrableOn_Icc.mono_set Ioc_subset_Icc_self).indicator hA

/-- Exact finite arithmetic expression for the signed integral for any real weight. -/
theorem integral_eq_arithmeticBulk (Q n : ℕ) (hn : 2*Q^2<n) (w : ℕ → ℝ) :
    (∫ t in (0:ℝ)..1, (catalogueArcs Q n)ᶜ.indicator (fun u =>
      GoldbachWeight.spectrum n w u * GoldbachWeight.spectrum n w u * phase (-(n:ℝ)*u)) t)
      = (arithmeticBulk Q n w:ℂ) := by
  have hA := (measurable_catalogue Q n).compl
  have hc (p r : ℕ) : Continuous (fun t => (↑(w p*w r):ℂ)*mode (offset n p r) t) :=
    continuous_const.mul (mode_continuous _)
  simp_rw [expand_spectrum]
  rw [integrate_sum _ _ hA _ (fun p _ => continuous_finsetSum _ (fun r _ => hc p r))]
  unfold arithmeticBulk
  rw [Complex.ofReal_sum]
  apply sum_congr rfl
  intro p _
  rw [integrate_sum _ _ hA _ (fun r _ => hc p r), Complex.ofReal_sum]
  apply sum_congr rfl
  intro r _
  simp_rw [Set.indicator_const_mul,intervalIntegral.integral_const_mul,minor_mode Q n hn]
  push_cast
  rfl

end GoldbachMinor

namespace GoldbachMinor

open Finset GoldbachWeight

private def neighbours (n p K : ℕ) : Finset ℕ :=
  (range (n+1)).filter fun r => offset n p r ≠ 0 ∧ (offset n p r).natAbs ≤ K

noncomputable def nearBulk (Q n K : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ p ∈ range (n+1), ∑ r ∈ neighbours n p K,
    w p*w r*minorCoefficient Q n (offset n p r).natAbs

/-- Keep the diagonal and precisely the frequencies whose absolute value exceeds K. -/
noncomputable def trimmedBulk (Q n K : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ p ∈ range (n+1), ∑ r ∈ range (n+1), if offset n p r = 0 ∨ K < (offset n p r).natAbs then
    w p*w r*minorCoefficient Q n (offset n p r).natAbs else 0

theorem split_near (Q n K : ℕ) (w : ℕ → ℝ) :
    arithmeticBulk Q n w = nearBulk Q n K w + trimmedBulk Q n K w := by
  unfold arithmeticBulk nearBulk trimmedBulk neighbours
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  rw [sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro r _
  by_cases h : offset n p r ≠ 0 ∧ (offset n p r).natAbs ≤ K
  · simp [h]
  · have h' : offset n p r = 0 ∨ K < (offset n p r).natAbs := by omega
    simp [h,h']

def logWidth (n : ℕ) : ℕ := Nat.log 2 (n+2) + 1

end GoldbachMinor

namespace GoldbachMinor
open Finset GoldbachWeight

/-- At a fixed first index p, each positive absolute frequency occurs at most twice. -/
private theorem row_modes (n p K : ℕ) (f : ℕ → ℝ) (hf : ∀ k, 0≤f k) :
    (∑ r ∈ (range (n+1)).filter (fun r => offset n p r ≠ 0 ∧ (offset n p r).natAbs ≤ K),
      f (offset n p r).natAbs) ≤ 2 * ∑ k ∈ Finset.Icc 1 K, f k := by
  classical
  let S := (range (n+1)).filter (fun r => offset n p r ≠ 0 ∧ (offset n p r).natAbs ≤ K)
  let tag (r : ℕ) : ℕ × ℕ := (if offset n p r < 0 then 0 else 1,(offset n p r).natAbs)
  have inj : Set.InjOn tag S := by
    intro x _ y _ h
    have hs := congrArg Prod.fst h
    have hm := Int.natAbs_eq_natAbs_iff.mp (congrArg Prod.snd h : (offset n p x).natAbs = (offset n p y).natAbs)
    dsimp only [tag] at hs
    by_cases hx : offset n p x < 0 <;> by_cases hy : offset n p y < 0 <;>
      simp [hx,hy] at hs <;> unfold offset at * <;> omega
  have sub : S.image tag ⊆ range 2 ×ˢ Finset.Icc 1 K := by
    intro x hx
    obtain ⟨r,hr,rfl⟩ := mem_image.mp hx
    obtain ⟨_,hz,hm⟩ := mem_filter.mp hr
    exact mem_product.mpr ⟨mem_range.mpr (by dsimp [tag]; split <;> decide),mem_Icc.mpr ⟨Int.natAbs_pos.mpr hz,hm⟩⟩
  calc
    _ ≤ ∑ x ∈ range 2 ×ˢ Finset.Icc 1 K, f x.2 :=
      sum_le_sum_of_injOn tag inj sub (fun _ _ => le_rfl) (fun a _ _ => hf a.2)
    _ = _ := by simp [sum_product,two_mul]

private theorem near_mass_bound (Q n K : ℕ) (hn : 0<n) (w : ℕ → ℝ) (W : ℝ)
    (hW : 0≤W) (hw : ∀ p ≤ n, |w p| ≤ W) :
    |nearBulk Q n K w| ≤ (∑ p ∈ range (n+1), |w p|) * W * 2 *
      ((2*(Q:ℝ)/n)*K*(harmonicCutoff Q)^2) := by
  let B := (2*(Q:ℝ)/n)*K*(harmonicCutoff Q)^2
  let C (k : ℕ) := |majorCoefficient Q n k|
  let S (p : ℕ) := (range (n+1)).filter (fun r => offset n p r ≠ 0 ∧ (offset n p r).natAbs ≤ K)
  have row (p : ℕ) : |∑ r ∈ S p, w p*w r*minorCoefficient Q n (offset n p r).natAbs| ≤
      |w p| *(W*2*B) := by
    calc
      _ ≤ _ := Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑ r ∈ S p, (|w p| *W)*C (offset n p r).natAbs := by
        apply sum_le_sum
        intro r hr
        obtain ⟨hrn,hne,_⟩ := mem_filter.mp hr
        have hk := Int.natAbs_pos.mpr hne
        simp only [minorCoefficient,ne_of_gt hk,ite_false,abs_mul,abs_neg,C]
        gcongr
        exact hw r (by have := mem_range.mp hrn; omega)
      _ = (|w p| *W)* ∑ r ∈ S p, C (offset n p r).natAbs := (mul_sum ..).symm
      _ ≤ (|w p| *W)*(2*∑ k ∈ Finset.Icc 1 K, C k) := by
        apply mul_le_mul_of_nonneg_left (row_modes n p K C (fun _ => abs_nonneg _)) (by positivity)
      _ ≤ (|w p| *W)*(2*B) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left (coefficient_mean Q n K hn) (by norm_num)
      _ = _ := by ring
  unfold nearBulk
  refine (Finset.abs_sum_le_sum_abs ..).trans ((sum_le_sum (fun p _ => row p)).trans_eq ?_)
  rw [← sum_mul]; ring

private theorem high_nonneg (n p : ℕ) : 0≤high n p := by
  unfold high
  split_ifs <;> positivity

private theorem high_mass (n : ℕ) : (∑ p ∈ range (n+1), |high n p|) ≤ Real.log 4*n := by
  refine le_trans ?_ (Chebyshev.theta_le_log4_mul_x (show 0≤(n:ℝ) by positivity))
  rw [Chebyshev.theta_eq_sum_Icc,Nat.floor_natCast,sum_filter]
  have eq : Finset.Icc 0 n = range (n+1) := by ext k; simp
  rw [eq]
  apply sum_le_sum
  intro p _
  rw [abs_of_nonneg (high_nonneg n p)]
  unfold high
  split_ifs <;> first | exact le_rfl | positivity

private theorem high_le_log (n p : ℕ) (hn : 0<n) (hp : p≤n) : |high n p| ≤ Real.log n := by
  rw [abs_of_nonneg (high_nonneg n p)]
  unfold high
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  split_ifs with _ h
  · exact hlog
  · exact Real.log_le_log (by exact_mod_cast h.pos) (by exact_mod_cast hp)
  · exact hlog

/-- A finite estimate using only Chebyshev's upper bound and divisor averaging. -/
theorem prime_band_bound (Q n K : ℕ) (hn : 0<n) :
    |nearBulk Q n K (high n)| ≤ 4*Real.log 4*Real.log n*Q*K*(harmonicCutoff Q)^2 := by
  have hlog : 0≤Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hp : 0<(n:ℝ) := by exact_mod_cast hn
  calc
    _ ≤ _ := near_mass_bound Q n K hn (high n) _ hlog (fun p h => high_le_log n p hn h)
    _ ≤ (Real.log 4*n)*Real.log n*2*((2*(Q:ℝ)/n)*K*(harmonicCutoff Q)^2) := by
      gcongr
      exact high_mass n
    _ = _ := by field_simp; ring

end GoldbachMinor
