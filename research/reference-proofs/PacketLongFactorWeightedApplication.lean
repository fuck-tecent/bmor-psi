import Conjectures.Goldbach.PacketLongFactorCenters
import Conjectures.Goldbach.PacketTotientHarmonicBudget

open Finset Conjectures.Goldbach

/-- Apply both proposed inputs with the parent's exact primitive-numerator count and cutoff. -/
example (X Q H m : ℕ) (S : Finset ℕ) (u : ℝ) (hm : 0 < m) (hu : 0 < u)
    (hS : S ⊆ Icc 2 X)
    (factor : ∀ q ∈ S, ∃ d : ℕ, Odd d ∧ d ∣ q ∧
       ∀ h : ℕ, 1 ≤ h → h ≤ H → ¬ d ∣ 2 ^ h - 1) :
    let K := fun t : ℝ => (∑ j ∈ range m, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(m:ℝ)
    let hits := fun q : ℕ => ((range (q+1)).filter
      (fun a => Nat.Coprime a q ∧ u < K ((a:ℝ)/(q:ℝ)))).card
    (m:ℝ) * u^2 * (∑ q ∈ S, min (1:ℝ) ((q:ℝ)/(Q:ℝ)) * (hits q : ℝ) /
        (q.totient : ℝ)^2) ≤
      (((m-1)/(H+1)+1 : ℕ):ℝ) * (Real.exp (Real.pi^2)*(1+Real.log (X:ℝ))) := by
  intro K hits
  let c : ℝ := (((m-1)/(H+1)+1 : ℕ):ℝ)
  have hsub : S ⊆ Icc 1 X := fun q h => mem_Icc.mpr
    ⟨by have := (mem_Icc.mp (hS h)).1; omega, (mem_Icc.mp (hS h)).2⟩
  have hrow (q : ℕ) (hq : q ∈ S) :
      (m:ℝ)*u^2 * (min (1:ℝ) ((q:ℝ)/(Q:ℝ))*(hits q:ℝ)/(q.totient:ℝ)^2)
        ≤ c * ((q:ℝ)/(q.totient:ℝ)^2) := by
    obtain ⟨d,hd,hdq,hperiod⟩ := factor q hq
    have h := PacketLongFactorCenters q d H m u (mem_Icc.mp (hS hq)).1 hm hu hd hdq hperiod
    change (m:ℝ)*u^2*(hits q : ℝ) ≤ (q:ℝ)*c at h
    have hn : 0 ≤ (m:ℝ)*u^2*(hits q : ℝ) := by positivity
    have hc := mul_le_mul_of_nonneg_right (min_le_left 1 ((q:ℝ)/(Q:ℝ))) hn
    rw [one_mul] at hc
    have v := div_le_div_of_nonneg_right (hc.trans h) (sq_nonneg (q.totient:ℝ))
    convert v using 1 <;> ring
  rw [mul_sum]
  calc
    _ ≤ _ := sum_le_sum hrow
    _ = _ := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)).trans
        (PacketTotientHarmonicBudget X)) (by dsimp [c]; positivity)
