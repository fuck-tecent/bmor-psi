import Mathlib

open Finset
namespace Conjectures.Goldbach.PacketTotientHarmonicBudget_aux
noncomputable section

private abbrev weight (p : ℕ) : ℝ := 6 / (p : ℝ)
private abbrev denom (s : Finset ℕ) : ℕ := ∏ p ∈ s, p

private theorem point {n : ℕ} (hn : 0 < n) :
    (n : ℝ) / (n.totient : ℝ)^2 ≤
      (∑ s ∈ n.primeFactors.powerset, ∏ p ∈ s, weight p) / n := by
  have hphi : (n.totient : ℝ) =
      (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have h := congrArg (fun t : ℚ => (t : ℝ)) (Nat.totient_eq_mul_prod_factors n)
    push_cast at h
    exact h
  have loc (p : ℕ) (hp : p ∈ n.primeFactors) :
      ((1 - (p : ℝ)⁻¹)⁻¹)^2 ≤ 1 + weight p := by
    have hp' : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hsub : 0 < (p : ℝ) - 1 := by linarith
    rw [show (1-(p:ℝ)⁻¹)⁻¹ = p / ((p:ℝ)-1) by field_simp]
    dsimp [weight]
    rw [div_pow, div_le_iff₀ (sq_pos_of_pos hsub)]
    field_simp
    nlinarith [sq_nonneg ((p : ℝ)-2), mul_nonneg (sub_nonneg.mpr hp') (show 0 ≤ (p:ℝ)-1 by linarith)]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← prod_one_add]
  have hprod := prod_le_prod₀ (fun p (_ : p ∈ n.primeFactors) => sq_nonneg ((1-(p:ℝ)⁻¹)⁻¹)) loc
  calc
    (n:ℝ)/(n.totient:ℝ)^2 = (∏ p ∈ n.primeFactors, ((1-(p:ℝ)⁻¹)⁻¹)^2) / n := by
      rw [hphi, prod_pow, prod_inv_distrib, mul_pow]
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hprod (Nat.cast_nonneg n)

private theorem multiples (X D : ℕ) (hD : 0 < D) :
    (∑ n ∈ (Icc 1 X).filter (fun n => D ∣ n), (n : ℝ)⁻¹) ≤
      (∑ k ∈ Icc 1 X, (k : ℝ)⁻¹) / D := by
  let s := (Icc 1 X).filter (fun n => D ∣ n)
  have spec {n : ℕ} (hn : n ∈ s) : n/D*D=n := Nat.div_mul_cancel (mem_filter.mp hn).2
  have maps {n : ℕ} (hn : n ∈ s) : n / D ∈ Icc 1 X := by
    obtain ⟨hpos, hmax⟩ := mem_Icc.mp (mem_filter.mp hn).1
    exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hpos (mem_filter.mp hn).2) hD,
      (Nat.div_le_self ..).trans hmax⟩
  have inj : Set.InjOn (fun n => n/D) (s : Set ℕ) := by
    intro n hn k hk he
    calc n = n/D*D := (spec hn).symm
         _ = k/D*D := congrArg (· * D) he
         _ = k := spec hk
  change (∑ n ∈ s, (n:ℝ)⁻¹) ≤ _
  calc
    _ = ∑ n ∈ s, (((n/D:ℕ):ℝ)⁻¹ / D) := by
      apply sum_congr rfl
      intro n hn
      conv_lhs => rw [← spec hn]
      simp [div_eq_mul_inv, mul_comm]
    _ = (∑ k ∈ s.image (· / D), (k:ℝ)⁻¹) / D := by rw [sum_div, sum_image inj]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg D)
      exact sum_le_sum_of_subset_of_nonneg (fun k hk => by
        obtain ⟨n,hn,rfl⟩ := mem_image.mp hk; exact maps hn) (fun k _ _ => by positivity)

private theorem factor_budget (P : Finset ℕ) :
    (∏ p ∈ P, (1 + weight p / p)) ≤ Real.exp (Real.pi^2) := by
  have h (p : ℕ) : weight p / p = 6 * (1/(p:ℝ)^2) := by
    dsimp [weight]
    ring
  calc
    _ ≤ ∏ p ∈ P, Real.exp (weight p / p) := prod_le_prod₀
      (fun p _ => by dsimp [weight]; positivity)
      (fun p _ => by linarith [Real.add_one_le_exp (weight p / p)])
    _ = Real.exp (∑ p ∈ P, weight p / p) := (Real.exp_sum ..).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      simp_rw [h]
      rw [← mul_sum]
      have hz := hasSum_zeta_two.summable.sum_le_tsum P (fun p _ => by positivity)
      rw [hasSum_zeta_two.tsum_eq] at hz
      linarith

theorem budget (X : ℕ) :
    (∑ n ∈ Icc 1 X, (n:ℝ) / (n.totient:ℝ)^2) ≤ Real.exp (Real.pi^2) * (1+Real.log X) := by
  classical
  let A := Icc 1 X
  let P := A.filter Nat.Prime
  let v (s : Finset ℕ) := ∏ p ∈ s, weight p
  let harm := ∑ n ∈ A, (n:ℝ)⁻¹
  have hP {n : ℕ} (hn : n ∈ A) : n.primeFactors ⊆ P := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hpr.pos,
      (Nat.le_of_dvd (mem_Icc.mp hn).1 (Nat.dvd_of_mem_primeFactors hp)).trans (mem_Icc.mp hn).2⟩,hpr⟩
  have term (n : ℕ) (hn : n ∈ A) :
      (n:ℝ)/(n.totient:ℝ)^2 ≤ ∑ s ∈ P.powerset,
        if denom s ∣ n then v s * (n:ℝ)⁻¹ else 0 := by
    apply (point (mem_Icc.mp hn).1).trans
    rw [sum_div]
    change (∑ s ∈ n.primeFactors.powerset, v s / n) ≤ _
    rw [← sum_filter]
    apply le_trans (le_of_eq (sum_congr rfl (fun s _ => div_eq_mul_inv ..)))
    apply sum_le_sum_of_subset_of_nonneg
    · intro s hs
      have hsub := mem_powerset.mp hs
      exact mem_filter.mpr ⟨mem_powerset.mpr (hsub.trans (hP hn)),
        (prod_dvd_prod_of_subset s n.primeFactors id hsub).trans (Nat.prod_primeFactors_dvd n)⟩
    · intro s _ _
      dsimp [v,weight]
      positivity
  have row (s : Finset ℕ) (hs : s ∈ P.powerset) :
      (∑ n ∈ A, if denom s ∣ n then v s * (n:ℝ)⁻¹ else 0) ≤
        (∏ p ∈ s, weight p / p) * harm := by
    have hpos : 0 < denom s := prod_pos fun p hp =>
      (mem_filter.mp (mem_powerset.mp hs hp)).2.pos
    rw [← sum_filter, ← mul_sum, prod_div_distrib]
    have hc : ((denom s : ℕ):ℝ) = ∏ p ∈ s, (p:ℝ) := by simp [denom]
    rw [← hc]
    have h := mul_le_mul_of_nonneg_left (multiples X (denom s) hpos)
      (show 0 ≤ v s by dsimp [v, weight]; positivity)
    convert h using 1
    dsimp [A,harm,v]
    ring
  have hp0 : 0 ≤ harm := sum_nonneg fun n _ => by positivity
  have hh : harm ≤ 1+Real.log X := by
    simpa only [harm,A,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
      using harmonic_le_one_add_log X
  calc
    _ ≤ _ := sum_le_sum term
    _ = _ := sum_comm
    _ ≤ _ := sum_le_sum row
    _ = (∏ p ∈ P, (1+weight p / p))*harm := by rw [prod_one_add, sum_mul]
    _ ≤ _ := mul_le_mul (factor_budget P) hh hp0 (Real.exp_pos _).le

end
end Conjectures.Goldbach.PacketTotientHarmonicBudget_aux

/-- A logarithmic budget for summing per-denominator resonance bounds. -/
theorem Conjectures.Goldbach.PacketTotientHarmonicBudget :
    ∀ X : ℕ, (∑ q ∈ Finset.Icc 1 X, (q : ℝ) / (q.totient : ℝ)^2)
      ≤ Real.exp (Real.pi^2) * (1 + Real.log (X : ℝ)) :=
  Conjectures.Goldbach.PacketTotientHarmonicBudget_aux.budget
