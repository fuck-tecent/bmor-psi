import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_weighted_endpoint_envelope :
    ∀ (ι : Type) [DecidableEq ι] (rows near : Finset ι) (f : ι → ℝ)
      (x C D α β γ : ℝ), 1 ≤ x → 0 ≤ C → 0 ≤ D → near ⊆ rows →
      (rows.card : ℝ) ≤ C * x ^ α → (near.card : ℝ) ≤ C * x ^ γ →
      (∀ i ∈ near, f i ≤ D * (Real.log x) ^ 2) →
      (∀ i ∈ rows \ near, f i ≤ D * x ^ (α / 2 - β) * (Real.log x) ^ 2) →
      (∑ i ∈ rows, f i) ≤ C * D * (x ^ γ + x ^ (3 * α / 2 - β)) * (Real.log x) ^ 2 := by
  intro ι _ rows near f x C D α β γ hx hC hD hsub hrows hnear hnearf hfar
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hL : 0 ≤ (Real.log x) ^ 2 := sq_nonneg _
  have hpowpos : 0 ≤ x ^ (α / 2 - β) := Real.rpow_nonneg hx0.le _
  have hnear_bound : ∑ i ∈ near, f i ≤ (near.card : ℝ) * (D * (Real.log x) ^ 2) := by
    calc
      ∑ i ∈ near, f i ≤ ∑ i ∈ near, (D * (Real.log x) ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hnearf i hi
      _ = (near.card : ℝ) * (D * (Real.log x) ^ 2) := by simp
  have hfar_bound : ∑ i ∈ rows \ near, f i ≤
      ((rows \ near).card : ℝ) * (D * x ^ (α / 2 - β) * (Real.log x) ^ 2) := by
    calc
      ∑ i ∈ rows \ near, f i ≤
          ∑ i ∈ rows \ near, (D * x ^ (α / 2 - β) * (Real.log x) ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hfar i hi
      _ = ((rows \ near).card : ℝ) * (D * x ^ (α / 2 - β) * (Real.log x) ^ 2) := by simp
  have hcard_sdiff : ((rows \ near).card : ℝ) ≤ (rows.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset)
  have hnear_mul : (near.card : ℝ) * (D * (Real.log x) ^ 2) ≤
      (C * x ^ γ) * (D * (Real.log x) ^ 2) := by
    exact mul_le_mul_of_nonneg_right hnear (mul_nonneg hD hL)
  have hfar_mul : ((rows \ near).card : ℝ) * (D * x ^ (α / 2 - β) * (Real.log x) ^ 2) ≤
      (C * x ^ α) * (D * x ^ (α / 2 - β) * (Real.log x) ^ 2) := by
    have hleft : ((rows \ near).card : ℝ) ≤ C * x ^ α := hcard_sdiff.trans hrows
    have hright : 0 ≤ D * x ^ (α / 2 - β) * (Real.log x) ^ 2 :=
      mul_nonneg (mul_nonneg hD hpowpos) hL
    exact mul_le_mul_of_nonneg_right hleft hright
  have hxpow : x ^ α * x ^ (α / 2 - β) = x ^ (3 * α / 2 - β) := by
    rw [← Real.rpow_add hx0]
    ring_nf
  calc
    ∑ i ∈ rows, f i = ∑ i ∈ near, f i + ∑ i ∈ rows \ near, f i := by
      rw [← Finset.sum_sdiff hsub]
      ring
    _ ≤ (near.card : ℝ) * (D * (Real.log x) ^ 2) +
        ((rows \ near).card : ℝ) * (D * x ^ (α / 2 - β) * (Real.log x) ^ 2) :=
      (add_le_add hnear_bound hfar_bound)
    _ ≤ (C * x ^ γ) * (D * (Real.log x) ^ 2) +
        (C * x ^ α) * (D * x ^ (α / 2 - β) * (Real.log x) ^ 2) :=
      (add_le_add hnear_mul hfar_mul)
    _ = C * D * (x ^ γ + x ^ (3 * α / 2 - β)) * (Real.log x) ^ 2 := by
      have h1 : C * x ^ α * (D * x ^ (α / 2 - β) * (Real.log x) ^ 2) =
          C * D * (x ^ α * x ^ (α / 2 - β)) * (Real.log x) ^ 2 := by ring
      rw [h1, hxpow]
      ring
