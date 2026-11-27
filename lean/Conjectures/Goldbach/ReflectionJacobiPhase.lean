import Mathlib

open scoped BigOperators

/-- PREPUB gap `L-goldbach-reflection-jacobi-phase` (reflection theme). -/
theorem Conjectures.Goldbach.ReflectionJacobiPhase :
    ∀ (p : ℕ) [Fact p.Prime] (t : ZMod p) (χ ψ : DirichletCharacter ℂ p),
      (∑ x : (ZMod p)ˣ, star (χ (x : ZMod p)) * ψ (t - (x : ZMod p))) =
        if t = 0 then (if χ = ψ then (p.totient : ℂ) * ψ (-1) else 0)
        else star (χ t) * ψ t * jacobiSum χ⁻¹ ψ := by
  intro p hp t χ ψ
  have hstar : ∀ a : ZMod p, star (χ a) = χ⁻¹ a := fun a => MulChar.star_apply' χ a
  -- 单位上的和 ↔ 整个 `ZMod p` 上的和（非单位处取值为 0）
  have hbridge : ∀ (g : ZMod p → ℂ), (∀ a : ZMod p, ¬ IsUnit a → g a = 0) →
      (∑ x : (ZMod p)ˣ, g (x : ZMod p)) = ∑ a : ZMod p, g a := by
    intro g hg
    have hsubset : ((Finset.univ : Finset (ZMod p)ˣ).map
        ⟨((↑) : (ZMod p)ˣ → ZMod p), Units.val_injective⟩) ⊆ Finset.univ :=
      Finset.subset_univ _
    have hzero : ∀ a ∈ (Finset.univ : Finset (ZMod p)),
        a ∉ ((Finset.univ : Finset (ZMod p)ˣ).map
          ⟨((↑) : (ZMod p)ˣ → ZMod p), Units.val_injective⟩) → g a = 0 := by
      intro a _ ha
      apply hg
      intro hau
      exact ha (Finset.mem_map.mpr ⟨hau.unit, by simp [hau.unit_spec]⟩)
    have h1 := Finset.sum_subset hsubset hzero
    have h2 : (∑ a ∈ ((Finset.univ : Finset (ZMod p)ˣ).map
          ⟨((↑) : (ZMod p)ˣ → ZMod p), Units.val_injective⟩), g a)
        = ∑ x : (ZMod p)ˣ, g (x : ZMod p) := by
      rw [Finset.sum_map]
      simp
    rw [← h2, ← h1]
  -- 单位上非平凡特征的和为 0
  have hsum_units_zero : ∀ (ω : DirichletCharacter ℂ p), ω ≠ 1 →
      (∑ x : (ZMod p)ˣ, ω (x : ZMod p)) = 0 := by
    intro ω hω
    have hall : (∑ a : ZMod p, ω a) = 0 := MulChar.sum_eq_zero_of_ne_one hω
    rw [← hbridge (fun a => ω a) (fun a ha => MulChar.map_nonunit ω ha)] at hall
    exact hall
  by_cases ht : t = 0
  · -- t = 0：正交关系
    subst ht
    rw [if_pos rfl]
    by_cases hχψ : χ = ψ
    · -- χ = ψ：每项贡献 χ(-1)
      subst hχψ
      rw [if_pos rfl]
      have hxinv : ∀ x : (ZMod p)ˣ, χ⁻¹ (x : ZMod p) * χ (x : ZMod p) = 1 := by
        intro x
        rw [← MulChar.mul_apply, MulChar.inv_mul, MulChar.one_apply x.isUnit]
      have hterm : ∀ x : (ZMod p)ˣ, star (χ (x : ZMod p)) * χ (-(x : ZMod p)) = χ (-1) := by
        intro x
        have hmul : χ (-(x : ZMod p)) = χ (-1) * χ (x : ZMod p) := by
          rw [show (-(x : ZMod p)) = (-1 : ZMod p) * (x : ZMod p) by ring]
          exact map_mul χ (-1) (x : ZMod p)
        rw [hstar, hmul]
        calc χ⁻¹ (x : ZMod p) * (χ (-1) * χ (x : ZMod p))
            = χ (-1) * (χ⁻¹ (x : ZMod p) * χ (x : ZMod p)) := by ring
          _ = χ (-1) := by rw [hxinv x, mul_one]
      simp only [zero_sub]
      rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_const, Finset.card_univ,
        ZMod.card_units_eq_totient, nsmul_eq_mul]
    · -- χ ≠ ψ：正交消失
      rw [if_neg hχψ]
      have hω : χ⁻¹ * ψ ≠ 1 := by
        intro h
        apply hχψ
        have hcalc : ψ = χ := by
          calc ψ = 1 * ψ := (one_mul ψ).symm
            _ = (χ * χ⁻¹) * ψ := by rw [mul_inv_cancel]
            _ = χ * (χ⁻¹ * ψ) := by rw [mul_assoc]
            _ = χ * 1 := by rw [h]
            _ = χ := mul_one χ
        exact hcalc.symm
      have hterm : ∀ x : (ZMod p)ˣ, star (χ (x : ZMod p)) * ψ (-(x : ZMod p))
          = ψ (-1) * (χ⁻¹ * ψ) (x : ZMod p) := by
        intro x
        have hmul : ψ (-(x : ZMod p)) = ψ (-1) * ψ (x : ZMod p) := by
          rw [show (-(x : ZMod p)) = (-1 : ZMod p) * (x : ZMod p) by ring]
          exact map_mul ψ (-1) (x : ZMod p)
        rw [hstar, hmul, MulChar.mul_apply]
        ring
      simp only [zero_sub]
      rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.mul_sum,
        hsum_units_zero (χ⁻¹ * ψ) hω, mul_zero]
  · -- t ≠ 0：x = t·a 换元（在整个 `ZMod p` 上）
    rw [if_neg ht]
    have htunit : IsUnit t := isUnit_iff_ne_zero.mpr ht
    -- LHS = Σ_{a : ZMod p} χ⁻¹ a · ψ (t - a)
    have hL : (∑ x : (ZMod p)ˣ, star (χ (x : ZMod p)) * ψ (t - (x : ZMod p)))
        = ∑ a : ZMod p, χ⁻¹ a * ψ (t - a) := by
      rw [← hbridge (fun a => χ⁻¹ a * ψ (t - a))
        (fun a ha => by rw [MulChar.map_nonunit χ⁻¹ ha, zero_mul])]
      apply Finset.sum_congr rfl
      intro x _
      rw [hstar]
    rw [hL]
    -- 换元 a ↦ t·a
    have hsubst : (∑ a : ZMod p, χ⁻¹ a * ψ (t - a))
        = ∑ a : ZMod p, χ⁻¹ (t * a) * ψ (t - t * a) := by
      have := Equiv.sum_comp (Equiv.mulLeft₀ t ht) (fun a : ZMod p => χ⁻¹ a * ψ (t - a))
      simpa [Equiv.mulLeft₀_apply] using this.symm
    rw [hsubst]
    have hterm : ∀ a : ZMod p,
        χ⁻¹ (t * a) * ψ (t - t * a) = (χ⁻¹ t * ψ t) * (χ⁻¹ a * ψ (1 - a)) := by
      intro a
      have h1 : χ⁻¹ (t * a) = χ⁻¹ t * χ⁻¹ a := map_mul χ⁻¹ t a
      have h2 : t - t * a = t * (1 - a) := by ring
      rw [h1, h2, map_mul ψ t (1 - a)]
      ring
    rw [Finset.sum_congr rfl (fun a _ => hterm a), ← Finset.mul_sum]
    -- 与 jacobiSum 对接
    have hjac : jacobiSum χ⁻¹ ψ
        = ∑ a : ZMod p, χ⁻¹ a * ψ (1 - a) := rfl
    rw [← hjac, hstar t]

namespace Conjectures.Goldbach
end Conjectures.Goldbach
