import Mathlib

theorem PEqualNP.Outside.L_goldbach_exceptional_prime_jacobi :
    ∀ (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p), χ ≠ 1 → χ^2 = 1 → ∀ t : ZMod p, t ≠ 0 →
      (∑ a : ZMod p, χ a * χ (t - a)) = -χ (-1) := by
  intro p _ χ hχne hsq t ht
  have hmul : χ * χ = 1 := by
    ext x
    have h := DFunLike.congr_fun hsq (x : ZMod p)
    simpa [pow_two, MonoidHom.mul_apply, MulChar.one_apply] using h
  have hinv : χ⁻¹ = χ := inv_eq_of_mul_eq_one_right hmul
  have ht2 : χ t * χ t = 1 := by
    have h := DFunLike.congr_fun hmul t
    have honet : (1 : DirichletCharacter ℂ p) t = 1 :=
      MulChar.one_apply (isUnit_iff_ne_zero.mpr ht)
    simpa [MonoidHom.mul_apply, honet] using h
  have hJ : jacobiSum χ χ = -χ (-1) := by
    have h := jacobiSum_nontrivial_inv (F := ZMod p) (R := ℂ) (hχ := hχne)
    rwa [hinv] at h
  have hsum : (∑ a : ZMod p, χ a * χ (t - a)) = jacobiSum χ χ := by
    rw [jacobiSum]
    rw [← Equiv.sum_comp (Equiv.mulLeft₀ t ht) (fun a => χ a * χ (t - a))]
    apply Finset.sum_congr rfl
    intro u _
    change χ (t * u) * χ (t - t * u) = χ u * χ (1 - u)
    have harg : t - t * u = t * (1 - u) := by ring
    rw [harg]
    simp only [map_mul]
    calc (χ t * χ u) * (χ t * χ (1 - u))
        = (χ t * χ t) * (χ u * χ (1 - u)) := by ring
      _ = χ u * χ (1 - u) := by rw [ht2]; ring
  rw [hsum, hJ]