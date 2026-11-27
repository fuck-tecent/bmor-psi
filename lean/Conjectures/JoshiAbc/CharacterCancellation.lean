import Mathlib

theorem Conjectures.JoshiAbc.CharacterCancellation : ∀ (p n : ℕ) [Fact p.Prime] (H : Submodule (ZMod p) (Fin n → ZMod p)) [Fintype H] (χ : (Fin n → ZMod p) → ℂ) (b : Fin n → ZMod p), (∀ x y, χ (x+y)=χ x*χ y) → (∃ h : H, χ h.val ≠ 1) → (∑ h : H, χ (b+h.val)) = 0 := by
  intro p n _ H _ χ b hχ h
  obtain ⟨h₀, hh₀⟩ := h
  refine eq_zero_of_mul_eq_self_left hh₀ ?_
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addLeft h₀) _ _ ?_
  intro h
  calc
    χ h₀.val * χ (b + h.val) = χ (h₀.val + (b + h.val)) := (hχ _ _).symm
    _ = χ (b + (h₀ + h).val) := by
      congr 1
      simp only [Submodule.coe_add]
      abel
