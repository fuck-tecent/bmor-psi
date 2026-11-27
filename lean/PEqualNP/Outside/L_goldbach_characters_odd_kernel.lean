import Mathlib

theorem PEqualNP.Outside.L_goldbach_characters_odd_kernel :
    ∀ (n : ℕ) [NeZero n], 2<n → let odd := (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1); ∀ a b : (ZMod n)ˣ, ((2:ℂ)/(n.totient:ℂ))* (∑ χ ∈ odd, χ ((↑a : ZMod n)⁻¹)*χ (↑b : ZMod n)) = (if a=b then 1 else 0) - (if (↑a : ZMod n) = -(↑b : ZMod n) then 1 else 0) := by
  classical
  intro n _ hn
  dsimp only
  intro a b
  have htot : (n.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < n)).ne'
  rw [div_mul_eq_mul_div, div_eq_iff htot, Finset.sum_filter, Finset.mul_sum]
  calc
    _ = ∑ χ : DirichletCharacter ℂ n,
        (χ (a.val⁻¹) * χ b.val - χ (a.val⁻¹) * χ (-b.val)) := by
      apply Finset.sum_congr rfl
      intro χ _
      rcases χ.even_or_odd with h | h
      · rw [ite_eq_right (show χ (-1) ≠ -1 from h.not_odd), h.eval_neg]
        ring
      · rw [ite_eq_left (show χ (-1) = -1 from h), h.eval_neg]
        ring
    _ = _ := by
      rw [Finset.sum_sub_distrib,
        DirichletCharacter.sum_char_inv_mul_char_eq ℂ a.isUnit b.val,
        DirichletCharacter.sum_char_inv_mul_char_eq ℂ a.isUnit (-b.val)]
      simp only [Units.val_inj]
      split_ifs <;> ring
