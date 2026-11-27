import Mathlib

theorem Conjectures.JoshiAbc.FiniteAffineTransform :
    ∀ (G : Type) [AddCommGroup G] [Fintype G] (H : AddSubgroup G) [Fintype H]
      (b : G) (χ : AddChar G ℂ) [Decidable (∀ h : H, χ h.val = 1)],
      (∑ h : H, χ (b + h.val)) =
        if (∀ h : H, χ h.val = 1) then (Nat.card H : ℂ) * χ b else 0 := by
  intro G _ _ H _ b χ _
  classical
  split_ifs with htriv
  · simp_rw [AddChar.map_add_eq_mul, htriv, mul_one]
    rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, nsmul_eq_mul]
  · push_neg at htriv
    rcases htriv with ⟨h0, h0ne⟩
    have hmul :
        χ h0.val * (∑ h : H, χ (b + h.val)) =
          ∑ h : H, χ (b + h.val) := by
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.addRight h0)
        (fun h : H => χ h0.val * χ (b + h.val))
        (fun h : H => χ (b + h.val)) ?_
      intro h
      calc
        χ h0.val * χ (b + h.val) = χ (b + h.val) * χ h0.val := mul_comm _ _
        _ = χ ((b + h.val) + h0.val) :=
          (AddChar.map_add_eq_mul χ (b + h.val) h0.val).symm
        _ = χ (b + (h + h0).val) := by
          rw [AddSubgroup.coe_add]
          congr 1
          ac_rfl
    have hzero : (χ h0.val - 1) * (∑ h : H, χ (b + h.val)) = 0 := by
      calc
        (χ h0.val - 1) * (∑ h : H, χ (b + h.val)) =
            χ h0.val * (∑ h : H, χ (b + h.val)) -
              (∑ h : H, χ (b + h.val)) := by ring
        _ = 0 := by rw [hmul]; simp
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr h0ne)
