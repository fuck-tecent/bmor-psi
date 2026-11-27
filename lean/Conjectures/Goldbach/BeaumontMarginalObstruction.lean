import Mathlib.Data.ZMod.Basic

/-- Beaumont geometric tools: two marginal-uniform clocks can avoid the diagonal forever.

Same speed with a unit offset keeps both marginals uniform while the joint orbit misses the
diagonal, so marginal uniformity alone cannot force a collision. -/
theorem Conjectures.Goldbach.BeaumontMarginalObstruction :
    ∀ m : ℕ, 2 ≤ m → ∃ a b : Fin m → ZMod m, Function.Bijective a ∧ Function.Bijective b ∧ ∀ t, a t ≠ b t := by
  intro m hm
  have h2 : (1 : ℕ) < m := Nat.lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hm
  have hm0 : 0 < m := Nat.lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hm
  haveI : NeZero m := ⟨hm0.ne'⟩
  let a : Fin m → ZMod m := fun t => (t.val : ZMod m)
  let b : Fin m → ZMod m := fun t => (t.val : ZMod m) + 1
  have ha_inj : Function.Injective a := by
    intro t u h
    have hmod : t.val % m = u.val % m := (ZMod.natCast_eq_natCast_iff' t.val u.val m).mp h
    rw [Nat.mod_eq_of_lt t.isLt, Nat.mod_eq_of_lt u.isLt] at hmod
    exact Fin.ext hmod
  have ha_surj : Function.Surjective a := by
    intro z
    exact ⟨⟨z.val, ZMod.val_lt z⟩, ZMod.natCast_zmod_val z⟩
  have hone : (1 : ZMod m) ≠ 0 := by
    intro h
    have hv : (1 : ZMod m).val = 0 := (ZMod.val_eq_zero (1 : ZMod m)).mpr h
    rw [ZMod.val_one'' h2.ne'] at hv
    exact Nat.one_ne_zero hv
  have hb_inj : Function.Injective b := by
    intro t u h
    exact ha_inj (add_right_cancel h)
  have hb_surj : Function.Surjective b := by
    intro z
    obtain ⟨t, ht⟩ := ha_surj (z - 1)
    exact ⟨t, by show a t + 1 = z; rw [ht]; exact sub_add_cancel z 1⟩
  refine ⟨a, b, ⟨ha_inj, ha_surj⟩, ⟨hb_inj, hb_surj⟩, ?_⟩
  intro t h
  have hh : a t + 1 = a t + 0 := by
    rw [add_zero]
    exact h.symm
  exact hone (add_left_cancel hh)
