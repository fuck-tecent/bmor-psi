import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_characters_diagonal_correction :
    ∀ (n : ℕ) [NeZero n], 2<n → ∀ w : ℕ → ℝ, (∑ a : (ZMod n)ˣ, w (a : ZMod n).val * w ((-a : (ZMod n)ˣ) : ZMod n).val) = ∑ k ∈ (Finset.range n).filter (fun k => k.Coprime n), w k*w (n-k) := by
  intro n hn htwo w
  classical
  refine Finset.sum_bij (fun a _ => (a : ZMod n).val) ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (ZMod.val_lt _), ZMod.val_coe_unit_coprime a⟩
  · intro a _ b _ h
    apply Units.ext
    calc
      (a : ZMod n) = (((a : ZMod n).val : ℕ) : ZMod n) := (ZMod.natCast_zmod_val _).symm
      _ = (((b : ZMod n).val : ℕ) : ZMod n) := by rw [h]
      _ = (b : ZMod n) := ZMod.natCast_zmod_val _
  · intro k hk
    obtain ⟨hkr, hcop⟩ := Finset.mem_filter.mp hk
    refine ⟨ZMod.unitOfCoprime k hcop, Finset.mem_univ _, ?_⟩
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hkr)
  · intro a _
    have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
    have : NeZero (a : ZMod n) := ⟨Units.ne_zero a⟩
    rw [Units.val_neg, ZMod.val_neg_of_ne_zero]
