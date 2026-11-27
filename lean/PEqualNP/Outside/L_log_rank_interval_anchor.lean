import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.ZMod.Defs

open scoped Fin.NatCast Fin.CommRing in
theorem PEqualNP.Outside.L_log_rank_interval_anchor :
    ∀ k : ℕ, 2 ≤ k → let n := 3*k+1; let layer := (Finset.univ : Finset (Fin n)).powersetCard k; let shift := fun (S : Finset (Fin n)) (t : Fin n) => S.image (fun i => i+t); let orbit := fun (S : Finset (Fin n)) => (Finset.univ : Finset (Fin n)).image (shift S); let I := (Finset.univ : Finset (Fin n)).filter (fun i => i.val < k); let lin := fun (w : Fin n → ℝ) (B : Finset (Fin n)) => Finset.sum B w; let uniqueOn := fun (Y : Finset (Finset (Fin n))) => ∀ (w : Fin n → ℝ) (c : ℝ), (∀ B ∈ Y, lin w B = c) → ∀ B ∈ layer, lin w B = c; uniqueOn (orbit I) := by
  classical
  intro k hk
  let n := 3 * k + 1
  have : NeZero n := ⟨by dsimp [n]; omega⟩
  let I := (Finset.univ : Finset (Fin n)).filter (fun i => i.val < k)
  let window (t : Fin n) := I.image (fun i => i + t)
  dsimp only
  intro w c horbit B hB
  have hsize : B.card = k := (Finset.mem_powersetCard.mp hB).2
  have windowSum (t : Fin n) : (∑ j ∈ Finset.range k, w ((j : Fin n) + t)) = c := by
    have h := horbit (window t) (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩)
    refine Eq.trans ?_ h
    refine Finset.sum_bij (fun j _ => (j : Fin n) + t) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro j hj
      have hlt := Finset.mem_range.mp hj
      have hjn : j < n := by dsimp [n]; omega
      apply Finset.mem_image.mpr
      exact ⟨(j : Fin n), Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa only [Fin.val_natCast, Nat.mod_eq_of_lt hjn] using hlt⟩, rfl⟩
    · intro i hi j hj heq
      have hi' := Finset.mem_range.mp hi
      have hj' := Finset.mem_range.mp hj
      have hin : i < n := by dsimp [n]; omega
      have hjn : j < n := by dsimp [n]; omega
      simpa only [Fin.val_natCast, Nat.mod_eq_of_lt hin, Nat.mod_eq_of_lt hjn]
        using congrArg Fin.val (add_right_cancel heq)
    · intro b hb
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
      exact ⟨i.val, Finset.mem_range.mpr (Finset.mem_filter.mp hi).2, by simp⟩
  -- Expand a window of length k+1 from each end.
  have step (t : Fin n) : w (t + k) = w t := by
    let f (j : ℕ) := w ((j : Fin n) + t)
    have sliding := (Finset.sum_range_succ f k).symm.trans (Finset.sum_range_succ' f k)
    have first : (∑ j ∈ Finset.range k, f j) = c := windowSum t
    have next : (∑ j ∈ Finset.range k, f (j + 1)) = c := by
      simpa only [f, Nat.cast_add, Nat.cast_one, add_assoc, add_comm (1 : Fin n) t]
        using windowSum (t + 1)
    rw [first, next] at sliding
    simpa [f, add_comm] using add_left_cancel sliding
  -- In Z/(3k+1), three steps of size k undo one step of size one.
  have wrap : (1 : Fin n) + k + k + k = 0 := by
    have h : 1 + k + k + k = n := by dsimp [n]; omega
    calc
      _ = ((1 + k + k + k : ℕ) : Fin n) := by push_cast; rfl
      _ = 0 := by rw [h]; apply Fin.ext; simp
  have unitStep (t : Fin n) : w (t + 1) = w t := by
    calc
      _ = w (t + 1 + k + k + k) :=
        ((step (t + 1 + k + k)).trans ((step (t + 1 + k)).trans (step (t + 1)))).symm
      _ = w t := by rw [add_assoc t, add_assoc t, add_assoc t, wrap, add_zero]
  have constantNat (j : ℕ) : w (j : Fin n) = w 0 := by
    induction j with
    | zero => simp
    | succ j ih => simpa only [Nat.cast_succ] using (unitStep (j : Fin n)).trans ih
  have constant (i : Fin n) : w i = w 0 := by simpa using constantNat i.val
  simpa only [constant, Finset.sum_const, Finset.card_range, hsize] using windowSum 0
