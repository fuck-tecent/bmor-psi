import Mathlib

theorem PEqualNP.Outside.L_twin_primes_no_wrap :
    ∀ (N X : ℕ) [NeZero N] (f : ℕ → ℝ), X+2 < N → (∀ n, X < n → f n=0) → (∑ j : ZMod N, f j.val * f (j+2).val) = (Finset.range (X+1)).sum (fun n => f n*f (n+2)) := by
  intro N X _ f hN hf
  have h2 : ((2 : ZMod N)).val = 2 := ZMod.val_ofNat_of_lt (show 2 < N by omega)
  have hR : (Finset.range (X+1)).sum (fun n => f n*f (n+2))
      = (Finset.range N).sum (fun n => f n*f (n+2)) := by
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_range] at hn ⊢
      omega
    · intro n _ hn
      simp only [Finset.mem_range, not_lt] at hn
      rw [hf n (by omega), zero_mul]
  rw [hR]
  refine Finset.sum_bij' (fun j _ => j.val) (fun n _ => (n : ZMod N)) ?_ ?_ ?_ ?_ ?_
  · intro j _
    exact Finset.mem_range.mpr (ZMod.val_lt j)
  · intro n _
    exact Finset.mem_univ _
  · intro j _
    exact ZMod.natCast_zmod_val j
  · intro n hn
    exact ZMod.val_cast_of_lt (Finset.mem_range.mp hn)
  · intro j _
    by_cases hj : X < j.val
    · rw [hf _ hj, zero_mul, zero_mul]
    · have : (j+2).val = j.val + 2 := by
        rw [ZMod.val_add, h2, Nat.mod_eq_of_lt]
        omega
      rw [this]
