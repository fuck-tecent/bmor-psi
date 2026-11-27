import Mathlib

theorem PEqualNP.Outside.L_goldbach_residue_blocks_partial_period :
    ∀ (q X a : ℕ), a < q →
      ((Finset.range X).filter (fun k => k % q = a)).card ≤ X / q + 1 := by
  intro q X a _ha
  rw [← Finset.card_range (X / q + 1)]
  refine Finset.card_le_card_of_injOn (fun k : ℕ => k / q) ?_ ?_
  · intro k hk
    have hkX := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hkX.le))
  · intro k hk l hl heq
    have hkMod := (Finset.mem_filter.mp hk).2
    have hlMod := (Finset.mem_filter.mp hl).2
    change k / q = l / q at heq
    calc
      k = k % q + q * (k / q) := (Nat.mod_add_div k q).symm
      _ = l % q + q * (l / q) := by rw [hkMod, hlMod, heq]
      _ = l := Nat.mod_add_div l q
