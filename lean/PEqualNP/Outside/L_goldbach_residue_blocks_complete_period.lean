import Mathlib

theorem PEqualNP.Outside.L_goldbach_residue_blocks_complete_period :
    ∀ (q m a : ℕ), a<q → ((Finset.range (m*q)).filter (fun k => k % q=a)).card=m := by
  intro q m a ha
  have hq : 0 < q := by omega
  conv_rhs => rw [← Finset.card_range m]
  apply Finset.card_bij (fun k _ => k/q)
  · intro k hk
    exact Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul hq).mpr
      (Finset.mem_range.mp (Finset.mem_filter.mp hk).1))
  · intro k hk l hl hdiv
    have hmod : k % q = l % q := (Finset.mem_filter.mp hk).2.trans (Finset.mem_filter.mp hl).2.symm
    calc
      k = k % q + q*(k/q) := (Nat.mod_add_div k q).symm
      _ = l % q + q*(l/q) := by rw [hdiv, hmod]
      _ = l := Nat.mod_add_div l q
  · intro j hj
    have hj' : j+1 ≤ m := Finset.mem_range.mp hj
    refine ⟨q*j+a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩, ?_⟩
    · calc
        q*j+a < q*j+q := Nat.add_lt_add_left ha _
        _ = (j+1)*q := by rw [Nat.succ_mul, Nat.mul_comm q j]
        _ ≤ m*q := Nat.mul_le_mul_right _ hj'
    · simp [Nat.add_mod, Nat.mod_eq_of_lt ha]
    · simp [Nat.mul_add_div hq, Nat.div_eq_of_lt ha]
