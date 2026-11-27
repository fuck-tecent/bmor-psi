import Mathlib

theorem PEqualNP.Outside.L_goldbach_ap_partition :
    let ap := fun (q a N : ℕ) (f : ℕ → ℝ) => Finset.sum ((Finset.range (N+1)).filter (fun k => k % q = a)) f;
    ∀ q N f, 0<q → Finset.sum (Finset.range q) (fun a => ap q a N f) = Finset.sum (Finset.range (N+1)) f := by
  dsimp only
  intro q N f hq
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_eq_single_of_mem (k % q) (Finset.mem_range.mpr (Nat.mod_lt k hq))]
  · simp
  · intro b hb hne
    simp [Ne.symm hne]
