import Mathlib

theorem PEqualNP.Outside.L_goldbach_pp_count_squares :
    ∀ n : ℕ, ((Finset.range (n+1)).filter (fun m => (Nat.sqrt m).Prime ∧ (Nat.sqrt m)^2=m)).card ≤ Nat.sqrt n := by
  intro n
  calc
    _ ≤ (Finset.Icc 1 (Nat.sqrt n)).card := by
      apply Finset.card_le_card_of_injOn Nat.sqrt
      · intro m hm
        obtain ⟨hrange, hprime, _⟩ := Finset.mem_filter.mp hm
        have hmn : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hrange)
        exact Finset.mem_Icc.mpr ⟨hprime.one_lt.le, Nat.sqrt_le_sqrt hmn⟩
      · intro x hx y hy hxy
        obtain ⟨_, _, hx_square⟩ := Finset.mem_filter.mp hx
        obtain ⟨_, _, hy_square⟩ := Finset.mem_filter.mp hy
        exact hx_square.symm.trans ((congrArg (fun z : ℕ => z ^ 2) hxy).trans hy_square)
    _ = Nat.sqrt n := by simp
