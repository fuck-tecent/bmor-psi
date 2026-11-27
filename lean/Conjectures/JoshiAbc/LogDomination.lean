import Mathlib

private theorem exponent_gap (j : ℕ) : j + 3 ≤ 3 ^ (j + 1) := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    change j + 4 ≤ 3 ^ (j + 1 + 1)
    rw [pow_succ]
    omega

theorem Conjectures.JoshiAbc.LogDomination :
    ∀ (p n : ℕ), p.Prime → 2 ≤ n →
      let c : ℕ := if p = 2 then 4 else p
      multiplicity p n < (n - 1) * multiplicity p c := by
  intro p n hp hn
  by_cases hp2 : p = 2
  · subst p
    have hfour : multiplicity 2 4 = 2 := by
      change multiplicity 2 (2 ^ 2) = 2
      exact multiplicity_base_pow (by decide) 2
    change multiplicity 2 n < (n - 1) * multiplicity 2 4
    rw [hfour]
    have h := Nat.multiplicity_lt_self (p := 2) (show n ≠ 0 by omega)
    omega
  · simp only [if_neg hp2, Nat.multiplicity_self hp.one_lt, mul_one]
    have hp3 : 3 ≤ p := by have ht := hp.two_le; omega
    have hpow : p ^ multiplicity p n ≤ n :=
      Nat.le_of_dvd (by omega) (pow_multiplicity_dvd p n)
    by_cases hm : multiplicity p n = 0
    · omega
    · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hm
      have hbound : j + 3 ≤ n := by
        refine (exponent_gap j).trans ((Nat.pow_le_pow_left hp3 (j + 1)).trans ?_)
        simpa only [hj] using hpow
      omega
