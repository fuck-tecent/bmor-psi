import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_central_window_reflection :
    ∀ n k : ℕ, k≤n → ((n≤3*k ∧ 3*k≤2*n) ↔ (n≤3*(n-k) ∧ 3*(n-k)≤2*n)) := by
  intro n k hk
  omega
