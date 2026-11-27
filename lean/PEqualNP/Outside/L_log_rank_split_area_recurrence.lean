import Mathlib

theorem PEqualNP.Outside.L_log_rank_split_area_recurrence :
    ∀ n r c s : ℕ, r ≤ s → s < n → c ≤ n-(s+1) → let F := fun t => Nat.choose t r * Nat.choose (n-t) c; (s+1-r)*(n-s)*F (s+1) = (s+1)*(n-s-c)*F s := by
  intro n r c s hrs hsn hc
  dsimp only
  have hns1 : n - (s + 1) = n - s - 1 := by omega
  rw [hns1]
  have hns : n - s - 1 + 1 = n - s := by omega
  have h1 : Nat.choose s r * (s + 1) = Nat.choose (s + 1) r * (s + 1 - r) :=
    Nat.choose_mul_succ_eq s r
  have h2 : Nat.choose (n - s - 1) c * (n - s) = Nat.choose (n - s) c * (n - s - c) := by
    have h := Nat.choose_mul_succ_eq (n - s - 1) c
    rwa [hns] at h
  calc
    (s + 1 - r) * (n - s) * (Nat.choose (s + 1) r * Nat.choose (n - s - 1) c)
        = (Nat.choose (s + 1) r * (s + 1 - r)) * (Nat.choose (n - s - 1) c * (n - s)) := by
          ring
    _ = (Nat.choose s r * (s + 1)) * (Nat.choose (n - s) c * (n - s - c)) := by
          rw [← h1, ← h2]
    _ = (s + 1) * (n - s - c) * (Nat.choose s r * Nat.choose (n - s) c) := by
          ring
