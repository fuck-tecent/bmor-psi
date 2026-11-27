import Mathlib

theorem Conjectures.Goldbach.BeaumontPerturbedClockGap :
    ∀ (n : ℕ) (s : ℤ) (x : ℝ), |x-(s:ℝ)| < 1/2 → |x-(n:ℝ)| ≤ 1/2 → s=(n:ℤ) := by
  intro n s x hs hn
  have htri : |(s:ℝ) - (n:ℝ)| < 1 := by
    calc |(s:ℝ) - (n:ℝ)| ≤ |(s:ℝ) - x| + |x - (n:ℝ)| := by
          rw [show (s:ℝ) - (n:ℝ) = ((s:ℝ) - x) + (x - (n:ℝ)) by ring]
          exact abs_add_le _ _
      _ < 1 := by rw [abs_sub_comm (s:ℝ) x]; linarith
  obtain ⟨hlo, hhi⟩ := abs_lt.mp htri
  have hlow : -(1:ℤ) < s - (n:ℤ) := by exact_mod_cast hlo
  have hupp : s - (n:ℤ) < 1 := by exact_mod_cast hhi
  omega
