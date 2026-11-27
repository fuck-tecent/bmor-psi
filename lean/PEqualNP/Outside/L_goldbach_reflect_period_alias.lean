import Mathlib

namespace PEqualNP.Outside

theorem L_goldbach_reflect_period_alias :
    ∀ (n : ℕ) (b : ℕ → ℝ), 0<n → (∑ k ∈ Finset.range (n+1), b k*b (n-k)) = (∑ k ∈ Finset.range n, b k*b ((n-k)%n)) + 2*b 0*b n-(b 0)^2 := by
  intro n b hn
  set S : ℝ := ∑ k ∈ Finset.range n, b k * b (n - k) with hS
  have hS2 : (∑ k ∈ Finset.range n, b k * b ((n - k) % n)) = S + b 0 * (b 0 - b n) := by
    have hpt : ∀ k ∈ Finset.range n,
        b k * b ((n - k) % n)
          = b k * b (n - k) + (if k = 0 then b 0 * (b 0 - b n) else 0) := by
      intro k hk
      by_cases hk0 : k = 0
      · subst hk0
        simp
        ring
      · have hklt : k < n := Finset.mem_range.mp hk
        have hlt : n - k < n := by omega
        rw [Nat.mod_eq_of_lt hlt]
        simp [hk0]
    calc
      (∑ k ∈ Finset.range n, b k * b ((n - k) % n))
          = ∑ k ∈ Finset.range n,
              (b k * b (n - k) + (if k = 0 then b 0 * (b 0 - b n) else 0)) :=
            Finset.sum_congr rfl hpt
      _ = (∑ k ∈ Finset.range n, b k * b (n - k))
            + ∑ k ∈ Finset.range n, (if k = 0 then b 0 * (b 0 - b n) else 0) :=
            Finset.sum_add_distrib
      _ = S + b 0 * (b 0 - b n) := by
            rw [hS]
            congr 1
            rw [Finset.sum_eq_single 0]
            · simp
            · intro k hk hk0
              simp [hk0]
            · intro h0
              exact absurd (Finset.mem_range.mpr hn) h0
  have hL : (∑ k ∈ Finset.range (n+1), b k * b (n - k)) = S + b n * b (n - n) := by
    rw [Finset.sum_range_succ, ← hS]
  rw [hL, hS2]
  simp only [Nat.sub_self]
  ring

end PEqualNP.Outside
