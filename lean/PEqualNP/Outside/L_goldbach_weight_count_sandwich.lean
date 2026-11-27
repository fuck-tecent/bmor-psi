import Mathlib

/-- On a representation by two primes, each logarithmic weight lies
between the logarithms of two and of the target. -/
theorem PEqualNP.Outside.L_goldbach_weight_count_sandwich :
    ∀ n : ℕ, 2 ≤ n →
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0
    let reps := fun n : ℕ => (Finset.range (n + 1)).filter
      (fun p => Nat.Prime p ∧ Nat.Prime (n - p))
    let conv := fun (u v : ℕ → ℝ) (n : ℕ) =>
      Finset.sum (Finset.range (n + 1)) (fun k => u k * v (n - k))
    (reps n).card * (Real.log 2)^2 ≤ conv w w n ∧
      conv w w n ≤ (reps n).card * (Real.log (n : ℝ))^2 := by
  intro n hn w reps conv
  have restrict_sum : conv w w n = ∑ k ∈ reps n, w k * w (n-k) := by
    change (∑ k ∈ Finset.range (n+1), w k * w (n-k)) = _
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hout
    by_cases hp : k.Prime
    · have hq : ¬ (n-k).Prime := fun h => hout (Finset.mem_filter.mpr ⟨hk,hp,h⟩)
      simp [w, hq]
    · simp [w, hp]
  have log_bounds (p : ℕ) (hp : p.Prime) (hpn : p ≤ n) :
      Real.log 2 ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ Real.log (n : ℝ) :=
    ⟨Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le),
      Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hpn)⟩
  have h₂ : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hN : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have term_bounds (p : ℕ) (hp : p ∈ reps n) :
      (Real.log 2)^2 ≤ w p * w (n-p) ∧ w p * w (n-p) ≤ (Real.log (n : ℝ))^2 := by
    obtain ⟨hr, hleft, hright⟩ := Finset.mem_filter.mp hp
    have hpn : p ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
    obtain ⟨hl₁, hu₁⟩ := log_bounds p hleft hpn
    obtain ⟨hl₂, hu₂⟩ := log_bounds (n-p) hright (Nat.sub_le ..)
    simp only [w, ite_eq_left hleft, ite_eq_left hright, pow_two]
    exact ⟨mul_le_mul hl₁ hl₂ h₂ (h₂.trans hl₁),
           mul_le_mul hu₁ hu₂ (h₂.trans hl₂) hN⟩
  rw [restrict_sum]
  constructor
  · simpa only [Finset.sum_const, nsmul_eq_mul] using
      (Finset.sum_le_sum fun p hp => (term_bounds p hp).1)
  · simpa only [Finset.sum_const, nsmul_eq_mul] using
      (Finset.sum_le_sum fun p hp => (term_bounds p hp).2)
