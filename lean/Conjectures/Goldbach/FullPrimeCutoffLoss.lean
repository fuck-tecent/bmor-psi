import Mathlib

namespace Conjectures.Goldbach.FullPrimeCutoffLoss_aux

theorem reflect_cross (b low : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), b k * low (n - k)) = ∑ k ∈ Finset.range (n + 1), low k * b (n - k) := by
  have h := Finset.sum_range_reflect (fun j : ℕ => low (n - j) * b j) (n + 1)
  simp only [Nat.add_sub_cancel] at h
  have h' : (∑ j ∈ Finset.range (n + 1), low j * b (n - j))
      = ∑ j ∈ Finset.range (n + 1), low (n - j) * b j := by
    rw [← h]
    exact Finset.sum_congr rfl fun j hj => by
      rw [Nat.sub_sub_self (by simp only [Finset.mem_range] at hj; omega)]
  calc (∑ k ∈ Finset.range (n + 1), b k * low (n - k))
      = ∑ k ∈ Finset.range (n + 1), low (n - k) * b k :=
        Finset.sum_congr rfl fun k _ => mul_comm _ _
    _ = ∑ k ∈ Finset.range (n + 1), low k * b (n - k) := h'.symm

theorem loss_identity (a : ℕ → ℝ) (n m : ℕ) (h : 2 * m < n) :
    (∑ k ∈ Finset.range (n + 1), a k * a (n - k))
        - (∑ k ∈ Finset.range (n + 1),
            (if k ≤ m then 0 else a k) * (if n - k ≤ m then 0 else a (n - k)))
      = 2 * (∑ k ∈ Finset.range (m + 1), a k * a (n - k)) := by
  set b : ℕ → ℝ := fun k => if k ≤ m then 0 else a k with hb
  set low : ℕ → ℝ := fun k => if k ≤ m then a k else 0 with hlow
  have hsplit : ∀ k : ℕ, a k = b k + low k := by
    intro k
    simp only [hb, hlow]
    split_ifs <;> ring
  have hcross : (∑ k ∈ Finset.range (n + 1), b k * low (n - k))
      = ∑ k ∈ Finset.range (n + 1), low k * b (n - k) := reflect_cross b low n
  have hzero : ∀ k ∈ Finset.range (n + 1), low k * low (n - k) = 0 := by
    intro k hk
    have hkn : k ≤ n := by simp only [Finset.mem_range] at hk; omega
    simp only [hlow]
    by_cases h1 : k ≤ m
    · by_cases h2 : n - k ≤ m
      · exfalso
        omega
      · simp [h1, h2]
    · simp [h1]
  have hlowb : (∑ k ∈ Finset.range (n + 1), low k * b (n - k))
      = ∑ k ∈ Finset.range (m + 1), a k * a (n - k) := by
    have hpt2 : ∀ k ∈ Finset.range (n + 1),
        low k * b (n - k) = if k ≤ m then a k * a (n - k) else 0 := by
      intro k hk
      have hkn : k ≤ n := by simp only [Finset.mem_range] at hk; omega
      simp only [hlow, hb]
      by_cases h1 : k ≤ m
      · have h2 : ¬ (n - k ≤ m) := by omega
        simp [h1, h2]
      · simp [h1]
    have h3 : (∑ k ∈ Finset.range (n + 1), low k * b (n - k))
        = ∑ k ∈ Finset.range (n + 1), (if k ≤ m then a k * a (n - k) else 0) :=
      Finset.sum_congr rfl hpt2
    have hsub : Finset.range (m + 1) ⊆ Finset.range (n + 1) := by
      intro x hx
      have hx' : x < m + 1 := Finset.mem_range.mp hx
      exact Finset.mem_range.mpr (by omega)
    have h4 : (∑ k ∈ Finset.range (n + 1), (if k ≤ m then a k * a (n - k) else 0))
        = ∑ k ∈ Finset.range (m + 1), (if k ≤ m then a k * a (n - k) else 0) := by
      refine (Finset.sum_subset hsub ?_).symm
      intro x hx hx'
      simp only [Finset.mem_range] at hx hx'
      have hxm : ¬ (x ≤ m) := by omega
      simp [hxm]
    have h5 : (∑ k ∈ Finset.range (m + 1), (if k ≤ m then a k * a (n - k) else 0))
        = ∑ k ∈ Finset.range (m + 1), a k * a (n - k) :=
      Finset.sum_congr rfl (fun k hk => by
        simp only [Finset.mem_range] at hk
        simp [show k ≤ m by omega])
    rw [h3, h4, h5]
  have hpt : ∀ k ∈ Finset.range (n + 1),
      a k * a (n - k) - b k * b (n - k)
        = b k * low (n - k) + low k * b (n - k) + low k * low (n - k) := by
    intro k _
    rw [hsplit k, hsplit (n - k)]
    ring
  have h1 : (∑ k ∈ Finset.range (n + 1), a k * a (n - k))
      - (∑ k ∈ Finset.range (n + 1), b k * b (n - k))
      = ∑ k ∈ Finset.range (n + 1),
          (b k * low (n - k) + low k * b (n - k) + low k * low (n - k)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl hpt
  have hmain : (∑ k ∈ Finset.range (n + 1), a k * a (n - k))
      - (∑ k ∈ Finset.range (n + 1), b k * b (n - k))
      = 2 * (∑ k ∈ Finset.range (m + 1), a k * a (n - k)) := by
    rw [h1, Finset.sum_add_distrib, Finset.sum_add_distrib, hcross,
      Finset.sum_eq_zero hzero, hlowb]
    ring
  simpa only [hb] using hmain

theorem sum_weight_le (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), (if Nat.Prime k then Real.log (k : ℝ) else 0))
      ≤ Real.log 4 * (m : ℝ) := by
  have hexpand : Chebyshev.theta (m : ℝ)
      = ∑ p ∈ Finset.Ioc 0 m, (if Nat.Prime p then Real.log (p : ℝ) else 0) := by
    simp [Chebyshev.theta, Finset.sum_filter]
  have hkey : (∑ k ∈ Finset.range (m + 1), (if Nat.Prime k then Real.log (k : ℝ) else 0))
      = Chebyshev.theta (m : ℝ) := by
    rw [hexpand]
    refine (Finset.sum_subset (s₁ := Finset.Ioc 0 m) (s₂ := Finset.range (m + 1)) ?_ ?_).symm
    · intro k hk
      simp only [Finset.mem_Ioc] at hk
      simp only [Finset.mem_range]
      omega
    · intro k hk hk'
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_Ioc] at hk'
      have hk0 : k = 0 := by omega
      subst hk0
      simp
  rw [hkey]
  exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg m)

theorem cutoff_loss_bound (w : ℕ → ℝ) (hw0 : ∀ k : ℕ, 0 ≤ w k)
    (hwle : ∀ k n : ℕ, k ≤ n → w k ≤ Real.log (n : ℝ))
    (hsum : ∀ m : ℕ, (∑ k ∈ Finset.range (m + 1), w k) ≤ Real.log 4 * (m : ℝ))
    (n m : ℕ) (h : 2 * m < n) :
    0 ≤ 2 * (∑ k ∈ Finset.range (m + 1), w k * w (n - k))
      ∧ 2 * (∑ k ∈ Finset.range (m + 1), w k * w (n - k))
        ≤ 2 * Real.log 4 * (m : ℝ) * Real.log (n : ℝ) := by
  have hS0 : 0 ≤ ∑ k ∈ Finset.range (m + 1), w k * w (n - k) :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (hw0 k) (hw0 (n - k)))
  have hSle : (∑ k ∈ Finset.range (m + 1), w k * w (n - k))
      ≤ Real.log 4 * (m : ℝ) * Real.log (n : ℝ) := by
    calc (∑ k ∈ Finset.range (m + 1), w k * w (n - k))
        ≤ ∑ k ∈ Finset.range (m + 1), w k * Real.log (n : ℝ) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' : k ≤ n := by simp only [Finset.mem_range] at hk; omega
          exact mul_le_mul_of_nonneg_left (hwle (n - k) n (Nat.sub_le n k)) (hw0 k)
      _ = Real.log (n : ℝ) * (∑ k ∈ Finset.range (m + 1), w k) := by
          rw [← Finset.sum_mul]
          ring
      _ ≤ Real.log (n : ℝ) * (Real.log 4 * (m : ℝ)) :=
          mul_le_mul_of_nonneg_left (hsum m) (Real.log_natCast_nonneg n)
      _ = Real.log 4 * (m : ℝ) * Real.log (n : ℝ) := by ring
  constructor
  · linarith
  · nlinarith [hSle]

theorem main_bound (w : ℕ → ℝ) (hw0 : ∀ k : ℕ, 0 ≤ w k)
    (hwle : ∀ k n : ℕ, k ≤ n → w k ≤ Real.log (n : ℝ))
    (hsum : ∀ m : ℕ, (∑ k ∈ Finset.range (m + 1), w k) ≤ Real.log 4 * (m : ℝ))
    (n m : ℕ) (h : 2 * m < n) :
    (∑ k ∈ Finset.range (n + 1), w k * w (n - k))
        - (∑ k ∈ Finset.range (n + 1),
            (if k ≤ m then 0 else w k) * (if n - k ≤ m then 0 else w (n - k)))
      = 2 * Finset.sum (Finset.range (m + 1)) (fun k => w k * w (n - k))
    ∧ 0 ≤ (∑ k ∈ Finset.range (n + 1), w k * w (n - k))
        - (∑ k ∈ Finset.range (n + 1),
            (if k ≤ m then 0 else w k) * (if n - k ≤ m then 0 else w (n - k)))
    ∧ (∑ k ∈ Finset.range (n + 1), w k * w (n - k))
        - (∑ k ∈ Finset.range (n + 1),
            (if k ≤ m then 0 else w k) * (if n - k ≤ m then 0 else w (n - k)))
      ≤ 2 * Real.log 4 * (m : ℝ) * Real.log (n : ℝ) := by
  have hid := loss_identity w n m h
  obtain ⟨hb0, hb1⟩ := cutoff_loss_bound w hw0 hwle hsum n m h
  rw [hid]
  exact ⟨rfl, hb0, hb1⟩

end Conjectures.Goldbach.FullPrimeCutoffLoss_aux

theorem Conjectures.Goldbach.FullPrimeCutoffLoss : let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0; let high := fun m k : ℕ => if k ≤ m then 0 else w k; let R := fun (a : ℕ → ℝ) (n : ℕ) => Finset.sum (Finset.range (n + 1)) (fun k => a k * a (n - k)); ∀ n m : ℕ, 2 * m < n → R w n - R (high m) n = 2 * Finset.sum (Finset.range (m + 1)) (fun k => w k * w (n - k)) ∧ 0 ≤ R w n - R (high m) n ∧ R w n - R (high m) n ≤ 2 * Real.log 4 * (m : ℝ) * Real.log (n : ℝ) := by
  dsimp only
  intro n m h
  exact Conjectures.Goldbach.FullPrimeCutoffLoss_aux.main_bound
    (fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0)
    (fun k => by
      show 0 ≤ (if Nat.Prime k then Real.log (k : ℝ) else 0)
      split_ifs
      · exact Real.log_natCast_nonneg k
      · exact le_refl 0)
    (fun k n hkn => by
      show (if Nat.Prime k then Real.log (k : ℝ) else 0) ≤ Real.log (n : ℝ)
      split_ifs with hk
      · exact Real.log_le_log (by exact_mod_cast Nat.Prime.pos hk) (by exact_mod_cast hkn)
      · exact Real.log_natCast_nonneg n)
    (fun m => Conjectures.Goldbach.FullPrimeCutoffLoss_aux.sum_weight_le m) n m h
