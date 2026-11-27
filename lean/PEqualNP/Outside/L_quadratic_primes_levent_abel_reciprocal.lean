import Mathlib

namespace PEqualNP.Outside

theorem L_quadratic_primes_levent_abel_reciprocal :
    let cheb := fun x : ℕ => ∑ p ∈ (Finset.Icc 1 x).filter (fun p => p.Prime ∧ p % 4 = 1), Real.log (p : ℝ); ∀ x y : ℕ, 1 ≤ x → x < y → (∑ p ∈ (Finset.Ioc x y).filter (fun p => p.Prime ∧ p % 4 = 1), Real.log (p : ℝ)/p) = cheb y / y - cheb x / ((x : ℝ)+1) + ∑ n ∈ Finset.Ico (x+1) y, cheb n * (1/(n : ℝ)-1/((n : ℝ)+1)) := by
  intro cheb x y hx hxy
  have h_step : ∀ m : ℕ, cheb (m + 1) - cheb m =
      if (m + 1).Prime ∧ (m + 1) % 4 = 1 then Real.log ((m + 1 : ℕ) : ℝ) else 0 := by
    intro m
    dsimp only [cheb]
    have h_icc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext p
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have h_not_mem : m + 1 ∉ Finset.Icc 1 m := by simp
    rw [h_icc, Finset.filter_insert]
    split_ifs with hP
    · rw [Finset.sum_insert (fun h => h_not_mem (Finset.mem_filter.mp h).1)]
      ring
    · ring
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, y = x + 1 + d := ⟨y - (x + 1), by omega⟩
  induction d with
  | zero =>
    simp only [Finset.Ico_self, Finset.sum_empty, add_zero]
    have h_ioc : Finset.Ioc x (x + 1) = {x + 1} := by
      ext p
      simp only [Finset.mem_Ioc, Finset.mem_singleton]
      omega
    rw [h_ioc, Finset.filter_singleton]
    have hx1_ne : ((x : ℝ) + 1) ≠ 0 := by positivity
    have h_diff := h_step x
    split_ifs with hP
    · rw [Finset.sum_singleton]
      simp only [hP, and_self, ↓reduceIte] at h_diff
      push_cast at h_diff ⊢
      field_simp [hx1_ne]
      linarith
    · rw [Finset.sum_empty]
      simp only [hP, ↓reduceIte] at h_diff
      push_cast at h_diff ⊢
      field_simp [hx1_ne]
      linarith
  | succ d ih =>
    set m : ℕ := x + 1 + d
    have hxm : x < m := by omega
    have ih_m := ih hxm
    have h_add_assoc : x + 1 + (d + 1) = m + 1 := by omega
    rw [h_add_assoc]
    have h_ioc : Finset.Ioc x (m + 1) = insert (m + 1) (Finset.Ioc x m) := by
      ext p
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    have h_not_ioc : m + 1 ∉ Finset.Ioc x m := by simp
    have h_ico : Finset.Ico (x + 1) (m + 1) = insert m (Finset.Ico (x + 1) m) := by
      ext n
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have h_not_ico : m ∉ Finset.Ico (x + 1) m := by simp
    rw [h_ioc, Finset.filter_insert, h_ico, Finset.sum_insert h_not_ico]
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hm_ne : (m : ℝ) ≠ 0 := hm_pos.ne'
    have hm1_ne : ((m : ℝ) + 1) ≠ 0 := by positivity
    have h_diff := h_step m
    have h_alg : cheb (m + 1) / ((m + 1 : ℕ) : ℝ) - cheb x / ((x : ℝ) + 1) +
        (cheb m * (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)) +
          ∑ n ∈ Finset.Ico (x + 1) m, cheb n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) =
        (cheb m / (m : ℝ) - cheb x / ((x : ℝ) + 1) +
          ∑ n ∈ Finset.Ico (x + 1) m, cheb n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) +
        (cheb (m + 1) - cheb m) / ((m + 1 : ℕ) : ℝ) := by
      push_cast
      field_simp [hm_ne, hm1_ne]
      ring
    rw [h_alg, ← ih_m, h_diff]
    split_ifs with hP
    · rw [Finset.sum_insert (fun h => h_not_ioc (Finset.mem_filter.mp h).1)]
      ring
    · simp

end PEqualNP.Outside
