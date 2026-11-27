import Mathlib

open Finset

namespace PEqualNP.Outside

theorem L_goldbach_cross_upper_triangle :
    ∀ (m : ℕ) (u : Fin m → ℂ), (∑ i, ∑ j ∈ Finset.univ.erase i, (u i*star (u j)).re) = 2*∑ i, ∑ j ∈ Finset.univ.filter (fun j => i<j), (u i*star (u j)).re := by
  intro m u
  classical
  have hsplit (i : Fin m) :
      (∑ j ∈ Finset.univ.erase i, (u i * star (u j)).re) =
        (∑ j ∈ Finset.univ.filter (fun j => i < j), (u i * star (u j)).re) +
          (∑ j ∈ Finset.univ.filter (fun j => j < i), (u i * star (u j)).re) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ.erase i) (p := fun j => i < j)]
    congr 1
    · congr 1
      ext j
      simp only [mem_filter, mem_erase, mem_univ, true_and, and_true]
      exact ⟨fun h => h.2, fun h => ⟨ne_of_gt h, h⟩⟩
    · congr 1
      ext j
      simp only [mem_filter, mem_erase, mem_univ, true_and, and_true]
      exact ⟨fun h => lt_of_le_of_ne (not_lt.mp h.2) h.1, fun h => ⟨ne_of_lt h, not_lt_of_gt h⟩⟩
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  have hswap :
      (∑ i : Fin m, ∑ j ∈ Finset.univ.filter (fun j => j < i), (u i * star (u j)).re) =
        ∑ i : Fin m, ∑ j ∈ Finset.univ.filter (fun j => i < j), (u i * star (u j)).re := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : i < j
    · simp [h, Complex.mul_re]
      ring
    · simp [h]
  rw [hswap, two_mul]

end PEqualNP.Outside
