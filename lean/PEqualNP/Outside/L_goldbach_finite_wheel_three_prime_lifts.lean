import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.Finset.Card

theorem PEqualNP.Outside.L_goldbach_finite_wheel_three_prime_lifts :
    ∀ r ∈ ({17,19,23,181,29,37,41,43,31,47,53,67} : Finset ℕ), ∃ S : Finset ℕ, S.card=3 ∧ (∀ p ∈ S, Nat.Prime p ∧ p ≤ 210233 ∧ p % 30030=r) ∧ (∀ p ∈ S, ∀ q ∈ S, p ≠ q → p % 17 ≠ q % 17 ∧ p % 19 ≠ q % 19) := by
  intro r hr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨{17, 30047, 60077}, by decide, ?_, by decide⟩
    simp only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
    norm_num
  · refine ⟨{19, 150169, 210229}, by decide, ?_, by decide⟩
    simp only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
    norm_num
  · refine ⟨{23, 60083, 210233}, by decide, ?_, by decide⟩
    simp only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
    norm_num
  · refine ⟨{181, 30211, 90271}, by decide, ?_, by decide⟩
    simp only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
    norm_num
  · refine ⟨{29, 30059, 60089}, by decide, ?_, by decide⟩
    simp only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
    norm_num
  · refine ⟨{37, 90127, 120157}, by decide, ?_, by decide⟩
    simp only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
    norm_num
  · refine ⟨{41, 30071, 60101}, by decide, ?_, by decide⟩
    simp only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
    norm_num
  · refine ⟨{43, 60103, 120163}, by decide, ?_, by decide⟩
    simp only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
    norm_num
  · refine ⟨{31, 60091, 90121}, by decide, ?_, by decide⟩
    simp only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
    norm_num
  · refine ⟨{47, 60107, 120167}, by decide, ?_, by decide⟩
    simp only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
    norm_num
  · refine ⟨{53, 150203, 180233}, by decide, ?_, by decide⟩
    simp only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
    norm_num
  · refine ⟨{67, 30097, 60127}, by decide, ?_, by decide⟩
    simp only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
    norm_num
