import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_heavy_buckets :
    ∀ (n:ℕ) (b:Fin n→ℕ), ((Finset.univ:Finset (Fin n)).filter (fun i => 3≤b i)).card≤∑ i,Nat.choose (b i) 3 := by
  intro n b
  rw [Finset.card_filter]
  apply Finset.sum_le_sum
  intro i hi
  by_cases h : 3 ≤ b i
  · rw [ite_eq_left h]
    have hp := Nat.choose_pos h
    omega
  · rw [ite_eq_right h]
    exact Nat.zero_le _

