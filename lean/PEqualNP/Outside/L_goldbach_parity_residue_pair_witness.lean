import Mathlib

theorem PEqualNP.Outside.L_goldbach_parity_residue_pair_witness :
    let liouville := fun n : ℕ => (-1:ℤ)^n.primeFactorsList.length; Nat.Prime 97 ∧ Nat.Prime 103 ∧ Nat.Prime 67 ∧ Nat.Prime 7 ∧ Nat.Prime 19 ∧ 133 = 7*19 ∧ 97+103=200 ∧ 67+133=200 ∧ (∀ x ∈ ({97,103,67,133} : Finset ℕ), 200 ≤ 3*x ∧ 3*x ≤ 400) ∧ (∀ m : ℕ, m ∣ 30 → ∀ F : ℕ → ℕ → ℝ, F (97 % m) (103 % m)=F (67 % m) (133 % m)) ∧ liouville 97 * liouville 103 = 1 ∧ liouville 67 * liouville 133 = -1 := by
  dsimp only
  have hp97 : Nat.Prime 97 := by norm_num
  have hp103 : Nat.Prime 103 := by norm_num
  have hp67 : Nat.Prime 67 := by norm_num
  have hp7 : Nat.Prime 7 := by norm_num
  have hp19 : Nat.Prime 19 := by norm_num
  refine ⟨hp97, hp103, hp67, hp7, hp19, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> omega
  · intro m hm F
    rcases hm with ⟨k, hk⟩
    have h1 : 97 % m = 67 % m := by
      have : 97 = 67 + m * k := by omega
      rw [this, Nat.add_mul_mod_self_left]
    have h2 : 133 % m = 103 % m := by
      have : 133 = 103 + m * k := by omega
      rw [this, Nat.add_mul_mod_self_left]
    rw [h1, h2]
  · rw [Nat.primeFactorsList_prime hp97, Nat.primeFactorsList_prime hp103]
    norm_num
  · rw [Nat.primeFactorsList_prime hp67]
    have hperm : (133 : ℕ).primeFactorsList.Perm (7 :: (19 : ℕ).primeFactorsList) := by
      have h133 : (133 : ℕ) = 7 * 19 := by norm_num
      rw [h133, ← List.singleton_append, ← Nat.primeFactorsList_prime hp7]
      exact Nat.perm_primeFactorsList_mul (by norm_num) (by norm_num)
    rw [Nat.primeFactorsList_prime hp19] at hperm
    rw [hperm.length_eq]
    norm_num
