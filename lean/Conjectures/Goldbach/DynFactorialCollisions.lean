import Mathlib

theorem Conjectures.Goldbach.DynFactorialCollisions :
    let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime; let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card; let K := fun (X p q : ℕ) => ((E X).filter (fun n => p≤n ∧ q≤n ∧ Nat.Prime (n-p) ∧ Nat.Prime (n-q))).card; ∀ X : ℕ, (∑ n ∈ E X, H X n * (H X n - 1)) = ∑ p ∈ P X, ∑ q ∈ (P X).erase p, K X p q := by
  intro E P H K X
  simp only [H, K]
  have h1 : ∀ n, ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card *
      (((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card - 1)
      = ∑ p ∈ P X, ∑ q ∈ (P X).erase p,
        if (p ≤ n ∧ Nat.Prime (n-p)) ∧ (q ≤ n ∧ Nat.Prime (n-q)) then 1 else 0 := by
    intro n
    set S := (P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p)) with hS
    have : S.card * (S.card - 1) = ∑ p ∈ S, ((P X).erase p |>.filter
        (fun q => q ≤ n ∧ Nat.Prime (n-q))).card := by
      have h2 : ∑ p ∈ S, ((P X).erase p |>.filter
          (fun q => q ≤ n ∧ Nat.Prime (n-q))).card = ∑ p ∈ S, (S.card - 1) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [← Finset.card_erase_of_mem hp]
        congr 1
        ext q
        simp only [hS, Finset.mem_erase, Finset.mem_filter]
        tauto
      rw [h2, Finset.sum_const, smul_eq_mul]
    rw [this, hS, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs with h
    · rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro q _
      simp [h]
    · symm
      apply Finset.sum_eq_zero
      intro q _
      simp [h]
  rw [Finset.sum_congr rfl (fun n _ => h1 n), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases a : p ≤ n <;> by_cases b : q ≤ n <;> simp [a, b]
