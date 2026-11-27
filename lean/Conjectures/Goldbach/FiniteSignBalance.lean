import Mathlib

theorem Conjectures.Goldbach.FiniteSignBalance :
∀ (n m : ℕ) (b : ℕ → Fin m → ℝ), ∃ s : ℕ → ℝ, (∀ k, s k = 1 ∨ s k = -1) ∧ (∑ j, (∑ k ∈ Finset.range n, s k * b k j)^2) ≤ ∑ j, ∑ k ∈ Finset.range n, (b k j)^2 := by
  intro n m b
  induction n with
  | zero =>
    refine ⟨fun _ => 1,fun _ => Or.inl rfl,?_⟩
    simp
  | succ n ih =>
    obtain ⟨s,hs,he⟩ := ih
    let u (j : Fin m) := ∑ k ∈ Finset.range n, s k*b k j
    let d := ∑ j, u j*b n j
    let t : ℝ := if 0 ≤ d then -1 else 1
    have ht : t = 1 ∨ t = -1 := by unfold t; split <;> simp
    have ht2 : t^2 = 1 := by rcases ht with h|h <;> rw [h] <;> norm_num
    have htd : t*d ≤ 0 := by dsimp [t]; split <;> rename_i h <;> simp <;> linarith
    let v (k : ℕ) := if k=n then t else s k
    refine ⟨v,fun k => by by_cases h : k=n <;> simp only [v,h,if_true,if_false]; exact ht; exact hs k,?_⟩
    have hv (j : Fin m) : (∑ k ∈ Finset.range (n+1), v k*b k j) = u j+t*b n j := by
      rw [Finset.sum_range_succ]; simp only [v,if_true]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      simp [(Finset.mem_range.mp hk).ne]
    simp_rw [hv]
    have expansion (j : Fin m) : (u j+t*b n j)^2 = (u j)^2+(b n j)^2+2*t*(u j*b n j) := by
      nlinarith only [show t^2*(b n j)^2 = (b n j)^2 by rw [ht2,one_mul]]
    simp_rw [expansion,Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_range_succ,Finset.sum_add_distrib]
    change (∑ j,(u j)^2)+(∑ j,(b n j)^2)+2*t*d ≤ _
    change (∑ j,(u j)^2) ≤ _ at he
    linarith
