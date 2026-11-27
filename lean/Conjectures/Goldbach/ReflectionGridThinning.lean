import Mathlib

namespace Conjectures.Goldbach.ReflectionGridThinning_aux

theorem signBalance :
∀ (n m : ℕ) (b : ℕ → Fin m → ℝ), ∃ s : ℕ → ℝ, (∀ k, s k = 1 ∨ s k = -1) ∧
    (∑ j, (∑ k ∈ Finset.range n, s k * b k j)^2) ≤ ∑ j, ∑ k ∈ Finset.range n, (b k j)^2 := by
  intro n m b
  induction n with
  | zero =>
    refine ⟨fun _ => 1, fun _ => Or.inl rfl, ?_⟩
    simp
  | succ n ih =>
    obtain ⟨s, hs, he⟩ := ih
    let u (j : Fin m) := ∑ k ∈ Finset.range n, s k * b k j
    let d := ∑ j, u j * b n j
    let t : ℝ := if 0 ≤ d then -1 else 1
    have ht : t = 1 ∨ t = -1 := by unfold t; split <;> simp
    have ht2 : t^2 = 1 := by rcases ht with h | h <;> rw [h] <;> norm_num
    have htd : t * d ≤ 0 := by dsimp [t]; split <;> rename_i h <;> simp <;> linarith
    let v (k : ℕ) := if k = n then t else s k
    refine ⟨v, fun k => by by_cases h : k = n <;> simp only [v, h, ite_true, ite_false]; exact ht; exact hs k, ?_⟩
    have hv (j : Fin m) : (∑ k ∈ Finset.range (n+1), v k * b k j) = u j + t * b n j := by
      rw [Finset.sum_range_succ]; simp only [v, ite_true]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      simp [(Finset.mem_range.mp hk).ne]
    simp_rw [hv]
    have expansion (j : Fin m) :
        (u j + t * b n j)^2 = (u j)^2 + (b n j)^2 + 2 * t * (u j * b n j) := by
      nlinarith only [show t^2 * (b n j)^2 = (b n j)^2 by rw [ht2, one_mul]]
    simp_rw [expansion, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_succ,
      Finset.sum_add_distrib]
    change (∑ j, (u j)^2) + (∑ j, (b n j)^2) + 2 * t * d ≤ _
    change (∑ j, (u j)^2) ≤ _ at he
    linarith

lemma sum_split_reflect (f : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (2*n+1), f k
      = (∑ k ∈ Finset.range n, f k) + (∑ k ∈ Finset.range n, f (2*n - k)) + f n := by
  have h1 : (∑ k ∈ Finset.Ico (n+1) (2*n+1), f k) = ∑ k ∈ Finset.range n, f (2*n - k) := by
    have h := Finset.sum_Ico_reflect f 0 (m := n) (n := 2*n) (by omega)
    rw [show (2*n+1:ℕ) - n = n+1 by omega, Nat.sub_zero, Nat.Ico_zero_eq_range] at h
    exact h.symm
  have h2 : (∑ k ∈ Finset.range (2*n+1), f k)
      = (∑ k ∈ Finset.range (n+1), f k) + (∑ k ∈ Finset.Ico (n+1) (2*n+1), f k) :=
    (Finset.sum_range_add_sum_Ico f (by omega)).symm
  rw [h2, Finset.sum_range_succ, h1]
  ring

variable {n k : ℕ} {w s : ℕ → ℝ}

def mkV (n : ℕ) (w s : ℕ → ℝ) : ℕ → ℝ := fun k =>
  if k < n then (1 + s k) * w k
  else if k = n then 0
  else if k ≤ 2 * n then (1 - s (2 * n - k)) * w k
  else w k

lemma mkV_of_lt (hk : k < n) : mkV n w s k = (1 + s k) * w k := by
  simp [mkV, hk]

lemma mkV_of_eq (hk : k = n) : mkV n w s k = 0 := by
  simp [mkV, hk]

lemma mkV_of_mid (hk1 : ¬ (k < n)) (hk2 : ¬ (k = n)) (hk3 : k ≤ 2 * n) :
    mkV n w s k = (1 - s (2 * n - k)) * w k := by
  simp [mkV, hk1, hk2, hk3]

lemma mkV_of_gt (hk1 : ¬ (k < n)) (hk2 : ¬ (k = n)) (hk3 : ¬ (k ≤ 2 * n)) :
    mkV n w s k = w k := by
  simp [mkV, hk1, hk2, hk3]

lemma mkV_center : mkV n w s n = 0 := mkV_of_eq rfl

lemma mkV_bounds (hw : ∀ k, 0 ≤ w k) (hs : ∀ k, s k = 1 ∨ s k = -1) :
    ∀ k, 0 ≤ mkV n w s k ∧ mkV n w s k ≤ 2 * w k := by
  intro k
  have hwk : (0 : ℝ) ≤ w k := hw k
  by_cases h1 : k < n
  · rw [mkV_of_lt h1]
    rcases hs k with h | h <;> rw [h] <;> constructor <;> nlinarith [hw k]
  · by_cases h2 : k = n
    · rw [mkV_of_eq h2]
      constructor <;> nlinarith [hw k]
    · by_cases h3 : k ≤ 2 * n
      · rw [mkV_of_mid h1 h2 h3]
        rcases hs (2 * n - k) with h | h <;> rw [h] <;> constructor <;> nlinarith [hw k]
      · rw [mkV_of_gt h1 h2 h3]
        constructor <;> nlinarith [hw k]

lemma mkV_reflect (hs : ∀ k, s k = 1 ∨ s k = -1) :
    ∀ k ≤ 2 * n, mkV n w s k * mkV n w s (2 * n - k) = 0 := by
  intro k hk
  by_cases h1 : k < n
  · have hge : ¬ (2 * n - k < n) := by omega
    have hne : ¬ (2 * n - k = n) := by omega
    have hle : 2 * n - k ≤ 2 * n := by omega
    have e1 : 2 * n - (2 * n - k) = k := by omega
    rw [mkV_of_lt h1, mkV_of_mid hge hne hle, e1]
    rcases hs k with h | h <;> rw [h] <;> ring
  · by_cases h2 : k = n
    · have hkn : 2 * n - k = n := by omega
      rw [hkn, h2, mkV_center, zero_mul]
    · have hjlt : 2 * n - k < n := by omega
      rw [mkV_of_mid h1 h2 hk, mkV_of_lt hjlt]
      rcases hs (2 * n - k) with h | h <;> rw [h] <;> ring

end Conjectures.Goldbach.ReflectionGridThinning_aux

open Conjectures.Goldbach.ReflectionGridThinning_aux

theorem Conjectures.Goldbach.ReflectionGridThinning :
∀ (n m : ℕ) (w : ℕ → ℝ) (a : ℕ → Fin m → ℝ), (∀ k, 0 ≤ w k) → ∃ v : ℕ → ℝ, (∀ k, 0 ≤ v k ∧ v k ≤ 2*w k) ∧ (∀ k ≤ 2*n, v k * v (2*n-k) = 0) ∧ v n = 0 ∧ (∑ j, ((∑ k ∈ Finset.range (2*n+1), (v k-w k)*a k j) + w n*a n j)^2) ≤ ∑ j, ∑ k ∈ Finset.range n, (w k*a k j-w (2*n-k)*a (2*n-k) j)^2 := by
  intro n m w a hw
  obtain ⟨s, hs, hbal⟩ := signBalance n m (fun k j => w k * a k j - w (2*n-k) * a (2*n-k) j)
  refine ⟨mkV n w s, ?_, ?_, ?_, ?_⟩
  · exact mkV_bounds hw hs
  · exact mkV_reflect hs
  · exact mkV_center
  · have key : ∀ j : Fin m,
        (∑ k ∈ Finset.range (2*n+1), (mkV n w s k - w k) * a k j) + w n * a n j
          = ∑ k ∈ Finset.range n, s k * (w k * a k j - w (2*n-k) * a (2*n-k) j) := by
      intro j
      have e1 : ∑ k ∈ Finset.range n, (mkV n w s k - w k) * a k j
          = ∑ k ∈ Finset.range n, s k * (w k * a k j) := by
        apply Finset.sum_congr rfl; intro k hk
        have hk' : k < n := Finset.mem_range.mp hk
        rw [mkV_of_lt hk']; ring
      have e2 : ∑ k ∈ Finset.range n, (mkV n w s (2*n-k) - w (2*n-k)) * a (2*n-k) j
          = -(∑ k ∈ Finset.range n, s k * (w (2*n-k) * a (2*n-k) j)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl; intro k hk
        have hk' : k < n := Finset.mem_range.mp hk
        have hge : ¬ (2*n - k < n) := by omega
        have hne : ¬ (2*n - k = n) := by omega
        have hle : 2*n - k ≤ 2*n := by omega
        have hC : 2*n - (2*n - k) = k := by omega
        rw [mkV_of_mid hge hne hle, hC]; ring
      have e3 : (mkV n w s n - w n) * a n j = -(w n * a n j) := by
        rw [mkV_center]; ring
      have e4 : ∑ k ∈ Finset.range n, s k * (w k * a k j - w (2*n-k) * a (2*n-k) j)
          = (∑ k ∈ Finset.range n, s k * (w k * a k j))
            - (∑ k ∈ Finset.range n, s k * (w (2*n-k) * a (2*n-k) j)) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro k _; ring
      rw [sum_split_reflect, e1, e2, e3, e4]
      ring
    simp_rw [key]
    exact hbal
