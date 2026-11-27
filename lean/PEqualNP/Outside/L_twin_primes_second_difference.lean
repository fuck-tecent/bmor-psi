import Mathlib

namespace PEqualNP.Outside

private lemma shift1 (f : ℕ → ℝ) (h0 : f 0 = 0) (N : ℕ) :
    ∑ t ∈ Finset.range N, f (t - 1) = ∑ t ∈ Finset.range (N - 1), f t := by
  cases N with
  | zero => simp
  | succ M =>
    rw [Finset.sum_range_succ']
    simp [h0]

private lemma shift2 (f : ℕ → ℝ) (h0 : f 0 = 0) (N : ℕ) :
    ∑ t ∈ Finset.range N, f (t - 2) = ∑ t ∈ Finset.range (N - 2), f t := by
  set g : ℕ → ℝ := fun u => f (u - 1) with hgdef
  have hg0 : g 0 = 0 := by
    simp [hgdef, h0]
  calc ∑ t ∈ Finset.range N, f (t - 2)
      = ∑ t ∈ Finset.range N, g (t - 1) := by
        apply Finset.sum_congr rfl
        intro t _
        simp [hgdef, Nat.sub_sub]
    _ = ∑ t ∈ Finset.range (N - 1), g t := shift1 g hg0 N
    _ = ∑ t ∈ Finset.range (N - 1), f (t - 1) := by
        apply Finset.sum_congr rfl
        intro t _
        simp [hgdef]
    _ = ∑ t ∈ Finset.range (N - 2), f t := by
        have h := shift1 f h0 (N - 1)
        simpa [Nat.sub_sub] using h

private lemma trim (f : ℕ → ℝ) (M : ℕ) (h : ∀ n, M ≤ n → f n = 0)
    (N : ℕ) (hN : M ≤ N) :
    ∑ n ∈ Finset.range N, f n = ∑ n ∈ Finset.range M, f n := by
  refine (Finset.sum_subset ?_ ?_).symm
  · intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  · intro x hxN hxM
    simp only [Finset.mem_range] at hxN hxM
    exact h x (by omega)

theorem L_twin_primes_second_difference :
    let v := fun (X n : ℕ) => if n ≤ X then ArithmeticFunction.vonMangoldt n else 0;
    let F := fun (X H : ℕ) => (Finset.range (X+H+1)).sum (fun t => ((Finset.range H).sum (fun j => if j ≤ t then v X (t-j) else 0))^2);
    let C := fun (X h : ℕ) => (Finset.range (X+1)).sum (fun n => v X n * v X (n+h));
    ∀ X : ℕ, F X 3-2*F X 2+F X 1 = 2*C X 2 := by
  intro v F C X
  set a : ℕ → ℝ := fun n => v X n with ha
  have ha0 : a 0 = 0 := by
    simp [ha, v]
  have ha1 : a 1 = 0 := by
    by_cases hX : (1:ℕ) ≤ X
    · have hv : (if (1:ℕ) ≤ X then ArithmeticFunction.vonMangoldt 1 else 0) = 0 := by
        rw [if_pos hX, ArithmeticFunction.vonMangoldt_apply_one]
      simpa [ha, v] using hv
    · have hv : (if (1:ℕ) ≤ X then ArithmeticFunction.vonMangoldt 1 else 0) = 0 := by
        rw [if_neg hX]
      simpa [ha, v] using hv
  have hvanish : ∀ n, X < n → a n = 0 := by
    intro n hn
    have hnl : ¬ n ≤ X := by omega
    simp [ha, v, hnl]
  have hin1 : ∀ t : ℕ, (Finset.range 1).sum (fun j => if j ≤ t then a (t - j) else 0) = a t := by
    intro t
    rw [Finset.sum_range_one]
    simp
  have hin2 : ∀ t : ℕ,
      (Finset.range 2).sum (fun j => if j ≤ t then a (t - j) else 0) = a t + a (t - 1) := by
    intro t
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    have h0 : (if (0:ℕ) ≤ t then a (t - 0) else 0) = a t := by simp
    have h1 : (if (1:ℕ) ≤ t then a (t - 1) else 0) = a (t - 1) := by
      by_cases ht : 1 ≤ t
      · simp [ht]
      · have ht0 : t = 0 := by omega
        simp [ht, ht0, ha0]
    simp [h0, h1]
  have hin3 : ∀ t : ℕ,
      (Finset.range 3).sum (fun j => if j ≤ t then a (t - j) else 0)
        = a t + a (t - 1) + a (t - 2) := by
    intro t
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    have h0 : (if (0:ℕ) ≤ t then a (t - 0) else 0) = a t := by simp
    have h1 : (if (1:ℕ) ≤ t then a (t - 1) else 0) = a (t - 1) := by
      by_cases ht : 1 ≤ t
      · simp [ht]
      · have ht0 : t = 0 := by omega
        simp [ht, ht0, ha0]
    have h2 : (if (2:ℕ) ≤ t then a (t - 2) else 0) = a (t - 2) := by
      by_cases ht : 2 ≤ t
      · simp [ht]
      · have ht1 : t - 2 = 0 := by omega
        have hta : a (t - 2) = 0 := by rw [ht1]; exact ha0
        simp [ht, hta]
    simp [h0, h1, h2]
  have hv1 : ∀ t : ℕ, (Finset.range 1).sum (fun j => if j ≤ t then v X (t - j) else 0) = v X t := by
    intro t
    simpa [ha] using hin1 t
  have hv2 : ∀ t : ℕ, (Finset.range 2).sum (fun j => if j ≤ t then v X (t - j) else 0) = v X t + v X (t - 1) := by
    intro t
    simpa [ha] using hin2 t
  have hv3 : ∀ t : ℕ, (Finset.range 3).sum (fun j => if j ≤ t then v X (t - j) else 0) = v X t + v X (t - 1) + v X (t - 2) := by
    intro t
    simpa [ha] using hin3 t
  have hF1 : F X 1 = ∑ t ∈ Finset.range (X+1+1), (a t)^2 := by
    simp [F, hv1, ha]
  have hF2 : F X 2 = ∑ t ∈ Finset.range (X+2+1), (a t + a (t - 1))^2 := by
    simp [F, hv2, ha]
  have hF3 : F X 3 = ∑ t ∈ Finset.range (X+3+1), (a t + a (t - 1) + a (t - 2))^2 := by
    simp [F, hv3, ha]
  have hsq_zero : ∀ n, X + 1 ≤ n → (a n)^2 = 0 := by
    intro n hn
    have hXn : X < n := by omega
    have h := hvanish n hXn
    simp [h]
  have hpair_zero : ∀ n, X + 2 ≤ n → (a n + a (n - 1))^2 = 0 := by
    intro n hn
    have h1 : a n = 0 := hvanish n (by omega)
    have h2 : a (n - 1) = 0 := hvanish (n - 1) (by omega)
    simp [h1, h2]
  have hE1 : ∑ t ∈ Finset.range (X+1+1), (a t)^2 = ∑ t ∈ Finset.range (X+3+1), (a t)^2 := by
    have h2 : X + 1 + 1 = X + 2 := by omega
    have hA : ∑ t ∈ Finset.range (X+2), (a t)^2 = ∑ t ∈ Finset.range (X+1), (a t)^2 :=
      trim (fun n => (a n)^2) (X+1) hsq_zero (X+2) (by omega)
    have hB : ∑ t ∈ Finset.range (X+3+1), (a t)^2 = ∑ t ∈ Finset.range (X+1), (a t)^2 :=
      trim (fun n => (a n)^2) (X+1) hsq_zero (X+3+1) (by omega)
    rw [h2]
    exact hA.trans hB.symm
  have hE2 : ∑ t ∈ Finset.range (X+2+1), (a t + a (t - 1))^2
      = ∑ t ∈ Finset.range (X+3+1), (a t + a (t - 1))^2 := by
    have h3 : X + 2 + 1 = X + 3 := by omega
    have hA : ∑ t ∈ Finset.range (X+3), (a t + a (t - 1))^2
        = ∑ t ∈ Finset.range (X+2), (a t + a (t - 1))^2 :=
      trim (fun n => (a n + a (n - 1))^2) (X+2) hpair_zero (X+3) (by omega)
    have hB : ∑ t ∈ Finset.range (X+3+1), (a t + a (t - 1))^2
        = ∑ t ∈ Finset.range (X+2), (a t + a (t - 1))^2 :=
      trim (fun n => (a n + a (n - 1))^2) (X+2) hpair_zero (X+3+1) (by omega)
    rw [h3]
    exact hA.trans hB.symm
  have hCombine : F X 3 - 2*F X 2 + F X 1
      = ∑ t ∈ Finset.range (X+3+1),
          ((a t + a (t - 1) + a (t - 2))^2 - 2*(a t + a (t - 1))^2 + (a t)^2) := by
    rw [hF3, hF2, hF1, hE1, hE2]
    rw [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    rw [← Finset.sum_add_distrib]
  have hExpand : ∑ t ∈ Finset.range (X+3+1),
        ((a t + a (t - 1) + a (t - 2))^2 - 2*(a t + a (t - 1))^2 + (a t)^2)
      = ∑ t ∈ Finset.range (X+3+1),
        ((a (t - 2))^2 - (a (t - 1))^2 - 2*(a t * a (t - 1))
          + 2*(a t * a (t - 2)) + 2*(a (t - 1) * a (t - 2))) := by
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hT1 : ∑ t ∈ Finset.range (X+3+1), (a (t - 2))^2
      = ∑ t ∈ Finset.range (X+2), (a t)^2 := by
    have h := shift2 (fun n => (a n)^2) (by simp [ha0]) (X+3+1)
    simpa [show X + 3 + 1 - 2 = X + 2 by omega] using h
  have hT2 : ∑ t ∈ Finset.range (X+3+1), (a (t - 1))^2
      = ∑ t ∈ Finset.range (X+3), (a t)^2 := by
    have h := shift1 (fun n => (a n)^2) (by simp [ha0]) (X+3+1)
    simpa [show X + 3 + 1 - 1 = X + 3 by omega] using h
  have hT2b : ∑ t ∈ Finset.range (X+3), (a t)^2 = ∑ t ∈ Finset.range (X+2), (a t)^2 := by
    have h1 : ∑ t ∈ Finset.range (X+3), (a t)^2 = ∑ t ∈ Finset.range (X+1), (a t)^2 :=
      trim (fun n => (a n)^2) (X+1) hsq_zero (X+3) (by omega)
    have h2 : ∑ t ∈ Finset.range (X+2), (a t)^2 = ∑ t ∈ Finset.range (X+1), (a t)^2 :=
      trim (fun n => (a n)^2) (X+1) hsq_zero (X+2) (by omega)
    exact h1.trans h2.symm
  have hT3 : ∑ t ∈ Finset.range (X+3+1), a t * a (t - 1)
      = ∑ t ∈ Finset.range (X+3), a t * a (t - 1) := by
    have hzero : ∀ n, X + 3 ≤ n → a n * a (n - 1) = 0 := by
      intro n hn
      have h1 : a n = 0 := hvanish n (by omega)
      simp [h1]
    exact trim (fun n => a n * a (n - 1)) (X+3) hzero (X+3+1) (by omega)
  have hT5 : ∑ t ∈ Finset.range (X+3+1), a (t - 1) * a (t - 2)
      = ∑ t ∈ Finset.range (X+3), a t * a (t - 1) := by
    have hg0 : (fun u : ℕ => a u * a (u - 1)) 0 = 0 := by simp [ha0]
    have h := shift1 (fun u : ℕ => a u * a (u - 1)) hg0 (X+3+1)
    simpa [Nat.sub_sub, show X + 3 + 1 - 1 = X + 3 by omega] using h
  have hT4bridge : ∑ t ∈ Finset.range (X+3+1), a t * a (t - 2)
      = ∑ t ∈ Finset.range (X+3+1), (fun n => a (n + 2) * a n) (t - 2) := by
    apply Finset.sum_congr rfl
    intro t _
    by_cases ht : 2 ≤ t
    · have hsub : t - 2 + 2 = t := by omega
      simp [hsub]
    · have ht0 : a t = 0 := by
        have : t = 0 ∨ t = 1 := by omega
        rcases this with h | h
        · simp [h, ha0]
        · simp [h, ha1]
      have ht2 : a (t - 2) = 0 := by
        have hle : t - 2 = 0 := by omega
        simp [hle, ha0]
      simp [ht0, ht2]
  have hT4 : ∑ t ∈ Finset.range (X+3+1), (fun n => a (n + 2) * a n) (t - 2)
      = ∑ t ∈ Finset.range (X+2), a (t + 2) * a t := by
    have h := shift2 (fun n => a (n + 2) * a n) (by simp [ha0]) (X+3+1)
    simpa [show X + 3 + 1 - 2 = X + 2 by omega] using h
  have hT4b : ∑ t ∈ Finset.range (X+2), a (t + 2) * a t = C X 2 := by
    have hCs : C X 2 = ∑ t ∈ Finset.range (X+1), a t * a (t + 2) := by
      simp [C, ha]
    have hzero : ∀ n, X + 1 ≤ n → a (n + 2) * a n = 0 := by
      intro n hn
      have h1 : a n = 0 := hvanish n (by omega)
      simp [h1]
    have htrim : ∑ t ∈ Finset.range (X+2), a (t + 2) * a t
        = ∑ t ∈ Finset.range (X+1), a (t + 2) * a t :=
      trim (fun n => a (n + 2) * a n) (X+1) hzero (X+2) (by omega)
    rw [hCs, htrim]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hSplit : ∑ t ∈ Finset.range (X+3+1),
        ((a (t - 2))^2 - (a (t - 1))^2 - 2*(a t * a (t - 1))
          + 2*(a t * a (t - 2)) + 2*(a (t - 1) * a (t - 2)))
      = (∑ t ∈ Finset.range (X+3+1), (a (t - 2))^2)
        - (∑ t ∈ Finset.range (X+3+1), (a (t - 1))^2)
        - 2*(∑ t ∈ Finset.range (X+3+1), a t * a (t - 1))
        + 2*(∑ t ∈ Finset.range (X+3+1), a t * a (t - 2))
        + 2*(∑ t ∈ Finset.range (X+3+1), a (t - 1) * a (t - 2)) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hCombine, hExpand, hSplit, hT1, hT2, hT2b, hT3, hT5, hT4bridge, hT4, hT4b]
  ring

end PEqualNP.Outside


