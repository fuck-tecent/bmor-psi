import Mathlib

theorem PEqualNP.Outside.L_goldbach_conductor_dyadic_sum :
    ∀ k : ℕ, 2≤k → (∑ j ∈ Finset.Icc 1 k, if 2 < 2^k/2^j then (Nat.totient (2^k/2^j) : ℝ)/Nat.totient (2^k) else 0) = 1-4/(2:ℝ)^k := by
  intro k hk
  have htot : ∀ t : ℕ, 0 < t → (Nat.totient (2^t) : ℝ) = (2:ℝ)^(t-1) := by
    intro t ht
    rw [Nat.totient_prime_pow Nat.prime_two ht]
    norm_num
  have hterm : ∀ j : ℕ, j ≤ k →
      (if 2 < 2^k/2^j then (Nat.totient (2^k/2^j) : ℝ)/Nat.totient (2^k) else 0) =
        if j ≤ k-2 then 1/(2:ℝ)^j else 0 := by
    intro j hj
    rw [Nat.pow_div hj (by norm_num : 0 < (2:ℕ))]
    by_cases h : j ≤ k-2
    · have ht : 2 ≤ k-j := by omega
      have hp : 2 < (2:ℕ)^(k-j) := by
        have h' := Nat.pow_lt_pow_right (by norm_num : 1 < (2:ℕ)) (show 1 < k-j by omega)
        simpa using h'
      rw [ite_eq_left hp, ite_eq_left h, htot (k-j) (by omega), htot k (by omega)]
      have he : k-1 = (k-j-1)+j := by omega
      rw [he, pow_add]
      have hn : (2:ℝ)^(k-j-1) ≠ 0 := by positivity
      have hn' : (2:ℝ)^j ≠ 0 := by positivity
      field_simp
    · have ht : k-j ≤ 1 := by omega
      have hp : ¬ 2 < (2:ℕ)^(k-j) := by
        have h' := Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) ht
        norm_num at h' ⊢
        omega
      simp [hp, h]
  have hgeom : ∀ m : ℕ, (∑ j ∈ Finset.Icc 1 m, 1/(2:ℝ)^j) = 1-1/(2:ℝ)^m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, pow_succ]
      have hn : (2:ℝ)^m ≠ 0 := by positivity
      field_simp
      ring
  calc
    (∑ j ∈ Finset.Icc 1 k, if 2 < 2^k/2^j then (Nat.totient (2^k/2^j) : ℝ)/Nat.totient (2^k) else 0)
        = ∑ j ∈ Finset.Icc 1 k, if j ≤ k-2 then 1/(2:ℝ)^j else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hterm j (Finset.mem_Icc.mp hj).2
    _ = ∑ j ∈ Finset.Icc 1 (k-2), 1/(2:ℝ)^j := by
      rw [← Finset.sum_filter]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    _ = 1-1/(2:ℝ)^(k-2) := hgeom (k-2)
    _ = 1-4/(2:ℝ)^k := by
      have he : k = (k-2)+2 := by omega
      conv_rhs => rw [he, pow_add]
      have hn : (2:ℝ)^(k-2) ≠ 0 := by positivity
      norm_num
      field_simp
