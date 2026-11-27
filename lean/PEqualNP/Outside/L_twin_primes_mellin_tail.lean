import Mathlib

theorem PEqualNP.Outside.L_twin_primes_mellin_tail :
    ∀ C : ℝ, 0 ≤ C → ∃ D : ℝ, 0 ≤ D ∧ ∀ (L : ℕ) (m : ℕ → ℝ), (∀ n, 0 ≤ m n ∧ m n ≤ C*Real.log (2+(n:ℝ))) → (∑' n : ℕ, m (L+n)/(1+(L:ℝ)+n)^6) ≤ D/(1+(L:ℝ))^4 := by
  have key : ∀ x y : ℝ, 1 ≤ x → y = x + 1 → (1:ℝ)/x^5 ≤ 4*(1/x^4 - 1/y^4) := by
    intro x y hx hy
    subst hy
    have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
    have hx1 : 0 < x + 1 := by linarith
    have hd : 0 < x^4*(x+1)^4 := by positivity
    have hA : 4*x^3 ≤ (x+1)^4 - x^4 := by
      have hq : (0:ℝ) ≤ 6*(x+1/3)^2 + 1/3 := by positivity
      nlinarith [hq, sq_nonneg x]
    have hB : (x+1)^4 ≤ 16*x^4 := by
      have h : x + 1 ≤ 2*x := by linarith
      calc (x+1)^4 ≤ (2*x)^4 := pow_le_pow_left₀ hx1.le h 4
        _ = 16*x^4 := by ring
    have h2 : (16:ℝ)*x^3/(x^4*(16*x^4)) ≤ 16*x^3/(x^4*(x+1)^4) := by
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      exact mul_le_mul_of_nonneg_left hB (by positivity)
    have h3 : (16:ℝ)*x^3/(x^4*(x+1)^4) ≤ 4*((x+1)^4 - x^4)/(x^4*(x+1)^4) := by
      refine div_le_div_of_nonneg_right ?_ hd.le
      linarith [hA]
    have h4 : (4:ℝ)*((x+1)^4 - x^4)/(x^4*(x+1)^4) = 4*(1/x^4 - 1/(x+1)^4) := by
      field_simp <;> ring
    have h5 : (1:ℝ)/x^5 = 16*x^3/(x^4*(16*x^4)) := by
      field_simp <;> ring
    calc (1:ℝ)/x^5 = 16*x^3/(x^4*(16*x^4)) := h5
      _ ≤ 16*x^3/(x^4*(x+1)^4) := h2
      _ ≤ 4*((x+1)^4 - x^4)/(x^4*(x+1)^4) := h3
      _ = 4*(1/x^4 - 1/(x+1)^4) := h4
  intro C hC
  refine ⟨4*C, by positivity, ?_⟩
  intro L m hm
  have hpt : ∀ n : ℕ, m (L+n)/(1+(L:ℝ)+n)^6 ≤ 4*C*(1/(1+(L:ℝ)+n)^4 - 1/(1+(L:ℝ)+((n+1:ℕ):ℝ))^4) := by
    intro n
    have hx : (1:ℝ) ≤ 1+(L:ℝ)+n := by
      have h1 : (0:ℝ) ≤ (L:ℝ) := Nat.cast_nonneg L
      have h2 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    have hlog : Real.log (2 + ((L+n:ℕ):ℝ)) ≤ 1+(L:ℝ)+n := by
      have hpos : 0 < 2 + ((L+n:ℕ):ℝ) := by
        have hnn : (0:ℝ) ≤ ((L+n:ℕ):ℝ) := Nat.cast_nonneg _
        linarith
      have h1 := Real.log_le_sub_one_of_pos hpos
      rwa [show (2:ℝ) + ((L+n:ℕ):ℝ) - 1 = 1+(L:ℝ)+n by push_cast; ring] at h1
    have hmle : m (L+n) ≤ C*(1+(L:ℝ)+n) := by
      calc m (L+n) ≤ C * Real.log (2 + ((L+n:ℕ):ℝ)) := (hm (L+n)).2
        _ ≤ C*(1+(L:ℝ)+n) := mul_le_mul_of_nonneg_left hlog hC
    have h6 : 0 < (1+(L:ℝ)+n)^6 := by positivity
    have hk := key (1+(L:ℝ)+n) (1+(L:ℝ)+((n+1:ℕ):ℝ)) hx (by push_cast; ring)
    calc m (L+n)/(1+(L:ℝ)+n)^6 ≤ C*(1+(L:ℝ)+n)/(1+(L:ℝ)+n)^6 :=
            div_le_div_of_nonneg_right hmle h6.le
      _ = C*((1:ℝ)/(1+(L:ℝ)+n)^5) := by field_simp <;> ring
      _ ≤ C*(4*(1/(1+(L:ℝ)+n)^4 - 1/(1+(L:ℝ)+((n+1:ℕ):ℝ))^4)) :=
            mul_le_mul_of_nonneg_left hk hC
      _ = 4*C*(1/(1+(L:ℝ)+n)^4 - 1/(1+(L:ℝ)+((n+1:ℕ):ℝ))^4) := by ring
  have htel : ∀ N : ℕ, ∑ i ∈ Finset.range N, ((1:ℝ)/(1+(L:ℝ)+i)^4 - 1/(1+(L:ℝ)+((i+1:ℕ):ℝ))^4)
      = 1/(1+(L:ℝ))^4 - 1/(1+(L:ℝ)+N)^4 := by
    intro N
    have h := Finset.sum_range_sub (fun i : ℕ => -((1:ℝ)/(1+(L:ℝ)+i)^4)) N
    calc ∑ i ∈ Finset.range N, ((1:ℝ)/(1+(L:ℝ)+i)^4 - 1/(1+(L:ℝ)+((i+1:ℕ):ℝ))^4)
        = ∑ i ∈ Finset.range N, (-((1:ℝ)/(1+(L:ℝ)+((i+1:ℕ):ℝ))^4) - -((1:ℝ)/(1+(L:ℝ)+i)^4)) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ = -((1:ℝ)/(1+(L:ℝ)+N)^4) - -((1:ℝ)/(1+(L:ℝ)+((0:ℕ):ℝ))^4) := h
      _ = 1/(1+(L:ℝ))^4 - 1/(1+(L:ℝ)+N)^4 := by push_cast <;> ring
  refine Real.tsum_le_of_sum_range_le (f := fun n : ℕ => m (L+n)/(1+(L:ℝ)+n)^6)
    (c := 4*C/(1+(L:ℝ))^4) ?_ ?_
  · intro n
    exact div_nonneg (hm (L+n)).1 (by positivity)
  · intro N
    calc ∑ i ∈ Finset.range N, m (L+i)/(1+(L:ℝ)+i)^6
        ≤ ∑ i ∈ Finset.range N, 4*C*(1/(1+(L:ℝ)+i)^4 - 1/(1+(L:ℝ)+((i+1:ℕ):ℝ))^4) :=
          Finset.sum_le_sum (fun i _ => hpt i)
      _ = 4*C*(1/(1+(L:ℝ))^4 - 1/(1+(L:ℝ)+N)^4) := by
          rw [← Finset.mul_sum, htel N]
      _ ≤ 4*C*(1/(1+(L:ℝ))^4) := by
          have hnn : (0:ℝ) ≤ 1/(1+(L:ℝ)+N)^4 := by positivity
          have hcc : (0:ℝ) ≤ 4*C := by positivity
          nlinarith
      _ = 4*C/(1+(L:ℝ))^4 := by ring
