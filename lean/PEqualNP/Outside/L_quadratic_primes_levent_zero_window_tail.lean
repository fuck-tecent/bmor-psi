import Mathlib
open Finset

private lemma quad_telescope (t : ℝ) (ht : 1 ≤ t) :
    1/t^5 ≤ 2*(1/t^4 - 1/(t+1)^4) := by
  have htpos : (0:ℝ) < t := by linarith
  have ht1pos : (0:ℝ) < t+1 := by linarith
  rw [div_le_iff₀ (by positivity : (0:ℝ) < t^5)]
  have e : 2*(1/t^4 - 1/(t+1)^4)*t^5 = 2*(t*(t+1)^4 - t^5)/(t+1)^4 := by
    field_simp
  rw [e]
  rw [le_div_iff₀ (by positivity : (0:ℝ) < (t+1)^4)]
  nlinarith [sq_nonneg t, sq_nonneg (t+1), ht]

theorem PEqualNP.Outside.L_quadratic_primes_levent_zero_window_tail :
    ∀ (b : ℕ → ℝ) (C : ℝ), 0≤C → (∀ j, 0≤b j ∧ b j≤C*Real.log (2+(j : ℝ))) → ∃ D : ℝ, 0≤D ∧ ∀ L : ℕ, (∑' j : ℕ, b (L+j)/(1+((L+j : ℕ) : ℝ))^6) ≤ D/(1+(L : ℝ))^4 := by
  intro b C hC hb
  refine ⟨4*C, by linarith, ?_⟩
  intro L
  set s : ℝ := 1 + (L:ℝ) with hs
  have hspos : (0:ℝ) < s := by rw [hs]; positivity
  have hs1 : (1:ℝ) ≤ s := by rw [hs]; have hL : (0:ℝ) ≤ (L:ℝ) := Nat.cast_nonneg L; linarith
  have hterm : ∀ j : ℕ, b (L+j)/(1+((L+j : ℕ) : ℝ))^6 ≤ 2*C/(s+(j:ℝ))^5 := by
    intro j
    have hden : (1 + ((L+j : ℕ) : ℝ)) = s + (j:ℝ) := by rw [hs]; push_cast; ring
    rw [hden]
    have hsj : (1:ℝ) ≤ s + (j:ℝ) := by
      have : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
      linarith
    have hbj : b (L+j) ≤ C*Real.log (2+((L+j : ℕ) : ℝ)) := (hb (L+j)).2
    have hargnn : (0:ℝ) ≤ 2+((L+j : ℕ) : ℝ) := by positivity
    have hlogle : Real.log (2+((L+j : ℕ) : ℝ)) ≤ 2+((L+j : ℕ) : ℝ) := Real.log_le_self hargnn
    have hbj2 : b (L+j) ≤ 2*C*(s+(j:ℝ)) := by
      have h1 : C*Real.log (2+((L+j : ℕ) : ℝ)) ≤ C*(2+((L+j : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogle hC
      have hcast : (2+((L+j : ℕ) : ℝ)) = (s+(j:ℝ)) + 1 := by rw [hs]; push_cast; ring
      have h2 : C*(2+((L+j : ℕ) : ℝ)) ≤ 2*C*(s+(j:ℝ)) := by
        rw [hcast]
        nlinarith [hC, hsj]
      linarith
    have h6 : (0:ℝ) < (s+(j:ℝ))^6 := by positivity
    rw [show (2:ℝ)*C/(s+(j:ℝ))^5 = 2*C*(s+(j:ℝ))/(s+(j:ℝ))^6 by field_simp]
    rw [div_le_div_iff_of_pos_right h6]
    exact hbj2
  have hnn : ∀ j : ℕ, (0:ℝ) ≤ b (L+j)/(1+((L+j : ℕ) : ℝ))^6 := by
    intro j
    apply div_nonneg (hb (L+j)).1
    positivity
  apply Real.tsum_le_of_sum_range_le (f := fun j : ℕ => b (L+j)/(1+((L+j : ℕ) : ℝ))^6) (c := 4*C/s^4) hnn
  intro n
  have hstep1 : (∑ i ∈ Finset.range n, b (L+i)/(1+((L+i : ℕ) : ℝ))^6)
      ≤ ∑ i ∈ Finset.range n, 2*C/(s+(i:ℝ))^5 := by
    apply Finset.sum_le_sum
    intro i _
    exact hterm i
  have htel : (∑ i ∈ Finset.range n, 1/(s+(i:ℝ))^5) ≤ 2/s^4 := by
    have h1 : (∑ i ∈ Finset.range n, 1/(s+(i:ℝ))^5)
        ≤ ∑ i ∈ Finset.range n, 2*(1/(s+(i:ℝ))^4 - 1/(s+((i:ℝ)+1))^4) := by
      apply Finset.sum_le_sum
      intro i _
      have hsi : (1:ℝ) ≤ s + (i:ℝ) := by
        have : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
        linarith
      have := quad_telescope (s+(i:ℝ)) hsi
      simpa [add_assoc] using this
    have h2 : (∑ i ∈ Finset.range n, 2*(1/(s+(i:ℝ))^4 - 1/(s+((i:ℝ)+1))^4))
        = 2*(1/s^4 - 1/(s+(n:ℝ))^4) := by
      rw [← Finset.mul_sum]
      congr 1
      have h := Finset.sum_range_sub' (fun i : ℕ => (1:ℝ)/(s+(i:ℝ))^4) n
      simpa [Nat.cast_add, Nat.cast_one] using h
    have h3 : 2*(1/s^4 - 1/(s+(n:ℝ))^4) ≤ 2/s^4 := by
      have h4 : (0:ℝ) ≤ 1/(s+(n:ℝ))^4 := by positivity
      have hEq : (2:ℝ)/s^4 = 2*(1/s^4) := by rw [div_eq_mul_inv, one_div]
      linarith [h4, hEq]
    rw [h2] at h1
    linarith
  have hstep2 : (∑ i ∈ Finset.range n, 2*C/(s+(i:ℝ))^5) = 2*C * (∑ i ∈ Finset.range n, 1/(s+(i:ℝ))^5) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_one_div]
  rw [hstep2] at hstep1
  have hstep3 : 2*C * (∑ i ∈ Finset.range n, 1/(s+(i:ℝ))^5) ≤ 2*C * (2/s^4) := by
    apply mul_le_mul_of_nonneg_left htel
    linarith
  have hfin : 2*C*(2/s^4) = 4*C/s^4 := by ring
  linarith [hstep1, hstep3, hfin]
