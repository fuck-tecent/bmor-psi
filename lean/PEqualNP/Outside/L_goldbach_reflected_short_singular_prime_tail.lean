import Mathlib

theorem PEqualNP.Outside.L_goldbach_reflected_short_singular_prime_tail :
    ∀ (y n : ℕ), 2 ≤ y → (∑ p ∈ n.primeFactors.filter (fun p => y < p), (1:ℝ)/((p:ℝ)-1)) ≤ Real.log n / ((y:ℝ)*Real.log (y+1)) := by
  intro y n hy
  by_cases hn : n = 0
  · simp [hn]
  let S := n.primeFactors.filter (fun p => y < p)
  let C : ℝ := (y:ℝ)*Real.log (y+1)
  have hy' : (2:ℝ) ≤ y := by exact_mod_cast hy
  have hC : 0<C := by
    dsimp [C]
    exact mul_pos (by linarith) (Real.log_pos (by linarith))
  have per (p : ℕ) (hp : p∈S) : (1:ℝ)/((p:ℝ)-1) ≤ Real.log p/C := by
    obtain ⟨hprime,hbig⟩ := Finset.mem_filter.mp hp
    have hprime := Nat.prime_of_mem_primeFactors hprime
    have hpn : (0:ℝ)<(p:ℝ)-1 := by
      have h : (2:ℝ) ≤ p := by exact_mod_cast hprime.two_le
      linarith
    have hp' : ((y:ℝ)+1) ≤ p := by exact_mod_cast hbig
    have hlog : Real.log (y+1) ≤ Real.log (p:ℝ) := Real.log_le_log (by linarith) hp'
    have hlogpos : 0 ≤ Real.log (y+1) := (Real.log_pos (by linarith : (1:ℝ)<y+1)).le
    apply (div_le_div_iff₀ hpn hC).2
    dsimp [C]
    have hmul := mul_le_mul (show (y:ℝ) ≤ p-1 by linarith) hlog hlogpos (by linarith : (0:ℝ)≤p-1)
    linarith
  have sumlog : (∑ p ∈ S, Real.log (p:ℝ)) ≤ Real.log n := by
    calc
      _ ≤ ∑ p ∈ n.primeFactors, Real.log (p:ℝ) := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun p hp _ => Real.log_nonneg
          (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le))
      _ ≤ _ := by
        rw [← Real.log_prod (s := n.primeFactors) (f := fun p : ℕ => (p:ℝ))
          (fun p hp => (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero : (p:ℝ) ≠ 0)),← Nat.cast_prod]
        have hprod : 0 < ∏ p ∈ n.primeFactors, p := Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
        exact Real.log_le_log (by exact_mod_cast hprod)
          (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n))
  change (∑ p ∈ S, (1:ℝ)/((p:ℝ)-1)) ≤ Real.log n/C
  calc
    _ ≤ ∑ p ∈ S, Real.log p/C := Finset.sum_le_sum per
    _ ≤ _ := by rw [← Finset.sum_div]; exact div_le_div_of_nonneg_right sumlog hC.le
