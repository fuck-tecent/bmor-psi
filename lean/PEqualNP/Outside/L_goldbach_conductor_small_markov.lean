import Mathlib

theorem PEqualNP.Outside.L_goldbach_conductor_small_markov :
    ∀ (n : ℕ) [NeZero n], 2<n → let odd := (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1); ((odd.filter (fun χ => χ.conductor^4≤n^3)).card : ℝ)*Real.log (n:ℝ) ≤ 4*∑ χ ∈ odd, Real.log ((n:ℝ)/(χ.conductor:ℝ)) := by
  intro n _ hn odd
  let low := odd.filter (fun χ => χ.conductor^4 ≤ n^3)
  let loss (χ : DirichletCharacter ℂ n) := Real.log ((n:ℝ)/(χ.conductor:ℝ))
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hdpos (χ : DirichletCharacter ℂ n) : 0 < (χ.conductor : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hnonneg (χ : DirichletCharacter ℂ n) : 0 ≤ loss χ := by
    apply Real.log_nonneg
    apply (one_le_div (hdpos χ)).mpr
    exact_mod_cast Nat.le_of_dvd (show 0 < n by omega) χ.conductor_dvd_level
  have hcharge (χ : DirichletCharacter ℂ n) (hχ : χ ∈ low) :
      Real.log n ≤ 4 * loss χ := by
    have hp : (χ.conductor : ℝ)^4 ≤ (n : ℝ)^3 := by
      exact_mod_cast (Finset.mem_filter.mp hχ).2
    have hlog := Real.log_le_log (pow_pos (hdpos χ) 4) hp
    rw [Real.log_pow, Real.log_pow] at hlog
    dsimp only [loss]
    rw [Real.log_div hnpos.ne' (hdpos χ).ne']
    norm_num at hlog
    linarith
  calc
    _ = ∑ _χ ∈ low, Real.log (n : ℝ) := by simp [low]
    _ ≤ ∑ χ ∈ low, 4 * loss χ := Finset.sum_le_sum hcharge
    _ = 4 * ∑ χ ∈ low, loss χ := (Finset.mul_sum ..).symm
    _ ≤ 4 * ∑ χ ∈ odd, loss χ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun χ _ _ => hnonneg χ)
