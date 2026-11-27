import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside

theorem L_goldbach_factor_line_near_diagonal_budget :
    ∀ (J : Finset ℤ) (D : ℕ) (u v : ℤ → ℝ) (B : ℝ), 0 ≤ B → (∀ i ∈ J, |u i * v i| ≤ B) → |∑ i ∈ J, ∑ j ∈ J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D), u i * v i * (u j * v j)| ≤ (J.card:ℝ) * (2*(D:ℝ)) * B^2 := by
  intro J D u v B hB hweight
  have hcount (i : ℤ) : (J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D)).card ≤ 2 * D := by
    let S : Finset ℤ := (Finset.Icc (i - D) (i + D)).erase i
    have hsub : J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D) ⊆ S := by
      intro j hj
      have hj' := (Finset.mem_filter.mp hj).2
      have ha : |j-i| ≤ (D : ℤ) := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast hj'.2
      simp only [S, Finset.mem_erase, Finset.mem_Icc]
      constructor
      · exact hj'.1
      · have := abs_le.mp ha
        omega
    have hi : i ∈ Finset.Icc (i - D) (i + D) := by
      simp only [Finset.mem_Icc]
      constructor <;> omega
    have hcard : S.card = 2 * D := by
      have h := Int.card_Icc_of_le (a := i - D) (b := i + D) (by omega)
      have he := Finset.card_erase_of_mem hi
      dsimp [S]
      omega
    exact (Finset.card_le_card hsub).trans_eq hcard
  have hterm (i j : ℤ) (hi : i ∈ J) (hj : j ∈ J) :
      |u i * v i * (u j * v j)| ≤ B^2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (hweight i hi) (hweight j hj) (abs_nonneg _) hB
  calc
    |∑ i ∈ J, ∑ j ∈ J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D), u i * v i * (u j * v j)|
        ≤ ∑ i ∈ J, ∑ j ∈ J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D), |u i * v i * (u j * v j)| := by
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i ∈ J, (2 * (D : ℝ)) * B^2 := by
          apply Finset.sum_le_sum
          intro i hi
          calc
            _ ≤ ((J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D)).card : ℝ) * B^2 := by
              simpa using (Finset.sum_le_card_nsmul (J.filter (fun j => j ≠ i ∧ (j-i).natAbs ≤ D)) (fun j => |u i * v i * (u j * v j)|) (B^2) (by intro j hj; exact hterm i j hi (Finset.mem_filter.mp hj).1))
            _ ≤ (2 * (D : ℝ)) * B^2 := by
              gcongr
              exact_mod_cast hcount i
    _ = (J.card:ℝ) * (2*(D:ℝ)) * B^2 := by simp [mul_assoc]

end PEqualNP.Outside
