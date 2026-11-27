import Mathlib

theorem PEqualNP.Outside.L_goldbach_odd_kernel_quadratic :
    ∀ (n : ℕ) (a : ℕ → ℝ), (∑ i ∈ Finset.range (n+1), ∑ j ∈ Finset.range (n+1), a i*a j*((if i=j then 1 else 0)-(if i+j=n then 1 else 0))) = (∑ i ∈ Finset.range (n+1), (a i)^2) - ∑ i ∈ Finset.range (n+1), a i*a (n-i) := by
  intro n a
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have href : n - i ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hanti (j : ℕ) : i + j = n ↔ n - i = j := by omega
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, hanti]
  simp [hi, href, pow_two]
