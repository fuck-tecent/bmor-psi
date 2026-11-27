import Mathlib

private def convAux (u v : ℕ → ℝ) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (n + 1)) (fun k => u k * v (n - k))

private lemma convAux_comm (u v : ℕ → ℝ) (n : ℕ) : convAux u v n = convAux v u n := by
  simp only [convAux]
  rw [← Finset.sum_range_reflect (fun j => v j * u (n - j)) (n + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ n := by
    have := Finset.mem_range.mp hj
    omega
  have h1 : n + 1 - 1 - j = n - j := by omega
  have h2 : n - (n - j) = j := by omega
  rw [h1, h2]
  ring

theorem PEqualNP.Outside.L_goldbach_conv_swap :
    let conv := fun (u v : ℕ → ℝ) (n : ℕ) => Finset.sum (Finset.range (n + 1)) (fun k => u k * v (n - k)); ∀ (u v : ℕ → ℝ) (n : ℕ), conv u v n = conv v u n := by
  exact fun u v n => convAux_comm u v n
