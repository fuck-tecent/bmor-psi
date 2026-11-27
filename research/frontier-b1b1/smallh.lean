import Mathlib
open scoped BigOperators

noncomputable section
namespace B1B1

def Qs (n : ℕ) : ℕ := (Nat.log 2 (n+2))^2
def Qcut (n : ℕ) : ℕ := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
def Hwide (n : ℕ) : ℕ := 256 * Qcut n * Qs n

/-- For small `h` every arc contributes its full length, and the `a`-sum
contributes a factor `q`; the total over the arc family is `2 H Q₁ / n`. -/
lemma small_h_arc_total (n : ℕ) (hn : 0 < n) :
    (∑ q ∈ Finset.Icc 1 (Qcut n),
        (q:ℝ) * (2*(Hwide n:ℝ)/((q:ℝ)*(n:ℝ))))
      = 2*(Hwide n:ℝ)*(Qcut n:ℝ)/(n:ℝ) := by
  have hnR : (n:ℝ) ≠ 0 := by positivity
  have hterm : ∀ q ∈ Finset.Icc 1 (Qcut n),
      (q:ℝ) * (2*(Hwide n:ℝ)/((q:ℝ)*(n:ℝ))) = 2*(Hwide n:ℝ)/(n:ℝ) := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hqR : (q:ℝ) ≠ 0 := by positivity
    field_simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  norm_num
  ring

end B1B1
