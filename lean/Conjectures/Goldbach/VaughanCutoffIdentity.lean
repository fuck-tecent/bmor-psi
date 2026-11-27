import Mathlib

theorem Conjectures.Goldbach.VaughanCutoffIdentity :
    let cut (h : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
      ⟨fun k => if k ≤ h then f k else 0, (ite_eq_left (Nat.zero_le h)).trans f.map_zero⟩
    let L := ArithmeticFunction.vonMangoldt
    let m : ArithmeticFunction ℝ := ArithmeticFunction.moebius
    let z : ArithmeticFunction ℝ := ArithmeticFunction.zeta
    ∀ U V : ℕ, let a := cut U m
               let b := cut V L
               L = b + a * ArithmeticFunction.log - a * b * z + (m-a) * ((L-b) * z) := by
  intro cut L m z U V a b
  have hinv : m * z = 1 := ArithmeticFunction.coe_moebius_mul_coe_zeta
  have hlog : L * z = ArithmeticFunction.log := ArithmeticFunction.vonMangoldt_mul_zeta
  calc
    L = b + (m * z) * (L - b) := by rw [hinv, one_mul]; abel
    _ = b + a * ArithmeticFunction.log - a * b * z + (m-a) * ((L-b) * z) := by
      rw [← hlog]
      ring
