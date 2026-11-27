import Mathlib

private theorem aux_containment_iff {n d e a : ℤ} :
    -d ≤ n - e * a ↔ a * e ≤ n + d := by
  constructor <;> intro h <;> linarith

theorem Conjectures.JoshiAbc.TraceDualFloor :
    ∀ (n d e t : ℤ), 0 < e → (∀ a : ℤ, a ≤ t ↔ -d ≤ n-e*a) → t = (n+d)/e := by
  intro n d e t he h
  apply eq_of_forall_le_iff
  intro a
  rw [h a, aux_containment_iff, Int.le_ediv_iff_mul_le he]
