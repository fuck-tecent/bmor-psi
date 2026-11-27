import Mathlib

namespace Conjectures.Goldbach.Rfc11CompatibleTwoFieldClasses_aux

private def witness : ℕ → ℕ × ℕ
  | 0 => (5, 23)
  | 2 => (5, 25)
  | 4 => (9, 23)
  | 6 => (9, 25)
  | 8 => (13, 23)
  | 10 => (13, 25)
  | 12 => (17, 23)
  | 14 => (5, 9)
  | 16 => (5, 11)
  | 18 => (9, 9)
  | 20 => (9, 11)
  | 22 => (13, 9)
  | 24 => (13, 11)
  | 26 => (17, 9)
  | _ => (0, 0)

private theorem witness_spec (r : ℕ) (hr : r < 28) (he : r % 2 = 0) :
    (witness r).1 < 28 ∧ (witness r).2 < 28 ∧
      ((witness r).1 + (witness r).2) % 28 = r % 28 ∧
      (witness r).1 % 4 = 1 ∧
      ((witness r).2 % 7 = 2 ∨ (witness r).2 % 7 = 4) ∧
      (witness r).1 % 7 ≠ 1 ∧
      Nat.Coprime (witness r).1 28 ∧ Nat.Coprime (witness r).2 28 := by
  interval_cases r <;> first | omega | decide

end Conjectures.Goldbach.Rfc11CompatibleTwoFieldClasses_aux

open Conjectures.Goldbach.Rfc11CompatibleTwoFieldClasses_aux in
theorem Conjectures.Goldbach.Rfc11CompatibleTwoFieldClasses :
    ∀ n : ℕ, 2 ∣ n → ∃ a b : ℕ, a < 28 ∧ b < 28 ∧ (a + b) % 28 = n % 28 ∧ a % 4 = 1 ∧ (b % 7 = 2 ∨ b % 7 = 4) ∧ a % 7 ≠ 1 ∧ Nat.Coprime a 28 ∧ Nat.Coprime b 28 := by
  intro n hn
  rcases hn with ⟨k, rfl⟩
  have hr : (2 * k) % 28 < 28 := Nat.mod_lt _ (by decide)
  have he : (2 * k) % 28 % 2 = 0 := by omega
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := witness_spec ((2 * k) % 28) hr he
  refine ⟨(witness ((2 * k) % 28)).1, (witness ((2 * k) % 28)).2, h1, h2, ?_, h4, h5, h6, h7, h8⟩
  rw [h3, Nat.mod_eq_of_lt hr]
