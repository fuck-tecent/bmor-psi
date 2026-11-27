import Mathlib

namespace Conjectures.Goldbach

theorem Rfc11ResidualDomainGlue :
    ∀ (lo hi : ℕ) (S A V : ℕ → Prop), (∀ n, lo≤n → n<hi → 2∣n → S n ∨ A n ∨ V n) → (∀ n, S n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n) → (∀ n, A n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n) → (∀ n, V n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n) → (fun (lo hi : ℕ) => ∀ n : ℕ, lo≤n → n<hi → 2∣n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n) lo hi := by
  intro lo hi S A V hcover hS hA hV n hlo hhi hEven
  rcases hcover n hlo hhi hEven with h | h | h
  · exact hS n h
  · exact hA n h
  · exact hV n h

end Conjectures.Goldbach
