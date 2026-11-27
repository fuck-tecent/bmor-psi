import Mathlib

theorem Conjectures.Goldbach.Rfc11DescendingTail :
    let P := fun (lo hi : ℕ) => ∀ n : ℕ, lo≤n → n<hi → 2∣n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n; ∀ a b c : ℕ, P a b → P b c → P a c := by
  dsimp only
  intro a b c hab hbc n hlo hhi heven
  rcases Nat.lt_or_ge n b with hlt | hge
  · exact hab n hlo hlt heven
  · exact hbc n hge hhi heven
