import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_secant_slice :
    let d := fun (a b c : ℤ × ℤ) => (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1); let ok := fun (S : Finset (ℤ × ℤ)) => ∀ a∈S, ∀ b∈S, ∀ c∈S, a≠b → b≠c → a≠c → d a b c≠0; ∀ (a b : ℤ × ℤ) (y x u : ℤ), a.2≠b.2 → d a b (x,y)=0 → d a b (u,y)=0 → x=u := by
  dsimp only
  intro a b y x u hne h1 h2
  have k1 : (b.2 - a.2) * (x - a.1) = (b.1 - a.1) * (y - a.2) := by linarith
  have k2 : (b.2 - a.2) * (u - a.1) = (b.1 - a.1) * (y - a.2) := by linarith
  have key : (b.2 - a.2) * (x - a.1) = (b.2 - a.2) * (u - a.1) := by linarith
  have := mul_left_cancel₀ (by omega : b.2 - a.2 ≠ 0) key
  linarith
