import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_conductor_odd_split :
    ∀ (m : ℕ) (r : Fin m → Fin m) (v : Fin m → ℂ), Function.Involutive r → let p := fun x i => (x i-x (r i))/2; ∀ i, p (p v) i=p v i := by
  intro m r v hr
  dsimp only
  intro i
  rw [hr i]
  ring
