import Mathlib

theorem PEqualNP.Outside.L_goldbach_conductor_odd_fixed :
    ∀ (m : ℕ) (r : Fin m → Fin m) (v : Fin m → ℂ), (∀ i, v (r i)= -v i) → ∀ i, r i=i → v i=0 := by
  intro m r v hodd i hfixed
  apply CharZero.eq_neg_self_iff.mp
  simpa only [hfixed] using hodd i
