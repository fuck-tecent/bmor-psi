import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_quadratic_graph_fourier :
    ∀ (p : ℕ) [NeZero p] (a n : ZMod p),
      (∑ t : ZMod p, ZMod.stdAddChar (t*(n^2+a))) = if n^2+a=0 then (p : ℂ) else 0 := by
  intro p _ a n
  by_cases h : n ^ 2 + a = 0
  · rw [if_pos h]
    have hterm : ∀ t : ZMod p, ZMod.stdAddChar (t * (n ^ 2 + a)) = 1 := by
      intro t
      rw [h, mul_zero, AddChar.map_zero_eq_one]
    rw [Finset.sum_congr rfl (fun t _ => hterm t)]
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  · rw [if_neg h]
    have hchar : AddChar.mulShift (ZMod.stdAddChar (N := p)) (n ^ 2 + a) ≠ 1 :=
      ZMod.isPrimitive_stdAddChar p h
    have hsum : (∑ t : ZMod p, ZMod.stdAddChar (t * (n ^ 2 + a))) =
        ∑ t : ZMod p, AddChar.mulShift (ZMod.stdAddChar (N := p)) (n ^ 2 + a) t := by
      apply Finset.sum_congr rfl
      intro t _
      rw [AddChar.mulShift_apply, mul_comm]
    rw [hsum]
    exact AddChar.sum_eq_zero_of_ne_one hchar
