import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_quadratic_gauss_norm :
    ∀ (p : ℕ) [Fact p.Prime] (a b : ZMod p), p≠2 → a≠0 → ‖∑ n : ZMod p, ZMod.stdAddChar (a*n^2+b*n)‖^2 = (p : ℝ) := by
  intro p _ a b hp ha
  have hpprime : p.Prime := Fact.out
  have hpodd : (2 : ZMod p) ≠ 0 := by
    have h2 : ¬ p ∣ 2 := by
      intro h
      have := Nat.le_of_dvd (by norm_num) h
      have := hpprime.two_le
      omega
    exact fun h => h2 ((ZMod.natCast_eq_zero_iff 2 p).1 h)
  have h2a : (2 : ZMod p) * a ≠ 0 := mul_ne_zero hpodd ha
  have hstar : ∀ x : ZMod p, star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
    intro x
    rw [Complex.star_def]
    exact (AddChar.map_neg_eq_conj ZMod.stdAddChar x).symm
  have hinner : ∀ d : ZMod p,
      (∑ n : ZMod p, ZMod.stdAddChar (-(2*a*d*n))) = if d = 0 then (p : ℂ) else 0 := by
    intro d
    rw [show (∑ n : ZMod p, ZMod.stdAddChar (-(2*a*d*n)))
        = ∑ n : ZMod p, ZMod.stdAddChar (n * (-(2*a*d))) from
      Finset.sum_congr rfl fun n _ => by rw [show -(2*a*d*n) = n * (-(2*a*d)) by ring]]
    rw [AddChar.sum_mulShift (-(2*a*d)) (ZMod.isPrimitive_stdAddChar p)]
    have hd : (-(2*a*d) = 0) ↔ d = 0 := by
      rw [neg_eq_zero, mul_eq_zero]
      simp [h2a]
    by_cases hd0 : d = 0
    · simp [hd0, ZMod.card]
    · have h : ¬ (-(2*a*d) = 0) := fun hh => hd0 (hd.mp hh)
      simp [h, hd0]
  have hterm : ∀ n d : ZMod p,
      ZMod.stdAddChar (a*n^2+b*n) * star (ZMod.stdAddChar (a*(d+n)^2+b*(d+n)))
        = ZMod.stdAddChar (-(a*d^2+b*d)) * ZMod.stdAddChar (-(2*a*d*n)) := by
    intro n d
    rw [hstar, ← AddChar.map_add_eq_mul,
      show a*n^2+b*n + -(a*(d+n)^2+b*(d+n)) = -(a*d^2+b*d) + -(2*a*d*n) by ring,
      AddChar.map_add_eq_mul]
  set S : ℂ := ∑ n : ZMod p, ZMod.stdAddChar (a*n^2+b*n) with hS
  have hSS1 : S * star S
      = ∑ n : ZMod p, ∑ d : ZMod p,
          ZMod.stdAddChar (a*n^2+b*n) * star (ZMod.stdAddChar (a*(d+n)^2+b*(d+n))) := by
    rw [hS, star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Equiv.sum_comp (Equiv.addRight n)
      (fun m => ZMod.stdAddChar (a*n^2+b*n) * star (ZMod.stdAddChar (a*m^2+b*m)))]
    simp only [Equiv.coe_addRight]
  have hSS2 : (∑ n : ZMod p, ∑ d : ZMod p,
        ZMod.stdAddChar (a*n^2+b*n) * star (ZMod.stdAddChar (a*(d+n)^2+b*(d+n))))
      = ∑ d : ZMod p, ZMod.stdAddChar (-(a*d^2+b*d)) * (∑ n : ZMod p, ZMod.stdAddChar (-(2*a*d*n))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => hterm n d
  have hdsum : (∑ d : ZMod p, ZMod.stdAddChar (-(a*d^2+b*d)) * (if d = 0 then (p : ℂ) else 0)) = (p : ℂ) := by
    rw [Finset.sum_eq_single (0 : ZMod p)]
    · simp
    · intro d _ hd
      simp [hd]
    · intro h
      exact absurd (Finset.mem_univ (0 : ZMod p)) h
  have hSS : S * star S = (p : ℂ) := by
    rw [hSS1, hSS2]
    calc ∑ d : ZMod p, ZMod.stdAddChar (-(a*d^2+b*d)) * (∑ n : ZMod p, ZMod.stdAddChar (-(2*a*d*n)))
        = ∑ d : ZMod p, ZMod.stdAddChar (-(a*d^2+b*d)) * (if d = 0 then (p : ℂ) else 0) := by
          refine Finset.sum_congr rfl fun d _ => by rw [hinner d]
      _ = (p : ℂ) := hdsum
  have hnorm : ‖S‖^2 = (p : ℝ) := by
    have h1 : ‖S‖^2 = ‖S * star S‖ := by rw [norm_mul, norm_star, sq]
    rw [h1, hSS]
    simp
  simpa [hS] using hnorm
