import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_fixed_a_discriminant :
    ∀ (p a : ℕ) [Fact p.Prime], (∃ r : ZMod p, r^2+a=0 ∧ 2*r=0) ↔ p ∣ 4*a := by
  intro p a
  intro hfact
  haveI : Fact p.Prime := hfact
  constructor
  · rintro ⟨r, hr1, hr2⟩
    have ha : (a : ZMod p) = -(r^2) := by linear_combination hr1
    have h4 : (4 : ZMod p) * r^2 = 0 := by
      have h2 : (2*r)^2 = 0 := by rw [hr2]; ring
      calc (4 : ZMod p) * r^2 = (2*r)^2 := by ring
        _ = 0 := h2
    have hzero : ((4*a : ℕ) : ZMod p) = 0 := by
      push_cast
      rw [ha]
      linear_combination -h4
    exact (CharP.cast_eq_zero_iff (ZMod p) p (4*a)).mp hzero
  · intro hdvd
    by_cases hp2 : p = 2
    · subst hp2
      have h2 : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
      refine ⟨(a : ZMod 2), ?_, ?_⟩
      · have hsq : (a : ZMod 2)^2 = (a : ZMod 2) := ZMod.pow_card _
        rw [hsq]
        linear_combination (a : ZMod 2) * h2
      · simp [h2]
    · have hp4 : ¬ p ∣ 4 := by
        intro hh
        have h' : p ∣ 2^2 := by simpa using hh
        have hp2d : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow h'
        rcases Nat.prime_two.eq_one_or_self_of_dvd p hp2d with h1 | h1
        · exact (Fact.out : p.Prime).ne_one h1
        · exact hp2 h1
      have hpa : p ∣ a := by
        rcases (Fact.out : p.Prime).dvd_mul.mp hdvd with h | h
        · exact absurd h hp4
        · exact h
      have haz : (a : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p a).mpr hpa
      refine ⟨0, ?_, ?_⟩
      · simp [haz]
      · simp
