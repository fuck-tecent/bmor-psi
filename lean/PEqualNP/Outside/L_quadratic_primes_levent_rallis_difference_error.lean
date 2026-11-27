import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_rallis_difference_error :
    ∀ A P Q M N E e f h : ℝ, 0<A → |(P-Q)/A-4*E|≤h → |P/A-M|≤e → |Q/A-N|≤f → |4*E-(M-N)|≤e+f+h := by
  intro A P Q M N E e f h _ hmatch hP hQ
  rw [sub_div] at hmatch
  rcases abs_le.mp hmatch with ⟨hmlo, hmhi⟩
  rcases abs_le.mp hP with ⟨hPlo, hPhi⟩
  rcases abs_le.mp hQ with ⟨hQlo, hQhi⟩
  apply abs_le.mpr
  constructor <;> linarith
