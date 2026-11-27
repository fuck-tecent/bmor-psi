import Mathlib

open scoped ComplexConjugate

theorem PEqualNP.Outside.L_goldbach_strip_geometry_mirror_denom :
    ∀ s : ℂ, s.re=1/2 → ‖1-s‖=‖s‖ := by
  intro s hs
  have hreflect : 1 - s = conj s := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    · simp
  rw [hreflect, Complex.norm_conj]
