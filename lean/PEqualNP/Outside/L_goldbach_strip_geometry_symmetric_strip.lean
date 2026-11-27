import Mathlib

theorem PEqualNP.Outside.L_goldbach_strip_geometry_symmetric_strip :
    ∀ (P : ℂ → Prop) (s : ℂ), P s → P (1-s) → (∀ z, P z → z.re≤1/2) → s.re=1/2 := by
  intro P s hs hs' h
  have h1 : s.re ≤ 1/2 := h s hs
  have h2 : (1-s).re ≤ 1/2 := h (1-s) hs'
  simp only [Complex.sub_re, Complex.one_re] at h2
  linarith
