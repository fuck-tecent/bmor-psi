import Mathlib

theorem Conjectures.JoshiAbc.MarkedTransport :
    ∀ (K F : Type) [NontriviallyNormedField K] [NontriviallyNormedField F] [CompleteSpace K] [CompleteSpace F] (e : K ≃+* F), Continuous e → Continuous e.symm → ∀ q u : K, e (∑' n : ℤ, q^(n*(n+1)/2)*u^(2*n+1)) = ∑' n : ℤ, (e q)^(n*(n+1)/2)*(e u)^(2*n+1) := by
  intro K F _ _ _ _ e he he' q u
  rw [Function.LeftInverse.map_tsum _ he he' e.symm_apply_apply]
  apply tsum_congr
  intro n
  rw [map_mul, map_zpow₀, map_zpow₀]
