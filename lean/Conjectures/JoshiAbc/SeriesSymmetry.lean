import Mathlib

noncomputable section

theorem Conjectures.JoshiAbc.SeriesSymmetry :
  ∀ (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K], let theta := fun (q u : K) => ∑' n : ℤ, q^(n*(n+1)/2) * u^(2*n+1); ∀ q u : K, u ≠ 0 → q ≠ 0 → theta q u⁻¹ = theta q u := by
  intro K _ _ _
  dsimp only
  intro q u hu hq
  let e : ℤ ≃ ℤ := ⟨fun n => -n-1, fun n => -n-1, by intro n; dsimp; omega, by intro n; dsimp; omega⟩
  have hexp (n : ℤ) : (-n-1)*(-n-1+1)/2 = n*(n+1)/2 := by congr 1 <;> ring
  have hflip (n : ℤ) : 2*(-n-1)+1 = -(2*n+1) := by ring
  have hp (n : ℤ) : q^((-n-1)*(-n-1+1)/2) * u^(2*(-n-1)+1) = q^(n*(n+1)/2)*(u⁻¹)^(2*n+1) := by
    rw [hexp, hflip, zpow_neg, inv_zpow]
  have h := e.tsum_eq (fun n : ℤ => q^(n*(n+1)/2) * u^(2*n+1))
  simp only [e, Equiv.coe_fn_mk] at h
  simp_rw [hp] at h
  exact h
