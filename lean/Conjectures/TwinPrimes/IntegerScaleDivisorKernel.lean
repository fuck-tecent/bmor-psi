import Mathlib

theorem Conjectures.TwinPrimes.IntegerScaleDivisorKernel :
    ∀ Y p d : ℕ, (Finset.Ico Y (2*Y)).filter (fun X => X<p ∧ 50*p<51*X ∧ X<d^3) = Finset.Ico (max Y (50*p/51+1)) (min (2*Y) (min p (d^3))) := by
  intro Y p d
  ext X
  simp only [Finset.mem_filter, Finset.mem_Ico, lt_min_iff, max_le_iff]
  omega
