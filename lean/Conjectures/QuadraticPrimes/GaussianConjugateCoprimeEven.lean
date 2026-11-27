import Mathlib

theorem Conjectures.QuadraticPrimes.GaussianConjugateCoprimeEven :
    ∀ n : ℕ, Even n → IsCoprime ((n : GaussianInt) + ⟨0,1⟩) ((n : GaussianInt) - ⟨0,1⟩) := by
  intro n hn
  obtain ⟨m, hm⟩ := hn
  refine ⟨-(m : GaussianInt), (m : GaussianInt) + ⟨0,1⟩, ?_⟩
  have hcast : (n : GaussianInt) = (m : GaussianInt) + (m : GaussianInt) := by
    rw [hm]; push_cast; ring
  have hii : (⟨0,1⟩ : GaussianInt) * ⟨0,1⟩ = -1 := by
    ext <;> simp
  rw [hcast]
  linear_combination -hii
