import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Finset.Union

theorem PEqualNP.Outside.L_goldbach_finite_witness_translate_bitset :
    ∀ (P Q D : Finset ℕ), (∀ p ∈ P, Nat.Prime p) → (∀ q ∈ Q, Nat.Prime q) → D ⊆ P.biUnion (fun p => Q.image (fun q => p+q)) → ∀ n ∈ D, ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n := by
  intro P Q D hP hQ hcover n hn
  obtain ⟨p, hp, hqImage⟩ := Finset.mem_biUnion.mp (hcover hn)
  obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hqImage
  exact ⟨p, q, hP p hp, hQ q hq, heq⟩
