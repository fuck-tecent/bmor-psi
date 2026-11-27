import Mathlib

/-! Certificate gap `L-hash-collision-lab-cert-4-5` (hash-collision-lab desk). `b ↦ choose b 4`
is discretely convex, so every bucket lies above its tangent line at load 5,
`choose b 4 ≥ 5 + 10 * (b - 5)`; summing over the `q` buckets gives the bound. -/

/-- Tangent line of `b ↦ choose b (j+1)` at `m`: discrete convexity, by Pascal's rule. -/
private theorem hash_tangent (j m b : ℕ) :
    Nat.choose m (j+1) + Nat.choose m j * b ≤ Nat.choose b (j+1) + Nat.choose m j * m := by
  rcases le_total m b with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    induction d with
    | zero => simp
    | succ d ih =>
      have hp : Nat.choose (m + (d+1)) (j+1) = Nat.choose (m+d) j + Nat.choose (m+d) (j+1) := by
        rw [show m + (d+1) = (m+d) + 1 by omega, Nat.choose_succ_succ']
      have hm : Nat.choose m j ≤ Nat.choose (m+d) j := Nat.choose_le_choose j (Nat.le_add_right m d)
      have e : Nat.choose m j * (m + (d+1)) = Nat.choose m j * (m+d) + Nat.choose m j := by ring
      have := ih (Nat.le_add_right m d)
      rw [hp, e]; linarith
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    induction d generalizing b with
    | zero => simp
    | succ d ih =>
      have ih' := ih (b+1) (by omega)
      rw [show b + 1 + d = b + (d+1) by omega] at ih'
      have hp : Nat.choose (b+1) (j+1) = Nat.choose b j + Nat.choose b (j+1) :=
        Nat.choose_succ_succ' b j
      have hm : Nat.choose b j ≤ Nat.choose (b + (d+1)) j :=
        Nat.choose_le_choose j (Nat.le_add_right b (d+1))
      have e : Nat.choose (b+(d+1)) j * (b+1) = Nat.choose (b+(d+1)) j * b + Nat.choose (b+(d+1)) j := by ring
      rw [hp, e] at ih'; linarith

theorem PEqualNP.Outside.L_hash_collision_lab_cert_4_5 : ∀ (q:ℕ) (b:Fin q→ℕ), (q*5)+10*(∑ i,b i)≤(∑ i,Nat.choose (b i) 4)+q*50 := by
  intro q b
  have key : ∀ i, 5 + 10 * b i ≤ Nat.choose (b i) 4 + 50 := fun i => by
    have h := hash_tangent 3 5 (b i)
    rw [show Nat.choose 5 4 = 5 by rfl, show Nat.choose 5 3 = 10 by rfl] at h
    simpa using h
  have hs := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) => key i
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, ← Finset.mul_sum] at hs
  linarith
