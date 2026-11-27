import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_balanced_profile :
    ∀ (q k:ℕ) (b:Fin q→ℕ), (∀ i,b i=k ∨ b i=k+1) → (∑ i,b i)=q*k+((Finset.univ:Finset (Fin q)).filter (fun i => b i=k+1)).card := by
  intro q k b hb
  have key : ∀ i : Fin q, b i = k + (if b i = k + 1 then 1 else 0) := by
    intro i
    rcases hb i with h | h
    · rw [h]
      simp
    · rw [h]
      simp
  have hsum : (∑ i : Fin q, b i) = ∑ i : Fin q, (k + (if b i = k + 1 then 1 else 0)) :=
    Finset.sum_congr rfl (fun i _ => key i)
  have hsplit : (∑ i : Fin q, (k + (if b i = k + 1 then 1 else 0)))
      = (∑ i : Fin q, k) + ∑ i : Fin q, (if b i = k + 1 then 1 else 0) :=
    Finset.sum_add_distrib
  have hk : (∑ i : Fin q, k) = q * k := by
    rw [Finset.sum_const_nat (m := k) (fun i _ => rfl), Finset.card_univ, Fintype.card_fin]
  have hcard : (∑ i : Fin q, (if b i = k + 1 then 1 else 0))
      = ((Finset.univ : Finset (Fin q)).filter (fun i => b i = k + 1)).card := by
    rw [Finset.card_filter]
  rw [hsum, hsplit, hk, hcard]
