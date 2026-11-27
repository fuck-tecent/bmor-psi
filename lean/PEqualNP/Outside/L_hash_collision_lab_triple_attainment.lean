import Mathlib

private lemma aux_const_split (q m A B : ℕ) :
    (∑ i : Fin q, (if i.val < m then A else B)) = (min q m) * A + (q - min q m) * B := by
  rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin q)))
    (p := fun i : Fin q => i.val < m)]
  have h1 : ((Finset.univ : Finset (Fin q)).filter (fun i => i.val < m)).card = min q m :=
    Fin.card_filter_val_lt
  have hAdd : ((Finset.univ : Finset (Fin q)).filter (fun i => i.val < m)).card
      + ((Finset.univ : Finset (Fin q)).filter (fun i => ¬ i.val < m)).card = q := by
    rw [Finset.card_filter_add_card_filter_not]
    simp
  have h2 : ((Finset.univ : Finset (Fin q)).filter (fun i => ¬ i.val < m)).card = q - min q m := by
    omega
  rw [Finset.sum_const_nat (m := A) (fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp [hi]),
      Finset.sum_const_nat (m := B) (fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp [hi]),
      h1, h2]

theorem PEqualNP.Outside.L_hash_collision_lab_triple_attainment :
    ∀ q M:ℕ,0<q → ∃ b:Fin q→ℕ,(∑ i,b i)=M ∧ (∑ i,Nat.choose (b i) 3)=(q-M % q)*Nat.choose (M/q) 3+(M % q)*Nat.choose (M/q+1) 3 := by
  intro q M hq
  have hrq : M % q ≤ q := Nat.le_of_lt (Nat.mod_lt M hq)
  refine ⟨fun i : Fin q => if i.val < q - M % q then M / q else M / q + 1, ?_, ?_⟩
  · rw [aux_const_split]
    have hmin : min q (q - M % q) = q - M % q := Nat.min_eq_right (Nat.sub_le q (M % q))
    have hsub : q - (q - M % q) = M % q := by omega
    rw [hmin, hsub]
    have hM : q * (M / q) + M % q = M := Nat.div_add_mod M q
    have e1 : M % q * (M / q + 1) = M % q * (M / q) + M % q := by ring
    have e2 : (q - M % q) * (M / q) + M % q * (M / q) = q * (M / q) := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hrq]
    omega
  · have hcongr : (∑ i : Fin q, Nat.choose (if i.val < q - M % q then M / q else M / q + 1) 3)
        = ∑ i : Fin q, (if i.val < q - M % q then Nat.choose (M / q) 3 else Nat.choose (M / q + 1) 3) := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> rfl
    rw [hcongr, aux_const_split]
    have hmin : min q (q - M % q) = q - M % q := Nat.min_eq_right (Nat.sub_le q (M % q))
    have hsub : q - (q - M % q) = M % q := by omega
    rw [hmin, hsub]
