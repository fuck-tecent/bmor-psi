import Mathlib

theorem PEqualNP.Outside.L_goldbach_characters_odd_card :
    ∀ (n : ℕ) [NeZero n], 2<n → let odd := (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1); 2*odd.card=n.totient := by
  intro n _ hn
  dsimp only
  classical
  let odd := (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1)
  change 2 * odd.card = n.totient
  have : Fact (2 < n) := ⟨hn⟩
  have hzero := DirichletCharacter.sum_characters_eq_zero ℂ (ZMod.neg_one_ne_one (n := n))
  have hcount : Fintype.card (DirichletCharacter ℂ n) = n.totient := by
    rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  have h : (2 : ℂ) * odd.card = (n.totient : ℂ) := calc
    (2 : ℂ) * odd.card = ∑ _χ ∈ odd, (2 : ℂ) := by simp [nsmul_eq_mul, mul_comm]
    _ = ∑ χ : DirichletCharacter ℂ n, (1 - χ (-1)) := by
      unfold odd
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro χ _
      rcases χ.even_or_odd with he | ho
      · change χ (-1) = 1 at he
        norm_num [he]
      · change χ (-1) = -1 at ho
        norm_num [ho]
    _ = (n.totient : ℂ) := by simp [Finset.sum_sub_distrib, hzero, hcount]
  exact_mod_cast h
