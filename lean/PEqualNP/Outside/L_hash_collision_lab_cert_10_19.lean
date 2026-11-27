import Mathlib

open scoped BigOperators

private lemma choose_key_pointwise (A B : ℕ) (hA : 1 ≤ A) (_hAB : A ≤ B) (n : ℕ) :
    B.choose (A - 1) * n + B.choose A ≤ n.choose A + B.choose (A - 1) * B := by
  have hpas : ∀ k, (k + 1).choose A = k.choose A + k.choose (A - 1) := by
    intro k
    have h := Nat.choose_succ_succ' k (A - 1)
    rw [Nat.sub_add_cancel hA] at h
    simpa [Nat.add_comm] using h
  rcases le_or_gt n B with hn | hn
  · have hmain : B.choose A ≤ n.choose A + B.choose (A - 1) * (B - n) := by
      revert hn
      refine Nat.decreasingInduction (n := B) (m := n)
        (motive := fun m _ => B.choose A ≤ m.choose A + B.choose (A - 1) * (B - m)) ?_ ?_
      · intro k hk ih
        have hle : k.choose (A - 1) ≤ B.choose (A - 1) := Nat.choose_le_choose _ (le_of_lt hk)
        rw [hpas k] at ih
        have hd : B - k = B - (k + 1) + 1 := by omega
        rw [hd]
        nlinarith [ih, hle]
      · simp
    nlinarith [hmain, Nat.sub_add_cancel hn]
  · have hlt : B ≤ n := le_of_lt hn
    have hmain : B.choose A + B.choose (A - 1) * (n - B) ≤ n.choose A := by
      revert hlt
      refine Nat.le_induction (motive := fun m _ => B.choose A + B.choose (A - 1) * (m - B) ≤ m.choose A) ?_ ?_ n
      · simp
      · intro m hm ih
        have hle : B.choose (A - 1) ≤ m.choose (A - 1) := Nat.choose_le_choose _ hm
        rw [hpas m]
        have hd : m + 1 - B = (m - B) + 1 := by omega
        rw [hd]
        nlinarith [ih, hle]
    nlinarith [hmain, Nat.sub_add_cancel hlt]


theorem PEqualNP.Outside.L_hash_collision_lab_cert_10_19 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*92378)+92378*(∑ i,b i)≤(∑ i,Nat.choose (b i) 10)+q*1755182 := by
  intro q b
  have hpt : ∀ n, 92378 * n + 92378 ≤ Nat.choose n 10 + 1755182 := by
    intro n
    have h := choose_key_pointwise 10 19 (by norm_num) (by norm_num) n
    have hY : Nat.choose 19 (10 - 1) = 92378 := by decide
    have hX : Nat.choose 19 10 = 92378 := by decide
    have hZ : 92378 * 19 = 1755182 := by norm_num
    rw [hY, hX, hZ] at h
    exact h
  have hsum : ∑ i : Fin q, (92378 * b i + 92378) ≤ ∑ i : Fin q, (Nat.choose (b i) 10 + 1755182) :=
    Finset.sum_le_sum (fun i _ => hpt (b i))
  have hL : (∑ i : Fin q, (92378 * b i + 92378)) = 92378 * (∑ i : Fin q, b i) + q * 92378 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  have hR : (∑ i : Fin q, (Nat.choose (b i) 10 + 1755182))
      = (∑ i : Fin q, Nat.choose (b i) 10) + q * 1755182 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  rw [hL, hR] at hsum
  nlinarith [hsum]
