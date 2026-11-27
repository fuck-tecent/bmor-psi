import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_7_15 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*6435)+5005*(∑ i,b i)≤(∑ i,Nat.choose (b i) 7)+q*75075 := by
  intro q b
  have centerVal : Nat.choose 15 7 = 6435 := by decide
  have centerSlope : Nat.choose 15 6 = 5005 := by decide
  have pascal (m : ℕ) : Nat.choose (m + 1) 7 =
      Nat.choose m 6 + Nat.choose m 7 :=
    Nat.choose_succ_succ' m 6
  have above : ∀ m : ℕ, 15 ≤ m →
      6435 + 5005 * m ≤ Nat.choose m 7 + 75075 := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => rw [centerVal] <;> decide
    | succ m hm ih =>
      have hs := Nat.choose_le_choose 6 hm
      rw [centerSlope] at hs
      calc
        _ = (6435 + 5005 * m) + 5005 := by rw [Nat.mul_succ] <;> ac_rfl
        _ ≤ (Nat.choose m 7 + 75075) + Nat.choose m 6 := Nat.add_le_add ih hs
        _ = _ := by rw [pascal] <;> ac_rfl
  have below : ∀ d m : ℕ, m + d = 15 →
      6435 + 5005 * m ≤ Nat.choose m 7 + 75075 := by
    intro d
    induction d with
    | zero =>
      intro m hm
      have eqCenter : m = 15 := by omega
      subst m
      rw [centerVal] <;> decide
    | succ d ih =>
      intro m hm
      have hnext := ih (m + 1) (by omega)
      have hs := Nat.choose_le_choose 6 (show m ≤ 15 by omega)
      rw [centerSlope] at hs
      have hp := pascal m
      omega
  have point (m : ℕ) : 6435 + 5005 * m ≤ Nat.choose m 7 + 75075 := by
    by_cases hm : 15 ≤ m
    · exact above m hm
    · exact below (15 - m) m (by omega)
  have total := Finset.sum_le_sum (s := Finset.univ)
    (fun (i : Fin q) _ => point (b i))
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, ← Finset.mul_sum] using total
