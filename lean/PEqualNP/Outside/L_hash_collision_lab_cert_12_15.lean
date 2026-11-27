import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_12_15 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*455)+1365*(∑ i,b i)≤(∑ i,Nat.choose (b i) 12)+q*20475 := by
  intro q b
  have centerVal : Nat.choose 15 12 = 455 := by decide
  have centerSlope : Nat.choose 15 11 = 1365 := by decide
  have pascal (m : ℕ) : Nat.choose (m + 1) 12 =
      Nat.choose m 11 + Nat.choose m 12 :=
    Nat.choose_succ_succ' m 11
  have above : ∀ m : ℕ, 15 ≤ m →
      455 + 1365 * m ≤ Nat.choose m 12 + 20475 := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => rw [centerVal] <;> decide
    | succ m hm ih =>
      have hs := Nat.choose_le_choose 11 hm
      rw [centerSlope] at hs
      calc
        _ = (455 + 1365 * m) + 1365 := by rw [Nat.mul_succ] <;> ac_rfl
        _ ≤ (Nat.choose m 12 + 20475) + Nat.choose m 11 := Nat.add_le_add ih hs
        _ = _ := by rw [pascal] <;> ac_rfl
  have below : ∀ d m : ℕ, m + d = 15 →
      455 + 1365 * m ≤ Nat.choose m 12 + 20475 := by
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
      have hs := Nat.choose_le_choose 11 (show m ≤ 15 by omega)
      rw [centerSlope] at hs
      have hp := pascal m
      omega
  have point (m : ℕ) : 455 + 1365 * m ≤ Nat.choose m 12 + 20475 := by
    by_cases hm : 15 ≤ m
    · exact above m hm
    · exact below (15 - m) m (by omega)
  have total := Finset.sum_le_sum (s := Finset.univ)
    (fun (i : Fin q) _ => point (b i))
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, ← Finset.mul_sum] using total
