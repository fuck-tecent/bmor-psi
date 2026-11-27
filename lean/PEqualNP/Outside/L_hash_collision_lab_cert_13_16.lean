import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_13_16 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*560)+1820*(∑ i,b i)≤(∑ i,Nat.choose (b i) 13)+q*29120 := by
  intro q b
  have centerVal : Nat.choose 16 13 = 560 := by decide
  have centerSlope : Nat.choose 16 12 = 1820 := by decide
  have pascal (m : ℕ) : Nat.choose (m + 1) 13 =
      Nat.choose m 12 + Nat.choose m 13 :=
    Nat.choose_succ_succ' m 12
  have above : ∀ m : ℕ, 16 ≤ m →
      560 + 1820 * m ≤ Nat.choose m 13 + 29120 := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => rw [centerVal] <;> decide
    | succ m hm ih =>
      have hs := Nat.choose_le_choose 12 hm
      rw [centerSlope] at hs
      calc
        _ = (560 + 1820 * m) + 1820 := by rw [Nat.mul_succ] <;> ac_rfl
        _ ≤ (Nat.choose m 13 + 29120) + Nat.choose m 12 := Nat.add_le_add ih hs
        _ = _ := by rw [pascal] <;> ac_rfl
  have below : ∀ d m : ℕ, m + d = 16 →
      560 + 1820 * m ≤ Nat.choose m 13 + 29120 := by
    intro d
    induction d with
    | zero =>
      intro m hm
      have eqCenter : m = 16 := by omega
      subst m
      rw [centerVal] <;> decide
    | succ d ih =>
      intro m hm
      have hnext := ih (m + 1) (by omega)
      have hs := Nat.choose_le_choose 12 (show m ≤ 16 by omega)
      rw [centerSlope] at hs
      have hp := pascal m
      omega
  have point (m : ℕ) : 560 + 1820 * m ≤ Nat.choose m 13 + 29120 := by
    by_cases hm : 16 ≤ m
    · exact above m hm
    · exact below (16 - m) m (by omega)
  have total := Finset.sum_le_sum (s := Finset.univ)
    (fun (i : Fin q) _ => point (b i))
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, ← Finset.mul_sum] using total
