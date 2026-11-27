import Mathlib

private theorem keyA (Q n : ℕ) (t : ℝ) (hQ1 : 1 ≤ Q) (hQn : Q ≤ n) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1)
    (hmem : ¬ ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / q| ≤ (Q : ℝ) / ((q : ℝ) * n)) :
    ∃ q a : ℕ, Q < q ∧ q ≤ n / Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * (((n / Q : ℕ) : ℝ) + 1)) := by
  have hQ0 : 0 < Q := by omega
  have hn0 : 0 < n := by omega
  have hH0 : 0 < n / Q := Nat.div_pos hQn hQ0
  have hH1 : (1 : ℝ) ≤ ((n / Q : ℕ) : ℝ) := by exact_mod_cast hH0
  have hhalf : (1 : ℝ) / (((n / Q : ℕ) : ℝ) + 1) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hQH : n ≤ Q * (n / Q + 1) := (Nat.lt_mul_div_succ n hQ0).le
  obtain ⟨j, k, hk0, hkH, habs⟩ := Real.exists_int_int_abs_mul_sub_le t hH0
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hkt0 : (0 : ℝ) ≤ (k : ℝ) * t := mul_nonneg hkr.le ht0
  have hkt1 : (k : ℝ) * t ≤ (k : ℝ) := by
    have hx := mul_le_mul_of_nonneg_left ht1 hkr.le
    linarith
  have hab1 := (abs_le.mp habs).1
  have hab2 := (abs_le.mp habs).2
  have hj0 : (0 : ℤ) ≤ j := by
    by_contra hc
    have h1 : (j : ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
    linarith
  have hjk : j ≤ k := by
    by_contra hc
    have h1 : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (show k + 1 ≤ j by omega)
    linarith
  obtain ⟨kN, hkN⟩ : ∃ kN : ℕ, (kN : ℤ) = k := ⟨k.toNat, Int.toNat_of_nonneg hk0.le⟩
  obtain ⟨jN, hjN⟩ : ∃ jN : ℕ, (jN : ℤ) = j := ⟨j.toNat, Int.toNat_of_nonneg hj0⟩
  subst hkN
  subst hjN
  have hkN0 : 0 < kN := by exact_mod_cast hk0
  have hjkN : jN ≤ kN := by exact_mod_cast hjk
  have hkNH : kN ≤ n / Q := by exact_mod_cast hkH
  have hkey : |((kN : ℕ) : ℝ) * t - ((jN : ℕ) : ℝ)| ≤ 1 / (((n / Q : ℕ) : ℝ) + 1) := by
    push_cast at habs
    exact habs
  have hd0 : 0 < Nat.gcd jN kN := Nat.gcd_pos_of_pos_right jN hkN0
  have hdle : Nat.gcd jN kN ≤ kN := Nat.gcd_le_right jN hkN0
  have hcop : Nat.Coprime (jN / Nat.gcd jN kN) (kN / Nat.gcd jN kN) :=
    Nat.coprime_div_gcd_div_gcd hd0
  have haq : jN / Nat.gcd jN kN ≤ kN / Nat.gcd jN kN :=
    Nat.div_le_div_right (c := Nat.gcd jN kN) hjkN
  have hqpos : 0 < kN / Nat.gcd jN kN := Nat.div_pos hdle hd0
  have hqle : kN / Nat.gcd jN kN ≤ kN := Nat.div_le_self _ _
  have hqd : kN / Nat.gcd jN kN * Nat.gcd jN kN = kN :=
    Nat.div_mul_cancel (Nat.gcd_dvd_right jN kN)
  have had : jN / Nat.gcd jN kN * Nat.gcd jN kN = jN :=
    Nat.div_mul_cancel (Nat.gcd_dvd_left jN kN)
  have hqp : (0 : ℝ) < ((kN / Nat.gcd jN kN : ℕ) : ℝ) := by exact_mod_cast hqpos
  have hnp : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast hn0
  have hqne : ((kN / Nat.gcd jN kN : ℕ) : ℝ) ≠ 0 := ne_of_gt hqp
  have hmul : ((jN / Nat.gcd jN kN : ℕ) : ℝ) / ((kN / Nat.gcd jN kN : ℕ) : ℝ) * ((kN : ℕ) : ℝ)
      = ((jN : ℕ) : ℝ) := by
    have e1 : ((jN / Nat.gcd jN kN : ℕ) : ℝ) * ((Nat.gcd jN kN : ℕ) : ℝ) = ((jN : ℕ) : ℝ) := by
      rw [← Nat.cast_mul, had]
    have e2 : ((kN / Nat.gcd jN kN : ℕ) : ℝ) * ((Nat.gcd jN kN : ℕ) : ℝ) = ((kN : ℕ) : ℝ) := by
      rw [← Nat.cast_mul, hqd]
    calc ((jN / Nat.gcd jN kN : ℕ) : ℝ) / ((kN / Nat.gcd jN kN : ℕ) : ℝ) * ((kN : ℕ) : ℝ)
        = ((jN / Nat.gcd jN kN : ℕ) : ℝ) / ((kN / Nat.gcd jN kN : ℕ) : ℝ) *
            (((kN / Nat.gcd jN kN : ℕ) : ℝ) * ((Nat.gcd jN kN : ℕ) : ℝ)) := by rw [← e2]
      _ = ((jN / Nat.gcd jN kN : ℕ) : ℝ) * ((Nat.gcd jN kN : ℕ) : ℝ) := by
          rw [← mul_assoc, div_mul_cancel₀ _ hqne]
      _ = ((jN : ℕ) : ℝ) := e1
  have hkNr : (0 : ℝ) < ((kN : ℕ) : ℝ) := by exact_mod_cast hkN0
  have hbound : |t - ((jN / Nat.gcd jN kN : ℕ) : ℝ) / ((kN / Nat.gcd jN kN : ℕ) : ℝ)| ≤
      1 / (((kN / Nat.gcd jN kN : ℕ) : ℝ) * (((n / Q : ℕ) : ℝ) + 1)) := by
    have h1 : |t - ((jN / Nat.gcd jN kN : ℕ) : ℝ) / ((kN / Nat.gcd jN kN : ℕ) : ℝ)| *
        ((kN : ℕ) : ℝ) = |((kN : ℕ) : ℝ) * t - ((jN : ℕ) : ℝ)| := by
      calc |t - ((jN / Nat.gcd jN kN : ℕ) : ℝ) / ((kN / Nat.gcd jN kN : ℕ) : ℝ)| *
              ((kN : ℕ) : ℝ)
          = |(t - ((jN / Nat.gcd jN kN : ℕ) : ℝ) / ((kN / Nat.gcd jN kN : ℕ) : ℝ)) *
              ((kN : ℕ) : ℝ)| := by rw [abs_mul, abs_of_pos hkNr]
        _ = |((kN : ℕ) : ℝ) * t - ((jN : ℕ) : ℝ)| := by
            have hz : (t - ((jN / Nat.gcd jN kN : ℕ) : ℝ) / ((kN / Nat.gcd jN kN : ℕ) : ℝ)) *
                ((kN : ℕ) : ℝ) = ((kN : ℕ) : ℝ) * t - ((jN : ℕ) : ℝ) := by
              have hw : (t - ((jN / Nat.gcd jN kN : ℕ) : ℝ) /
                  ((kN / Nat.gcd jN kN : ℕ) : ℝ)) * ((kN : ℕ) : ℝ) =
                  t * ((kN : ℕ) : ℝ) - (((jN / Nat.gcd jN kN : ℕ) : ℝ) /
                    ((kN / Nat.gcd jN kN : ℕ) : ℝ)) * ((kN : ℕ) : ℝ) := by ring
              rw [hw, hmul]
              ring
            rw [hz]
    have h2 : |t - ((jN / Nat.gcd jN kN : ℕ) : ℝ) / ((kN / Nat.gcd jN kN : ℕ) : ℝ)| *
        ((kN : ℕ) : ℝ) ≤ 1 / (((n / Q : ℕ) : ℝ) + 1) := by rw [h1]; exact hkey
    calc |t - ((jN / Nat.gcd jN kN : ℕ) : ℝ) / ((kN / Nat.gcd jN kN : ℕ) : ℝ)|
        = (|t - ((jN / Nat.gcd jN kN : ℕ) : ℝ) / ((kN / Nat.gcd jN kN : ℕ) : ℝ)| *
            ((kN : ℕ) : ℝ)) / ((kN : ℕ) : ℝ) := by
          rw [mul_div_cancel_right₀ _ (ne_of_gt hkNr)]
      _ ≤ (1 / (((n / Q : ℕ) : ℝ) + 1)) / ((kN : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right h2 hkNr.le
      _ = 1 / ((((n / Q : ℕ) : ℝ) + 1) * ((kN : ℕ) : ℝ)) := by rw [div_div]
      _ = 1 / (((kN : ℕ) : ℝ) * (((n / Q : ℕ) : ℝ) + 1)) := by
          congr 1
          ring
      _ ≤ 1 / (((kN / Nat.gcd jN kN : ℕ) : ℝ) * (((n / Q : ℕ) : ℝ) + 1)) :=
          one_div_le_one_div_of_le (mul_pos hqp (by positivity))
            (mul_le_mul_of_nonneg_right (by exact_mod_cast hqle) (by positivity))
  have harcd : Q < kN / Nat.gcd jN kN := by
    by_contra hc
    have hc' : kN / Nat.gcd jN kN ≤ Q := by omega
    apply hmem
    refine ⟨kN / Nat.gcd jN kN, jN / Nat.gcd jN kN, by omega, hc', haq, hcop, ?_⟩
    have hQHr : ((n : ℕ) : ℝ) ≤ ((Q : ℕ) : ℝ) * (((n / Q : ℕ) : ℝ) + 1) := by
      have h1 : ((n : ℕ) : ℝ) ≤ ((Q * (n / Q + 1) : ℕ) : ℝ) := by exact_mod_cast hQH
      have h2 : ((Q * (n / Q + 1) : ℕ) : ℝ) = ((Q : ℕ) : ℝ) * (((n / Q : ℕ) : ℝ) + 1) := by
        push_cast
        ring
      linarith
    have hstep : (1 : ℝ) / (((kN / Nat.gcd jN kN : ℕ) : ℝ) * (((n / Q : ℕ) : ℝ) + 1))
        ≤ ((Q : ℕ) : ℝ) / (((kN / Nat.gcd jN kN : ℕ) : ℝ) * ((n : ℕ) : ℝ)) := by
      rw [div_le_div_iff₀ (mul_pos hqp (by positivity)) (mul_pos hqp hnp)]
      calc (1 : ℝ) * (((kN / Nat.gcd jN kN : ℕ) : ℝ) * ((n : ℕ) : ℝ))
          = ((kN / Nat.gcd jN kN : ℕ) : ℝ) * ((n : ℕ) : ℝ) := by ring
        _ ≤ ((kN / Nat.gcd jN kN : ℕ) : ℝ) * (((Q : ℕ) : ℝ) * (((n / Q : ℕ) : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hQHr hqp.le
        _ = ((Q : ℕ) : ℝ) * (((kN / Nat.gcd jN kN : ℕ) : ℝ) * (((n / Q : ℕ) : ℝ) + 1)) := by
            ring
    exact hbound.trans hstep
  exact ⟨kN / Nat.gcd jN kN, jN / Nat.gcd jN kN, harcd, le_trans hqle hkNH, haq, hcop, hbound⟩

theorem Conjectures.Goldbach.DirichletMinorApproximation :
    let Q (n : ℕ) := (Nat.log 2 (n + 2)) ^ 2; let arcs (n : ℕ) := {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / q| ≤ (Q n : ℝ) / ((q : ℝ) * n)}; ∀ (n : ℕ) (t : ℝ), 1 ≤ Q n → Q n ≤ n → t ∈ Set.Icc (0 : ℝ) 1 → t ∉ arcs n → ∃ q a : ℕ, Q n < q ∧ q ≤ n / Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * (((n / Q n : ℕ) : ℝ) + 1)) := by
  dsimp only
  intro n t hQ1 hQn ht hmem
  exact keyA _ n t hQ1 hQn ht.1 ht.2 hmem
