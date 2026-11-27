import Mathlib

private theorem goldbach_shell_kernel (a H k : ℕ) (hHk : H ≤ k) :
    1 / ((k : ℝ) + 1) ^ (a + 3) ≤
      (2 / ((H : ℝ) + 1) ^ (a + 1)) *
        (1 / ((k : ℝ) + 1) - 1 / (((k : ℝ) + 1) + 1)) := by
  let x : ℝ := (k : ℝ) + 1
  let y : ℝ := (H : ℝ) + 1
  change 1 / x ^ (a + 3) ≤ (2 / y ^ (a + 1)) * (1 / x - 1 / (x + 1))
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
    linarith only [hk]
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hy : 0 < y := by dsimp [y]; positivity
  have hxy : y ≤ x := by dsimp [x, y]; exact_mod_cast (show H + 1 ≤ k + 1 by omega)
  have hweight : 1 / x ^ (a + 1) ≤ 1 / y ^ (a + 1) := by
    apply (div_le_div_iff₀ (pow_pos hx _) (pow_pos hy _)).2
    simpa using pow_le_pow_left₀ hy.le hxy (a + 1)
  have hxnext : 0 < x + 1 := by positivity
  have hdiff : 1 / x - 1 / (x + 1) = 1 / (x * (x + 1)) := by
    field_simp [hx.ne', hxnext.ne'] <;> ring
  have hquadratic : 1 / x ^ 2 ≤ 2 * (1 / x - 1 / (x + 1)) := by
    rw [hdiff]
    have h : 1 / x ^ 2 ≤ 2 / (x * (x + 1)) := by
      apply (div_le_div_iff₀ (pow_pos hx _) (mul_pos hx hxnext)).2
      nlinarith only [mul_nonneg hx.le (sub_nonneg.mpr hx1)]
    simpa [div_eq_mul_inv] using h
  calc
    1 / x ^ (a + 3) = (1 / x ^ (a + 1)) * (1 / x ^ 2) := by
      rw [show a + 3 = (a + 1) + 2 by omega, pow_add]
      field_simp [hx.ne'] <;> ring
    _ ≤ (1 / y ^ (a + 1)) * (2 * (1 / x - 1 / (x + 1))) :=
      mul_le_mul hweight hquadratic (by positivity) (by positivity)
    _ = _ := by ring

private theorem goldbach_shell_log (d H k : ℕ) (hd : 1 ≤ d) :
    Real.log ((d * (k + 2) : ℕ) : ℝ) ≤
      ((k : ℝ) + 1) * Real.log ((d * (H + 2) : ℕ) : ℝ) := by
  let b := d * (H + 2)
  have hb : 2 ≤ b := by
    simpa [b] using Nat.mul_le_mul hd (show 2 ≤ H + 2 by omega)
  have hp (j : ℕ) : d * (j + 2) ≤ b ^ (j + 1) := by
    induction j with
    | zero =>
      simp only [Nat.zero_add, pow_one]
      dsimp [b]
      exact Nat.mul_le_mul_left d (by omega)
    | succ j ih =>
      calc
        d * (j + 1 + 2) ≤ d * ((j + 2) * 2) := Nat.mul_le_mul_left d (by omega)
        _ = (d * (j + 2)) * 2 := by ring
        _ ≤ b ^ (j + 1) * b := Nat.mul_le_mul ih hb
        _ = b ^ (j + 1 + 1) := (pow_succ b (j + 1)).symm
  have hpow : ((d * (k + 2) : ℕ) : ℝ) ≤ (b : ℝ) ^ (k + 1) := by exact_mod_cast hp k
  have hprod : 0 < d * (k + 2) := Nat.mul_pos (by omega) (by omega)
  have hlog := Real.log_le_log (show (0 : ℝ) < ((d * (k + 2) : ℕ) : ℝ) by exact_mod_cast hprod) hpow
  simpa [Real.log_pow, b] using hlog

private theorem shell_mass (a m k d : ℕ) (γ : Fin m → ℝ) (W : ℝ → ℂ)
    (K L : ℝ) (hK : 0 ≤ K) (hw : ∀ t, ‖W t‖ ≤ K / (1 + |t|) ^ (a + 4))
    (hZ : ((Finset.univ.filter (fun j => (k : ℝ) ≤ |γ j| ∧
      |γ j| < (k + 1 : ℕ))).card : ℝ) ≤ L * Real.log ((d * (k + 2) : ℕ) : ℝ)) :
    (∑ j ∈ Finset.univ.filter (fun j => (k : ℝ) ≤ |γ j| ∧ |γ j| < (k + 1 : ℕ)),
      ‖W (γ j)‖) ≤ L * Real.log ((d * (k + 2) : ℕ) : ℝ) *
        (K / ((k : ℝ) + 1) ^ (a + 4)) := by
  let S := Finset.univ.filter (fun j => (k : ℝ) ≤ |γ j| ∧ |γ j| < (k + 1 : ℕ))
  change (∑ j ∈ S, ‖W (γ j)‖) ≤ _
  have hk : 0 < (k : ℝ) + 1 := by positivity
  calc
    _ ≤ ∑ _j ∈ S, K / ((k : ℝ) + 1) ^ (a + 4) := by
      apply Finset.sum_le_sum
      intro j hj
      have hkj : (k : ℝ) ≤ |γ j| := (Finset.mem_filter.mp hj).2.1
      apply (hw (γ j)).trans
      exact div_le_div_of_nonneg_left hK (pow_pos hk _) <|
        pow_le_pow_left₀ hk.le (by linarith) _
    _ = (S.card : ℝ) * (K / ((k : ℝ) + 1) ^ (a + 4)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hZ (div_nonneg hK (pow_nonneg hk.le _))

private theorem shell_estimate (a m k d H : ℕ) (γ : Fin m → ℝ) (W : ℝ → ℂ)
    (K L : ℝ) (hK : 0 ≤ K) (hw : ∀ t, ‖W t‖ ≤ K / (1 + |t|) ^ (a + 4))
    (hZ : ((Finset.univ.filter (fun j => (k : ℝ) ≤ |γ j| ∧
      |γ j| < (k + 1 : ℕ))).card : ℝ) ≤ L * Real.log ((d * (k + 2) : ℕ) : ℝ))
    (hL : 0 ≤ L) (hD : 0 ≤ Real.log ((d * (H + 2) : ℕ) : ℝ))
    (hlog : Real.log ((d * (k + 2) : ℕ) : ℝ) ≤
      ((k : ℝ) + 1) * Real.log ((d * (H + 2) : ℕ) : ℝ))
    (hkernel : 1 / ((k : ℝ) + 1) ^ (a + 3) ≤
      (2 / ((H : ℝ) + 1) ^ (a + 1)) *
        (1 / ((k : ℝ) + 1) - 1 / (((k : ℝ) + 1) + 1))) :
    (∑ j ∈ Finset.univ.filter (fun j => (k : ℝ) ≤ |γ j| ∧ |γ j| < (k + 1 : ℕ)),
      ‖W (γ j)‖) ≤ (2 * K * L * Real.log ((d * (H + 2) : ℕ) : ℝ) /
        ((H : ℝ) + 1) ^ (a + 1)) *
          (1 / ((k : ℝ) + 1) - 1 / (((k : ℝ) + 1) + 1)) := by
  have hk : 0 < (k : ℝ) + 1 := by positivity
  apply (shell_mass a m k d γ W K L hK hw hZ).trans
  calc
    _ ≤ (L * (((k : ℝ) + 1) * Real.log ((d * (H + 2) : ℕ) : ℝ))) *
        (K / ((k : ℝ) + 1) ^ (a + 4)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hL)
        (div_nonneg hK (pow_nonneg hk.le _))
    _ = (K * L * Real.log ((d * (H + 2) : ℕ) : ℝ)) *
        (1 / ((k : ℝ) + 1) ^ (a + 3)) := by
      rw [show a + 4 = (a + 3) + 1 by omega, pow_succ]
      field_simp [hk.ne']
      <;> ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hkernel
      (mul_nonneg (mul_nonneg hK hL) hD)).trans_eq (by
        simp only [div_eq_mul_inv]
        ring)

private theorem sum_shell_tail {m : ℕ} (γ : Fin m → ℝ) (f : Fin m → ℝ)
    (H : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (bound : ∀ k : ℕ, H ≤ k →
      (∑ j ∈ Finset.univ.filter (fun j => (k : ℝ) ≤ |γ j| ∧ |γ j| < (k+1 : ℕ)), f j) ≤
        c * (1 / ((k : ℝ) + 1) - 1 / (((k : ℝ) + 1) + 1))) :
    (∑ j ∈ Finset.univ.filter (fun j => (H : ℝ) ≤ |γ j|), f j) ≤ c * (1 / ((H : ℝ) + 1)) := by
  classical
  let T (k : ℕ) := Finset.univ.filter (fun j => (k : ℝ) ≤ |γ j|)
  let S (k : ℕ) := Finset.univ.filter (fun j => (k : ℝ) ≤ |γ j| ∧ |γ j| < (k+1 : ℕ))
  let u (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  let tail (k : ℕ) := ∑ j ∈ T k, f j
  let shell (k : ℕ) := ∑ j ∈ S k, f j
  have hsplit (k : ℕ) : tail k = shell k + tail (k+1) := by
    have hsucc : (k : ℝ) ≤ ((k+1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
    have heq : T k = S k ∪ T (k+1) := by
      ext j
      simp only [T, S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hj
        by_cases ht : |γ j| < ((k+1 : ℕ) : ℝ)
        · exact Or.inl ⟨hj, ht⟩
        · exact Or.inr (le_of_not_gt ht)
      · rintro (⟨hj, _⟩ | hj)
        · exact hj
        · exact hsucc.trans hj
    have hdis : Disjoint (S k) (T (k+1)) := by
      apply Finset.disjoint_left.mpr
      intro j hj ht
      exact (not_lt_of_ge (Finset.mem_filter.mp ht).2) (Finset.mem_filter.mp hj).2.2
    change (∑ j ∈ T k, f j) = (∑ j ∈ S k, f j) + ∑ j ∈ T (k+1), f j
    rw [heq, Finset.sum_union hdis]
  have hs (k : ℕ) (hk : H ≤ k) : shell k ≤ c * (u k - u (k+1)) := by
    simpa only [shell, S, u, Nat.cast_add, Nat.cast_one] using bound k hk
  have hpartial (t : ℕ) : tail H ≤ c * (u H - u (H+t)) + tail (H+t) := by
    induction t with
    | zero => simp
    | succ t ih =>
      have ht := hs (H+t) (by omega)
      rw [hsplit (H+t)] at ih
      rw [Nat.add_succ]
      linarith only [ih, ht]
  obtain ⟨N, hN⟩ := exists_nat_gt (∑ j : Fin m, |γ j|)
  have hempty : T (H+N) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have hsingle : |γ j| ≤ ∑ i : Fin m, |γ i| :=
      Finset.single_le_sum (fun i _ => abs_nonneg (γ i)) (Finset.mem_univ j)
    have hlarge : ((H+N : ℕ) : ℝ) ≤ |γ j| := (Finset.mem_filter.mp hj).2
    push_cast at hlarge
    have hH : 0 ≤ (H : ℝ) := by positivity
    linarith
  have hz : tail (H+N) = 0 := by simp [tail, hempty]
  have endpoint := hpartial N
  rw [hz, add_zero] at endpoint
  have hu : 0 ≤ u (H+N) := by dsimp [u]; positivity
  change tail H ≤ c * u H
  linarith only [endpoint, mul_nonneg hc hu]

theorem PEqualNP.Outside.L_goldbach_mellin_weight_tail : let Z := fun (m k : ℕ) (γ : Fin m → ℝ) => Finset.univ.filter (fun j => (k:ℝ) ≤ |γ j| ∧ |γ j| < (k+1:ℕ)); ∀ a : ℕ, ∃ C : ℝ, 0<C ∧ ∀ (m d H : ℕ) (γ : Fin m → ℝ) (W : ℝ → ℂ) (K L : ℝ), 1≤d → 0≤K → 0≤L → (∀ t, ‖W t‖ ≤ K/(1+|t|)^(a+4)) → (∀ k, ((Z m k γ).card:ℝ) ≤ L*Real.log ((d*(k+2):ℕ):ℝ)) → (∑ j ∈ Finset.univ.filter (fun i => (H:ℝ) ≤ |γ i|), ‖W (γ j)‖) ≤ C*K*L*Real.log ((d*(H+2):ℕ):ℝ)/((H+1:ℕ):ℝ)^(a+2) := by
  dsimp only
  intro a
  refine ⟨2, by norm_num, ?_⟩
  intro m d H γ W K L hd hK hL hw hZ
  have hbase : 1 ≤ d * (H+2) := by
    simpa using Nat.mul_le_mul hd (show 1 ≤ H+2 by omega)
  have hD : 0 ≤ Real.log ((d*(H+2) : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hbase)
  let c := 2 * K * L * Real.log ((d*(H+2) : ℕ) : ℝ) / ((H : ℝ)+1)^(a+1)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have ht := sum_shell_tail γ (fun j => ‖W (γ j)‖) H c hc (fun k hk =>
    shell_estimate a m k d H γ W K L hK hw (hZ k) hL hD
      (goldbach_shell_log d H k hd) (goldbach_shell_kernel a H k hk))
  apply ht.trans_eq
  dsimp [c]
  push_cast
  rw [show a + 2 = (a + 1) + 1 by omega, pow_succ _ (a+1)]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring
