import Mathlib

private lemma ptb_harm (X : ℕ) :
    (∑ m ∈ Finset.Icc 1 X, (1 / (m : ℝ))) ≤ 1 + Real.log (X : ℝ) := by
  have h := harmonic_le_one_add_log X
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa using h

private lemma ptb_factor (p : ℕ) (hp : 2 ≤ p) :
    ((1 - (p : ℝ)⁻¹)⁻¹) ^ 2 ≤ 1 + 6 / (p : ℝ) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have e : (1 - (p : ℝ)⁻¹) = ((p : ℝ) - 1) / p := by field_simp
  rw [e, inv_div, div_pow, div_le_iff₀ (by nlinarith)]
  have : (1 + 6 / (p : ℝ)) = ((p : ℝ) + 6) / p := by field_simp
  rw [this, div_mul_eq_mul_div, le_div_iff₀ hp0]
  nlinarith [sq_nonneg ((p : ℝ) - 2), mul_pos hp0 hp0]

private lemma ptb_euler (q : ℕ) (hq : 0 < q) :
    (q : ℝ) / ((q.totient : ℝ)) ^ 2 ≤ (1 / (q : ℝ)) * ∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ)) := by
  have ht : (q.totient : ℝ) = q * ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have := Nat.totient_eq_mul_prod_factors q
    have h2 := congrArg (fun x : ℚ => (x : ℝ)) this
    push_cast at h2
    exact h2
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hpos : ∀ p ∈ q.primeFactors, (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) h2
    linarith
  have hP : (0 : ℝ) < ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) := Finset.prod_pos hpos
  have e : (q : ℝ) / ((q.totient : ℝ)) ^ 2
      = (1 / (q : ℝ)) * ∏ p ∈ q.primeFactors, ((1 - (p : ℝ)⁻¹)⁻¹) ^ 2 := by
    rw [ht, Finset.prod_pow, Finset.prod_inv_distrib]
    field_simp
  rw [e]
  have hq1 : (0 : ℝ) ≤ 1 / (q : ℝ) := by positivity
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun p hp => by have := hpos p hp; positivity) (fun p hp => ptb_factor p (Nat.prime_of_mem_primeFactors hp).two_le)) hq1

private lemma ptb_mult (X D : ℕ) (hD : 0 < D) (w : ℝ) (hw : 0 ≤ w) :
    (∑ q ∈ (Finset.Icc 1 X).filter (fun q => D ∣ q), w * (1 / (q : ℝ)))
      ≤ w / D * (1 + Real.log (X : ℝ)) := by
  have hsub : (Finset.Icc 1 X).filter (fun q => D ∣ q) ⊆ (Finset.Icc 1 X).image (fun m => D * m) := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨h1, h2⟩, m, rfl⟩ := hq
    simp only [Finset.mem_image, Finset.mem_Icc]
    refine ⟨m, ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp at h1
      · exact h
    · nlinarith
  calc (∑ q ∈ (Finset.Icc 1 X).filter (fun q => D ∣ q), w * (1 / (q : ℝ)))
      ≤ ∑ q ∈ (Finset.Icc 1 X).image (fun m => D * m), w * (1 / (q : ℝ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro i _ _; positivity
    _ = ∑ m ∈ Finset.Icc 1 X, w * (1 / ((D * m : ℕ) : ℝ)) := by
        rw [Finset.sum_image]
        intro a _ b _ h
        exact Nat.eq_of_mul_eq_mul_left hD h
    _ = w / D * ∑ m ∈ Finset.Icc 1 X, (1 / (m : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        push_cast
        field_simp
    _ ≤ w / D * (1 + Real.log (X : ℝ)) := by
        apply mul_le_mul_of_nonneg_left (ptb_harm X)
        have : (0 : ℝ) < D := by exact_mod_cast hD
        positivity

private lemma ptb_primes_sq (X : ℕ) :
    ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, (6 / ((p : ℝ)) ^ 2) ≤ 6 := by
  have h := sum_Ioo_inv_sq_le (α := ℝ) 1 (X + 1)
  have hsub : (Finset.Icc 1 X).filter Nat.Prime ⊆ Finset.Ioo 1 (X + 1) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    simp only [Finset.mem_Ioo]
    have := hp.2.two_le
    omega
  calc ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, (6 / ((p : ℝ)) ^ 2)
      = 6 * ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, (((p : ℝ)) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; rw [div_eq_mul_inv]
    _ ≤ 6 * ∑ p ∈ Finset.Ioo 1 (X + 1), (((p : ℝ)) ^ 2)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intros; positivity
    _ ≤ 6 * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        norm_num at h
        linarith
    _ = 6 := by ring

theorem Conjectures.Goldbach.PacketTotientHarmonicBudget :
    ∀ X : ℕ, (∑ q ∈ Finset.Icc 1 X, (q : ℝ) / (q.totient : ℝ)^2) ≤ Real.exp (Real.pi^2) * (1 + Real.log (X : ℝ)) := by
  intro X
  classical
  set P : Finset ℕ := (Finset.Icc 1 X).filter Nat.Prime with hPdef
  set w : Finset ℕ → ℝ := fun s => ∏ p ∈ s, (6 / (p : ℝ)) with hw
  have hPf : ∀ q ∈ Finset.Icc 1 X, q.primeFactors ⊆ P := by
    intro q hq p hp
    have hq' := Finset.mem_Icc.mp hq
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hd := Nat.dvd_of_mem_primeFactors hp
    simp only [hPdef, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hpp.one_le, le_trans (Nat.le_of_dvd (by omega) hd) hq'.2⟩, hpp⟩
  have step1 : ∀ q ∈ Finset.Icc 1 X, (q : ℝ) / (q.totient : ℝ)^2
      ≤ ∑ s ∈ P.powerset, (1 / (q : ℝ)) * (if s ⊆ q.primeFactors then w s else 0) := by
    intro q hq
    have hq' := Finset.mem_Icc.mp hq
    refine (ptb_euler q (by omega)).trans ?_
    rw [Finset.prod_one_add]
    rw [← Finset.mul_sum]
    apply le_of_eq
    congr 1
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext s
      simp only [Finset.mem_powerset, Finset.mem_filter]
      constructor
      · intro h; exact ⟨h.trans (hPf q hq), h⟩
      · intro h; exact h.2
    · intros; rfl
  have step2 : ∀ s ∈ P.powerset,
      (∑ q ∈ Finset.Icc 1 X, (1 / (q : ℝ)) * (if s ⊆ q.primeFactors then w s else 0))
        ≤ (∏ p ∈ s, (6 / ((p : ℝ)) ^ 2)) * (1 + Real.log (X : ℝ)) := by
    intro s hs
    have hsP : ∀ p ∈ s, p.Prime := by
      intro p hp
      have := Finset.mem_powerset.mp hs hp
      simp only [hPdef, Finset.mem_filter] at this
      exact this.2
    have hsX : ∀ p ∈ s, 1 ≤ p := fun p hp => (hsP p hp).one_le
    have hD : 0 < ∏ p ∈ s, p := Finset.prod_pos (fun p hp => (hsP p hp).pos)
    have hw0 : 0 ≤ w s := Finset.prod_nonneg (fun p _ => by positivity)
    have hval : w s / ((∏ p ∈ s, p : ℕ) : ℝ) = ∏ p ∈ s, (6 / ((p : ℝ)) ^ 2) := by
      rw [hw]; simp only
      push_cast
      rw [← Finset.prod_div_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      have : (0 : ℝ) < p := by exact_mod_cast (hsP p hp).pos
      field_simp
    rw [← hval]
    refine le_trans ?_ (ptb_mult X _ hD (w s) hw0)
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 X) (fun q => ∏ p ∈ s, p ∣ q)]
    have h0 : (∑ q ∈ (Finset.Icc 1 X).filter (fun q => ¬ ∏ p ∈ s, p ∣ q),
        (1 / (q : ℝ)) * (if s ⊆ q.primeFactors then w s else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      have hq' := Finset.mem_filter.mp hq
      rw [if_neg]; · simp
      intro hsub
      apply hq'.2
      have hq1 := (Finset.mem_Icc.mp hq'.1).1
      apply Finset.prod_primes_dvd q (fun p hp => (hsP p hp).prime)
      intro p hp
      exact Nat.dvd_of_mem_primeFactors (hsub hp)
    rw [h0, add_zero]
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hq1 := (Finset.mem_Icc.mp hq'.1).1
    rw [if_pos]
    · ring
    · intro p hp
      rw [Nat.mem_primeFactors]
      refine ⟨hsP p hp, ?_, by omega⟩
      exact (Finset.dvd_prod_of_mem _ hp).trans hq'.2
  have hprod : ∑ s ∈ P.powerset, ∏ p ∈ s, (6 / ((p : ℝ)) ^ 2) ≤ Real.exp 6 := by
    rw [← Finset.prod_one_add]
    refine (Real.prod_one_add_le_exp_sum P (fun i => by positivity)).trans ?_
    exact Real.exp_le_exp.mpr (ptb_primes_sq X)
  have hexp : Real.exp 6 ≤ Real.exp (Real.pi ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_gt_three]
  have hH : 0 ≤ 1 + Real.log (X : ℝ) := by
    have := ptb_harm X
    refine le_trans (Finset.sum_nonneg (fun m _ => by positivity)) this
  calc (∑ q ∈ Finset.Icc 1 X, (q : ℝ) / (q.totient : ℝ)^2)
      ≤ ∑ q ∈ Finset.Icc 1 X, ∑ s ∈ P.powerset, (1 / (q : ℝ)) * (if s ⊆ q.primeFactors then w s else 0) :=
        Finset.sum_le_sum step1
    _ = ∑ s ∈ P.powerset, ∑ q ∈ Finset.Icc 1 X, (1 / (q : ℝ)) * (if s ⊆ q.primeFactors then w s else 0) :=
        Finset.sum_comm
    _ ≤ ∑ s ∈ P.powerset, (∏ p ∈ s, (6 / ((p : ℝ)) ^ 2)) * (1 + Real.log (X : ℝ)) :=
        Finset.sum_le_sum step2
    _ = (∑ s ∈ P.powerset, ∏ p ∈ s, (6 / ((p : ℝ)) ^ 2)) * (1 + Real.log (X : ℝ)) := by
        rw [Finset.sum_mul]
    _ ≤ Real.exp (Real.pi ^ 2) * (1 + Real.log (X : ℝ)) :=
        mul_le_mul_of_nonneg_right (hprod.trans hexp) hH
