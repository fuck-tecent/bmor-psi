import Mathlib

theorem Conjectures.Goldbach.TwistedCutoffResidual :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (c : ℝ) (s : ℂ), 1 ≤ c → 1 < s.re → let w : ℕ → ℂ := fun n => if 1 ≤ n ∧ (n : ℝ) < c then ((Real.log c - Real.log (n : ℝ) : ℝ) : ℂ) else 0; let r : ℕ → ℂ := (Real.log c : ℂ) • LSeries.delta - LSeries.convolution (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) w; LSeries (fun n : ℕ => χ (n : ZMod N) * r n) s = (Real.log c : ℂ) - LSeries (fun n : ℕ => χ (n : ZMod N) * w n) s / χ.LFunction s := by
  intro N _ χ c s hc hs w r
  have hfin : ∀ (f : ℕ → ℂ) (m : ℕ), (∀ n : ℕ, m ≤ n → f n = 0) → LSeriesSummable f s := by
    intro f m hf
    refine summable_of_ne_finset_zero (s := Finset.range m) fun n hn => ?_
    have : m ≤ n := by simpa using hn
    simp [LSeries.term, hf n this]
  have hw : LSeriesSummable w s := by
    obtain ⟨m, hm⟩ := exists_nat_ge c
    refine hfin _ m fun n hn => ?_
    have : c ≤ (n : ℝ) := hm.trans (by exact_mod_cast hn)
    simp only [w]
    rw [ite_eq_right_iff]
    rintro ⟨_, h⟩
    exact absurd this (not_le.mpr h)
  have hδ : LSeriesSummable LSeries.delta s := hfin _ 2 fun n hn => by
    have : n ≠ 1 := by omega
    simp [LSeries.delta, this]
  have hμ : LSeriesSummable (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have hχw : LSeriesSummable (fun n : ℕ => χ (n : ZMod N) * w n) s :=
    DirichletCharacter.LSeriesSummable_mul χ hw
  have hm : LSeriesSummable (fun n : ℕ => χ (n : ZMod N) * (ArithmeticFunction.moebius n : ℂ)) s :=
    DirichletCharacter.LSeriesSummable_mul χ hμ
  have hconv : (fun n : ℕ => χ (n : ZMod N) * r n)
      = (Real.log c : ℂ) • LSeries.delta
        - LSeries.convolution (fun n : ℕ => χ (n : ZMod N) * (ArithmeticFunction.moebius n : ℂ))
            (fun n : ℕ => χ (n : ZMod N) * w n) := by
    have h1 := DirichletCharacter.mul_convolution_distrib χ
      (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) w
    have h2 := DirichletCharacter.mul_delta χ
    ext n
    have h1n := congrFun h1 n
    have h2n := congrFun h2 n
    simp only [Pi.mul_apply] at h1n h2n
    simp only [r, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_sub, ← h1n]
    congr 1
    rw [mul_left_comm, h2n]
  rw [hconv, LSeries_sub (hδ.smul _) (hm.convolution hχw), LSeries_smul, LSeries_delta,
    LSeries_convolution' hm hχw]
  have hL := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hne := DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hs
  rw [χ.LFunction_eq_LSeries hs]
  have : LSeries (fun n : ℕ => χ (n : ZMod N) * (ArithmeticFunction.moebius n : ℂ)) s
      = (LSeries (fun n : ℕ => χ (n : ZMod N)) s)⁻¹ := by
    exact eq_inv_of_mul_eq_one_right hL
  rw [this]
  simp [div_eq_mul_inv, mul_comm]
