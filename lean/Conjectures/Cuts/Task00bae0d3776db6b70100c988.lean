import Mathlib

theorem Conjectures.Cuts.Task00bae0d3776db6b70100c988 :
    (∀ (x1 x2 : ℕ), (0 : ℕ) < x1 → (0 : ℕ) < x2 → x1 ∣ x2 → (∀ (x6 : ℕ), x6 ^ (2 : ℕ) ∣ x1 → x6 ^ (30 : ℕ) ≤ x1 ^ (7 : ℕ)) → Real.log ↑x1 ≤ (15 / 8 : ℝ) * Real.log ↑(x2.primeFactors.prod id)) := by
  classical
  intro n N hn hN hd hsmall
  obtain ⟨s,t,hs,ht,hst,hsf⟩ := Nat.sq_mul_squarefree_of_pos hn
  let r := N.primeFactors.prod id
  have htD : t^2 ∣ n := ⟨s,hst.symm⟩
  have hsD : s ∣ N :=
    dvd_trans (show s ∣ n from ⟨t^2,by rw [← hst,mul_comm]⟩) hd
  have hr : 0<r := Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  have hsRad : s ≤ r := by
    apply Nat.le_of_dvd hr
    have hsub : s.primeFactors ⊆ N.primeFactors := Nat.primeFactors_mono hsD hN.ne'
    have := Finset.prod_dvd_prod_of_subset s.primeFactors N.primeFactors id hsub
    rw [show s.primeFactors.prod id = s from Nat.prod_primeFactors_of_squarefree hsf] at this
    exact this
  have hPower : n^8 ≤ r^15 := by
    apply Nat.le_of_mul_le_mul_left _ (pow_pos hn 7)
    calc
      n^7 * n^8 = n^15 := by ring
      _ = t^30 * s^15 := by rw [← hst]; ring
      _ ≤ n^7 * r^15 := Nat.mul_le_mul (hsmall t htD) (Nat.pow_le_pow_left hsRad _)
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hPR : (n:ℝ)^8 ≤ (r:ℝ)^15 := by exact_mod_cast hPower
  have hL := Real.log_le_log (by positivity : (0:ℝ)<(n:ℝ)^8) hPR
  simp only [Real.log_pow,Nat.cast_ofNat] at hL
  change Real.log (n:ℝ) ≤ (15/8 : ℝ)*Real.log (r:ℝ)
  linarith only [hL]
