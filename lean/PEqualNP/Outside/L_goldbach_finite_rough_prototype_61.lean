import Mathlib

private theorem residueWitness : ∀ residue : Fin 105, ∃ prime : Fin 20,
    Nat.Prime prime.val ∧ Nat.Coprime ((2 * residue.val + 210 - prime.val) % 210) 210 := by
  decide

private theorem roughWitness :
    ∀ n : ℕ, 22 ≤ n → Even n → ∃ p : ℕ, Nat.Prime p ∧ p < n ∧ 2 ≤ n-p ∧ Nat.Coprime (n-p) 210 := by
  rintro n lower ⟨half, rfl⟩
  obtain ⟨prime, primeIsPrime, coprimeResidue⟩ := residueWitness ⟨half % 105, Nat.mod_lt _ (by decide)⟩
  have bound := prime.isLt
  refine ⟨prime.val, primeIsPrime, by omega, by omega, ?_⟩
  change Nat.Coprime ((2 * (half % 105) + 210 - prime.val) % 210) 210 at coprimeResidue
  have residueEq : (half + half - prime.val) % 210 = (2 * (half % 105) + 210 - prime.val) % 210 := by omega
  change Nat.gcd (half + half - prime.val) 210 = 1
  rwa [Nat.gcd_comm, Nat.gcd_rec, residueEq]


private theorem power_le_product (b : ℕ) (l : List ℕ) (h : ∀ a ∈ l, b ≤ a) : b^l.length ≤ l.prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, List.prod_cons, pow_succ']
    exact Nat.mul_le_mul (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

private theorem factors_bound {m : ℕ} (hm : 2 ≤ m) (hc : m.Coprime 210) :
    11^m.primeFactorsList.length ≤ m := by
  calc
    _ ≤ m.primeFactorsList.prod := power_le_product 11 _ (by
      intro p hp
      by_contra! h
      have small : ∀ i : Fin 11, Nat.Prime i.val → i.val ∣ 210 := by decide
      have prime := Nat.prime_of_mem_primeFactorsList hp
      have both := Nat.dvd_gcd (Nat.dvd_of_mem_primeFactorsList hp) (small ⟨p,h⟩ prime)
      exact prime.not_dvd_one (hc.gcd_eq_one ▸ both))
    _ = m := Nat.prod_primeFactorsList (by omega)

set_option maxRecDepth 4096 in
private theorem size_bound : Real.exp (Real.exp 5) < (11:ℝ)^62 := by
  have he : Real.exp 1 < (2.7183 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num)
  have hfive : Real.exp 5 < (297/2 : ℝ) := calc
    _ = (Real.exp 1)^5 := by simp
    _ ≤ (2.7183 : ℝ)^5 := pow_le_pow_left₀ (Real.exp_pos _).le he.le _
    _ < _ := by norm_num
  have hs : Real.exp (Real.exp 5)^2 < ((11:ℝ)^62)^2 := calc
    _ = Real.exp (2 * Real.exp 5) := by rw [← Real.exp_nat_mul]; norm_num
    _ < Real.exp 297 := Real.exp_lt_exp.mpr (by linarith only [hfive])
    _ = (Real.exp 1)^297 := by simp
    _ ≤ (2.7183 : ℝ)^297 := pow_le_pow_left₀ (Real.exp_pos _).le he.le _
    _ < _ := by rw [show 297 = 99*3 by decide, pow_mul]; norm_num
  exact lt_of_not_ge (fun h => (not_le_of_gt hs) (pow_le_pow_left₀ (by positivity) h 2))

set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.L_goldbach_finite_rough_prototype_61 :
    ∀ n : ℕ, 4 ≤ n → Even n → (n:ℝ) < Real.exp (Real.exp 5) → ∃ p : ℕ, Nat.Prime p ∧ 2 ≤ n-p ∧ (n-p).primeFactorsList.length ≤ 61 := by
  intro n hn heven hsize
  by_cases large : 22 ≤ n
  · obtain ⟨p, hprime, _, hm, hc⟩ := roughWitness n large heven
    refine ⟨p, hprime, hm, ?_⟩
    by_contra! h
    have hpow : 11^62 ≤ n := (Nat.pow_le_pow_right (by decide) (by omega : 62 ≤ (n-p).primeFactorsList.length)).trans
      ((factors_bound hm hc).trans (Nat.sub_le n p))
    have hh : (11:ℝ)^62 ≤ n := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using (Nat.cast_le.mpr hpow : ((11^62 : ℕ) : ℝ) ≤ n)
    exact (not_le_of_gt (hsize.trans size_bound)) hh
  · refine ⟨2, by decide, by omega, ?_⟩
    have hp := power_le_product 2 (n-2).primeFactorsList (fun _ h => (Nat.prime_of_mem_primeFactorsList h).two_le)
    rw [Nat.prod_primeFactorsList (by omega)] at hp
    by_contra! h
    have hh := (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 5 ≤ (n-2).primeFactorsList.length)).trans hp
    omega
