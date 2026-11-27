import Mathlib

/- The residue and lifting arguments below adapt an independently written 26day
   local proof for L-goldbach-finite-rough-candidate-lift, source SHA-256
   444ac383c4a7d9cc7408ef00af853231a21ed5d824c535374a72215601940323.
   The lifting theorem is private here. -/

private def goodResidue (a p : ℕ) : Prop :=
  Nat.Coprime ((a + 210 - p) % 210) 210

private instance (a p : ℕ) : Decidable (goodResidue a p) :=
  inferInstanceAs (Decidable (Nat.Coprime _ _))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
private theorem evenResidues : ∀ a : Fin 210, a.val % 2 = 0 →
    goodResidue a 3 ∨ goodResidue a 5 ∨ goodResidue a 7 ∨
    goodResidue a 11 ∨ goodResidue a 19 := by decide

private theorem roughCandidate :
    ∀ n : ℕ, 22 ≤ n → Even n → ∃ p : ℕ, Nat.Prime p ∧ p < n ∧ 2 ≤ n-p ∧ Nat.Coprime (n-p) 210 := by
  intro n hn heven
  obtain ⟨k, hk⟩ := heven
  let a : Fin 210 := ⟨n % 210, Nat.mod_lt _ (by decide)⟩
  have ha : a.val % 2 = 0 := by dsimp [a]; omega
  have liftPrime (p : ℕ) (hp : Nat.Prime p) (hbound : p ≤ 19)
      (hr : goodResidue a p) :
      ∃ p : ℕ, Nat.Prime p ∧ p < n ∧ 2 ≤ n-p ∧ Nat.Coprime (n-p) 210 := by
    refine ⟨p, hp, by omega, by omega, ?_⟩
    have hmod : (n - p) % 210 = (a.val + 210 - p) % 210 := by dsimp [a]; omega
    change (n - p).gcd 210 = 1
    rw [Nat.gcd_comm, Nat.gcd_rec, hmod]
    exact hr
  rcases evenResidues a ha with h | h | h | h | h
  · exact liftPrime 3 (by decide) (by decide) h
  · exact liftPrime 5 (by decide) (by decide) h
  · exact liftPrime 7 (by decide) (by decide) h
  · exact liftPrime 11 (by decide) (by decide) h
  · exact liftPrime 19 (by decide) (by decide) h

private theorem sizeCutoff : Real.exp (Real.exp (19 / 5)) < (11 : ℝ) ^ 19 := by
  have he : Real.exp 1 ≤ 2.719 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have h19 : Real.exp 19 = Real.exp 1 ^ 19 := by
    simp
  have h45 : Real.exp 45 = Real.exp 1 ^ 45 := by
    simp
  have h5 : Real.exp (19 / 5) ^ 5 = Real.exp 19 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hsmall : Real.exp (19 / 5) < 45 := by
    by_contra! h
    have lower := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 45) h 5
    have upper := pow_le_pow_left₀ (Real.exp_pos 1).le he 19
    rw [h5, h19] at lower
    exact (by norm_num : ¬ (45:ℝ)^5 ≤ (2.719:ℝ)^19) (lower.trans upper)
  calc
    Real.exp (Real.exp (19 / 5)) < Real.exp 45 := Real.exp_lt_exp.mpr hsmall
    _ = _ := h45
    _ ≤ (2.719:ℝ)^45 := pow_le_pow_left₀ (Real.exp_pos 1).le he 45
    _ < (11:ℝ)^19 := by norm_num

private theorem listPowerLower (l : List ℕ) (h : ∀ q ∈ l, 11 ≤ q) :
    11 ^ l.length ≤ l.prod := by
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.length_cons, List.prod_cons, pow_succ']
    exact Nat.mul_le_mul (h q (by simp)) (ih (fun r hr => h r (by simp [hr])))

private theorem roughPower (m : ℕ) (hm : 2 ≤ m) (hc : m.Coprime 210) :
    11 ^ m.primeFactorsList.length ≤ m := by
  conv_rhs => rw [← Nat.prod_primeFactorsList (by omega : m ≠ 0)]
  apply listPowerLower
  intro q hq
  have hp := Nat.prime_of_mem_primeFactorsList hq
  have hd := Nat.dvd_of_mem_primeFactorsList hq
  by_contra! hlt
  have h210 : q ∣ 210 := by
    have small : ∀ r : Fin 11, Nat.Prime r.val → r.val ∣ 210 := by decide
    exact small ⟨q, hlt⟩ hp
  exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hc hd h210)

private theorem smallPairs : ∀ a : Fin 22, 4 ≤ a.val → a.val % 2 = 0 →
    ∃ p : Fin 22, Nat.Prime p.val ∧ Nat.Prime (a.val - p.val) := by decide

theorem PEqualNP.Outside.L_goldbach_finite_rough_prototype_18 :
    ∀ n : ℕ, 4 ≤ n → Even n → (n:ℝ) < Real.exp (Real.exp (19/5)) → ∃ p : ℕ, Nat.Prime p ∧ 2 ≤ n-p ∧ (n-p).primeFactorsList.length ≤ 18 := by
  intro n hn heven hsize
  by_cases hlarge : 22 ≤ n
  · obtain ⟨p, hp, _, hm, hc⟩ := roughCandidate n hlarge heven
    refine ⟨p, hp, hm, ?_⟩
    by_contra! hmany
    have hlen : 19 ≤ (n-p).primeFactorsList.length := by omega
    have hpow : (11:ℕ)^19 ≤ n :=
      (Nat.pow_le_pow_right (by decide) hlen).trans
        ((roughPower _ hm hc).trans (Nat.sub_le _ _))
    have hreal : (11:ℝ)^19 ≤ n := by exact_mod_cast hpow
    exact (not_lt_of_ge hreal) (hsize.trans sizeCutoff)
  · obtain ⟨k, hk⟩ := heven
    obtain ⟨p, hp, hq⟩ := smallPairs ⟨n, by omega⟩ hn (by dsimp; omega)
    change Nat.Prime (n - p.val) at hq
    exact ⟨p.val, hp, hq.two_le, by simp [Nat.primeFactorsList_prime hq]⟩
