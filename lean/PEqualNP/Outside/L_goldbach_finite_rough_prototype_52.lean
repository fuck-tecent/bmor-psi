import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Factors


set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem roughResidueGrid30030 :
    ∀ (i : Fin 143) (j : Fin 105),
      ∃ p ∈ ({3,5,7,11,31,43,61,79,149,197} : Finset ℕ),
        Nat.Coprime ((2 * (105 * i.val + j.val) + 30030 - p) % 30030) 30030 := by
  decide +kernel

private theorem finiteResidueWitness30030 :
    ∀ a : ℕ, a < 30030 → Even a →
      ∃ p ∈ ({3,5,7,11,31,43,61,79,149,197} : Finset ℕ),
        Nat.Coprime ((a + 30030 - p) % 30030) 30030 := by
  intro a ha he
  obtain ⟨b, hb⟩ := he
  let i : Fin 143 := ⟨b / 105, by omega⟩
  let j : Fin 105 := ⟨b % 105, by omega⟩
  have ha' : 2 * (105 * i.val + j.val) = a := by
    dsimp [i, j]
    omega
  simpa only [ha'] using roughResidueGrid30030 i j

namespace GoldbachFinite

private theorem exp_one_lt_2719 : Real.exp 1 < 2.719 :=
  Real.exp_one_lt_d9.trans (by norm_num)

theorem exp_45_div_16_lt_17 : Real.exp (45 / 16) < 17 := by
  apply lt_of_pow_lt_pow_left₀ 16 (by norm_num)
  calc
    Real.exp (45 / 16) ^ 16 = Real.exp 1 ^ 45 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      norm_num
    _ < (2.719 : ℝ) ^ 45 := pow_lt_pow_left₀
      exp_one_lt_2719 (Real.exp_pos _).le (by decide)
    _ < (17 : ℝ) ^ 16 := by norm_num

theorem exp_19_div_5_lt_45 : Real.exp (19 / 5) < 45 := by
  apply lt_of_pow_lt_pow_left₀ 5 (by norm_num)
  calc
    Real.exp (19 / 5) ^ 5 = Real.exp 1 ^ 19 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      norm_num
    _ < (2.719 : ℝ) ^ 19 := pow_lt_pow_left₀
      exp_one_lt_2719 (Real.exp_pos _).le (by decide)
    _ < (45 : ℝ) ^ 5 := by norm_num

theorem exp_5_lt_149 : Real.exp 5 < 149 := by
  calc
    Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    _ < (2.719 : ℝ) ^ 5 := pow_lt_pow_left₀
      exp_one_lt_2719 (Real.exp_pos _).le (by decide)
    _ < 149 := by norm_num

end GoldbachFinite

private theorem product_ge_power_of_length (y : ℕ) (parts : List ℕ)
    (h : ∀ p ∈ parts, y ≤ p) : y ^ parts.length ≤ parts.prod := by
  induction parts with
  | nil => simp
  | cons p parts ih =>
      simp only [List.length_cons, List.prod_cons, pow_succ']
      exact Nat.mul_le_mul (h p (by simp)) (ih (fun r hr => h r (by simp [hr])))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem candidate30030_prime_bound :
    ∀ p ∈ ({3,5,7,11,31,43,61,79,149,197} : Finset ℕ), Nat.Prime p ∧ p ≤ 197 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_prime_divides_30030 :
    ∀ p ∈ Finset.range 17, Nat.Prime p → p ∣ 30030 := by
  decide +kernel

private theorem rough_prototype_30030 (cap n : ℕ) (hc : 8 ≤ cap)
    (hn : 4 ≤ n) (he : Even n) (hsize : n < 17^(cap+1)) :
    ∃ p : ℕ, Nat.Prime p ∧ 2 ≤ n-p ∧ (n-p).primeFactorsList.length ≤ cap := by
  by_cases hsmall : n < 200
  · have hm : 2 ≤ n-2 := by omega
    have hprod := product_ge_power_of_length 2 (n-2).primeFactorsList
      (fun k hk => (Nat.prime_of_mem_primeFactorsList hk).two_le)
    rw [Nat.prod_primeFactorsList (by omega : n-2 ≠ 0)] at hprod
    refine ⟨2, by decide, hm, ?_⟩
    by_contra! hl
    have h8 : (2 : ℕ)^8 ≤ (2 : ℕ)^((n-2).primeFactorsList.length) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hex := h8.trans hprod
    norm_num at hex
    omega
  · let a := n % 30030
    have ha : a < 30030 := Nat.mod_lt _ (by decide)
    have hae : Even a := by
      obtain ⟨k, hk⟩ := he
      refine ⟨a / 2, ?_⟩
      dsimp [a]
      omega
    obtain ⟨p, hp, hcop⟩ := finiteResidueWitness30030 a ha hae
    obtain ⟨hprime, hpBound⟩ := candidate30030_prime_bound p hp
    have hm : 2 ≤ n-p := by omega
    have hmEq : (n-p) % 30030 = (a+30030-p)%30030 := by
      dsimp [a]
      omega
    have hrough : Nat.Coprime (n-p) 30030 := by
      change Nat.gcd (n-p) 30030 = 1
      rw [Nat.gcd_comm (n-p) 30030, Nat.gcd_rec, hmEq]
      exact hcop
    have hf (r : ℕ) (hr : r ∈ (n-p).primeFactorsList) : 17 ≤ r := by
      by_contra! hlt
      have hrPrime := Nat.prime_of_mem_primeFactorsList hr
      have hdiv := Nat.dvd_gcd (Nat.dvd_of_mem_primeFactorsList hr)
        (small_prime_divides_30030 r (Finset.mem_range.mpr hlt) hrPrime)
      change Nat.gcd (n-p) 30030 = 1 at hrough
      rw [hrough] at hdiv
      exact hrPrime.ne_one (Nat.dvd_one.mp hdiv)
    have hprod := product_ge_power_of_length 17 (n-p).primeFactorsList hf
    rw [Nat.prod_primeFactorsList (by omega : n-p ≠ 0)] at hprod
    refine ⟨p, hprime, hm, ?_⟩
    by_contra! hl
    have hpow : (17:ℕ)^(cap+1) ≤ (17:ℕ)^((n-p).primeFactorsList.length) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    exact (not_le_of_gt hsize) (hpow.trans (hprod.trans (Nat.sub_le _ _)))

private theorem exp_end_75_lt_17_pow_16 : Real.exp (Real.exp (19/5)) < (17:ℝ)^16 := by
  calc
    _ < Real.exp 45 := Real.exp_lt_exp.mpr GoldbachFinite.exp_19_div_5_lt_45
    _ = Real.exp (45/16) ^ 16 := by rw [← Real.exp_nat_mul]; norm_num
    _ < _ := pow_lt_pow_left₀ GoldbachFinite.exp_45_div_16_lt_17
      (Real.exp_pos _).le (by decide)

private theorem exp_full_prototype_lt_17_pow_53 : Real.exp (Real.exp 5) < (17:ℝ)^53 := by
  calc
    _ < Real.exp 149 := Real.exp_lt_exp.mpr GoldbachFinite.exp_5_lt_149
    _ ≤ Real.exp ((53:ℝ) * (45/16)) := Real.exp_le_exp.mpr (by norm_num)
    _ = Real.exp (45/16) ^ 53 := by rw [← Real.exp_nat_mul]; norm_num
    _ < _ := pow_lt_pow_left₀ GoldbachFinite.exp_45_div_16_lt_17
      (Real.exp_pos _).le (by decide)


theorem PEqualNP.Outside.L_goldbach_finite_rough_prototype_52 :
    ∀ n : ℕ, 4 ≤ n → Even n → (n:ℝ) < Real.exp (Real.exp 5) → ∃ p : ℕ, Nat.Prime p ∧ 2 ≤ n-p ∧ (n-p).primeFactorsList.length ≤ 52 := by
  intro n hn he hs
  apply rough_prototype_30030 52 n (by decide) hn he
  have hx : (n : ℝ) < ((17^53 : ℕ) : ℝ) := by
    exact hs.trans (by exact_mod_cast exp_full_prototype_lt_17_pow_53)
  exact_mod_cast hx
