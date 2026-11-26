import Mathlib

namespace GoldbachFixedAP
noncomputable section

private def ap (q a n : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k

private def evenMass (n : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range (n+1)).filter (fun k => ¬Nat.Coprime k 2), ArithmeticFunction.vonMangoldt k

theorem liftFour (n : ℕ) :
    ap 2 1 n = ap 4 1 n + ap 4 3 n ∧
    ap 1 0 n = ap 4 1 n + ap 4 3 n + evenMass n := by
  unfold ap evenMass
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  constructor <;> apply Finset.sum_congr rfl <;> intro k _
  · split_ifs <;> first | omega | simp_all
  · have parity : Nat.Coprime k 2 ↔ k%2=1 := by rw [Nat.coprime_comm,Nat.coprime_two_left, Nat.odd_iff]
    simp only [parity]
    split_ifs <;> first | omega | simp_all

private theorem normalization (q a n : ℕ) : ap q a n = ap q (a%q) n := by simp [ap]

private abbrev ExplicitInput := ∀ q a n : ℕ, 3≤q → q≤105 → a<q → Nat.Coprime a q →
  8000000000≤n → |ap q a n-(n:ℝ)/q.totient| ≤ (n:ℝ)/(840*Real.log (n:ℝ))
private abbrev Parent := ∀ q a n : ℕ, 1≤q → q≤105 → Nat.Coprime a q → 10^16≤n →
  (n:ℝ)<Real.exp (Real.exp (19/5)) → |ap q a n-(n:ℝ)/q.totient| ≤ (n:ℝ)/100

theorem fromBMOR (bmor : ExplicitInput)
    (nonunit : ∀ q n : ℕ, 1≤q → 1≤n →
      (∑ k ∈ (Finset.range (n+1)).filter (fun k => ¬ Nat.Coprime k q), ArithmeticFunction.vonMangoldt k)
        ≤ (q.primeFactors.card:ℝ)*Real.log n) : Parent := by
  intro q a n hq h105 cop hn hmax
  have hn1 : 1≤n := by omega
  have nr : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have log1 : 1≤Real.log (n:ℝ) := by
    have h3 : (3:ℝ)≤n := by exact_mod_cast (show 3≤n by omega)
    exact (Real.le_log_iff_exp_le nr).mpr (Real.exp_one_lt_d9.le.trans (by linarith))
  have small (q a : ℕ) (hq : 3≤q) (hu : q≤105) (ha : Nat.Coprime a q) :
      |ap q a n-(n:ℝ)/q.totient| ≤ (n:ℝ)/840 := by
    rw [normalization q a n]
    have hcop : Nat.Coprime (a%q) q := by
      change (a%q).gcd q = 1
      rw [← Nat.gcd_rec q a]
      exact ha.symm
    apply (bmor q (a%q) n hq hu (Nat.mod_lt _ (by omega)) hcop (by omega)).trans
    exact div_le_div_of_nonneg_left nr.le (by norm_num) (by linarith)
  by_cases h : 3≤q
  · linarith only [small q a h h105 cop,nr]
  have e1 := small 4 1 (by decide) (by decide) (by decide)
  have e3 := small 4 3 (by decide) (by decide) (by decide)
  rw [show Nat.totient 4=2 by decide] at e1 e3
  have both : |ap 4 1 n+ap 4 3 n-(n:ℝ)| ≤ 2*((n:ℝ)/840) := by
    rw [show ap 4 1 n+ap 4 3 n-(n:ℝ) = (ap 4 1 n-(n:ℝ)/2)+(ap 4 3 n-(n:ℝ)/2) by ring]
    exact (abs_add_le ..).trans (by norm_num at e1 e3 ⊢; linarith)
  rcases (show q=1 ∨ q=2 by omega) with rfl | rfl
  · have ev := nonunit 2 n (by decide) hn1
    change evenMass n ≤ _ at ev
    rw [Nat.prime_two.primeFactors, Finset.card_singleton] at ev
    have epos : 0≤evenMass n := Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
    have lmax : Real.log (n:ℝ) < 81 := by
      have hb : Real.log (n:ℝ)<Real.exp (19/5) := (Real.log_lt_iff_lt_exp nr).mpr hmax
      have h4 : Real.exp (19/5) ≤ Real.exp ((4:ℕ)*1) := Real.exp_le_exp.mpr (by norm_num)
      rw [Real.exp_nat_mul] at h4
      have p : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      linarith only [hb,h4,pow_le_pow_left₀ (Real.exp_pos 1).le p 4]
    rw [normalization 1 a n,Nat.mod_one,(liftFour n).2,Nat.totient_one,Nat.cast_one,div_one]
    rw [show ap 4 1 n+ap 4 3 n+evenMass n-(n:ℝ)=(ap 4 1 n+ap 4 3 n-(n:ℝ))+evenMass n by ring]
    apply (abs_add_le ..).trans
    rw [abs_of_nonneg epos]
    have big : (10^16:ℝ)≤n := by exact_mod_cast hn
    norm_num at ev
    linarith
  · have ar : a%2=1 := by rw [Nat.coprime_comm,Nat.coprime_two_left,Nat.odd_iff] at cop; exact cop
    rw [normalization 2 a n,ar,(liftFour n).1,show Nat.totient 2=1 by decide,Nat.cast_one,div_one]
    linarith only [both,nr]

private def theta (q a n : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q),
    (if k.Prime then ArithmeticFunction.vonMangoldt k else 0)

private def powers (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), (if k.Prime then 0 else ArithmeticFunction.vonMangoldt k)

private theorem ap_theta (q a n : ℕ) : 0 ≤ ap q a n - theta q a n ∧
    ap q a n - theta q a n ≤ powers n := by
  unfold ap theta powers
  rw [← Finset.sum_sub_distrib, Finset.sum_filter]
  constructor
  · apply Finset.sum_nonneg
    intro k _
    split_ifs <;> simp_all [ArithmeticFunction.vonMangoldt_nonneg]
  · apply Finset.sum_le_sum
    intro k _
    split_ifs <;> simp_all [ArithmeticFunction.vonMangoldt_nonneg]

theorem fromTheta
    (primes : ∀ q a n : ℕ, 1 ≤ q → q ≤ 105 → Nat.Coprime a q → 10^16 ≤ n →
      (n:ℝ) < Real.exp (Real.exp (19/5)) → |theta q a n - (n:ℝ)/q.totient| ≤ (n:ℝ)/200)
    (higher : ∀ n : ℕ, 10^16 ≤ n → powers n ≤ (n:ℝ)/200) : Parent := by
  intro q a n hq h105 hcop hn hmax
  have ht := abs_le.mp (primes q a n hq h105 hcop hn hmax)
  obtain ⟨hlo,hhi⟩ := ap_theta q a n
  have hp := higher n hn
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  apply abs_le.mpr
  constructor <;> linarith

end
end GoldbachFixedAP
