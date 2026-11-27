import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_middle_prime_container :
    let block := fun x : ℕ => Finset.Ioc x (2*x); let primes := fun x : ℕ => (Finset.Ioc x ((2*x)^2+1)).filter (fun p => Nat.Prime p ∧ p^100000 ≤ (2*x)^132301); let window := fun x p : ℕ => (block x).filter (fun n => p^100000 ≤ n^132301); let band := fun a x n : ℕ => (n^2+a).primeFactors.filter (fun p => x<p ∧ p^100000 ≤ n^132301); ∀ a x n p : ℕ, n ∈ block x → p ∈ band a x n → p ∈ primes x ∧ n ∈ window x p := by
  change ∀ a x n p : ℕ,
    n ∈ Finset.Ioc x (2 * x) →
    p ∈ (n ^ 2 + a).primeFactors.filter (fun p => x < p ∧ p ^ 100000 ≤ n ^ 132301) →
    p ∈ (Finset.Ioc x ((2 * x) ^ 2 + 1)).filter
      (fun p => Nat.Prime p ∧ p ^ 100000 ≤ (2 * x) ^ 132301) ∧
    n ∈ (Finset.Ioc x (2 * x)).filter (fun n => p ^ 100000 ≤ n ^ 132301)
  intro a x n p hn hp
  have hxn : x < n := (Finset.mem_Ioc.mp hn).1
  have hn2x : n ≤ 2 * x := (Finset.mem_Ioc.mp hn).2
  have hn_pos : 0 < n := Nat.zero_lt_of_lt hxn
  have hp_mem : p ∈ (n ^ 2 + a).primeFactors ∧ (x < p ∧ p ^ 100000 ≤ n ^ 132301) :=
    Finset.mem_filter.mp hp
  have hp_fac : p ∈ (n ^ 2 + a).primeFactors := hp_mem.1
  have hxp : x < p := hp_mem.2.1
  have hpow : p ^ 100000 ≤ n ^ 132301 := hp_mem.2.2
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp_fac
  have hp_2x : p ^ 100000 ≤ (2 * x) ^ 132301 :=
    le_trans hpow (Nat.pow_le_pow_left hn2x 132301)
  have hexp : (132301 : ℕ) ≤ 2 * 100000 := by decide
  have hp_sq_pow : p ^ 100000 ≤ (n ^ 2) ^ 100000 := by
    calc p ^ 100000 ≤ n ^ 132301 := hpow
      _ ≤ n ^ (2 * 100000) := Nat.pow_le_pow_right hn_pos hexp
      _ = (n ^ 2) ^ 100000 := by rw [pow_mul]
  have hk : (100000 : ℕ) ≠ 0 := by decide
  have hp_le_n2 : p ≤ n ^ 2 := (Nat.pow_le_pow_iff_left hk).mp hp_sq_pow
  have hn2_le : n ^ 2 ≤ (2 * x) ^ 2 := Nat.pow_le_pow_left hn2x 2
  have hp_bound : p ≤ (2 * x) ^ 2 + 1 :=
    le_trans hp_le_n2 (le_trans hn2_le (Nat.le_succ _))
  refine ⟨?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hxp, hp_bound⟩, hp_prime, hp_2x⟩
  · exact Finset.mem_filter.mpr ⟨hn, hpow⟩
