import Mathlib

private lemma struct_bad (x n p : ℕ) (hx : 1 ≤ x) (hn : n ∈ Finset.Ioc x (2*x))
    (hp : p ∈ (n^2+1).primeFactors.filter (fun p => x < p))
    (he : 2 ≤ (n^2+1).factorization p) :
    n^2+1 = 2*p^2 ∧ (n^2+1).factorization p = 2 := by
  classical
  have hxlt : x < p := (Finset.mem_filter.mp hp).2
  have hmem : p ∈ (n^2+1).primeFactors := (Finset.mem_filter.mp hp).1
  have hprime : p.Prime := (Nat.mem_primeFactors.mp hmem).1
  have hn0 : n^2+1 ≠ 0 := (Nat.mem_primeFactors.mp hmem).2.2
  have hnm : n ≤ 2*x := (Finset.mem_Ioc.mp hn).2
  have hnx : x < n := (Finset.mem_Ioc.mp hn).1
  have hp2 : p^2 ∣ n^2+1 := (Nat.Prime.pow_dvd_iff_le_factorization hprime hn0).mpr he
  obtain ⟨k, hk⟩ := hp2
  -- hk : n^2 + 1 = p^2 * k
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, Nat.mul_zero] at hk
      omega
    · exact h
  have hk4 : k ≤ 4 := by
    by_contra h5
    have h5' : 5 ≤ k := by omega
    have hle : 5 * p^2 ≤ n^2+1 := by
      rw [hk]
      calc 5 * p^2 = p^2 * 5 := by ring
        _ ≤ p^2 * k := by exact Nat.mul_le_mul_left _ h5'
    have hn2 : n^2 ≤ 4*x^2 := by nlinarith
    have hp2ge : (x+1)^2 ≤ p^2 := by nlinarith
    nlinarith
  interval_cases k
  · -- k = 1
    exfalso
    have h1 : n^2 < p^2 := by nlinarith
    have h2 : p^2 < (n+1)^2 := by nlinarith
    have h3 : n < p := by nlinarith
    have h4 : p < n+1 := by nlinarith
    omega
  · -- k = 2
    have hm : n^2+1 = 2*p^2 := by nlinarith
    refine ⟨hm, ?_⟩
    have hpne : p ≠ 2 := by
      rintro rfl
      have : n^2 = 7 := by nlinarith
      have hnle : n ≤ 2 := by nlinarith
      interval_cases n <;> simp at this
    have hfac : (2 * p^2).factorization p = 2 := by
      rw [Nat.factorization_mul (by norm_num) (pow_ne_zero 2 (Nat.Prime.ne_zero hprime)),
        Finsupp.add_apply, Nat.factorization_eq_zero_of_lt (by omega),
        Nat.factorization_pow_self hprime]
    simpa [hm] using hfac
  · -- k = 3
    exfalso
    have hz : ((n : ZMod 3))^2 + 1 = 0 := by
      have hc := congrArg (fun t : ℕ => (t : ZMod 3)) hk
      push_cast at hc
      have h3z : (3 : ZMod 3) = 0 := by decide
      rw [hc, h3z, mul_zero]
    have h3 : ∀ r : ZMod 3, r^2 + 1 ≠ 0 := by decide
    exact h3 _ hz
  · -- k = 4
    exfalso
    have hz : ((n : ZMod 4))^2 + 1 = 0 := by
      have hc := congrArg (fun t : ℕ => (t : ZMod 4)) hk
      push_cast at hc
      have h4z : (4 : ZMod 4) = 0 := by decide
      rw [hc, h4z, mul_zero]
    have h4 : ∀ r : ZMod 4, r^2 + 1 ≠ 0 := by decide
    exact h4 _ hz

private lemma pell_gap (n m p q : ℕ) (hn1 : 1 ≤ n) (hnm : n < m) (hmn : m ≤ 2*n)
    (h1 : n^2+1 = 2*p^2) (h2 : m^2+1 = 2*q^2) : False := by
  have hnm' : (n:ℝ) < (m:ℝ) := by exact_mod_cast hnm
  have hmn' : (m:ℝ) ≤ 2*(n:ℝ) := by exact_mod_cast hmn
  have hn1' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  -- integer Pell identity
  set A : ℤ := (n:ℤ)*(m:ℤ) - 2*((p:ℤ)*(q:ℤ)) with hA
  set B : ℤ := (n:ℤ)*(q:ℤ) - (m:ℤ)*(p:ℤ) with hB
  have hc1 : 2*(p:ℤ)^2 = (n:ℤ)^2 + 1 := by
    have h := congrArg (fun t : ℕ => (t:ℤ)) h1
    push_cast at h
    linarith
  have hc2 : 2*(q:ℤ)^2 = (m:ℤ)^2 + 1 := by
    have h := congrArg (fun t : ℕ => (t:ℤ)) h2
    push_cast at h
    linarith
  have hPell : A^2 - 2*B^2 = 1 := by
    rw [hA, hB]
    linear_combination (1:ℤ)*hc1 + (1:ℤ)*hc2 + (2*(p:ℤ)^2 - (n:ℤ)^2 - 1)*hc2
  -- B is nonzero
  have hBne : B ≠ 0 := by
    intro hBz
    have heq : (n:ℤ)*(q:ℤ) = (m:ℤ)*(p:ℤ) := by rw [hB] at hBz; linarith
    have hsq : (n:ℤ)^2*(q:ℤ)^2 = (m:ℤ)^2*(p:ℤ)^2 := by
      calc (n:ℤ)^2*(q:ℤ)^2 = ((n:ℤ)*(q:ℤ))^2 := by ring
        _ = ((m:ℤ)*(p:ℤ))^2 := by rw [heq]
        _ = (m:ℤ)^2*(p:ℤ)^2 := by ring
    have e1 : 2*(m:ℤ)^2*(p:ℤ)^2 = (m:ℤ)^2*((n:ℤ)^2+1) := by nlinarith [hc1]
    have e2 : 2*(n:ℤ)^2*(q:ℤ)^2 = (n:ℤ)^2*((m:ℤ)^2+1) := by nlinarith [hc2]
    have e3 : 2*((n:ℤ)^2*(q:ℤ)^2) = 2*((m:ℤ)^2*(p:ℤ)^2) := by rw [hsq]
    have hnmz : (n:ℤ) < (m:ℤ) := by exact_mod_cast hnm
    have hnz : (0:ℤ) < (n:ℤ) := by exact_mod_cast (by omega : 0 < n)
    nlinarith [e1, e2, e3, hnmz, hnz]
  -- real bound: A^2 < 4
  have hlt2 : (A:ℝ)^2 < 4 := by
    have f1 : 2*(p:ℝ)^2 = (n:ℝ)^2 + 1 := by
      have h := congrArg (fun t : ℕ => (t:ℝ)) h1
      push_cast at h
      linarith
    have f2 : 2*(q:ℝ)^2 = (m:ℝ)^2 + 1 := by
      have h := congrArg (fun t : ℕ => (t:ℝ)) h2
      push_cast at h
      linarith
    have hprod : (2*(p:ℝ)*(q:ℝ) - (n:ℝ)*(m:ℝ)) * (2*(p:ℝ)*(q:ℝ) + (n:ℝ)*(m:ℝ))
        = (n:ℝ)^2 + (m:ℝ)^2 + 1 := by
      linear_combination (2*(q:ℝ)^2) * f1 + ((n:ℝ)^2 + 1) * f2
    have hnp : (0:ℝ) < (n:ℝ) := by linarith
    have hmp : (0:ℝ) < (m:ℝ) := by linarith
    have h1' : (0:ℝ) < (n:ℝ)*(m:ℝ) := by positivity
    have h2pq : (n:ℝ)*(m:ℝ) < 2*(p:ℝ)*(q:ℝ) := by
      have hsq : ((n:ℝ)*(m:ℝ))^2 < (2*(p:ℝ)*(q:ℝ))^2 := by nlinarith [hprod]
      have habs : |(n:ℝ)*(m:ℝ)| < |2*(p:ℝ)*(q:ℝ)| := sq_lt_sq.mp hsq
      rwa [abs_of_pos h1', abs_of_nonneg (by positivity)] at habs
    have hpos : (0:ℝ) < 2*(p:ℝ)*(q:ℝ) + (n:ℝ)*(m:ℝ) := by linarith
    have hdiff : 2*(p:ℝ)*(q:ℝ) - (n:ℝ)*(m:ℝ)
        = ((n:ℝ)^2 + (m:ℝ)^2 + 1) / (2*(p:ℝ)*(q:ℝ) + (n:ℝ)*(m:ℝ)) := by
      rw [eq_div_iff (ne_of_gt hpos)]
      exact hprod
    have hc : (n:ℝ)^2 + (m:ℝ)^2 + 1 ≤ 4*((n:ℝ)*(m:ℝ)) := by nlinarith [hnm', hmn', hn1']
    have hlt : 2*(p:ℝ)*(q:ℝ) - (n:ℝ)*(m:ℝ) < 2 := by
      rw [hdiff, div_lt_iff₀ hpos]
      nlinarith [hc, h2pq]
    have hAval : (A:ℝ) = (n:ℝ)*(m:ℝ) - 2*((p:ℝ)*(q:ℝ)) := by
      rw [hA]; push_cast; ring
    nlinarith [hlt, h2pq, hAval]
  -- integrality conclusion
  have hAle : A^2 ≤ 3 := by
    have hcast : ((A^2 : ℤ) : ℝ) < 4 := by push_cast; exact hlt2
    have h4 : A^2 < 4 := by exact_mod_cast hcast
    omega
  have hBsq : 1 ≤ B^2 := by
    have h : B ≤ -1 ∨ 1 ≤ B := by omega
    rcases h with h | h
    · nlinarith [h]
    · nlinarith [h]
  have hA3 : A^2 = 3 := by nlinarith [hPell, hBsq, hAle]
  have hno : A^2 ≠ 3 := by
    intro h
    have h1' : A ≤ 1 := by
      by_contra hc
      push_neg at hc
      nlinarith [h]
    have h2' : -1 ≤ A := by
      by_contra hc
      push_neg at hc
      nlinarith [h]
    interval_cases A <;> norm_num at h
  exact hno hA3

private theorem repeat_block_cost :
    let w := fun (n p : ℕ) => ((((n^2+1).factorization p-1:ℕ):ℝ))*Real.log (p:ℝ); ∀ x : ℕ, 1≤x → (∑ n ∈ Finset.Ioc x (2*x), ∑ p ∈ ((n:ℕ)^2+1).primeFactors.filter (fun p => x<p), w n p) ≤ Real.log (((2*x)^2+1:ℕ):ℝ) := by
  dsimp only
  intro x hx
  classical
  set B : ℕ → Finset ℕ := fun n =>
    ((n^2+1).primeFactors.filter (fun p => x < p)).filter (fun p => 2 ≤ (n^2+1).factorization p) with hB
  set N : Finset ℕ := (Finset.Ioc x (2*x)).filter (fun n => (B n).Nonempty) with hN
  have hBmem : ∀ n p, p ∈ B n ↔
      p ∈ (n^2+1).primeFactors.filter (fun p => x < p) ∧ 2 ≤ (n^2+1).factorization p := by
    intro n p
    simp [hB]
  have hNmem : ∀ n, n ∈ N ↔ n ∈ Finset.Ioc x (2*x) ∧ (B n).Nonempty := by
    intro n
    simp [hN]
  have hlog2x : (0:ℝ) ≤ Real.log (2*x) := by
    apply Real.log_nonneg
    have h1 : (1:ℕ) ≤ 2*x := by omega
    exact_mod_cast h1
  -- a prime factor in `primeFactors` divides with positive multiplicity
  have hone : ∀ (n : ℕ), n ∈ Finset.Ioc x (2*x) →
      ∀ (p : ℕ), p ∈ (n^2+1).primeFactors.filter (fun p => x < p) → 1 ≤ (n^2+1).factorization p := by
    intro n hn p hp
    have hmem : p ∈ (n^2+1).primeFactors := (Finset.mem_filter.mp hp).1
    obtain ⟨hpp, hpdvd, hn0⟩ := Nat.mem_primeFactors.mp hmem
    exact (Nat.Prime.dvd_iff_one_le_factorization hpp hn0).mp hpdvd
  -- the individual summand only survives for repeated large prime factors
  have hterm : ∀ (n : ℕ), n ∈ Finset.Ioc x (2*x) →
      ∀ (p : ℕ), p ∈ (n^2+1).primeFactors.filter (fun p => x < p) →
      ((((n^2+1).factorization p - 1 : ℕ)) : ℝ) * Real.log ((p:ℕ):ℝ)
        = if 2 ≤ (n^2+1).factorization p then Real.log ((p:ℕ):ℝ) else 0 := by
    intro n hn p hp
    by_cases h2 : 2 ≤ (n^2+1).factorization p
    · have he := (struct_bad x n p hx hn hp h2).2
      rw [if_pos h2, he]
      norm_num
    · have h1 := hone n hn p hp
      have he1 : (n^2+1).factorization p = 1 := by omega
      rw [if_neg h2, he1]
      norm_num
  -- the inner sum is exactly the sum of `log p` over the repeated large primes
  have hper : ∀ n ∈ Finset.Ioc x (2*x),
      (∑ p ∈ ((n:ℕ)^2+1).primeFactors.filter (fun p => x<p),
          ((((n^2+1).factorization p - 1 : ℕ)) : ℝ) * Real.log ((p:ℕ):ℝ))
        = ∑ p ∈ B n, Real.log ((p:ℕ):ℝ) := by
    intro n hn
    simp only [hB]
    rw [Finset.sum_congr rfl (hterm n hn), ← Finset.sum_filter]
  have hBcard : ∀ n ∈ Finset.Ioc x (2*x), (B n).card ≤ 1 := by
    intro n hn
    rw [Finset.card_le_one]
    intro p hp q hq
    have hp' := struct_bad x n p hx hn ((hBmem n p).mp hp).1 ((hBmem n p).mp hp).2
    have hq' := struct_bad x n q hx hn ((hBmem n q).mp hq).1 ((hBmem n q).mp hq).2
    have h2 : 2*p^2 = 2*q^2 := by rw [← hp'.1, ← hq'.1]
    have h3 : p^2 = q^2 := by nlinarith
    nlinarith
  have hbound : ∀ n ∈ Finset.Ioc x (2*x), (B n).Nonempty →
      (∑ p ∈ ((n:ℕ)^2+1).primeFactors.filter (fun p => x<p),
          ((((n^2+1).factorization p - 1 : ℕ)) : ℝ) * Real.log ((p:ℕ):ℝ)) ≤ Real.log (2*x) := by
    intro n hn hne
    rw [hper n hn]
    calc ∑ p ∈ B n, Real.log ((p:ℕ):ℝ) ≤ ∑ p ∈ B n, Real.log (2*x) := by
          apply Finset.sum_le_sum
          intro p hp
          have hpF := ((hBmem n p).mp hp).1
          have hp2 := ((hBmem n p).mp hp).2
          have hs := struct_bad x n p hx hn hpF hp2
          have hpn : p ≤ n := by nlinarith [hs.1]
          have hpx : p ≤ 2*x := le_trans hpn (Finset.mem_Ioc.mp hn).2
          have hpos : (0:ℝ) < ((p:ℕ):ℝ) := by
            have h0 : 0 < p := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hpF).1).1.pos
            exact_mod_cast h0
          exact Real.log_le_log hpos (by exact_mod_cast hpx)
      _ = (B n).card * Real.log (2*x) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * Real.log (2*x) := by
          apply mul_le_mul_of_nonneg_right _ hlog2x
          exact_mod_cast hBcard n hn
      _ = Real.log (2*x) := one_mul _
  -- at most one `n` in the block carries a repeated large prime factor
  have hNcard : N.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro n hn m hm
    by_contra hne
    obtain ⟨hnI, hne'⟩ := (hNmem n).mp hn
    obtain ⟨hmI, hme'⟩ := (hNmem m).mp hm
    obtain ⟨p, hp⟩ := hne'
    obtain ⟨q, hq⟩ := hme'
    have hpF := ((hBmem n p).mp hp).1
    have hp2 := ((hBmem n p).mp hp).2
    have hqF := ((hBmem m q).mp hq).1
    have hq2 := ((hBmem m q).mp hq).2
    have hsn := struct_bad x n p hx hnI hpF hp2
    have hsm := struct_bad x m q hx hmI hqF hq2
    have hn1 : 1 ≤ n := by have := (Finset.mem_Ioc.mp hnI).1; omega
    have hm1 : 1 ≤ m := by have := (Finset.mem_Ioc.mp hmI).1; omega
    have hnx : x < n := (Finset.mem_Ioc.mp hnI).1
    have hn2x : n ≤ 2*x := (Finset.mem_Ioc.mp hnI).2
    have hmx : x < m := (Finset.mem_Ioc.mp hmI).1
    have hm2x : m ≤ 2*x := (Finset.mem_Ioc.mp hmI).2
    rcases lt_trichotomy n m with hlt | heq | hgt
    · exact pell_gap n m p q hn1 hlt (by omega) hsn.1 hsm.1
    · exact hne heq
    · exact pell_gap m n q p hm1 hgt (by omega) hsm.1 hsn.1
  -- rewrite the block sum as a sum over `N` (elsewhere the summand vanishes)
  have hsum_eq : (∑ n ∈ Finset.Ioc x (2*x),
        ∑ p ∈ ((n:ℕ)^2+1).primeFactors.filter (fun p => x<p),
          ((((n^2+1).factorization p - 1 : ℕ)) : ℝ) * Real.log ((p:ℕ):ℝ))
      = ∑ n ∈ N, ∑ p ∈ ((n:ℕ)^2+1).primeFactors.filter (fun p => x<p),
          ((((n^2+1).factorization p - 1 : ℕ)) : ℝ) * Real.log ((p:ℕ):ℝ) := by
    rw [hN]
    refine (Finset.sum_subset (Finset.filter_subset (fun n => (B n).Nonempty) (Finset.Ioc x (2*x))) ?_).symm
    intro n hnIoc hnN
    have hne : ¬ (B n).Nonempty := by
      intro h
      exact hnN (Finset.mem_filter.mpr ⟨hnIoc, h⟩)
    rw [hper n hnIoc, Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
  have hle1 : (∑ n ∈ N, ∑ p ∈ ((n:ℕ)^2+1).primeFactors.filter (fun p => x<p),
        ((((n^2+1).factorization p - 1 : ℕ)) : ℝ) * Real.log ((p:ℕ):ℝ))
      ≤ ∑ n ∈ N, Real.log (2*x) := by
    apply Finset.sum_le_sum
    intro n hn
    obtain ⟨hnI, hne⟩ := (hNmem n).mp hn
    exact hbound n hnI hne
  have hle2 : (∑ n ∈ N, Real.log (2*x)) = (N.card : ℝ) * Real.log (2*x) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hle3 : (N.card : ℝ) * Real.log (2*x) ≤ Real.log (2*x) := by
    have hc : (N.card : ℝ) ≤ 1 := by exact_mod_cast hNcard
    nlinarith
  have hle4 : Real.log (2*x) ≤ Real.log (((2*x)^2+1:ℕ):ℝ) := by
    apply Real.log_le_log (by positivity)
    push_cast
    nlinarith
  linarith [hsum_eq, hle1, hle2, hle3, hle4]

set_option maxHeartbeats 1000000 in
private theorem restricted_cost (x : ℕ) (hx : 1 ≤ x) (s : ℕ → Finset ℕ)
    (hsub : ∀ n, s n ⊆ (n^2+1).primeFactors.filter (fun p => x<p)) :
    (∑ n ∈ Finset.Ioc x (2*x), ∑ p ∈ s n,
      (((n^2+1).factorization p - 1 : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ)) ≤
        Real.log (((2*x)^2+1 : ℕ) : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.Ioc x (2*x), ∑ p ∈ (n^2+1).primeFactors.filter (fun p : ℕ => x<p),
        (((n^2+1).factorization p - 1 : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum_of_subset_of_nonneg (hsub n)
      intro p hp hnot
      have hprime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hprime.one_le))
    _ ≤ _ := by
      have hb := repeat_block_cost
      dsimp only at hb
      exact hb x hx

set_option maxHeartbeats 1000000 in
private theorem restricted_excess :
    let block := fun x : ℕ => Finset.Ioc x (2*x); let band := fun a x n : ℕ => (n^2+a).primeFactors.filter (fun p => x<p ∧ p^100000 ≤ n^132301); let excess := fun a x : ℕ => ∑ n ∈ block x, ∑ p ∈ band a x n, (((n^2+a).factorization p - 1 : ℕ) : ℝ) * Real.log (p : ℝ); ∀ x : ℕ, 1≤x → excess 1 x ≤ Real.log (((2*x)^2+1 : ℕ) : ℝ) := by
  intro block band excess x hx
  apply restricted_cost x hx (band 1 x)
  intro n p hp
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2.1⟩



private theorem dyadic_log_absorption :
    let budget := fun x : ℕ => (x : ℝ) * Real.log (x : ℝ); ∀ ε : ℝ, 0<ε → ∃ X : ℕ, ∀ x ≥ X, Real.log (((2*x)^2+1 : ℕ) : ℝ) ≤ ε*budget x := by
  dsimp only
  intro ε hε
  have hlog : Filter.Tendsto (fun x : ℕ => Real.log (x:ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ x : ℕ in Filter.atTop, 6 ≤ ε * Real.log (x:ℝ) :=
    (hlog.const_mul_atTop hε).eventually_ge_atTop 6
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max X 1, ?_⟩
  intro x hx
  have hxX : X ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have h6 : 6 ≤ ε * Real.log (x:ℝ) := hX x hxX
  have hxpos : (0:ℝ) < (x:ℝ) := by exact_mod_cast hx1
  have hx1R : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx1
  have hN : (((2*x)^2+1 : ℕ) : ℝ) ≤ (3*(x:ℝ))^2 := by
    push_cast
    nlinarith
  have hpos : (0:ℝ) < (((2*x)^2+1 : ℕ) : ℝ) := by positivity
  have hstep1 : Real.log (((2*x)^2+1 : ℕ) : ℝ) ≤ Real.log ((3*(x:ℝ))^2) :=
    Real.log_le_log hpos hN
  have hstep2 : Real.log ((3*(x:ℝ))^2) = 2 * Real.log (3*(x:ℝ)) := by
    rw [Real.log_pow]
    norm_num
  have hstep3 : Real.log (3*(x:ℝ)) ≤ 3*(x:ℝ) := Real.log_le_self (by positivity)
  have hfin : 6*(x:ℝ) ≤ ε*((x:ℝ)*Real.log (x:ℝ)) := by nlinarith
  linarith

theorem PEqualNP.Outside.L_quadratic_primes_levent_sieve_margin :
    let block := fun x : ℕ => Finset.Ioc x (2*x); let budget := fun x : ℕ => (x : ℝ) * Real.log (x : ℝ); let band := fun a x n : ℕ => (n^2+a).primeFactors.filter (fun p => x<p ∧ p^100000 ≤ n^132301); let excess := fun a x : ℕ => ∑ n ∈ block x, ∑ p ∈ band a x n, (((n^2+a).factorization p - 1 : ℕ) : ℝ) * Real.log (p : ℝ); ∃ X : ℕ, ∀ x ≥ X, excess 1 x ≤ (1/100 : ℝ)*budget x := by
  intro block budget band excess
  have hbound := restricted_excess
  dsimp only at hbound
  have habsorb := dyadic_log_absorption
  dsimp only at habsorb
  obtain ⟨X, hX⟩ := habsorb (1 / 100 : ℝ) (by norm_num)
  refine ⟨max X 1, ?_⟩
  intro x hx
  exact (hbound x (le_trans (le_max_right _ _) hx)).trans
    (hX x (le_trans (le_max_left _ _) hx))
