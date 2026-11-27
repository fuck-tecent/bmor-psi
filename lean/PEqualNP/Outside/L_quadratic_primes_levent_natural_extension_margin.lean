import Mathlib

set_option maxHeartbeats 4000000 in
private theorem fixed_a_exchange_aux :
    let block := fun x : ℕ => Finset.Ioc x (2*x);
    let primes := fun x : ℕ => (Finset.Ioc x ((2*x)^2+1)).filter (fun p => Nat.Prime p ∧ p^100000 ≤ (2*x)^132301);
    let window := fun x p : ℕ => (block x).filter (fun n => p^100000 ≤ n^132301);
    let countHits := fun a x p : ℕ => ((window x p).filter (fun n => p ∣ n^2+a)).card;
    let band := fun a x n : ℕ => (n^2+a).primeFactors.filter (fun p => x<p ∧ p^100000 ≤ n^132301);
    let inc := fun a x : ℕ => ∑ p ∈ primes x, (countHits a x p : ℝ) * Real.log (p : ℝ);
    ∀ a x : ℕ, (∑ n ∈ block x, ∑ p ∈ band a x n, Real.log (p : ℝ)) = inc a x := by
  dsimp only
  intro a x
  set Bx : Finset ℕ := Finset.Ioc x (2*x) with hBx
  set Px : Finset ℕ := (Finset.Ioc x ((2*x)^2+1)).filter (fun p => Nat.Prime p ∧ p^100000 ≤ (2*x)^132301) with hPxset
  have hxlt : ∀ n ∈ Bx, x < n := by
    intro n hn
    rw [hBx] at hn
    exact (Finset.mem_Ioc.1 hn).1
  have hxle : ∀ n ∈ Bx, n ≤ 2*x := by
    intro n hn
    rw [hBx] at hn
    exact (Finset.mem_Ioc.1 hn).2
  have hnpos : ∀ n ∈ Bx, 0 < n := by
    intro n hn
    have h := hxlt n hn
    omega
  have hPxmem : ∀ p ∈ Px, Nat.Prime p ∧ x < p ∧ p^100000 ≤ (2*x)^132301 := by
    intro p hp
    rw [hPxset] at hp
    obtain ⟨hp1, hp2, hp3⟩ := Finset.mem_filter.1 hp
    exact ⟨hp2, (Finset.mem_Ioc.1 hp1).1, hp3⟩
  have hsingle : ∀ n p : ℕ, 0 < n → p^100000 ≤ n^132301 → p ≤ n^2 := by
    intro n p hn hle
    by_contra hcon
    have hlt : n^2 < p := Nat.lt_of_not_le hcon
    have h1 : (n^2)^100000 < p^100000 := Nat.pow_lt_pow_left hlt (by norm_num)
    have h2 : n^132301 ≤ n^200000 := Nat.pow_le_pow_right hn (by norm_num)
    have h3 : (n^2)^100000 = n^200000 := by
      rw [← pow_mul]
    have h4 : n^200000 < p^100000 := by
      rw [← h3]
      exact h1
    omega
  have hsub : ∀ n ∈ Bx, (n^2+a).primeFactors.filter (fun p => x < p ∧ p^100000 ≤ n^132301) ⊆ Px := by
    intro n hn p hp
    obtain ⟨hp1, hp2, hp3⟩ := Finset.mem_filter.1 hp
    obtain ⟨hpp, hpdvd, hpnz⟩ := Nat.mem_primeFactors.1 hp1
    have hle : p ≤ (2*x)^2 := le_trans (hsingle n p (hnpos n hn) hp3) (Nat.pow_le_pow_left (hxle n hn) 2)
    rw [hPxset]
    refine Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨hp2, by omega⟩, hpp, ?_⟩
    exact le_trans hp3 (Nat.pow_le_pow_left (hxle n hn) 132301)
  have hpos2 : ∀ n ∈ Bx, n^2+a ≠ 0 := by
    intro n hn
    have h1 : 0 < n^2 := by
      have := hnpos n hn
      positivity
    have h2 : 0 < n^2+a := by omega
    exact Nat.pos_iff_ne_zero.1 h2
  have stepA : (∑ n ∈ Bx, ∑ p ∈ (n^2+a).primeFactors.filter (fun p => x < p ∧ p^100000 ≤ n^132301), Real.log (p : ℝ))
      = ∑ n ∈ Bx, ∑ p ∈ Px, (if (p^100000 ≤ n^132301 ∧ p ∣ n^2+a) then Real.log (p : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hsubn := hsub n hn
    have e1 : (∑ p ∈ (n^2+a).primeFactors.filter (fun p => x < p ∧ p^100000 ≤ n^132301), Real.log (p : ℝ))
        = ∑ p ∈ (n^2+a).primeFactors.filter (fun p => x < p ∧ p^100000 ≤ n^132301),
            (if p ∈ (n^2+a).primeFactors.filter (fun p => x < p ∧ p^100000 ≤ n^132301) then Real.log (p : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [if_pos hp]
    have e2 : (∑ p ∈ (n^2+a).primeFactors.filter (fun p => x < p ∧ p^100000 ≤ n^132301),
            (if p ∈ (n^2+a).primeFactors.filter (fun p => x < p ∧ p^100000 ≤ n^132301) then Real.log (p : ℝ) else 0))
        = ∑ p ∈ Px, (if p ∈ (n^2+a).primeFactors.filter (fun p => x < p ∧ p^100000 ≤ n^132301) then Real.log (p : ℝ) else 0) := by
      refine Finset.sum_subset hsubn ?_
      intro p hp hpns
      rw [if_neg hpns]
    have e3 : (∑ p ∈ Px, (if p ∈ (n^2+a).primeFactors.filter (fun p => x < p ∧ p^100000 ≤ n^132301) then Real.log (p : ℝ) else 0))
        = ∑ p ∈ Px, (if (p^100000 ≤ n^132301 ∧ p ∣ n^2+a) then Real.log (p : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro p hp
      obtain ⟨hpp, hxp, hple⟩ := hPxmem p hp
      have hmem : p ∈ (n^2+a).primeFactors.filter (fun p => x < p ∧ p^100000 ≤ n^132301) ↔ (p^100000 ≤ n^132301 ∧ p ∣ n^2+a) := by
        rw [Finset.mem_filter, Nat.mem_primeFactors]
        constructor
        · rintro ⟨⟨_, hdvd, _⟩, _, hle⟩
          exact ⟨hle, hdvd⟩
        · rintro ⟨hle, hdvd⟩
          exact ⟨⟨hpp, hdvd, hpos2 n hn⟩, hxp, hle⟩
      simp only [hmem]
    exact e1.trans (e2.trans e3)
  have stepB : ∀ p ∈ Px, ((((Bx.filter (fun n => p^100000 ≤ n^132301)).filter (fun n => p ∣ n^2+a)).card : ℝ) * Real.log (p : ℝ))
      = ∑ n ∈ Bx, (if (p^100000 ≤ n^132301 ∧ p ∣ n^2+a) then Real.log (p : ℝ) else 0) := by
    intro p hp
    have hW : ((Bx.filter (fun n => p^100000 ≤ n^132301)).filter (fun n => p ∣ n^2+a))
        = Bx.filter (fun n => p^100000 ≤ n^132301 ∧ p ∣ n^2+a) := by
      rw [Finset.filter_filter]
    rw [hW]
    have h1 : (∑ n ∈ Bx.filter (fun n => p^100000 ≤ n^132301 ∧ p ∣ n^2+a), Real.log (p : ℝ))
        = ((Bx.filter (fun n => p^100000 ≤ n^132301 ∧ p ∣ n^2+a)).card : ℝ) * Real.log (p : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h2 : (∑ n ∈ Bx.filter (fun n => p^100000 ≤ n^132301 ∧ p ∣ n^2+a), Real.log (p : ℝ))
        = ∑ n ∈ Bx, (if (p^100000 ≤ n^132301 ∧ p ∣ n^2+a) then Real.log (p : ℝ) else 0) :=
      Finset.sum_filter _ _
    exact h1.symm.trans h2
  calc (∑ n ∈ Bx, ∑ p ∈ (n^2+a).primeFactors.filter (fun p => x < p ∧ p^100000 ≤ n^132301), Real.log (p : ℝ))
      = ∑ n ∈ Bx, ∑ p ∈ Px, (if (p^100000 ≤ n^132301 ∧ p ∣ n^2+a) then Real.log (p : ℝ) else 0) := stepA
    _ = ∑ p ∈ Px, ∑ n ∈ Bx, (if (p^100000 ≤ n^132301 ∧ p ∣ n^2+a) then Real.log (p : ℝ) else 0) := Finset.sum_comm
    _ = ∑ p ∈ Px, ((((Bx.filter (fun n => p^100000 ≤ n^132301)).filter (fun n => p ∣ n^2+a)).card : ℝ) * Real.log (p : ℝ)) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact (stepB p hp).symm

/- The counting lemma above is adapted from PR #2596 (https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/2596), Apache-2.0. -/

theorem PEqualNP.Outside.L_quadratic_primes_levent_natural_extension_margin :
    let block := fun x : ℕ => Finset.Ioc x (2*x); let primes := fun x : ℕ => (Finset.Ioc x ((2*x)^2+1)).filter (fun p => Nat.Prime p ∧ p^100000 ≤ (2*x)^132301); let window := fun x p : ℕ => (block x).filter (fun n => p^100000 ≤ n^132301); let countHits := fun a x p : ℕ => ((window x p).filter (fun n => p ∣ n^2+a)).card; let band := fun a x n : ℕ => (n^2+a).primeFactors.filter (fun p => x<p ∧ p^100000 ≤ n^132301); let mass := fun a x : ℕ => ∑ n ∈ block x, ∑ p ∈ band a x n, ((n^2+a).factorization p : ℝ) * Real.log (p : ℝ); let excess := fun a x : ℕ => ∑ n ∈ block x, ∑ p ∈ band a x n, (((n^2+a).factorization p - 1 : ℕ) : ℝ) * Real.log (p : ℝ); let inc := fun a x : ℕ => ∑ p ∈ primes x, (countHits a x p : ℝ) * Real.log (p : ℝ); ∀ a x : ℕ, 0<a → mass a x = inc a x + excess a x := by
  intro block primes window countHits band mass excess inc a x ha
  have hfirst : (∑ n ∈ block x, ∑ p ∈ band a x n, Real.log (p : ℝ)) = inc a x := by
    exact fixed_a_exchange_aux a x
  change (∑ n ∈ block x, ∑ p ∈ band a x n, ((n^2+a).factorization p : ℝ) * Real.log (p : ℝ)) =
    inc a x + ∑ n ∈ block x, ∑ p ∈ band a x n, (((n^2+a).factorization p - 1 : ℕ) : ℝ) * Real.log (p : ℝ)
  rw [← hfirst, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hprime : Nat.Prime p := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1
  have hdvd : p ∣ n^2+a := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).2.1
  have hne : n^2+a ≠ 0 := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).2.2
  have hv : 0 < (n^2+a).factorization p := hprime.factorization_pos_of_dvd hne hdvd
  have heq : ((n^2+a).factorization p : ℝ) = 1 + (((n^2+a).factorization p - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : (n^2+a).factorization p = 1 + ((n^2+a).factorization p - 1))
  rw [heq]
  ring
