import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_prime_values_power_count :
    let block := fun x : ℕ => Finset.Ioc x (2*x);
    ∃ C : ℝ, 0<C ∧ ∀ x : ℕ, 2≤x → (((block x).filter (fun n => ArithmeticFunction.vonMangoldt (n^2+1)≠0 ∧ ¬ (n^2+1).Prime)).card : ℝ) ≤ C*(x : ℝ)^(2/3 : ℝ)*Real.log (2*(x : ℝ)) := by
  dsimp only
  refine ⟨100, by norm_num, ?_⟩
  intro x hx
  classical
  set S : Finset ℕ := (Finset.Ioc x (2*x)).filter
    (fun n => ArithmeticFunction.vonMangoldt (n^2+1) ≠ 0 ∧ ¬ (n^2+1).Prime) with hS
  set N : ℕ := Nat.floor (((2*(x:ℝ))^2+1)^(1/3:ℝ)) with hN
  set K : ℕ := Nat.log 2 ((2*x)^2+1) with hK
  have hxR : (2:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by linarith
  have hx0 : (0:ℝ) ≤ (x:ℝ) := by linarith
  have hsq : ∀ n m : ℕ, n^2 = m^2 → n = m := by
    intro n m h
    rcases Nat.lt_trichotomy n m with h' | h' | h'
    · exfalso
      have : n^2 < m^2 := Nat.pow_lt_pow_left h' (by norm_num)
      omega
    · exact h'
    · exfalso
      have : m^2 < n^2 := Nat.pow_lt_pow_left h' (by norm_num)
      omega
  -- ### Step 1: structure of every member of S
  have hdata : ∀ n ∈ S, ∃ p k : ℕ, p.Prime ∧ 3 ≤ k ∧ n^2+1 = p^k ∧ p ≤ N ∧ k ≤ K := by
    intro n hn
    obtain ⟨hmem, hL, hnp⟩ := Finset.mem_filter.mp hn
    have hn2x : n ≤ 2*x := (Finset.mem_Ioc.mp hmem).2
    have hn1 : 1 ≤ n := by
      have := (Finset.mem_Ioc.mp hmem).1
      omega
    have hIP : IsPrimePow (n^2+1) := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hL
    obtain ⟨k, hklog, hkpos, p, hple, heq, hp⟩ := (isPrimePow_nat_iff_bounded_log (n^2+1)).mp hIP
    have hk1 : k ≠ 1 := by
      intro h1
      apply hnp
      rw [heq, h1, pow_one]
      exact hp
    have hk2 : k ≠ 2 := by
      intro h2
      have hp2 : p^2 = n^2+1 := by
        have h := heq
        rw [h2] at h
        exact h.symm
      have hlt : n < p := by
        rcases Nat.lt_or_ge n p with h' | h'
        · exact h'
        · exfalso
          have hle : p^2 ≤ n^2 := Nat.pow_le_pow_left h' 2
          omega
      have hlt2 : p < n+1 := by
        rcases Nat.lt_or_ge p (n+1) with h' | h'
        · exact h'
        · exfalso
          have hle : (n+1)^2 ≤ p^2 := Nat.pow_le_pow_left h' 2
          nlinarith
      omega
    have hk3 : 3 ≤ k := by omega
    have hpmem : n^2+1 ≤ (2*x)^2+1 := Nat.add_le_add_right (Nat.pow_le_pow_left hn2x 2) 1
    have hp3 : p^3 ≤ n^2+1 := by
      calc p^3 ≤ p^k := Nat.pow_le_pow_right hp.one_le hk3
        _ = n^2+1 := heq.symm
    have hpM : (p:ℝ)^3 ≤ (2*(x:ℝ))^2+1 := by
      have h1 : ((p:ℝ))^3 ≤ ((n^2+1 : ℕ) : ℝ) := by
        calc ((p:ℝ))^3 = ((p^3 : ℕ) : ℝ) := by push_cast; ring
          _ ≤ ((n^2+1 : ℕ) : ℝ) := by exact_mod_cast hp3
      have h2 : ((n^2+1 : ℕ) : ℝ) ≤ (2*(x:ℝ))^2+1 := by
        calc ((n^2+1 : ℕ) : ℝ) ≤ (((2*x)^2+1 : ℕ) : ℝ) := by exact_mod_cast hpmem
          _ = (2*(x:ℝ))^2+1 := by push_cast; ring
      linarith
    have hpN : p ≤ N := by
      rw [hN]
      apply Nat.le_floor
      have hp0 : (0:ℝ) ≤ (p:ℝ) := by positivity
      have hstep : (p:ℝ) = ((p:ℝ)^3)^(1/3:ℝ) := by
        have h := Real.pow_rpow_inv_natCast (x := (p:ℝ)) hp0 (n := 3) (by norm_num)
        simpa using h.symm
      rw [hstep]
      exact Real.rpow_le_rpow (by positivity) hpM (by norm_num)
    have hkK : k ≤ K := by
      rw [hK]
      exact le_trans hklog (Nat.log_mono_right hpmem)
    exact ⟨p, k, hp, hk3, heq, hpN, hkK⟩
  -- ### Step 2: injective map into pairs (prime, exponent)
  let Q : ℕ → Prop := fun n => ∃ p k : ℕ, p.Prime ∧ 3 ≤ k ∧ n^2+1 = p^k ∧ p ≤ N ∧ k ≤ K
  let f : ℕ → ℕ × ℕ := fun n =>
    if h : Q n then (Classical.choose h, Classical.choose (Classical.choose_spec h)) else (0, 0)
  have hf_spec : ∀ n ∈ S, (f n).1.Prime ∧ 3 ≤ (f n).2 ∧ n^2+1 = (f n).1^(f n).2 ∧ (f n).1 ≤ N ∧ (f n).2 ≤ K := by
    intro n hn
    have hex : Q n := hdata n hn
    have hval : f n = (Classical.choose hex, Classical.choose (Classical.choose_spec hex)) := by
      simp only [f, dite_eq_left hex]
    rw [hval]
    exact Classical.choose_spec (Classical.choose_spec hex)
  have hmaps : Set.MapsTo f (↑S : Set ℕ) ↑((Finset.range (N+1)).filter Nat.Prime ×ˢ Finset.range (K+1)) := by
    intro n hn
    have hspec := hf_spec n hn
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_range]
    refine ⟨⟨by omega, hspec.1⟩, by omega⟩
  have hinj : (↑S : Set ℕ).InjOn f := by
    intro n hn m hm hnm
    have hn' := hf_spec n hn
    have hm' := hf_spec m hm
    have h1 : (f n).1 = (f m).1 := by rw [hnm]
    have h2 : (f n).2 = (f m).2 := by rw [hnm]
    have he : n^2+1 = m^2+1 := by
      rw [hn'.2.2.1, hm'.2.2.1, h1, h2]
    exact hsq n m (by omega)
  -- ### Step 3: cardinality bound
  have hcardS := Finset.card_le_card_of_injOn f hmaps hinj
  set T : Finset (ℕ × ℕ) := (Finset.range (N+1)).filter Nat.Prime ×ˢ Finset.range (K+1) with hT
  have hcardT : S.card ≤ ((N+1) * (K+1) : ℕ) := by
    calc S.card ≤ T.card := hcardS
      _ = ((Finset.range (N+1)).filter Nat.Prime).card * (Finset.range (K+1)).card := by
            rw [hT, Finset.card_product]
      _ ≤ (N+1) * (K+1) := by
            apply Nat.mul_le_mul _ (le_of_eq (Finset.card_range _))
            exact le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_range _))
  -- ### Step 4: real bounds
  have hNle : ((N:ℝ) + 1) ≤ 3 * (x:ℝ)^(2/3:ℝ) := by
    rw [hN]
    have hr0 : (0:ℝ) ≤ (((2*(x:ℝ))^2+1)^(1/3:ℝ)) := Real.rpow_nonneg (by positivity) _
    have hcube : ((x:ℝ)^(2/3:ℝ))^3 = (x:ℝ)^2 := by
      rw [← Real.rpow_mul_natCast hx0 (2/3:ℝ) 3]
      norm_num [Real.rpow_two]
    have hA : (2*(x:ℝ))^2+1 ≤ (2 * (x:ℝ)^(2/3:ℝ))^3 := by nlinarith
    have hB : (((2*(x:ℝ))^2+1)^(1/3:ℝ)) ≤ ((2 * (x:ℝ)^(2/3:ℝ))^3)^(1/3:ℝ) :=
      Real.rpow_le_rpow (by positivity) hA (by norm_num)
    have h2c : (0:ℝ) ≤ 2 * (x:ℝ)^(2/3:ℝ) := by
      have := Real.rpow_nonneg hx0 (2/3:ℝ)
      linarith
    have hC : ((2 * (x:ℝ)^(2/3:ℝ))^3)^(1/3:ℝ) = 2 * (x:ℝ)^(2/3:ℝ) := by
      have h := Real.pow_rpow_inv_natCast (x := 2 * (x:ℝ)^(2/3:ℝ)) h2c (n := 3) (by norm_num)
      simpa using h
    have hNfloor : ((Nat.floor (((2*(x:ℝ))^2+1)^(1/3:ℝ)) : ℕ) : ℝ) ≤ ((2*(x:ℝ))^2+1)^(1/3:ℝ) :=
      Nat.floor_le hr0
    have hx23 : (1:ℝ) ≤ (x:ℝ)^(2/3:ℝ) := Real.one_le_rpow hx1 (by norm_num)
    linarith
  have hKle : ((K:ℝ) + 1) ≤ 7 * Real.log (2*(x:ℝ)) := by
    rw [hK]
    have hKne : (2*x)^2+1 ≠ 0 := by positivity
    have h2K : (2:ℝ)^(Nat.log 2 ((2*x)^2+1)) ≤ (((2*x)^2+1 : ℕ) : ℝ) := by
      have h := Nat.pow_log_le_self 2 hKne
      exact_mod_cast h
    have hcast : (((2*x)^2+1 : ℕ) : ℝ) = (2*(x:ℝ))^2+1 := by push_cast; ring
    have h2K' : (2:ℝ)^(Nat.log 2 ((2*x)^2+1)) ≤ (2*(x:ℝ))^2+1 := by rw [← hcast]; exact h2K
    have hKlog : ((Nat.log 2 ((2*x)^2+1) : ℕ) : ℝ) * Real.log 2 ≤ Real.log ((2*(x:ℝ))^2+1) := by
      have h := Real.log_le_log (by positivity) h2K'
      rwa [Real.log_pow] at h
    have hMle : Real.log ((2*(x:ℝ))^2+1) ≤ 4 * Real.log (2*(x:ℝ)) := by
      have h5 : (0:ℝ) < (2*(x:ℝ))^2+1 := by positivity
      have h1 : Real.log ((2*(x:ℝ))^2+1) ≤ Real.log (8*(x:ℝ)^2) := by
        apply Real.log_le_log h5
        nlinarith
      have h2 : Real.log (8*(x:ℝ)^2) = 3*Real.log 2 + 2*Real.log (x:ℝ) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        have h8 : Real.log (8:ℝ) = 3*Real.log 2 := by
          rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
        push_cast
        linarith
      have h3 : Real.log (2*(x:ℝ)) = Real.log 2 + Real.log (x:ℝ) := by
        rw [Real.log_mul (by norm_num) (by linarith)]
      have hlx : (0:ℝ) ≤ Real.log (x:ℝ) := Real.log_nonneg hx1
      have hl2 : (0:ℝ) ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num))
      linarith
    have hL1 : (1:ℝ) ≤ Real.log (2*(x:ℝ)) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      nlinarith [Real.exp_one_lt_three]
    have hK6 : ((Nat.log 2 ((2*x)^2+1) : ℕ) : ℝ) ≤ 6 * Real.log (2*(x:ℝ)) := by
      have hl2 : (2/3:ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
      have hKnn : (0:ℝ) ≤ ((Nat.log 2 ((2*x)^2+1) : ℕ) : ℝ) := by positivity
      nlinarith
    linarith
  have hLnn : (0:ℝ) ≤ Real.log (2*(x:ℝ)) := by
    have : (1:ℝ) ≤ Real.log (2*(x:ℝ)) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      nlinarith [Real.exp_one_lt_three]
    linarith
  have hxnn : (0:ℝ) ≤ (x:ℝ)^(2/3:ℝ) := Real.rpow_nonneg hx0 _
  have hcardR : ((S.card : ℕ) : ℝ) ≤ ((N:ℝ) + 1) * ((K:ℝ) + 1) := by
    have h := hcardT
    calc ((S.card : ℕ) : ℝ) ≤ (((N+1) * (K+1) : ℕ) : ℝ) := by exact_mod_cast h
      _ = ((N:ℝ) + 1) * ((K:ℝ) + 1) := by push_cast; ring
  have hprod : ((N:ℝ) + 1) * ((K:ℝ) + 1) ≤ (3 * (x:ℝ)^(2/3:ℝ)) * (7 * Real.log (2*(x:ℝ))) :=
    mul_le_mul hNle hKle (by linarith) (by positivity)
  nlinarith
