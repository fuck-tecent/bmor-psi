import Mathlib

/-!
The square sieve is reproduced from SaladDay's formally verified PR #3933.
The small square classification is from PR #3833 and the higher-power
bound is from PR #2915. This single-file verification retains upstream
Apache-2.0 source notices and includes each dependency before it is used.
-/

open scoped BigOperators

noncomputable section

/-- `log 2 ≥ 1/2`. -/
private lemma log_two_ge_half : (1/2 : ℝ) ≤ Real.log 2 := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 2)]
  have hsq : Real.exp (1/2) * Real.exp (1/2) = Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have hlt : Real.exp 1 < 4 := by
    linarith [Real.exp_one_lt_d9]
  have hpos : 0 < Real.exp (1/2) := Real.exp_pos _
  nlinarith [hsq, hlt, hpos, sq_nonneg (Real.exp (1/2) - 2)]

/-- From `p^k ≤ Y` (over `ℕ`) deduce `p ≤ Y^(1/k)` (over `ℝ`). -/
private lemma le_rpow_of_pow_le {p k Y : ℕ} (hp : 1 ≤ p) (hk : 1 ≤ k) (hpk : p^k ≤ Y) :
    (p:ℝ) ≤ (Y:ℝ) ^ ((1:ℝ)/(k:ℝ)) := by
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
  have hpkR : (p:ℝ)^k ≤ (Y:ℝ) := by exact_mod_cast hpk
  have hpeq : ((p:ℝ)^k) ^ ((1:ℝ)/(k:ℝ)) = (p:ℝ) := by
    rw [← Real.rpow_natCast ((p:ℝ)) k, ← Real.rpow_mul (le_of_lt hp0)]
    rw [show ((k:ℝ) * ((1:ℝ)/(k:ℝ))) = 1 by field_simp]
    rw [Real.rpow_one]
  rw [← hpeq]
  exact Real.rpow_le_rpow (by positivity) hpkR (by positivity)

/-- The log-weighted sum of primes `p` with `p^k ≤ Y` is at most `log 4 · Y^(1/k)`. -/
private lemma prime_sum_pow_le (k Y : ℕ) (hk : 3 ≤ k) :
    (∑ p ∈ (Finset.range (Y+1)).filter (fun p => p.Prime ∧ p^k ≤ Y), Real.log (p:ℝ))
      ≤ Real.log 4 * (Y:ℝ) ^ ((1:ℝ)/(k:ℝ)) := by
  classical
  set y : ℝ := (Y:ℝ) ^ ((1:ℝ)/(k:ℝ)) with hy
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hle : ∀ p ∈ (Finset.range (Y+1)).filter (fun p => p.Prime ∧ p^k ≤ Y),
      (p:ℝ) ≤ y := by
    intro p hp
    obtain ⟨-, hpp, hpk⟩ := Finset.mem_filter.mp hp
    exact le_rpow_of_pow_le hpp.one_le (by omega) hpk
  have hsub : (Finset.range (Y+1)).filter (fun p => p.Prime ∧ p^k ≤ Y)
      ⊆ Nat.primesLE ⌊y⌋₊ := by
    intro p hp
    obtain ⟨-, hpp, -⟩ := Finset.mem_filter.mp hp
    have hpfloor : p ≤ ⌊y⌋₊ := Nat.le_floor (hle p hp)
    rw [Nat.primesLE_eq_filter_range, Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hpfloor), hpp⟩
  calc (∑ p ∈ (Finset.range (Y+1)).filter (fun p => p.Prime ∧ p^k ≤ Y), Real.log (p:ℝ))
      ≤ ∑ p ∈ Nat.primesLE ⌊y⌋₊, Real.log (p:ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => Real.log_natCast_nonneg p)
    _ = Chebyshev.theta y := (Chebyshev.theta_eq_sum_primesLE y).symm
    _ ≤ Real.log 4 * y := Chebyshev.theta_le_log4_mul_x hy0
    _ = Real.log 4 * (Y:ℝ) ^ ((1:ℝ)/(k:ℝ)) := by rw [hy]

/-- PREPUB twin-primes gap `L-twin-primes-higher-power-log-mass`:
the von Mangoldt mass of prime powers `p^k` with `k ≥ 3` up to `Y` is at most a constant times
`Y^(1/3) log(2+Y)`. -/
theorem Conjectures.TwinPrimes.HigherPowerLogMass :
    let Λ := ArithmeticFunction.vonMangoldt;
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℕ, 2 ≤ Y →
      (@Finset.filter ℕ (fun n => ∃ p k : ℕ, p.Prime ∧ 3 ≤ k ∧ n = p^k)
        (fun _ => Classical.propDecidable _) (Finset.range (Y+1))).sum (fun n => Λ n)
        ≤ C*(Y:ℝ)^(1/3:ℝ)*Real.log (2+(Y:ℝ)) := by
  dsimp only
  refine ⟨400, by norm_num, ?_⟩
  intro Y hY
  classical
  set F : Finset ℕ := (@Finset.filter ℕ (fun n => ∃ p k : ℕ, p.Prime ∧ 3 ≤ k ∧ n = p^k)
      (fun _ => Classical.propDecidable _) (Finset.range (Y+1))) with hF
  set K : ℕ := Nat.log 2 Y with hK
  have hY1 : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast (by omega : 1 ≤ Y)
  have hY2 : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hYpos : (0 : ℝ) < (Y : ℝ) := by linarith
  -- per-term bound: `Λ n ≤ log Y` for `n ∈ F`
  have hterm : ∀ n ∈ F, ArithmeticFunction.vonMangoldt n ≤ Real.log (Y:ℝ) := by
    intro n hn
    rw [hF, Finset.mem_filter] at hn
    obtain ⟨hnrange, p, k, hpp, hk3, hnk⟩ := hn
    have hnY : n ≤ Y := Nat.lt_succ_iff.mp (Finset.mem_range.mp hnrange)
    have hΛ : ArithmeticFunction.vonMangoldt n = Real.log (p:ℝ) := by
      rw [hnk, ArithmeticFunction.vonMangoldt_apply_pow (by omega : k ≠ 0)]
      exact ArithmeticFunction.vonMangoldt_apply_prime hpp
    rw [hΛ]
    have hpk_le : p^k ≤ Y := by rw [← hnk]; exact hnY
    have hreal : (p:ℝ) ≤ (Y:ℝ) := by
      have h1 : (p:ℝ)^k ≤ (Y:ℝ) := by exact_mod_cast hpk_le
      have h2 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpp.one_le
      calc (p:ℝ) = (p:ℝ)^1 := (pow_one _).symm
        _ ≤ (p:ℝ)^k := pow_le_pow_right₀ h2 (by omega)
        _ ≤ (Y:ℝ) := h1
    exact Real.log_le_log (by exact_mod_cast hpp.pos) hreal
  -- key bounds on `K`
  have hKle : (K:ℝ) ≤ 2 * Real.log (Y:ℝ) := by
    have hpow : (2:ℝ)^K ≤ (Y:ℝ) := by
      rw [hK]
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : Y ≠ 0)
    have hlog : (K:ℝ) * Real.log 2 ≤ Real.log (Y:ℝ) := by
      have h := Real.log_le_log (by positivity : (0:ℝ) < (2:ℝ)^K) hpow
      rwa [Real.log_pow] at h
    have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hdiv : (K:ℝ) ≤ Real.log (Y:ℝ) / Real.log 2 := by
      rw [le_div_iff₀ hlog2]; linarith
    have hlog2half : (1/2:ℝ) ≤ Real.log 2 := log_two_ge_half
    have hlogY0 : 0 ≤ Real.log (Y:ℝ) := Real.log_nonneg hY1
    have : Real.log (Y:ℝ) / Real.log 2 ≤ 2 * Real.log (Y:ℝ) := by
      rw [div_le_iff₀ hlog2]; nlinarith
    linarith
  have hlog_bound : Real.log (Y:ℝ) ≤ 39 * (Y:ℝ) ^ ((1:ℝ)/39) := by
    have h := Real.log_le_rpow_div (x := (Y:ℝ)) (ε := (1:ℝ)/39) (le_of_lt hYpos) (by norm_num)
    have h' : (Y:ℝ) ^ ((1:ℝ)/39) / ((1:ℝ)/39) = 39 * (Y:ℝ) ^ ((1:ℝ)/39) := by
      field_simp
    rw [h'] at h
    exact h
  have hKle2 : (K:ℝ) ≤ 78 * (Y:ℝ) ^ ((1:ℝ)/39) := by nlinarith
  have hpow_le : (Y:ℝ) ^ ((1:ℝ)/39) ≤ (Y:ℝ) ^ (1/3:ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hY1
    norm_num
  have hpow_le13 : (Y:ℝ) ^ (1/13:ℝ) ≤ (Y:ℝ) ^ (1/3:ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hY1
    norm_num
  have hKpos : (1:ℝ) ≤ (K:ℝ) := by
    have : 1 ≤ K := by
      rw [hK]
      exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) (by simpa using hY)
    exact_mod_cast this
  -- `(K+1)` and `(K+1)·Y^(1/13)` bounds
  have hKplus : (K:ℝ) + 1 ≤ 156 * (Y:ℝ) ^ (1/3:ℝ) := by
    have h1 : (K:ℝ) ≤ 78 * (Y:ℝ) ^ (1/3:ℝ) := by
      calc (K:ℝ) ≤ 78 * (Y:ℝ) ^ ((1:ℝ)/39) := hKle2
        _ ≤ 78 * (Y:ℝ) ^ (1/3:ℝ) := by
            apply mul_le_mul_of_nonneg_left hpow_le (by norm_num)
    calc (K:ℝ) + 1 ≤ 2 * (K:ℝ) := by linarith
      _ ≤ 156 * (Y:ℝ) ^ (1/3:ℝ) := by nlinarith
  have hKplus13 : ((K:ℝ) + 1) * (Y:ℝ) ^ (1/13:ℝ) ≤ 156 * (Y:ℝ) ^ (1/3:ℝ) := by
    have h1 : (K:ℝ) + 1 ≤ 156 * (Y:ℝ) ^ ((1:ℝ)/39) := by
      have h2 : (K:ℝ) ≤ 78 * (Y:ℝ) ^ ((1:ℝ)/39) := hKle2
      calc (K:ℝ) + 1 ≤ 2 * (K:ℝ) := by linarith
        _ ≤ 156 * (Y:ℝ) ^ ((1:ℝ)/39) := by nlinarith
    have h2 : (Y:ℝ) ^ ((1:ℝ)/39) * (Y:ℝ) ^ (1/13:ℝ) = (Y:ℝ) ^ ((4:ℝ)/39) := by
      rw [← Real.rpow_add hYpos]
      norm_num
    calc ((K:ℝ) + 1) * (Y:ℝ) ^ (1/13:ℝ)
        ≤ (156 * (Y:ℝ) ^ ((1:ℝ)/39)) * (Y:ℝ) ^ (1/13:ℝ) := by
          apply mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 156 * ((Y:ℝ) ^ ((1:ℝ)/39) * (Y:ℝ) ^ (1/13:ℝ)) := by ring
      _ = 156 * (Y:ℝ) ^ ((4:ℝ)/39) := by rw [h2]
      _ ≤ 156 * (Y:ℝ) ^ (1/3:ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Real.rpow_le_rpow_of_exponent_le hY1
          norm_num
  -- cardinality bound
  have hcard : (F.card:ℝ) ≤ 322 * (Y:ℝ) ^ (1/3:ℝ) := by
    set P : ℕ → Finset ℕ := fun k =>
      (Finset.range (Y+1)).filter (fun p => p.Prime ∧ 3 ≤ k ∧ p^k ≤ Y) with hP
    set G : Finset (ℕ × ℕ) := (Finset.range (K+1)).biUnion
      (fun k => (P k).image (fun p => (k, p))) with hG
    have hFsub : F ⊆ G.image (fun q : ℕ × ℕ => q.2 ^ q.1) := by
      intro n hn
      rw [hF, Finset.mem_filter] at hn
      obtain ⟨hnrange, p, k, hpp, hk3, hnk⟩ := hn
      have hnY : n ≤ Y := Nat.lt_succ_iff.mp (Finset.mem_range.mp hnrange)
      have hpk_le : p^k ≤ Y := by rw [← hnk]; exact hnY
      have hk_le : k ≤ K := by
        rw [hK]
        apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
        calc 2^k ≤ p^k := Nat.pow_le_pow_left hpp.two_le k
          _ ≤ Y := hpk_le
      have hpY : p ≤ Y := by
        have hple : (p:ℝ) ≤ (Y:ℝ) := by
          have h1 : (p:ℝ)^k ≤ (Y:ℝ) := by exact_mod_cast hpk_le
          have h2 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpp.one_le
          calc (p:ℝ) = (p:ℝ)^1 := (pow_one _).symm
            _ ≤ (p:ℝ)^k := pow_le_pow_right₀ h2 (by omega)
            _ ≤ (Y:ℝ) := h1
        exact_mod_cast hple
      rw [Finset.mem_image]
      refine ⟨(k, p), ?_, hnk.symm⟩
      rw [hG]
      refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr (by omega), ?_⟩
      rw [Finset.mem_image]
      refine ⟨p, ?_, rfl⟩
      rw [hP, Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hpY), hpp, hk3, hpk_le⟩
    have h1 : F.card ≤ (G.image (fun q : ℕ × ℕ => q.2 ^ q.1)).card := Finset.card_le_card hFsub
    have h2 : (G.image (fun q : ℕ × ℕ => q.2 ^ q.1)).card ≤ G.card := Finset.card_image_le
    have h3 : G.card ≤ ∑ k ∈ Finset.range (K+1), (P k).card := by
      calc G.card ≤ ∑ k ∈ Finset.range (K+1), ((P k).image (fun p => (k, p))).card := by
            rw [hG]
            simpa using (Finset.card_biUnion_le (s := Finset.range (K+1))
              (t := fun k => (P k).image (fun p => (k, p))))
        _ ≤ ∑ k ∈ Finset.range (K+1), (P k).card :=
            Finset.sum_le_sum (fun k _ => Finset.card_image_le)
    -- bound each fiber
    have hPcard : ∀ k ∈ Finset.range (K+1),
        ((P k).card:ℝ) ≤ (if 3 ≤ k then (Y:ℝ) ^ ((1:ℝ)/(k:ℝ)) + 1 else 0) := by
      intro k _
      by_cases hk : 3 ≤ k
      · rw [if_pos hk]
        have hy0 : 0 ≤ (Y:ℝ) ^ ((1:ℝ)/(k:ℝ)) := by positivity
        have hsubk : P k ⊆ Finset.range (⌊(Y:ℝ) ^ ((1:ℝ)/(k:ℝ))⌋₊ + 1) := by
          intro p hp
          rw [hP, Finset.mem_filter] at hp
          obtain ⟨-, hpp, -, hpk⟩ := hp
          have hple : (p:ℝ) ≤ (Y:ℝ) ^ ((1:ℝ)/(k:ℝ)) :=
            le_rpow_of_pow_le hpp.one_le (by omega) hpk
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hple))
        have hcard_le : (P k).card ≤ ⌊(Y:ℝ) ^ ((1:ℝ)/(k:ℝ))⌋₊ + 1 := by
          calc (P k).card ≤ (Finset.range (⌊(Y:ℝ) ^ ((1:ℝ)/(k:ℝ))⌋₊ + 1)).card :=
                Finset.card_le_card hsubk
            _ = ⌊(Y:ℝ) ^ ((1:ℝ)/(k:ℝ))⌋₊ + 1 := Finset.card_range _
        have hfloor : ((⌊(Y:ℝ) ^ ((1:ℝ)/(k:ℝ))⌋₊ : ℕ) : ℝ) ≤ (Y:ℝ) ^ ((1:ℝ)/(k:ℝ)) :=
          Nat.floor_le hy0
        calc ((P k).card:ℝ) ≤ ((⌊(Y:ℝ) ^ ((1:ℝ)/(k:ℝ))⌋₊ + 1 : ℕ) : ℝ) := by
              exact_mod_cast hcard_le
          _ = ((⌊(Y:ℝ) ^ ((1:ℝ)/(k:ℝ))⌋₊ : ℕ) : ℝ) + 1 := by push_cast; ring
          _ ≤ (Y:ℝ) ^ ((1:ℝ)/(k:ℝ)) + 1 := by linarith
      · rw [if_neg hk]
        have hempty : P k = ∅ := by
          rw [hP, Finset.eq_empty_iff_forall_notMem]
          intro p hp
          obtain ⟨-, -, hk3, -⟩ := Finset.mem_filter.mp hp
          exact hk hk3
        rw [hempty]
        simp
    -- sum bound
    have hsum_bound : (∑ k ∈ Finset.range (K+1),
        (if 3 ≤ k then (Y:ℝ) ^ ((1:ℝ)/(k:ℝ)) + 1 else 0))
        ≤ 322 * (Y:ℝ) ^ (1/3:ℝ) := by
      set Ks : Finset ℕ := (Finset.range (K+1)).filter (fun k => 3 ≤ k) with hKs
      have hEq : (∑ k ∈ Finset.range (K+1),
          (if 3 ≤ k then (Y:ℝ) ^ ((1:ℝ)/(k:ℝ)) + 1 else 0))
          = ∑ k ∈ Ks, ((Y:ℝ) ^ ((1:ℝ)/(k:ℝ)) + 1) := by
        rw [hKs, ← Finset.sum_filter]
      rw [hEq]
      -- split into `k ≤ 12` and `k > 12`
      have hsplit1 : (∑ k ∈ Ks.filter (fun k => k ≤ 12), (Y:ℝ) ^ ((1:ℝ)/(k:ℝ)))
          ≤ 10 * (Y:ℝ) ^ (1/3:ℝ) := by
        have hterm' : ∀ k ∈ Ks.filter (fun k => k ≤ 12),
            (Y:ℝ) ^ ((1:ℝ)/(k:ℝ)) ≤ (Y:ℝ) ^ (1/3:ℝ) := by
          intro k hk
          have hkK : k ∈ Ks := (Finset.mem_filter.mp hk).1
          have hk3 : 3 ≤ k := (Finset.mem_filter.mp hkK).2
          apply Real.rpow_le_rpow_of_exponent_le hY1
          have hk3R : (3:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk3
          rw [show ((1:ℝ)/(k:ℝ)) = 1/(k:ℝ) by ring, show ((1:ℝ)/3) = 1/3 from rfl]
          exact one_div_le_one_div_of_le (by norm_num) hk3R
        have hcard10 : (Ks.filter (fun k => k ≤ 12)).card ≤ 10 := by
          have hsub' : Ks.filter (fun k => k ≤ 12) ⊆ Finset.Ico 3 13 := by
            intro k hk
            obtain ⟨hkK, hk12⟩ := Finset.mem_filter.mp hk
            obtain ⟨-, hk3⟩ := Finset.mem_filter.mp hkK
            exact Finset.mem_Ico.mpr ⟨hk3, by omega⟩
          calc (Ks.filter (fun k => k ≤ 12)).card ≤ (Finset.Ico 3 13).card :=
                Finset.card_le_card hsub'
            _ = 10 := by rw [Nat.card_Ico]
        have h := Finset.sum_le_card_nsmul (Ks.filter (fun k => k ≤ 12))
          (fun k => (Y:ℝ) ^ ((1:ℝ)/(k:ℝ))) ((Y:ℝ) ^ (1/3:ℝ)) hterm'
        rw [nsmul_eq_mul] at h
        have hc : ((Ks.filter (fun k => k ≤ 12)).card : ℝ) ≤ 10 := by exact_mod_cast hcard10
        have hnn : (0:ℝ) ≤ (Y:ℝ) ^ (1/3:ℝ) := by positivity
        calc (∑ k ∈ Ks.filter (fun k => k ≤ 12), (Y:ℝ) ^ ((1:ℝ)/(k:ℝ)))
            ≤ ((Ks.filter (fun k => k ≤ 12)).card : ℝ) * (Y:ℝ) ^ (1/3:ℝ) := h
          _ ≤ 10 * (Y:ℝ) ^ (1/3:ℝ) := by nlinarith
      have hsplit2 : (∑ k ∈ Ks.filter (fun k => ¬ k ≤ 12), (Y:ℝ) ^ ((1:ℝ)/(k:ℝ)))
          ≤ 156 * (Y:ℝ) ^ (1/3:ℝ) := by
        have hterm' : ∀ k ∈ Ks.filter (fun k => ¬ k ≤ 12),
            (Y:ℝ) ^ ((1:ℝ)/(k:ℝ)) ≤ (Y:ℝ) ^ (1/13:ℝ) := by
          intro k hk
          obtain ⟨hkK, hk12⟩ := Finset.mem_filter.mp hk
          apply Real.rpow_le_rpow_of_exponent_le hY1
          have hk13 : 13 ≤ k := by omega
          have hkpos : (0:ℝ) < (k:ℝ) := by
            have : 0 < k := by omega
            exact_mod_cast this
          have h13 : (13:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk13
          rw [show ((1:ℝ)/(k:ℝ)) = 1/(k:ℝ) by ring, show ((1:ℝ)/13) = 1/13 from rfl]
          exact one_div_le_one_div_of_le (by norm_num) h13
        have hcardK : ((Ks.filter (fun k => ¬ k ≤ 12)).card : ℝ) ≤ (K:ℝ) + 1 := by
          have hsub' : Ks.filter (fun k => ¬ k ≤ 12) ⊆ Finset.range (K+1) := by
            intro k hk
            exact (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).1
          have hc : (Ks.filter (fun k => ¬ k ≤ 12)).card ≤ K + 1 := by
            calc _ ≤ (Finset.range (K+1)).card := Finset.card_le_card hsub'
              _ = K + 1 := Finset.card_range _
          exact_mod_cast hc
        have h := Finset.sum_le_card_nsmul (Ks.filter (fun k => ¬ k ≤ 12))
          (fun k => (Y:ℝ) ^ ((1:ℝ)/(k:ℝ))) ((Y:ℝ) ^ (1/13:ℝ)) hterm'
        rw [nsmul_eq_mul] at h
        have hnn : (0:ℝ) ≤ (Y:ℝ) ^ (1/13:ℝ) := by positivity
        calc (∑ k ∈ Ks.filter (fun k => ¬ k ≤ 12), (Y:ℝ) ^ ((1:ℝ)/(k:ℝ)))
            ≤ ((Ks.filter (fun k => ¬ k ≤ 12)).card : ℝ) * (Y:ℝ) ^ (1/13:ℝ) := h
          _ ≤ ((K:ℝ) + 1) * (Y:ℝ) ^ (1/13:ℝ) := by
              apply mul_le_mul_of_nonneg_right hcardK hnn
          _ ≤ 156 * (Y:ℝ) ^ (1/3:ℝ) := hKplus13
      have hsumK : (∑ k ∈ Ks, (Y:ℝ) ^ ((1:ℝ)/(k:ℝ)))
          ≤ 166 * (Y:ℝ) ^ (1/3:ℝ) := by
        rw [← Finset.sum_filter_add_sum_filter_not Ks (fun k => k ≤ 12)
          (fun k => (Y:ℝ) ^ ((1:ℝ)/(k:ℝ)))]
        have := hsplit1
        linarith
      have hcardKs : ((Ks.card : ℕ) : ℝ) ≤ 156 * (Y:ℝ) ^ (1/3:ℝ) := by
        have hc : Ks.card ≤ K + 1 := by
          calc Ks.card ≤ (Finset.range (K+1)).card := Finset.card_le_card (by
                intro k hk; exact (Finset.mem_filter.mp hk).1)
            _ = K + 1 := Finset.card_range _
        calc ((Ks.card : ℕ) : ℝ) ≤ ((K:ℝ) + 1) := by exact_mod_cast hc
          _ ≤ 156 * (Y:ℝ) ^ (1/3:ℝ) := hKplus
      have hsum1 : (∑ k ∈ Ks, (1:ℝ)) = ((Ks.card : ℕ) : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [Finset.sum_add_distrib, hsum1]
      linarith [hsumK, hcardKs]
    calc (F.card:ℝ) ≤ ((G.image (fun q : ℕ × ℕ => q.2 ^ q.1)).card : ℝ) := by exact_mod_cast h1
      _ ≤ (G.card:ℝ) := by exact_mod_cast h2
      _ ≤ ((∑ k ∈ Finset.range (K+1), (P k).card) : ℝ) := by exact_mod_cast h3
      _ = ∑ k ∈ Finset.range (K+1), ((P k).card:ℝ) := by push_cast; ring
      _ ≤ ∑ k ∈ Finset.range (K+1),
            (if 3 ≤ k then (Y:ℝ) ^ ((1:ℝ)/(k:ℝ)) + 1 else 0) :=
          Finset.sum_le_sum hPcard
      _ ≤ 322 * (Y:ℝ) ^ (1/3:ℝ) := hsum_bound
  -- assemble
  have hlogY : 0 ≤ Real.log (Y:ℝ) := Real.log_nonneg hY1
  have hS1 : (F.sum fun n => ArithmeticFunction.vonMangoldt n) ≤ (F.card:ℝ) * Real.log (Y:ℝ) := by
    calc F.sum (fun n => ArithmeticFunction.vonMangoldt n)
        ≤ F.sum (fun _ => Real.log (Y:ℝ)) := Finset.sum_le_sum hterm
      _ = (F.card:ℝ) * Real.log (Y:ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hlog_le : Real.log (Y:ℝ) ≤ Real.log (2+(Y:ℝ)) := by
    apply Real.log_le_log hYpos
    linarith
  have hlogpos : 0 ≤ Real.log (2+(Y:ℝ)) := Real.log_nonneg (by linarith)
  have hA : (0:ℝ) ≤ (Y:ℝ) ^ (1/3:ℝ) := by positivity
  calc (F.sum fun n => ArithmeticFunction.vonMangoldt n)
      ≤ (F.card:ℝ) * Real.log (Y:ℝ) := hS1
    _ ≤ (322 * (Y:ℝ) ^ (1/3:ℝ)) * Real.log (Y:ℝ) := by
        apply mul_le_mul_of_nonneg_right hcard hlogY
    _ ≤ (400 * (Y:ℝ) ^ (1/3:ℝ)) * Real.log (2+(Y:ℝ)) := by
        have h322 : (322:ℝ) * (Y:ℝ) ^ (1/3:ℝ) * Real.log (Y:ℝ)
            ≤ 400 * (Y:ℝ) ^ (1/3:ℝ) * Real.log (Y:ℝ) := by nlinarith [mul_nonneg hA hlogY]
        have hstep : (400:ℝ) * (Y:ℝ) ^ (1/3:ℝ) * Real.log (Y:ℝ)
            ≤ 400 * (Y:ℝ) ^ (1/3:ℝ) * Real.log (2+(Y:ℝ)) := by
          apply mul_le_mul_of_nonneg_left hlog_le
          positivity
        linarith
    _ = 400*(Y:ℝ)^(1/3:ℝ)*Real.log (2+(Y:ℝ)) := by ring

namespace Conjectures.TwinPrimes.CofactorTwoLinearSieve_aux


/-!
The finite Goldbach Selberg sieve and smooth-number Euler product bounds below are adapted
from OpenAI, openai/math (Apache License 2.0), revision 3344da59991ed94f9ba711217b29c1d760badfa6.
https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/NumberTheory/EgyptianFractions
The modules are combined for verification with the pinned toolchain. The cutoff and denominator estimates are derived here.
-/

-- Upstream module OAI.NumberTheory.EgyptianFractions.SelbergOptimal

namespace OAI
noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius
open Finset ArithmeticFunction

namespace Problem337.SelbergOptimal

/-- Complementation turns a sum over multiples among divisors into a divisor sum. -/
theorem sum_multiples_complement (P l : ℕ) (hP : P ≠ 0) (hl : l ∣ P)
    (f : ℕ → ℝ) :
    (∑ d ∈ P.divisors, if l ∣ d then f (P / d) else 0) =
      ∑ d ∈ (P / l).divisors, f d := by
  calc
    _ = ∑ d ∈ P.divisors, if l ∣ P / d then f d else 0 := by
      rw [← Nat.sum_div_divisors P (fun d => if l ∣ d then f (P / d) else 0)]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hP]
    _ = ∑ d ∈ (P / l).divisors, f d := by
      rw [← Finset.sum_filter]
      congr 1
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hd, _⟩, hld⟩
        refine ⟨?_, Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) hl)
          (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP hl)))⟩
        apply (Nat.dvd_div_iff_mul_dvd hl).2
        rw [Nat.mul_comm]
        exact (Nat.dvd_div_iff_mul_dvd hd).1 hld
      · rintro ⟨hd, _⟩
        have hdP : d ∣ P := hd.trans (Nat.div_dvd_of_dvd hl)
        refine ⟨⟨hdP, hP⟩, ?_⟩
        apply (Nat.dvd_div_iff_mul_dvd hdP).2
        rw [Nat.mul_comm]
        exact (Nat.dvd_div_iff_mul_dvd hl).1 hd

/-- Inverse of the upper divisor-sum transform, expressed through ordinary
Möbius inversion after complementing divisors. -/
def upperInverse (P : ℕ) (y : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ x ∈ (P / d).divisorsAntidiagonal, (μ x.1 : ℝ) * y (P / x.2)

theorem sum_upperInverse (P l : ℕ) (hP : P ≠ 0) (hl : l ∣ P)
    (y : ℕ → ℝ) :
    (∑ d ∈ P.divisors, if l ∣ d then upperInverse P y d else 0) = y l := by
  let f : ℕ → ℝ := fun n =>
    ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℝ) * y (P / x.2)
  have hmob : ∀ n > 0, ∑ d ∈ n.divisors, f d = y (P / n) := by
    apply ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mpr
    intro n hn
    rfl
  change (∑ d ∈ P.divisors, if l ∣ d then f (P / d) else 0) = y l
  rw [sum_multiples_complement P l hP hl f]
  rw [hmob (P / l) (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) hl)
    (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP hl)))]
  rw [Nat.div_div_self hl hP]

theorem upperInverse_one (P : ℕ) (hP : P ≠ 0) (y : ℕ → ℝ) :
    upperInverse P y 1 = ∑ d ∈ P.divisors, (μ d : ℝ) * y d := by
  unfold upperInverse
  rw [Nat.div_one, Nat.sum_divisorsAntidiagonal (f := fun d e => (μ d : ℝ) * y (P / e))]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hP]

/-- The positive finite normalizing sum of the optimal Selberg weights. -/
def normalizer (s : BoundingSieve) (z : ℕ) : ℝ :=
  ∑ d ∈ s.prodPrimes.divisors, if d ≤ z then s.selbergTerms d else 0

theorem normalizer_pos (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    0 < normalizer s z := by
  apply Finset.sum_pos'
  · intro d hd
    split_ifs
    · exact (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hd)).le
    · exact le_rfl
  · refine ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, s.prodPrimes_ne_zero⟩, ?_⟩
    rw [ite_eq_left hz]
    exact s.selbergTerms_pos (one_dvd _)

/-- The diagonal coordinates attaining the constrained minimum. -/
def optimalDiagonal (s : BoundingSieve) (z d : ℕ) : ℝ :=
  if d ≤ z then (μ d : ℝ) * s.selbergTerms d / normalizer s z else 0

/-- Selberg weights obtained by upper Möbius inversion. -/
def optimalWeight (s : BoundingSieve) (z d : ℕ) : ℝ :=
  if d ∣ s.prodPrimes then
    upperInverse s.prodPrimes (optimalDiagonal s z) d / s.nu d else 0

theorem optimalWeight_transform (s : BoundingSieve) (z l : ℕ)
    (hl : l ∣ s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors,
      if l ∣ d then s.nu d * optimalWeight s z d else 0) =
      optimalDiagonal s z l := by
  calc
    _ = ∑ d ∈ s.prodPrimes.divisors,
        if l ∣ d then upperInverse s.prodPrimes (optimalDiagonal s z) d else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdP := Nat.dvd_of_mem_divisors hd
      rw [optimalWeight, ite_eq_left hdP]
      have hnu := s.nu_ne_zero hdP
      congr 1
      field_simp
    _ = _ := sum_upperInverse _ _ s.prodPrimes_ne_zero hl _

theorem optimalWeight_one (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    optimalWeight s z 1 = 1 := by
  rw [optimalWeight, ite_eq_left (one_dvd _), s.nu_mult.map_one, div_one,
    upperInverse_one _ s.prodPrimes_ne_zero]
  have hG : normalizer s z ≠ 0 := (normalizer_pos s hz).ne'
  calc
    _ = (∑ d ∈ s.prodPrimes.divisors,
        if d ≤ z then s.selbergTerms d else 0) / normalizer s z := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d hd
      have hmu : (μ d : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
          (s.squarefree_of_mem_divisors_prodPrimes hd)
      unfold optimalDiagonal
      split_ifs with he
      · rw [mul_div_assoc, ← mul_assoc, ← pow_two, hmu, one_mul]
      · simp
    _ = 1 := div_self hG

/-- The diagonalized main term at the optimal weights is exactly the
reciprocal of the finite Selberg normalizer. -/
theorem mainSum_optimalWeight (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    s.mainSum (BoundingSieve.lambdaSquared (optimalWeight s z)) =
      1 / normalizer s z := by
  rw [s.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  have hG : normalizer s z ≠ 0 := (normalizer_pos s hz).ne'
  calc
    _ = (∑ d ∈ s.prodPrimes.divisors,
        if d ≤ z then s.selbergTerms d else 0) / normalizer s z ^ 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d hd
      have hdP := Nat.dvd_of_mem_divisors hd
      have hg : s.selbergTerms d ≠ 0 := (s.selbergTerms_pos hdP).ne'
      have hmu : (μ d : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
          (s.squarefree_of_mem_divisors_prodPrimes hd)
      rw [optimalWeight_transform s z d hdP]
      unfold optimalDiagonal
      split_ifs with he
      · rw [div_pow, mul_pow, hmu, one_mul]
        field_simp
      · simp
    _ = 1 / normalizer s z := by
      change normalizer s z / normalizer s z ^ 2 = _
      field_simp

/-- The Selberg upper-bound sieve with its main term optimized. -/
theorem siftedSum_le (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    s.siftedSum ≤ s.totalMass / normalizer s z +
      s.errSum (BoundingSieve.lambdaSquared (optimalWeight s z)) := by
  have h := s.siftedSum_le_mainSum_errSum_of_upperMoebius
    (BoundingSieve.lambdaSquared (optimalWeight s z))
    (BoundingSieve.upperMoebius_lambdaSquared _ (optimalWeight_one s hz))
  rw [mainSum_optimalWeight s hz, mul_one_div] at h
  exact h

/-- No optimal weight lies above the chosen truncation. -/
theorem optimalWeight_eq_zero_of_lt (s : BoundingSieve) {z d : ℕ} (hzd : z < d) :
    optimalWeight s z d = 0 := by
  unfold optimalWeight
  split_ifs with hdP
  · suffices upperInverse s.prodPrimes (optimalDiagonal s z) d = 0 by rw [this, zero_div]
    unfold upperInverse
    apply Finset.sum_eq_zero
    intro x hx
    have hx2 : x.2 ∣ s.prodPrimes / d :=
      Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)
    have hxP : x.2 ∣ s.prodPrimes := hx2.trans (Nat.div_dvd_of_dvd hdP)
    have hdx : d ∣ s.prodPrimes / x.2 := by
      apply (Nat.dvd_div_iff_mul_dvd hxP).2
      rw [Nat.mul_comm]
      exact (Nat.dvd_div_iff_mul_dvd hdP).1 hx2
    have hpos : 0 < s.prodPrimes / x.2 :=
      Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero s.prodPrimes_ne_zero) hxP)
        (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hxP))
    have hlong : z < s.prodPrimes / x.2 := hzd.trans_le (Nat.le_of_dvd hpos hdx)
    simp [optimalDiagonal, not_le.mpr hlong]
  · rfl

/-- Upper Möbius inversion does not increase the crude full-divisor
absolute-mass bound. This estimate is independent of squarefreeness. -/
theorem abs_upperInverse_le (P d : ℕ) (hP : P ≠ 0) (hd : d ∣ P)
    (y : ℕ → ℝ) :
    |upperInverse P y d| ≤ ∑ e ∈ P.divisors, |y e| := by
  unfold upperInverse
  rw [Nat.sum_divisorsAntidiagonal' (f := fun a b => (μ a : ℝ) * y (P / b))]
  calc
    _ ≤ ∑ e ∈ (P / d).divisors, |(μ ((P / d) / e) : ℝ) * y (P / e)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ (P / d).divisors, |y (P / e)| := by
      apply Finset.sum_le_sum
      intro e he
      have hmu : |(μ ((P / d) / e) : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := (P / d) / e)
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_right hmu (abs_nonneg (y (P / e)))
    _ ≤ ∑ e ∈ P.divisors, |y (P / e)| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        exact Nat.mem_divisors.mpr
          ⟨(Nat.dvd_of_mem_divisors he).trans (Nat.div_dvd_of_dvd hd), hP⟩
      · intro e he hnot
        exact abs_nonneg _
    _ = _ := Nat.sum_div_divisors P (fun e => |y e|)

/-- The optimal diagonal coordinates have total absolute mass one. -/
theorem sum_abs_optimalDiagonal (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    (∑ d ∈ s.prodPrimes.divisors, |optimalDiagonal s z d|) = 1 := by
  have hG := normalizer_pos s hz
  calc
    _ = (∑ d ∈ s.prodPrimes.divisors,
        if d ≤ z then s.selbergTerms d else 0) / normalizer s z := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d hd
      have hg := s.selbergTerms_pos (Nat.dvd_of_mem_divisors hd)
      have hmu : |(μ d : ℝ)| = 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree
          (s.squarefree_of_mem_divisors_prodPrimes hd)
      unfold optimalDiagonal
      split_ifs
      · rw [abs_div, abs_mul, hmu, abs_of_pos hg, abs_of_pos hG, one_mul]
      · simp
    _ = 1 := div_self hG.ne'

/-- A coefficient bound adequate for polynomial-error applications of the sieve. -/
theorem abs_optimalWeight_le (s : BoundingSieve) {z d : ℕ} (hz : 1 ≤ z)
    (hd : d ∣ s.prodPrimes) :
    |optimalWeight s z d| ≤ (s.nu d)⁻¹ := by
  rw [optimalWeight, ite_eq_left hd, abs_div, abs_of_pos (s.nu_pos_of_dvd_prodPrimes hd)]
  have h := abs_upperInverse_le s.prodPrimes d s.prodPrimes_ne_zero hd
    (optimalDiagonal s z)
  rw [sum_abs_optimalDiagonal s hz] at h
  simpa only [one_div] using div_le_div_of_nonneg_right h
    (s.nu_pos_of_dvd_prodPrimes hd).le

/-- The upper inverse in the more usual sum-over-multiples form. -/
theorem upperInverse_eq_sum_multiples (P d : ℕ) (hP : P ≠ 0) (hd : d ∣ P)
    (y : ℕ → ℝ) :
    upperInverse P y d =
      ∑ e ∈ P.divisors, if d ∣ e then (μ (e / d) : ℝ) * y e else 0 := by
  unfold upperInverse
  rw [Nat.sum_divisorsAntidiagonal' (f := fun a b => (μ a : ℝ) * y (P / b)),
    ← sum_multiples_complement P d hP hd
      (fun e => (μ ((P / d) / e) : ℝ) * y (P / e))]
  apply Finset.sum_congr rfl
  intro e he
  have heP := Nat.dvd_of_mem_divisors he
  rw [Nat.div_div_self heP hP]
  split_ifs with hde
  · have hPe : 0 < P / e := Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) heP)
      (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP heP))
    have hquot : (P / d) / (P / e) = e / d := by
      rw [← Nat.div_mul_div heP hde, Nat.mul_comm, Nat.mul_div_cancel _ hPe]
    rw [hquot]
  · rfl

/-- Divisor multiples are parametrized by the complementary quotient. -/
theorem sum_multiples_eq (P d : ℕ) (hP : P ≠ 0) (hd : d ∣ P)
    (f : ℕ → ℝ) :
    (∑ e ∈ P.divisors, if d ∣ e then f e else 0) =
      ∑ t ∈ (P / d).divisors, f (d * t) := by
  calc
    _ = ∑ e ∈ P.divisors, if d ∣ e then f (P / (P / e)) else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      rw [Nat.div_div_self (Nat.dvd_of_mem_divisors he) hP]
    _ = ∑ t ∈ (P / d).divisors, f (P / t) :=
      sum_multiples_complement P d hP hd (fun t => f (P / t))
    _ = ∑ t ∈ (P / d).divisors, f (d * t) := by
      rw [← Nat.sum_div_divisors (P / d) (fun t => f (P / t))]
      apply Finset.sum_congr rfl
      intro t ht
      have htQ := Nat.dvd_of_mem_divisors ht
      have hQpos : 0 < P / d := Nat.div_pos
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) hd)
        (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP hd))
      have hQt : 0 < (P / d) / t := Nat.div_pos (Nat.le_of_dvd hQpos htQ)
        (Nat.pos_of_mem_divisors ht)
      have hprod : ((P / d) / t) * (d * t) = P := by
        calc
          _ = d * (((P / d) / t) * t) := by ring
          _ = d * (P / d) := by rw [Nat.div_mul_cancel htQ]
          _ = P := Nat.mul_div_cancel' hd
      congr 1
      conv_lhs => arg 1; rw [← hprod]
      exact Nat.mul_div_cancel_left (d * t) hQt

/-- The two Möbius signs from upper inversion collapse on squarefree divisors. -/
theorem moebius_div_mul (e d : ℕ) (he : Squarefree e) (hd : d ∣ e) :
    (μ (e / d) : ℝ) * (μ e : ℝ) = (μ d : ℝ) := by
  have hm : d * (e / d) = e := Nat.mul_div_cancel' hd
  have hcop : d.Coprime (e / d) := Nat.coprime_of_squarefree_mul (hm.symm ▸ he)
  have hmu := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  rw [hm] at hmu
  have heq : (μ e : ℝ) = (μ d : ℝ) * (μ (e / d) : ℝ) := by exact_mod_cast hmu
  have hsquare : (μ (e / d) : ℝ) ^ 2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
      (he.squarefree_of_dvd (Nat.div_dvd_of_dvd hd))
  rw [heq]
  calc
    _ = (μ d : ℝ) * (μ (e / d) : ℝ) ^ 2 := by ring
    _ = _ := by rw [hsquare, mul_one]

/-- The truncated normalizer on complementary divisors. -/
def complementNormalizer (s : BoundingSieve) (z d : ℕ) : ℝ :=
  ∑ t ∈ (s.prodPrimes / d).divisors, if t ≤ z / d then s.selbergTerms t else 0

/-- Explicit classical formula for the optimal coefficient. In particular,
the sign is the Möbius sign and the remaining factors are nonnegative. -/
theorem optimalWeight_formula (s : BoundingSieve) (z d : ℕ)
    (hd : d ∣ s.prodPrimes) :
    optimalWeight s z d = (μ d : ℝ) * s.selbergTerms d / s.nu d *
      (complementNormalizer s z d / normalizer s z) := by
  rw [optimalWeight, ite_eq_left hd,
    upperInverse_eq_sum_multiples _ _ s.prodPrimes_ne_zero hd]
  have hdpos : 0 < d := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hd)
  have hsum :
      (∑ e ∈ s.prodPrimes.divisors,
        if d ∣ e then (μ (e / d) : ℝ) * optimalDiagonal s z e else 0) =
      (μ d : ℝ) / normalizer s z *
        (s.selbergTerms d * complementNormalizer s z d) := by
    calc
      _ = (μ d : ℝ) / normalizer s z *
          (∑ e ∈ s.prodPrimes.divisors,
            if d ∣ e then (if e ≤ z then s.selbergTerms e else 0) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        by_cases hde : d ∣ e
        · rw [ite_eq_left hde, ite_eq_left hde]
          unfold optimalDiagonal
          split_ifs with hez
          · rw [mul_div_assoc, ← mul_assoc,
              moebius_div_mul e d (s.squarefree_of_mem_divisors_prodPrimes he) hde]
            ring
          · simp
        · simp [hde]
      _ = (μ d : ℝ) / normalizer s z *
          (∑ t ∈ (s.prodPrimes / d).divisors,
            if d * t ≤ z then s.selbergTerms (d * t) else 0) := by
        rw [sum_multiples_eq _ _ s.prodPrimes_ne_zero hd]
      _ = _ := by
        congr 1
        unfold complementNormalizer
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        have htQ := Nat.dvd_of_mem_divisors ht
        have hdt : d * t ∣ s.prodPrimes := by
          simpa [Nat.mul_comm] using (Nat.dvd_div_iff_mul_dvd hd).1 htQ
        have hcop : d.Coprime t := Nat.coprime_of_squarefree_mul
          (s.squarefree_of_dvd_prodPrimes hdt)
        have hiff : d * t ≤ z ↔ t ≤ z / d := by
          rw [Nat.le_div_iff_mul_le hdpos, Nat.mul_comm]
        simp only [hiff]
        split_ifs
        · exact s.selbergTerms_isMultiplicative.map_mul_of_coprime hcop
        · simp
  rw [hsum]
  ring

end Problem337.SelbergOptimal

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.SelbergWeightBound

namespace OAI
noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius
open Finset

namespace Problem337.SelbergOptimal

/-- Summation over the divisors of a coprime product has no multiplicities. -/
theorem sum_coprime_divisors {a b : ℕ} (hab : a.Coprime b) (f : ℕ → ℝ) :
    (∑ d ∈ (a * b).divisors, f d) =
      ∑ e ∈ a.divisors, ∑ t ∈ b.divisors, f (e * t) := by
  rw [hab.divisors_mul]
  simp only [sum_map]
  exact (sum_attach (a.divisors ×ˢ b.divisors)
    (fun p : ℕ × ℕ => f (p.1 * p.2))).trans (sum_product _ _ _)

/-- The complementary divisor of a squarefree integer is coprime to it. -/
theorem coprime_complement (s : BoundingSieve) {d : ℕ} (hd : d ∣ s.prodPrimes) :
    d.Coprime (s.prodPrimes / d) := by
  apply Nat.coprime_of_squarefree_mul
  simpa only [Nat.mul_div_cancel' hd] using s.prodPrimes_squarefree

/-- Split the finite Selberg normalizer at a divisor of the sieving product. -/
theorem normalizer_decompose (s : BoundingSieve) (z : ℕ) {d : ℕ}
    (hd : d ∣ s.prodPrimes) :
    normalizer s z =
      ∑ e ∈ d.divisors, ∑ t ∈ (s.prodPrimes / d).divisors,
        if e * t ≤ z then s.selbergTerms e * s.selbergTerms t else 0 := by
  have hcop := coprime_complement s hd
  unfold normalizer
  conv_lhs => rw [← Nat.mul_div_cancel' hd]
  rw [sum_coprime_divisors hcop]
  apply sum_congr rfl
  intro e he
  apply sum_congr rfl
  intro t ht
  rw [s.selbergTerms_isMultiplicative.map_mul_of_coprime
    (hcop.coprime_dvd_left (Nat.dvd_of_mem_divisors he) |>.coprime_dvd_right
      (Nat.dvd_of_mem_divisors ht))]

theorem sum_selbergTerms_divisors (s : BoundingSieve) {d : ℕ}
    (hd : d ∣ s.prodPrimes) :
    (∑ e ∈ d.divisors, s.selbergTerms e) = s.selbergTerms d / s.nu d := by
  have h := s.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hd
  rw [← sum_filter, Nat.divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero hd] at h
  simpa only [div_eq_mul_inv] using h

/-- The positive numerator of an optimal Selberg weight is a subsum of the
normalizer, after splitting into complementary divisor coordinates. -/
theorem truncated_complement_sum_le_normalizer (s : BoundingSieve) (z : ℕ)
    {d : ℕ} (hd : d ∣ s.prodPrimes) :
    (s.selbergTerms d / s.nu d) *
        (∑ t ∈ (s.prodPrimes / d).divisors,
          if d * t ≤ z then s.selbergTerms t else 0) ≤ normalizer s z := by
  rw [← sum_selbergTerms_divisors s hd, sum_mul,
    normalizer_decompose s z hd]
  apply sum_le_sum
  intro e he
  rw [mul_sum]
  apply sum_le_sum
  intro t ht
  have heP := (Nat.dvd_of_mem_divisors he).trans hd
  have htP := (Nat.dvd_of_mem_divisors ht).trans (Nat.div_dvd_of_dvd hd)
  have he0 := (s.selbergTerms_pos heP).le
  have ht0 := (s.selbergTerms_pos htP).le
  by_cases hdt : d * t ≤ z
  · have het : e * t ≤ z :=
      (Nat.mul_le_mul_right t (Nat.le_of_dvd
        (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hd))
        (Nat.dvd_of_mem_divisors he))).trans hdt
    simp only [ite_eq_left hdt, ite_eq_left het, le_refl]
  · simp only [ite_eq_right hdt, mul_zero]
    split_ifs <;> positivity

/-- The same bound in the quotient-cutoff form used in the explicit weights. -/
theorem truncated_div_sum_le_normalizer (s : BoundingSieve) (z : ℕ)
    {d : ℕ} (hd : d ∣ s.prodPrimes) :
    (s.selbergTerms d / s.nu d) *
        (∑ t ∈ (s.prodPrimes / d).divisors,
          if t ≤ z / d then s.selbergTerms t else 0) ≤ normalizer s z := by
  have hd0 : 0 < d :=
    Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hd)
  simpa only [Nat.le_div_iff_mul_le hd0, Nat.mul_comm] using
    truncated_complement_sum_le_normalizer s z hd

/-- The normalized explicit optimal-weight expression has absolute value at
most one. This bound is independent of the local sieve dimension. -/
theorem abs_normalized_complement_le_one (s : BoundingSieve) {z : ℕ}
    (hz : 1 ≤ z) {d : ℕ} (hd : d ∣ s.prodPrimes) :
    |(μ d : ℝ) * (s.selbergTerms d / s.nu d) /
        normalizer s z *
        (∑ t ∈ (s.prodPrimes / d).divisors,
          if t ≤ z / d then s.selbergTerms t else 0)| ≤ 1 := by
  have hG := normalizer_pos s hz
  have hnu := s.nu_pos_of_dvd_prodPrimes hd
  have hg := s.selbergTerms_pos hd
  have hsum : 0 ≤ ∑ t ∈ (s.prodPrimes / d).divisors,
      if t ≤ z / d then s.selbergTerms t else 0 := by
    apply sum_nonneg
    intro t ht
    split_ifs
    · exact (s.selbergTerms_pos ((Nat.dvd_of_mem_divisors ht).trans
        (Nat.div_dvd_of_dvd hd))).le
    · exact le_rfl
  have hmu : |(μ d : ℝ)| = 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree
      (s.squarefree_of_dvd_prodPrimes hd)
  rw [abs_mul, abs_div, abs_mul, hmu, one_mul,
    abs_of_pos (div_pos hg hnu), abs_of_pos hG, abs_of_nonneg hsum]
  rw [div_mul_eq_mul_div, div_le_one hG]
  exact truncated_div_sum_le_normalizer s z hd

end Problem337.SelbergOptimal

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.SelbergErrorBound

namespace OAI
/-!
# Remainder control for the Selberg square sieve

The estimates here retain the actual local remainder.  In particular no
prime distribution hypothesis is manufactured by passing to square weights.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace Problem337.SelbergError

/-- A weighted version of the divisor expansion of the square sieve. -/
theorem sum_lambdaSquared_mul (P : ℕ) (hP : P ≠ 0)
    (lam f : ℕ → ℝ) :
    (∑ d ∈ P.divisors, BoundingSieve.lambdaSquared lam d * f d) =
      ∑ a ∈ P.divisors, ∑ b ∈ P.divisors,
        lam a * lam b * f (Nat.lcm a b) := by
  have henlarge (g : ℕ → ℕ → ℕ → ℝ) :
      (∑ d ∈ P.divisors, ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
        if d = Nat.lcm a b then g a b d else 0) =
      ∑ d ∈ P.divisors, ∑ a ∈ P.divisors, ∑ b ∈ P.divisors,
        if d = Nat.lcm a b then g a b d else 0 := by
    congr! 1 with d hd
    rw [Nat.mem_divisors] at hd
    have heq : ∀ a b, (a ∣ d ∧ b ∣ d ∧ d = Nat.lcm a b) =
        (d = Nat.lcm a b) := by
      simp +contextual [← and_assoc, Nat.dvd_lcm_left, Nat.dvd_lcm_right]
    simp_rw [← Nat.divisors_filter_dvd_of_dvd hd.2 hd.1,
      sum_filter, ite_sum_zero, ← ite_and, heq]
  calc
    _ = ∑ d ∈ P.divisors, ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
        if d = Nat.lcm a b then lam a * lam b * f d else 0 := by
      simp [BoundingSieve.lambdaSquared, sum_mul]
    _ = ∑ d ∈ P.divisors, ∑ a ∈ P.divisors, ∑ b ∈ P.divisors,
        if d = Nat.lcm a b then lam a * lam b * f d else 0 := henlarge _
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro a ha
      rw [sum_comm]
      apply sum_congr rfl
      intro b hb
      have hlcm : Nat.lcm a b ∈ P.divisors :=
        Nat.mem_divisors.mpr ⟨Nat.lcm_dvd_iff.mpr
          ⟨Nat.dvd_of_mem_divisors ha, Nat.dvd_of_mem_divisors hb⟩, hP⟩
      rw [sum_ite_eq_of_mem' _ _ _ hlcm]

/-- Absolute square weights are dominated by the square weights of absolute
values.  This inequality does not assume that the original weights are positive. -/
theorem abs_lambdaSquared_le (lam : ℕ → ℝ) (d : ℕ) :
    |BoundingSieve.lambdaSquared lam d| ≤
      BoundingSieve.lambdaSquared (fun n => |lam n|) d := by
  unfold BoundingSieve.lambdaSquared
  calc
    _ ≤ ∑ a ∈ d.divisors, |∑ b ∈ d.divisors,
        if d = Nat.lcm a b then lam a * lam b else 0| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ d.divisors, ∑ b ∈ d.divisors,
        |if d = Nat.lcm a b then lam a * lam b else 0| := by
      apply sum_le_sum
      intro a ha
      exact abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_ite, abs_mul, abs_zero]

/-- Exact local remainders can be bounded before any uniform estimate is made. -/
theorem errSum_lambdaSquared_le (s : BoundingSieve) (lam : ℕ → ℝ) :
    s.errSum (BoundingSieve.lambdaSquared lam) ≤
      ∑ a ∈ s.prodPrimes.divisors, ∑ b ∈ s.prodPrimes.divisors,
        |lam a| * |lam b| * |s.rem (Nat.lcm a b)| := by
  calc
    _ ≤ ∑ d ∈ s.prodPrimes.divisors,
        BoundingSieve.lambdaSquared (fun n => |lam n|) d * |s.rem d| := by
      apply sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_right (abs_lambdaSquared_le lam d) (abs_nonneg _)
    _ = _ := sum_lambdaSquared_mul s.prodPrimes
      BoundingSieve.prodPrimes_ne_zero _ _

/-- A factorizable local remainder envelope gives the usual weighted L1-square
bound for the square-sieve error. -/
theorem errSum_lambdaSquared_le_sq (s : BoundingSieve) (lam w : ℕ → ℝ)
    (hrem : ∀ a ∈ s.prodPrimes.divisors, ∀ b ∈ s.prodPrimes.divisors,
      |s.rem (Nat.lcm a b)| ≤ w a * w b) :
    s.errSum (BoundingSieve.lambdaSquared lam) ≤
      (∑ d ∈ s.prodPrimes.divisors, |lam d| * w d) ^ 2 := by
  calc
    _ ≤ ∑ a ∈ s.prodPrimes.divisors, ∑ b ∈ s.prodPrimes.divisors,
        |lam a| * |lam b| * |s.rem (Nat.lcm a b)| := errSum_lambdaSquared_le s lam
    _ ≤ ∑ a ∈ s.prodPrimes.divisors, ∑ b ∈ s.prodPrimes.divisors,
        |lam a| * |lam b| * (w a * w b) := by
      apply sum_le_sum
      intro a ha
      apply sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (hrem a ha b hb) (by positivity)
    _ = _ := by
      rw [sq, sum_mul_sum]
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      ring

end Problem337.SelbergError

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.DivisorTupleBounds

namespace OAI
/-!
# Elementary summatory bounds for divisor tuples

These finite hyperbola estimates supply logarithmic remainder bounds for
square sieves.  They do not use a prime number theorem.
-/
noncomputable section
open scoped BigOperators
open Finset

namespace Problem337.SelbergError

/-- Ordered positive factor tuples, expressed by Dirichlet powers of zeta. -/
def divisorTupleCount (k n : ℕ) : ℕ :=
  (ArithmeticFunction.zeta ^ k) n

private lemma sum_divisorsAntidiagonal_le_rectangle (N : ℕ)
    (F : ℕ × ℕ → ℝ) (hF : ∀ x, 0 ≤ F x) :
    (∑ n ∈ Icc 1 N, ∑ x ∈ n.divisorsAntidiagonal, F x) ≤
      ∑ x ∈ Icc 1 N ×ˢ Icc 1 N, F x := by
  have hdisj : Set.PairwiseDisjoint (Icc 1 N : Finset ℕ)
      Nat.divisorsAntidiagonal := by
    intro n hn m hm hnm
    apply disjoint_left.mpr
    intro x hxn hxm
    exact hnm ((Nat.mem_divisorsAntidiagonal.mp hxn).1.symm.trans
      (Nat.mem_divisorsAntidiagonal.mp hxm).1)
  rw [← sum_biUnion hdisj]
  apply sum_le_sum_of_subset_of_nonneg
  · intro x hx
    obtain ⟨n, hn, hxn⟩ := mem_biUnion.mp hx
    obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hxn
    have ha : 0 < x.1 := by
      by_contra h
      have : x.1 = 0 := by omega
      simp [this] at hprod
      omega
    have hb : 0 < x.2 := by
      by_contra h
      have : x.2 = 0 := by omega
      simp [this] at hprod
      omega
    have haN : x.1 ≤ N := (Nat.le_of_dvd (by omega : 0 < n)
      ⟨x.2, hprod.symm⟩).trans (mem_Icc.mp hn).2
    have hbN : x.2 ≤ N := (Nat.le_of_dvd (by omega : 0 < n)
      ⟨x.1, by simpa [Nat.mul_comm] using hprod.symm⟩).trans (mem_Icc.mp hn).2
    exact mem_product.mpr ⟨mem_Icc.mpr ⟨ha, haN⟩, mem_Icc.mpr ⟨hb, hbN⟩⟩
  · intro x hx hxnot
    exact hF x

/-- The harmonic norm on an initial interval is submultiplicative for
Dirichlet convolution of nonnegative arithmetic functions. -/
theorem harmonic_convolution_le (f g : ArithmeticFunction ℕ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ((f * g) n : ℝ) / n) ≤
      (∑ a ∈ Icc 1 N, (f a : ℝ) / a) *
      (∑ b ∈ Icc 1 N, (g b : ℝ) / b) := by
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ x ∈ n.divisorsAntidiagonal,
        ((f x.1 : ℝ) / x.1) * ((g x.2 : ℝ) / x.2) := by
      apply sum_congr rfl
      intro n hn
      rw [ArithmeticFunction.mul_apply, Nat.cast_sum, sum_div]
      apply sum_congr rfl
      intro x hx
      have hp := (Nat.mem_divisorsAntidiagonal.mp hx).1
      rw [Nat.cast_mul, ← hp, Nat.cast_mul]
      ring
    _ ≤ ∑ x ∈ Icc 1 N ×ˢ Icc 1 N,
        ((f x.1 : ℝ) / x.1) * ((g x.2 : ℝ) / x.2) :=
      sum_divisorsAntidiagonal_le_rectangle N _ (by intro x; positivity)
    _ = _ := by rw [sum_product, sum_mul_sum]

lemma zeta_harmonic_sum (N : ℕ) :
    (∑ n ∈ Icc 1 N, (ArithmeticFunction.zeta n : ℝ) / n) =
      (harmonic N : ℝ) := by
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  apply sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
  simp [ArithmeticFunction.zeta_apply_ne hn0]

/-- The harmonic sum over ordered `k`-factor tuples has at most the expected
`k` logarithmic factors. -/
theorem divisorTuple_harmonic_le (k N : ℕ) :
    (∑ n ∈ Icc 1 N, (divisorTupleCount k n : ℝ) / n) ≤
      (harmonic N : ℝ) ^ k := by
  induction k with
  | zero =>
    simp only [divisorTupleCount, pow_zero, ArithmeticFunction.one_apply]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_div, zero_div]
    by_cases hN : 1 ≤ N
    · simp [hN]
    · have : N = 0 := by omega
      simp [this]
  | succ k ih =>
    have h := harmonic_convolution_le (ArithmeticFunction.zeta ^ k)
      ArithmeticFunction.zeta N
    rw [zeta_harmonic_sum] at h
    calc
      _ ≤ (∑ n ∈ Icc 1 N, (divisorTupleCount k n : ℝ) / n) *
          (harmonic N : ℝ) := by simpa [divisorTupleCount, pow_succ] using h
      _ ≤ (harmonic N : ℝ) ^ k * (harmonic N : ℝ) :=
        mul_le_mul_of_nonneg_right ih (by rw [harmonic, Rat.cast_sum]; positivity)
      _ = _ := (pow_succ _ _).symm

/-- A uniform summatory bound, with one harmless extra logarithmic factor.
It holds also at `N = 0` and requires no squarefreeness restriction. -/
theorem divisorTuple_sum_le (k N : ℕ) :
    (∑ n ∈ Icc 1 N, (divisorTupleCount k n : ℝ)) ≤
      (N : ℝ) * (harmonic N : ℝ) ^ k := by
  calc
    _ ≤ ∑ n ∈ Icc 1 N, (N : ℝ) * ((divisorTupleCount k n : ℝ) / n) := by
      apply sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
      rw [← mul_div_assoc, le_div_iff₀ hn0]
      nlinarith [show (0 : ℝ) ≤ divisorTupleCount k n by positivity]
    _ = (N : ℝ) * ∑ n ∈ Icc 1 N, (divisorTupleCount k n : ℝ) / n :=
      (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (divisorTuple_harmonic_le k N) (by positivity)

/-- At a prime, there are exactly `k` ordered `k`-factor tuples. -/
theorem divisorTupleCount_prime (k p : ℕ) (hp : p.Prime) :
    divisorTupleCount k p = k := by
  induction k with
  | zero => simp [divisorTupleCount, hp.ne_one]
  | succ k ih =>
    have h1 : (ArithmeticFunction.zeta ^ k) 1 = 1 :=
      ArithmeticFunction.isMultiplicative_zeta.pow.1
    change (ArithmeticFunction.zeta ^ (k + 1)) p = k + 1
    rw [pow_succ, ArithmeticFunction.mul_zeta_apply, hp.divisors]
    change (ArithmeticFunction.zeta ^ k) p = k at ih
    simp [hp.ne_one.symm, h1, ih, Nat.add_comm]

/-- A squarefree number has one independent choice among `k` tuple positions
for every prime factor. -/
theorem divisorTupleCount_squarefree (k n : ℕ) (hn : Squarefree n) :
    divisorTupleCount k n = k ^ n.primeFactors.card := by
  have hmult := (ArithmeticFunction.isMultiplicative_zeta.pow
    (k := k)).prod_primeFactors hn
  change (ArithmeticFunction.zeta ^ k) n = _
  rw [← hmult]
  calc
    _ = ∏ p ∈ n.primeFactors, k := by
      apply prod_congr rfl
      intro p hp
      exact divisorTupleCount_prime k p (Nat.prime_of_mem_primeFactors hp)
    _ = _ := by simp

/-- Explicit elementary logarithmic summatory majorant. -/
theorem divisorTuple_sum_le_log (k N : ℕ) :
    (∑ n ∈ Icc 1 N, (divisorTupleCount k n : ℝ)) ≤
      (N : ℝ) * (1 + Real.log N) ^ k := by
  refine (divisorTuple_sum_le k N).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ (by rw [harmonic, Rat.cast_sum]; positivity)
    (harmonic_le_one_add_log N) k

/-- A finite squarefree support has a power-of-prime-count sum bounded by
an elementary divisor-tuple sum. -/
theorem sum_squarefree_pow_le (S : Finset ℕ) (k N : ℕ)
    (hS : ∀ n ∈ S, Squarefree n) (hSN : S ⊆ Icc 1 N) :
    (∑ n ∈ S, (k : ℝ) ^ n.primeFactors.card) ≤
      (N : ℝ) * (1 + Real.log N) ^ k := by
  calc
    _ = ∑ n ∈ S, (divisorTupleCount k n : ℝ) := by
      apply sum_congr rfl
      intro n hn
      rw [divisorTupleCount_squarefree k n (hS n hn), Nat.cast_pow]
    _ ≤ ∑ n ∈ Icc 1 N, (divisorTupleCount k n : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hSN (by intros; positivity)
    _ ≤ _ := divisorTuple_sum_le_log k N

end Problem337.SelbergError

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.OptimizedSelbergError

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset

namespace Problem337.SelbergOptimal

/-- The actual optimal weights have a logarithmically bounded weighted mass.
This uses the sharp coefficient bound, not the crude inverse-density estimate. -/
theorem optimalWeight_primeFactor_mass_le (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    (∑ d ∈ s.prodPrimes.divisors, |optimalWeight s z d| *
      (2 : ℝ) ^ d.primeFactors.card) ≤ (z : ℝ) * (1 + Real.log z) ^ 2 := by
  calc
    _ ≤ ∑ d ∈ s.prodPrimes.divisors,
        if d ≤ z then (2 : ℝ) ^ d.primeFactors.card else 0 := by
      apply sum_le_sum
      intro d hd
      by_cases hdz : d ≤ z
      · rw [ite_eq_left hdz]
        have hw : |optimalWeight s z d| ≤ 1 := by
          rw [optimalWeight_formula s z d (Nat.dvd_of_mem_divisors hd)]
          convert abs_normalized_complement_le_one s hz (Nat.dvd_of_mem_divisors hd) using 1
          unfold complementNormalizer
          congr 1
          ring
        simpa using mul_le_mul_of_nonneg_right hw
          (by positivity : 0 ≤ (2 : ℝ) ^ d.primeFactors.card)
      · rw [ite_eq_right hdz, optimalWeight_eq_zero_of_lt s (lt_of_not_ge hdz)]
        simp
    _ = ∑ d ∈ s.prodPrimes.divisors.filter (fun d => d ≤ z),
        (2 : ℝ) ^ d.primeFactors.card := (sum_filter _ _).symm
    _ ≤ _ := SelbergError.sum_squarefree_pow_le _ 2 z
      (fun d hd => s.squarefree_of_mem_divisors_prodPrimes (mem_filter.mp hd).1)
      (by
        intro d hd
        obtain ⟨hdP, hdz⟩ := mem_filter.mp hd
        exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdP, hdz⟩)

/-- A dimension-two local remainder envelope gives an explicit logarithmic
error for the constructed optimal Selberg weights. -/
theorem errSum_optimalWeight_le_log (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z)
    (hrem : ∀ a ∈ s.prodPrimes.divisors, ∀ b ∈ s.prodPrimes.divisors,
      |s.rem (Nat.lcm a b)| ≤
        (2 : ℝ) ^ a.primeFactors.card * (2 : ℝ) ^ b.primeFactors.card) :
    s.errSum (BoundingSieve.lambdaSquared (optimalWeight s z)) ≤
      (z : ℝ) ^ 2 * (1 + Real.log z) ^ 4 := by
  calc
    _ ≤ (∑ d ∈ s.prodPrimes.divisors, |optimalWeight s z d| *
        (2 : ℝ) ^ d.primeFactors.card) ^ 2 :=
      SelbergError.errSum_lambdaSquared_le_sq s (optimalWeight s z)
        (fun d => (2 : ℝ) ^ d.primeFactors.card) hrem
    _ ≤ ((z : ℝ) * (1 + Real.log z) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (sum_nonneg (by intros; positivity))
        (optimalWeight_primeFactor_mass_le s hz) 2
    _ = _ := by ring

/-- Fully optimized finite Selberg inequality with explicit logarithmic error. -/
theorem siftedSum_le_log_error (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z)
    (hrem : ∀ a ∈ s.prodPrimes.divisors, ∀ b ∈ s.prodPrimes.divisors,
      |s.rem (Nat.lcm a b)| ≤
        (2 : ℝ) ^ a.primeFactors.card * (2 : ℝ) ^ b.primeFactors.card) :
    s.siftedSum ≤ s.totalMass / normalizer s z +
      (z : ℝ) ^ 2 * (1 + Real.log z) ^ 4 :=
  (siftedSum_le s hz).trans
    (add_le_add le_rfl (errSum_optimalWeight_le_log s hz hrem))

end Problem337.SelbergOptimal

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.GoldbachSieveLocal

namespace OAI
/-!
Finite local arithmetic for a possible binary Goldbach sieve.  These results
count roots of the polynomial `x * (u - x)` and provide its multiplicative local
density.  They do not assert any prime-pair bound or positive density of Goldbach
numbers.
-/

noncomputable section

open scoped BigOperators

namespace Problem337

/-- Residue classes removed by the binary Goldbach sieve. -/
def GoldbachSieveRoot (u d : ℕ) :=
  {x : ZMod d // x * ((u : ZMod d) - x) = 0}

/-- Local number of roots of `x * (u - x)` modulo `d`. -/
def goldbachSieveRootCount (u d : ℕ) : ℕ :=
  Nat.card (GoldbachSieveRoot u d)

/-- The Chinese remainder theorem separates the local root conditions. -/
def goldbachSieveRootEquiv (u a b : ℕ) (hab : a.Coprime b) :
    GoldbachSieveRoot u (a * b) ≃
      GoldbachSieveRoot u a × GoldbachSieveRoot u b := by
  let e := ZMod.chineseRemainder hab
  apply (Equiv.subtypeEquiv e.toEquiv ?_).trans Equiv.subtypeProdEquivProd
  intro x
  change x * ((u : ZMod (a * b)) - x) = 0 ↔
    (e x).1 * ((u : ZMod a) - (e x).1) = 0 ∧
      (e x).2 * ((u : ZMod b) - (e x).2) = 0
  have h := e.injective.eq_iff (a := x * ((u : ZMod (a * b)) - x)) (b := 0)
  simpa only [map_mul, map_sub, map_natCast, map_zero, Prod.mk_zero_zero,
    Prod.mul_def, Prod.sub_def, Prod.fst_natCast, Prod.snd_natCast,
    Prod.mk.injEq, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] using h.symm

/-- Root counts are multiplicative at coprime moduli, with no distribution hypothesis. -/
theorem goldbachSieveRootCount_mul (u a b : ℕ) (hab : a.Coprime b) :
    goldbachSieveRootCount u (a * b) =
      goldbachSieveRootCount u a * goldbachSieveRootCount u b := by
  unfold goldbachSieveRootCount
  rw [Nat.card_congr (goldbachSieveRootEquiv u a b hab), Nat.card_prod]

@[simp] theorem goldbachSieveRootCount_one (u : ℕ) :
    goldbachSieveRootCount u 1 = 1 := by
  unfold goldbachSieveRootCount GoldbachSieveRoot
  have e : {x : ZMod 1 // x * ((u : ZMod 1) - x) = 0} ≃ ZMod 1 :=
    Equiv.subtypeUnivEquiv (fun x => Subsingleton.elim _ _)
  rw [Nat.card_congr e, Nat.card_zmod]

/-- At a prime, the only roots are zero and the target residue. -/
theorem goldbachSieveRootCount_prime (u p : ℕ) (hp : p.Prime) :
    goldbachSieveRootCount u p = if p ∣ u then 1 else 2 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hroots : (Finset.univ.filter
      (fun x : ZMod p => x * ((u : ZMod p) - x) = 0)) = {0, (u : ZMod p)} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      mul_eq_zero, sub_eq_zero, Finset.mem_insert, Finset.mem_singleton]
    tauto
  unfold goldbachSieveRootCount GoldbachSieveRoot
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hroots]
  by_cases h : p ∣ u
  · simp [h, (ZMod.natCast_eq_zero_iff u p).mpr h]
  · have hne : (u : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff u p).not.mpr h
    simp [h, Ne.symm hne]

/-- A finite product of distinct primes gives the product of the local counts. -/
theorem goldbachSieveRootCount_prod_primes (u : ℕ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    goldbachSieveRootCount u (∏ p ∈ s, p) =
      ∏ p ∈ s, goldbachSieveRootCount u p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      have hpp := hs p (Finset.mem_insert_self p s)
      have hsp : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
      have hcop : p.Coprime (∏ q ∈ s, q) := by
        apply Nat.Coprime.prod_right
        intro q hq
        apply (Nat.coprime_primes hpp (hsp q hq)).mpr
        intro heq
        exact hp (heq ▸ hq)
      rw [Finset.prod_insert hp, goldbachSieveRootCount_mul u p _ hcop,
        ih hsp, Finset.prod_insert hp]

/-- Exact squarefree local factor for the binary Goldbach sieve. -/
theorem goldbachSieveRootCount_squarefree (u d : ℕ) (hd : Squarefree d) :
    goldbachSieveRootCount u d =
      ∏ p ∈ d.primeFactors, if p ∣ u then 1 else 2 := by
  calc
    goldbachSieveRootCount u d =
        goldbachSieveRootCount u (∏ p ∈ d.primeFactors, p) := by
          rw [Nat.prod_primeFactors_of_squarefree hd]
    _ = ∏ p ∈ d.primeFactors, goldbachSieveRootCount u p :=
      goldbachSieveRootCount_prod_primes u d.primeFactors
        (fun p hp => (Nat.mem_primeFactors.mp hp).1)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      exact goldbachSieveRootCount_prime u p (Nat.mem_primeFactors.mp hp).1

/-- The exact finite local root density, normalized as an arithmetic function. -/
def goldbachSieveDensity (u : ℕ) : ArithmeticFunction ℝ where
  toFun d := (goldbachSieveRootCount u d : ℝ) / (d : ℝ)
  map_zero' := by simp

@[simp] theorem goldbachSieveDensity_apply (u d : ℕ) :
    goldbachSieveDensity u d = (goldbachSieveRootCount u d : ℝ) / (d : ℝ) := rfl

/-- The finite local density has exactly the multiplicativity required by a sieve. -/
theorem goldbachSieveDensity_isMultiplicative (u : ℕ) :
    (goldbachSieveDensity u).IsMultiplicative := by
  constructor
  · simp
  · intro a b hab
    simp only [goldbachSieveDensity_apply, goldbachSieveRootCount_mul u a b hab,
      Nat.cast_mul, mul_div_mul_comm]

/-- The local density at a prime is `1/p` or `2/p`. -/
theorem goldbachSieveDensity_prime (u p : ℕ) (hp : p.Prime) :
    goldbachSieveDensity u p = if p ∣ u then 1 / (p : ℝ) else 2 / (p : ℝ) := by
  rw [goldbachSieveDensity_apply, goldbachSieveRootCount_prime u p hp]
  split_ifs <;> norm_num

/-- All prime local root densities are positive. -/
theorem goldbachSieveDensity_prime_pos (u p : ℕ) (hp : p.Prime) :
    0 < goldbachSieveDensity u p := by
  rw [goldbachSieveDensity_prime u p hp]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  split_ifs <;> positivity

/-- At odd primes the sieve is nondegenerate. At two, this requires an even target. -/
theorem goldbachSieveDensity_prime_lt_one (u p : ℕ) (hp : p.Prime)
    (hparity : p = 2 → 2 ∣ u) : goldbachSieveDensity u p < 1 := by
  rw [goldbachSieveDensity_prime u p hp]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  split_ifs with h
  · rw [div_lt_one hpR]
    exact_mod_cast hp.one_lt
  · have hp2 : 2 < p := by
      have := hp.two_le
      by_contra hnot
      have heq : p = 2 := by omega
      exact h (heq ▸ hparity heq)
    rw [div_lt_one hpR]
    exact_mod_cast hp2

end Problem337

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.ResidueIntervalCount

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- The exact number of natural numbers below `N` in one residue class. -/
theorem card_range_zmod_eq {d : ℕ} [NeZero d] (N : ℕ) (r : ZMod d) :
    ((Finset.range N).filter (fun n : ℕ => (n : ZMod d) = r)).card =
      N / d + if r.val < N % d then 1 else 0 := by
  have hd : 0 < d := NeZero.pos d
  have he : (Finset.range N).filter (fun n : ℕ => (n : ZMod d) = r) =
      (Finset.range N).filter (fun n => Nat.ModEq d n r.val) := by
    apply Finset.filter_congr
    intro n hn
    simpa only [ZMod.natCast_zmod_val] using
      (ZMod.natCast_eq_natCast_iff n r.val d)
  rw [he, ← Nat.count_eq_card_filter_range,
    Nat.count_modEq_card N hd r.val, Nat.mod_eq_of_lt r.val_lt]

/-- Exact quotient/remainder decomposition for any collection of residues. -/
theorem card_range_zmod_mem {d : ℕ} [NeZero d] (N : ℕ) (S : Finset (ZMod d)) :
    ((Finset.range N).filter (fun n : ℕ => (n : ZMod d) ∈ S)).card =
      (N / d) * S.card + (S.filter (fun r => r.val < N % d)).card := by
  classical
  rw [← Finset.sum_card_fiberwise_eq_card_filter (Finset.range N) S
    (fun n : ℕ => (n : ZMod d))]
  simp_rw [card_range_zmod_eq]
  rw [Finset.sum_add_distrib]
  simp [mul_comm]

/-- The elementary progression-counting error is at most the number of
residue classes, uniformly in the interval length and modulus. -/
theorem abs_card_range_zmod_mem_sub {d : ℕ} [NeZero d]
    (N : ℕ) (S : Finset (ZMod d)) :
    |(((Finset.range N).filter (fun n : ℕ => (n : ZMod d) ∈ S)).card : ℝ) -
      (N : ℝ) * S.card / d| ≤ (S.card : ℝ) := by
  classical
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hr : ((N % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt N (NeZero.pos d)
  have hq : (N : ℝ) = (N / d : ℕ) * (d : ℝ) + (N % d : ℕ) := by
    exact_mod_cast (show N = (N / d) * d + N % d by
      simpa only [Nat.mul_comm] using (Nat.div_add_mod N d).symm)
  have hs : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have ht : (0 : ℝ) ≤ (S.filter (fun r => r.val < N % d)).card := Nat.cast_nonneg _
  have hts : ((S.filter (fun r => r.val < N % d)).card : ℝ) ≤ S.card := by
    exact_mod_cast Finset.card_filter_le S (fun r => r.val < N % d)
  have hfrac0 : (0 : ℝ) ≤ (N % d : ℕ) / d := by positivity
  have hfrac1 : ((N % d : ℕ) : ℝ) / d ≤ 1 := (div_le_one hd).2 hr.le
  have hmain : (N : ℝ) * S.card / d =
      (N / d : ℕ) * (S.card : ℝ) + ((N % d : ℕ) : ℝ) / d * S.card := by
    rw [hq]
    field_simp
  rw [card_range_zmod_mem, Nat.cast_add, Nat.cast_mul, hmain]
  rw [abs_le]
  constructor <;> nlinarith

end Problem337

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.PeriodicResidueCount

namespace OAI
noncomputable section

namespace Problem337

/-- A periodic predicate has one full period's worth of solutions in each block. -/
theorem periodic_count_mul {p : ℕ → Prop} [DecidablePred p] {d : ℕ}
    (hp : Function.Periodic p d) (q : ℕ) :
    Nat.count p (q * d) = q * Nat.count p d := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, Nat.count_add']
    have hshift : (fun k => p (k + d)) = p := by
      funext k
      exact hp k
    simp only [hshift, ih]
    ring

/-- Exact quotient-and-remainder formula for a periodic counting function. -/
theorem periodic_count_div_mod {p : ℕ → Prop} [DecidablePred p] {d : ℕ}
    (hp : Function.Periodic p d) (N : ℕ) :
    Nat.count p N = (N / d) * Nat.count p d + Nat.count p (N % d) := by
  conv_lhs => rw [← Nat.mod_add_div N d]
  rw [Nat.count_add']
  have hshift : (fun k => p (k + d * (N / d))) = p := by
    funext k
    simpa [Nat.mul_comm] using hp.nsmul (N / d) k
  simp only [hshift]
  rw [Nat.mul_comm d, periodic_count_mul hp]
  omega

/-- The count on an initial interval differs from its periodic mean by at most the number
of allowed residues in one period. This bound is uniform in the length of the interval. -/
theorem periodic_count_discrepancy {p : ℕ → Prop} [DecidablePred p] {d : ℕ}
    (hd : 0 < d) (hp : Function.Periodic p d) (N : ℕ) :
    |(Nat.count p N : ℝ) - (N : ℝ) * Nat.count p d / d| ≤ Nat.count p d := by
  have hcount := periodic_count_div_mod hp N
  have hrem := Nat.count_monotone p (Nat.mod_lt N hd).le
  have hdiv := Nat.mod_add_div N d
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hremR : (Nat.count p (N % d) : ℝ) ≤ Nat.count p d := by exact_mod_cast hrem
  have hmodR : ((N % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt N hd).le
  have hdivR : ((N % d : ℕ) : ℝ) + (d : ℝ) * (N / d : ℕ) = N := by exact_mod_cast hdiv
  have hcountR : (Nat.count p N : ℝ) =
      (N / d : ℕ) * (Nat.count p d : ℝ) + Nat.count p (N % d) := by exact_mod_cast hcount
  have hnonneg : (0 : ℝ) ≤ Nat.count p d := by positivity
  have hterm0 : 0 ≤ ((N % d : ℕ) : ℝ) * Nat.count p d / d := by positivity
  have hterm : ((N % d : ℕ) : ℝ) * Nat.count p d / d ≤ Nat.count p d := by
    apply (div_le_iff₀ hdR).2
    nlinarith [mul_le_mul_of_nonneg_right hmodR hnonneg]
  have heq : (Nat.count p N : ℝ) - (N : ℝ) * Nat.count p d / d =
      Nat.count p (N % d) - ((N % d : ℕ) : ℝ) * Nat.count p d / d := by
    rw [hcountR, ← hdivR]
    field_simp
    ring
  rw [heq, abs_le]
  constructor <;> linarith [show (0 : ℝ) ≤ Nat.count p (N % d) by positivity]

/-- Shifting a periodic predicate does not change its mass over a full period. -/
theorem periodic_count_shift_period {p : ℕ → Prop} [DecidablePred p] {d : ℕ}
    (hp : Function.Periodic p d) (a : ℕ) :
    Nat.count (fun n => p (a + n)) d = Nat.count p d := by
  have h₁ := Nat.count_add p a d
  have h₂ := Nat.count_add' p a d
  have hshift : (fun n => p (n + d)) = p := funext hp
  simp only [hshift] at h₂
  omega

/-- Counting a predicate on a shifted natural interval is the same as counting
its translate on an initial interval. -/
theorem filter_Ico_card_eq_count_shift (p : ℕ → Prop) [DecidablePred p]
    (a N : ℕ) :
    ((Finset.Ico a (a + N)).filter p).card =
      Nat.count (fun n => p (a + n)) N := by
  rw [Nat.count_eq_card_filter_range, ← Nat.Ico_zero_eq_range]
  have hmap := Finset.map_add_left_Ico 0 N a
  rw [Nat.add_zero] at hmap
  rw [← hmap, Finset.filter_map, Finset.card_map]
  rfl

/-- Sharp periodic discrepancy on any shifted interval: the error is bounded
by one period's mass, independent of both endpoints. -/
theorem periodic_Ico_count_discrepancy {p : ℕ → Prop} [DecidablePred p] {d : ℕ}
    (hd : 0 < d) (hp : Function.Periodic p d) (a N : ℕ) :
    |(((Finset.Ico a (a + N)).filter p).card : ℝ) -
      (N : ℝ) * Nat.count p d / d| ≤ Nat.count p d := by
  have hshift : Function.Periodic (fun n => p (a + n)) d := by
    intro n
    simpa only [Nat.add_assoc] using hp (a + n)
  have h := periodic_count_discrepancy hd hshift N
  rw [periodic_count_shift_period hp a] at h
  simpa only [filter_Ico_card_eq_count_shift] using h

/-- The periodic mass of a predicate on residue classes is its finite cardinality. -/
theorem zmod_predicate_period_count (d : ℕ) [NeZero d]
    (P : ZMod d → Prop) [DecidablePred P] :
    Nat.count (fun n : ℕ => P (n : ZMod d)) d =
      (Finset.univ.filter P).card := by
  classical
  simpa [Nat.count_eq_card_filter_range, Nat.div_self (NeZero.pos d)] using
    (card_range_zmod_mem d (Finset.univ.filter P))

/-- Residue classes are equidistributed up to one copy of the allowed set on
any natural interval, without a primality or coprimality assumption. -/
theorem zmod_predicate_Ico_discrepancy (d : ℕ) [NeZero d]
    (P : ZMod d → Prop) [DecidablePred P] (a N : ℕ) :
    |(((Finset.Ico a (a + N)).filter (fun n : ℕ => P (n : ZMod d))).card : ℝ) -
      (N : ℝ) * (Finset.univ.filter P).card / d| ≤ (Finset.univ.filter P).card := by
  have hp : Function.Periodic (fun n : ℕ => P (n : ZMod d)) d := by
    intro n
    simp
  have h := periodic_Ico_count_discrepancy (NeZero.pos d) hp a N
  simpa only [zmod_predicate_period_count d P] using h

end Problem337

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.GoldbachSieveRemainder

namespace OAI
/-!
The exact finite progression error for the binary Goldbach polynomial. No
prime-distribution estimate or sieve-density lower bound is assumed here.
-/

noncomputable section

namespace Problem337

/-- The local root-count definition is the cardinality of the corresponding
finite set whenever the modulus is nonzero. -/
theorem goldbachSieveRootCount_eq_filter_card (u d : ℕ) [NeZero d] :
    goldbachSieveRootCount u d =
      (Finset.univ.filter (fun x : ZMod d => x * ((u : ZMod d) - x) = 0)).card := by
  classical
  unfold goldbachSieveRootCount GoldbachSieveRoot
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- On the natural interval used for ordered positive prime pairs, the
truncated natural subtraction agrees with subtraction in the residue ring. -/
theorem goldbach_polynomial_dvd_iff_zmod (u d n : ℕ) (hn : n ≤ u) :
    d ∣ n * (u - n) ↔
      (n : ZMod d) * ((u : ZMod d) - (n : ZMod d)) = 0 := by
  rw [← Nat.cast_sub hn, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]

/-- Sharp, uniform error for counting divisibility of `n*(u-n)` on `1 ≤ n < u`.
The formulation includes the empty intervals at `u=0` and `u=1`. -/
theorem goldbach_polynomial_count_discrepancy (u d : ℕ) [NeZero d] :
    |(((Finset.Icc 1 (u - 1)).filter (fun n => d ∣ n * (u - n))).card : ℝ) -
      ((u - 1 : ℕ) : ℝ) * goldbachSieveRootCount u d / d| ≤
        goldbachSieveRootCount u d := by
  classical
  have hI : Finset.Icc 1 (u - 1) = Finset.Ico 1 (1 + (u - 1)) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hfilter : (Finset.Icc 1 (u - 1)).filter (fun n => d ∣ n * (u - n)) =
      (Finset.Ico 1 (1 + (u - 1))).filter
        (fun n : ℕ => (n : ZMod d) * ((u : ZMod d) - (n : ZMod d)) = 0) := by
    rw [← hI]
    apply Finset.filter_congr
    intro n hn
    exact goldbach_polynomial_dvd_iff_zmod u d n
      ((Finset.mem_Icc.mp hn).2.trans (Nat.sub_le u 1))
  rw [hfilter, goldbachSieveRootCount_eq_filter_card]
  exact zmod_predicate_Ico_discrepancy d
    (fun x : ZMod d => x * ((u : ZMod d) - x) = 0) 1 (u - 1)

/-- The same error with the normalized multiplicative sieve density. -/
theorem goldbach_polynomial_count_density_discrepancy (u d : ℕ) [NeZero d] :
    |(((Finset.Icc 1 (u - 1)).filter (fun n => d ∣ n * (u - n))).card : ℝ) -
      goldbachSieveDensity u d * ((u - 1 : ℕ) : ℝ)| ≤
        goldbachSieveRootCount u d := by
  simpa only [goldbachSieveDensity_apply, div_mul_eq_mul_div, mul_div_assoc, mul_comm] using
    goldbach_polynomial_count_discrepancy u d

end Problem337

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.PrimePairSieveModel

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.PrimePairSieve

/-- Pushing a finite set through a noninjective map retains the multiplicity
of each image value. In particular, the two ordered Goldbach pairs with
coordinates exchanged must not be identified by the polynomial map. -/
def fiberWeight (A : Finset ℕ) (f : ℕ → ℕ) (y : ℕ) : ℝ :=
  ((A.filter (fun x => f x = y)).card : ℝ)

lemma fiberWeight_nonneg (A : Finset ℕ) (f : ℕ → ℕ) (y : ℕ) :
    0 ≤ fiberWeight A f y := by
  exact Nat.cast_nonneg _

lemma sum_fiberWeight_indicator (A : Finset ℕ) (f : ℕ → ℕ)
    (p : ℕ → Prop) [DecidablePred p] :
    (∑ y ∈ A.image f, if p y then fiberWeight A f y else 0) =
      ((A.filter (fun x => p (f x))).card : ℝ) := by
  classical
  rw [← Finset.sum_filter]
  unfold fiberWeight
  rw [← Nat.cast_sum]
  congr 1
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, _, hp⟩
    exact ⟨hx, hp⟩
  · rintro ⟨hx, hp⟩
    exact ⟨hx, Finset.mem_image_of_mem f hx, hp⟩

/-- A concrete `BoundingSieve` attached to any polynomial image, with exact
fiber weights rather than an unjustified injectivity assumption. -/
def imageSieve (A : Finset ℕ) (f : ℕ → ℕ) (P : ℕ)
    (hP : Squarefree P) (ν : ArithmeticFunction ℝ)
    (hν : ν.IsMultiplicative)
    (hνpos : ∀ p : ℕ, p.Prime → p ∣ P → 0 < ν p)
    (hνlt : ∀ p : ℕ, p.Prime → p ∣ P → ν p < 1) : BoundingSieve where
  support := A.image f
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fiberWeight A f
  weights_nonneg := fiberWeight_nonneg A f
  totalMass := A.card
  nu := ν
  nu_mult := hν
  nu_pos_of_prime := hνpos
  nu_lt_one_of_prime := hνlt

lemma imageSieve_multSum (A : Finset ℕ) (f : ℕ → ℕ) (P : ℕ)
    (hP : Squarefree P) (ν : ArithmeticFunction ℝ)
    (hν : ν.IsMultiplicative)
    (hνpos : ∀ p : ℕ, p.Prime → p ∣ P → 0 < ν p)
    (hνlt : ∀ p : ℕ, p.Prime → p ∣ P → ν p < 1) (d : ℕ) :
    (imageSieve A f P hP ν hν hνpos hνlt).multSum d =
      ((A.filter (fun x => d ∣ f x)).card : ℝ) := by
  exact sum_fiberWeight_indicator A f (fun y => d ∣ y)

lemma imageSieve_siftedSum (A : Finset ℕ) (f : ℕ → ℕ) (P : ℕ)
    (hP : Squarefree P) (ν : ArithmeticFunction ℝ)
    (hν : ν.IsMultiplicative)
    (hνpos : ∀ p : ℕ, p.Prime → p ∣ P → 0 < ν p)
    (hνlt : ∀ p : ℕ, p.Prime → p ∣ P → ν p < 1) :
    (imageSieve A f P hP ν hν hνpos hνlt).siftedSum =
      ((A.filter (fun x => P.Coprime (f x))).card : ℝ) := by
  exact sum_fiberWeight_indicator A f (fun y => P.Coprime y)

/-- First coordinates of the ordered representations of `N` by two primes. -/
def primePairs (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (N - 1)).filter (fun x => x.Prime ∧ (N - x).Prime)

/-- The original integer coordinates left after sieving both prime factors. -/
def siftedPairs (N P : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (N - 1)).filter (fun x => P.Coprime (x * (N - x)))

/-- A prime pair is either sifted or has a coordinate among the prime divisors
of `P`. This is the exact small-prime correction, valid even for `N=0,1`. -/
theorem primePairs_subset (N P : ℕ) (hP : P ≠ 0) :
    primePairs N ⊆ siftedPairs N P ∪
      (P.primeFactors ∪ P.primeFactors.image (fun p => N - p)) := by
  intro x hx
  obtain ⟨hxI, hxprime, hother⟩ := Finset.mem_filter.mp hx
  have hxN : x ≤ N := by
    have := (Finset.mem_Icc.mp hxI).2
    omega
  by_cases hxdvd : x ∣ P
  · exact Finset.mem_union_right _ (Finset.mem_union_left _
      (Nat.mem_primeFactors.mpr ⟨hxprime, hxdvd, hP⟩))
  by_cases hydvd : N - x ∣ P
  · apply Finset.mem_union_right
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨N - x, Nat.mem_primeFactors.mpr ⟨hother, hydvd, hP⟩,
      Nat.sub_sub_self hxN⟩
  apply Finset.mem_union_left
  apply Finset.mem_filter.mpr
  exact ⟨hxI, ((hxprime.coprime_iff_not_dvd.mpr hxdvd).symm).mul_right
    ((hother.coprime_iff_not_dvd.mpr hydvd).symm)⟩

/-- At most twice the number of sieving primes is lost when passing from
ordered prime pairs to sifted polynomial values with multiplicities. -/
theorem card_primePairs_le_sifted (N P : ℕ) (hP : P ≠ 0) :
    (primePairs N).card ≤ (siftedPairs N P).card + 2 * P.primeFactors.card := by
  calc
    (primePairs N).card ≤
        (siftedPairs N P ∪ (P.primeFactors ∪
          P.primeFactors.image (fun p => N - p))).card :=
      Finset.card_le_card (primePairs_subset N P hP)
    _ ≤ (siftedPairs N P).card + (P.primeFactors ∪
          P.primeFactors.image (fun p => N - p)).card := Finset.card_union_le _ _
    _ ≤ (siftedPairs N P).card +
        (P.primeFactors.card + (P.primeFactors.image (fun p => N - p)).card) :=
      Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ ≤ (siftedPairs N P).card + 2 * P.primeFactors.card := by
      have := Finset.card_image_le (s := P.primeFactors) (f := fun p => N - p)
      omega

/-- The exact polynomial divisor count is the remainder term supplied to the
Selberg sieve; no analytic approximation is built into this model. -/
lemma imageSieve_rem (A : Finset ℕ) (f : ℕ → ℕ) (P : ℕ)
    (hP : Squarefree P) (ν : ArithmeticFunction ℝ)
    (hν : ν.IsMultiplicative)
    (hνpos : ∀ p : ℕ, p.Prime → p ∣ P → 0 < ν p)
    (hνlt : ∀ p : ℕ, p.Prime → p ∣ P → ν p < 1) (d : ℕ) :
    (imageSieve A f P hP ν hν hνpos hνlt).rem d =
      ((A.filter (fun x => d ∣ f x)).card : ℝ) - ν d * A.card := by
  rw [BoundingSieve.rem, imageSieve_multSum]
  rfl

/-- A fully concrete prime-pair Λ² bound with ordered-pair multiplicities and
an explicit small-prime correction. The main coefficient and its arithmetic
remainder are still to be estimated by the sieve application. -/
theorem primePairs_lambdaSquared_bound (N P : ℕ)
    (hP : Squarefree P) (ν : ArithmeticFunction ℝ)
    (hν : ν.IsMultiplicative)
    (hνpos : ∀ p : ℕ, p.Prime → p ∣ P → 0 < ν p)
    (hνlt : ∀ p : ℕ, p.Prime → p ∣ P → ν p < 1)
    (w : ℕ → ℝ) (hw : w 1 = 1) :
    ((primePairs N).card : ℝ) ≤
      ((Finset.Icc 1 (N - 1)).card : ℝ) *
        (∑ d ∈ P.divisors, BoundingSieve.lambdaSquared w d * ν d) +
      (∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d| *
        |(((Finset.Icc 1 (N - 1)).filter
            (fun x => d ∣ x * (N - x))).card : ℝ) -
          ν d * (Finset.Icc 1 (N - 1)).card|) +
      2 * P.primeFactors.card := by
  let s := imageSieve (Finset.Icc 1 (N - 1)) (fun x => x * (N - x))
    P hP ν hν hνpos hνlt
  have hcard : ((primePairs N).card : ℝ) ≤
      ((siftedPairs N P).card : ℝ) + 2 * P.primeFactors.card := by
    exact_mod_cast card_primePairs_le_sifted N P hP.ne_zero
  have hs : s.siftedSum = ((siftedPairs N P).card : ℝ) :=
    imageSieve_siftedSum _ _ _ _ _ _ _ _
  have hb := s.siftedSum_le_mainSum_errSum_of_upperMoebius
    (BoundingSieve.lambdaSquared w) (BoundingSieve.upperMoebius_lambdaSquared w hw)
  have herr : s.errSum (BoundingSieve.lambdaSquared w) =
      ∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d| *
        |(((Finset.Icc 1 (N - 1)).filter
            (fun x => d ∣ x * (N - x))).card : ℝ) -
          ν d * (Finset.Icc 1 (N - 1)).card| := by
    unfold BoundingSieve.errSum
    simp only [s, imageSieve_rem]
    rfl
  rw [hs, herr] at hb
  change ((siftedPairs N P).card : ℝ) ≤
    ((Finset.Icc 1 (N - 1)).card : ℝ) *
      (∑ d ∈ P.divisors, BoundingSieve.lambdaSquared w d * ν d) + _ at hb
  linarith

end Problem337.PrimePairSieve

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.GoldbachSieveApplication

namespace OAI
/-!
A finite, unconditional Selberg upper bound for ordered prime pairs with the
actual Goldbach local density and explicit root-count error. The analytic
estimates for the optimizing weights and denominator are separate tasks.
-/

noncomputable section
open scoped BigOperators

namespace Problem337

/-- The actual Goldbach local density and progression error may be inserted in
the multiplicity-preserving Selberg model. All arithmetic approximation input
has been discharged; the weights are still arbitrary with `w 1 = 1`. -/
theorem goldbach_primePairs_lambdaSquared_bound (N P : ℕ)
    (hN : 2 ∣ N) (hP : Squarefree P) (w : ℕ → ℝ) (hw : w 1 = 1) :
    ((PrimePairSieve.primePairs N).card : ℝ) ≤
      ((N - 1 : ℕ) : ℝ) *
        (∑ d ∈ P.divisors, BoundingSieve.lambdaSquared w d * goldbachSieveDensity N d) +
      (∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d| * goldbachSieveRootCount N d) +
      2 * P.primeFactors.card := by
  have hpos : ∀ p : ℕ, p.Prime → p ∣ P → 0 < goldbachSieveDensity N p := by
    intro p hp _
    exact goldbachSieveDensity_prime_pos N p hp
  have hlt : ∀ p : ℕ, p.Prime → p ∣ P → goldbachSieveDensity N p < 1 := by
    intro p hp _
    exact goldbachSieveDensity_prime_lt_one N p hp (fun _ => hN)
  have hb := PrimePairSieve.primePairs_lambdaSquared_bound N P hP
    (goldbachSieveDensity N) (goldbachSieveDensity_isMultiplicative N)
    hpos hlt w hw
  have hcard : (Finset.Icc 1 (N - 1)).card = N - 1 := by simp
  rw [hcard] at hb
  refine hb.trans (add_le_add (add_le_add le_rfl ?_) le_rfl)
  apply Finset.sum_le_sum
  intro d hd
  have hd0 : d ≠ 0 := by
    have hdiv := (Nat.mem_divisors.mp hd).1
    intro hzero
    subst d
    exact hP.ne_zero (by simpa using hdiv)
  let : NeZero d := ⟨hd0⟩
  exact mul_le_mul_of_nonneg_left (goldbach_polynomial_count_density_discrepancy N d)
    (abs_nonneg _)

end Problem337

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.GoldbachSieveRootBounds

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

instance goldbachSieveRootFintype (u d : ℕ) [NeZero d] :
    Fintype (GoldbachSieveRoot u d) :=
  inferInstanceAs (Fintype {x : ZMod d // x * ((u : ZMod d) - x) = 0})

instance goldbachSieveRootNonempty (u d : ℕ) : Nonempty (GoldbachSieveRoot u d) :=
  ⟨⟨0, by simp⟩⟩

/-- Reduction modulo two possibly noncoprime moduli is injective when the
source modulus is their least common multiple. This remains true on roots. -/
def goldbachSieveRootLCMEmbedding (u a b : ℕ) :
    GoldbachSieveRoot u (a.lcm b) ↪
      GoldbachSieveRoot u a × GoldbachSieveRoot u b := by
  let e : ZMod (a.lcm b) →+* ZMod a × ZMod b :=
    ZMod.castHom (dvd_refl (a.lcm b)) _
  have einj : Function.Injective e := ZMod.castHom_injective _
  have he (x : GoldbachSieveRoot u (a.lcm b)) :
      (e x.val).1 * ((u : ZMod a) - (e x.val).1) = 0 ∧
        (e x.val).2 * ((u : ZMod b) - (e x.val).2) = 0 := by
    have h := congrArg e x.property
    simpa only [map_mul, map_sub, map_natCast, map_zero, Prod.mul_def,
      Prod.sub_def, Prod.ext_iff, Prod.fst_natCast, Prod.snd_natCast,
      Prod.fst_zero, Prod.snd_zero] using h
  refine ⟨fun x => (⟨(e x.val).1, (he x).1⟩, ⟨(e x.val).2, (he x).2⟩), ?_⟩
  intro x y hxy
  apply Subtype.ext
  apply einj
  apply Prod.ext
  · exact congrArg (fun z : GoldbachSieveRoot u a × GoldbachSieveRoot u b => z.1.val) hxy
  · exact congrArg (fun z : GoldbachSieveRoot u a × GoldbachSieveRoot u b => z.2.val) hxy

/-- LCM-submultiplicativity of the root count. This needs no squarefreeness. -/
theorem goldbachSieveRootCount_lcm_le (u a b : ℕ) [NeZero a] [NeZero b] :
    goldbachSieveRootCount u (a.lcm b) ≤
      goldbachSieveRootCount u a * goldbachSieveRootCount u b := by
  unfold goldbachSieveRootCount
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective (goldbachSieveRootLCMEmbedding u a b)
    (goldbachSieveRootLCMEmbedding u a b).injective

/-- Zero is always a root, so each positive modulus has positive local count. -/
theorem goldbachSieveRootCount_pos (u d : ℕ) [NeZero d] :
    0 < goldbachSieveRootCount u d := by
  exact Nat.card_pos

/-- The local root count cannot exceed the modulus. -/
theorem goldbachSieveRootCount_le (u d : ℕ) [NeZero d] :
    goldbachSieveRootCount u d ≤ d := by
  calc
    goldbachSieveRootCount u d ≤ Nat.card (ZMod d) :=
      Nat.card_le_card_of_injective (fun x : GoldbachSieveRoot u d => x.val)
        Subtype.val_injective
    _ = d := Nat.card_zmod d

/-- Exact exponent of two in a squarefree local root count. -/
theorem goldbachSieveRootCount_eq_two_pow (u d : ℕ) (hd : Squarefree d) :
    goldbachSieveRootCount u d =
      2 ^ (d.primeFactors.filter (fun p => ¬p ∣ u)).card := by
  rw [goldbachSieveRootCount_squarefree u d hd]
  have hf : (∏ p ∈ d.primeFactors, if p ∣ u then 1 else 2) =
      ∏ p ∈ d.primeFactors.filter (fun p => ¬p ∣ u), (2 : ℕ) := by
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro p hp
    split_ifs <;> simp_all
  rw [hf, Finset.prod_const]

/-- Squarefree local root counts are bounded by the number of subsets of
prime factors, uniformly in the target. -/
theorem goldbachSieveRootCount_le_two_pow (u d : ℕ) (hd : Squarefree d) :
    goldbachSieveRootCount u d ≤ 2 ^ d.primeFactors.card := by
  rw [goldbachSieveRootCount_eq_two_pow u d hd]
  exact Nat.pow_le_pow_right (by omega) (Finset.card_filter_le _ _)

end Problem337

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.GoldbachSelbergBound

namespace OAI
noncomputable section
open scoped BigOperators
open Finset

namespace Problem337.GoldbachSelberg

/-- The actual multiplicity-preserving sieve for an even target. -/
def sieve (N P : ℕ) (hN : 2 ∣ N) (hP : Squarefree P) : BoundingSieve :=
  PrimePairSieve.imageSieve (Icc 1 (N - 1)) (fun x => x * (N - x)) P hP
    (goldbachSieveDensity N) (goldbachSieveDensity_isMultiplicative N)
    (fun p hp _ => goldbachSieveDensity_prime_pos N p hp)
    (fun p hp _ => goldbachSieveDensity_prime_lt_one N p hp (fun _ => hN))

/-- A concrete finite denominator, independent of proof-valued sieve parameters. -/
def denominator (N P z : ℕ) : ℝ :=
  ∑ d ∈ P.divisors, if d ≤ z then
    goldbachSieveDensity N d *
      ∏ p ∈ d.primeFactors, (1 - goldbachSieveDensity N p)⁻¹ else 0

theorem normalizer_eq_denominator (N P z : ℕ) (hN : 2 ∣ N) (hP : Squarefree P) :
    SelbergOptimal.normalizer (sieve N P hN hP) z = denominator N P z := by
  unfold SelbergOptimal.normalizer denominator
  apply sum_congr rfl
  intro d hd
  rw [BoundingSieve.selbergTerms_apply]
  rfl

theorem denominator_pos (N P : ℕ) (hN : 2 ∣ N) (hP : Squarefree P)
    {z : ℕ} (hz : 1 ≤ z) : 0 < denominator N P z := by
  rw [← normalizer_eq_denominator N P z hN hP]
  exact SelbergOptimal.normalizer_pos _ hz

/-- The local error of this actual sieve is bounded by its actual root count. -/
theorem rem_bound (N P d : ℕ) (hN : 2 ∣ N) (hP : Squarefree P) [NeZero d] :
    |(sieve N P hN hP).rem d| ≤ goldbachSieveRootCount N d := by
  unfold sieve
  rw [PrimePairSieve.imageSieve_rem]
  simpa using goldbach_polynomial_count_density_discrepancy N d

/-- The polynomial root count yields the dimension-two factorizable remainder
bound required by the optimized logarithmic error estimate. -/
theorem rem_lcm_bound (N P : ℕ) (hN : 2 ∣ N) (hP : Squarefree P)
    (a : ℕ) (ha : a ∈ P.divisors) (b : ℕ) (hb : b ∈ P.divisors) :
    |(sieve N P hN hP).rem (Nat.lcm a b)| ≤
      (2 : ℝ) ^ a.primeFactors.card * (2 : ℝ) ^ b.primeFactors.card := by
  let : NeZero a := ⟨(Nat.pos_of_mem_divisors ha).ne'⟩
  let : NeZero b := ⟨(Nat.pos_of_mem_divisors hb).ne'⟩
  let : NeZero (Nat.lcm a b) := ⟨Nat.lcm_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  have ha2 := goldbachSieveRootCount_le_two_pow N a
    (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors ha))
  have hb2 := goldbachSieveRootCount_le_two_pow N b
    (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hb))
  calc
    _ ≤ (goldbachSieveRootCount N (Nat.lcm a b) : ℝ) := rem_bound N P _ hN hP
    _ ≤ (goldbachSieveRootCount N a : ℝ) * goldbachSieveRootCount N b := by
      exact_mod_cast goldbachSieveRootCount_lcm_le N a b
    _ ≤ _ := by exact_mod_cast Nat.mul_le_mul ha2 hb2

/-- An unconditional, explicit finite upper sieve for ordered Goldbach pairs.
Only evenness, squarefreeness of the chosen sieving product, and `z ≥ 1` are
assumed. The remaining denominator is an actual finite arithmetic sum; no
prime-distribution or unproved remainder estimate is hidden in a premise. -/
theorem primePairs_le (N P : ℕ) (hN : 2 ∣ N) (hP : Squarefree P)
    {z : ℕ} (hz : 1 ≤ z) :
    ((PrimePairSieve.primePairs N).card : ℝ) ≤
      ((N - 1 : ℕ) : ℝ) / denominator N P z +
      (z : ℝ) ^ 2 * (1 + Real.log z) ^ 4 + 2 * P.primeFactors.card := by
  let s := sieve N P hN hP
  have he := SelbergOptimal.siftedSum_le_log_error s hz
    (fun a ha b hb => rem_lcm_bound N P hN hP a ha b hb)
  have hsum : s.siftedSum = ((PrimePairSieve.siftedPairs N P).card : ℝ) :=
    PrimePairSieve.imageSieve_siftedSum _ _ _ _ _ _ _ _
  have hmass : s.totalMass = ((N - 1 : ℕ) : ℝ) := by
    simp [s, sieve, PrimePairSieve.imageSieve]
  have hnorm : SelbergOptimal.normalizer s z = denominator N P z :=
    normalizer_eq_denominator N P z hN hP
  rw [hsum, hmass, hnorm] at he
  have hpairs : ((PrimePairSieve.primePairs N).card : ℝ) ≤
      (PrimePairSieve.siftedPairs N P).card + 2 * P.primeFactors.card := by
    exact_mod_cast PrimePairSieve.card_primePairs_le_sifted N P hP.ne_zero
  linarith

/-- With the primorial cutoff, the denominator is a sum over every squarefree
integer up to the cutoff, not an unspecified subset of them. -/
theorem denominator_primorial (N z : ℕ) :
    denominator N (primorial z) z =
      ∑ d ∈ Icc 1 z, if Squarefree d then
        goldbachSieveDensity N d *
          ∏ p ∈ d.primeFactors, (1 - goldbachSieveDensity N p)⁻¹ else 0 := by
  classical
  unfold denominator
  rw [← sum_filter]
  have hsets : (primorial z).divisors.filter (fun d => d ≤ z) =
      (Icc 1 z).filter Squarefree := by
    ext d
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨hd, hdz⟩
      exact ⟨⟨Nat.pos_of_mem_divisors hd, hdz⟩,
        (squarefree_primorial z).squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)⟩
    · rintro ⟨⟨hdpos, hdz⟩, hsq⟩
      exact ⟨Nat.mem_divisors.mpr
        ⟨hsq.dvd_primorial.trans (primorial_dvd_primorial hdz),
          primorial_ne_zero z⟩, hdz⟩
  rw [hsets, sum_filter]

/-- The explicit prime-pair sieve at the canonical primorial product. -/
theorem primePairs_le_primorial (N : ℕ) (hN : 2 ∣ N) {z : ℕ} (hz : 1 ≤ z) :
    ((PrimePairSieve.primePairs N).card : ℝ) ≤
      ((N - 1 : ℕ) : ℝ) / denominator N (primorial z) z +
      (z : ℝ) ^ 2 * (1 + Real.log z) ^ 4 + 2 * (Nat.primesLE z).card := by
  simpa only [primeFactors_primorial] using
    primePairs_le N (primorial z) hN (squarefree_primorial z) hz

end Problem337.GoldbachSelberg

end

end OAI

-- Upstream module OAI.NumberTheory.EgyptianFractions.SmoothRankin

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

/-- A finite nonnegative sum over smooth numbers is bounded by the finite
Euler product. Only the local prime-power series need to be summable. -/
theorem smooth_sum_le_euler_product
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hf1 : f 1 = 1)
    (hmul : ∀ {m n}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hsum : ∀ {p : ℕ}, p.Prime → Summable (fun j : ℕ => ‖f (p ^ j)‖))
    (N : ℕ) (s : Finset ℕ) (hs : ∀ n ∈ s, n ∈ N.smoothNumbers) :
    (∑ n ∈ s, f n) ≤ ∏ p ∈ N.primesBelow, ∑' j : ℕ, f (p ^ j) := by
  classical
  obtain ⟨_, hprod⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    hf1 hmul hsum N
  calc
    (∑ n ∈ s, f n) = ∑ n ∈ s.subtype (fun n => n ∈ N.smoothNumbers), f n :=
      (Finset.sum_subtype_of_mem f hs).symm
    _ ≤ ∑' n : N.smoothNumbers, f n :=
      hprod.summable.sum_le_tsum _ (fun n _ => hf n)
    _ = ∏ p ∈ N.primesBelow, ∑' j : ℕ, f (p ^ j) := hprod.tsum_eq

/-- The elementary exponential weight used in Rankin's tail estimate. -/
theorem rankin_weight_bound {V β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hn : Real.exp V ≤ (n : ℝ)) :
    1 ≤ Real.exp (-β * V) * (n : ℝ) ^ β := by
  have hpow := Real.rpow_le_rpow (le_of_lt (Real.exp_pos V)) hn hβ
  rw [← Real.exp_mul] at hpow
  have h := mul_le_mul_of_nonneg_left hpow (le_of_lt (Real.exp_pos (-β * V)))
  have hid : Real.exp (-β * V) * Real.exp (V * β) = 1 := by
    rw [← Real.exp_add]
    have : -β * V + V * β = 0 := by ring
    rw [this, Real.exp_zero]
  rwa [hid] at h

/-- Rankin's trick followed by a finite Euler product. This form applies to
`f n = τ(n)^r / n`; the local weight then has exponent `-1 + β`. -/
theorem smooth_rankin_bound
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hf1 : f 1 = 1)
    (hmul : ∀ {m n}, Nat.Coprime m n → f (m * n) = f m * f n)
    {V β : ℝ} (hβ : 0 ≤ β)
    (hsum : ∀ {p : ℕ}, p.Prime →
      Summable (fun j : ℕ => ‖f (p ^ j) * ((p ^ j : ℕ) : ℝ) ^ β‖))
    (N : ℕ) (s : Finset ℕ) (hs : ∀ n ∈ s, n ∈ N.smoothNumbers)
    (hlarge : ∀ n ∈ s, Real.exp V ≤ (n : ℝ)) :
    (∑ n ∈ s, f n) ≤ Real.exp (-β * V) *
      (∏ p ∈ N.primesBelow, ∑' j : ℕ, f (p ^ j) * ((p ^ j : ℕ) : ℝ) ^ β) := by
  have hg : ∀ n : ℕ, 0 ≤ f n * (n : ℝ) ^ β := by
    intro n
    exact mul_nonneg (hf n) (Real.rpow_nonneg (Nat.cast_nonneg n) β)
  have hg1 : f 1 * (1 : ℝ) ^ β = 1 := by simp [hf1]
  have hgmul : ∀ {m n : ℕ}, Nat.Coprime m n →
      f (m * n) * ((m * n : ℕ) : ℝ) ^ β =
        (f m * (m : ℝ) ^ β) * (f n * (n : ℝ) ^ β) := by
    intro m n hmn
    rw [hmul hmn, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring
  have heuler := smooth_sum_le_euler_product (fun n => f n * (n : ℝ) ^ β)
    hg (by simpa using hg1) hgmul hsum N s hs
  calc
    (∑ n ∈ s, f n) ≤ ∑ n ∈ s, Real.exp (-β * V) * (f n * (n : ℝ) ^ β) := by
      apply Finset.sum_le_sum
      intro n hn
      have h := mul_le_mul_of_nonneg_left (rankin_weight_bound hβ (hlarge n hn)) (hf n)
      nlinarith
    _ = Real.exp (-β * V) * ∑ n ∈ s, f n * (n : ℝ) ^ β := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-β * V) *
        (∏ p ∈ N.primesBelow, ∑' j : ℕ, f (p ^ j) * ((p ^ j : ℕ) : ℝ) ^ β) :=
      mul_le_mul_of_nonneg_left heuler (le_of_lt (Real.exp_pos _))

/-- The multiplicative weight occurring in divisor harmonic moments. -/
def divisorHarmonicWeight (r n : ℕ) : ℝ :=
  (n.divisors.card : ℝ) ^ r / (n : ℝ)

theorem divisorHarmonicWeight_nonneg (r n : ℕ) : 0 ≤ divisorHarmonicWeight r n := by
  unfold divisorHarmonicWeight
  positivity

theorem divisorHarmonicWeight_one (r : ℕ) : divisorHarmonicWeight r 1 = 1 := by
  simp [divisorHarmonicWeight]

theorem divisorHarmonicWeight_mul (r : ℕ) {m n : ℕ} (h : m.Coprime n) :
    divisorHarmonicWeight r (m * n) = divisorHarmonicWeight r m * divisorHarmonicWeight r n := by
  simp only [divisorHarmonicWeight, h.card_divisors_mul, Nat.cast_mul, mul_pow]
  ring

theorem divisorHarmonicWeight_prime_power (r : ℕ) {p : ℕ} (hp : p.Prime) (j : ℕ)
    (β : ℝ) :
    divisorHarmonicWeight r (p ^ j) * ((p ^ j : ℕ) : ℝ) ^ β =
      ((j + 1 : ℕ) : ℝ) ^ r * ((p : ℝ) ^ (β - 1)) ^ j := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpow : (0 : ℝ) < (p : ℝ) ^ j := pow_pos hpR j
  simp only [divisorHarmonicWeight, Nat.divisors_prime_pow hp, Finset.card_map,
    Finset.card_range, Nat.cast_pow]
  rw [Real.rpow_pow_comm (le_of_lt hpR), Real.rpow_sub_one (ne_of_gt hpow)]
  ring

theorem summable_successor_pow_geometric (r : ℕ) {q : ℝ} (hq : 0 < q) (hqone : q < 1) :
    Summable (fun j : ℕ => ‖((j + 1 : ℕ) : ℝ) ^ r * q ^ j‖) := by
  have hnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hq] using hqone
  have h := (summable_norm_pow_mul_geometric_of_norm_lt_one r hnorm).comp_injective
    Nat.succ_injective
  have h' := h.mul_right q⁻¹
  apply h'.congr
  intro j
  change ‖((j + 1 : ℕ) : ℝ) ^ r * q ^ (j + 1)‖ * q⁻¹ =
    ‖((j + 1 : ℕ) : ℝ) ^ r * q ^ j‖
  rw [pow_succ, ← mul_assoc, norm_mul, Real.norm_eq_abs q, abs_of_pos hq]
  field_simp

theorem divisorHarmonicWeight_local_summable (r : ℕ) {β : ℝ} (hβ : β < 1)
    {p : ℕ} (hp : p.Prime) :
    Summable (fun j : ℕ => ‖divisorHarmonicWeight r (p ^ j) * ((p ^ j : ℕ) : ℝ) ^ β‖) := by
  simp_rw [divisorHarmonicWeight_prime_power r hp]
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact summable_successor_pow_geometric r (Real.rpow_pos_of_pos (by linarith) _)
    (Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith))

/-- Concrete smooth initial-interval Rankin estimate for any natural moment order. -/
theorem divisor_smooth_rankin_bound (r : ℕ) {V β : ℝ} (hβ : 0 ≤ β) (hβone : β < 1)
    (N : ℕ) (s : Finset ℕ) (hs : ∀ n ∈ s, n ∈ N.smoothNumbers)
    (hlarge : ∀ n ∈ s, Real.exp V ≤ (n : ℝ)) :
    (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤ Real.exp (-β * V) *
      (∏ p ∈ N.primesBelow, ∑' j : ℕ,
        ((j + 1 : ℕ) : ℝ) ^ r * ((p : ℝ) ^ (β - 1)) ^ j) := by
  have h := smooth_rankin_bound (divisorHarmonicWeight r) (divisorHarmonicWeight_nonneg r)
    (divisorHarmonicWeight_one r) (divisorHarmonicWeight_mul r) hβ
    (divisorHarmonicWeight_local_summable r hβone) N s hs hlarge
  change (∑ n ∈ s, divisorHarmonicWeight r n) ≤ _
  apply h.trans_eq
  apply congrArg (fun x : ℝ => Real.exp (-β * V) * x)
  apply Finset.prod_congr rfl
  intro p hp
  apply tsum_congr
  intro j
  exact divisorHarmonicWeight_prime_power r (Nat.prime_of_mem_primesBelow hp) j β

/-- The unweighted finite Euler-product bound for harmonic divisor moments. -/
theorem divisor_harmonic_sum_le_euler_product (r N : ℕ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, n ∈ N.smoothNumbers) :
    (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
      ∏ p ∈ N.primesBelow, ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ r * ((p : ℝ)⁻¹) ^ j := by
  have hlarge : ∀ n ∈ s, Real.exp (0 : ℝ) ≤ (n : ℝ) := by
    intro n hn
    rw [Real.exp_zero]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_zero_of_mem_smoothNumbers (hs n hn))
  simpa [Real.rpow_neg_one] using divisor_smooth_rankin_bound r (le_refl (0 : ℝ)) (by norm_num : (0 : ℝ) < 1)
    N s hs hlarge

/-- A local Euler factor, in the indexing convenient for Rankin's trick. -/
def divisorEulerFactor (r p : ℕ) (β : ℝ) : ℝ :=
  ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ r * ((p : ℝ) ^ (β - 1)) ^ j

theorem divisorEulerFactor_one_le (r : ℕ) {p : ℕ} (hp : p.Prime) {β : ℝ}
    (hβ : β < 1) : 1 ≤ divisorEulerFactor r p β := by
  have hs := divisorHarmonicWeight_local_summable r hβ hp
  simp_rw [divisorHarmonicWeight_prime_power r hp] at hs
  have h := hs.of_norm.sum_le_tsum {0} (by
    intro j _
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    positivity)
  simpa [divisorEulerFactor] using h

/-- Logarithmic local-factor estimates turn the Rankin Euler product into a
single exponential. This is the precise smooth initial-interval bound used in the
divisor-moment decomposition. -/
theorem divisor_smooth_rankin_log_bound (r : ℕ) {V β C : ℝ}
    (hβ : 0 ≤ β) (hβone : β < 1) (N : ℕ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, n ∈ N.smoothNumbers)
    (hlarge : ∀ n ∈ s, Real.exp V ≤ (n : ℝ))
    (hlocal : ∀ p ∈ N.primesBelow,
      Real.log (divisorEulerFactor r p β) ≤ C * (p : ℝ) ^ (β - 1)) :
    (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
      Real.exp (-β * V + C * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (β - 1)) := by
  have hpos : ∀ p ∈ N.primesBelow, 0 < divisorEulerFactor r p β := by
    intro p hp
    have := divisorEulerFactor_one_le r (Nat.prime_of_mem_primesBelow hp) hβone
    linarith
  have hprodpos : 0 < ∏ p ∈ N.primesBelow, divisorEulerFactor r p β := Finset.prod_pos hpos
  have hlog : Real.log (∏ p ∈ N.primesBelow, divisorEulerFactor r p β) ≤
      C * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (β - 1) := by
    rw [Real.log_prod (fun p hp => ne_of_gt (hpos p hp)), Finset.mul_sum]
    exact Finset.sum_le_sum hlocal
  have hprod := (Real.log_le_iff_le_exp hprodpos).mp hlog
  have hrank := divisor_smooth_rankin_bound r hβ hβone N s hs hlarge
  change (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
    Real.exp (-β * V) * ∏ p ∈ N.primesBelow, divisorEulerFactor r p β at hrank
  calc
    (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
        Real.exp (-β * V) * ∏ p ∈ N.primesBelow, divisorEulerFactor r p β := hrank
    _ ≤ Real.exp (-β * V) *
        Real.exp (C * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (β - 1)) :=
      mul_le_mul_of_nonneg_left hprod (le_of_lt (Real.exp_pos _))
    _ = Real.exp (-β * V + C * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (β - 1)) :=
      (Real.exp_add _ _).symm

end Problem337

end

end OAI


open Finset

namespace CentralSelberg

theorem prime_log_mass (m : ℕ) (hm : 0 < m) :
    (∑ p ∈ m.primeFactors, Real.log (p:ℝ)) ≤ Real.log m := by
  rw [← Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  rw [← Nat.cast_prod]
  apply Real.log_le_log
  · exact_mod_cast Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  · exact_mod_cast Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)

/-- An elementary upper bound for the weighted prime harmonic sum via counting multiples. -/
theorem weighted_harmonic (y : ℕ) (hy : 1 ≤ y) :
    (∑ p ∈ y.primesLE, Real.log (p:ℝ)/(p:ℝ)) ≤ 2*Real.log y := by
  let T := Finset.Ioc 0 y
  have hcnt (p : ℕ) : ((T.filter (p ∣ ·)).card:ℝ) = (y/p:ℕ) := by
    exact_mod_cast Nat.Ioc_filter_dvd_card_eq_div y p
  have hsum : (∑ p ∈ y.primesLE, ((y/p:ℕ):ℝ)*Real.log p) ≤ (y:ℝ)*Real.log y := by
    calc
      _ = ∑ p ∈ y.primesLE, ∑ k ∈ T, if p ∣ k then Real.log p else 0 := by
        refine sum_congr rfl fun p _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcnt]
      _ = ∑ k ∈ T, ∑ p ∈ y.primesLE, if p ∣ k then Real.log p else 0 := Finset.sum_comm
      _ ≤ ∑ _k ∈ T, Real.log y := by
        refine sum_le_sum fun k hk => ?_
        obtain ⟨hkpos, hky⟩ := Finset.mem_Ioc.mp hk
        rw [← Finset.sum_filter]
        have heq : (y.primesLE.filter (· ∣ k)) = k.primeFactors := by
          ext p
          simp only [Finset.mem_filter, Nat.mem_primesLE, Nat.mem_primeFactors]
          exact ⟨fun h => ⟨h.1.2, h.2, hkpos.ne'⟩, fun h => ⟨⟨(Nat.le_of_dvd hkpos h.2.1).trans hky, h.1⟩, h.2.1⟩⟩
        rw [heq]
        exact (prime_log_mass _ hkpos).trans (Real.log_le_log (by exact_mod_cast hkpos) (by exact_mod_cast hky))
      _ = _ := by simp [T]
  have hyR : (0:ℝ) < y := by exact_mod_cast hy
  apply (le_of_mul_le_mul_left (a := (y:ℝ)) ?_ hyR)
  calc
    _ = ∑ p ∈ y.primesLE, (y:ℝ)*(Real.log p/p) := Finset.mul_sum ..
    _ ≤ ∑ p ∈ y.primesLE, 2*(((y/p:ℕ):ℝ)*Real.log p) := by
      refine sum_le_sum fun p hp => ?_
      obtain ⟨hpy,hprime⟩ := Nat.mem_primesLE.mp hp
      have hp0 : (0:ℝ) < p := by exact_mod_cast hprime.pos
      have hd : 1 ≤ y/p := (Nat.le_div_iff_mul_le hprime.pos).mpr (by simpa)
      have hdiv : y ≤ 2*((y/p)*p) := by
        have he := Nat.div_add_mod y p
        have hr := Nat.mod_lt y hprime.pos
        have hpq := Nat.mul_le_mul_right p hd
        rw [Nat.mul_comm p] at he
        omega
      have hr : (y:ℝ) ≤ 2*(((y/p:ℕ):ℝ)*p) := by exact_mod_cast hdiv
      rw [← mul_div_assoc, div_le_iff₀ hp0]
      calc
        _ ≤ (2*(((y/p:ℕ):ℝ)*p))*Real.log p :=
          mul_le_mul_of_nonneg_right hr (Real.log_nonneg (by exact_mod_cast hprime.one_le))
        _ = _ := by ring
    _ ≤ _ := by rw [← Finset.mul_sum]; linarith

end CentralSelberg


open Finset
namespace CentralSelberg

/-- First logarithmic moment of a finite Euler product. -/
theorem powerset_moment (s : Finset ℕ) (g l : ℕ → ℝ)
    (hg : ∀ i ∈ s, 0 ≤ g i) :
    (∑ t ∈ s.powerset, (∏ i ∈ t, g i)*(∑ i ∈ t, l i)) =
      (∏ i ∈ s, (1+g i)) * (∑ i ∈ s, g i/(1+g i)*l i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hn : 1+g a ≠ 0 := by have := hg a (Finset.mem_insert_self ..); linarith
    have hi := ih (fun p hp => hg p (mem_insert_of_mem hp))
    rw [Finset.sum_powerset_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hexp : (∑ t ∈ s.powerset, (∏ i ∈ insert a t, g i)*(∑ i ∈ insert a t, l i)) =
        g a*l a * (∏ i ∈ s, (1+g i)) +
        g a * (∑ t ∈ s.powerset, (∏ i ∈ t, g i)*(∑ i ∈ t, l i)) := by
      rw [Finset.prod_one_add s, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t ht => ?_
      have hat : a ∉ t := fun h => ha ((Finset.mem_powerset.mp ht) h)
      rw [Finset.prod_insert hat, Finset.sum_insert hat]
      ring
    rw [hexp, hi]
    field_simp
    ring

end CentralSelberg


open Finset
open OAI.Problem337
namespace CentralSelberg
noncomputable section

def rho (n p : ℕ) := goldbachSieveDensity n p

def wgt (n p : ℕ) : ℝ := rho n p * (1-rho n p)⁻¹

def loc (n p : ℕ) : ℝ := if 2<p ∧ p∣n then 1+1/((p:ℝ)-2) else 1

theorem rho_bounds (n : ℕ) (hn : 2∣n) (p : ℕ) (hp : p.Prime) :
    0 < rho n p ∧ rho n p < 1 :=
  ⟨goldbachSieveDensity_prime_pos n p hp, goldbachSieveDensity_prime_lt_one n p hp (fun _ => hn)⟩

theorem wgt_pos (n : ℕ) (hn : 2∣n) (p : ℕ) (hp : p.Prime) : 0 < wgt n p := by
  have h := rho_bounds n hn p hp
  exact mul_pos h.1 (inv_pos.mpr (by linarith [h.2]))

theorem wgt_ratio (n : ℕ) (hn : 2∣n) (p : ℕ) (hp : p.Prime) :
    wgt n p/(1+wgt n p) = rho n p := by
  have h := (rho_bounds n hn p hp).2
  have hpos := wgt_pos n hn p hp
  unfold wgt at *
  field_simp
  ring

theorem harmonic_product (y : ℕ) :
    Real.log ((y:ℝ)+1) ≤ ∏ p ∈ y.primesLE, (1-(p:ℝ)⁻¹)⁻¹ := by
  let S := Finset.Icc 1 y
  have hsm (k : ℕ) (hk : k ∈ S) : k ∈ (y+1).smoothNumbers :=
    Nat.mem_smoothNumbers_of_lt (Finset.mem_Icc.mp hk).1 (by have := (Finset.mem_Icc.mp hk).2; omega)
  have H := divisor_harmonic_sum_le_euler_product 0 (y+1) S hsm
  simp only [pow_zero, one_mul, one_div] at H
  have hgeo (p : ℕ) (hp : p∈y.primesLE) : (∑' j : ℕ, ((p:ℝ)⁻¹)^j) = (1-(p:ℝ)⁻¹)⁻¹ := by
    apply tsum_geometric_of_lt_one
    · positivity
    · exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt)
  calc
    _ ≤ (harmonic y:ℝ) := by simpa using log_add_one_le_harmonic y
    _ = ∑ k ∈ S, (k:ℝ)⁻¹ := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rfl
    _ ≤ _ := H.trans_eq (Finset.prod_congr rfl hgeo)

end
end CentralSelberg


open Finset OAI.Problem337
namespace CentralSelberg
noncomputable section

def singular (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors.filter (fun p => 2<p), (1+1/((p:ℝ)-2))

theorem factor_one_le (n p : ℕ) : 1 ≤ loc n p := by
  unfold loc
  split
  · rename_i h
    have : (2:ℝ)<p := by exact_mod_cast h.1
    linarith [show 0≤1/((p:ℝ)-2) by positivity]
  · rfl

theorem singular_one_le (n : ℕ) : 1 ≤ singular n := by
  apply Finset.one_le_prod₀
  intro p hp
  have h : (2:ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2
  linarith [show 0 ≤ 1/((p:ℝ)-2) by positivity]

theorem local_correction (n y : ℕ) (hn : 0<n) :
    (∏ p ∈ y.primesLE, loc n p) ≤ singular n := by
  let T := y.primesLE.filter (fun p => 2<p ∧ p∣n)
  have sub : T ⊆ n.primeFactors.filter (fun p => 2<p) := by
    intro p hp
    obtain ⟨h,ho,hd⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primesLE h,hd,hn.ne'⟩,ho⟩
  change (∏ p ∈ y.primesLE, if 2<p ∧ p∣n then _ else 1) ≤ _
  rw [← Finset.prod_filter]
  exact Finset.prod_le_prod_of_subset_of_one_le₀ sub (fun p hp => by
    have h : (2:ℝ)<p := by exact_mod_cast (Finset.mem_filter.mp hp).2.1
    positivity) (fun p hp _ => by
    have h : (2:ℝ)<p := by exact_mod_cast (Finset.mem_filter.mp hp).2
    linarith [show 0 ≤ 1/((p:ℝ)-2) by positivity])

theorem euler_mass (n y : ℕ) (hn : 2∣n) (hnp : 0<n) :
    (Real.log ((y:ℝ)+1))^2 ≤ 2*singular n*(∏ p ∈ y.primesLE, (1+wgt n p)) := by
  let T := y.primesLE
  have hloc (p : ℕ) (hp : p ∈ T) :
      ((1-(p:ℝ)⁻¹)⁻¹)^2 ≤ (if p=2 then 2 else 1)*loc n p*(1+wgt n p) := by
    have hpP := Nat.prime_of_mem_primesLE hp
    have hr := goldbachSieveDensity_prime n p hpP
    unfold wgt rho loc
    rw [hr]
    by_cases h2 : p=2
    · subst p; norm_num [hn]
    · have hh : 2 < p := by have := hpP.two_le; omega
      have hrp : (2:ℝ) < p := by exact_mod_cast hh
      have hp0 : (0:ℝ)<p := by linarith
      by_cases hd : p∣n
      · simp only [hh,hd,h2,if_true,true_and,if_false,one_mul]
        have hp1 : 0 < (p:ℝ) - 1 := by linarith
        have hp2 : 0 < (p:ℝ) - 2 := by linarith
        field_simp [hp1, hp2]
        nlinarith [sq_nonneg (p:ℝ)]
      · simp only [hh,hd,h2,if_true,true_and,if_false,one_mul]
        have hp1 : 0 < (p:ℝ) - 1 := by linarith
        have hp2 : 0 < (p:ℝ) - 2 := by linarith
        field_simp [hp1, hp2]
        nlinarith [sq_nonneg (p:ℝ)]
  have htwo : (∏ p ∈ T, (if p=2 then (2:ℝ) else 1)) ≤ 2 := by
    rw [Finset.prod_ite_eq']; split <;> norm_num
  have hpos := Finset.prod_nonneg (s := T) (f := fun p => 1+wgt n p) (fun p hp => by
    have := wgt_pos n hn p (Nat.prime_of_mem_primesLE hp); linarith)
  have hcorr := local_correction n y hnp
  have hcpos := Finset.prod_nonneg (s := T) (f := loc n)
    (fun p hp => by linarith [factor_one_le n p])
  have htwo' := mul_le_mul htwo hcorr hcpos (by norm_num : (0:ℝ) ≤ 2)
  calc
    _ ≤ (∏ p ∈ T, (1-(p:ℝ)⁻¹)⁻¹)^2 :=
      pow_le_pow_left₀ (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) y])) (harmonic_product y) _
    _ = ∏ p ∈ T, ((1-(p:ℝ)⁻¹)⁻¹)^2 := (Finset.prod_pow ..).symm
    _ ≤ ∏ p ∈ T, (if p=2 then 2 else 1)*loc n p*(1+wgt n p) := Finset.prod_le_prod₀
      (fun p hp => sq_nonneg _) hloc
    _ ≤ _ := by
      simp only [Finset.prod_mul_distrib]
      exact mul_le_mul_of_nonneg_right htwo' hpos

end
end CentralSelberg


open Finset OAI.Problem337
namespace CentralSelberg
noncomputable section

def mass (n y : ℕ) : ℝ := ∏ p ∈ y.primesLE, (1+wgt n p)
def index (t : Finset ℕ) : ℕ := ∏ p ∈ t, p
def weight (n : ℕ) (t : Finset ℕ) : ℝ := ∏ p ∈ t, wgt n p

theorem denominator_as_sum (n y z : ℕ) :
    GoldbachSelberg.denominator n (primorial y) z =
      ∑ t ∈ y.primesLE.powerset, if index t ≤ z then weight n t else 0 := by
  classical
  let P := primorial y
  have prime (t : Finset ℕ) (ht : t∈y.primesLE.powerset) : ∀ p∈t, p.Prime :=
    fun p hp => Nat.prime_of_mem_primesLE ((Finset.mem_powerset.mp ht) hp)
  have hfac (t : Finset ℕ) (ht : t∈y.primesLE.powerset) :
      (index t).primeFactors=t := Nat.primeFactors_prod (prime t ht)
  have hmap : P.divisors = y.primesLE.powerset.image index := by
    ext d
    constructor
    · intro hd
      have hsq := (squarefree_primorial y).squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
      have hmono := Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) (primorial_ne_zero y)
      rw [primeFactors_primorial] at hmono
      exact Finset.mem_image.mpr ⟨d.primeFactors, Finset.mem_powerset.mpr hmono, Nat.prod_primeFactors_of_squarefree hsq⟩
    · rintro hd
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hd
      exact Nat.mem_divisors.mpr ⟨Finset.prod_dvd_prod_of_subset _ _ _ (Finset.mem_powerset.mp ht),primorial_ne_zero y⟩
  unfold GoldbachSelberg.denominator
  change (∑ d ∈ P.divisors, _) = _
  rw [hmap, Finset.sum_image (fun a ha b hb hh => (hfac a ha).symm.trans ((congrArg Nat.primeFactors hh).trans (hfac b hb)))]
  refine Finset.sum_congr rfl fun t ht => ?_
  split_ifs
  · rw [hfac t ht, index, (goldbachSieveDensity_isMultiplicative n).map_prod_of_prime t (prime t ht)]
    exact (Finset.prod_mul_distrib).symm
  · rfl

theorem retained (n y : ℕ) (hn : 2∣n) (hy : 2≤y) :
    mass n y ≤ 2 * GoldbachSelberg.denominator n (primorial y) (y^8) := by
  let T := y.primesLE.powerset
  let W := weight n
  let D := GoldbachSelberg.denominator n (primorial y) (y^8)
  have wp (t : Finset ℕ) (ht : t ∈ T) : 0 ≤ W t :=
    Finset.prod_nonneg fun p hp => (wgt_pos n hn p (Nat.prime_of_mem_primesLE ((Finset.mem_powerset.mp ht) hp))).le
  have total : (∑ t ∈ T, W t) = mass n y := (Finset.prod_one_add _).symm
  have heavy_point (t : Finset ℕ) (ht : t ∈ T) :
      (if y^8 < index t then W t else 0)*(8*Real.log y) ≤ W t*Real.log (index t) := by
    have hip : 0 < index t := Finset.prod_pos fun p hp =>
      (Nat.prime_of_mem_primesLE ((Finset.mem_powerset.mp ht) hp)).pos
    split
    · rename_i hl
      apply mul_le_mul_of_nonneg_left _ (wp t ht)
      have hlog := Real.log_le_log (show (0:ℝ) < ((y^8:ℕ):ℝ) by positivity) (show ((y^8:ℕ):ℝ) ≤ index t by exact_mod_cast hl.le)
      simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using hlog
    · rw [zero_mul]
      exact mul_nonneg (wp t ht) (Real.log_nonneg (by exact_mod_cast hip))
  have mean := powerset_moment y.primesLE (wgt n) (fun p => Real.log (p:ℝ))
    (fun p hp => (wgt_pos n hn p (Nat.prime_of_mem_primesLE hp)).le)
  have hsumlog (t : Finset ℕ) (ht : t∈T) :
      Real.log (index t) = ∑ p ∈ t, Real.log (p:ℝ) := by
    unfold index
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp; exact_mod_cast (Nat.prime_of_mem_primesLE ((Finset.mem_powerset.mp ht) hp)).ne_zero
  have bound : (∑ p ∈ y.primesLE, wgt n p/(1+wgt n p)*Real.log p) ≤ 4*Real.log y := by
    calc
      _ ≤ ∑ p ∈ y.primesLE, 2*(Real.log p/p) := by
        refine sum_le_sum fun p hp => ?_
        have hpP := Nat.prime_of_mem_primesLE hp
        have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpP.one_le)
        rw [wgt_ratio n hn p hpP]
        unfold rho
        rw [goldbachSieveDensity_prime n p hpP]
        split <;> ring_nf <;> first | rfl | nlinarith [mul_nonneg hlog (inv_nonneg.mpr (Nat.cast_nonneg p : (0:ℝ) ≤ _))]
      _ ≤ _ := by rw [←Finset.mul_sum]; linarith [weighted_harmonic y (by omega)]
  have hmass : 0 ≤ mass n y := Finset.prod_nonneg (fun p hp => by
    linarith [wgt_pos n hn p (Nat.prime_of_mem_primesLE hp)])
  have moment : (∑ t ∈ T, W t*Real.log (index t)) ≤ mass n y * (4*Real.log y) := by
    calc
      _ = ∑ t ∈ y.primesLE.powerset, (∏ p ∈ t, wgt n p)*(∑ p ∈ t, Real.log p) :=
        sum_congr rfl (fun t ht => by rw [hsumlog t ht]; rfl)
      _ = _ := mean
      _ ≤ _ := mul_le_mul_of_nonneg_left bound hmass
  have hdiff : (∑ t ∈ T, if y^8 < index t then W t else 0) = mass n y - D := by
    rw [← total, show D = _ from denominator_as_sum n y (y^8), ← Finset.sum_sub_distrib]
    apply sum_congr rfl; intro t _; by_cases h : index t ≤ y^8 <;> simp [h,not_lt.mpr,lt_of_not_ge,W]
  have hh := (sum_le_sum heavy_point).trans moment
  rw [← Finset.sum_mul, hdiff] at hh
  have hl : 0 < Real.log y := Real.log_pos (by exact_mod_cast (show 1<y by omega))
  change mass n y ≤ 2*D
  apply (le_of_mul_le_mul_right (a := Real.log y) ?_ hl)
  linarith only [hh]

end
end CentralSelberg


open Filter Topology
namespace CentralSelberg

/-- A small prime cutoff with enough logarithmic length for the denominator. -/
theorem scales :
    ∀ᶠ n : ℕ in atTop, ∃ y : ℕ, 2≤y ∧
       Real.log (n:ℝ) ≤ 32*Real.log ((y:ℝ)+1) ∧
       (((y^8:ℕ):ℝ)^2*(1+Real.log (y^8:ℕ))^4 + 2*(y:ℝ)) * (Real.log n)^2 ≤ 18*n := by
  have hs := (isLittleO_log_rpow_rpow_atTop (6:ℝ) (by norm_num : (0:ℝ)<1/2)).bound (by norm_num : (0:ℝ)<1)
  have hs' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hs
  have hl := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
  filter_upwards [hs',hl,eventually_ge_atTop (2^32:ℕ)] with n hn hlog hn32
  change 1 ≤ Real.log (n:ℝ) at hlog
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hn1 : 1 ≤ (n:ℝ) := by linarith [show (2:ℝ)^32 ≤ n by exact_mod_cast hn32]
  have hbig : (Real.log n)^6 ≤ Real.sqrt n := by
    have hr : (n:ℝ)^(1/2:ℝ) = Real.sqrt n := (Real.sqrt_eq_rpow _).symm
    simpa only [Real.norm_eq_abs, Real.rpow_natCast_mul, Real.rpow_ofNat, abs_of_nonneg (by positivity : 0≤(Real.log n)^6),
      abs_of_nonneg (Real.rpow_nonneg hn0.le _), one_mul, hr, abs_of_nonneg (Real.sqrt_nonneg _)] using hn
  let u : ℝ := (n:ℝ)^(1/32:ℝ)
  let y := ⌊u⌋₊
  have hu : 0≤u := Real.rpow_nonneg hn0.le _
  have hu32 : u^32 = n := by
    rw [show u^32 = (n:ℝ)^((1/32:ℝ)*32) from (Real.rpow_mul_natCast hn0.le _ _).symm]
    norm_num
  have hy2 : 2≤y := by
    apply (Nat.le_floor_iff hu).mpr
    by_contra! h
    have hp := pow_lt_pow_left₀ h hu (by decide : 32≠0)
    rw [hu32] at hp
    exact (not_lt_of_ge (show (2:ℝ)^32 ≤ n by exact_mod_cast hn32)) hp
  have hyp : (0:ℝ)<y := by exact_mod_cast (show 0<y by omega)
  have hyr : (1:ℝ)≤y := by exact_mod_cast (show 1≤y by omega)
  have hlow := pow_le_pow_left₀ hyp.le (Nat.floor_le hu : (y:ℝ) ≤ u) 32
  have hhigh := pow_le_pow_left₀ hu (Nat.lt_floor_add_one u).le 32
  rw [hu32] at hlow hhigh
  have hylog : Real.log (n:ℝ) ≤ 32*Real.log ((y:ℝ)+1) := by
    have hh := Real.log_le_log hn0 hhigh
    simpa only [Real.log_pow, Nat.cast_ofNat, y] using hh
  have hy16 : (y:ℝ)^16 ≤ Real.sqrt n := by
    apply (Real.le_sqrt (by positivity) hn0.le).mpr
    convert hlow using 1 <;> ring
  have hy1 : (y:ℝ) ≤ Real.sqrt n := by
    exact (le_self_pow₀ hyr (by decide : 16≠0)).trans hy16
  have hly : Real.log ((y^8:ℕ):ℝ) ≤ Real.log n := by
    apply Real.log_le_log (by positivity)
    rw [Nat.cast_pow]
    exact (pow_le_pow_right₀ hyr (by decide : 8≤32)).trans hlow
  have hp4 : (1+Real.log ((y^8:ℕ):ℝ))^4 ≤ (2*Real.log n)^4 :=
    pow_le_pow_left₀ (by have := Real.log_nonneg (show (1:ℝ)≤(y^8:ℕ) by exact_mod_cast (Nat.one_le_pow _ _ (by omega : 1≤y))); linarith) (by linarith) _
  rw [Nat.cast_pow] at hp4
  have hsqr := Real.sq_sqrt hn0.le
  have hmain : Real.sqrt n*(Real.log n)^6 ≤ n := by nlinarith [mul_le_mul_of_nonneg_left hbig (Real.sqrt_nonneg n)]
  have hminor : Real.sqrt n*(Real.log n)^2 ≤ n :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlog (by decide : 2≤6)) (Real.sqrt_nonneg n)).trans hmain
  refine ⟨y,hy2,hylog,?_⟩
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.sqrt n*(2*Real.log n)^4 + 2*Real.sqrt n)*(Real.log n)^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply add_le_add _ (by linarith only [hy1])
      apply mul_le_mul (by convert hy16 using 1 <;> ring) hp4 (by positivity) (Real.sqrt_nonneg n)
    _ ≤ _ := by linarith only [hmain,hminor]

end CentralSelberg

open Finset Filter OAI.Problem337
namespace CentralSelberg
noncomputable section

def w (k : ℕ) : ℝ := if k.Prime then Real.log k else 0
def C (n : ℕ) : ℝ := ∑ p ∈ (range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n), w p*w (n-p)

theorem center_card (n : ℕ) (hn : 2 ≤ n) : C n ≤ ((PrimePairSieve.primePairs n).card:ℝ)*(Real.log n)^2 := by
  let T := (range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n)
  have hw (k : ℕ) (hk : k.Prime) : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk.one_le)
  calc
    _ ≤ ∑ p ∈ T, if p∈PrimePairSieve.primePairs n then (Real.log n)^2 else 0 := by
      refine sum_le_sum fun p hp => ?_
      obtain ⟨hpx,h1,h2⟩ := Finset.mem_filter.mp hp
      have hp' := Finset.mem_range.mp hpx
      by_cases hpP : p.Prime
      · by_cases hqP : (n-p).Prime
        · have mem : p∈PrimePairSieve.primePairs n := Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨hpP.one_le, by have := hqP.one_le; omega⟩, hpP,hqP⟩
          rw [if_pos mem, w, if_pos hpP, w, if_pos hqP, pow_two]
          exact mul_le_mul
            (Real.log_le_log (by exact_mod_cast hpP.pos) (by exact_mod_cast (show p≤n by omega)))
            (Real.log_le_log (by exact_mod_cast hqP.pos) (by exact_mod_cast Nat.sub_le n p))
            (hw _ hqP) (Real.log_nonneg (by exact_mod_cast (show 1≤n by omega)))
        · simp [w,hqP,PrimePairSieve.primePairs]
      · simp [w,hpP,PrimePairSieve.primePairs]
    _ = ((T.filter (·∈PrimePairSieve.primePairs n)).card:ℝ)*(Real.log n)^2 := by rw [←sum_filter]; simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card (fun p hp => (mem_filter.mp hp).2))) (sq_nonneg _)

theorem central_upper :
    ∃ K : ℝ, 0<K ∧ ∃ X : ℕ, ∀ n≥X, Even n → C n ≤ K*(n:ℝ)* singular n := by
  obtain ⟨X,hX⟩ := eventually_atTop.mp scales
  refine ⟨4114,by norm_num,max X 2,?_⟩
  intro n hn he
  have hn2 : 2 ≤ n := (le_max_right ..).trans hn
  have hn0 : 0<n := by omega
  obtain ⟨y,hy,hlog,herr⟩ := hX n ((le_max_left ..).trans hn)
  have he' : 2∣n := even_iff_two_dvd.mp he
  have zpos : 1≤ y^8 := Nat.one_le_pow _ _ (by omega)
  let D := GoldbachSelberg.denominator n (primorial y) (y^8)
  have hD : 0<D := GoldbachSelberg.denominator_pos n _ he' (squarefree_primorial _) zpos
  have hsing := singular_one_le n
  have hDen : (Real.log n)^2 ≤ 4096 * singular n * D := by
    have hp : 0≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1≤n by omega))
    have hsq := pow_le_pow_left₀ hp hlog 2
    have hEu := euler_mass n y he' hn0
    have hcut := retained n y he' hy
    change _ ≤ 2*singular n * mass n y at hEu
    change mass n y ≤ 2*D at hcut
    nlinarith only [hsq,hEu,mul_le_mul_of_nonneg_left hcut (a := singular n) (by linarith)]
  have first : (((n-1:ℕ):ℝ)/D)*(Real.log n)^2 ≤ 4096*(n:ℝ)*singular n := by
    have hnle : ((n-1:ℕ):ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
    calc
      _ ≤ ((n:ℝ)/D)*(Real.log n)^2 := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hnle hD.le) (sq_nonneg _)
      _ ≤ ((n:ℝ)/D)*(4096*singular n*D) := mul_le_mul_of_nonneg_left hDen (by positivity)
      _ = _ := by field_simp
  have hcard : ((Nat.primesLE y).card:ℝ) ≤ y := by
    exact_mod_cast Finset.card_le_card (s := y.primesLE) (t := Icc 1 y) (fun p hp =>
      Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hp).one_le,(Nat.mem_primesLE.mp hp).1⟩) |>.trans_eq (by simp)
  have hs := GoldbachSelberg.primePairs_le n (primorial y) he' (squarefree_primorial _) zpos
  rw [primeFactors_primorial] at hs
  change _ ≤ ((n-1:ℕ):ℝ)/D + _ + _ at hs
  have hb := center_card n hn2
  have heP := mul_le_mul_of_nonneg_right hs (sq_nonneg (Real.log n))
  have hbc := mul_le_mul_of_nonneg_right hcard (sq_nonneg (Real.log n))
  have hsn := mul_le_mul_of_nonneg_left hsing (Nat.cast_nonneg (α:=ℝ) n)
  nlinarith only [hb, heP, hbc, herr, first, hsn]

end
end CentralSelberg

open Filter Topology
namespace CentralSelberg

theorem scales2 :
    ∀ᶠ n : ℕ in atTop, ∃ y : ℕ, 2≤y ∧ y ≤ n ∧
       Real.log (n:ℝ) ≤ 32*Real.log ((y:ℝ)+1) ∧
       (((y^8:ℕ):ℝ)^2*(1+Real.log (y^8:ℕ))^4 + 2*(y:ℝ)) * (Real.log n)^2 ≤ 18*n := by
  have hs := (isLittleO_log_rpow_rpow_atTop (6:ℝ) (by norm_num : (0:ℝ)<1/2)).bound (by norm_num : (0:ℝ)<1)
  have hs' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hs
  have hl := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
  filter_upwards [hs',hl,eventually_ge_atTop (2^32:ℕ)] with n hn hlog hn32
  change 1 ≤ Real.log (n:ℝ) at hlog
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hn1 : 1 ≤ (n:ℝ) := by linarith [show (2:ℝ)^32 ≤ n by exact_mod_cast hn32]
  have hbig : (Real.log n)^6 ≤ Real.sqrt n := by
    have hr : (n:ℝ)^(1/2:ℝ) = Real.sqrt n := (Real.sqrt_eq_rpow _).symm
    simpa only [Real.norm_eq_abs, Real.rpow_natCast_mul, Real.rpow_ofNat, abs_of_nonneg (by positivity : 0≤(Real.log n)^6),
      abs_of_nonneg (Real.rpow_nonneg hn0.le _), one_mul, hr, abs_of_nonneg (Real.sqrt_nonneg _)] using hn
  let u : ℝ := (n:ℝ)^(1/32:ℝ)
  let y := ⌊u⌋₊
  have hu : 0≤u := Real.rpow_nonneg hn0.le _
  have hu32 : u^32 = n := by
    rw [show u^32 = (n:ℝ)^((1/32:ℝ)*32) from (Real.rpow_mul_natCast hn0.le _ _).symm]
    norm_num
  have hy2 : 2≤y := by
    apply (Nat.le_floor_iff hu).mpr
    by_contra! h
    have hp := pow_lt_pow_left₀ h hu (by decide : 32≠0)
    rw [hu32] at hp
    exact (not_lt_of_ge (show (2:ℝ)^32 ≤ n by exact_mod_cast hn32)) hp
  have hyn : y ≤ n := by
    have h1 : (y:ℝ) ≤ u := Nat.floor_le hu
    have h2 : u ≤ (n:ℝ) := by
      have hx := Real.rpow_le_rpow_of_exponent_le hn1 (show (1/32:ℝ) ≤ 1 by norm_num)
      simpa [u] using hx
    exact_mod_cast h1.trans h2
  have hyp : (0:ℝ)<y := by exact_mod_cast (show 0<y by omega)
  have hyr : (1:ℝ)≤y := by exact_mod_cast (show 1≤y by omega)
  have hlow := pow_le_pow_left₀ hyp.le (Nat.floor_le hu : (y:ℝ) ≤ u) 32
  have hhigh := pow_le_pow_left₀ hu (Nat.lt_floor_add_one u).le 32
  rw [hu32] at hlow hhigh
  have hylog : Real.log (n:ℝ) ≤ 32*Real.log ((y:ℝ)+1) := by
    have hh := Real.log_le_log hn0 hhigh
    simpa only [Real.log_pow, Nat.cast_ofNat, y] using hh
  have hy16 : (y:ℝ)^16 ≤ Real.sqrt n := by
    apply (Real.le_sqrt (by positivity) hn0.le).mpr
    convert hlow using 1 <;> ring
  have hy1 : (y:ℝ) ≤ Real.sqrt n := by
    exact (le_self_pow₀ hyr (by decide : 16≠0)).trans hy16
  have hly : Real.log ((y^8:ℕ):ℝ) ≤ Real.log n := by
    apply Real.log_le_log (by positivity)
    rw [Nat.cast_pow]
    exact (pow_le_pow_right₀ hyr (by decide : 8≤32)).trans hlow
  have hp4 : (1+Real.log ((y^8:ℕ):ℝ))^4 ≤ (2*Real.log n)^4 :=
    pow_le_pow_left₀ (by have := Real.log_nonneg (show (1:ℝ)≤(y^8:ℕ) by exact_mod_cast (Nat.one_le_pow _ _ (by omega : 1≤y))); linarith) (by linarith) _
  rw [Nat.cast_pow] at hp4
  have hsqr := Real.sq_sqrt hn0.le
  have hmain : Real.sqrt n*(Real.log n)^6 ≤ n := by nlinarith [mul_le_mul_of_nonneg_left hbig (Real.sqrt_nonneg n)]
  have hminor : Real.sqrt n*(Real.log n)^2 ≤ n :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlog (by decide : 2≤6)) (Real.sqrt_nonneg n)).trans hmain
  refine ⟨y,hy2,hyn,hylog,?_⟩
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.sqrt n*(2*Real.log n)^4 + 2*Real.sqrt n)*(Real.log n)^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply add_le_add _ (by linarith only [hy1])
      apply mul_le_mul (by convert hy16 using 1 <;> ring) hp4 (by positivity) (Real.sqrt_nonneg n)
    _ ≤ _ := by linarith only [hmain,hminor]

end CentralSelberg

noncomputable section

def CofRoot (u r d : ℕ) :=
  {x : ZMod d // x * ((r : ZMod d) * x - (u : ZMod d)) = 0}

def cofRootCount (u r d : ℕ) : ℕ :=
  Nat.card (CofRoot u r d)

def cofRootEquiv (u r a b : ℕ) (hab : a.Coprime b) :
    CofRoot u r (a * b) ≃ CofRoot u r a × CofRoot u r b := by
  let e := ZMod.chineseRemainder hab
  apply (Equiv.subtypeEquiv e.toEquiv ?_).trans Equiv.subtypeProdEquivProd
  intro x
  change x * ((r : ZMod (a * b)) * x - (u : ZMod (a * b))) = 0 ↔
    (e x).1 * ((r : ZMod a) * (e x).1 - (u : ZMod a)) = 0 ∧
      (e x).2 * ((r : ZMod b) * (e x).2 - (u : ZMod b)) = 0
  have h := e.injective.eq_iff
    (a := x * ((r : ZMod (a * b)) * x - (u : ZMod (a * b)))) (b := 0)
  simpa only [map_mul, map_sub, map_natCast, map_zero, Prod.mk_zero_zero,
    Prod.mul_def, Prod.sub_def, Prod.fst_natCast, Prod.snd_natCast,
    Prod.mk.injEq, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] using h.symm

theorem cofRootCount_mul (u r a b : ℕ) (hab : a.Coprime b) :
    cofRootCount u r (a * b) = cofRootCount u r a * cofRootCount u r b := by
  unfold cofRootCount
  rw [Nat.card_congr (cofRootEquiv u r a b hab), Nat.card_prod]

@[simp] theorem cofRootCount_one (u r : ℕ) : cofRootCount u r 1 = 1 := by
  unfold cofRootCount CofRoot
  have e : {x : ZMod 1 // x * ((r : ZMod 1) * x - (u : ZMod 1)) = 0} ≃ ZMod 1 :=
    Equiv.subtypeUnivEquiv (fun x => Subsingleton.elim _ _)
  rw [Nat.card_congr e, Nat.card_zmod]

theorem cofRootCount_prod_primes (u r : ℕ) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    cofRootCount u r (∏ p ∈ s, p) = ∏ p ∈ s, cofRootCount u r p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      have hpp := hs p (Finset.mem_insert_self p s)
      have hsp : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
      have hcop : p.Coprime (∏ q ∈ s, q) := by
        apply Nat.Coprime.prod_right
        intro q hq
        apply (Nat.coprime_primes hpp (hsp q hq)).mpr
        intro heq
        exact hp (heq ▸ hq)
      rw [Finset.prod_insert hp, cofRootCount_mul u r p _ hcop, ih hsp, Finset.prod_insert hp]

theorem cofRootCount_squarefree (u r d : ℕ) (hd : Squarefree d) :
    cofRootCount u r d = ∏ p ∈ d.primeFactors, cofRootCount u r p := by
  calc
    cofRootCount u r d = cofRootCount u r (∏ p ∈ d.primeFactors, p) := by
          rw [Nat.prod_primeFactors_of_squarefree hd]
    _ = ∏ p ∈ d.primeFactors, cofRootCount u r p :=
      cofRootCount_prod_primes u r d.primeFactors
        (fun p hp => (Nat.mem_primeFactors.mp hp).1)

theorem cofRootCount_eq_filter_card (u r d : ℕ) [NeZero d] :
    cofRootCount u r d =
      (Finset.univ.filter
        (fun x : ZMod d => x * ((r : ZMod d) * x - (u : ZMod d)) = 0)).card := by
  classical
  unfold cofRootCount CofRoot
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem cofRootCount_eq_goldbach (u r d : ℕ) [NeZero d] (h : Nat.Coprime r d) :
    cofRootCount u r d = goldbachSieveRootCount u d := by
  classical
  have hbij : Function.Bijective (fun x : ZMod d => (r : ZMod d) * x) := by
    have hu : IsUnit (r : ZMod d) := (ZMod.isUnit_iff_coprime r d).mpr h
    obtain ⟨v, hv⟩ := hu
    constructor
    · intro x y hxy
      have hxy' := congrArg (fun z : ZMod d => ((v⁻¹ : (ZMod d)ˣ) : ZMod d) * z) hxy
      simp only [← hv, ← mul_assoc, Units.inv_mul, one_mul] at hxy'
      exact hxy'
    · intro y
      refine ⟨((v⁻¹ : (ZMod d)ˣ) : ZMod d) * y, ?_⟩
      have hz : (r : ZMod d) * (((v⁻¹ : (ZMod d)ˣ) : ZMod d) * y) = y := by
        rw [← hv, ← mul_assoc, Units.mul_inv, one_mul]
      exact hz
  have key : ∀ x : ZMod d, (x * ((r : ZMod d) * x - (u : ZMod d)) = 0) ↔
      ((r : ZMod d) * x) * ((u : ZMod d) - (r : ZMod d) * x) = 0 := by
    intro x
    have halg : (r : ZMod d) * (x * ((r : ZMod d) * x - (u : ZMod d)))
        = -((r : ZMod d) * x * ((u : ZMod d) - (r : ZMod d) * x)) := by ring
    constructor
    · intro hx
      have h1 : (r : ZMod d) * (x * ((r : ZMod d) * x - (u : ZMod d))) = 0 := by
        rw [hx, mul_zero]
      have h2 : -((r : ZMod d) * x * ((u : ZMod d) - (r : ZMod d) * x)) = 0 := by
        rw [← halg]
        exact h1
      exact neg_eq_zero.mp h2
    · intro hx
      have h1 : (r : ZMod d) * (x * ((r : ZMod d) * x - (u : ZMod d))) = 0 := by
        rw [halg, hx, neg_zero]
      have hz : (r : ZMod d) * (x * ((r : ZMod d) * x - (u : ZMod d)))
          = (r : ZMod d) * 0 := by rw [h1, mul_zero]
      exact hbij.1 hz
  unfold cofRootCount goldbachSieveRootCount
  apply Nat.card_congr
  refine Equiv.ofBijective
    (fun x : CofRoot u r d =>
      (⟨(r : ZMod d) * x.val, (key x.val).mp x.property⟩ : GoldbachSieveRoot u d)) ?_
  constructor
  · intro x y hxy
    have hxy' := congrArg (fun z : GoldbachSieveRoot u d => z.val) hxy
    apply Subtype.ext
    exact hbij.1 hxy'
  · intro y
    obtain ⟨x₀, hx₀⟩ := hbij.2 y.val
    have hx₀' : (r : ZMod d) * x₀ = y.val := hx₀
    have hprop : x₀ * ((r : ZMod d) * x₀ - (u : ZMod d)) = 0 := by
      rw [key x₀, hx₀']
      exact y.property
    refine ⟨⟨x₀, hprop⟩, ?_⟩
    apply Subtype.ext
    exact hx₀'

theorem cofRootCount_prime_of_dvd (u r p : ℕ) (hp : p.Prime) (hdvd : p ∣ r)
    (hu : ¬ p ∣ u) : cofRootCount u r p = 1 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hr0 : (r : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff r p).mpr hdvd
  have hu0 : (u : ZMod p) ≠ 0 := by
    intro hz
    exact hu ((ZMod.natCast_eq_zero_iff u p).mp hz)
  rw [cofRootCount_eq_filter_card]
  have hset : (Finset.univ.filter
      (fun x : ZMod p => x * ((r : ZMod p) * x - (u : ZMod p)) = 0)) = {0} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [hr0, zero_mul, zero_sub, mul_eq_zero, neg_eq_zero]
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact hx
      · exact absurd hx hu0
    · intro hx
      subst hx
      simp
  rw [hset, Finset.card_singleton]

theorem cofRootCount_two_prime (r p : ℕ) (hp : p.Prime) (hro : Odd r) :
    cofRootCount 2 r p = if p ∣ 2 * r then 1 else 2 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  by_cases hdvd : p ∣ r
  · have hp2 : p ≠ 2 := by
      intro heq
      subst heq
      obtain ⟨k, hk⟩ := hro
      obtain ⟨m, hm⟩ := hdvd
      omega
    have hu : ¬ (p ∣ 2) := by
      intro hd
      have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
      have htl := hp.two_le
      exact hp2 (by omega)
    have h1 : cofRootCount 2 r p = 1 := cofRootCount_prime_of_dvd 2 r p hp hdvd hu
    rw [h1, if_pos (hp.dvd_mul.mpr (Or.inr hdvd))]
  · have hcop : Nat.Coprime p r := hp.coprime_iff_not_dvd.mpr hdvd
    have hrp : Nat.Coprime r p := hcop.symm
    have heq : p ∣ 2 * r ↔ p ∣ 2 := by
      constructor
      · intro hx
        rcases hp.dvd_mul.mp hx with h1 | h1
        · exact h1
        · exact absurd h1 hdvd
      · intro hx
        exact hp.dvd_mul.mpr (Or.inl hx)
    rw [cofRootCount_eq_goldbach 2 r p hrp, goldbachSieveRootCount_prime 2 p hp]
    by_cases h2 : p ∣ 2
    · rw [if_pos h2, if_pos (heq.mpr h2)]
    · rw [if_neg h2, if_neg (fun hx => h2 (heq.mp hx))]

theorem cofRootCount_two_eq (r d : ℕ) (hro : Odd r) (hd : Squarefree d) :
    cofRootCount 2 r d = goldbachSieveRootCount (2 * r) d := by
  rw [cofRootCount_squarefree 2 r d hd, goldbachSieveRootCount_squarefree (2*r) d hd]
  apply Finset.prod_congr rfl
  intro p hp
  exact cofRootCount_two_prime r p (Nat.mem_primeFactors.mp hp).1 hro

theorem cof_dvd_iff_zmod (u r d s : ℕ) (h : u ≤ r * s) :
    d ∣ s * (r * s - u) ↔
      (s : ZMod d) * ((r : ZMod d) * (s : ZMod d) - (u : ZMod d)) = 0 := by
  have h1 : ((r * s - u : ℕ) : ZMod d) = (r : ZMod d) * (s : ZMod d) - (u : ZMod d) := by
    rw [Nat.cast_sub h, Nat.cast_mul]
  have h2 : ((s * (r * s - u) : ℕ) : ZMod d) =
      (s : ZMod d) * ((r : ZMod d) * (s : ZMod d) - (u : ZMod d)) := by
    rw [Nat.cast_mul, h1]
  rw [← h2, ZMod.natCast_eq_zero_iff]

theorem cof_count_discrepancy (r Y d : ℕ) [NeZero d] (hY : 1 ≤ Y) (hr : 2 ≤ r) :
    |(((Finset.Ioc Y (2*Y)).filter (fun s => d ∣ s * (r*s - 2))).card : ℝ) -
      (Y:ℝ) * cofRootCount 2 r d / d| ≤ cofRootCount 2 r d := by
  classical
  have hI : Finset.Ioc Y (2*Y) = Finset.Ico (Y+1) ((Y+1) + Y) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have hfilt : (Finset.Ioc Y (2*Y)).filter (fun s => d ∣ s * (r*s - 2)) =
      (Finset.Ico (Y+1) ((Y+1)+Y)).filter
        (fun s : ℕ => (s : ZMod d) * ((r : ZMod d) * (s : ZMod d) - (2 : ZMod d)) = 0) := by
    rw [← hI]
    apply Finset.filter_congr
    intro s hs
    have hs1 : 1 ≤ s := by have := (Finset.mem_Ioc.mp hs).1; omega
    have h2 : (2:ℕ) ≤ r * s := by
      calc (2:ℕ) ≤ r := hr
        _ = r * 1 := (Nat.mul_one r).symm
        _ ≤ r * s := Nat.mul_le_mul (le_refl r) hs1
    exact cof_dvd_iff_zmod 2 r d s h2
  rw [hfilt, cofRootCount_eq_filter_card]
  exact zmod_predicate_Ico_discrepancy d
    (fun x : ZMod d => x * ((r : ZMod d) * x - (2 : ZMod d)) = 0) (Y+1) Y

theorem cof_density_discrepancy (r Y d : ℕ) [NeZero d] (hY : 1 ≤ Y) (hr : 2 ≤ r)
    (hro : Odd r) (hd : Squarefree d) :
    |(((Finset.Ioc Y (2*Y)).filter (fun s => d ∣ s * (r*s - 2))).card : ℝ) -
      goldbachSieveDensity (2*r) d * (Y:ℝ)| ≤ goldbachSieveRootCount (2*r) d := by
  have h := cof_count_discrepancy r Y d hY hr
  rw [cofRootCount_two_eq r d hro hd] at h
  simpa only [goldbachSieveDensity_apply, div_mul_eq_mul_div, mul_div_assoc, mul_comm] using h

def cofactorSieve (Y r P : ℕ) (hP : Squarefree P) : BoundingSieve where
  support := (Finset.Ioc Y (2*Y)).image (fun s => s * (r*s - 2))
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := PrimePairSieve.fiberWeight (Finset.Ioc Y (2*Y)) (fun s => s * (r*s - 2))
  weights_nonneg := fun n => PrimePairSieve.fiberWeight_nonneg _ _ n
  totalMass := (Y : ℝ)
  nu := goldbachSieveDensity (2*r)
  nu_mult := goldbachSieveDensity_isMultiplicative (2*r)
  nu_pos_of_prime := fun p hp _ => goldbachSieveDensity_prime_pos (2*r) p hp
  nu_lt_one_of_prime := fun p hp _ =>
    goldbachSieveDensity_prime_lt_one (2*r) p hp (fun _ => ⟨r, rfl⟩)

theorem cofactorSieve_totalMass (Y r P : ℕ) (hP : Squarefree P) :
    (cofactorSieve Y r P hP).totalMass = (Y : ℝ) := rfl

theorem cofactorSieve_multSum (Y r P : ℕ) (hP : Squarefree P) (d : ℕ) :
    (cofactorSieve Y r P hP).multSum d =
      ((((Finset.Ioc Y (2*Y)).filter (fun s => d ∣ s * (r*s - 2))).card : ℕ) : ℝ) :=
  PrimePairSieve.sum_fiberWeight_indicator _ _ (fun y => d ∣ y)

theorem cofactorSieve_siftedSum (Y r P : ℕ) (hP : Squarefree P) :
    (cofactorSieve Y r P hP).siftedSum =
      ((((Finset.Ioc Y (2*Y)).filter
        (fun s => P.Coprime (s * (r*s - 2)))).card : ℕ) : ℝ) :=
  PrimePairSieve.sum_fiberWeight_indicator _ _ (fun y => P.Coprime y)

theorem cofactorSieve_rem (Y r P : ℕ) (hP : Squarefree P) (d : ℕ) :
    (cofactorSieve Y r P hP).rem d =
      ((((Finset.Ioc Y (2*Y)).filter (fun s => d ∣ s * (r*s - 2))).card : ℕ) : ℝ) -
        goldbachSieveDensity (2*r) d * (Y : ℝ) := by
  rw [BoundingSieve.rem, cofactorSieve_multSum]
  rfl

theorem cof_normalizer (Y r P z : ℕ) (hP : Squarefree P) :
    SelbergOptimal.normalizer (cofactorSieve Y r P hP) z =
      GoldbachSelberg.denominator (2*r) P z := by
  unfold SelbergOptimal.normalizer GoldbachSelberg.denominator
  apply sum_congr rfl
  intro d hd
  rw [BoundingSieve.selbergTerms_apply]
  rfl

theorem cof_denominator_pos (Y r P : ℕ) (hP : Squarefree P) {z : ℕ} (hz : 1 ≤ z) :
    0 < GoldbachSelberg.denominator (2*r) P z := by
  rw [← cof_normalizer Y r P z hP]
  exact SelbergOptimal.normalizer_pos _ hz

theorem cof_rem_bound (Y r P d : ℕ) (hY : 1 ≤ Y) (hr : 2 ≤ r) (hro : Odd r)
    (hP : Squarefree P) (hd : Squarefree d) [NeZero d] :
    |(cofactorSieve Y r P hP).rem d| ≤ goldbachSieveRootCount (2*r) d := by
  rw [cofactorSieve_rem]
  exact cof_density_discrepancy r Y d hY hr hro hd

theorem cof_rem_lcm_bound (Y r P : ℕ) (hY : 1 ≤ Y) (hr : 2 ≤ r) (hro : Odd r)
    (hP : Squarefree P) (a : ℕ) (ha : a ∈ P.divisors) (b : ℕ) (hb : b ∈ P.divisors) :
    |(cofactorSieve Y r P hP).rem (Nat.lcm a b)| ≤
      (2 : ℝ) ^ a.primeFactors.card * (2 : ℝ) ^ b.primeFactors.card := by
  let : NeZero a := ⟨(Nat.pos_of_mem_divisors ha).ne'⟩
  let : NeZero b := ⟨(Nat.pos_of_mem_divisors hb).ne'⟩
  let : NeZero (Nat.lcm a b) := ⟨Nat.lcm_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  have hsq : Squarefree (Nat.lcm a b) :=
    hP.squarefree_of_dvd (Nat.lcm_dvd (Nat.dvd_of_mem_divisors ha) (Nat.dvd_of_mem_divisors hb))
  have ha2 := goldbachSieveRootCount_le_two_pow (2*r) a
    (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors ha))
  have hb2 := goldbachSieveRootCount_le_two_pow (2*r) b
    (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hb))
  calc
    _ ≤ (goldbachSieveRootCount (2*r) (Nat.lcm a b) : ℝ) :=
      cof_rem_bound Y r P _ hY hr hro hP hsq
    _ ≤ (goldbachSieveRootCount (2*r) a : ℝ) * goldbachSieveRootCount (2*r) b := by
      exact_mod_cast goldbachSieveRootCount_lcm_le (2*r) a b
    _ ≤ _ := by exact_mod_cast Nat.mul_le_mul ha2 hb2

theorem cof_card_le_sifted (Y r P : ℕ) (hY : 1 ≤ Y) (hr : 2 ≤ r) (hro : Odd r)
    (hP : Squarefree P) {z : ℕ} (hz : 1 ≤ z) :
    ((((Finset.Ioc Y (2*Y)).filter
        (fun s => P.Coprime (s * (r*s - 2)))).card : ℕ) : ℝ) ≤
      (Y:ℝ) / GoldbachSelberg.denominator (2*r) P z +
        (z:ℝ)^2 * (1 + Real.log z)^4 := by
  have he := SelbergOptimal.siftedSum_le_log_error (cofactorSieve Y r P hP) hz
    (fun a ha b hb => cof_rem_lcm_bound Y r P hY hr hro hP a ha b hb)
  rw [cofactorSieve_siftedSum, cofactorSieve_totalMass, cof_normalizer Y r P z hP] at he
  exact he

theorem singular_two_mul (r : ℕ) (hrp : r.Prime) (hr2 : 2 < r) :
    CentralSelberg.singular (2*r) = 1 + 1/((r:ℝ)-2) := by
  have hset : (2*r).primeFactors.filter (fun p => 2 < p) = {r} := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hpp, hpd, -⟩, hp2⟩
      have hpr : p ∣ r := by
        rcases hpp.dvd_mul.mp hpd with h1 | h1
        · exfalso
          have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h1
          have := hpp.two_le
          omega
        · exact h1
      exact (hrp.dvd_iff_eq hpp.ne_one).mp hpr |>.symm
    · intro hp
      subst hp
      exact ⟨⟨hrp, ⟨2, by ring⟩, Nat.mul_ne_zero (by norm_num) (by omega)⟩, hr2⟩
  unfold CentralSelberg.singular
  rw [hset]
  simp

theorem singular_two_mul_le (r : ℕ) (hrp : r.Prime) (hr2 : 2 < r) :
    CentralSelberg.singular (2*r) ≤ 2 := by
  rw [singular_two_mul r hrp hr2]
  have h3 : (3:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr2
  have h1 : (0:ℝ) < (r:ℝ) - 2 := by linarith
  have hle : (1:ℝ)/((r:ℝ)-2) ≤ 1 := by
    rw [div_le_one h1]
    linarith
  linarith

theorem cofactor_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y r : ℕ), 3 ≤ Y → r.Prime → 2 < r →
      ((((Finset.Ioc Y (2*Y)).filter (fun s => s.Prime ∧ (r*s-2).Prime)).card:ℕ):ℝ) ≤
        C*(Y:ℝ)/(Real.log Y)^2 := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp CentralSelberg.scales2
  refine ⟨8210 + (Real.log ((max X 3 : ℕ) : ℝ))^2, by positivity, ?_⟩
  intro Y r hY hrp hr2
  have hY1 : 1 ≤ Y := by omega
  have hYpos : 0 < Y := by omega
  have hlogYpos : 0 < Real.log Y := Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hr2le : 2 ≤ r := by omega
  have hro : Odd r := hrp.odd_of_ne_two (by omega)
  have hcardIoc : (Finset.Ioc Y (2*Y)).card = Y := by
    rw [Nat.card_Ioc]
    omega
  rw [le_div_iff₀ (pow_pos hlogYpos 2)]
  by_cases hcase : Y < max X 3
  · have hcardT : ((((Finset.Ioc Y (2*Y)).filter
        (fun s => s.Prime ∧ (r*s-2).Prime)).card : ℕ) : ℝ) ≤ (Y : ℝ) := by
      have h1 : ((Finset.Ioc Y (2*Y)).filter
          (fun s => s.Prime ∧ (r*s-2).Prime)).card ≤ (Finset.Ioc Y (2*Y)).card := by
        apply Finset.card_le_card
        intro s hs
        exact (Finset.mem_filter.mp hs).1
      rw [hcardIoc] at h1
      exact_mod_cast h1
    have hmono : Real.log Y ≤ Real.log ((max X 3 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast hYpos) (by exact_mod_cast (le_of_lt hcase))
    have hsq : (Real.log Y)^2 ≤ (Real.log ((max X 3 : ℕ) : ℝ))^2 :=
      pow_le_pow_left₀ hlogYpos.le hmono 2
    calc _ ≤ (Y:ℝ) * (Real.log Y)^2 :=
          mul_le_mul_of_nonneg_right hcardT (sq_nonneg (Real.log Y))
      _ ≤ (Y:ℝ) * (Real.log ((max X 3 : ℕ) : ℝ))^2 :=
          mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg Y)
      _ ≤ (8210 + (Real.log ((max X 3 : ℕ) : ℝ))^2) * (Y:ℝ) := by
          calc (Y:ℝ) * (Real.log ((max X 3 : ℕ) : ℝ))^2
              ≤ (Y:ℝ) * (Real.log ((max X 3 : ℕ) : ℝ))^2 + 8210 * (Y:ℝ) :=
                le_add_of_nonneg_right (by positivity)
            _ = (8210 + (Real.log ((max X 3 : ℕ) : ℝ))^2) * (Y:ℝ) := by ring
  · have hcase' : max X 3 ≤ Y := by omega
    obtain ⟨y, hy2, hyn, hlog, herr⟩ := hX Y ((le_max_left X 3).trans hcase')
    have hzpos : 1 ≤ y^8 := Nat.one_le_pow _ _ (by omega)
    have hsing := singular_two_mul_le r hrp hr2
    have hone := CentralSelberg.singular_one_le (2*r)
    have hEu := CentralSelberg.euler_mass (2*r) y ⟨r, rfl⟩ (by omega)
    have hcut := CentralSelberg.retained (2*r) y ⟨r, rfl⟩ hy2
    change _ ≤ 2*CentralSelberg.singular (2*r)*CentralSelberg.mass (2*r) y at hEu
    change CentralSelberg.mass (2*r) y ≤ 2*_ at hcut
    have hmass0 : (0:ℝ) ≤ CentralSelberg.mass (2*r) y := by
      apply Finset.prod_nonneg
      intro p hp
      have := CentralSelberg.wgt_pos (2*r) ⟨r, rfl⟩ p (Nat.prime_of_mem_primesLE hp)
      linarith
    have h1 : (Real.log ((y:ℝ)+1))^2 ≤
        4 * CentralSelberg.singular (2*r) * GoldbachSelberg.denominator (2*r) (primorial y) (y^8) := by
      calc _ ≤ 2*CentralSelberg.singular (2*r)*CentralSelberg.mass (2*r) y := hEu
        _ ≤ 2*CentralSelberg.singular (2*r)*(2*GoldbachSelberg.denominator (2*r) (primorial y) (y^8)) := by
            apply mul_le_mul_of_nonneg_left hcut
            nlinarith [hone]
        _ = _ := by ring
    have hDpos : 0 < GoldbachSelberg.denominator (2*r) (primorial y) (y^8) :=
      cof_denominator_pos Y r _ (squarefree_primorial y) hzpos
    have h2 : (Real.log ((y:ℝ)+1))^2 ≤
        8 * GoldbachSelberg.denominator (2*r) (primorial y) (y^8) := by
      calc _ ≤ 4*CentralSelberg.singular (2*r)*GoldbachSelberg.denominator (2*r) (primorial y) (y^8) := h1
        _ ≤ 4*2*GoldbachSelberg.denominator (2*r) (primorial y) (y^8) := by
            apply mul_le_mul_of_nonneg_right _ hDpos.le
            nlinarith [hsing]
        _ = _ := by ring
    have hsq : (Real.log Y)^2 ≤ (32*Real.log ((y:ℝ)+1))^2 :=
      pow_le_pow_left₀ hlogYpos.le hlog 2
    have hDen : (Real.log Y)^2 ≤
        8192 * GoldbachSelberg.denominator (2*r) (primorial y) (y^8) := by
      calc _ ≤ (32*Real.log ((y:ℝ)+1))^2 := hsq
        _ = 1024 * (Real.log ((y:ℝ)+1))^2 := by ring
        _ ≤ 1024 * (8*GoldbachSelberg.denominator (2*r) (primorial y) (y^8)) := by
            exact mul_le_mul_of_nonneg_left h2 (by norm_num)
        _ = _ := by ring
    have hD0 : GoldbachSelberg.denominator (2*r) (primorial y) (y^8) ≠ 0 := hDpos.ne'
    have hfirst : ((Y:ℝ)/GoldbachSelberg.denominator (2*r) (primorial y) (y^8))*(Real.log Y)^2
        ≤ 8192*(Y:ℝ) := by
      calc _ ≤ ((Y:ℝ)/GoldbachSelberg.denominator (2*r) (primorial y) (y^8)) *
            (8192*GoldbachSelberg.denominator (2*r) (primorial y) (y^8)) := by
            exact mul_le_mul_of_nonneg_left hDen (by positivity)
        _ = _ := by field_simp
    have herr' : (((y^8:ℕ):ℝ)^2*(1+Real.log (y^8:ℕ))^4 + 2*(y:ℝ)) * (Real.log Y)^2 ≤
        18*(Y:ℝ) := by
      have hthis := herr
      push_cast at hthis ⊢
      exact hthis
    have herr2 : ((y^8:ℕ):ℝ)^2*(1+Real.log (y^8:ℕ))^4*(Real.log Y)^2 ≤ 18*(Y:ℝ) := by
      have h0 : (0:ℝ) ≤ 2*(y:ℝ)*(Real.log Y)^2 := by positivity
      nlinarith [herr']
    have hsub : (Finset.Ioc Y (2*Y)).filter (fun s => s.Prime ∧ (r*s-2).Prime) ⊆
        (Finset.Ioc Y (2*Y)).filter
          (fun s => (primorial y).Coprime (s * (r*s - 2))) := by
      intro s hs
      obtain ⟨hsI, hsP, hsQ⟩ := Finset.mem_filter.mp hs
      have hsY : Y < s := (Finset.mem_Ioc.mp hsI).1
      have hsy : ¬ (s ∣ primorial y) := by
        intro hd
        have hmem : s ∈ (primorial y).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hsP, hd, primorial_ne_zero y⟩
        rw [primeFactors_primorial] at hmem
        have := (Nat.mem_primesLE.mp hmem).1
        omega
      have hq : y < r*s - 2 := by
        have h3 : 3 ≤ r := by omega
        have hs1 : Y + 1 ≤ s := by omega
        have hmul : 3*(Y+1) ≤ r*s := Nat.mul_le_mul h3 hs1
        omega
      have hqy : ¬ ((r*s - 2) ∣ primorial y) := by
        intro hd
        have hmem : r*s - 2 ∈ (primorial y).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hsQ, hd, primorial_ne_zero y⟩
        rw [primeFactors_primorial] at hmem
        have := (Nat.mem_primesLE.mp hmem).1
        omega
      refine Finset.mem_filter.mpr ⟨hsI, ?_⟩
      exact ((hsP.coprime_iff_not_dvd.mpr hsy).symm).mul_right
        ((hsQ.coprime_iff_not_dvd.mpr hqy).symm)
    have hcardle : ((((Finset.Ioc Y (2*Y)).filter
        (fun s => s.Prime ∧ (r*s-2).Prime)).card : ℕ) : ℝ) ≤
        (Y:ℝ)/GoldbachSelberg.denominator (2*r) (primorial y) (y^8) +
          ((y^8:ℕ):ℝ)^2*(1+Real.log (y^8:ℕ))^4 := by
      calc _ ≤ ((((Finset.Ioc Y (2*Y)).filter
              (fun s => (primorial y).Coprime (s * (r*s - 2)))).card : ℕ) : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ _ := cof_card_le_sifted Y r (primorial y) hY1 hr2le hro
              (squarefree_primorial y) hzpos
    have hmul := mul_le_mul_of_nonneg_right hcardle (sq_nonneg (Real.log Y))
    calc _ ≤ ((Y:ℝ)/GoldbachSelberg.denominator (2*r) (primorial y) (y^8) +
          ((y^8:ℕ):ℝ)^2*(1+Real.log (y^8:ℕ))^4) * (Real.log Y)^2 := hmul
      _ = ((Y:ℝ)/GoldbachSelberg.denominator (2*r) (primorial y) (y^8)) *
            (Real.log Y)^2 +
          ((y^8:ℕ):ℝ)^2*(1+Real.log (y^8:ℕ))^4 * (Real.log Y)^2 := by ring
      _ ≤ 8192*(Y:ℝ) + 18*(Y:ℝ) := add_le_add hfirst herr2
      _ ≤ (8210 + (Real.log ((max X 3 : ℕ) : ℝ))^2) * (Y:ℝ) := by
          calc 8192*(Y:ℝ) + 18*(Y:ℝ) = 8210*(Y:ℝ) := by ring
            _ ≤ 8210*(Y:ℝ) + (Real.log ((max X 3 : ℕ) : ℝ))^2 * (Y:ℝ) :=
                le_add_of_nonneg_right
                  (mul_nonneg (sq_nonneg (Real.log ((max X 3 : ℕ) : ℝ))) (Nat.cast_nonneg Y))
            _ = (8210 + (Real.log ((max X 3 : ℕ) : ℝ))^2) * (Y:ℝ) := by ring

end

end Conjectures.TwinPrimes.CofactorTwoLinearSieve_aux

theorem Conjectures.TwinPrimes.CofactorTwoLinearSieve : ∃ C : ℝ, 0 < C ∧ ∀ (Y r : ℕ), 3 ≤ Y → r.Prime → 2 < r → ((((Finset.Ioc Y (2*Y)).filter (fun s => s.Prime ∧ (r*s-2).Prime)).card:ℕ):ℝ) ≤ C*(Y:ℝ)/(Real.log Y)^2 := Conjectures.TwinPrimes.CofactorTwoLinearSieve_aux.cofactor_upper

/-!
# Major-arc estimates for the prime logarithmic sum

The general finite estimates below are from DFQDZZ, goldbach-proofs PR #316,
revision e4ab24712555ae8c2c926adf19d368a9fb392c35 (Apache-2.0).

The analytic material in the namespaces OAI.LargePrimeGaps is selected and adapted
from OpenAI's openai/math, lean/OAI/NumberTheory/PrimeGaps, at revision
f5702854040e97fa7675c21ba37a9608f5f92dd3, licensed under Apache 2.0 (see LICENSE).
It is specialized to the declarations required for the small-modulus estimate and
ported from toolchain 4.34.1 to the version locked by this repository.
-/

section

-- Source module: CharacterErrors
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
noncomputable def primeCharacterPrefix (x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n∈Finset.Ioc 0 ⌊x⌋₊, χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)

noncomputable def primeCharacterError (x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  primeCharacterPrefix x χ-if χ=1 then (x:ℂ) else 0

end LargePrimeGaps
end OAI

-- Source module: ConductorBounds
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
open Filter Topology
def SiegelWalfisz : Prop :=
  ∀ A B : ℝ, 0 < A → 0 < B → ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
    ∀ x : ℝ, x₀ ≤ x → ∀ d : ℕ, 0 < d → (d:ℝ) ≤ (Real.log x)^B →
      ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
        ‖primeCharacterError x χ‖ ≤ M*x*(Real.log x)^(-A)

theorem eventually_log_rpow_le_rpow (a : ℝ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ x : ℝ in atTop, (Real.log x)^a ≤ x^s := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop a hs).bound (by norm_num : (0:ℝ)<1),
    eventually_ge_atTop (1:ℝ)] with x h hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx) _),
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0≤x) _),one_mul] using h

end LargePrimeGaps
end OAI

-- Source module: LogParameters
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
open Filter Topology
open Complex Filter Topology
noncomputable def poleRemovedL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ q else χ.LFunction

noncomputable def primeLogDerivativeRegular {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  -deriv (poleRemovedL χ) s / poleRemovedL χ s

theorem poleRemovedL_differentiable {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) : Differentiable ℂ (poleRemovedL χ) := by
  unfold poleRemovedL
  split_ifs with hχ
  · exact DirichletCharacter.differentiable_LFunctionTrivChar₁ q
  · exact DirichletCharacter.differentiable_LFunction hχ

theorem poleRemovedL_ne_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 ≤ s.re) :
    poleRemovedL χ s ≠ 0 := by
  unfold poleRemovedL
  split_ifs with hχ
  · rcases eq_or_ne s 1 with rfl | hs1
    · exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q
    · rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1]
      refine mul_ne_zero (sub_ne_zero.mpr hs1) ?_
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re 1 (.inr hs1) hs
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) hs

theorem primeLogDerivativeRegular_analyticAt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : poleRemovedL χ s ≠ 0) :
    AnalyticAt ℂ (primeLogDerivativeRegular χ) s := by
  have h := (poleRemovedL_differentiable χ).analyticAt s
  exact h.deriv.neg.div h hs

theorem primeLogDerivativeRegular_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    primeLogDerivativeRegular χ s =
      LSeries (fun n : ℕ => χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) s -
        (if χ = 1 then 1 / (s - 1) else 0) := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hL := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  change LSeries (fun n : ℕ => χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) s =
    -deriv (LSeries (fun n : ℕ => χ (n : ZMod q))) s /
      LSeries (fun n : ℕ => χ (n : ZMod q)) s at hL
  rw [hL, ← DirichletCharacter.LFunction_eq_LSeries χ hs,
    ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs]
  by_cases hχ : χ = 1
  · subst χ
    have hn := DirichletCharacter.LFunction_ne_zero_of_one_le_re
      (1 : DirichletCharacter ℂ q) (.inr hs1) hs.le
    simp only [primeLogDerivativeRegular, poleRemovedL, ↓reduceIte]
    rw [DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one q hs1,
      DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1]
    change -((s-1)*deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s +
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s) /
      ((s-1)*DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s) = _
    field_simp
    ring
  · simp [primeLogDerivativeRegular, poleRemovedL, hχ]

end LargePrimeGaps
end OAI

-- Source module: DirichletGrowth
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
open Filter Topology
open Complex Filter Topology
open Complex Filter Topology Set MeasureTheory Asymptotics
noncomputable def discrepancyTail (A : ℝ → ℂ) (u : ℝ) (s : ℂ) : ℂ :=
  ∫ t in Ioi u, A t * (t:ℂ)^(-(s+1))

lemma discrepancyTail_integrable {A : ℝ → ℂ} {u D : ℝ} (hu : 0 < u) (hD : 0 ≤ D)
    (hA : Measurable A) (hbound : ∀ t, u < t → ‖A t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t => A t * (t:ℂ)^(-(s+1))) (Ioi u) := by
  have hp : (-(s+1)).re < -1 := by simp only [neg_re,add_re,one_re]; linarith
  have hi := (integrableOn_Ioi_norm_cpow_of_lt hp hu).const_mul D
  have hm := (integrableOn_Ioi_cpow_of_lt hp hu).aestronglyMeasurable
  refine hi.mono (hA.aestronglyMeasurable.restrict.mul hm) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hD (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right (hbound t ht) (norm_nonneg _)

lemma discrepancyTail_norm_le {A : ℝ → ℂ} {u D : ℝ} (hu : 0 < u) (_hD : 0 ≤ D)
    (_hA : Measurable A) (hbound : ∀ t, u < t → ‖A t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    ‖discrepancyTail A u s‖ ≤ D * u^(-s.re)/s.re := by
  have hi := (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re-1 < -1) hu).const_mul D
  calc
    _ ≤ ∫ t in Ioi u, D*t^(-s.re-1) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (hu.trans ht)]
      simp only [neg_re,add_re,one_re,neg_add_rev]
      have he : -1 + -s.re = -s.re-1 := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_right (hbound t ht) (Real.rpow_nonneg (hu.trans ht).le _)
    _ = _ := by
      rw [integral_const_mul,integral_Ioi_rpow_of_lt (by linarith : -s.re-1 < -1) hu]
      ring_nf

lemma discrepancyTail_eq_mellin {A : ℝ → ℂ} {u : ℝ} (hu : 0 ≤ u) (s : ℂ) :
    discrepancyTail A u s = mellin ((Ioi u).indicator A) (-s) := by
  rw [mellin]
  simp_rw [←Set.indicator_smul]
  rw [integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
  have he : Ioi u ∩ Ioi 0 = Ioi u := Set.inter_eq_left.mpr (fun t ht => hu.trans_lt ht)
  rw [he]
  unfold discrepancyTail
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  ring

lemma discrepancyTail_differentiableAt {A : ℝ → ℂ} {u D : ℝ} (hu : 0 < u) (hD : 0 ≤ D)
    (hA : Measurable A) (hbound : ∀ t, u < t → ‖A t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (discrepancyTail A u) s := by
  let B := (Ioi u).indicator A
  have hm : Measurable B := hA.indicator measurableSet_Ioi
  have hb : ∀ t, ‖B t‖ ≤ D := by
    intro t
    by_cases ht : u < t
    · simpa [B,ht] using hbound t ht
    · simpa [B,ht] using hD
  have hloc : LocallyIntegrableOn B (Ioi 0) :=
    ((locallyIntegrable_const D).mono hm.aestronglyMeasurable
      (.of_forall (fun t => (hb t).trans (le_abs_self D)))).locallyIntegrableOn _
  have htop : B =O[atTop] (fun t : ℝ => t^(-(0:ℝ))) := by
    refine isBigO_iff.mpr ⟨D,Eventually.of_forall ?_⟩
    intro t
    simpa using hb t
  have hbot : B =O[𝓝[>] 0] (fun t : ℝ => t^(-(-s.re-1))) := by
    refine isBigO_iff.mpr ⟨0,?_⟩
    filter_upwards [nhdsWithin_le_nhds (gt_mem_nhds hu)] with t ht
    simp [B,not_lt.mpr ht.le]
  have hd := mellin_differentiableAt_of_isBigO_rpow hloc htop
    (by simpa using hs : (-s).re < 0) hbot (by simp : -s.re-1 < (-s).re)
  have he : discrepancyTail A u = fun z => mellin B (-z) := funext (discrepancyTail_eq_mellin hu.le)
  rw [he]
  exact hd.comp s differentiableAt_id.neg

open Finset
lemma periodic_sum_norm_le {f : ℕ → ℂ} {q : ℕ} (hq : 0 < q)
    (hp : ∀ n, f (q+n) = f n) (hz : ∑ n ∈ range q, f n = 0)
    (hb : ∀ n, ‖f n‖ ≤ 1) (N : ℕ) : ‖∑ n ∈ range N, f n‖ ≤ q := by
  induction N using Nat.strong_induction_on with
  | ind N ih =>
    by_cases hN : N < q
    · calc
        _ ≤ ∑ n ∈ range N, ‖f n‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ range N, (1:ℝ) := sum_le_sum (fun n _ => hb n)
        _ = N := by simp
        _ ≤ q := by exact_mod_cast hN.le
    · have he : q+(N-q) = N := Nat.add_sub_of_le (not_lt.mp hN)
      rw [←he, sum_range_add, hz, zero_add]
      simp_rw [hp]
      exact ih _ (Nat.sub_lt (lt_of_lt_of_le hq (not_lt.mp hN)) hq)

lemma char_sum_range_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : ∑ n ∈ range q, χ (n : ZMod q) = 0 := by
  rw [←Fin.sum_univ_eq_sum_range]
  have he := (ZMod.finEquiv q).toEquiv.sum_comp χ
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
    have hz := he.trans (MulChar.sum_eq_zero_of_ne_one hχ)
    change (∑ i : Fin (q+1), χ i) = 0 at hz
    calc
      _ = ∑ i : Fin (q+1), χ (i : Fin (q+1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        exact Fin.cast_val_eq_self i
      _ = 0 := hz

lemma char_sum_Icc_norm_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (N : ℕ) : ‖∑ n ∈ Icc 1 N, χ (n : ZMod q)‖ ≤ q+1 := by
  have hr := periodic_sum_norm_le (NeZero.pos q)
    (f := fun n => χ (n : ZMod q)) (by intro n; simp)
    (char_sum_range_zero hχ) (fun n => χ.norm_le_one _) (N+1)
  have he : ∑ n ∈ range (N+1), χ (n : ZMod q) =
      χ (0 : ZMod q) + ∑ n ∈ Icc 1 N, χ (n : ZMod q) := by
    rw [Nat.range_succ_eq_Icc_zero, ←Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le N)]
    simp
  rw [he] at hr
  calc
    _ = ‖(χ (0 : ZMod q) + ∑ n ∈ Icc 1 N, χ (n : ZMod q)) - χ 0‖ := by congr 1; ring
    _ ≤ ‖χ (0 : ZMod q) + ∑ n ∈ Icc 1 N, χ (n : ZMod q)‖ + ‖χ 0‖ := norm_sub_le _ _
    _ ≤ q+1 := add_le_add hr (χ.norm_le_one _)

noncomputable def seriesDiscrepancy (f : ℕ → ℂ) (c : ℂ) (t : ℝ) : ℂ :=
  (∑ n ∈ Icc 1 ⌊t⌋₊, f n) - c*t

lemma measurable_seriesDiscrepancy (f : ℕ → ℂ) (c : ℂ) :
    Measurable (seriesDiscrepancy f c) := by
  exact ((measurable_of_countable (fun N : ℕ => ∑ n ∈ Icc 1 N, f n)).comp
    Nat.measurable_floor).sub (measurable_const.mul Complex.continuous_ofReal.measurable)

noncomputable def regularSeries (f : ℕ → ℂ) (c : ℂ) (s : ℂ) : ℂ :=
  c+s*discrepancyTail (seriesDiscrepancy f c) 1 s

lemma regularSeries_differentiableAt {f : ℕ → ℂ} {c : ℂ} {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (regularSeries f c) s := by
  exact (differentiableAt_const c).add (differentiableAt_id.mul
    (discrepancyTail_differentiableAt zero_lt_one hD (measurable_seriesDiscrepancy f c) hb hs))

lemma regularSeries_eq_LSeries_sub {f : ℕ → ℂ} {c : ℂ} {D : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ 1) (hD : 0 ≤ D)
    (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D) {s : ℂ} (hs : 1 < s.re) :
    regularSeries f c s = LSeries f s - c/(s-1) := by
  have hO : (fun n => ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] (fun n => (n:ℝ)^(1:ℝ)) := by
    refine isBigO_iff.mpr ⟨1, .of_forall (fun n => ?_)⟩
    simp only [Real.rpow_one, one_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg (sum_nonneg (fun _ _ => norm_nonneg _))]
    calc
      _ ≤ ∑ _k ∈ Icc 1 n, (1:ℝ) := sum_le_sum (fun n _ => hf n)
      _ ≤ |(n:ℝ)| := by simp
  rw [LSeries_eq_mul_integral' f zero_le_one hs hO]
  have hiA := discrepancyTail_integrable zero_lt_one hD (measurable_seriesDiscrepancy f c) hb
    (zero_lt_one.trans hs)
  have hi := integrableOn_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs : (-s).re < -1) zero_lt_one
  have he (t : ℝ) (ht : 1 < t) :
      (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t:ℂ)^(-(s+1)) =
      seriesDiscrepancy f c t * (t:ℂ)^(-(s+1)) + c*(t:ℂ)^(-s) := by
    have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans ht).ne'
    have ht1 : (t:ℂ)*(t:ℂ)^(-(s+1)) = (t:ℂ)^(-s) := by
      nth_rw 1 [←Complex.cpow_one (t:ℂ)]
      rw [←Complex.cpow_add _ _ ht0]
      congr 1
      ring
    dsimp [seriesDiscrepancy]
    rw [sub_mul, mul_assoc c, ht1]
    ring
  have hs0 : s-1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hv : ∫ t in Ioi (1:ℝ), (t:ℂ)^(-s) = 1/(s-1) := by
    rw [integral_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs : (-s).re < -1) zero_lt_one]
    simp only [ofReal_one, one_cpow]
    have he : -s+1 = -(s-1) := by ring
    rw [he, neg_div_neg_eq]
  have hint : (∫ t in Ioi (1:ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t:ℂ)^(-(s+1))) =
      ∫ t in Ioi (1:ℝ), seriesDiscrepancy f c t * (t:ℂ)^(-(s+1)) + c*(t:ℂ)^(-s) :=
    setIntegral_congr_fun measurableSet_Ioi (fun {t} ht => he t ht)
  rw [hint,
    integral_add hiA (hi.const_mul c), integral_const_mul, hv]
  dsimp [regularSeries,discrepancyTail]
  field_simp [hs0]
  ring

lemma sum_Icc_zero_eq {f : ℕ → ℂ} (hf : f 0 = 0) (N : ℕ) :
    ∑ k ∈ Icc 0 N, f k = ∑ k ∈ Icc 1 N, f k := by
  rw [←Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le N)]
  simp [hf]

lemma weighted_sum_abel {f : ℕ → ℂ} (hf : f 0 = 0) {N : ℕ} (hN : 1 ≤ N)
    {s : ℂ} (hs : 0 < s.re) :
    ∑ n ∈ Icc 1 N, f n * (n:ℂ)^(-s) =
      (∑ n ∈ Icc 1 N, f n)*(N:ℂ)^(-s) +
        s*∫ t in (1:ℝ)..N, (∑ n ∈ Icc 1 ⌊t⌋₊, f n)*(t:ℂ)^(-(s+1)) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs
  have hd (t:ℝ) (ht : t ∈ Set.Icc 1 (N:ℝ)) :
      HasDerivAt (fun t : ℝ => (t:ℂ)^(-s)) ((-s)*(t:ℂ)^(-(s+1))) t := by
    rw [show -(s+1) = -s-1 by ring]
    exact hasDerivAt_ofReal_cpow_const ((zero_lt_one.trans_le ht.1).ne') (neg_ne_zero.mpr hs0)
  have hcont : ContinuousOn (fun t : ℝ => (-s)*(t:ℂ)^(-(s+1))) (Set.Icc 1 (N:ℝ)) := by
    intro t ht
    exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const _ _
      (.inr (zero_lt_one.trans_le ht.1).ne'))).continuousWithinAt
  have hi : IntegrableOn (deriv (fun t:ℝ => (t:ℂ)^(-s))) (Set.Icc 1 (N:ℝ)) :=
    hcont.integrableOn_Icc.congr_fun (fun t ht => (hd t ht).deriv.symm) measurableSet_Icc
  have ha := sum_mul_eq_sub_sub_integral_mul' f hN (fun t ht => (hd t (by simpa using ht)).differentiableAt) (by simpa using hi)
  have he : (insert 1 (Finset.Ioc 1 N) : Finset ℕ) = Finset.Icc 1 N := by
    ext k
    simp only [Finset.mem_insert,Finset.mem_Ioc,Finset.mem_Icc]
    omega
  have hint : (∫ t in Set.Ioc (1:ℝ) (N:ℝ),
      deriv (fun t:ℝ => (t:ℂ)^(-s)) t * ∑ k ∈ Icc 0 ⌊t⌋₊, f k) =
      (-s)*∫ t in (1:ℝ)..N, (∑ k ∈ Icc 1 ⌊t⌋₊, f k)*(t:ℂ)^(-(s+1)) := by
    rw [intervalIntegral.integral_of_le hNR, ←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [(hd t ⟨ht.1.le,ht.2⟩).deriv,sum_Icc_zero_eq hf]
    ring
  simp only [Nat.cast_one, Complex.ofReal_natCast, Complex.ofReal_one] at ha
  rw [hint] at ha
  simp only [one_cpow,one_mul,sum_Icc_zero_eq hf,Finset.Icc_self,sum_singleton] at ha
  conv_lhs => rw [←he,sum_insert (by simp)]
  simp only [Nat.cast_one,one_cpow,mul_one]
  simp_rw [mul_comm (f _) ((_:ℂ)^(-s))]
  rw [ha]
  ring

lemma cpow_sub_eq_mul_intervalIntegral {N : ℝ} (hN : 1 ≤ N) (s : ℂ) :
    (N:ℂ)^(1-s)-1 = (1-s)*∫ t in (1:ℝ)..N, (t:ℂ)^(-s) := by
  by_cases hs : s = 1
  · subst s
    simp
  · have hn : (0:ℝ) ∉ Set.uIcc 1 N := by rw [Set.uIcc_of_le hN]; simp
    rw [integral_cpow (.inr ⟨by simpa using hs,hn⟩)]
    simp only [Complex.ofReal_one,one_cpow]
    have he : -s+1 = 1-s := by ring
    rw [he]
    field_simp

lemma regularSeries_cutoff {f : ℕ → ℂ} {c : ℂ} {D : ℝ} (hf : f 0 = 0)
    (hD : 0 ≤ D) (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D)
    {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    regularSeries f c s = (∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) -
      seriesDiscrepancy f c N * (N:ℂ)^(-s) +
      s*discrepancyTail (seriesDiscrepancy f c) N s -
      c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (N:ℂ) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN).ne'
  have hi := discrepancyTail_integrable zero_lt_one hD (measurable_seriesDiscrepancy f c) hb hs
  have htail := intervalIntegral.integral_Ioi_sub_Ioi hi hNR
  have hp : ∀ t ∈ Set.Icc (1:ℝ) (N:ℝ),
      (t:ℂ)*(t:ℂ)^(-(s+1)) = (t:ℂ)^(-s) := by
    intro t ht
    have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le ht.1).ne'
    nth_rw 1 [←Complex.cpow_one (t:ℂ)]
    rw [←Complex.cpow_add _ _ ht0]
    congr 1
    ring
  have hip : IntervalIntegrable (fun t:ℝ => (t:ℂ)^(-s)) volume 1 N :=
    intervalIntegral.intervalIntegrable_cpow (.inr (by rw [Set.uIcc_of_le hNR]; simp))
  have hiA : IntervalIntegrable (fun t:ℝ => seriesDiscrepancy f c t*(t:ℂ)^(-(s+1))) volume 1 N :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hNR).mpr (hi.mono_set Set.Ioc_subset_Ioi_self)
  have hint : (∫ t in (1:ℝ)..N, (∑ n ∈ Icc 1 ⌊t⌋₊, f n)*(t:ℂ)^(-(s+1))) =
      (∫ t in (1:ℝ)..N, seriesDiscrepancy f c t*(t:ℂ)^(-(s+1))) +
        c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s) := by
    rw [←intervalIntegral.integral_const_mul, ←intervalIntegral.integral_add hiA (hip.const_mul c)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hNR] at ht
    dsimp [seriesDiscrepancy]
    rw [sub_mul,mul_assoc c,hp t ht]
    ring
  have hab := weighted_sum_abel hf hN hs
  rw [hint, ←htail] at hab
  have hpow : (N:ℂ)*(N:ℂ)^(-s) = (N:ℂ)^(1-s) := by
    nth_rw 1 [←Complex.cpow_one (N:ℂ)]
    rw [←Complex.cpow_add _ _ hn0]
    congr 1
  have hc := cpow_sub_eq_mul_intervalIntegral hNR s
  simp only [Complex.ofReal_natCast] at hc
  dsimp [regularSeries,discrepancyTail]
  rw [hab]
  simp only [seriesDiscrepancy,Nat.floor_natCast,Complex.ofReal_natCast]
  rw [sub_mul,mul_assoc c,hpow,sub_eq_iff_eq_add.mp hc]
  ring

lemma sum_cpow_norm_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {ε : ℝ} (hε : 0 < ε)
    {s : ℂ} (hs : 1-ε ≤ s.re) {N : ℕ} (_hN : 1 ≤ N) :
    ‖∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)‖ ≤
      (∑' n : ℕ, (n:ℝ)^(-1-ε)) * (N:ℝ)^(2*ε) := by
  have hsumm : Summable (fun n : ℕ => (n:ℝ)^(-1-ε)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ‖f n*(n:ℂ)^(-s)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 N, (n:ℝ)^(-1-ε)*(N:ℝ)^(2*ε) := by
      apply sum_le_sum
      intro n hn
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
      have hnN : (n:ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
      have hn0 := zero_lt_one.trans_le hn1
      rw [norm_mul]
      have hn0C : (n:ℂ) = ((n:ℝ):ℂ) := by simp
      rw [hn0C,Complex.norm_cpow_eq_rpow_re_of_pos hn0,Complex.neg_re]
      calc
        _ ≤ (n:ℝ)^(-s.re) := by
          simpa using mul_le_mul_of_nonneg_right (hf n) (Real.rpow_nonneg hn0.le (-s.re))
        _ ≤ (n:ℝ)^(-1+ε) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        _ = (n:ℝ)^(-1-ε)*(n:ℝ)^(2*ε) := by rw [←Real.rpow_add hn0]; congr 1; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn0.le hnN (by positivity))
          (Real.rpow_nonneg hn0.le _)
    _ = (∑ n ∈ Icc 1 N, (n:ℝ)^(-1-ε))*(N:ℝ)^(2*ε) := by rw [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hsumm.sum_le_tsum _ (fun n _ => Real.rpow_nonneg n.cast_nonneg _))
      (Real.rpow_nonneg N.cast_nonneg _)

lemma norm_intervalIntegral_cpow_le {ε N : ℝ} (hε : 0 < ε) (hN : 1 ≤ N)
    {s : ℂ} (hs : 1-ε ≤ s.re) :
    ‖∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ ≤ N^ε/ε := by
  have hn : (0:ℝ) ∉ Set.uIcc 1 N := by rw [Set.uIcc_of_le hN]; simp
  calc
    _ ≤ ∫ t in (1:ℝ)..N, t^(-1+ε) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hN
        (.of_forall (fun t ht => ?_)) (intervalIntegral.intervalIntegrable_rpow (.inr hn))
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht.1),Complex.neg_re]
      exact Real.rpow_le_rpow_of_exponent_le ht.1.le (by linarith)
    _ = (N^ε-1)/ε := by
      rw [integral_rpow (.inl (by linarith : -1 < -1+ε))]
      have he : -1+ε+1 = ε := by ring
      simp [he]
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hε.le

lemma regularSeries_norm_cutoff {f : ℕ → ℂ} {c : ℂ} {D ε : ℝ}
    (hf0 : f 0 = 0) (hf : ∀ n, ‖f n‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hD : 0 ≤ D)
    (hb : ∀ t, 1 ≤ t → ‖seriesDiscrepancy f c t‖ ≤ D)
    (hε : 0 < ε) (hε1 : ε ≤ 1/2) {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hs : 1-ε ≤ s.re) (hNs : D*(1+‖s‖) ≤ N) :
    ‖regularSeries f c s‖ ≤ ((∑' n : ℕ, (n:ℝ)^(-1-ε))+2+1/ε)*(N:ℝ)^(2*ε) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNP := zero_lt_one.trans_le hNR
  have hs0 : 0 < s.re := by linarith
  have hhalf : 1/2 ≤ s.re := by linarith
  have htail := discrepancyTail_norm_le hNP hD (measurable_seriesDiscrepancy f c)
    (fun t ht => hb t (hNR.trans ht.le)) hs0
  have hboundary : ‖seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ ≤ D*(N:ℝ)^(-s.re) := by
    rw [norm_mul, ←Complex.ofReal_natCast N, Complex.norm_cpow_eq_rpow_re_of_pos hNP,Complex.neg_re]
    exact mul_le_mul_of_nonneg_right (hb _ hNR) (Real.rpow_nonneg hNP.le _)
  have hsmall : ‖seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ +
      ‖s*discrepancyTail (seriesDiscrepancy f c) N s‖ ≤ 2*(N:ℝ)^ε := by
    have ht : D*(N:ℝ)^(-s.re)/s.re ≤ 2*D*(N:ℝ)^(-s.re) := by
      apply (div_le_iff₀ hs0).mpr
      have hn := Real.rpow_nonneg hNP.le (-s.re)
      nlinarith [mul_nonneg hD hn,mul_nonneg (mul_nonneg hD hn) (sub_nonneg.mpr hhalf)]
    have he : (N:ℝ)*(N:ℝ)^(-s.re) ≤ (N:ℝ)^ε := by
      nth_rw 1 [←Real.rpow_one (N:ℝ)]
      rw [←Real.rpow_add hNP]
      apply Real.rpow_le_rpow_of_exponent_le hNR
      linarith
    calc
      _ ≤ D*(N:ℝ)^(-s.re) + ‖s‖*(2*D*(N:ℝ)^(-s.re)) := by
        nth_rw 2 [norm_mul]
        exact add_le_add hboundary (mul_le_mul_of_nonneg_left (htail.trans ht) (norm_nonneg s))
      _ ≤ 2*(N:ℝ)*(N:ℝ)^(-s.re) := by
        have hcoeff : D+2*‖s‖*D ≤ 2*(N:ℝ) := by nlinarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hcoeff) (Real.rpow_nonneg hNP.le (-s.re))]
      _ ≤ _ := by nlinarith [he]
  have hi : ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ ≤ (N:ℝ)^ε/ε := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans (by
      simpa using norm_intervalIntegral_cpow_le hε hNR hs)
  have hp : (N:ℝ)^ε ≤ (N:ℝ)^(2*ε) := Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
  rw [regularSeries_cutoff hf0 hD (fun t ht => hb t ht.le) hN hs0]
  calc
    _ ≤ ‖∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)‖ +
        (‖seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ +
        ‖s*discrepancyTail (seriesDiscrepancy f c) N s‖) +
        ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ := by
      calc
        _ ≤ ‖(∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) - seriesDiscrepancy f c N * (N:ℂ)^(-s) +
             s*discrepancyTail (seriesDiscrepancy f c) N s‖ +
             ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ := norm_sub_le _ _
        _ ≤ (‖(∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) - seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ +
             ‖s*discrepancyTail (seriesDiscrepancy f c) N s‖) +
             ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ := add_le_add (norm_add_le _ _) le_rfl
        _ ≤ _ := by
          have htri := norm_sub_le (∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) (seriesDiscrepancy f c N * (N:ℂ)^(-s))
          linarith
    _ ≤ ((∑' n : ℕ, (n:ℝ)^(-1-ε)))*(N:ℝ)^(2*ε) +
      2*(N:ℝ)^ε+(N:ℝ)^ε/ε := add_le_add (add_le_add (sum_cpow_norm_le hf hε hs hN) hsmall) hi
    _ ≤ ((∑' n : ℕ, (n:ℝ)^(-1-ε)))*(N:ℝ)^(2*ε) +
      2*(N:ℝ)^(2*ε)+(N:ℝ)^(2*ε)/ε := by
        linarith [div_le_div_of_nonneg_right hp hε.le]
    _ = _ := by ring

lemma regularSeries_norm_small_power {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℕ → ℂ) (c : ℂ) (D : ℝ),
      f 0 = 0 → (∀ n, ‖f n‖ ≤ 1) → ‖c‖ ≤ 1 → 0 ≤ D →
      (∀ t, 1 ≤ t → ‖seriesDiscrepancy f c t‖ ≤ D) →
      ∀ s : ℂ, 1-ε ≤ s.re →
      ‖regularSeries f c s‖ ≤ K*((D+1)*(‖s‖+2))^(2*ε) := by
  let K₀ := (∑' n : ℕ, (n:ℝ)^(-1-ε))+2+1/ε
  have hK₀ : 0 < K₀ := by
    have ht : 0 ≤ ∑' n : ℕ, (n:ℝ)^(-1-ε) := tsum_nonneg (fun n => Real.rpow_nonneg n.cast_nonneg _)
    dsimp [K₀]
    positivity
  refine ⟨K₀*2^(2*ε), by positivity, ?_⟩
  intro f c D hf0 hf hc hD hb s hs
  let B := (D+1)*(‖s‖+2)
  have hB : 1 ≤ B := by dsimp [B]; nlinarith [norm_nonneg s]
  let N := ⌈B⌉₊
  have hBN : B ≤ (N:ℝ) := Nat.le_ceil B
  have hN : 1 ≤ N := by exact_mod_cast (hB.trans hBN)
  have hN2 : (N:ℝ) ≤ 2*B := by
    have := Nat.ceil_lt_add_one (zero_lt_one.trans_le hB).le
    change (N:ℝ) < B+1 at this
    linarith
  have hcut := regularSeries_norm_cutoff hf0 hf hc hD hb hε hε1 hN hs
    (show D*(1+‖s‖) ≤ (N:ℝ) from (by dsimp [B] at hBN; nlinarith [norm_nonneg s]))
  calc
    _ ≤ K₀*(N:ℝ)^(2*ε) := hcut
    _ ≤ K₀*(2*B)^(2*ε) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow N.cast_nonneg hN2 (by positivity)) hK₀.le
    _ = _ := by rw [Real.mul_rpow (by norm_num) (by linarith : 0 ≤ B)]; ring

def positiveCoefficients (f : ℕ → ℂ) (n : ℕ) : ℂ := if n = 0 then 0 else f n

lemma positiveCoefficients_zero (f : ℕ → ℂ) : positiveCoefficients f 0 = 0 := by simp [positiveCoefficients]

lemma positiveCoefficients_norm_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (n : ℕ) :
    ‖positiveCoefficients f n‖ ≤ 1 := by
  by_cases hn : n=0 <;> simp [positiveCoefficients,hn,hf]

lemma sum_positiveCoefficients (f : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, positiveCoefficients f n = ∑ n ∈ Icc 1 N, f n := by
  apply sum_congr rfl
  intro n hn
  simp [positiveCoefficients,show n ≠ 0 from Nat.ne_of_gt (mem_Icc.mp hn).1]

lemma LSeries_positiveCoefficients (f : ℕ → ℂ) (s : ℂ) :
    LSeries (positiveCoefficients f) s = LSeries f s := by
  apply LSeries_congr
  intro n hn
  simp [positiveCoefficients,hn]

lemma discrepancy_character_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (t : ℝ) :
    ‖seriesDiscrepancy (positiveCoefficients (fun n => χ (n : ZMod q))) 0 t‖ ≤ q+1 := by
  simpa [seriesDiscrepancy,sum_positiveCoefficients] using char_sum_Icc_norm_le hχ ⌊t⌋₊

lemma discrepancy_constant_bound {t : ℝ} (ht : 1 ≤ t) :
    ‖seriesDiscrepancy (positiveCoefficients (fun _ => 1)) 1 t‖ ≤ 1 := by
  simp only [seriesDiscrepancy,sum_positiveCoefficients,Finset.sum_const,nsmul_eq_mul,
    mul_one,Nat.card_Icc,Nat.add_sub_cancel,one_mul]
  rw [←Complex.ofReal_natCast,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have ht0 := (show (0:ℝ) ≤ t by linarith)
  rw [abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le ht0))]
  have := Nat.lt_floor_add_one t
  linarith

lemma regularSeries_character_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) 0 s = χ.LFunction s := by
  let f := positiveCoefficients (fun n => χ (n : ZMod q))
  have hfrac : AnalyticOnNhd ℂ (regularSeries f 0) {s : ℂ | 0 < s.re} := by
    apply DifferentiableOn.analyticOnNhd ?_ (show IsOpen {z : ℂ | 0 < z.re} from isOpen_lt continuous_const Complex.continuous_re)
    intro s hs
    exact (regularSeries_differentiableAt (by positivity : (0:ℝ) ≤ q+1)
      (fun t _ => discrepancy_character_bound hχ t) hs).differentiableWithinAt
  have hL : AnalyticOnNhd ℂ χ.LFunction {s : ℂ | 0 < s.re} :=
    fun s _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt s
  have he : regularSeries f 0 =ᶠ[𝓝 (2:ℂ)] χ.LFunction := by
    filter_upwards [(continuous_re.tendsto (2:ℂ)).eventually (lt_mem_nhds (by norm_num : (1:ℝ) < (2:ℂ).re))] with z hz
    rw [regularSeries_eq_LSeries_sub (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
      (by positivity : (0:ℝ) ≤ q+1) (fun t _ => discrepancy_character_bound hχ t) hz]
    simp only [zero_div,sub_zero]
    rw [LSeries_positiveCoefficients,DirichletCharacter.LFunction_eq_LSeries χ hz]
  exact hfrac.eqOn_of_preconnected_of_eventuallyEq hL (convex_halfSpace_re_gt 0).isPreconnected
    (show (2:ℂ) ∈ {s:ℂ | 0<s.re} by norm_num) he hs

lemma LFunction_norm_small_power {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ s : ℂ, 1-ε ≤ s.re →
      ‖χ.LFunction s‖ ≤ K*((q+2)*(‖s‖+2))^(2*ε) := by
  obtain ⟨K,hK,h⟩ := regularSeries_norm_small_power hε hε1
  refine ⟨K,hK,fun q _ χ hχ s hs => ?_⟩
  have he := h _ 0 (q+1) (positiveCoefficients_zero _) (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
    (by simp) (by positivity) (fun t _ => discrepancy_character_bound hχ t) s hs
  rw [regularSeries_character_eq hχ (by linarith)] at he
  convert he using 1
  congr 3
  ring

lemma regularSeries_deriv_norm_small_power {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℕ → ℂ) (c : ℂ) (D : ℝ),
      f 0 = 0 → (∀ n, ‖f n‖ ≤ 1) → ‖c‖ ≤ 1 → 0 ≤ D →
      (∀ t, 1 ≤ t → ‖seriesDiscrepancy f c t‖ ≤ D) →
      ∀ s : ℂ, 1-ε/2 ≤ s.re →
      ‖deriv (regularSeries f c) s‖ ≤ K*((D+1)*(‖s‖+2))^(2*ε) := by
  obtain ⟨K,hK,h⟩ := regularSeries_norm_small_power hε hε1
  refine ⟨K*2^(2*ε)/(ε/2),by positivity,?_⟩
  intro f c D hf0 hf hc hD hb s hs
  have hε2 : 0 < ε/2 := by positivity
  have hre (z:ℂ) (hz : dist z s ≤ ε/2) : 1-ε ≤ z.re := by
    have hd := Complex.re_le_norm (s-z)
    rw [Complex.sub_re,←dist_eq_norm,dist_comm] at hd
    linarith
  have hd : DiffContOnCl ℂ (regularSeries f c) (Metric.ball s (ε/2)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hε2.ne']
    intro z hz
    exact (regularSeries_differentiableAt hD (fun t ht => hb t ht.le) (by
      have := hre z (Metric.mem_closedBall.mp hz)
      linarith)).differentiableWithinAt
  have hbnd (z:ℂ) (hz : z ∈ Metric.sphere s (ε/2)) :
      ‖regularSeries f c z‖ ≤ K*2^(2*ε)*((D+1)*(‖s‖+2))^(2*ε) := by
    have hdist := Metric.mem_sphere.mp hz
    have hzR := hre z hdist.le
    have hnorm : ‖z‖+2 ≤ 2*(‖s‖+2) := by
      have : ‖z‖ ≤ dist z s + ‖s‖ := by simpa [dist_eq_norm] using norm_add_le (z-s) s
      rw [hdist] at this
      nlinarith [norm_nonneg s]
    calc
      _ ≤ K*((D+1)*(‖z‖+2))^(2*ε) := h f c D hf0 hf hc hD hb z hzR
      _ ≤ K*(2*((D+1)*(‖s‖+2)))^(2*ε) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)) hK.le
      _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity)]; ring
  have hder := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hε2 hd hbnd
  convert hder using 1
  ring

end LargePrimeGaps
end OAI

-- Source module: TaylorBounds
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
open scoped ComplexConjugate
open Filter Topology
open Complex Filter Topology
open Complex Filter Topology Set MeasureTheory Asymptotics
open Finset
open Complex Filter Topology Finset
lemma power_series_tail_bound {a : ℕ → ℝ} {M r z : ℝ} (_hM : 0 ≤ M)
    (hr : 0 < r) (hz : 0 ≤ z) (hzr : z < r)
    (hb : ∀ n, |a n| ≤ M/r^n) (N : ℕ) :
    |∑' n : ℕ, a (n+N)*z^(n+N)| ≤ M*(z/r)^N/(1-z/r) := by
  have hρ : 0 ≤ z/r := div_nonneg hz hr.le
  have hρ1 : z/r < 1 := (div_lt_one hr).mpr hzr
  have hg := (summable_geometric_of_lt_one hρ hρ1).mul_left (M*(z/r)^N)
  have hbound (n : ℕ) : ‖a (n+N)*z^(n+N)‖ ≤ (M*(z/r)^N)*(z/r)^n := by
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg hz _)]
    calc
      _ ≤ (M/r^(n+N))*z^(n+N) := mul_le_mul_of_nonneg_right (hb _) (pow_nonneg hz _)
      _ = M*(z/r)^(n+N) := by rw [div_pow]; ring
      _ = _ := by rw [pow_add]; ring
  have hn := hg.of_nonneg_of_le (fun n => norm_nonneg _) hbound
  calc
    _ = ‖∑' n : ℕ, a (n+N)*z^(n+N)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n : ℕ, ‖a (n+N)*z^(n+N)‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n : ℕ, (M*(z/r)^N)*(z/r)^n := hn.tsum_le_tsum hbound hg
    _ = _ := by rw [tsum_mul_left,tsum_geometric_of_lt_one hρ hρ1]; rfl

lemma residue_lower_bound_of_taylor {a : ℕ → ℝ} {R M r z : ℝ} {N : ℕ}
    (hM : 0 ≤ M) (hr : 0 < r) (hz : 1 < z) (hzr : z < r)
    (hb : ∀ n, |a n| ≤ M/r^n) (ha0 : 1-R ≤ a 0)
    (ha : ∀ n, -R ≤ a n) (hN : 1 ≤ N)
    (hvalue : (∑' n : ℕ, a n*z^n) ≤ R/(z-1))
    (htail : M*(z/r)^N/(1-z/r) ≤ 1/2) :
    (z-1)/2 ≤ R*z^N := by
  have heach : ∀ n, (if n=0 then 1 else (0:ℝ)) - R*z^n ≤ a n*z^n := by
    intro n
    by_cases hn : n=0
    · simpa [hn] using ha0
    · simp only [hn,↓reduceIte,zero_sub]
      nlinarith [mul_le_mul_of_nonneg_right (ha n) (pow_nonneg (zero_lt_one.trans hz).le n)]
  have hsum := Finset.sum_le_sum (s := range N) (fun n _ => heach n)
  have hzero : (∑ n ∈ range N, if n=0 then 1 else (0:ℝ)) = 1 := by
    simp [show 0 < N by omega]
  rw [sum_sub_distrib,hzero,←mul_sum] at hsum
  have htail' := power_series_tail_bound hM hr (zero_lt_one.trans hz).le hzr hb N
  have ht : -(1/2:ℝ) ≤ ∑' n : ℕ, a (n+N)*z^(n+N) := by
    have := (abs_le.mp (htail'.trans htail)).1
    linarith
  have hs : Summable (fun n : ℕ => a n*z^n) := by
    have hρ : 0 ≤ z/r := by positivity
    have hρ1 : z/r < 1 := (div_lt_one hr).mpr hzr
    apply ((summable_geometric_of_lt_one hρ hρ1).mul_left M).of_norm_bounded
    intro n
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg (zero_lt_one.trans hz).le _)]
    calc
      _ ≤ (M/r^n)*z^n := mul_le_mul_of_nonneg_right (hb _) (pow_nonneg (zero_lt_one.trans hz).le _)
      _ = M*(z/r)^n := by rw [div_mul_eq_mul_div,div_pow]; ring
  have hdecomp := hs.sum_add_tsum_nat_add N
  have hm : 1/2 ≤ R/(z-1)+R*(∑ n ∈ range N, z^n) := by linarith
  have hgeom := geom_sum_mul z N
  have hv := (le_div_iff₀ (sub_pos.mpr hz)).mp
    (show (1/2:ℝ) ≤ (R+R*(∑ n ∈ range N, z^n)*(z-1))/(z-1) from by
      rw [add_div,mul_div_cancel_right₀ _ (sub_pos.mpr hz).ne']
      exact hm)
  have hid : R+R*(∑ n ∈ range N, z^n)*(z-1) = R*z^N := by
    rw [mul_assoc R, hgeom]
    ring
  rw [hid] at hv
  linarith

noncomputable def signedTaylorCoeff (H : ℂ → ℂ) (n : ℕ) : ℝ :=
  (((-1:ℂ)^n)*(n.factorial:ℂ)⁻¹*iteratedDeriv n H 2).re

lemma signedTaylorCoeff_hasSum {H : ℂ → ℂ} {r z : ℝ}
    (hf : DifferentiableOn ℂ H (Metric.ball 2 r)) (hz : |z| < r) :
    HasSum (fun n => signedTaylorCoeff H n*z^n) (H ((2-z:ℝ):ℂ)).re := by
  have hmem : ((2-z:ℝ):ℂ) ∈ Metric.ball (2:ℂ) r := by
    rw [Metric.mem_ball,dist_eq_norm]
    have he : ((2-z:ℝ):ℂ)-(2:ℂ) = -(z:ℂ) := by push_cast; ring
    simpa [he,Complex.norm_real,Real.norm_eq_abs] using hz
  have hs := (Complex.hasSum_taylorSeries_on_ball hf hmem).map Complex.reCLM Complex.continuous_re
  change HasSum (fun n => ((n.factorial:ℂ)⁻¹ *
    ((((2-z:ℝ):ℂ)-2)^n * iteratedDeriv n H 2)).re) (H ((2-z:ℝ):ℂ)).re at hs
  convert hs using 1
  funext n
  dsimp [signedTaylorCoeff]
  have he : ((2-z:ℝ):ℂ)-(2:ℂ) = -(z:ℂ) := by push_cast; ring
  rw [he, show (-(z:ℂ))^n = (-1:ℂ)^n * (z:ℂ)^n by rw [←mul_pow]; congr 1; ring]
  have hmul : (n.factorial:ℂ)⁻¹*((-1:ℂ)^n*(z:ℂ)^n*iteratedDeriv n H 2) =
      ((-1:ℂ)^n*(n.factorial:ℂ)⁻¹*iteratedDeriv n H 2)*(z:ℂ)^n := by ring
  rw [hmul]
  simp only [←Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,sub_zero]

lemma signedTaylorCoeff_norm_bound {H : ℂ → ℂ} {r M : ℝ} (hr : 0 < r)
    (hf : DiffContOnCl ℂ H (Metric.ball 2 r))
    (hb : ∀ s ∈ Metric.sphere 2 r, ‖H s‖ ≤ M) (n : ℕ) :
    |signedTaylorCoeff H n| ≤ M/r^n := by
  have hder := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hf hb
  have hfact : (n.factorial:ℝ) ≠ 0 := by positivity
  calc
    _ ≤ ‖(-1:ℂ)^n*(n.factorial:ℂ)⁻¹*iteratedDeriv n H 2‖ := Complex.abs_re_le_norm _
    _ = (n.factorial:ℝ)⁻¹*‖iteratedDeriv n H 2‖ := by simp [norm_pow]
    _ ≤ (n.factorial:ℝ)⁻¹*((n.factorial:ℝ)*M/r^n) := by gcongr
    _ = _ := by field_simp

lemma signedTaylorCoeff_pole (R : ℝ) (n : ℕ) :
    signedTaylorCoeff (fun s : ℂ => (R:ℂ)/(s-1)) n = R := by
  unfold signedTaylorCoeff
  simp only [div_eq_mul_inv,iteratedDeriv_const_mul_field]
  have hi : iteratedDeriv n (fun s : ℂ => (s-1)⁻¹) 2 = (-1:ℂ)^n*n.factorial := by
    rw [iteratedDeriv_eq_iterate]
    simpa only [one_mul,one_pow, show (2:ℂ)-1=1 by norm_num, one_zpow,mul_one] using
      congrFun (iter_deriv_inv_linear_sub n (1:ℂ) 1) 2
  rw [hi]
  have hf : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hp : (-1:ℂ)^n*(-1:ℂ)^n = 1 := by rw [←mul_pow]; simp
  have he : (-1:ℂ)^n*(n.factorial:ℂ)⁻¹*((R:ℂ)*((-1:ℂ)^n*n.factorial)) = R := by
    calc
      _ = ((-1:ℂ)^n*(-1:ℂ)^n)*(R:ℂ)*((n.factorial:ℂ)⁻¹*n.factorial) := by ring
      _ = _ := by rw [hp,inv_mul_cancel₀ hf]; ring
  rw [he,Complex.ofReal_re]

lemma signedTaylorCoeff_sub {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 2)
    (hG : AnalyticAt ℂ G 2) (n : ℕ) :
    signedTaylorCoeff (fun s => F s-G s) n = signedTaylorCoeff F n-signedTaylorCoeff G n := by
  unfold signedTaylorCoeff
  have hd := iteratedDeriv_sub (n:=n) hF.contDiffAt hG.contDiffAt
  change iteratedDeriv n (fun s => F s-G s) 2 = _ at hd
  rw [hd,mul_sub,Complex.sub_re]

open scoped ComplexOrder in
lemma signedTaylorCoeff_LSeries_nonneg {a : ℕ → ℂ} (ha : ∀ n, 0 ≤ a n)
    (hc : LSeries.abscissaOfAbsConv a < (2:ℝ)) (n : ℕ) :
    0 ≤ signedTaylorCoeff (LSeries a) n := by
  have h := LSeries.iteratedDeriv_alternating ha hc n
  have hf : (0:ℝ) ≤ (n.factorial:ℝ)⁻¹ := by positivity
  have hr := (Complex.nonneg_iff.mp h).1
  unfold signedTaylorCoeff
  have he : (-1:ℂ)^n*(n.factorial:ℂ)⁻¹*iteratedDeriv n (LSeries a) 2 =
      (n.factorial:ℂ)⁻¹*((-1:ℂ)^n*iteratedDeriv n (LSeries a) 2) := by ring
  rw [he]
  simpa using mul_nonneg hf hr

open scoped ComplexOrder in
lemma LSeries_two_re_ge_one {a : ℕ → ℂ} (ha : ∀ n, 0 ≤ a n)
    (ha1 : 1 ≤ a 1) (hc : LSeries.abscissaOfAbsConv a < (2:ℝ)) :
    1 ≤ (LSeries a 2).re := by
  have hs : LSeriesSummable a 2 := LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using hc)
  have hl := hs.le_tsum 1 (fun n _ => LSeries.term_nonneg (ha n) 2)
  have hterm : LSeries.term a 2 1 = a 1 := by simp
  rw [hterm] at hl
  exact (Complex.le_def.mp (ha1.trans hl)).1

open scoped ComplexOrder in
set_option maxHeartbeats 800000 in
lemma signedTaylorCoeff_regular_nonneg {H : ℂ → ℂ} {a : ℕ → ℂ} {R : ℝ}
    (ha : ∀ n, 0 ≤ a n) (ha1 : 1 ≤ a 1)
    (hc : LSeries.abscissaOfAbsConv a < (2:ℝ))
    (he : H =ᶠ[𝓝 (2:ℂ)] fun s => LSeries a s-(R:ℂ)/(s-1)) :
    1-R ≤ (H 2).re ∧ ∀ n, -R ≤ signedTaylorCoeff H n := by
  have hL : AnalyticAt ℂ (LSeries a) 2 := LSeries_analyticOnNhd a 2 (by simpa using hc)
  have hP : AnalyticAt ℂ (fun s : ℂ => (R:ℂ)/(s-1)) 2 :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (by norm_num)
  constructor
  · rw [he.self_of_nhds]
    have h := LSeries_two_re_ge_one ha ha1 hc
    simp only [show (2:ℂ)-1=1 by norm_num,div_one,Complex.sub_re,Complex.ofReal_re]
    linarith
  · intro n
    unfold signedTaylorCoeff
    rw [he.iteratedDeriv_eq]
    change -R ≤ signedTaylorCoeff (fun s => LSeries a s-(R:ℂ)/(s-1)) n
    rw [signedTaylorCoeff_sub hL hP,signedTaylorCoeff_pole]
    linarith [signedTaylorCoeff_LSeries_nonneg ha hc n]

lemma residue_polynomial_lower {a : ℕ → ℝ} {R A Q z ε : ℝ}
    (hA : 0 ≤ A) (hQ : 2 ≤ Q) (hQA : 12*A ≤ Q)
    (hz : 1 < z) (hz1 : z ≤ 5/4) (hzε : 60*(z-1) ≤ ε)
    (hb : ∀ n, |a n| ≤ (A*Q^4)/(3/2)^n)
    (ha0 : 1-R ≤ a 0) (ha : ∀ n, -R ≤ a n)
    (hv : (∑' n : ℕ, a n*z^n) ≤ R/(z-1)) :
    ((z-1)/(2*z))*Q^(-ε) ≤ R := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
  have hz0 : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos hz
  let N : ℕ := ⌈60*Real.log Q⌉₊
  have hNlo : 60*Real.log Q ≤ (N:ℝ) := Nat.le_ceil _
  have hNhi : (N:ℝ) < 60*Real.log Q+1 := Nat.ceil_lt_add_one (by positivity)
  have hN : 1 ≤ N := by
    have : 0 < (N:ℝ) := lt_of_lt_of_le (by positivity) hNlo
    exact_mod_cast (show 1 ≤ N from Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast this.ne'))
  have hρ : 0 ≤ z/(3/2) := by positivity
  have hρ1 : z/(3/2) ≤ 5/6 := by linarith
  have hlogρ : Real.log (5/6:ℝ) ≤ -(1/6:ℝ) := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 5/6)
    linarith
  have hdecay : (z/(3/2))^N ≤ Q^(-10:ℝ) := by
    calc
      _ ≤ (5/6:ℝ)^N := pow_le_pow_left₀ hρ hρ1 N
      _ = Real.exp (Real.log (5/6:ℝ)*(N:ℝ)) := by
        rw [←Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 5/6)]
      _ ≤ Real.exp (Real.log Q*(-10)) := by
        apply Real.exp_le_exp.mpr
        have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
        nlinarith [mul_le_mul_of_nonneg_right hlogρ hN0]
      _ = _ := (Real.rpow_def_of_pos hQ0 _).symm
  have htail : (A*Q^4)*(z/(3/2))^N/(1-z/(3/2)) ≤ 1/2 := by
    have hden : 0 < 1-z/(3/2) := by linarith
    have hpow : Q^4*Q^(-10:ℝ) ≤ Q⁻¹ := by
      calc
        _ = Q^(-6:ℝ) := by
          rw [←Real.rpow_natCast,←Real.rpow_add hQ0]
          norm_num
        _ ≤ Q^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
        _ = Q⁻¹ := Real.rpow_neg_one Q
    have hp : (A*Q^4)*(z/(3/2))^N ≤ A/Q := by
      calc
        _ ≤ (A*Q^4)*Q^(-10:ℝ) := mul_le_mul_of_nonneg_left hdecay (by positivity)
        _ ≤ A*Q⁻¹ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hpow hA
        _ = _ := by rw [div_eq_mul_inv]
    have hAQ : A/Q ≤ 1/12 := (div_le_iff₀ hQ0).mpr (by linarith)
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hres := residue_lower_bound_of_taylor (by positivity : (0:ℝ) ≤ A*Q^4)
    (by norm_num : (0:ℝ) < 3/2) hz (by linarith : z < 3/2) hb ha0 ha hN hv htail
  have hzpow : z^N ≤ z*Q^ε := by
    have hlogz' : 60*Real.log z ≤ ε := by
      have := Real.log_le_sub_one_of_pos hz0
      linarith
    calc
      _ = Real.exp (Real.log z*(N:ℝ)) := by rw [←Real.rpow_natCast,Real.rpow_def_of_pos hz0]
      _ ≤ Real.exp (Real.log z+(Real.log Q)*ε) := by
        apply Real.exp_le_exp.mpr
        have h1 := mul_le_mul_of_nonneg_left hNhi.le hlogz.le
        have h2 := mul_le_mul_of_nonneg_left hlogz' hlogQ.le
        nlinarith
      _ = _ := by rw [Real.exp_add,Real.exp_log hz0,Real.rpow_def_of_pos hQ0]
  have hR : 0 ≤ R := by
    by_contra! h
    have := mul_neg_of_neg_of_pos h (pow_pos hz0 N)
    linarith
  have hres' : (z-1)/2 ≤ R*(z*Q^ε) := hres.trans (mul_le_mul_of_nonneg_left hzpow hR)
  rw [Real.rpow_neg hQ0.le,←div_eq_mul_inv]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hQ0 ε)).mpr
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*z)).mpr
  nlinarith

open Complex Filter Topology Finset Set MeasureTheory
noncomputable def zetaRegular : ℂ → ℂ :=
  regularSeries (positiveCoefficients (fun _ => 1)) 1

lemma zetaRegular_differentiableAt {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ zetaRegular s :=
  regularSeries_differentiableAt zero_le_one (fun _ ht => discrepancy_constant_bound ht.le) hs

lemma zetaRegular_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    zetaRegular s = riemannZeta s-1/(s-1) := by
  rw [zetaRegular,regularSeries_eq_LSeries_sub (positiveCoefficients_norm_le (by simp))
    zero_le_one (fun _ ht => discrepancy_constant_bound ht.le) hs,LSeries_positiveCoefficients]
  rw [show (fun _ : ℕ => (1:ℂ)) = 1 from rfl,LSeries_one_eq_riemannZeta hs]

lemma poleRemovedZeta_eq {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunctionTrivChar₁ 1 s = (s-1)*zetaRegular s+1 := by
  have hF : AnalyticOnNhd ℂ (DirichletCharacter.LFunctionTrivChar₁ 1) {s : ℂ | 0 < s.re} :=
    fun z _ => (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).analyticAt z
  have hG : AnalyticOnNhd ℂ (fun s : ℂ => (s-1)*zetaRegular s+1) {s : ℂ | 0 < s.re} := by
    apply DifferentiableOn.analyticOnNhd ?_ (show IsOpen {z : ℂ | 0 < z.re} from isOpen_lt continuous_const Complex.continuous_re)
    intro z hz
    exact (((differentiableAt_id.sub_const 1).mul (zetaRegular_differentiableAt hz)).add_const 1).differentiableWithinAt
  have he : DirichletCharacter.LFunctionTrivChar₁ 1 =ᶠ[𝓝 (2:ℂ)]
      fun s : ℂ => (s-1)*zetaRegular s+1 := by
    filter_upwards [(continuous_re.tendsto (2:ℂ)).eventually
      (lt_mem_nhds (by norm_num : (1:ℝ) < (2:ℂ).re))] with z hz
    have hz1 : z ≠ 1 := by intro h; simp [h] at hz
    rw [DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hz1,
      DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq,
      zetaRegular_eq_of_one_lt_re hz]
    field_simp
    ring
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG (convex_halfSpace_re_gt 0).isPreconnected
    (show (2:ℂ) ∈ {s : ℂ | 0 < s.re} by norm_num) he hs

lemma zetaRegular_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    zetaRegular s = riemannZeta s-1/(s-1) := by
  have h := poleRemovedZeta_eq hs
  rw [DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hs1,
    DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq] at h
  have hn : s-1 ≠ 0 := sub_ne_zero.mpr hs1
  apply (mul_left_cancel₀ hn)
  rw [mul_sub,mul_div_cancel₀ _ hn]
  linear_combination -h

lemma regularSeries_norm_simple {f : ℕ → ℂ} {c : ℂ} {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    ‖regularSeries f c s‖ ≤ ‖c‖+‖s‖*D/s.re := by
  have h := discrepancyTail_norm_le zero_lt_one hD (measurable_seriesDiscrepancy f c) hb hs
  simp only [Real.one_rpow,mul_one] at h
  calc
    _ ≤ ‖c‖+‖s*discrepancyTail (seriesDiscrepancy f c) 1 s‖ := norm_add_le _ _
    _ ≤ ‖c‖+‖s‖*(D/s.re) := by rw [norm_mul]; gcongr
    _ = _ := by ring

lemma closedBall_two_re_norm {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    (1/4:ℝ) ≤ s.re ∧ ‖s‖ ≤ 4 := by
  have hd := Metric.mem_closedBall.mp hs
  have hr := Complex.re_le_norm ((2:ℂ)-s)
  rw [Complex.sub_re,←dist_eq_norm,dist_comm] at hr
  have hn : ‖s‖ ≤ dist s 2+‖(2:ℂ)‖ := by simpa [dist_eq_norm] using norm_add_le (s-2) (2:ℂ)
  norm_num at hr hn
  constructor <;> linarith

lemma zetaRegular_norm_le_seventeen {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    ‖zetaRegular s‖ ≤ 17 := by
  obtain ⟨hre,hnorm⟩ := closedBall_two_re_norm hs
  have hp : 0 < s.re := by linarith
  have h := regularSeries_norm_simple zero_le_one (fun _ ht => discrepancy_constant_bound ht.le) hp
  change ‖zetaRegular s‖ ≤ _ at h
  norm_num at h
  have hq : ‖s‖/s.re ≤ 16 := (div_le_iff₀ hp).mpr (by linarith)
  linarith

lemma LFunction_norm_polynomial {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    ‖χ.LFunction s‖ ≤ 16*((q:ℝ)+1) := by
  obtain ⟨hre,hnorm⟩ := closedBall_two_re_norm hs
  have hp : 0 < s.re := by linarith
  have hb := regularSeries_norm_simple (by positivity : (0:ℝ) ≤ q+1)
    (fun t _ => discrepancy_character_bound hχ t) hp
  rw [regularSeries_character_eq hχ hp] at hb
  simp only [norm_zero,zero_add] at hb
  apply hb.trans
  apply (div_le_iff₀ hp).mpr
  nlinarith [Nat.cast_nonneg (α:=ℝ) q]

noncomputable def regularizedZetaProduct (P : ℂ → ℂ) (s : ℂ) : ℂ :=
  zetaRegular s*P s+dslope P 1 s

lemma regularizedZetaProduct_differentiableOn {P : ℂ → ℂ}
    (hP : DifferentiableOn ℂ P {s : ℂ | 0 < s.re}) :
    DifferentiableOn ℂ (regularizedZetaProduct P) {s : ℂ | 0 < s.re} := by
  have hs : {s : ℂ | 0 < s.re} ∈ 𝓝 (1:ℂ) :=
    (show IsOpen {z : ℂ | 0 < z.re} from isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hd := (Complex.differentiableOn_dslope hs).mpr hP
  have hz : DifferentiableOn ℂ zetaRegular {s : ℂ | 0 < s.re} :=
    fun s hs => (zetaRegular_differentiableAt hs).differentiableWithinAt
  exact (hz.mul hP).add hd

lemma regularizedZetaProduct_eq {P : ℂ → ℂ} {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    regularizedZetaProduct P s = riemannZeta s*P s-P 1/(s-1) := by
  rw [regularizedZetaProduct,zetaRegular_eq hs hs1,dslope_of_ne P hs1,slope_def_field]
  ring

lemma regularizedZetaProduct_bound {P : ℂ → ℂ} {B : ℝ}
    (hP : DifferentiableOn ℂ P {s : ℂ | 0 < s.re}) (_hB : 0 ≤ B)
    (hb : ∀ s ∈ Metric.closedBall (2:ℂ) (7/4:ℝ), ‖P s‖ ≤ B) :
    DiffContOnCl ℂ (regularizedZetaProduct P) (Metric.ball 2 (3/2:ℝ)) ∧
      ∀ s ∈ Metric.closedBall (2:ℂ) (3/2:ℝ), ‖regularizedZetaProduct P s‖ ≤ 21*B := by
  have hsRe (s : ℂ) (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) : 0 < s.re := by
    have := (closedBall_two_re_norm hs).1
    linarith
  have hder (s : ℂ) (hs : s ∈ Metric.closedBall 2 (3/2:ℝ)) : ‖deriv P s‖ ≤ 4*B := by
    have hsub : Metric.closedBall s (1/4:ℝ) ⊆ Metric.closedBall (2:ℂ) (7/4:ℝ) := by
      intro z hz
      have hdist := dist_triangle z s (2:ℂ)
      have hz' := Metric.mem_closedBall.mp hz
      have hs' := Metric.mem_closedBall.mp hs
      apply Metric.mem_closedBall.mpr
      linarith
    have hdiff : DiffContOnCl ℂ P (Metric.ball s (1/4:ℝ)) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball _ (by norm_num : (1/4:ℝ) ≠ 0)]
      exact hP.mono (fun z hz => hsRe z (hsub hz))
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ) < 1/4)
      hdiff (fun z hz => hb z (hsub (Metric.sphere_subset_closedBall hz)))
    convert h using 1; ring
  have hone : (1:ℂ) ∈ Metric.closedBall (2:ℂ) (3/2:ℝ) := by
    norm_num [Metric.mem_closedBall,dist_eq_norm]
  have hdslope (s : ℂ) (hs : s ∈ Metric.closedBall 2 (3/2:ℝ)) : ‖dslope P 1 s‖ ≤ 4*B := by
    by_cases hs1 : s = 1
    · subst s
      simpa only [dslope_same] using hder 1 hone
    · rw [dslope_of_ne P hs1,slope_def_field,norm_div]
      have hd := (convex_closedBall (2:ℂ) (3/2:ℝ)).norm_image_sub_le_of_norm_deriv_le
        (fun z hz => (hP z (hsRe z (Metric.closedBall_subset_closedBall (by norm_num) hz))).differentiableAt
          ((show IsOpen {z : ℂ | 0 < z.re} from isOpen_lt continuous_const Complex.continuous_re).mem_nhds
            (hsRe z (Metric.closedBall_subset_closedBall (by norm_num) hz)))) hder hone hs
      exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs1))).mpr hd
  constructor
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (by norm_num : (3/2:ℝ) ≠ 0)]
    exact (regularizedZetaProduct_differentiableOn hP).mono
      (fun z hz => hsRe z (Metric.closedBall_subset_closedBall (by norm_num) hz))
  · intro s hs
    have hs' := Metric.closedBall_subset_closedBall (by norm_num : (3/2:ℝ) ≤ 7/4) hs
    calc
      _ ≤ ‖zetaRegular s*P s‖+‖dslope P 1 s‖ := norm_add_le _ _
      _ ≤ 17*B+4*B := by rw [norm_mul]; gcongr; exact zetaRegular_norm_le_seventeen hs'; exact hb s hs'; exact hdslope s hs
      _ = _ := by ring

open Complex Finset ArithmeticFunction
open scoped ComplexOrder
def PrimePowerEq (p : ℕ) (f g : ArithmeticFunction ℂ) : Prop :=
  ∀ k : ℕ, f (p^k) = g (p^k)

lemma PrimePowerEq.refl (p : ℕ) (f : ArithmeticFunction ℂ) : PrimePowerEq p f f := fun _ => rfl

lemma PrimePowerEq.mul {p : ℕ} (hp : p.Prime) {f f' g g' : ArithmeticFunction ℂ}
    (hf : PrimePowerEq p f f') (hg : PrimePowerEq p g g') : PrimePowerEq p (f*g) (f'*g') := by
  intro k
  simp only [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨i,hi,hxi⟩ := (Nat.dvd_prime_pow hp).mp (Nat.mem_divisors.mp
    (Nat.fst_mem_divisors_of_mem_antidiagonal hx)).1
  obtain ⟨j,hj,hxj⟩ := (Nat.dvd_prime_pow hp).mp (Nat.mem_divisors.mp
    (Nat.snd_mem_divisors_of_mem_antidiagonal hx)).1
  rw [hxi,hxj,hf,hg]

lemma primePower_zeta {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ) (p^k) = 1 := by
  simp [hp.ne_zero]

lemma primePower_one {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (1 : ArithmeticFunction ℂ) (p^k) = (0:ℂ)^k := by
  cases k with
  | zero => simp
  | succ k =>
    have hn : p^(k+1) ≠ 1 := by
      have h : 1 < p^(k+1) := one_lt_pow₀ hp.one_lt (by omega)
      omega
    simp [hp.ne_one]

lemma primePower_character {q p : ℕ} (χ : DirichletCharacter ℂ q) (hp : p.Prime) (k : ℕ) :
    toArithmeticFunction (χ ·) (p^k) = χ (p : ZMod q)^k := by
  simp [toArithmeticFunction,hp.ne_zero]

lemma arithmetic_convolution_nonneg {f g : ArithmeticFunction ℂ}
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (n : ℕ) : 0 ≤ (f*g) n := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (hf x.1) (hg x.2))

noncomputable def biquadraticCoefficients {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) : ArithmeticFunction ℂ :=
  ArithmeticFunction.zeta * toArithmeticFunction (χ ·) * toArithmeticFunction (ψ ·) *
    (toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·))

lemma biquadraticCoefficients_multiplicative {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    (biquadraticCoefficients χ ψ).IsMultiplicative := by
  exact ((isMultiplicative_zeta.natCast.mul (DirichletCharacter.isMultiplicative_toArithmeticFunction χ)).mul
    (DirichletCharacter.isMultiplicative_toArithmeticFunction ψ)).mul
    ((DirichletCharacter.isMultiplicative_toArithmeticFunction χ).pmul (DirichletCharacter.isMultiplicative_toArithmeticFunction ψ))

lemma biquadraticCoefficients_comm {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    biquadraticCoefficients χ ψ = biquadraticCoefficients ψ χ := by
  unfold biquadraticCoefficients
  rw [ArithmeticFunction.pmul_comm]
  ring

lemma biquadratic_prime_zero {q r p : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (hp : p.Prime)
    (hχ : χ (p : ZMod q) = 0) :
    PrimePowerEq p (biquadraticCoefficients χ ψ) ψ.zetaMul := by
  have hf : PrimePowerEq p (toArithmeticFunction (χ ·)) 1 := by
    intro k
    rw [primePower_character χ hp, hχ,primePower_one hp]
  have hh : PrimePowerEq p ((toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·))) 1 := by
    intro k
    rw [ArithmeticFunction.pmul_apply,primePower_character χ hp,primePower_character ψ hp,
      hχ,←mul_pow,zero_mul,primePower_one hp]
  have h := ((PrimePowerEq.refl p (ArithmeticFunction.zeta : ArithmeticFunction ℂ)).mul hp hf).mul hp
    (PrimePowerEq.refl p (toArithmeticFunction (ψ ·))) |>.mul hp hh
  simpa only [mul_one,biquadraticCoefficients,DirichletCharacter.zetaMul] using h

lemma biquadratic_prime_one {q r p : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (hp : p.Prime)
    (hχ : χ (p : ZMod q) = 1) :
    PrimePowerEq p (biquadraticCoefficients χ ψ) (ψ.zetaMul*ψ.zetaMul) := by
  have hf : PrimePowerEq p (toArithmeticFunction (χ ·)) ArithmeticFunction.zeta := by
    intro k
    rw [primePower_character χ hp,hχ,one_pow,primePower_zeta hp]
  have hh : PrimePowerEq p ((toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·)))
      (toArithmeticFunction (ψ ·)) := by
    intro k
    rw [ArithmeticFunction.pmul_apply,primePower_character χ hp,hχ,one_pow,one_mul]
  have h := ((PrimePowerEq.refl p (ArithmeticFunction.zeta : ArithmeticFunction ℂ)).mul hp hf).mul hp
    (PrimePowerEq.refl p (toArithmeticFunction (ψ ·))) |>.mul hp hh
  have he : (ArithmeticFunction.zeta : ArithmeticFunction ℂ)*ArithmeticFunction.zeta*
      toArithmeticFunction (ψ ·)*toArithmeticFunction (ψ ·) = ψ.zetaMul*ψ.zetaMul := by
    unfold DirichletCharacter.zetaMul
    ring
  simpa only [he,biquadraticCoefficients] using h

lemma biquadratic_prime_neg_one {q r p : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (hp : p.Prime)
    (hχ : χ (p : ZMod q) = -1) (hψ : ψ (p : ZMod r) = -1) :
    PrimePowerEq p (biquadraticCoefficients χ ψ) (χ.zetaMul*χ.zetaMul) := by
  have hg : PrimePowerEq p (toArithmeticFunction (ψ ·)) (toArithmeticFunction (χ ·)) := by
    intro k
    rw [primePower_character ψ hp,primePower_character χ hp,hχ,hψ]
  have hh : PrimePowerEq p ((toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·)))
      ArithmeticFunction.zeta := by
    intro k
    rw [ArithmeticFunction.pmul_apply,primePower_character χ hp,primePower_character ψ hp,
      hχ,hψ,←mul_pow,neg_mul_neg,one_mul,one_pow,primePower_zeta hp]
  have h := ((PrimePowerEq.refl p (ArithmeticFunction.zeta : ArithmeticFunction ℂ)).mul hp
    (PrimePowerEq.refl p (toArithmeticFunction (χ ·)))).mul hp hg |>.mul hp hh
  have he : (ArithmeticFunction.zeta : ArithmeticFunction ℂ)*toArithmeticFunction (χ ·)*
      toArithmeticFunction (χ ·)*ArithmeticFunction.zeta = χ.zetaMul*χ.zetaMul := by
    unfold DirichletCharacter.zetaMul
    ring
  simpa only [he,biquadraticCoefficients] using h

lemma biquadraticCoefficients_nonneg {q r : ℕ} {χ : DirichletCharacter ℂ q}
    {ψ : DirichletCharacter ℂ r} (hχ : χ^2=1) (hψ : ψ^2=1) (n : ℕ) :
    0 ≤ biquadraticCoefficients χ ψ n := by
  have hp (p : ℕ) (hp : p.Prime) (k : ℕ) : 0 ≤ biquadraticCoefficients χ ψ (p^k) := by
    rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ (p:ZMod q) with h0|h1|hm
    · rw [biquadratic_prime_zero χ ψ hp h0 k]
      exact DirichletCharacter.zetaMul_nonneg hψ _
    · rw [biquadratic_prime_one χ ψ hp h1 k]
      exact arithmetic_convolution_nonneg (DirichletCharacter.zetaMul_nonneg hψ)
        (DirichletCharacter.zetaMul_nonneg hψ) _
    · rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hψ (p:ZMod r) with h0|h1|hm'
      · rw [biquadraticCoefficients_comm χ ψ,biquadratic_prime_zero ψ χ hp h0 k]
        exact DirichletCharacter.zetaMul_nonneg hχ _
      · rw [biquadraticCoefficients_comm χ ψ,biquadratic_prime_one ψ χ hp h1 k]
        exact arithmetic_convolution_nonneg (DirichletCharacter.zetaMul_nonneg hχ)
          (DirichletCharacter.zetaMul_nonneg hχ) _
      · rw [biquadratic_prime_neg_one χ ψ hp hm hm' k]
        exact arithmetic_convolution_nonneg (DirichletCharacter.zetaMul_nonneg hχ)
          (DirichletCharacter.zetaMul_nonneg hχ) _
  rcases eq_or_ne n 0 with rfl|hn
  · simp
  · simpa only [(biquadraticCoefficients_multiplicative χ ψ).multiplicative_factorization _ hn,
      Finsupp.prod, Nat.support_factorization] using
      Finset.prod_nonneg (fun p hp' => hp p (Nat.prime_of_mem_primeFactors hp') _)

end LargePrimeGaps
end OAI

-- Source module: SiegelBounds
namespace OAI
namespace LargePrimeGaps
section
open Complex Filter Topology Set MeasureTheory Finset ArithmeticFunction
lemma quadratic_character_im {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ^2=1)
    (a : ZMod q) : (χ a).im = 0 := by
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ a with h|h|h <;> simp [h]

lemma regularSeries_im_zero {f : ℕ → ℂ} {c : ℂ} {D : ℝ}
    (hf : ∀ n, (f n).im=0) (hc : c.im=0) (hD : 0 ≤ D)
    (hb : ∀ t, 1<t → ‖seriesDiscrepancy f c t‖ ≤ D) {x : ℝ} (hx : 0<x) :
    (regularSeries f c x).im=0 := by
  have hi := discrepancyTail_integrable zero_lt_one hD (measurable_seriesDiscrepancy f c) hb
    (show 0<(x:ℂ).re from hx)
  have he : (discrepancyTail (seriesDiscrepancy f c) 1 x).im=0 := by
    unfold discrepancyTail
    change RCLike.im (∫ t in Ioi (1:ℝ), seriesDiscrepancy f c t*(t:ℂ)^(-((x:ℂ)+1)))=0
    rw [←integral_im hi]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hp : ((t:ℂ)^(-((x:ℂ)+1))).im=0 := by
      rw [show -((x:ℂ)+1)= (-(x+1):ℝ) by push_cast; rfl,
        ←Complex.ofReal_cpow (by exact (zero_lt_one.trans ht).le : 0≤t)]
      rfl
    change (seriesDiscrepancy f c t * (t:ℂ)^(-((x:ℂ)+1))).im=0
    rw [Complex.mul_im,hp,mul_zero,zero_add]
    have hz : (seriesDiscrepancy f c t).im=0 := by simp [seriesDiscrepancy,Complex.mul_im,hc,hf]
    rw [hz,zero_mul]
  simp [regularSeries,Complex.mul_im,hc,he]

lemma quadratic_LFunction_im {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) (hχ2 : χ^2=1) {x : ℝ} (hx : 0<x) : (χ.LFunction x).im=0 := by
  rw [←regularSeries_character_eq hχ hx]
  apply regularSeries_im_zero _ (by simp) (by positivity : (0:ℝ)≤q+1)
    (fun t _ => discrepancy_character_bound hχ t) hx
  intro n
  simp only [positiveCoefficients]
  split_ifs <;> simp [quadratic_character_im hχ2]

lemma LSeries_character_summable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (toArithmeticFunction (fun n : ℕ => χ (n : ZMod q))) s := by
  apply (LSeriesSummable_congr _ (fun h => (χ.apply_eq_toArithmeticFunction_apply h).symm)).mpr
  exact ZMod.LSeriesSummable_of_one_lt_re χ hs

lemma LSeries_character_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) :
    LSeries (toArithmeticFunction (fun n : ℕ => χ (n : ZMod q))) s = χ.LFunction s := by
  rw [χ.LFunction_eq_LSeries hs]
  exact (LSeries_congr χ.apply_eq_toArithmeticFunction_apply s).symm

lemma LSeries_zeta_complex_eq {s : ℂ} (hs : 1<s.re) :
    LSeries (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s=riemannZeta s := by
  rw [←LSeries_one_eq_riemannZeta hs]
  apply LSeries_congr
  intro n hn
  simp [hn]

lemma LSeries_zetaMul_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) : LSeries χ.zetaMul s=riemannZeta s*χ.LFunction s := by
  have hz : LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m:=1) _ hs
    intro n hn
    simp [hn]
  rw [DirichletCharacter.zetaMul,ArithmeticFunction.LSeries_mul' hz
    (LSeries_character_summable χ hs),LSeries_character_eq χ hs,LSeries_zeta_complex_eq hs]

open scoped ComplexOrder in
lemma quadratic_LFunction_re_pos_of_one_lt {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ2 : χ^2=1) {x : ℝ} (hx : 1<x) :
    0<(χ.LFunction x).re := by
  have hp := LSeries.positive (DirichletCharacter.zetaMul_nonneg hχ2)
    (χ.isMultiplicative_zetaMul.map_one ▸ zero_lt_one)
    (lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun s hs => χ.LSeriesSummable_zetaMul hs)) (show (1:EReal)<x by exact_mod_cast hx))
  rw [LSeries_zetaMul_eq χ hx] at hp
  have hr := (Complex.pos_iff.mp hp).1
  rw [Complex.mul_re,riemannZeta_im_eq_zero_of_one_lt hx,zero_mul,sub_zero] at hr
  exact (mul_pos_iff.mp hr).resolve_right (fun h => (riemannZeta_re_pos_of_one_lt hx).not_ge h.1.le) |>.2

lemma quadratic_LFunction_re_pos_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) (hχ2 : χ^2=1) : 0<(χ.LFunction 1).re := by
  have hc : Continuous (fun x : ℝ => (χ.LFunction x).re) :=
    Complex.continuous_re.comp ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
      Complex.continuous_ofReal)
  have hn : 0≤(χ.LFunction 1).re := by
    apply ge_of_tendsto (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto (fun x : ℝ => (χ.LFunction x).re) (𝓝[>] 1) (𝓝 ((χ.LFunction 1).re)))
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (quadratic_LFunction_re_pos_of_one_lt hχ2 hx).le
  refine lt_of_le_of_ne hn ?_
  intro he
  apply DirichletCharacter.LFunction_apply_one_ne_zero hχ
  apply Complex.ext
  · simpa using he.symm
  · simpa using quadratic_LFunction_im hχ hχ2 (x:=1) zero_lt_one

lemma quadratic_LFunction_re_pos_of_no_root {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ≠1) (hχ2 : χ^2=1)
    {β : ℝ} (hβ : 0<β) (hβ1 : β≤1)
    (hz : ∀ x ∈ Set.Icc β 1, χ.LFunction x≠0) : 0<(χ.LFunction β).re := by
  by_contra! hn
  have hc : Continuous (fun x : ℝ => (χ.LFunction x).re) :=
    Complex.continuous_re.comp ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
      Complex.continuous_ofReal)
  obtain ⟨x,hx,hxe⟩ := intermediate_value_Icc hβ1 hc.continuousOn
    (show (0:ℝ) ∈ Set.Icc ((χ.LFunction β).re) ((χ.LFunction 1).re) from
      ⟨hn,(quadratic_LFunction_re_pos_one hχ hχ2).le⟩)
  apply hz x hx
  apply Complex.ext
  · simpa using hxe
  · simpa using quadratic_LFunction_im hχ hχ2 (hβ.trans_le hx.1)

end
section
open Complex Finset ArithmeticFunction
noncomputable def productCharacter {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) : DirichletCharacter ℂ (q*r) :=
  χ.changeLevel (dvd_mul_right q r) * ψ.changeLevel (dvd_mul_left r q)

lemma changeLevel_natCast {q m : ℕ} (χ : DirichletCharacter ℂ q) (hqm : q∣m)
    {n : ℕ} (hn : n.Coprime m) :
    χ.changeLevel hqm (n : ZMod m)=χ (n : ZMod q) := by
  have h := χ.changeLevel_eq_cast_of_dvd hqm (ZMod.unitOfCoprime n hn)
  simp only [ZMod.coe_unitOfCoprime] at h
  rw [ZMod.cast_natCast hqm] at h
  exact h

lemma productCharacter_apply {q r n : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) : productCharacter χ ψ (n : ZMod (q*r))=
      χ (n : ZMod q)*ψ (n : ZMod r) := by
  by_cases hn : n.Coprime (q*r)
  · simp only [productCharacter,MulChar.mul_apply,changeLevel_natCast _ _ hn]
  · rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])]
    by_cases hq : n.Coprime q
    · have hr : ¬n.Coprime r := fun hr => hn (hq.mul_right hr)
      rw [ψ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime]),mul_zero]
    · rw [χ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime]),zero_mul]

lemma productCharacter_quadratic {q r : ℕ} {χ : DirichletCharacter ℂ q}
    {ψ : DirichletCharacter ℂ r} (hχ : χ^2=1) (hψ : ψ^2=1) :
    (productCharacter χ ψ)^2=1 := by
  simp [productCharacter,mul_pow,←map_pow,hχ,hψ]

lemma productCharacter_ne_one_of_levels_ne {q r : ℕ} [NeZero q] [NeZero r]
    {χ : DirichletCharacter ℂ q} {ψ : DirichletCharacter ℂ r}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hψ2 : ψ^2=1) (hqr : q≠r) :
    productCharacter χ ψ≠1 := by
  intro h
  have h2 : (ψ.changeLevel (dvd_mul_left r q))^2=1 := by rw [←map_pow,hψ2,map_one]
  have he : χ.changeLevel (dvd_mul_right q r) = ψ.changeLevel (dvd_mul_left r q) := by
    calc
      _ = (χ.changeLevel (dvd_mul_right q r)*ψ.changeLevel (dvd_mul_left r q))*
          ψ.changeLevel (dvd_mul_left r q) := by rw [mul_assoc,←pow_two,h2,mul_one]
      _ = _ := by rw [show χ.changeLevel (dvd_mul_right q r)*ψ.changeLevel (dvd_mul_left r q)=1 from h,one_mul]
  have hc := congrArg DirichletCharacter.conductor he
  rw [DirichletCharacter.conductor_changeLevel,DirichletCharacter.conductor_changeLevel,
    hχ,hψ] at hc
  exact hqr hc

lemma productCharacter_toArithmeticFunction {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) :
    toArithmeticFunction (productCharacter χ ψ ·)=
      (toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·)) := by
  ext n
  by_cases hn : n=0
  · simp [hn]
  · rw [ArithmeticFunction.pmul_apply]
    simp [toArithmeticFunction,hn,productCharacter_apply]

end
section
open Complex Filter Topology Set MeasureTheory Finset
open scoped ComplexOrder in
lemma zeta_product_residue_lower {P : ℂ → ℂ} {a : ℕ → ℂ} {A B Q β ε : ℝ}
    (hP : DifferentiableOn ℂ P {s : ℂ | 0<s.re})
    (hB : 0≤B) (hb : ∀ s ∈ Metric.closedBall (2:ℂ) (7/4:ℝ), ‖P s‖≤B)
    (hA : 0≤A) (hQ : 2≤Q) (hQA : 12*A≤Q) (hBQ : 21*B≤A*Q^4)
    (hβ : 3/4≤β) (hβ1 : β<1) (hβε : 60*(1-β)≤ε)
    (ha : ∀ n, 0≤a n) (ha1 : 1≤a 1) (haC : LSeries.abscissaOfAbsConv a≤1)
    (haP : ∀ s : ℂ, 1<s.re → LSeries a s=riemannZeta s*P s)
    (hvalue : (riemannZeta β*P β).re≤0) (hreal : (P 1).im=0) :
    ((1-β)/(2*(2-β)))*Q^(-ε)≤(P 1).re := by
  let H := regularizedZetaProduct P
  have hR : P 1=((P 1).re:ℂ) := by apply Complex.ext <;> simp [hreal]
  obtain ⟨hf,hbound⟩ := regularizedZetaProduct_bound hP hB hb
  have he : H =ᶠ[𝓝 (2:ℂ)] fun s => LSeries a s-((P 1).re:ℂ)/(s-1) := by
    filter_upwards [(continuous_re.tendsto (2:ℂ)).eventually
      (lt_mem_nhds (by norm_num : (1:ℝ)<(2:ℂ).re))] with s hs
    have hs1 : s≠1 := by intro h; simp [h] at hs
    rw [show H s=regularizedZetaProduct P s from rfl,regularizedZetaProduct_eq (by linarith) hs1,
      ←haP s hs,hR]
    simp only [Complex.ofReal_re]
  have hac : LSeries.abscissaOfAbsConv a<(2:ℝ) := haC.trans_lt (by exact_mod_cast (show (1:ℝ)<2 by norm_num))
  obtain ⟨ha0,han⟩ := signedTaylorCoeff_regular_nonneg ha ha1 hac he
  have hz : 1<2-β := by linarith
  have hz0 : 0<2-β := by linarith
  have hzr : 2-β<(3/2:ℝ) := by linarith
  have hv : (∑' n : ℕ, signedTaylorCoeff H n*(2-β)^n)≤(P 1).re/((2-β)-1) := by
    rw [(signedTaylorCoeff_hasSum hf.differentiableOn (by rwa [abs_of_pos hz0])).tsum_eq]
    have hβ0 : 0<β := by linarith
    have hβne : (β:ℂ)≠1 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [show (2-(2-β):ℝ)=β by ring]
    change (regularizedZetaProduct P β).re≤_
    rw [regularizedZetaProduct_eq hβ0 hβne,Complex.sub_re,hR,
      ←Complex.ofReal_one,←Complex.ofReal_sub,←Complex.ofReal_div,Complex.ofReal_re]
    have hid : (P 1).re/(β-1) = -(P 1).re/((2-β)-1) := by
      rw [show β-1 = -((2-β)-1) by ring,div_neg,neg_div]
    simp only [Complex.ofReal_one,Complex.ofReal_re]
    rw [hid,neg_div,sub_neg_eq_add]
    exact add_le_of_nonpos_left hvalue
  have hn (n : ℕ) : |signedTaylorCoeff H n|≤(A*Q^4)/(3/2)^n := by
    apply (signedTaylorCoeff_norm_bound (by norm_num : (0:ℝ)<3/2) hf
      (fun s hs => (hbound s (Metric.sphere_subset_closedBall hs)).trans hBQ) n)
  have hr := residue_polynomial_lower (ε:=ε) hA hQ hQA hz (by linarith) (by linarith) hn
    (by simpa [signedTaylorCoeff] using ha0) han hv
  convert hr using 1
  congr 2
  ring

lemma zeta_re_neg_near_one {β : ℝ} (hβ : 99/100≤β) (hβ1 : β<1) :
    (riemannZeta β).re<0 := by
  have hβ0 : 0<β := by linarith
  have hβne : (β:ℂ)≠1 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hmem : (β:ℂ) ∈ Metric.closedBall 2 (7/4:ℝ) := by
    rw [Metric.mem_closedBall,dist_eq_norm,←Complex.ofReal_ofNat,←Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs,abs_of_neg (by linarith : β-2<0)]
    linarith
  have hb := (Complex.re_le_norm (zetaRegular β)).trans (zetaRegular_norm_le_seventeen hmem)
  rw [zetaRegular_eq hβ0 hβne,Complex.sub_re,←Complex.ofReal_one,
    ←Complex.ofReal_sub,←Complex.ofReal_div,Complex.ofReal_re] at hb
  have hd : 1/(β-1)≤-100 := (div_le_iff_of_neg (by linarith : β-1<0)).mpr (by linarith)
  linarith

end
open Complex Filter Topology Set MeasureTheory Finset ArithmeticFunction
lemma LSeries_zeta_complex_summable {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re (m:=1) _ hs
  intro n hn
  simp [hn]

lemma biquadraticCoefficients_summable {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (biquadraticCoefficients χ ψ) s := by
  rw [biquadraticCoefficients,←productCharacter_toArithmeticFunction]
  exact ArithmeticFunction.LSeriesSummable_mul
    (ArithmeticFunction.LSeriesSummable_mul
      (ArithmeticFunction.LSeriesSummable_mul (LSeries_zeta_complex_summable hs) (LSeries_character_summable χ hs))
      (LSeries_character_summable ψ hs)) (LSeries_character_summable (productCharacter χ ψ) hs)

lemma LSeries_biquadratic_eq {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) {s : ℂ} (hs : 1<s.re) :
    LSeries (biquadraticCoefficients χ ψ) s=
      riemannZeta s*(χ.LFunction s*ψ.LFunction s*(productCharacter χ ψ).LFunction s) := by
  have hz := LSeries_zeta_complex_summable hs
  have hχ := LSeries_character_summable χ hs
  have hψ := LSeries_character_summable ψ hs
  have hp := LSeries_character_summable (productCharacter χ ψ) hs
  rw [biquadraticCoefficients,←productCharacter_toArithmeticFunction,
    ArithmeticFunction.LSeries_mul' (ArithmeticFunction.LSeriesSummable_mul (ArithmeticFunction.LSeriesSummable_mul hz hχ) hψ) hp,
    ArithmeticFunction.LSeries_mul' (ArithmeticFunction.LSeriesSummable_mul hz hχ) hψ,
    ArithmeticFunction.LSeries_mul' hz hχ,LSeries_zeta_complex_eq hs,
    LSeries_character_eq χ hs,LSeries_character_eq ψ hs,
    LSeries_character_eq (productCharacter χ ψ) hs]
  ring

lemma quadratic_residue_lower_of_no_root {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ≠1) (hχ2 : χ^2=1)
    {β ε : ℝ} (hβ : 99/100≤β) (hβ1 : β<1) (hβε : 60*(1-β)≤ε)
    (hq : (4032:ℝ)≤q+1) (hz : ∀ x ∈ Set.Icc β 1, χ.LFunction x≠0) :
    ((1-β)/(2*(2-β)))*((q:ℝ)+1)^(-ε)≤‖χ.LFunction 1‖ := by
  have hQ : (2:ℝ)≤q+1 := by linarith
  have hpow : (q:ℝ)+1≤((q:ℝ)+1)^4 := le_self_pow₀ (by linarith) (by norm_num)
  have hv : (riemannZeta β*χ.LFunction β).re≤0 := by
    rw [Complex.mul_re,quadratic_LFunction_im hχ hχ2 (by linarith),mul_zero,sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (zeta_re_neg_near_one hβ hβ1).le
      (quadratic_LFunction_re_pos_of_no_root hχ hχ2 (by linarith) hβ1.le hz).le
  apply le_trans _ (Complex.re_le_norm _)
  apply zeta_product_residue_lower (a:=χ.zetaMul) (A:=336) (B:=16*((q:ℝ)+1))
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn (by positivity)
    (fun s hs => LFunction_norm_polynomial hχ hs) (by norm_num) hQ
    (by norm_num; exact hq) (by nlinarith) (by linarith) hβ1 hβε
    (DirichletCharacter.zetaMul_nonneg hχ2)
    (by simp only [χ.isMultiplicative_zetaMul.map_one,le_refl])
    (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (fun s hs => χ.LSeriesSummable_zetaMul hs))
    (fun s hs => LSeries_zetaMul_eq χ hs) hv
    (by simpa using quadratic_LFunction_im hχ hχ2 (x:=1) zero_lt_one)

lemma biquadratic_norm_bound {q r : ℕ} [NeZero q] [NeZero r]
    {χ : DirichletCharacter ℂ q} {ψ : DirichletCharacter ℂ r}
    (hχ : χ≠1) (hψ : ψ≠1) (hp : productCharacter χ ψ≠1)
    {s : ℂ} (hs : s ∈ Metric.closedBall 2 (7/4:ℝ)) :
    ‖χ.LFunction s*ψ.LFunction s*(productCharacter χ ψ).LFunction s‖≤
      16^3*((q:ℝ)+1)^2*((r:ℝ)+1)^2 := by
  have hq0 : (0:ℝ)≤q := Nat.cast_nonneg q
  have hr0 : (0:ℝ)≤r := Nat.cast_nonneg r
  have hp' := LFunction_norm_polynomial hp hs
  simp only [Nat.cast_mul] at hp'
  calc
    _ ≤ (16*((q:ℝ)+1))*(16*((r:ℝ)+1))*(16*((q:ℝ)*r+1)) := by
      simp only [norm_mul]
      gcongr
      · exact LFunction_norm_polynomial hχ hs
      · exact LFunction_norm_polynomial hψ hs
    _ ≤ _ := by nlinarith [mul_nonneg hq0 hr0]

lemma biquadratic_residue_lower_of_root {q r : ℕ} [NeZero q] [NeZero r]
    {χ : DirichletCharacter ℂ q} {ψ : DirichletCharacter ℂ r}
    (hχ : χ≠1) (hχ2 : χ^2=1) (hψ : ψ≠1) (hψ2 : ψ^2=1)
    (hp : productCharacter ψ χ≠1) {β ε : ℝ}
    (hβ : 3/4≤β) (hβ1 : β<1) (hβε : 60*(1-β)≤ε)
    (hq : (12*(21*16^3*((r:ℝ)+1)^2))≤q+1) (hq1 : (2:ℝ)≤q+1)
    (hz : ψ.LFunction β=0) :
    ((1-β)/(2*(2-β)))*((q:ℝ)+1)^(-ε)≤
      ‖ψ.LFunction 1‖*‖χ.LFunction 1‖*‖(productCharacter ψ χ).LFunction 1‖ := by
  let P := fun s => ψ.LFunction s*χ.LFunction s*(productCharacter ψ χ).LFunction s
  have hd : Differentiable ℂ P :=
    ((DirichletCharacter.differentiable_LFunction hψ).mul
      (DirichletCharacter.differentiable_LFunction hχ)).mul
      (DirichletCharacter.differentiable_LFunction hp)
  have hpow : ((q:ℝ)+1)^2≤((q:ℝ)+1)^4 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have hb : ∀ s ∈ Metric.closedBall (2:ℂ) (7/4:ℝ),
      ‖P s‖≤16^3*((r:ℝ)+1)^2*((q:ℝ)+1)^2 := fun s hs => biquadratic_norm_bound hψ hχ hp hs
  have hiψ : (ψ.LFunction 1).im=0 := by simpa using quadratic_LFunction_im hψ hψ2 (x:=1) zero_lt_one
  have hiχ : (χ.LFunction 1).im=0 := by simpa using quadratic_LFunction_im hχ hχ2 (x:=1) zero_lt_one
  have hip : ((productCharacter ψ χ).LFunction 1).im=0 := by
    simpa using quadratic_LFunction_im hp (productCharacter_quadratic hψ2 hχ2) (x:=1) zero_lt_one
  have hreal : (P 1).im=0 := by simp [P,Complex.mul_im,hiψ,hiχ,hip]
  have hR := zeta_product_residue_lower (P:=P) (a:=biquadraticCoefficients ψ χ)
    (A:=21*16^3*((r:ℝ)+1)^2) (B:=16^3*((r:ℝ)+1)^2*((q:ℝ)+1)^2)
    hd.differentiableOn (by positivity) hb (by positivity) hq1 hq
    (by nlinarith [mul_le_mul_of_nonneg_left hpow (by positivity : (0:ℝ)≤21*16^3*((r:ℝ)+1)^2)])
    hβ hβ1 hβε (biquadraticCoefficients_nonneg hψ2 hχ2)
    (by simp only [(biquadraticCoefficients_multiplicative ψ χ).map_one,le_refl])
    (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun s hs => biquadraticCoefficients_summable ψ χ hs))
    (fun s hs => LSeries_biquadratic_eq ψ χ hs) (by simp [P,hz]) hreal
  have := hR.trans (Complex.re_le_norm (P 1))
  simpa only [P,norm_mul] using this

lemma quadratic_siegel_eventual {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c Q₀ : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → χ^2=1 → Q₀≤(q:ℝ)+1 → c*((q:ℝ)+1)^(-ε)≤‖χ.LFunction 1‖ := by
  classical
  let β₀ : ℝ := 1-ε/240
  have hβ₀ : 99/100≤β₀ := by dsimp [β₀]; linarith
  have hβ₀1 : β₀<1 := by dsimp [β₀]; linarith
  by_cases hex : ∃ r : ℕ, ∃ ψ : DirichletCharacter ℂ (r+1),
      ψ.IsPrimitive ∧ ψ≠1 ∧ ψ^2=1 ∧ ∃ β ∈ Set.Icc β₀ 1, ψ.LFunction β=0
  · obtain ⟨r,ψ,hψprim,hψ,hψ2,β,hβI,hzero⟩ := hex
    have hβ1 : β<1 := lt_of_le_of_ne hβI.2 (by
      intro he
      apply DirichletCharacter.LFunction_apply_one_ne_zero hψ
      simpa [he] using hzero)
    have hβ : 99/100≤β := hβ₀.trans hβI.1
    have hβε : 60*(1-β)≤ε/2 := by dsimp [β₀] at hβI; linarith [hβI.1]
    obtain ⟨K,hK,hgrowth⟩ := LFunction_norm_small_power (by linarith : 0<ε/4)
      (by linarith : ε/4≤1/2)
    let D : ℝ := 3*((r:ℝ)+3)
    let U : ℝ := ‖ψ.LFunction 1‖*K*D^(ε/2)
    have hD : 0<D := by dsimp [D]; positivity
    have hU : 0<U := by
      exact mul_pos (mul_pos (norm_pos_iff.mpr (DirichletCharacter.LFunction_apply_one_ne_zero hψ)) hK)
        (Real.rpow_pos_of_pos hD _)
    let c : ℝ := (1-β)/(2*(2-β))/U
    have hc : 0<c := div_pos (div_pos (by linarith) (by linarith)) hU
    refine ⟨c,max (12*(21*16^3*(((r+1:ℕ):ℝ)+1)^2)) ((r:ℝ)+3),hc,?_⟩
    intro q _ χ hχprim hχ hχ2 hq
    have hq1 : (2:ℝ)≤q+1 := by have := (le_max_right _ _).trans hq; have : (0:ℝ)≤r := Nat.cast_nonneg r; linarith
    have hqr : r+1≠q := by
      have hr := (le_max_right _ _).trans hq
      intro he
      rw [←he] at hr
      push_cast at hr
      linarith
    have hp : productCharacter ψ χ≠1 :=
      productCharacter_ne_one_of_levels_ne hψprim hχprim hχ2 hqr
    have hl := biquadratic_residue_lower_of_root hχ hχ2 hψ hψ2 hp
      (by linarith) hβ1 hβε ((le_max_left _ _).trans hq) hq1 hzero
    have hb := hgrowth ((r+1)*q) (productCharacter ψ χ) hp 1 (by simp; linarith)
    have hQ0 : 0<(q:ℝ)+1 := by positivity
    have he : 2*(ε/4)=ε/2 := by ring
    rw [he] at hb
    have hbase : (((r+1)*q:ℕ):ℝ)+2≤((r:ℝ)+3)*((q:ℝ)+1) := by push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) q,Nat.cast_nonneg (α:=ℝ) r]
    have hb' : ‖(productCharacter ψ χ).LFunction 1‖≤K*D^(ε/2)*((q:ℝ)+1)^(ε/2) := by
      apply hb.trans
      simp only [norm_one]
      calc
        K*(((((r+1)*q:ℕ):ℝ)+2)*(1+2))^(ε/2) ≤ K*(D*((q:ℝ)+1))^(ε/2) := by
          apply mul_le_mul_of_nonneg_left _ hK.le
          apply Real.rpow_le_rpow (by positivity) _ (by linarith)
          dsimp [D]
          nlinarith
        _ = _ := by rw [Real.mul_rpow hD.le hQ0.le]; ring
    have hupper : ‖ψ.LFunction 1‖*‖χ.LFunction 1‖*‖(productCharacter ψ χ).LFunction 1‖≤
        U*((q:ℝ)+1)^(ε/2)*‖χ.LFunction 1‖ := by
      calc
        _ ≤ ‖ψ.LFunction 1‖*‖χ.LFunction 1‖*(K*D^(ε/2)*((q:ℝ)+1)^(ε/2)) := by gcongr
        _ = _ := by dsimp [U]; ring
    have hlow := hl.trans hupper
    have hQp : 0<((q:ℝ)+1)^(ε/2) := Real.rpow_pos_of_pos hQ0 _
    have hexp : ((q:ℝ)+1)^(-ε)*((q:ℝ)+1)^(ε/2)=((q:ℝ)+1)^(-(ε/2)) := by
      rw [←Real.rpow_add hQ0]; congr 1; ring
    have hfinal : U*(c*((q:ℝ)+1)^(-ε)*((q:ℝ)+1)^(ε/2)) ≤
        U*(‖χ.LFunction 1‖*((q:ℝ)+1)^(ε/2)) := by
      calc
        U*(c*((q:ℝ)+1)^(-ε)*((q:ℝ)+1)^(ε/2)) =
            ((1-β)/(2*(2-β)))*((q:ℝ)+1)^(-(ε/2)) := by
          rw [mul_assoc c,hexp]
          dsimp [c]
          field_simp
        _ ≤ U*(‖χ.LFunction 1‖*((q:ℝ)+1)^(ε/2)) := by simpa only [mul_assoc,mul_left_comm,mul_comm] using hlow
    exact (mul_le_mul_iff_left₀ hQp).mp ((mul_le_mul_iff_right₀ hU).mp hfinal)
  · refine ⟨(1-β₀)/(2*(2-β₀)),4032,div_pos (by linarith) (by linarith),?_⟩
    intro q hq χ hχprim hχ hχ2 hqbig
    apply quadratic_residue_lower_of_no_root hχ hχ2 hβ₀ hβ₀1
      (by dsimp [β₀]; linarith) hqbig
    intro x hx hz
    apply hex
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q => exact ⟨q,χ,hχprim,hχ,hχ2,x,hx,hz⟩

lemma finite_positive_lower {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i∈S,0<f i) : ∃ c : ℝ, 0<c ∧ ∀ i∈S,c≤f i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,zero_lt_one,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨c,hc,hcb⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine ⟨min c (f a),lt_min hc (hf a (Finset.mem_insert_self _ _)),?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hcb i hi)

lemma LFunction_one_finite_lower (N : ℕ) :
    ∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      q≤N → χ≠1 → c≤‖χ.LFunction 1‖ := by
  classical
  induction N with
  | zero => exact ⟨1,zero_lt_one,fun q _ χ hq _ => (NeZero.ne q (Nat.eq_zero_of_le_zero hq)).elim⟩
  | succ N ih =>
    obtain ⟨c,hc,hcb⟩ := ih
    obtain ⟨d,hd,hdb⟩ := finite_positive_lower
      ((Finset.univ : Finset (DirichletCharacter ℂ (N+1))).filter (·≠1))
      (fun χ => ‖χ.LFunction 1‖) (fun χ hχ =>
        norm_pos_iff.mpr (DirichletCharacter.LFunction_apply_one_ne_zero (Finset.mem_filter.mp hχ).2))
    refine ⟨min c d,lt_min hc hd,?_⟩
    intro q _ χ hq hχ
    rcases Nat.le_succ_iff_eq_or_le.mp hq with rfl|hq
    · exact (min_le_right _ _).trans (hdb χ (by simp [hχ]))
    · exact (min_le_left _ _).trans (hcb q χ hq hχ)

theorem quadratic_siegel {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → χ^2=1 → c*((q:ℝ)+1)^(-ε)≤‖χ.LFunction 1‖ := by
  obtain ⟨c,Q₀,hc,hcb⟩ := quadratic_siegel_eventual hε hε1
  obtain ⟨d,hd,hdb⟩ := LFunction_one_finite_lower ⌈Q₀⌉₊
  refine ⟨min c d,lt_min hc hd,?_⟩
  intro q _ χ hχp hχ hχ2
  by_cases hq : Q₀≤(q:ℝ)+1
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg (by positivity) _)).trans
      (hcb q χ hχp hχ hχ2 hq)
  · have hqn : q≤⌈Q₀⌉₊ := by
      have := Nat.le_ceil Q₀
      have : (q:ℝ)≤(⌈Q₀⌉₊:ℝ) := by linarith
      exact_mod_cast this
    have hp : ((q:ℝ)+1)^(-ε)≤1 := Real.rpow_le_one_of_one_le_of_nonpos (by have := Nat.cast_nonneg (α:=ℝ) q; linarith) (by linarith)
    exact (mul_le_of_le_one_right (le_of_lt (lt_min hc hd)) hp).trans
      ((min_le_right _ _).trans (hdb q χ hqn hχ))

end LargePrimeGaps
end OAI

-- Source module: ZeroFreeBounds
namespace OAI
namespace LargePrimeGaps
section
open Complex Filter Topology Set MeasureTheory Finset
lemma periodic_sum_norm_le_mul {f : ℕ → ℂ} {q : ℕ} {D : ℝ} (hq : 0<q) (hD : 0≤D)
    (hp : ∀ n,f (q+n)=f n) (hz : ∑ n∈range q,f n=0)
    (hb : ∀ n,‖f n‖≤D) (N : ℕ) : ‖∑ n∈range N,f n‖≤q*D := by
  induction N using Nat.strong_induction_on with
  | ind N ih =>
    by_cases hN : N<q
    · calc
        _ ≤ ∑ n∈range N,‖f n‖ := norm_sum_le _ _
        _ ≤ ∑ _n∈range N,D := sum_le_sum (fun n _ => hb n)
        _ = N*D := by simp
        _ ≤ q*D := mul_le_mul_of_nonneg_right (by exact_mod_cast hN.le) hD
    · have he : q+(N-q)=N := Nat.add_sub_of_le (not_lt.mp hN)
      rw [←he,sum_range_add,hz,zero_add]
      simp_rw [hp]
      exact ih _ (Nat.sub_lt (lt_of_lt_of_le hq (not_lt.mp hN)) hq)

noncomputable def characterMean {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  (∑ n∈range q,χ (n : ZMod q))/(q:ℂ)

lemma characterMean_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖characterMean χ‖≤1 := by
  rw [characterMean,norm_div,Complex.norm_natCast]
  apply (div_le_one (by exact_mod_cast NeZero.pos q : (0:ℝ)<q)).mpr
  calc
    _ ≤ ∑ n∈range q,‖χ (n : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _n∈range q,(1:ℝ) := sum_le_sum (fun n _ => χ.norm_le_one _)
    _ = q := by simp

lemma characterMean_eq_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ≠1) :
    characterMean χ=0 := by simp [characterMean,char_sum_range_zero hχ]

lemma discrepancy_characterMean_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {t : ℝ} (ht : 1≤t) :
    ‖seriesDiscrepancy (positiveCoefficients (fun n => χ (n : ZMod q))) (characterMean χ) t‖≤2*q+3 := by
  let c := characterMean χ
  have hc : ‖c‖≤1 := characterMean_norm_le χ
  have hb (n : ℕ) : ‖χ (n : ZMod q)-c‖≤2 := (norm_sub_le _ _).trans (by linarith [χ.norm_le_one (n : ZMod q)])
  have hz : ∑ n∈range q,(χ (n : ZMod q)-c)=0 := by
    rw [sum_sub_distrib,sum_const,card_range,nsmul_eq_mul]
    dsimp [c,characterMean]
    have hq : (q:ℂ)≠0 := by exact_mod_cast NeZero.ne q
    field_simp
    ring
  have hr := periodic_sum_norm_le_mul (NeZero.pos q) (by norm_num : (0:ℝ)≤2)
    (f:=fun n => χ (n : ZMod q)-c) (by intro n; simp) hz hb (⌊t⌋₊+1)
  have he : ∑ n∈range (⌊t⌋₊+1),(χ (n : ZMod q)-c) =
      χ (0 : ZMod q)-c+ ∑ n∈Icc 1 ⌊t⌋₊,(χ (n : ZMod q)-c) := by
    rw [Nat.range_succ_eq_Icc_zero,←Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le ⌊t⌋₊)]
    simp
    ring
  have ht0 : 0≤t := by linarith
  have hfloor : ‖(⌊t⌋₊:ℂ)-(t:ℂ)‖≤1 := by
    rw [←Complex.ofReal_natCast,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le ht0))]
    have := Nat.lt_floor_add_one t
    linarith
  have heq : seriesDiscrepancy (positiveCoefficients (fun n => χ (n : ZMod q))) c t =
      (∑ n∈range (⌊t⌋₊+1),(χ (n : ZMod q)-c))-(χ 0-c)+c*((⌊t⌋₊:ℂ)-(t:ℂ)) := by
    rw [he]
    simp only [seriesDiscrepancy,sum_positiveCoefficients,sum_sub_distrib,sum_const,Nat.card_Icc,
      Nat.add_sub_cancel,nsmul_eq_mul]
    ring
  rw [heq]
  calc
    _ ≤ ‖∑ n∈range (⌊t⌋₊+1),(χ (n : ZMod q)-c)‖+‖χ 0-c‖+‖c*((⌊t⌋₊:ℂ)-(t:ℂ))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (q:ℝ)*2+2+1 := by
      gcongr
      · simpa using hb 0
      · rw [norm_mul]; exact (mul_le_mul hc hfloor (norm_nonneg _) zero_le_one).trans_eq (by ring)
    _ = _ := by ring

lemma LFunction_regularSeries_characterMean {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) :
    χ.LFunction s = regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) (characterMean χ) s+
      characterMean χ/(s-1) := by
  rw [regularSeries_eq_LSeries_sub (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
    (by positivity : (0:ℝ)≤2*q+3) (fun t ht => discrepancy_characterMean_bound χ ht.le) hs,
    sub_add_cancel,LSeries_positiveCoefficients,←χ.LFunction_eq_LSeries hs]

lemma LFunction_deriv_norm_small_power {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1/2) :
    ∃ K : ℝ,0<K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),χ≠1 →
      ∀ s : ℂ,1-ε/2 ≤ s.re → ‖deriv χ.LFunction s‖≤K*((q+2)*(‖s‖+2))^(2*ε) := by
  obtain ⟨K,hK,h⟩ := regularSeries_deriv_norm_small_power hε hε1
  refine ⟨K,hK,?_⟩
  intro q _ χ hχ s hs
  have he : regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) 0 =ᶠ[𝓝 s] χ.LFunction := by
    filter_upwards [(continuous_re.tendsto s).eventually (lt_mem_nhds (by linarith : 0<s.re))] with z hz
    exact regularSeries_character_eq hχ hz
  rw [←he.deriv_eq]
  have hb := h _ 0 (q+1) (positiveCoefficients_zero _) (positiveCoefficients_norm_le (fun n => χ.norm_le_one _))
    (by simp) (by positivity) (fun t _ => discrepancy_character_bound hχ t) s hs
  convert hb using 1
  congr 3
  ring

noncomputable def characterRegular {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  regularSeries (positiveCoefficients (fun n => χ (n : ZMod q))) (characterMean χ)

lemma character_line_bounds {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1/2) :
    ∃ K : ℝ,1≤K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ),
      (∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
        ‖characterRegular χ s‖≤K*((q+2)*(|t|+2))^(2*ε)) ∧
      (χ≠1 → ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
        ‖deriv χ.LFunction s‖≤K*((q+2)*(|t|+2))^(2*ε)) := by
  obtain ⟨K₀,hK₀,h₀⟩ := regularSeries_norm_small_power hε hε1
  obtain ⟨K₁,hK₁,h₁⟩ := LFunction_deriv_norm_small_power hε hε1
  let K := 1+K₀*8^(2*ε)+K₁*4^(2*ε)
  have hp₀ : 0≤K₀*8^(2*ε) := by positivity
  have hp₁ : 0≤K₁*4^(2*ε) := by positivity
  have hK : 1≤K := by dsimp [K]; linarith
  refine ⟨K,hK,?_⟩
  intro q _ χ t
  have hq : (0:ℝ)≤q := Nat.cast_nonneg q
  have ht : 0≤|t| := abs_nonneg t
  have hp : 0≤((q:ℝ)+2)*(|t|+2) := by positivity
  have he : 0≤2*ε := by positivity
  constructor
  · intro s hs hn
    have hb := h₀ _ (characterMean χ) (2*q+3) (positiveCoefficients_zero _)
      (positiveCoefficients_norm_le (fun n => χ.norm_le_one _)) (characterMean_norm_le χ)
      (by positivity) (fun t ht => discrepancy_characterMean_bound χ ht) s (by linarith)
    change ‖characterRegular χ s‖≤_ at hb
    have hb' : (2*q+3+1)*(‖s‖+2)≤8*(((q:ℝ)+2)*(|t|+2)) := by
      nlinarith [mul_nonneg (show (0:ℝ)≤2*q+4 by positivity) (sub_nonneg.mpr hn)]
    calc
      _ ≤ K₀*((2*q+3+1)*(‖s‖+2))^(2*ε) := hb
      _ ≤ K₀*(8*(((q:ℝ)+2)*(|t|+2)))^(2*ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hb' he) hK₀.le
      _ = (K₀*8^(2*ε))*(((q:ℝ)+2)*(|t|+2))^(2*ε) := by rw [Real.mul_rpow (by norm_num) hp]; ring
      _ ≤ _ := by gcongr; dsimp [K]; linarith
  · intro hχ s hs hn
    have hb := h₁ q χ hχ s (by linarith)
    have hb' : (q+2)*(‖s‖+2)≤4*(((q:ℝ)+2)*(|t|+2)) := by
      nlinarith [mul_nonneg (show (0:ℝ)≤q+2 by positivity) (sub_nonneg.mpr hn)]
    calc
      _ ≤ K₁*((q+2)*(‖s‖+2))^(2*ε) := hb
      _ ≤ K₁*(4*(((q:ℝ)+2)*(|t|+2)))^(2*ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hb' he) hK₁.le
      _ = (K₁*4^(2*ε))*(((q:ℝ)+2)*(|t|+2))^(2*ε) := by rw [Real.mul_rpow (by norm_num) hp]; ring
      _ ≤ _ := by gcongr; dsimp [K]; linarith

lemma line_growth_lipschitz {f : ℂ → ℂ} {t D : ℝ} (hf : Differentiable ℂ f)
    (hb : ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) → ‖deriv f s‖≤D)
    {z w : ℂ} (hz : 1 ≤ z.re) (hw : 1 ≤ w.re)
    (hzn : ‖z‖+2≤4*(|t|+2)) (hwn : ‖w‖+2≤4*(|t|+2)) :
    ‖f z-f w‖≤D*‖z-w‖ := by
  let S := {s : ℂ | 1 ≤ s.re} ∩ Metric.closedBall 0 (4*(|t|+2)-2)
  have hS : Convex ℝ S := (convex_halfSpace_re_ge 1).inter (convex_closedBall 0 _)
  apply Convex.norm_image_sub_le_of_norm_deriv_le (s:=S) (fun z _ => hf z) ?_ hS
      ⟨hw,by simp [Metric.mem_closedBall,dist_zero_right]; linarith⟩
      ⟨hz,by simp [Metric.mem_closedBall,dist_zero_right]; linarith⟩
  intro s hs
  exact hb s hs.1 (by have := hs.2; simp only [Metric.mem_closedBall,dist_zero_right] at this; linarith)

end
lemma three_four_one_lower {a D E : ℝ} (ha : 0≤a) (hD : 1≤D) (hE : 1≤E)
    (h : ∀ δ : ℝ,0<δ → δ≤1 → 1≤(2*D/δ)^3*(a+D*δ)^4*E) :
    1/(256*D^6*E)≤a := by
  have hD0 : 0<D := by linarith
  have hE0 : 0<E := by linarith
  let δ := 1/(256*D^7*E)
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδ1 : δ≤1 := by
    have hp : (1:ℝ)≤D^7 := one_le_pow₀ hD
    have hp' : (1:ℝ)≤D^7*E := one_le_mul_of_one_le_of_one_le hp hE
    dsimp [δ]
    apply (div_le_one (by positivity)).mpr
    linarith
  have he : 1/(256*D^6*E)=D*δ := by dsimp [δ]; field_simp
  rw [he]
  by_contra! han
  have hb : a+D*δ≤2*D*δ := by linarith
  have hh := h δ hδ hδ1
  have hu : (2*D/δ)^3*(a+D*δ)^4*E≤(2*D/δ)^3*(2*D*δ)^4*E := by gcongr
  have hv : (2*D/δ)^3*(2*D*δ)^4*E=1/2 := by dsimp [δ]; field_simp; norm_num
  rw [hv] at hu
  linarith

open Complex Filter Topology Finset
lemma line_sample_norm {δ t u : ℝ} (hδ : 0≤δ) (hδ1 : δ≤1) (hu : |u|≤2*|t|) :
    ‖(1:ℂ)+δ+I*u‖+2≤4*(|t|+2) := by
  have h := Complex.norm_le_abs_re_add_abs_im ((1:ℂ)+δ+I*u)
  simp only [Complex.add_re,Complex.one_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
    Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_self,add_zero,Complex.add_im,
    Complex.one_im,Complex.mul_im,one_mul,zero_add] at h
  rw [abs_of_nonneg (by linarith : (0:ℝ)≤1+δ)] at h
  linarith [abs_nonneg t]

lemma LFunction_norm_le_regular_add_pole {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) :
    ‖χ.LFunction s‖≤‖characterRegular χ s‖+1/‖s-1‖ := by
  rw [LFunction_regularSeries_characterMean χ hs]
  apply (norm_add_le _ _).trans
  dsimp [characterRegular]
  apply add_le_add le_rfl
  rw [norm_div]
  exact div_le_div_of_nonneg_right (characterMean_norm_le χ) (norm_nonneg _)

lemma characterRegular_eq_nonprincipal {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) {s : ℂ} (hs : 0<s.re) : characterRegular χ s=χ.LFunction s := by
  rw [characterRegular,characterMean_eq_zero hχ,regularSeries_character_eq hχ hs]

lemma nonprincipal_line_lower_aux {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) {t c K P : ℝ} (hc : 0<c) (_hc1 : c≤1) (hK : 1≤K) (hP : 1≤P)
    (hr : ∀ ψ : DirichletCharacter ℂ q,∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
      ‖characterRegular ψ s‖≤K*P)
    (hd : ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) → ‖deriv χ.LFunction s‖≤K*P)
    (hsi : χ^2=1 → c/P≤‖χ.LFunction 1‖) :
    min (c/2) (1/(256*K^6*(K+K/c)))/P^8≤‖χ.LFunction (1+I*t)‖ := by
  have hK0 : 0<K := by linarith
  have hP0 : 0<P := by linarith
  have hhc : 0<K+K/c := by positivity
  have hKP : 1≤K*P := one_le_mul_of_one_le_of_one_le hK hP
  have hn0 : ‖(1:ℂ)+I*t‖+2≤4*(|t|+2) := by
    simpa using line_sample_norm (t:=t) (u:=t) (δ:=0) le_rfl zero_le_one (by linarith [abs_nonneg t])
  have hn1 : ‖(1:ℂ)‖+2≤4*(|t|+2) := by norm_num; linarith [abs_nonneg t]
  by_cases hsmall : χ^2=1 ∧ |t|≤c/(2*K*P^2)
  · have hdiff := line_growth_lipschitz (DirichletCharacter.differentiable_LFunction hχ) hd
      (z:=1) (w:=1+I*t) (by simp) (by simp) hn1 hn0
    have hnorm : ‖(1:ℂ)-(1+I*t)‖=|t| := by
      rw [show (1:ℂ)-(1+I*t)=-(I*t) by ring,norm_neg,norm_mul,Complex.norm_I,one_mul,
        Complex.norm_real,Real.norm_eq_abs]
    rw [hnorm] at hdiff
    have hdiff' : ‖χ.LFunction 1-χ.LFunction (1+I*t)‖≤c/(2*P) := by
      calc
        _ ≤ K*P*|t| := hdiff
        _ ≤ K*P*(c/(2*K*P^2)) := mul_le_mul_of_nonneg_left hsmall.2 (by positivity)
        _ = _ := by field_simp
    have hval : c/(2*P)≤‖χ.LFunction (1+I*t)‖ := by
      have htri := norm_add_le (χ.LFunction 1-χ.LFunction (1+I*t)) (χ.LFunction (1+I*t))
      rw [sub_add_cancel] at htri
      have he : c/P=2*(c/(2*P)) := by ring
      have hsi' := hsi hsmall.1
      rw [he] at hsi'
      linarith
    have hP8 : P≤P^8 := by simpa using pow_le_pow_right₀ hP (show (1:ℕ)≤8 by norm_num)
    calc
      _ ≤ (c/2)/P^8 := div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
      _ ≤ (c/2)/P := div_le_div_of_nonneg_left (by positivity) hP0 hP8
      _ = c/(2*P) := by ring
      _ ≤ _ := hval
  · have hLo : 1/(256*(K*P)^6*((K+K/c)*P^2))≤‖χ.LFunction (1+I*t)‖ := by
      apply three_four_one_lower (norm_nonneg _) hKP
        (one_le_mul_of_one_le_of_one_le (by linarith [div_pos hK0 hc]) (one_le_pow₀ hP))
      intro δ hδ hδ1
      have hrδ : ((1:ℂ)+δ+I*t).re=1+δ := by simp
      have hrδ2 : ((1:ℂ)+δ+2*I*t).re=1+δ := by simp
      have hnδ := line_sample_norm hδ.le hδ1 (t:=t) (u:=t) (by linarith [abs_nonneg t])
      have hnδ2 : ‖(1:ℂ)+δ+2*I*t‖+2≤4*(|t|+2) := by
        simpa only [show I*((2*t:ℝ):ℂ)=2*I*t by push_cast; ring] using
          line_sample_norm hδ.le hδ1 (t:=t) (u:=2*t) (by rw [abs_mul]; norm_num)
      have hL0 : ‖DirichletCharacter.LFunctionTrivChar q (1+δ)‖≤2*(K*P)/δ := by
        have hn : ‖(1:ℂ)+δ‖+2≤4*(|t|+2) := by
          simpa using line_sample_norm hδ.le hδ1 (t:=t) (u:=0) (by simp)
        have hreg := hr (1:DirichletCharacter ℂ q) (1+δ) (by simp; linarith) hn
        have hp := LFunction_norm_le_regular_add_pole (1:DirichletCharacter ℂ q)
          (s:=1+δ) (by simp; linarith)
        have hden : ‖(1:ℂ)+δ-1‖=δ := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
        rw [hden] at hp
        change ‖DirichletCharacter.LFunction (1:DirichletCharacter ℂ q) (1+δ)‖≤_
        apply (hp.trans (add_le_add hreg le_rfl)).trans
        apply (le_div_iff₀ hδ).mpr
        have hd : (K*P)*δ≤K*P := mul_le_of_le_one_right (by positivity) hδ1
        field_simp
        nlinarith
      have hLχ : ‖χ.LFunction (1+δ+I*t)‖≤‖χ.LFunction (1+I*t)‖+(K*P)*δ := by
        have hl := line_growth_lipschitz (DirichletCharacter.differentiable_LFunction hχ) hd
          (z:=1+δ+I*t) (w:=1+I*t) (by simp; linarith) (by simp) hnδ hn0
        have hden : ‖(1:ℂ)+δ+I*t-(1+I*t)‖=δ := by
          rw [show (1:ℂ)+δ+I*t-(1+I*t)=(δ:ℂ) by ring,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
        rw [hden] at hl
        have ht := norm_add_le (χ.LFunction (1+δ+I*t)-χ.LFunction (1+I*t)) (χ.LFunction (1+I*t))
        rw [sub_add_cancel] at ht
        linarith
      have hL2 : ‖(χ^2).LFunction (1+δ+2*I*t)‖≤(K+K/c)*P^2 := by
        by_cases hχ2 : χ^2=1
        · have ht : c/(2*K*P^2)< |t| := lt_of_not_ge (fun ht => hsmall ⟨hχ2,ht⟩)
          have ht0 : 0< |t| := (by positivity : 0<c/(2*K*P^2)).trans ht
          have hp := LFunction_norm_le_regular_add_pole (χ^2) (s:=1+δ+2*I*t) (by rw [hrδ2]; linarith)
          have hn : 2*|t|≤‖(1:ℂ)+δ+2*I*t-1‖ := by
            have h := Complex.abs_im_le_norm ((1:ℂ)+δ+2*I*t-1)
            simpa [abs_mul] using h
          have hfrac : 1/‖(1:ℂ)+δ+2*I*t-1‖≤K*P^2/c := by
            apply (div_le_div_of_nonneg_left zero_le_one (by positivity : 0<2*|t|) hn).trans
            apply (div_le_iff₀ (by positivity : 0<2*|t|)).mpr
            have ht' := (div_lt_iff₀ (by positivity : 0<2*K*P^2)).mp ht
            rw [div_mul_eq_mul_div]
            apply (le_div_iff₀ hc).mpr
            nlinarith
          have hreg := hr (χ^2) (1+δ+2*I*t) (by rw [hrδ2]; linarith) hnδ2
          have hP2 : P≤P^2 := by nlinarith
          have h := hp.trans (add_le_add hreg hfrac)
          apply h.trans
          calc
            K*P+K*P^2/c ≤ K*P^2+K*P^2/c := add_le_add (mul_le_mul_of_nonneg_left hP2 hK0.le) le_rfl
            _ = _ := by ring
        · have hreg := hr (χ^2) (1+δ+2*I*t) (by rw [hrδ2]; linarith) hnδ2
          rw [characterRegular_eq_nonprincipal hχ2 (by rw [hrδ2]; linarith)] at hreg
          have hP2 : P≤P^2 := by nlinarith
          exact hreg.trans (by nlinarith [mul_le_mul_of_nonneg_left hP2 hK0.le,div_pos hK0 hc])
      have hprod := χ.norm_LFunction_product_ge_one hδ t
      simp only [norm_mul,norm_pow] at hprod
      exact hprod.trans (by gcongr)
    calc
      _ ≤ (1/(256*K^6*(K+K/c)))/P^8 := div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = 1/(256*(K*P)^6*((K+K/c)*P^2)) := by field_simp
      _ ≤ _ := hLo

lemma nonprincipal_line_lower {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c : ℝ,0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → ∀ t : ℝ,
        c*(((q:ℝ)+2)*(|t|+2))^(-ε)≤‖χ.LFunction (1+I*t)‖ := by
  obtain ⟨K,hK,hgrowth⟩ := character_line_bounds (by linarith : 0<ε/16) (by linarith : ε/16≤1/2)
  obtain ⟨c₀,hc₀,hsiegel⟩ := quadratic_siegel (by linarith : 0<ε/8) (by linarith : ε/8≤1)
  let c := min c₀ 1
  have hc : 0<c := lt_min hc₀ zero_lt_one
  have hc1 : c≤1 := min_le_right _ _
  let d := min (c/2) (1/(256*K^6*(K+K/c)))
  have hK0 : 0<K := by linarith
  have hd : 0<d := by dsimp [d]; positivity
  refine ⟨d,hd,?_⟩
  intro q _ χ hχp hχ t
  let X : ℝ := ((q:ℝ)+2)*(|t|+2)
  let P : ℝ := X^(ε/8)
  have hX : 1≤X := by dsimp [X]; nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
  have hX0 : 0<X := by linarith
  have hP : 1≤P := Real.one_le_rpow hX (by positivity)
  have he : 2*(ε/16)=ε/8 := by ring
  have hsi : χ^2=1 → c/P≤‖χ.LFunction 1‖ := by
    intro hχ2
    have hq : (q:ℝ)+1≤X := by dsimp [X]; nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
    calc
      c/P = c*X^(-(ε/8)) := by rw [Real.rpow_neg hX0.le]; rfl
      _ ≤ c₀*((q:ℝ)+1)^(-(ε/8)) := by
        apply mul_le_mul (min_le_left _ _) (Real.rpow_le_rpow_of_nonpos (by positivity) hq (by linarith))
          (Real.rpow_nonneg hX0.le _) hc₀.le
      _ ≤ _ := hsiegel q χ hχp hχ hχ2
  have hh := nonprincipal_line_lower_aux hχ hc hc1 hK hP
    (fun ψ s hs hn => by simpa only [he] using (hgrowth q ψ t).1 s hs hn)
    (fun s hs hn => by simpa only [he] using (hgrowth q χ t).2 hχ s hs hn) hsi
  have hP8 : P^8=X^ε := by
    dsimp [P]
    rw [←Real.rpow_mul_natCast hX0.le]
    congr 1
    norm_num
  change d/P^8≤_ at hh
  rw [hP8] at hh
  change d*X^(-ε)≤_
  simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hh

lemma character_interior_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {t K P δ : ℝ} (hK : 1≤K) (hP : 1≤P) (hδ : 0<δ) (hδ1 : δ≤1)
    (hr : ∀ ψ : DirichletCharacter ℂ q,∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
      ‖characterRegular ψ s‖≤K*P) :
    δ/(2*K*P)≤‖χ.LFunction (1+δ+I*t)‖ := by
  have hKP : 1≤K*P := one_le_mul_of_one_le_of_one_le hK hP
  have hKP0 : 0<K*P := by linarith
  have hb (ψ : DirichletCharacter ℂ q) (u : ℝ) (hu : |u|≤2*|t|) :
      ‖ψ.LFunction (1+δ+I*u)‖≤2*K*P/δ := by
    have hp := LFunction_norm_le_regular_add_pole ψ (s:=1+δ+I*u) (by simp; linarith)
    have hn : δ≤‖(1:ℂ)+δ+I*u-1‖ := by
      simpa using Complex.re_le_norm ((1:ℂ)+δ+I*u-1)
    have hreg := hr ψ (1+δ+I*u) (by simp; linarith) (line_sample_norm hδ.le hδ1 hu)
    have hfrac := div_le_div_of_nonneg_left zero_le_one hδ hn
    apply (hp.trans (add_le_add hreg hfrac)).trans
    apply (le_div_iff₀ hδ).mpr
    have hd := mul_le_of_le_one_right hKP0.le hδ1
    have he : (K*P+1/δ)*δ=K*P*δ+1 := by field_simp
    rw [he]
    nlinarith
  have h0 : ‖DirichletCharacter.LFunctionTrivChar q (1+δ)‖≤2*K*P/δ := by
    simpa using hb (1:DirichletCharacter ℂ q) 0 (by simp)
  have h2 : ‖(χ^2).LFunction (1+δ+2*I*t)‖≤2*K*P/δ := by
    simpa only [show I*((2*t:ℝ):ℂ)=2*I*t by push_cast; ring] using hb (χ^2) (2*t) (by rw [abs_mul]; norm_num)
  have hh := χ.norm_LFunction_product_ge_one hδ t
  simp only [norm_mul,norm_pow] at hh
  have hu : 1≤(2*K*P/δ)^3*‖χ.LFunction (1+δ+I*t)‖^4*(2*K*P/δ) := hh.trans (by gcongr)
  have hp : (1:ℝ)^4≤((2*K*P/δ)*‖χ.LFunction (1+δ+I*t)‖)^4 := by convert hu using 1 <;> ring
  have hv := le_of_pow_le_pow_left₀ (by norm_num : (4:ℕ)≠0) (by positivity) hp
  apply (div_le_iff₀ (by positivity : 0<2*K*P)).mpr
  have he : (2*K*P/δ)*‖χ.LFunction (1+δ+I*t)‖=(‖χ.LFunction (1+δ+I*t)‖*(2*K*P))/δ := by ring
  rw [he] at hv
  simpa only [one_mul] using (le_div_iff₀ hδ).mp hv

lemma nonprincipal_strip_lower_aux {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) {t c K P δ : ℝ} (hc : 0<c) (hK : 1≤K) (hP : 1≤P)
    (hδ : 0≤δ) (hδ1 : δ≤1)
    (hr : ∀ ψ : DirichletCharacter ℂ q,∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
      ‖characterRegular ψ s‖≤K*P)
    (hd : ∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) → ‖deriv χ.LFunction s‖≤K*P)
    (hl : c/P≤‖χ.LFunction (1+I*t)‖) :
    (c/(4*K^2))/P^3≤‖χ.LFunction (1+δ+I*t)‖ := by
  have hK0 : 0<K := by linarith
  have hP0 : 0<P := by linarith
  by_cases hnear : δ≤c/(2*K*P^2)
  · have hn0 : ‖(1:ℂ)+I*t‖+2≤4*(|t|+2) := by
      simpa using line_sample_norm (t:=t) (u:=t) (δ:=0) le_rfl zero_le_one (by linarith [abs_nonneg t])
    have hnδ := line_sample_norm hδ hδ1 (t:=t) (u:=t) (by linarith [abs_nonneg t])
    have hdif := line_growth_lipschitz (DirichletCharacter.differentiable_LFunction hχ) hd
      (z:=1+I*t) (w:=1+δ+I*t) (by simp) (by simp; linarith) hn0 hnδ
    have hnorm : ‖(1:ℂ)+I*t-(1+δ+I*t)‖=δ := by
      rw [show (1:ℂ)+I*t-(1+δ+I*t)=-(δ:ℂ) by ring,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hδ]
    rw [hnorm] at hdif
    have hdb : ‖χ.LFunction (1+I*t)-χ.LFunction (1+δ+I*t)‖≤c/(2*P) := by
      apply hdif.trans
      calc
        K*P*δ ≤ K*P*(c/(2*K*P^2)) := mul_le_mul_of_nonneg_left hnear (by positivity)
        _ = _ := by field_simp
    have htri := norm_add_le (χ.LFunction (1+I*t)-χ.LFunction (1+δ+I*t)) (χ.LFunction (1+δ+I*t))
    rw [sub_add_cancel] at htri
    have hva : c/(2*P)≤‖χ.LFunction (1+δ+I*t)‖ := by
      have he : c/P=2*(c/(2*P)) := by ring
      rw [he] at hl
      linarith
    apply le_trans ?_ hva
    rw [div_div]
    apply div_le_div_of_nonneg_left hc.le (by positivity)
    have hP3 : P≤P^3 := by simpa using pow_le_pow_right₀ hP (show (1:ℕ)≤3 by norm_num)
    have hK2 : 1≤K^2 := one_le_pow₀ hK
    nlinarith [mul_le_mul_of_nonneg_left hP3 (show (0:ℝ)≤4*K^2 by positivity)]
  · have hδ0 : 0<δ := (by positivity : 0<c/(2*K*P^2)).trans (lt_of_not_ge hnear)
    apply le_trans ?_ (character_interior_lower χ hK hP hδ0 hδ1 hr)
    calc
      (c/(4*K^2))/P^3 = (c/(2*K*P^2))/(2*K*P) := by field_simp; norm_num
      _ ≤ δ/(2*K*P) := div_le_div_of_nonneg_right (le_of_not_ge hnear) (by positivity)

lemma nonprincipal_strip_lower {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c : ℝ,0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → ∀ σ t : ℝ, 1≤σ → σ≤2 →
        c*(((q:ℝ)+2)*(|t|+2))^(-ε)≤‖χ.LFunction (σ+I*t)‖ := by
  obtain ⟨K,hK,hg⟩ := character_line_bounds (by linarith : 0<ε/6) (by linarith : ε/6≤1/2)
  obtain ⟨c,hc,hl⟩ := nonprincipal_line_lower (by linarith : 0<ε/3) (by linarith : ε/3≤1)
  have hK0 : 0<K := by linarith
  refine ⟨c/(4*K^2),by positivity,?_⟩
  intro q _ χ hχp hχ σ t hσ hσ2
  let X : ℝ := ((q:ℝ)+2)*(|t|+2)
  let P : ℝ := X^(ε/3)
  have hX : 1≤X := by dsimp [X]; nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
  have hX0 : 0<X := by linarith
  have hP : 1≤P := Real.one_le_rpow hX (by positivity)
  have he : 2*(ε/6)=ε/3 := by ring
  have hl' : c/P≤‖χ.LFunction (1+I*t)‖ := by
    have hh := hl q χ hχp hχ t
    change c*X^(-(ε/3))≤_ at hh
    change c/X^(ε/3)≤_
    simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hh
  have hb := nonprincipal_strip_lower_aux hχ hc hK hP (δ:=σ-1) (by linarith) (by linarith)
    (fun ψ s hs hn => by simpa only [he] using (hg q ψ t).1 s hs hn)
    (fun s hs hn => by simpa only [he] using (hg q χ t).2 hχ s hs hn) hl'
  have hP3 : P^3=X^ε := by dsimp [P]; rw [←Real.rpow_mul_natCast hX0.le]; congr 1; norm_num
  rw [hP3] at hb
  have hs : (1:ℂ)+((σ-1:ℝ):ℂ)+I*t=(σ:ℂ)+I*t := by push_cast; ring
  rw [hs] at hb
  change (c/(4*K^2))*X^(-ε)≤_
  simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hb

end LargePrimeGaps
end OAI

-- Source module: PrincipalGrowth
namespace OAI
namespace LargePrimeGaps
open Complex Filter Topology
lemma zetaRegular_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ s : ℂ, 1-ε/2 ≤ s.re →
      ‖zetaRegular s‖ ≤ K*(‖s‖+2)^(2*ε) ∧
      ‖deriv zetaRegular s‖ ≤ K*(‖s‖+2)^(2*ε) := by
  obtain ⟨K₀,hK₀,h₀⟩ := regularSeries_norm_small_power hε hε1
  obtain ⟨K₁,hK₁,h₁⟩ := regularSeries_deriv_norm_small_power hε hε1
  let K := 1+(K₀+K₁)*2^(2*ε)
  have hK : 1 ≤ K := by dsimp [K]; linarith [show 0 < (K₀+K₁)*2^(2*ε) by positivity]
  refine ⟨K,hK,?_⟩
  intro s hs
  have hb₀ := h₀ _ 1 1 (positiveCoefficients_zero _) (positiveCoefficients_norm_le (by simp))
    (by simp) zero_le_one (fun t ht => discrepancy_constant_bound ht) s (by linarith)
  have hb₁ := h₁ _ 1 1 (positiveCoefficients_zero _) (positiveCoefficients_norm_le (by simp))
    (by simp) zero_le_one (fun t ht => discrepancy_constant_bound ht) s hs
  change ‖zetaRegular s‖ ≤ _ at hb₀
  change ‖deriv zetaRegular s‖ ≤ _ at hb₁
  norm_num only [one_add_one_eq_two] at hb₀ hb₁
  rw [Real.mul_rpow (by norm_num) (by positivity)] at hb₀ hb₁
  constructor
  · apply hb₀.trans
    have hc : K₀*2^(2*ε) ≤ K := by dsimp [K]; nlinarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (2*ε)]
    calc
      _ = (K₀*2^(2*ε))*(‖s‖+2)^(2*ε) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
  · apply hb₁.trans
    have hc : K₁*2^(2*ε) ≤ K := by dsimp [K]; nlinarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (2*ε)]
    calc
      _ = (K₁*2^(2*ε))*(‖s‖+2)^(2*ε) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

lemma zeta_deriv_eq_regular {s : ℂ} (hs : 0 < s.re) (hs1 : s≠1) :
    deriv riemannZeta s = deriv zetaRegular s-1/(s-1)^2 := by
  have he : riemannZeta =ᶠ[𝓝 s] fun z => zetaRegular z+1/(z-1) := by
    filter_upwards [(continuous_re.tendsto s).eventually (lt_mem_nhds hs),
      eventually_ne_nhds hs1] with z hz hz1
    rw [zetaRegular_eq hz hz1,sub_add_cancel]
  rw [he.deriv_eq]
  have hd := (hasDerivAt_const s (1:ℂ)).div ((hasDerivAt_id s).sub_const 1) (sub_ne_zero.mpr hs1)
  have hh := (zetaRegular_differentiableAt hs).hasDerivAt.add hd
  simpa only [Pi.add_def, Pi.div_def, id_eq, zero_mul, one_mul, zero_sub, neg_div, sub_eq_add_neg, zero_add] using hh.deriv

lemma horizontal_growth_lipschitz {f : ℂ → ℂ} {t D : ℝ}
    (hf : ∀ s : ℂ, 1 ≤ s.re → s.im=t → DifferentiableAt ℂ f s)
    (hb : ∀ s : ℂ, 1 ≤ s.re → s.im=t → ‖s‖+2 ≤ 4*(|t|+2) → ‖deriv f s‖ ≤ D)
    {z w : ℂ} (hz : 1 ≤ z.re) (hw : 1 ≤ w.re) (hzt : z.im=t) (hwt : w.im=t)
    (hzn : ‖z‖+2 ≤ 4*(|t|+2)) (hwn : ‖w‖+2 ≤ 4*(|t|+2)) :
    ‖f z-f w‖ ≤ D*‖z-w‖ := by
  let S := ({s : ℂ | 1 ≤ s.re} ∩ {s : ℂ | s.im=t}) ∩ Metric.closedBall 0 (4*(|t|+2)-2)
  have hi : Convex ℝ {s : ℂ | s.im=t} := convex_hyperplane (.mk Complex.add_im Complex.smul_im) t
  have hS : Convex ℝ S := ((convex_halfSpace_re_ge 1).inter hi).inter (convex_closedBall 0 _)
  apply Convex.norm_image_sub_le_of_norm_deriv_le (s:=S) (fun z hz => hf z hz.1.1 hz.1.2) ?_ hS
    ⟨⟨hw,hwt⟩,by simp [Metric.mem_closedBall,dist_zero_right]; linarith⟩
    ⟨⟨hz,hzt⟩,by simp [Metric.mem_closedBall,dist_zero_right]; linarith⟩
  intro s hs
  exact hb s hs.1.1 hs.1.2 (by have := hs.2; simp only [Metric.mem_closedBall,dist_zero_right] at this; linarith)

lemma zeta_high_line_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ t : ℝ, 1 ≤ |t| →
      (∀ ψ : DirichletCharacter ℂ 1, ∀ s : ℂ, 1 ≤ s.re → ‖s‖+2 ≤ 4*(|t|+2) →
        ‖characterRegular ψ s‖ ≤ K*(|t|+2)^(2*ε)) ∧
      (∀ s : ℂ, 1 ≤ s.re → s.im=t → ‖s‖+2 ≤ 4*(|t|+2) →
        ‖deriv riemannZeta s‖ ≤ K*(|t|+2)^(2*ε)) := by
  obtain ⟨K₀,hK₀,h₀⟩ := character_line_bounds hε hε1
  obtain ⟨K₁,hK₁,h₁⟩ := zetaRegular_bounds hε hε1
  let K := K₀*3^(2*ε)+K₁*4^(2*ε)+1
  have hK₀' : 0 < K₀ := by linarith
  have hK₁' : 0 < K₁ := by linarith
  have hK : 1 ≤ K := by dsimp [K]; linarith [show 0 < K₀*3^(2*ε) by positivity, show 0 < K₁*4^(2*ε) by positivity]
  refine ⟨K,hK,?_⟩
  intro t ht
  have hP : 1 ≤ (|t|+2)^(2*ε) := Real.one_le_rpow (by linarith [abs_nonneg t]) (by positivity)
  constructor
  · intro ψ s hs hn
    have hb := (h₀ 1 ψ t).1 s hs hn
    norm_num only [Nat.cast_one,show (1:ℝ)+2=3 by norm_num] at hb
    rw [Real.mul_rpow (by norm_num) (by positivity)] at hb
    apply hb.trans
    have hc : K₀*3^(2*ε) ≤ K := by dsimp [K]; linarith [show 0 < K₁*4^(2*ε) by positivity]
    convert mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (|t|+2)^(2*ε)) using 1
    ring
  · intro s hs him hn
    have hs1 : s≠1 := by intro h; simp [h] at him; rw [←him] at ht; norm_num at ht
    have hd := (h₁ s (by linarith)).2
    have hden : 1 ≤ ‖s-1‖ := by
      have h := Complex.abs_im_le_norm (s-1)
      simp only [Complex.sub_im,Complex.one_im,sub_zero,him] at h
      exact ht.trans h
    have hfrac : ‖(1:ℂ)/(s-1)^2‖ ≤ 1 := by
      simp only [norm_div,norm_one,norm_pow]
      exact div_le_one_of_le₀ (one_le_pow₀ hden) (by positivity)
    rw [zeta_deriv_eq_regular (by linarith) hs1]
    apply (norm_sub_le _ _).trans
    have hnorm := Real.rpow_le_rpow (by positivity : 0 ≤ ‖s‖+2) hn (by positivity : 0 ≤ 2*ε)
    rw [Real.mul_rpow (by norm_num) (by positivity)] at hnorm
    have hc : K₁*4^(2*ε)+1 ≤ K := by dsimp [K]; linarith [show 0 < K₀*3^(2*ε) by positivity]
    calc
      _ ≤ K₁*(‖s‖+2)^(2*ε)+1 := add_le_add hd hfrac
      _ ≤ (K₁*4^(2*ε))*(|t|+2)^(2*ε)+(|t|+2)^(2*ε) := by nlinarith
      _ = (K₁*4^(2*ε)+1)*(|t|+2)^(2*ε) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

lemma zeta_high_line_lower_aux {t K P : ℝ} (ht : 1 ≤ |t|) (hK : 1 ≤ K) (hP : 1 ≤ P)
    (hr : ∀ ψ : DirichletCharacter ℂ 1, ∀ s : ℂ, 1 ≤ s.re → ‖s‖+2 ≤ 4*(|t|+2) →
      ‖characterRegular ψ s‖ ≤ K*P)
    (hd : ∀ s : ℂ, 1 ≤ s.re → s.im=t → ‖s‖+2 ≤ 4*(|t|+2) → ‖deriv riemannZeta s‖ ≤ K*P) :
    (1/(512*K^7))/P^7 ≤ ‖riemannZeta (1+I*t)‖ := by
  have hK0 : 0 < K := by linarith
  have hP0 : 0 < P := by linarith
  have hKP : 1 ≤ K*P := one_le_mul_of_one_le_of_one_le hK hP
  have hh : 1/(256*(K*P)^6*(2*K*P)) ≤ ‖riemannZeta (1+I*t)‖ := by
    apply three_four_one_lower (norm_nonneg _) hKP (by linarith)
    intro δ hδ hδ1
    have hn0 : ‖(1:ℂ)+I*t‖+2 ≤ 4*(|t|+2) := by
      simpa using line_sample_norm (t:=t) (u:=t) (δ:=0) le_rfl zero_le_one (by linarith [abs_nonneg t])
    have hnδ := line_sample_norm hδ.le hδ1 (t:=t) (u:=t) (by linarith [abs_nonneg t])
    have hL0 : ‖DirichletCharacter.LFunctionTrivChar 1 (1+δ)‖ ≤ 2*(K*P)/δ := by
      have hn : ‖(1:ℂ)+δ‖+2 ≤ 4*(|t|+2) := by
        simpa using line_sample_norm hδ.le hδ1 (t:=t) (u:=0) (by simp)
      have hreg := hr 1 (1+δ) (by simp; linarith) hn
      have hp := LFunction_norm_le_regular_add_pole (1:DirichletCharacter ℂ 1)
        (s:=1+δ) (by simp; linarith)
      have hden : ‖(1:ℂ)+δ-1‖=δ := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
      rw [hden] at hp
      change ‖DirichletCharacter.LFunction (1:DirichletCharacter ℂ 1) (1+δ)‖ ≤ _
      apply (hp.trans (add_le_add hreg le_rfl)).trans
      apply (le_div_iff₀ hδ).mpr
      have hd := mul_le_of_le_one_right (by positivity : 0 ≤ K*P) hδ1
      field_simp
      nlinarith
    have hL1 : ‖riemannZeta (1+δ+I*t)‖ ≤ ‖riemannZeta (1+I*t)‖+(K*P)*δ := by
      have hf (s : ℂ) (_hs : 1 ≤ s.re) (him : s.im=t) : DifferentiableAt ℂ riemannZeta s := by
        apply differentiableAt_riemannZeta
        intro hs
        simp [hs] at him
        rw [←him] at ht
        norm_num at ht
      have hl := horizontal_growth_lipschitz hf hd (z:=1+δ+I*t) (w:=1+I*t)
        (by simp; linarith) (by simp) (by simp) (by simp) hnδ hn0
      have hden : ‖(1:ℂ)+δ+I*t-(1+I*t)‖=δ := by
        rw [show (1:ℂ)+δ+I*t-(1+I*t)=(δ:ℂ) by ring,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
      rw [hden] at hl
      have hh := norm_add_le (riemannZeta (1+δ+I*t)-riemannZeta (1+I*t)) (riemannZeta (1+I*t))
      rw [sub_add_cancel] at hh
      linarith
    have hL2 : ‖riemannZeta (1+δ+2*I*t)‖ ≤ 2*K*P := by
      have hn : ‖(1:ℂ)+δ+2*I*t‖+2 ≤ 4*(|t|+2) := by
        simpa only [show I*((2*t:ℝ):ℂ)=2*I*t by push_cast; ring] using
          line_sample_norm hδ.le hδ1 (t:=t) (u:=2*t) (by rw [abs_mul]; norm_num)
      have hp := LFunction_norm_le_regular_add_pole (1:DirichletCharacter ℂ 1)
        (s:=1+δ+2*I*t) (by simp; linarith)
      rw [DirichletCharacter.LFunction_modOne_eq] at hp
      have hreg := hr 1 (1+δ+2*I*t) (by simp; linarith) hn
      have hden : 1 ≤ ‖(1:ℂ)+δ+2*I*t-1‖ := by
        have hb := Complex.abs_im_le_norm ((1:ℂ)+δ+2*I*t-1)
        simp [abs_mul] at hb
        linarith
      have hfrac : 1/‖(1:ℂ)+δ+2*I*t-1‖ ≤ 1 := div_le_one_of_le₀ hden (norm_nonneg _)
      linarith
    have hprod := (1:DirichletCharacter ℂ 1).norm_LFunction_product_ge_one hδ t
    simp only [one_pow,DirichletCharacter.LFunction_modOne_eq,norm_mul,norm_pow] at hprod
    have hL0' : ‖riemannZeta (1+δ)‖ ≤ 2*(K*P)/δ := by
      simpa only [DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq] using hL0
    exact hprod.trans (by gcongr)
  convert hh using 1
  field_simp
  ring

lemma zeta_high_line_lower {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 1 ≤ |t| →
      c*(|t|+2)^(-ε) ≤ ‖riemannZeta (1+I*t)‖ := by
  obtain ⟨K,hK,hg⟩ := zeta_high_line_bounds (by linarith : 0 < ε/14) (by linarith : ε/14 ≤ 1/2)
  have hK0 : 0 < K := by linarith
  refine ⟨1/(512*K^7),by positivity,?_⟩
  intro t ht
  let P : ℝ := (|t|+2)^(ε/7)
  have hP : 1 ≤ P := Real.one_le_rpow (by linarith [abs_nonneg t]) (by positivity)
  have he : 2*(ε/14)=ε/7 := by ring
  have hh := zeta_high_line_lower_aux ht hK hP
    (fun ψ s hs hn => by simpa only [he] using (hg t ht).1 ψ s hs hn)
    (fun s hs him hn => by simpa only [he] using (hg t ht).2 s hs him hn)
  have hP7 : P^7=(|t|+2)^ε := by
    dsimp [P]
    rw [←Real.rpow_mul_natCast (by positivity : 0 ≤ |t|+2)]
    congr 1
    norm_num
  rw [hP7] at hh
  simpa only [Real.rpow_neg (by positivity : 0 ≤ |t|+2),div_eq_mul_inv] using hh

lemma zeta_high_strip_lower_aux {t c K P δ : ℝ} (ht : 1 ≤ |t|) (hc : 0<c) (hK : 1≤K) (hP : 1≤P)
    (hδ : 0≤δ) (hδ1 : δ≤1)
    (hr : ∀ ψ : DirichletCharacter ℂ 1,∀ s : ℂ,1 ≤ s.re → ‖s‖+2≤4*(|t|+2) →
      ‖characterRegular ψ s‖≤K*P)
    (hd : ∀ s : ℂ,1 ≤ s.re → s.im=t → ‖s‖+2≤4*(|t|+2) → ‖deriv riemannZeta s‖≤K*P)
    (hl : c/P≤‖riemannZeta (1+I*t)‖) :
    (c/(4*K^2))/P^3≤‖riemannZeta (1+δ+I*t)‖ := by
  have hK0 : 0<K := by linarith
  have hP0 : 0<P := by linarith
  by_cases hnear : δ≤c/(2*K*P^2)
  · have hn0 : ‖(1:ℂ)+I*t‖+2≤4*(|t|+2) := by
      simpa using line_sample_norm (t:=t) (u:=t) (δ:=0) le_rfl zero_le_one (by linarith [abs_nonneg t])
    have hnδ := line_sample_norm hδ hδ1 (t:=t) (u:=t) (by linarith [abs_nonneg t])
    have hf (s : ℂ) (_hs : 1 ≤ s.re) (him : s.im=t) : DifferentiableAt ℂ riemannZeta s := by
      apply differentiableAt_riemannZeta
      intro hs
      simp [hs] at him
      rw [←him] at ht
      norm_num at ht
    have hdif := horizontal_growth_lipschitz hf hd
      (z:=1+I*t) (w:=1+δ+I*t) (by simp) (by simp; linarith) (by simp) (by simp) hn0 hnδ
    have hnorm : ‖(1:ℂ)+I*t-(1+δ+I*t)‖=δ := by
      rw [show (1:ℂ)+I*t-(1+δ+I*t)=-(δ:ℂ) by ring,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hδ]
    rw [hnorm] at hdif
    have hdb : ‖riemannZeta (1+I*t)-riemannZeta (1+δ+I*t)‖≤c/(2*P) := by
      apply hdif.trans
      calc
        K*P*δ ≤ K*P*(c/(2*K*P^2)) := mul_le_mul_of_nonneg_left hnear (by positivity)
        _ = _ := by field_simp
    have htri := norm_add_le (riemannZeta (1+I*t)-riemannZeta (1+δ+I*t)) (riemannZeta (1+δ+I*t))
    rw [sub_add_cancel] at htri
    have hva : c/(2*P)≤‖riemannZeta (1+δ+I*t)‖ := by
      have he : c/P=2*(c/(2*P)) := by ring
      rw [he] at hl
      linarith
    apply le_trans ?_ hva
    rw [div_div]
    apply div_le_div_of_nonneg_left hc.le (by positivity)
    have hP3 : P≤P^3 := by simpa using pow_le_pow_right₀ hP (show (1:ℕ)≤3 by norm_num)
    have hK2 : 1≤K^2 := one_le_pow₀ hK
    nlinarith [mul_le_mul_of_nonneg_left hP3 (show (0:ℝ)≤4*K^2 by positivity)]
  · have hδ0 : 0<δ := (by positivity : 0<c/(2*K*P^2)).trans (lt_of_not_ge hnear)
    have hInt := character_interior_lower (1:DirichletCharacter ℂ 1) hK hP hδ0 hδ1 hr
    rw [DirichletCharacter.LFunction_modOne_eq] at hInt
    apply le_trans ?_ hInt
    calc
      (c/(4*K^2))/P^3 = (c/(2*K*P^2))/(2*K*P) := by field_simp; norm_num
      _ ≤ δ/(2*K*P) := div_le_div_of_nonneg_right (le_of_not_ge hnear) (by positivity)

lemma zeta_high_strip_lower {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1) :
    ∃ c : ℝ,0<c ∧ ∀ σ t : ℝ, 1≤σ → σ≤2 → 1 ≤ |t| →
        c*(|t|+2)^(-ε)≤‖riemannZeta (σ+I*t)‖ := by
  obtain ⟨K,hK,hg⟩ := zeta_high_line_bounds (by linarith : 0<ε/6) (by linarith : ε/6≤1/2)
  obtain ⟨c,hc,hl⟩ := zeta_high_line_lower (by linarith : 0<ε/3) (by linarith : ε/3≤1)
  have hK0 : 0<K := by linarith
  refine ⟨c/(4*K^2),by positivity,?_⟩
  intro σ t hσ hσ2 ht
  let X : ℝ := (|t|+2)
  let P : ℝ := X^(ε/3)
  have hX : 1≤X := by dsimp [X]; linarith [abs_nonneg t]
  have hX0 : 0<X := by linarith
  have hP : 1≤P := Real.one_le_rpow hX (by positivity)
  have he : 2*(ε/6)=ε/3 := by ring
  have hl' : c/P≤‖riemannZeta (1+I*t)‖ := by
    have hh := hl t ht
    change c*X^(-(ε/3))≤_ at hh
    change c/X^(ε/3)≤_
    simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hh
  have hb := zeta_high_strip_lower_aux ht hc hK hP (δ:=σ-1) (by linarith) (by linarith)
    (fun ψ s hs hn => by simpa only [he] using (hg t ht).1 ψ s hs hn)
    (fun s hs him hn => by simpa only [he] using (hg t ht).2 s hs him hn) hl'
  have hP3 : P^3=X^ε := by dsimp [P]; rw [←Real.rpow_mul_natCast hX0.le]; congr 1; norm_num
  rw [hP3] at hb
  have hs : (1:ℂ)+((σ-1:ℝ):ℂ)+I*t=(σ:ℂ)+I*t := by push_cast; ring
  rw [hs] at hb
  change (c/(4*K^2))*X^(-ε)≤_
  simpa only [Real.rpow_neg hX0.le,div_eq_mul_inv] using hb

lemma principal_deriv_eq_regular {s : ℂ} (hs : 0 < s.re) :
    deriv (poleRemovedL (1:DirichletCharacter ℂ 1)) s = zetaRegular s+(s-1)*deriv zetaRegular s := by
  have he : poleRemovedL (1:DirichletCharacter ℂ 1) =ᶠ[𝓝 s] (fun z => (z-1)*zetaRegular z+1) := by
    filter_upwards [(continuous_re.tendsto s).eventually (lt_mem_nhds hs)] with z hz
    simpa only [poleRemovedL,ite_true] using poleRemovedZeta_eq hz
  have hh := (((hasDerivAt_id s).sub_const 1).mul (zetaRegular_differentiableAt hs).hasDerivAt).add_const 1
  rw [he.deriv_eq]
  simpa only [id_eq,one_mul,Pi.mul_apply] using hh.deriv

lemma principal_deriv_growth {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℂ, 1-ε/4 ≤ s.re →
      ‖deriv (poleRemovedL (1:DirichletCharacter ℂ 1)) s‖ ≤ K*(‖s‖+2)*(‖s‖+2)^ε := by
  obtain ⟨K,hK,hb⟩ := zetaRegular_bounds (by linarith : 0 < ε/2) (by linarith : ε/2 ≤ 1/2)
  have hK0 : 0 < K := by linarith
  refine ⟨K,hK0,?_⟩
  intro s hs
  obtain ⟨hl,hd⟩ := hb s (by linarith)
  rw [show 2*(ε/2)=ε by ring] at hl hd
  rw [principal_deriv_eq_regular (by linarith)]
  have hn : ‖s-1‖ ≤ ‖s‖+1 := by simpa using norm_sub_le s 1
  calc
    _ ≤ ‖zetaRegular s‖+‖s-1‖*‖deriv zetaRegular s‖ := by
      apply (norm_add_le _ _).trans_eq
      rw [norm_mul]
    _ ≤ K*(‖s‖+2)^ε+(‖s‖+1)*(K*(‖s‖+2)^ε) := by gcongr
    _ = _ := by ring

lemma principal_strip_lower {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 →
      c*(|t|+2)/((|t|+2)^ε) ≤ ‖poleRemovedL (1:DirichletCharacter ℂ 1) (σ+I*t)‖ := by
  obtain ⟨c₀,hc₀,hl⟩ := zeta_high_strip_lower hε hε1
  let F := poleRemovedL (1:DirichletCharacter ℂ 1)
  let S : Set ℂ := (fun p : ℝ×ℝ => (p.1:ℂ)+I*p.2) '' (Set.Icc 1 2 ×ˢ Set.Icc (-1) 1)
  have hS : IsCompact S := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hmem (z : ℂ) : z∈S ↔ 1 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ 1 := by
    constructor
    · rintro ⟨⟨u,v⟩,⟨hu,hv⟩,rfl⟩
      simpa [abs_le,and_assoc] using And.intro hu hv
    · rintro ⟨h₁,h₂,h₃⟩
      refine ⟨(z.re,z.im),⟨⟨h₁,h₂⟩,abs_le.mp h₃⟩,?_⟩
      simpa only [mul_comm] using Complex.re_add_im z
  have hc : ContinuousOn (fun z => (F z)⁻¹) S := by
    intro z hz
    exact (((poleRemovedL_differentiable 1).continuous.continuousAt).inv₀
      (poleRemovedL_ne_zero 1 ((hmem z).mp hz).1)).continuousWithinAt
  obtain ⟨M,hM⟩ := hS.exists_bound_of_continuousOn hc
  let D := max M 1
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let c := min (c₀/3) (1/(3*D))
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c,hc,?_⟩
  intro σ t hσ hσ2
  let z : ℂ := (σ:ℂ)+I*t
  have hz : 1 ≤ z.re := by simpa [z] using hσ
  have hT : 1 ≤ |t|+2 := by linarith [abs_nonneg t]
  have hP : 1 ≤ (|t|+2)^ε := Real.one_le_rpow hT hε.le
  by_cases ht : 1 ≤ |t|
  · have hz1 : z≠1 := by intro hh; have hi := congrArg Complex.im hh; simp [z] at hi; simp [hi] at ht; norm_num at ht
    have he : F z=(z-1)*riemannZeta z := by
      simp only [F,poleRemovedL,ite_true,DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hz1,
        DirichletCharacter.LFunctionTrivChar,DirichletCharacter.LFunction_modOne_eq]
    have hnorm : (|t|+2)/3 ≤ ‖z-1‖ := by
      have hi := Complex.abs_im_le_norm (z-1)
      simp [z] at hi
      linarith
    have hlow := hl σ t hσ hσ2 ht
    rw [Real.rpow_neg (by positivity : 0 ≤ |t|+2),←div_eq_mul_inv] at hlow
    change c*(|t|+2)/( |t|+2)^ε ≤ ‖F z‖
    rw [he,norm_mul]
    calc
      _ ≤ (c₀/3)*(|t|+2)/(|t|+2)^ε := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)) (by positivity)
      _ = ((|t|+2)/3)*(c₀/(|t|+2)^ε) := by ring
      _ ≤ _ := mul_le_mul hnorm hlow (by positivity) (norm_nonneg _)
  · have ht1 : |t| ≤ 1 := le_of_not_ge ht
    have hzS : z∈S := (hmem z).mpr ⟨hz,by simpa [z] using hσ2,by simpa [z] using ht1⟩
    have hb := (hM z hzS).trans (le_max_left M 1)
    have hn : 0 < ‖F z‖ := norm_pos_iff.mpr (poleRemovedL_ne_zero 1 hz)
    rw [norm_inv,inv_eq_one_div] at hb
    have hlow : 1/D ≤ ‖F z‖ := by
      apply (div_le_iff₀ hD).mpr
      have hh := (div_le_iff₀ hn).mp hb
      nlinarith
    change c*(|t|+2)/(|t|+2)^ε ≤ ‖F z‖
    apply le_trans ?_ hlow
    calc
      _ ≤ c*(|t|+2) := div_le_self (by positivity) hP
      _ ≤ (1/(3*D))*3 := mul_le_mul (min_le_right _ _) (by linarith) (by positivity) (by positivity)
      _ = 1/D := by ring

end LargePrimeGaps
end OAI

-- Source module: RieszBounds
namespace OAI
namespace LargePrimeGaps
open Complex Filter Topology
noncomputable def logRiesz (f : ℂ → ℂ) (s : ℂ) : ℂ := (-deriv f s / f s)/(s*(s+1))

lemma near_line_denominator {z w : ℂ} {r : ℝ} (hz : 1 ≤  z.re) (hr : r ≤ 1/4)
    (hw : w∈Metric.closedBall z r) :
    w≠0 ∧ w+1≠0 ∧ (|z.im|+2)^2 ≤ 16*‖w‖*‖w+1‖ := by
  have hd : ‖w-z‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hw
  have hre := Complex.re_le_norm (z-w)
  rw [Complex.sub_re,norm_sub_rev] at hre
  have hwre : 3/4 ≤ w.re := by linarith
  have hw0 : w≠0 := by intro h; simp [h] at hwre; norm_num at hwre
  have hw1 : w+1≠0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hna : 3/4 ≤ ‖w‖ := hwre.trans (Complex.re_le_norm w)
  have hnb : 3/4 ≤ ‖w+1‖ := by
    have h := Complex.re_le_norm (w+1)
    simp only [Complex.add_re,Complex.one_re] at h
    linarith
  have ha : |z.im| ≤ ‖w‖+r := by
    have ht := norm_add_le (z-w) w
    rw [sub_add_cancel,norm_sub_rev] at ht
    linarith [Complex.abs_im_le_norm z]
  have hb : |z.im| ≤ ‖w+1‖+r := by
    have ht := norm_add_le (z-w) (w+1)
    rw [show z-w+(w+1)=z+1 by ring,norm_sub_rev] at ht
    have hi := Complex.abs_im_le_norm (z+1)
    simp only [Complex.add_im,Complex.one_im,add_zero] at hi
    linarith
  have ha' : |z.im|+2 ≤ 4*‖w‖ := by linarith
  have hb' : |z.im|+2 ≤ 4*‖w+1‖ := by linarith
  refine ⟨hw0,hw1,?_⟩
  have hp := mul_le_mul ha' hb' (by positivity : 0 ≤ |z.im|+2) (by positivity : 0 ≤ 4*‖w‖)
  nlinarith

lemma logRiesz_local {f : ℂ → ℂ} {z : ℂ} {r m M : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1/4) (hm : 0 < m) (hM : 0 ≤ M) (hz : 1 ≤  z.re)
    (hf : ∀ w∈Metric.closedBall z r,AnalyticAt ℂ f w)
    (hb : ∀ w∈Metric.closedBall z r,‖deriv f w‖ ≤ M)
    (hl : m ≤ ‖f z‖) (hMr : M*r ≤ m/2) :
    (∀ w∈Metric.closedBall z r,f w≠0) ∧
      DiffContOnCl ℂ (logRiesz f) (Metric.ball z r) ∧
      ∀ w∈Metric.closedBall z r,‖logRiesz f w‖ ≤ (32*M/m)/(|z.im|+2)^2 := by
  have hmem : z∈Metric.closedBall z r := Metric.mem_closedBall_self hr.le
  have hlo (w : ℂ) (hw : w∈Metric.closedBall z r) : m/2 ≤ ‖f w‖ := by
    have hd := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun w hw => (hf w hw).differentiableAt) hb (convex_closedBall z r) hw hmem
    have hdist : ‖z-w‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev] using hw
    have hd' := hd.trans (mul_le_mul_of_nonneg_left hdist hM)
    have ht := norm_add_le (f z-f w) (f w)
    rw [sub_add_cancel] at ht
    linarith
  have hne (w : ℂ) (hw : w∈Metric.closedBall z r) : f w≠0 := by
    exact norm_pos_iff.mp ((by positivity : 0 < m/2).trans_le (hlo w hw))
  refine ⟨hne,?_,?_⟩
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hr.ne']
    intro w hw
    obtain ⟨hw0,hw1,_⟩ := near_line_denominator hz hr1 hw
    exact (((hf w hw).deriv.neg.div (hf w hw) (hne w hw)).div
      (analyticAt_id.mul (analyticAt_id.add analyticAt_const)) (mul_ne_zero hw0 hw1)).differentiableWithinAt
  · intro w hw
    obtain ⟨hw0,hw1,hden⟩ := near_line_denominator hz hr1 hw
    have hnorm : 0 < ‖w‖*‖w+1‖ := mul_pos (norm_pos_iff.mpr hw0) (norm_pos_iff.mpr hw1)
    have hb₀ : ‖deriv f w‖/‖f w‖ ≤ 2*M/m := by
      apply (div_le_div₀ hM (hb w hw) (by positivity : 0 < m/2) (hlo w hw)).trans_eq
      ring
    have hb₁ : 1/(‖w‖*‖w+1‖) ≤ 16/(|z.im|+2)^2 := by
      apply (div_le_div_iff₀ hnorm (by positivity)).mpr
      nlinarith
    simp only [logRiesz,norm_div,norm_neg,norm_mul]
    calc
      _ = (‖deriv f w‖/‖f w‖)*(1/(‖w‖*‖w+1‖)) := by ring
      _  ≤  (2*M/m)*(16/(|z.im|+2)^2) := mul_le_mul hb₀ hb₁ (by positivity) (by positivity)
      _ = _ := by ring

lemma logRiesz_iteratedDeriv_bound {f : ℂ → ℂ} {z : ℂ} {r m M : ℝ}
    (n : ℕ) (hr : 0 < r) (hr1 : r ≤ 1/4) (hm : 0 < m) (hM : 0 ≤ M) (hz : 1 ≤  z.re)
    (hf : ∀ w∈Metric.closedBall z r,AnalyticAt ℂ f w)
    (hb : ∀ w∈Metric.closedBall z r,‖deriv f w‖ ≤ M)
    (hl : m ≤ ‖f z‖) (hMr : M*r ≤ m/2) :
    ‖iteratedDeriv n (logRiesz f) z‖ ≤ (n.factorial:ℝ)*((32*M/m)/(|z.im|+2)^2)/r^n := by
  have hh := logRiesz_local hr hr1 hm hM hz hf hb hl hMr
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hh.2.1
    (fun w hw => hh.2.2 w (Metric.sphere_subset_closedBall hw))

lemma logRiesz_power_bound {f : ℂ → ℂ} {z : ℂ} {P W c K d : ℝ} (n : ℕ)
    (hP : 1 ≤ P) (hW : 0 < W) (hc : 0 < c) (hK : 0 < K) (hd : 0 < d)
    (hd1 : d ≤ 1/4) (hKd : K*d ≤ c/2) (hz : 1 ≤ z.re)
    (hf : ∀ w∈Metric.closedBall z (d/P^2), AnalyticAt ℂ f w)
    (hb : ∀ w∈Metric.closedBall z (d/P^2), ‖deriv f w‖ ≤ K*W*P)
    (hl : c*W/P ≤ ‖f z‖) :
    ‖iteratedDeriv n (logRiesz f) z‖ ≤
      ((n.factorial:ℝ)*(32*K/c)/d^n)*P^(2*n+2)/(|z.im|+2)^2 := by
  have hP0 : 0 < P := by linarith
  have hr1 : d/P^2 ≤ 1/4 := by
    apply (div_le_self hd.le (one_le_pow₀ hP)).trans hd1
  have hMr : (K*W*P)*(d/P^2) ≤ (c*W/P)/2 := by
    calc
      _ = (K*d)*W/P := by field_simp
      _ ≤ (c/2)*W/P := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hKd hW.le) hP0.le
      _ = _ := by ring
  have hh := logRiesz_iteratedDeriv_bound n (by positivity : 0 < d/P^2) hr1
    (by positivity : 0 < c*W/P) (by positivity : 0 ≤ K*W*P) hz hf hb hl hMr
  apply hh.trans_eq
  rw [div_pow,pow_add,pow_mul]
  field_simp

lemma near_strip_geometry {σ t d P η : ℝ} (hσ : 1 ≤ σ) (hσ2 : σ ≤ 2)
    (hP : 1 ≤ P) (hd : 0 ≤ d) (hd1 : d ≤ 1/4) (hdη : d ≤ η/4)
    {w : ℂ} (hw : w∈Metric.closedBall ((σ:ℂ)+I*t) (d/P^2)) :
    1-η/4 ≤ w.re ∧ ‖w‖+2 ≤ 3*(|t|+2) := by
  have hr : d/P^2 ≤ d := div_le_self hd (one_le_pow₀ hP)
  have hdist : ‖w-((σ:ℂ)+I*t)‖ ≤ d/P^2 := by
    simpa only [Metric.mem_closedBall,dist_eq_norm] using hw
  have hre := Complex.re_le_norm (((σ:ℂ)+I*t)-w)
  simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
    Complex.I_re,Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_self,add_zero,norm_sub_rev] at hre
  have hnorm := norm_add_le (w-((σ:ℂ)+I*t)) ((σ:ℂ)+I*t)
  rw [sub_add_cancel] at hnorm
  have hnz := Complex.norm_le_abs_re_add_abs_im ((σ:ℂ)+I*t)
  simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,
    one_mul,sub_self,zero_add,add_zero,abs_of_nonneg (by linarith : 0 ≤ σ)] at hnz
  constructor <;> linarith [abs_nonneg t]

lemma nonprincipal_logRiesz_bound (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ≠1 → ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 →
        ‖iteratedDeriv n (logRiesz χ.LFunction) (σ+I*t)‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*(|t|+2)^(-(3/2:ℝ)) := by
  let ε : ℝ := 1/(4*(n+1:ℕ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    apply (div_le_one (by positivity : 0 < 4*((n+1:ℕ):ℝ))).mpr
    have hn : (1:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast (Nat.succ_pos n)
    linarith
  obtain ⟨c,hc,hl⟩ := nonprincipal_strip_lower hε hε1
  obtain ⟨K₀,hK₀,hb⟩ := LFunction_deriv_norm_small_power (by linarith : 0 < ε/2) (by linarith : ε/2 ≤ 1/2)
  let K := K₀*3^ε
  have hK : 0 < K := by dsimp [K]; positivity
  let d := min (min (1/4) (ε/4)) (c/(2*K))
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d ≤ 1/4 := (min_le_left _ _).trans (min_le_left _ _)
  have hdε : d ≤ ε/4 := (min_le_left _ _).trans (min_le_right _ _)
  have hKd : K*d ≤ c/2 := by
    have h := min_le_right (min (1/4) (ε/4)) (c/(2*K))
    change d ≤ c/(2*K) at h
    have hh := mul_le_mul_of_nonneg_left h hK.le
    have he : K*(c/(2*K))=c/2 := by field_simp
    rwa [he] at hh
  let D := (n.factorial:ℝ)*(32*K/c)/d^n
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D,hD,?_⟩
  intro q _ χ hχp hχ σ t hσ hσ2
  let X : ℝ := ((q:ℝ)+2)*(|t|+2)
  let P : ℝ := X^ε
  have hX : 1 ≤ X := by dsimp [X]; nlinarith [Nat.cast_nonneg (α:=ℝ) q,abs_nonneg t]
  have hX0 : 0 < X := by linarith
  have hP : 1 ≤ P := Real.one_le_rpow hX hε.le
  have hlow : c*1/P ≤ ‖χ.LFunction (σ+I*t)‖ := by
    have h := hl q χ hχp hχ σ t hσ hσ2
    change c*X^(-ε) ≤ _ at h
    simpa only [mul_one,Real.rpow_neg hX0.le,div_eq_mul_inv] using h
  have hbound : ∀ w∈Metric.closedBall ((σ:ℂ)+I*t) (d/P^2), ‖deriv χ.LFunction w‖ ≤ K*1*P := by
    intro w hw
    obtain ⟨hre,hnorm⟩ := near_strip_geometry hσ hσ2 hP hd.le hd1 hdε hw
    have h := hb q χ hχ w (by linarith)
    rw [show 2*(ε/2)=ε by ring] at h
    have hn : ((q:ℝ)+2)*(‖w‖+2) ≤ 3*X := by
      dsimp [X]
      nlinarith [mul_nonneg (show (0:ℝ) ≤ q+2 by positivity) (sub_nonneg.mpr hnorm)]
    calc
      _ ≤ K₀*((q+2)*(‖w‖+2))^ε := h
      _ ≤ K₀*(3*X)^ε := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hn hε.le) hK₀.le
      _ = K*1*P := by rw [Real.mul_rpow (by norm_num) hX0.le]; dsimp [K,P]; ring
  have hh := logRiesz_power_bound n hP zero_lt_one hc hK hd hd1 hKd (by simpa using hσ)
    (fun w _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt w) hbound hlow
  have he : ε*(2*n+2:ℕ)=1/2 := by
    dsimp [ε]
    push_cast
    field_simp
    ring
  have hpow : P^(2*n+2)=X^(1/2:ℝ) := by
    dsimp [P]
    rw [←Real.rpow_mul_natCast hX0.le,he]
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,
    zero_mul,one_mul,zero_add] at hh
  change ‖iteratedDeriv n (logRiesz χ.LFunction) (σ+I*t)‖ ≤ D*P^(2*n+2)/(|t|+2)^2 at hh
  rw [hpow] at hh
  apply hh.trans_eq
  dsimp [X]
  rw [Real.mul_rpow (by positivity) (by positivity),Real.rpow_neg (by positivity : 0 ≤ |t|+2)]
  have ht : (|t|+2)^(1/2:ℝ)*(|t|+2)^(3/2:ℝ)=(|t|+2)^2 := by
    rw [←Real.rpow_add (by positivity),show (1/2:ℝ)+3/2=2 by norm_num]
    norm_num
  field_simp
  rw [←ht]

end LargePrimeGaps
end OAI

-- Source module: MellinSmoothing
namespace OAI
namespace LargePrimeGaps
open Complex Real Set MeasureTheory Filter Topology
noncomputable def rieszKernel : ℝ → ℂ := (Ioc 0 1).indicator (fun t => 1-(t:ℂ))

lemma hasMellin_rieszKernel {s : ℂ} (hs : 0<s.re) :
    HasMellin rieszKernel s (1/(s*(s+1))) := by
  have h₀ := hasMellin_one_Ioc hs
  have h₁ := hasMellin_cpow_Ioc 1 (by simp; linarith : 0<s.re+(1:ℂ).re)
  have hh := hasMellin_sub h₀.1 h₁.1
  rw [h₀.2,h₁.2] at hh
  have he : (fun t : ℝ => (Ioc 0 1).indicator (fun _ : ℝ => (1:ℂ)) t-
      (Ioc 0 1).indicator (fun t : ℝ => (t:ℂ)^(1:ℂ)) t)=rieszKernel := by
    ext t
    by_cases ht : t∈Ioc (0:ℝ) 1 <;> simp [rieszKernel,ht]
  rw [he] at hh
  have hs0 : s≠0 := by intro h; simp [h] at hs
  have hs1 : s+1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have heval : 1/s-1/(s+1)=1/(s*(s+1)) := by field_simp; ring
  rwa [heval] at hh

lemma rieszKernel_eq_max {x : ℝ} (hx : 0<x) : rieszKernel x=(max (1-x) 0:ℝ) := by
  by_cases hx1 : x≤1
  · simp [rieszKernel,Set.mem_Ioc,hx,hx1]
  · simp [rieszKernel,Set.mem_Ioc,hx,hx1,max_eq_right (by linarith : 1-x≤(0:ℝ))]

lemma rieszKernel_continuousAt {x : ℝ} (hx : 0<x) : ContinuousAt rieszKernel x := by
  have he : rieszKernel =ᶠ[𝓝 x] (fun x : ℝ => ((max (1-x) 0:ℝ):ℂ)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact rieszKernel_eq_max hy
  exact (show ContinuousAt (fun x : ℝ => ((max (1-x) 0:ℝ):ℂ)) x by fun_prop).congr he.symm

lemma rieszDenominator_bound {s : ℂ} (hs : 1≤ s.re) :
    ‖1/(s*(s+1))‖≤2/(1+s.im^2) := by
  have ha : 1≤‖s‖ := hs.trans (Complex.re_le_norm s)
  have hb : 1≤‖s+1‖ := by have h := Complex.re_le_norm (s+1); simp at h; linarith
  have hai : |s.im|≤‖s‖ := Complex.abs_im_le_norm s
  have hbi : |s.im|≤‖s+1‖ := by simpa using Complex.abs_im_le_norm (s+1)
  have hp : 1≤‖s‖*‖s+1‖ := one_le_mul_of_one_le_of_one_le ha hb
  have hpi : s.im^2≤‖s‖*‖s+1‖ := by
    simpa only [←sq, sq_abs] using mul_le_mul hai hbi (abs_nonneg _) (norm_nonneg _)
  rw [norm_div,norm_one,norm_mul]
  apply (div_le_div_iff₀ (by positivity : 0<‖s‖*‖s+1‖) (by positivity : 0<1+s.im^2)).mpr
  nlinarith

set_option maxHeartbeats 800000 in
lemma rieszDenominator_verticalIntegrable {σ : ℝ} (hσ : 1≤σ) :
    VerticalIntegrable (fun s : ℂ => 1/(s*(s+1))) σ := by
  have hne (t : ℝ) : (σ:ℂ)+(t:ℂ)*I≠0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hne1 (t : ℝ) : (σ:ℂ)+(t:ℂ)*I+1≠0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hm : Continuous (fun t : ℝ => 1/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro t
    exact mul_ne_zero (hne t) (hne1 t)
  apply (integrable_inv_one_add_sq.const_mul 2).mono' hm.aestronglyMeasurable
  filter_upwards [] with t
  have hb := rieszDenominator_bound (s:=(σ:ℂ)+t*I) (by simpa using hσ)
  simpa only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,mul_zero,
    Complex.ofReal_re,Complex.I_im,mul_one,add_zero,zero_add,div_eq_mul_inv] using hb

lemma rieszKernel_mellinInv {σ x : ℝ} (hσ : 1≤σ) (hx : 0<x) :
    mellinInv σ (fun s : ℂ => 1/(s*(s+1))) x=rieszKernel x := by
  have hσ0 : (0:ℝ)<σ := by linarith
  have hm (t : ℝ) : mellin rieszKernel (σ+t*I)=1/((σ+t*I)*(σ+t*I+1)) :=
    (hasMellin_rieszKernel (by simpa using hσ0)).2
  have hF : VerticalIntegrable (mellin rieszKernel) σ := by
    unfold VerticalIntegrable
    simp_rw [hm]
    exact rieszDenominator_verticalIntegrable hσ
  rw [←mellinInv_mellin_eq σ rieszKernel hx (hasMellin_rieszKernel (by simpa using hσ0)).1 hF
    (rieszKernel_continuousAt hx)]
  simp only [mellinInv,hm]

open Complex Filter Topology
lemma principal_logRiesz_bound (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 →
        ‖iteratedDeriv n (logRiesz (poleRemovedL (1:DirichletCharacter ℂ 1))) (σ+I*t)‖ ≤
          D*(|t|+2)^(-(3/2:ℝ)) := by
  let ε : ℝ := 1/(4*(n+1:ℕ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    apply (div_le_one (by positivity : 0 < 4*((n+1:ℕ):ℝ))).mpr
    have hn : (1:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast (Nat.succ_pos n)
    linarith
  obtain ⟨c,hc,hl⟩ := principal_strip_lower hε hε1
  obtain ⟨K₀,hK₀,hb⟩ := principal_deriv_growth hε hε1
  let K := 3*K₀*3^ε
  have hK : 0 < K := by dsimp [K]; positivity
  let d := min (min (1/4) (ε/4)) (c/(2*K))
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d ≤ 1/4 := (min_le_left _ _).trans (min_le_left _ _)
  have hdε : d ≤ ε/4 := (min_le_left _ _).trans (min_le_right _ _)
  have hKd : K*d ≤ c/2 := by
    have h := min_le_right (min (1/4) (ε/4)) (c/(2*K))
    change d ≤ c/(2*K) at h
    have hh := mul_le_mul_of_nonneg_left h hK.le
    have he : K*(c/(2*K))=c/2 := by field_simp
    rwa [he] at hh
  let D := (n.factorial:ℝ)*(32*K/c)/d^n
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D,hD,?_⟩
  intro σ t hσ hσ2
  let X : ℝ := (|t|+2)
  let P : ℝ := X^ε
  have hX : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg t]
  have hX0 : 0 < X := by linarith
  have hP : 1 ≤ P := Real.one_le_rpow hX hε.le
  have hlow : c*(|t|+2)/P ≤ ‖poleRemovedL (1:DirichletCharacter ℂ 1) (σ+I*t)‖ := hl σ t hσ hσ2
  have hbound : ∀ w∈Metric.closedBall ((σ:ℂ)+I*t) (d/P^2),
      ‖deriv (poleRemovedL (1:DirichletCharacter ℂ 1)) w‖ ≤ K*(|t|+2)*P := by
    intro w hw
    obtain ⟨hre,hnorm⟩ := near_strip_geometry hσ hσ2 hP hd.le hd1 hdε hw
    have h := hb w hre
    calc
      _ ≤ K₀*(‖w‖+2)*(‖w‖+2)^ε := h
      _ ≤ K₀*(3*X)*(3*X)^ε := by gcongr
      _ = K*(|t|+2)*P := by rw [Real.mul_rpow (by norm_num) hX0.le]; dsimp [K,P,X]; ring
  have hh := logRiesz_power_bound n hP (by positivity : 0 < |t|+2) hc hK hd hd1 hKd (by simpa using hσ)
    (fun w _ => (poleRemovedL_differentiable (1:DirichletCharacter ℂ 1)).analyticAt w) hbound hlow
  have he : ε*(2*n+2:ℕ)=1/2 := by
    dsimp [ε]
    push_cast
    field_simp
    ring
  have hpow : P^(2*n+2)=X^(1/2:ℝ) := by
    dsimp [P]
    rw [←Real.rpow_mul_natCast hX0.le,he]
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,
    zero_mul,one_mul,zero_add] at hh
  change ‖iteratedDeriv n (logRiesz (poleRemovedL (1:DirichletCharacter ℂ 1))) (σ+I*t)‖ ≤ D*P^(2*n+2)/(|t|+2)^2 at hh
  rw [hpow] at hh
  apply hh.trans_eq
  dsimp [X]
  rw [Real.rpow_neg (by positivity : 0 ≤ |t|+2)]
  have ht : (|t|+2)^(1/2:ℝ)*(|t|+2)^(3/2:ℝ)=(|t|+2)^2 := by
    rw [←Real.rpow_add (by positivity),show (1/2:ℝ)+3/2=2 by norm_num]
    norm_num
  field_simp
  rw [←ht]

lemma primitive_logRiesz_bound (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 →
        ‖iteratedDeriv n (logRiesz (poleRemovedL χ)) (σ+I*t)‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*(|t|+2)^(-(3/2:ℝ)) := by
  obtain ⟨D₀,hD₀,h₀⟩ := nonprincipal_logRiesz_bound n
  obtain ⟨D₁,hD₁,h₁⟩ := principal_logRiesz_bound n
  refine ⟨max D₀ D₁,lt_of_lt_of_le hD₀ (le_max_left _ _),?_⟩
  intro q _ χ hχp σ t hσ hσ2
  have hq : 1 ≤ ((q:ℝ)+2)^(1/2:ℝ) := Real.one_le_rpow (by linarith [Nat.cast_nonneg (α:=ℝ) q]) (by norm_num)
  by_cases hχ : χ=1
  · subst χ
    have hq1 : q=1 := by simpa [DirichletCharacter.IsPrimitive,DirichletCharacter.conductor_one] using hχp.symm
    subst q
    have hq' : 1 ≤ ((1:ℝ)+2)^(1/2:ℝ) := by simpa only [Nat.cast_one] using hq
    have hb := h₁ σ t hσ hσ2
    apply hb.trans
    have hc : D₁ ≤ max D₀ D₁*((1:ℝ)+2)^(1/2:ℝ) := by
      calc
        D₁ ≤ max D₀ D₁ := le_max_right _ _
        _ ≤ _ := le_mul_of_one_le_right (le_trans hD₀.le (le_max_left _ _)) hq'
    simpa only [Nat.cast_one] using mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (|t|+2)^(-(3/2:ℝ)))
  · have hb := h₀ q χ hχp hχ σ t hσ hσ2
    simp only [poleRemovedL,hχ,ite_false]
    apply hb.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity)

lemma logRiesz_poleRemoved_analyticAt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 ≤ s.re) : AnalyticAt ℂ (logRiesz (poleRemovedL χ)) s := by
  have h₀ : s≠0 := by intro h; simp [h] at hs; norm_num at hs
  have h₁ : s+1≠0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith
  exact (primeLogDerivativeRegular_analyticAt χ (poleRemovedL_ne_zero χ hs)).div
    (analyticAt_id.mul (analyticAt_id.add analyticAt_const)) (mul_ne_zero h₀ h₁)

open Complex Filter Topology MeasureTheory
open scoped FourierTransform
lemma analyticAt_iteratedDeriv_local {f : ℂ → ℂ} {z : ℂ} (h : AnalyticAt ℂ f z) (n : ℕ) :
    AnalyticAt ℂ (iteratedDeriv n f) z := by
  induction n with
  | zero => simpa using h
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

lemma vertical_contDiff {f : ℂ → ℂ} {z a : ℂ}
    (hf : ∀ t : ℝ, AnalyticAt ℂ f (z+a*t)) :
    ContDiff ℝ ⊤ (fun t : ℝ => f (z+a*t)) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have hr : ContDiffAt ℝ ⊤ (fun t : ℝ => (t:ℂ)) t := Complex.ofRealCLM.contDiff.contDiffAt
  exact ((hf t).contDiffAt.restrict_scalars ℝ).comp t
    (contDiffAt_const.add (contDiffAt_const.mul hr))

lemma vertical_iteratedDeriv {f : ℂ → ℂ} {z a : ℂ}
    (hf : ∀ t : ℝ, AnalyticAt ℂ f (z+a*t)) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => f (z+a*t)) =
      fun t : ℝ => a^n * iteratedDeriv n f (z+a*t) := by
  induction n with
  | zero => ext t; simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext t
    have ha : HasDerivAt (fun t : ℝ => z+a*t) a t := by
      convert (((hasDerivAt_id (t:ℂ)).const_mul a).const_add z).comp_ofReal using 1 <;> simp
    have hd := ((analyticAt_iteratedDeriv_local (hf t) n).differentiableAt.hasDerivAt.comp t ha).const_mul (a^n)
    rw [iteratedDeriv_succ]
    simpa only [Function.comp_def,pow_succ,mul_assoc,mul_comm,mul_left_comm] using hd.deriv

noncomputable def decayMajorant (t : ℝ) : ℝ := (1+|t|)^(-(3/2:ℝ))

lemma decayMajorant_integrable : Integrable decayMajorant := by
  change Integrable (fun t : ℝ => (1+|t|)^(-(3/2:ℝ)))
  simpa only [Real.norm_eq_abs] using
    (integrable_one_add_norm (E:=ℝ) (by norm_num : (Module.finrank ℝ ℝ:ℝ) < 3/2))

lemma integrable_of_decay_bound {g : ℝ → ℂ} {M : ℝ} (hg : Continuous g)
    (hb : ∀ t, ‖g t‖ ≤ M*decayMajorant t) : Integrable g := by
  exact (decayMajorant_integrable.const_mul M).mono' hg.aestronglyMeasurable (Filter.Eventually.of_forall hb)

lemma integral_norm_le_of_decay_bound {g : ℝ → ℂ} {M : ℝ} (hg : Continuous g)
    (hb : ∀ t, ‖g t‖ ≤ M*decayMajorant t) :
    ∫ t, ‖g t‖ ≤ M*(∫ t, decayMajorant t) := by
  rw [←integral_const_mul]
  exact integral_mono (integrable_of_decay_bound hg hb).norm
    (decayMajorant_integrable.const_mul M) hb

lemma fourierInv_decay {g : ℝ → ℂ} (hg : ContDiff ℝ ⊤ g)
    (hi : ∀ n : ℕ, Integrable (iteratedDeriv n g)) (n : ℕ) {M u : ℝ}
    (hb : (∫ t, ‖iteratedDeriv n g t‖) ≤ M) (hu : 0 < |u|) :
    ‖𝓕⁻ g u‖ ≤ M/|u|^n := by
  have he := congrFun (Real.fourier_iteratedDeriv (N:=⊤) (hg.of_le le_top) (fun n _ => hi n) (n:=n) (by simp)) (-u)
  have hn := VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
    (innerₗ ℝ) (iteratedDeriv n g) (-u)
  change ‖𝓕 (iteratedDeriv n g) (-u)‖ ≤ _ at hn
  have hn' := hn.trans hb
  rw [he,norm_smul,norm_pow] at hn'
  have hc : ‖(2:ℂ)*Real.pi*I*(-u)‖=2*Real.pi*|u| := by
    simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  simp only [Complex.ofReal_neg] at hn'
  rw [hc] at hn'
  rw [Real.fourierInv_eq_fourier_neg]
  apply (le_div_iff₀ (pow_pos hu n)).mpr
  have hπ : (1:ℝ) ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
  have hpow : |u|^n ≤ (2*Real.pi*|u|)^n := by
    gcongr
    exact le_mul_of_one_le_left hu.le hπ
  nlinarith [mul_le_mul_of_nonneg_right hpow (norm_nonneg (𝓕 g (-u)))]

open Complex Real Set MeasureTheory Filter Topology
lemma mellinInv_const_mul (σ : ℝ) (f : ℂ → ℂ) (a : ℂ) (x : ℝ) :
    mellinInv σ (fun s => a*f s) x=a*mellinInv σ f x := by
  simp [mellinInv,smul_eq_mul,Complex.real_smul,mul_left_comm,integral_const_mul,mul_assoc]

lemma mellinInv_term_riesz {σ y : ℝ} (hσ : 1≤σ) (hy : 0<y)
    (a : ℕ → ℂ) (n : ℕ) :
    mellinInv σ (fun s => LSeries.term a s n/(s*(s+1))) y=
      if n=0 then 0 else a n*rieszKernel ((n:ℝ)*y) := by
  by_cases hn : n=0
  · simp [hn,mellinInv]
  rw [ite_eq_right hn]
  have hi := rieszKernel_mellinInv hσ (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hy)
  rw [←hi]
  simp only [mellinInv,LSeries.term_of_ne_zero hn,smul_eq_mul,Complex.real_smul]
  rw [mul_left_comm (a n) ((1/(2*π):ℝ):ℂ)]
  congr 1
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg n) hy.le]
  simp only [Complex.ofReal_natCast,Complex.cpow_neg]
  ring

lemma riesz_inverse_integrand_norm {σ y : ℝ} (hy : 0<y) (a : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    ‖(y:ℂ)^(-((σ:ℂ)+t*I))*(LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))‖=
      (y^(-σ)*‖LSeries.term a (σ:ℂ) n‖)*‖1/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))‖ := by
  simp only [norm_mul,norm_div,norm_one,Complex.norm_cpow_eq_rpow_re_of_pos hy,
    Complex.neg_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero,LSeries.norm_term_eq]
  ring

lemma riesz_inverse_integrand_summable {σ y : ℝ} (hσ : 1≤σ) (hy : 0<y)
    (a : ℕ → ℂ) (ha : LSeriesSummable a (σ:ℂ)) :
    (∀ n : ℕ, Integrable (fun t : ℝ => (y:ℂ)^(-((σ:ℂ)+t*I))*
        (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))))) ∧
    Summable (fun n : ℕ => ∫ t : ℝ, ‖(y:ℂ)^(-((σ:ℂ)+t*I))*
        (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))‖) := by
  have hc (n : ℕ) : Continuous (fun t : ℝ => (y:ℂ)^(-((σ:ℂ)+t*I))*
      (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))) := by
    have hz (t : ℝ) : (σ:ℂ)+t*I≠0 := by
      intro hh; have := congrArg Complex.re hh; simp at this; linarith
    have hz1 (t : ℝ) : (σ:ℂ)+t*I+1≠0 := by
      intro hh; have := congrArg Complex.re hh; simp at this; linarith
    have hd : Continuous (fun t : ℝ => ((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)) := by fun_prop
    have he : Continuous (fun t : ℝ => -((σ:ℂ)+t*I)) := by fun_prop
    apply (he.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).mul
    apply Continuous.div _ hd (fun t => mul_ne_zero (hz t) (hz1 t))
    by_cases hn : n=0
    · simpa [hn] using (continuous_const : Continuous (fun _t : ℝ => (0:ℂ)))
    · simp only [LSeries.term_of_ne_zero hn]
      apply continuous_const.div
      · exact (show Continuous (fun t : ℝ => (σ:ℂ)+t*I) by fun_prop).const_cpow
          (.inl (Nat.cast_ne_zero.mpr hn))
      · intro t; exact Complex.cpow_ne_zero_iff.mpr (.inl (Nat.cast_ne_zero.mpr hn))
  have hnorm (n : ℕ) : Integrable (fun t : ℝ => ‖(y:ℂ)^(-((σ:ℂ)+t*I))*
      (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))‖) := by
    simp_rw [riesz_inverse_integrand_norm hy]
    exact (rieszDenominator_verticalIntegrable hσ).norm.const_mul _
  refine ⟨fun n => (integrable_norm_iff (hc n).aestronglyMeasurable).mp (hnorm n), ?_⟩
  simp_rw [riesz_inverse_integrand_norm hy,integral_const_mul]
  exact (ha.norm.mul_left (y^(-σ))).mul_right _

lemma mellinInv_LSeries_riesz {σ y : ℝ} (hσ : 1≤σ) (hy : 0<y)
    (a : ℕ → ℂ) (ha : LSeriesSummable a (σ:ℂ)) :
    mellinInv σ (fun s => LSeries a s/(s*(s+1))) y=
      ∑' n : ℕ, if n=0 then 0 else a n*rieszKernel ((n:ℝ)*y) := by
  obtain ⟨hi,hs⟩ := riesz_inverse_integrand_summable hσ hy a ha
  have he := integral_tsum_of_summable_integral_norm hi hs
  simp only [mellinInv,smul_eq_mul,Complex.real_smul]
  simp only [LSeries,←tsum_div_const,←tsum_mul_left]
  rw [←he,←tsum_mul_left]
  apply tsum_congr
  intro n
  exact mellinInv_term_riesz hσ hy a n

noncomputable def rieszSum (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n*(1-(n:ℂ)/(x:ℂ))

lemma rieszKernel_tsum_eq {x : ℝ} (hx : 0<x) (a : ℕ → ℂ) :
    (∑' n : ℕ, if n=0 then 0 else a n*rieszKernel ((n:ℝ)*(1/x)))=rieszSum a x := by
  classical
  rw [tsum_eq_sum (s:=Finset.Ioc 0 ⌊x⌋₊)]
  · apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hn0,hnx⟩ := Finset.mem_Ioc.mp hn
    have hn0' : (0:ℝ)<n := by exact_mod_cast hn0
    have hnx' : (n:ℝ)≤x := (Nat.le_floor_iff hx.le).mp hnx
    have hm0 : 0<(n:ℝ)*(1/x) := mul_pos hn0' (one_div_pos.mpr hx)
    have hm1 : (n:ℝ)*(1/x)≤1 := by rw [mul_one_div]; exact (div_le_one hx).mpr hnx'
    rw [ite_eq_right (by omega : n≠0),rieszKernel,
      Set.indicator_of_mem (show (n:ℝ)*(1/x)∈Ioc (0:ℝ) 1 from ⟨hm0,hm1⟩)]
    push_cast
    ring
  · intro n hn
    by_cases hn0 : n=0
    · simp [hn0]
    have hnx : x<(n:ℝ) := by
      have hnot : ¬n≤⌊x⌋₊ := by intro h; exact hn (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0,h⟩)
      exact lt_of_not_ge (fun h => hnot ((Nat.le_floor_iff hx.le).mpr h))
    have hm1 : ¬(n:ℝ)*(1/x)≤1 := by rw [mul_one_div]; exact not_le.mpr ((lt_div_iff₀ hx).mpr (by simpa using hnx))
    rw [ite_eq_right hn0,rieszKernel,
      Set.indicator_of_notMem (show (n:ℝ)*(1/x)∉Ioc (0:ℝ) 1 from fun h => hm1 h.2),mul_zero]

lemma rieszSum_mellinInv {σ x : ℝ} (hσ : 1≤σ) (hx : 0<x)
    (a : ℕ → ℂ) (ha : LSeriesSummable a (σ:ℂ)) :
    mellinInv σ (fun s => LSeries a s/(s*(s+1))) (1/x)=rieszSum a x := by
  rw [mellinInv_LSeries_riesz hσ (one_div_pos.mpr hx) a ha,rieszKernel_tsum_eq hx]

open Complex Real Set MeasureTheory Filter Topology
noncomputable def poleRieszKernel (y : ℝ) : ℂ :=
  (1/2:ℂ)*((y:ℂ)^(-1:ℂ)*rieszKernel y-rieszKernel y)

lemma hasMellin_poleRieszKernel {s : ℂ} (hs : 1<s.re) :
    HasMellin poleRieszKernel s (1/((s-1)*s*(s+1))) := by
  have h₀ := hasMellin_rieszKernel (s:=s) (by linarith)
  have h₁ := hasMellin_rieszKernel (s:=s+(-1)) (by simp; linarith)
  have hshift : MellinConvergent (fun t : ℝ => (t:ℂ)^(-1:ℂ) • rieszKernel t) s :=
    MellinConvergent.cpow_smul.mpr h₁.1
  have hm := mellin_cpow_smul rieszKernel s (-1)
  have hh := hasMellin_sub hshift h₀.1
  rw [hm,h₁.2,h₀.2] at hh
  have hhalf := hasMellin_const_smul hh.1 (1/2:ℂ)
  rw [hh.2] at hhalf
  have he : (1/2:ℂ) • (1/((s+-1)*(s+-1+1))-1/(s*(s+1)))=
      1/((s-1)*s*(s+1)) := by
    have hs0 : s≠0 := by intro h; simp [h] at hs; norm_num at hs
    have hs1 : s-1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    have hs2 : s+1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [show s+-1+1=s by ring,←sub_eq_add_neg]
    simp only [smul_eq_mul]
    field_simp [hs0,hs1,hs2]
    ring
  rw [he] at hhalf
  change HasMellin (fun t : ℝ => (1/2:ℂ)*((t:ℂ)^(-1:ℂ)*rieszKernel t-rieszKernel t)) s _
  simpa only [smul_eq_mul] using hhalf

lemma poleRieszKernel_continuousAt {y : ℝ} (hy : 0<y) :
    ContinuousAt poleRieszKernel y := by
  apply continuousAt_const.mul
  apply ContinuousAt.sub _ (rieszKernel_continuousAt hy)
  apply ContinuousAt.mul _ (rieszKernel_continuousAt hy)
  simp only [Complex.cpow_neg_one]
  have hr : ContinuousAt (fun t : ℝ => (t:ℂ)) y := Complex.continuous_ofReal.continuousAt
  exact hr.inv₀ (Complex.ofReal_ne_zero.mpr hy.ne')

set_option maxHeartbeats 3000000 in
lemma poleRiesz_verticalIntegrable {σ : ℝ} (hσ : 1<σ) :
    VerticalIntegrable (fun s : ℂ => 1/((s-1)*s*(s+1))) σ := by
  have hn (t : ℝ) : ((σ:ℂ)+t*I-1)*((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)≠0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · intro h; have := congrArg Complex.re h; simp at this; linarith
      · intro h; have := congrArg Complex.re h; simp at this; linarith
    · intro h; have := congrArg Complex.re h; simp at this; linarith
  have hc : Continuous (fun t : ℝ => 1/(((σ:ℂ)+t*I-1)*((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))) :=
    continuous_const.div (by fun_prop) hn
  have hbase : Integrable (fun t : ℝ => ‖1/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))‖) :=
    (rieszDenominator_verticalIntegrable hσ.le).norm
  change Integrable (fun t : ℝ => 1/(((σ:ℂ)+t*I-1)*((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))
  apply (hbase.const_mul (1/(σ-1))).mono' hc.aestronglyMeasurable
  filter_upwards [] with t
  rw [norm_div,norm_one,norm_mul,norm_mul]
  have hl : σ-1 ≤ ‖(σ:ℂ)+t*I-1‖ := by simpa using Complex.re_le_norm ((σ:ℂ)+t*I-1)
  have hn0 : 0<‖(σ:ℂ)+t*I-1‖ := lt_of_lt_of_le (by linarith) hl
  have hh : 1/‖(σ:ℂ)+t*I-1‖ ≤ 1/(σ-1) := one_div_le_one_div_of_le (by linarith) hl
  simpa only [norm_div,norm_one,norm_mul,div_eq_mul_inv,mul_inv_rev,norm_inv,mul_assoc,mul_comm,mul_left_comm,one_mul,mul_one]
    using mul_le_mul_of_nonneg_right hh (norm_nonneg (1/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))))

lemma poleRiesz_mellinInv {σ y : ℝ} (hσ : 1<σ) (hy : 0<y) :
    mellinInv σ (fun s : ℂ => 1/((s-1)*s*(s+1))) y=poleRieszKernel y := by
  have hm (t : ℝ) : mellin poleRieszKernel (σ+t*I)=1/((σ+t*I-1)*(σ+t*I)*(σ+t*I+1)) :=
    (hasMellin_poleRieszKernel (by simpa using hσ)).2
  have hf : VerticalIntegrable (mellin poleRieszKernel) σ := by
    unfold VerticalIntegrable
    simp_rw [hm]
    exact poleRiesz_verticalIntegrable hσ
  rw [←mellinInv_mellin_eq σ poleRieszKernel hy
    (hasMellin_poleRieszKernel (by simpa using hσ)).1 hf (poleRieszKernel_continuousAt hy)]
  simp only [mellinInv,hm]

lemma poleRieszKernel_inv {x : ℝ} (hx : 1≤x) :
    poleRieszKernel (1/x)=((x/2-1+1/(2*x):ℝ):ℂ) := by
  have hx0 : 0<x := by linarith
  have hy : 0<1/x := one_div_pos.mpr hx0
  have hy1 : 1/x≤1 := (div_le_one hx0).mpr hx
  rw [poleRieszKernel,rieszKernel_eq_max hy,max_eq_left (by linarith : 0≤1-1/x)]
  simp only [Complex.cpow_neg_one,Complex.ofReal_div,Complex.ofReal_one,inv_div,div_one,
    Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_ofNat]
  have hn : (x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  field_simp
  ring

lemma mellinInv_integrable {σ y : ℝ} (hy : 0<y) {f : ℂ → ℂ}
    (hf : VerticalIntegrable f σ) :
    Integrable (fun t : ℝ => (y:ℂ)^(-((σ:ℂ)+t*I))*f ((σ:ℂ)+t*I)) := by
  have he : Continuous (fun t : ℝ => -((σ:ℂ)+t*I)) := by fun_prop
  have hc := he.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hy.ne'))
  apply (hf.norm.const_mul (y^(-σ))).mono' (hc.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [] with t
  change ‖(y:ℂ)^(-((σ:ℂ)+t*I))*f ((σ:ℂ)+t*I)‖ ≤ y^(-σ)*‖f ((σ:ℂ)+t*I)‖
  simp only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy,Complex.neg_re,
    Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    mul_zero,zero_mul,sub_self,add_zero,le_refl]

lemma mellinInv_add_of_verticalIntegrable {σ y : ℝ} (hy : 0<y) {f g : ℂ → ℂ}
    (hf : VerticalIntegrable f σ) (hg : VerticalIntegrable g σ) :
    mellinInv σ (fun s => f s+g s) y=mellinInv σ f y+mellinInv σ g y := by
  simp only [mellinInv,smul_eq_mul,Complex.real_smul,mul_add]
  rw [integral_add (mellinInv_integrable hy hf) (mellinInv_integrable hy hg),mul_add]

open Complex Real Set MeasureTheory Filter Topology
open scoped FourierTransform
end LargePrimeGaps
end OAI

-- Source module: RieszDecay
namespace OAI
namespace LargePrimeGaps
open Complex Filter Topology
open Complex Filter Topology MeasureTheory
open Complex Real Set MeasureTheory Filter Topology
open scoped FourierTransform
noncomputable def logRieszVertical {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) : ℂ := logRiesz (poleRemovedL χ) (σ+2*π*t*I)

lemma logRieszVertical_contDiff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1≤σ) : ContDiff ℝ ⊤ (logRieszVertical χ σ) := by
  have h : ∀ t : ℝ, AnalyticAt ℂ (logRiesz (poleRemovedL χ)) ((σ:ℂ)+(2*π*I)*(t:ℂ)) := by
    intro t
    apply logRiesz_poleRemoved_analyticAt
    simpa using hσ
  convert vertical_contDiff h using 1
  ext t
  dsimp [logRieszVertical]
  congr 1
  ring

lemma logRieszVertical_iteratedDeriv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1≤σ) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (logRieszVertical χ σ) t=
      ((2:ℂ)*π*I)^n*iteratedDeriv n (logRiesz (poleRemovedL χ)) (σ+2*π*t*I) := by
  have h : ∀ t : ℝ, AnalyticAt ℂ (logRiesz (poleRemovedL χ)) ((σ:ℂ)+(2*π*I)*(t:ℂ)) := by
    intro t
    apply logRiesz_poleRemoved_analyticAt
    simpa using hσ
  have he : logRieszVertical χ σ=(fun t : ℝ => logRiesz (poleRemovedL χ) ((σ:ℂ)+(2*π*I)*(t:ℂ))) := by
    ext t
    dsimp [logRieszVertical]
    congr 1
    ring
  simpa only [he,mul_assoc,mul_comm,mul_left_comm] using congrFun (vertical_iteratedDeriv h n) t

lemma logRieszVertical_bound (n : ℕ) :
    ∃ D : ℝ, 0<D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ σ t : ℝ, 1≤σ → σ≤2 →
        ‖iteratedDeriv n (logRieszVertical χ σ) t‖ ≤
          (D*((q:ℝ)+2)^(1/2:ℝ))*decayMajorant t := by
  obtain ⟨D,hD,hb⟩ := primitive_logRiesz_bound n
  refine ⟨(2*π)^n*D,by positivity,?_⟩
  intro q _ χ hp σ t hσ hσ2
  have he : (σ:ℂ)+2*π*t*I=(σ:ℂ)+I*((2*π*t:ℝ):ℂ) := by push_cast; ring
  rw [logRieszVertical_iteratedDeriv χ hσ,norm_mul,norm_pow,he]
  have hc : ‖(2:ℂ)*π*I‖=2*π := by simp [abs_of_pos pi_pos]
  rw [hc]
  have ht : (|2*π*t|+2)^(-(3/2:ℝ)) ≤ decayMajorant t := by
    dsimp [decayMajorant]
    apply Real.rpow_le_rpow_of_nonpos (by positivity)
    · rw [abs_mul,abs_mul,abs_of_pos pi_pos]
      norm_num
      nlinarith [abs_nonneg t,pi_gt_three]
    · norm_num
  calc
    _ ≤ (2*π)^n*(D*((q:ℝ)+2)^(1/2:ℝ)*(|2*π*t|+2)^(-(3/2:ℝ))) :=
      mul_le_mul_of_nonneg_left (hb q χ hp σ (2*π*t) hσ hσ2) (by positivity)
    _ ≤ (2*π)^n*(D*((q:ℝ)+2)^(1/2:ℝ)*decayMajorant t) := by gcongr
    _ = _ := by ring

lemma logRieszVertical_integrable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) {σ : ℝ} (hσ : 1≤σ) (hσ2 : σ≤2) (n : ℕ) :
    Integrable (iteratedDeriv n (logRieszVertical χ σ)) := by
  obtain ⟨D,hD,hb⟩ := logRieszVertical_bound n
  exact integrable_of_decay_bound
    ((logRieszVertical_contDiff χ hσ).continuous_iteratedDeriv n (by simp))
    (hb q χ hp σ · hσ hσ2)

lemma logRiesz_mellinInv_bound (n : ℕ) :
    ∃ D : ℝ, 0<D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ σ x : ℝ, 1≤σ → σ≤2 → 1<x →
        ‖mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*x^σ/(Real.log x)^n := by
  obtain ⟨D,hD,hb⟩ := logRieszVertical_bound n
  let J : ℝ := ∫ t, decayMajorant t
  refine ⟨D*(|J|+1),by dsimp [J]; positivity,?_⟩
  intro q _ χ hp σ x hσ hσ2 hx
  have hx0 : 0<x := by linarith
  have hlog : 0<Real.log x := Real.log_pos hx
  have hi := logRieszVertical_integrable χ hp hσ hσ2
  have hg := logRieszVertical_contDiff χ hσ
  have hb' : (∫ t, ‖iteratedDeriv n (logRieszVertical χ σ) t‖) ≤ D*((q:ℝ)+2)^(1/2:ℝ)*J :=
    integral_norm_le_of_decay_bound (hg.continuous_iteratedDeriv n (by simp)) (hb q χ hp σ · hσ hσ2)
  have hf := fourierInv_decay hg hi n hb' (u:=Real.log x) (by rwa [abs_of_pos hlog])
  rw [mellinInv_eq_fourierInv σ _ (one_div_pos.mpr hx0),norm_smul,
    Complex.norm_cpow_eq_rpow_re_of_pos (one_div_pos.mpr hx0)]
  have he : -(Real.log (1/x))=Real.log x := by simp
  rw [he]
  change (1/x)^(-σ)*‖𝓕⁻ (logRieszVertical χ σ) (Real.log x)‖ ≤ _
  rw [one_div,Real.inv_rpow hx0.le,←Real.rpow_neg hx0.le,neg_neg]
  have hJ : J ≤ |J|+1 := by linarith [le_abs_self J]
  have hfac : 0≤ D*((q:ℝ)+2)^(1/2:ℝ) := by positivity
  calc
    _ ≤ x^σ*(D*((q:ℝ)+2)^(1/2:ℝ)*J/|Real.log x|^n) := mul_le_mul_of_nonneg_left hf (by positivity)
    _ ≤ x^σ*(D*((q:ℝ)+2)^(1/2:ℝ)*(|J|+1)/(Real.log x)^n) := by
      rw [abs_of_pos hlog]
      gcongr
    _ = _ := by ring

open Complex Real Set MeasureTheory Filter Topology
noncomputable def primeCoefficients {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)

noncomputable def characterMain {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ := by
  classical
  exact if χ=1 then 1 else 0

lemma characterMain_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) : ‖characterMain χ‖≤1 := by
  unfold characterMain
  split_ifs <;> norm_num

lemma primeCoefficients_summable {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (primeCoefficients χ) s := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs

lemma primeCoefficients_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖primeCoefficients χ n‖≤Real.log n := by
  rw [primeCoefficients,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact (mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)).trans
    ArithmeticFunction.vonMangoldt_le_log

lemma primeRiesz_identity {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1<s.re) :
    LSeries (primeCoefficients χ) s/(s*(s+1))=
      logRiesz (poleRemovedL χ) s+characterMain χ*(1/((s-1)*s*(s+1))) := by
  have he := primeLogDerivativeRegular_eq χ hs
  change primeLogDerivativeRegular χ s=LSeries (primeCoefficients χ) s-_ at he
  have hlog : logRiesz (poleRemovedL χ) s=primeLogDerivativeRegular χ s/(s*(s+1)) := rfl
  have hs0 : s≠0 := by intro h; simp [h] at hs; norm_num at hs
  have hs1 : s-1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hs2 : s+1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [hlog,he,characterMain]
  split_ifs <;> field_simp <;> ring

lemma logRiesz_verticalIntegrable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) {σ : ℝ} (hσ : 1≤σ) (hσ2 : σ≤2) :
    VerticalIntegrable (logRiesz (poleRemovedL χ)) σ := by
  have hπ : (2*π:ℝ)≠0 := by positivity
  have hi := (logRieszVertical_integrable χ hp hσ hσ2 0).comp_mul_left' (inv_ne_zero hπ)
  simp only [iteratedDeriv_zero] at hi
  have he : (fun t : ℝ => logRieszVertical χ σ ((2*π)⁻¹*t))=
      (fun t : ℝ => logRiesz (poleRemovedL χ) (σ+t*I)) := by
    ext t
    dsimp [logRieszVertical]
    congr 1
    push_cast
    field_simp
  rwa [he] at hi

set_option maxHeartbeats 800000 in
lemma primeRiesz_mellinInv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) {σ x : ℝ} (hσ : 1<σ) (hσ2 : σ≤2) (hx : 0<x) :
    mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)=
      rieszSum (primeCoefficients χ) x-characterMain χ*poleRieszKernel (1/x) := by
  have he : rieszSum (primeCoefficients χ) x=
      mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)+characterMain χ*poleRieszKernel (1/x) := by
    rw [←rieszSum_mellinInv hσ.le hx _ (primeCoefficients_summable χ (by simpa using hσ))]
    calc
      _ = mellinInv σ (fun s => logRiesz (poleRemovedL χ) s+
          characterMain χ*(1/((s-1)*s*(s+1)))) (1/x) := by
        unfold mellinInv
        congr 1
        apply integral_congr_ae
        filter_upwards [] with t
        rw [primeRiesz_identity χ (by simpa using hσ)]
      _ = mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)+
          mellinInv σ (fun s => characterMain χ*(1/((s-1)*s*(s+1)))) (1/x) :=
        mellinInv_add_of_verticalIntegrable (one_div_pos.mpr hx)
          (logRiesz_verticalIntegrable χ hp hσ.le hσ2) ((poleRiesz_verticalIntegrable hσ).const_mul _)
      _ = _ := by rw [mellinInv_const_mul,poleRiesz_mellinInv hσ (one_div_pos.mpr hx)]
  linear_combination -he

lemma primeRiesz_error_bound (n : ℕ) :
    ∃ D : ℝ, 0<D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ σ x : ℝ, 1<σ → σ≤2 → 1<x →
        ‖rieszSum (primeCoefficients χ) x-characterMain χ*(x:ℂ)/2‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*x^σ/(Real.log x)^n+1 := by
  obtain ⟨D,hD,hb⟩ := logRiesz_mellinInv_bound n
  refine ⟨D,hD,?_⟩
  intro q _ χ hp σ x hσ hσ2 hx
  have he := primeRiesz_mellinInv χ hp hσ hσ2 (by linarith : 0<x)
  rw [poleRieszKernel_inv hx.le] at he
  have he' : rieszSum (primeCoefficients χ) x-characterMain χ*(x:ℂ)/2=
      mellinInv σ (logRiesz (poleRemovedL χ)) (1/x)+characterMain χ*((-1+1/(2*x):ℝ):ℂ) := by
    push_cast at he ⊢
    linear_combination -he
  rw [he']
  apply (norm_add_le _ _).trans
  apply add_le_add (hb q χ hp σ x hσ.le hσ2 hx)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  have ht : |-1+1/(2*x)|≤1 := by
    rw [abs_le]
    have hx0 : 0<x := by linarith
    have ht0 : 0≤1/(2*x) := by positivity
    have ht1 : 1/(2*x)≤1 := (div_le_one (by positivity)).mpr (by linarith)
    constructor <;> linarith
  exact (mul_le_mul (characterMain_norm_le χ) ht (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

open Complex Real Set MeasureTheory Filter Topology
noncomputable def weightedPrefix (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n∈Finset.Ioc 0 ⌊x⌋₊, ((x-(n:ℝ):ℝ):ℂ)*a n

lemma weightedPrefix_difference {x h : ℝ} (hh : 0≤h) (a : ℕ → ℂ) :
    weightedPrefix a (x+h)-weightedPrefix a x=
      (h:ℂ)*(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)+
      ∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n := by
  classical
  have hfloor : ⌊x⌋₊≤⌊x+h⌋₊ := Nat.floor_mono (by linarith)
  have he : Finset.Ioc 0 ⌊x+h⌋₊=Finset.Ioc 0 ⌊x⌋₊ ∪ Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊ := by
    ext n
    simp only [Finset.mem_Ioc,Finset.mem_union]
    omega
  have hd : Disjoint (Finset.Ioc 0 ⌊x⌋₊) (Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊) := by
    rw [Finset.disjoint_left]
    intro n h₁ h₂
    simp only [Finset.mem_Ioc] at h₁ h₂
    omega
  unfold weightedPrefix
  rw [he,Finset.sum_union hd]
  have hs : (∑ n∈Finset.Ioc 0 ⌊x⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n)=
      (h:ℂ)*(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)+
      ∑ n∈Finset.Ioc 0 ⌊x⌋₊, ((x-(n:ℝ):ℝ):ℂ)*a n := by
    rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    push_cast
    ring
  rw [hs]
  ring

lemma weightedPrefix_tail_bound {x h L : ℝ} (hx : 0≤x) (hh : 0≤h) (hL : 0≤L)
    (a : ℕ → ℂ) (ha : ∀ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ‖a n‖≤L) :
    ‖∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n‖ ≤ (h+1)*(h*L) := by
  have hfloor : ⌊x⌋₊≤⌊x+h⌋₊ := Nat.floor_mono (by linarith)
  have hn (n : ℕ) (hn : n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊) :
      0≤x+h-(n:ℝ) ∧ x+h-(n:ℝ)≤h := by
    obtain ⟨h₁,h₂⟩ := Finset.mem_Ioc.mp hn
    have hlo : x<(n:ℝ) := by
      have hn' : (⌊x⌋₊:ℝ)+1≤n := by exact_mod_cast h₁
      linarith [Nat.lt_floor_add_one x]
    have hup : (n:ℝ)≤x+h := (Nat.le_floor_iff (by linarith)).mp h₂
    constructor <;> linarith
  have hc : ((Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊).card:ℝ) ≤ h+1 := by
    rw [Nat.card_Ioc,Nat.cast_sub hfloor]
    have hlo := Nat.lt_floor_add_one x
    have hup := Nat.floor_le (by linarith : 0≤x+h)
    linarith
  calc
    _ ≤ ∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ‖((x+h-(n:ℝ):ℝ):ℂ)*a n‖ := norm_sum_le _ _
    _ ≤ ∑ _n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, h*L := by
      apply Finset.sum_le_sum
      intro n hn'
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hn n hn').1]
      exact mul_le_mul (hn n hn').2 (ha n hn') (norm_nonneg _) hh
    _ = ((Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊).card:ℝ)*(h*L) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (mul_nonneg hh hL)

lemma prefix_unsmoothing {x h L : ℝ} (hx : 0≤x) (hh : 0<h) (hL : 0≤L)
    (a : ℕ → ℂ) (δ : ℂ) (ha : ∀ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ‖a n‖≤L) :
    ‖(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ)‖ ≤
      (‖weightedPrefix a (x+h)-δ*((x+h:ℝ):ℂ)^2/2‖+
        ‖weightedPrefix a x-δ*(x:ℂ)^2/2‖)/h+(h+1)*L+‖δ‖*h/2 := by
  let T := ∑ n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊, ((x+h-(n:ℝ):ℝ):ℂ)*a n
  let E (y : ℝ) := weightedPrefix a y-δ*(y:ℂ)^2/2
  have he : (h:ℂ)*((∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ))=
      (E (x+h)-E x)-T+δ*(h:ℂ)^2/2 := by
    have hd := weightedPrefix_difference (x:=x) hh.le a
    change weightedPrefix a (x+h)-weightedPrefix a x = _+T at hd
    dsimp [E]
    push_cast
    linear_combination -hd
  have hn : h*‖(∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ)‖ ≤
      (‖E (x+h)‖+‖E x‖)+((h+1)*(h*L))+‖δ‖*h^2/2 := by
    calc
      _ = ‖(h:ℂ)*((∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n)-δ*(x:ℂ))‖ := by
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
      _ = ‖(E (x+h)-E x)-T+δ*(h:ℂ)^2/2‖ := congrArg norm he
      _ ≤ ‖E (x+h)-E x‖+‖T‖+‖δ*(h:ℂ)^2/2‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ (‖E (x+h)‖+‖E x‖)+((h+1)*(h*L))+‖δ‖*h^2/2 := by
        have hT : ‖T‖≤(h+1)*(h*L) := weightedPrefix_tail_bound hx hh.le hL a ha
        have hδ : ‖δ*(h:ℂ)^2/2‖=‖δ‖*h^2/2 := by
          simp [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
        rw [hδ]
        exact add_le_add (add_le_add (norm_sub_le _ _) hT) le_rfl
  have hd : h*((‖E (x+h)‖+‖E x‖)/h+(h+1)*L+‖δ‖*h/2)=
      (‖E (x+h)‖+‖E x‖)+((h+1)*(h*L))+‖δ‖*h^2/2 := by field_simp
  dsimp [E] at hn hd
  apply (mul_le_mul_iff_left₀ hh).mp
  rw [mul_comm _ h, mul_comm _ h, hd]
  exact hn

open Complex Real Set MeasureTheory Filter Topology
lemma weightedPrefix_eq_mul_rieszSum (a : ℕ → ℂ) {x : ℝ} (hx : 0<x) :
    weightedPrefix a x=(x:ℂ)*rieszSum a x := by
  unfold weightedPrefix rieszSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hx0 : (x:ℂ)≠0 := by exact_mod_cast hx.ne'
  push_cast
  field_simp

lemma rpow_one_add_inv_log {x : ℝ} (hx : 1<x) :
    x^(1+1/Real.log x)=Real.exp 1*x := by
  have hx0 : 0<x := by linarith
  have hlog : Real.log x≠0 := (Real.log_pos hx).ne'
  rw [Real.rpow_add hx0,Real.rpow_one,Real.rpow_def_of_pos hx0]
  rw [mul_one_div_cancel hlog]
  ring

lemma primeWeighted_error_bound (a : ℝ) :
    ∃ D : ℝ, 0<D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ x : ℝ, 1<x → 1≤Real.log x →
        ‖weightedPrefix (primeCoefficients χ) x-characterMain χ*(x:ℂ)^2/2‖ ≤
          D*((q:ℝ)+2)^(1/2:ℝ)*x^2*(Real.log x)^(-a)+x := by
  obtain ⟨D,hD,hb⟩ := primeRiesz_error_bound ⌈a⌉₊
  refine ⟨D*Real.exp 1,by positivity,?_⟩
  intro q _ χ hp x hx hL
  have hx0 : 0<x := by linarith
  have hlog : 0<Real.log x := Real.log_pos hx
  have hσ : 1<1+1/Real.log x := by linarith [one_div_pos.mpr hlog]
  have hσ2 : 1+1/Real.log x≤2 := by
    have : 1/Real.log x≤1 := (div_le_one hlog).mpr hL
    linarith
  have he : weightedPrefix (primeCoefficients χ) x-characterMain χ*(x:ℂ)^2/2=
      (x:ℂ)*(rieszSum (primeCoefficients χ) x-characterMain χ*(x:ℂ)/2) := by
    rw [weightedPrefix_eq_mul_rieszSum _ hx0]
    ring
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx0]
  calc
    _ ≤ x*(D*((q:ℝ)+2)^(1/2:ℝ)*x^(1+1/Real.log x)/(Real.log x)^⌈a⌉₊+1) :=
      mul_le_mul_of_nonneg_left (hb q χ hp _ x hσ hσ2 hx) hx0.le
    _ = D*Real.exp 1*((q:ℝ)+2)^(1/2:ℝ)*x^2*(Real.log x)^(-(⌈a⌉₊:ℝ))+x := by
      rw [rpow_one_add_inv_log hx,Real.rpow_neg hlog.le,Real.rpow_natCast]
      ring
    _ ≤ _ := by
      have hn : a≤(⌈a⌉₊:ℝ) := Nat.le_ceil a
      gcongr

end LargePrimeGaps
end OAI

-- Source module: Main
namespace OAI
namespace LargePrimeGaps
open Complex Filter Topology
open Complex Filter Topology MeasureTheory
open scoped FourierTransform
open Complex Real Set MeasureTheory Filter Topology
lemma primeCharacterError_log_bound (A B : ℝ) (hA : 0<A) (hB : 0<B) :
    ∃ M : ℝ, 0<M ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ x : ℝ, 2≤x → 1≤Real.log x → (Real.log x)^(2*A+2)≤x →
        (q:ℝ)≤(Real.log x)^B →
        ‖primeCharacterError x χ‖≤M*x*(Real.log x)^(-A) := by
  obtain ⟨D,hD,hb⟩ := primeWeighted_error_bound (B+2*A+2)
  refine ⟨15*D+8,by positivity,?_⟩
  intro q _ χ hp x hx hL hpower hq
  let L := Real.log x
  let K := A+2
  let a := B+2*A+2
  let Q := ((q:ℝ)+2)^(1/2:ℝ)
  let h := x/L^K
  have hx0 : 0<x := by linarith
  have hx1 : 1<x := by linarith
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hK : 0<K := by dsimp [K]; linarith
  have ha : 0<a := by dsimp [a]; linarith
  have hpK : 0<L^K := Real.rpow_pos_of_pos hL0 _
  have hh0 : 0<h := div_pos hx0 hpK
  have hK1 : 1≤L^K := Real.one_le_rpow hL hK.le
  have hhx : h≤x := (div_le_self hx0.le hK1)
  have hKh : L^K≤x := by
    apply (Real.rpow_le_rpow_of_exponent_le hL (show K≤2*A+2 by dsimp [K]; linarith)).trans
    exact hpower
  have hh1 : 1≤h := (le_div_iff₀ hpK).mpr (by simpa using hKh)
  have hyx : x≤x+h := by linarith
  have hy : 1<x+h := by linarith
  have hy2 : x+h≤2*x := by linarith
  have hLy : L≤Real.log (x+h) := Real.log_le_log hx0 hyx
  have hLy1 : 1≤Real.log (x+h) := hL.trans hLy
  have hLy2 : Real.log (x+h)≤2*L := by
    calc
      _ ≤ Real.log (x^2) := Real.log_le_log (by linarith) (by nlinarith)
      _ = _ := by rw [Real.log_pow]; rfl
  have hQ0 : 0≤Q := by dsimp [Q]; positivity
  have hQ : Q≤3*L^B := by
    have hq2 : 1≤(q:ℝ)+2 := by have := Nat.cast_nonneg (α:=ℝ) q; linarith
    have hqpow : Q≤(q:ℝ)+2 := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hq2 (show (1/2:ℝ)≤1 by norm_num)
    have hLB : 1≤L^B := Real.one_le_rpow hL hB.le
    linarith
  let E (y : ℝ) := ‖weightedPrefix (primeCoefficients χ) y-characterMain χ*(y:ℂ)^2/2‖
  have hEx : E x≤D*Q*x^2*L^(-a)+x := hb q χ hp x hx1 hL
  have hEy : E (x+h)≤4*D*Q*x^2*L^(-a)+2*x := by
    calc
      _ ≤ D*Q*(x+h)^2*(Real.log (x+h))^(-a)+(x+h) := hb q χ hp (x+h) hy hLy1
      _ ≤ D*Q*(2*x)^2*L^(-a)+2*x := by
        apply add_le_add _ hy2
        apply mul_le_mul _ (Real.rpow_le_rpow_of_nonpos hL0 hLy (neg_nonpos.mpr ha.le)) (by positivity) (by positivity)
        gcongr
      _ = _ := by ring
  have hcoeff (n : ℕ) (hn : n∈Finset.Ioc ⌊x⌋₊ ⌊x+h⌋₊) :
      ‖primeCoefficients χ n‖≤2*L := by
    have hn0 : 0<(n:ℝ) := by exact_mod_cast (show 0<n by have := (Finset.mem_Ioc.mp hn).1; omega)
    have hnx : (n:ℝ)≤x+h := (Nat.le_floor_iff (by linarith : 0≤x+h)).mp (Finset.mem_Ioc.mp hn).2
    exact (primeCoefficients_norm_le χ n).trans ((Real.log_le_log hn0 hnx).trans hLy2)
  have heq : primeCharacterError x χ=
      (∑ n∈Finset.Ioc 0 ⌊x⌋₊, primeCoefficients χ n)-characterMain χ*(x:ℂ) := by
    classical
    simp only [primeCharacterError,primeCharacterPrefix,primeCoefficients,characterMain]
    split_ifs <;> simp
  rw [heq]
  have hu := prefix_unsmoothing hx0.le hh0 (show 0≤2*L by positivity)
    (primeCoefficients χ) (characterMain χ) hcoeff
  change _≤(E (x+h)+E x)/h+(h+1)*(2*L)+‖characterMain χ‖*h/2 at hu
  have hδ : ‖characterMain χ‖*h/2≤h := by
    have := mul_le_mul_of_nonneg_right (characterMain_norm_le χ) hh0.le
    linarith
  have htail : (h+1)*(2*L)≤4*h*L := by nlinarith
  have herr : (E (x+h)+E x)/h ≤ 15*D*x*L^(-A)+3*x*L^(-A) := by
    calc
      _ ≤ (5*D*Q*x^2*L^(-a)+3*x)/h := by
        apply div_le_div_of_nonneg_right _ hh0.le
        linarith
      _ ≤ (5*D*(3*L^B)*x^2*L^(-a)+3*x)/h := by gcongr
      _ = (15*D*L^B*x^2*L^(-a)+3*x)/h := by ring
      _ = 15*D*x*L^(-A)+3*L^K := by
        dsimp [h]
        rw [div_eq_mul_inv,inv_div]
        have hr : L^B*L^(-a)*L^K=L^(-A) := by
          rw [←Real.rpow_add hL0,←Real.rpow_add hL0]
          congr 1
          dsimp [a,K]
          ring
        field_simp
        linear_combination 15*D*x*hr
      _ ≤ _ := by
        have ht : L^K≤x*L^(-A) := by
          calc
            _ = L^(2*A+2)*L^(-A) := by rw [←Real.rpow_add hL0]; congr 1; dsimp [K]; ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hpower (by positivity)
        nlinarith [ht]
  have hsmall : h≤x*L^(-A) := by
    dsimp [h]
    rw [div_eq_mul_inv,←Real.rpow_neg hL0.le]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (show -K≤-A by dsimp [K]; linarith)) hx0.le
  have htail' : 4*h*L≤4*x*L^(-A) := by
    calc
      _ = 4*x*L^(1-K) := by
        dsimp [h]
        rw [div_eq_mul_inv,Real.rpow_sub hL0,Real.rpow_one]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL (show 1-K≤-A by dsimp [K]; linarith)) (by positivity)
  calc
    _ ≤ (E (x+h)+E x)/h+(h+1)*(2*L)+‖characterMain χ‖*h/2 := hu
    _ ≤ (15*D*x*L^(-A)+3*x*L^(-A))+4*x*L^(-A)+x*L^(-A) := by
      exact add_le_add (add_le_add herr (htail.trans htail')) (hδ.trans hsmall)
    _ = _ := by ring

theorem siegelWalfisz : SiegelWalfisz := by
  intro A B hA hB
  obtain ⟨M,hM,hb⟩ := primeCharacterError_log_bound A B hA hB
  have hevent : ∀ᶠ x : ℝ in atTop, 2≤x ∧ 1≤Real.log x ∧ (Real.log x)^(2*A+2)≤x := by
    filter_upwards [eventually_ge_atTop (2:ℝ),eventually_ge_atTop (Real.exp 1),
      eventually_log_rpow_le_rpow (2*A+2) (by norm_num : (0:ℝ)<1)] with x hx hex hp
    refine ⟨hx,?_,by simpa only [Real.rpow_one] using hp⟩
    rw [←Real.log_exp (1:ℝ)]
    exact Real.log_le_log (Real.exp_pos _) hex
  obtain ⟨x₀,hx₀⟩ := eventually_atTop.mp hevent
  refine ⟨M,hM,max x₀ 2,by have := le_max_right x₀ (2:ℝ); linarith,?_⟩
  intro x hx d hd hdlog χ hχ
  let : NeZero d := ⟨ne_of_gt hd⟩
  obtain ⟨hx2,hlog,hpower⟩ := hx₀ x ((le_max_left _ _).trans hx)
  exact hb d χ hχ x hx2 hlog hpower hdlog

end LargePrimeGaps
end OAI


-- Source module: OrthantIntegrals
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
noncomputable def residueSlice (f : ℕ → ℝ) (L U q c : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Ioc L U).filter (fun n => n % q = c), f n

noncomputable def residuePrefix (f : ℕ → ℝ) (Y q c : ℕ) : ℝ :=
  residueSlice f 0 Y q c

end LargePrimeGaps
end OAI

-- Source module: CharacterErrors
namespace OAI
namespace LargePrimeGaps
open Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Asymptotics
open scoped Classical
open scoped ContDiff
open Topology
open scoped Convolution ContDiff Pointwise
theorem character_prefix_orthogonality (x : ℝ) {q c : ℕ} (hq : 0<q)
    (hc : c<q) (hcop : Nat.Coprime c q) :
    ∑ χ : DirichletCharacter ℂ q, χ (c:ZMod q)⁻¹*primeCharacterPrefix x χ=
      (q.totient:ℂ)*(residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c:ℂ) := by
  classical
  have : NeZero q := ⟨ne_of_gt hq⟩
  have hu : IsUnit (c:ZMod q) := (ZMod.isUnit_iff_coprime c q).mpr hcop
  have he (n : ℕ) : (c:ZMod q)=(n:ZMod q) ↔ n % q = c := by
    rw [ZMod.natCast_eq_natCast_iff',Nat.mod_eq_of_lt hc]
    exact eq_comm
  unfold primeCharacterPrefix
  simp_rw [Finset.mul_sum,←mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [←Finset.sum_mul,DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu,he]
  simp only [residuePrefix,residueSlice,Complex.ofReal_sum,Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> simp

theorem character_error_orthogonality (x : ℝ) {q c : ℕ} (hq : 0<q)
    (hc : c<q) (hcop : Nat.Coprime c q) :
    ∑ χ : DirichletCharacter ℂ q, χ (c:ZMod q)⁻¹*primeCharacterError x χ=
      (q.totient:ℂ)*((residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-x/q.totient:ℝ):ℂ) := by
  classical
  have : NeZero q := ⟨ne_of_gt hq⟩
  have hu : IsUnit (c:ZMod q) := (ZMod.isUnit_iff_coprime c q).mpr hcop
  have huinv : IsUnit (c:ZMod q)⁻¹ := by
    obtain ⟨u,hu⟩ := hu
    rw [←hu,ZMod.inv_coe_unit]
    exact (u⁻¹).isUnit
  have ht : (q.totient:ℂ)≠0 := by exact_mod_cast ne_of_gt (Nat.totient_pos.mpr hq)
  simp only [primeCharacterError,mul_sub,Finset.sum_sub_distrib]
  rw [character_prefix_orthogonality x hq hc hcop]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte,MulChar.one_apply huinv,one_mul]
  push_cast
  field_simp

theorem endpointClassError_le_character_sum (x : ℝ) {q c : ℕ} (hq : 0<q)
    (hc : c<q) (hcop : Nat.Coprime c q) :
    |residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-x/q.totient|≤
      (∑ χ : DirichletCharacter ℂ q, ‖primeCharacterError x χ‖)/(q.totient:ℝ) := by
  have hphi : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  apply (le_div_iff₀ hphi).mpr
  have hh := character_error_orthogonality x hq hc hcop
  calc
    _ = ‖(q.totient:ℂ)*((residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c-x/q.totient:ℝ):ℂ)‖ := by
      rw [norm_mul,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,mul_comm]
    _ = ‖∑ χ : DirichletCharacter ℂ q, χ (c:ZMod q)⁻¹*primeCharacterError x χ‖ := congrArg norm hh.symm
    _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖χ (c:ZMod q)⁻¹*primeCharacterError x χ‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro χ _
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

theorem vonMangoldt_noncoprime_sum_le (X : ℕ) {q : ℕ} (hq : 0<q) :
    (∑ n∈(Finset.Ioc 0 X).filter (fun n => ¬Nat.Coprime n q),
      ArithmeticFunction.vonMangoldt n)≤(Nat.log 2 X:ℝ)*Real.log q := by
  classical
  let S := (Finset.Ioc 0 X).filter (fun n => ¬Nat.Coprime n q ∧ ArithmeticFunction.vonMangoldt n≠0)
  have he : (∑ n∈(Finset.Ioc 0 X).filter (fun n => ¬Nat.Coprime n q),
      ArithmeticFunction.vonMangoldt n)=∑ n∈S,ArithmeticFunction.vonMangoldt n := by
    simp only [S,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hcop : Nat.Coprime n q <;> by_cases hn : ArithmeticFunction.vonMangoldt n=0 <;> simp [hcop,hn]
  rw [he]
  have hsub : S⊆(q^(Nat.log 2 X)).divisors := by
    intro n hn
    obtain ⟨hnI,hnq,hnv⟩ := Finset.mem_filter.mp hn
    obtain ⟨p,k,hp,_hk,hpkn⟩ := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hnv
    have hp' : p.Prime := Nat.prime_iff.mpr hp
    have hdp : p∣q := by
      by_contra hd
      have hc := (hp'.coprime_iff_not_dvd).mpr hd
      exact hnq (hpkn ▸ hc.pow_left k)
    have hkX : k≤Nat.log 2 X := by
      apply Nat.le_log_of_pow_le (by norm_num : 1<2)
      calc
        2^k≤p^k := Nat.pow_le_pow_left hp'.two_le k
        _ = n := hpkn
        _ ≤ X := (Finset.mem_Ioc.mp hnI).2
    apply Nat.mem_divisors.mpr
    refine ⟨?_,pow_ne_zero _ (ne_of_gt hq)⟩
    rw [←hpkn]
    exact (pow_dvd_pow_of_dvd hdp k).trans (pow_dvd_pow q hkX)
  calc
    _ ≤ ∑ n∈(q^(Nat.log 2 X)).divisors,ArithmeticFunction.vonMangoldt n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = Real.log ((q^(Nat.log 2 X):ℕ):ℝ) := ArithmeticFunction.vonMangoldt_sum
    _ = _ := by rw [Nat.cast_pow,Real.log_pow]

theorem primitiveCharacter_eq_one_iff {q : ℕ} (hq : 0<q) (χ : DirichletCharacter ℂ q) :
    χ.primitiveCharacter=1 ↔ χ=1 := by
  have : NeZero q := ⟨ne_of_gt hq⟩
  constructor
  · intro h
    rw [←DirichletCharacter.changeLevel_primitiveCharacter χ,h,DirichletCharacter.changeLevel_one]
  · rintro rfl
    exact DirichletCharacter.primitiveCharacter_one

theorem primeCharacterPrefix_primitive_difference (x : ℝ) {q : ℕ} (hq : 0<q)
    (χ : DirichletCharacter ℂ q) :
    ‖primeCharacterPrefix x χ-primeCharacterPrefix x χ.primitiveCharacter‖≤
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  have hsame (n : ℕ) (hn : Nat.Coprime n q) :
      χ.primitiveCharacter (n:ZMod χ.conductor)=χ (n:ZMod q) := by
    simpa only [Int.cast_natCast] using χ.primitiveCharacter_apply_of_isCoprime hn.isCoprime
  have hzero (n : ℕ) (hn : ¬Nat.Coprime n q) : χ (n:ZMod q)=0 :=
    χ.map_nonunit (fun h => hn ((ZMod.isUnit_iff_coprime n q).mp h))
  calc
    _ = ‖∑ n∈Finset.Ioc 0 ⌊x⌋₊,(χ (n:ZMod q)-χ.primitiveCharacter (n:ZMod χ.conductor))*
        (ArithmeticFunction.vonMangoldt n:ℂ)‖ := by
      congr 1
      simp only [primeCharacterPrefix,sub_mul,Finset.sum_sub_distrib]
    _ ≤ ∑ n∈Finset.Ioc 0 ⌊x⌋₊,‖(χ (n:ZMod q)-χ.primitiveCharacter (n:ZMod χ.conductor))*
        (ArithmeticFunction.vonMangoldt n:ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n∈(Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬Nat.Coprime n q),ArithmeticFunction.vonMangoldt n := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro n _
      by_cases hn : Nat.Coprime n q
      · simp [hn,hsame n hn]
      · simp only [ite_eq_left hn,hzero n hn,zero_sub,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
          (χ.primitiveCharacter.norm_le_one _)
    _ ≤ _ := vonMangoldt_noncoprime_sum_le _ hq

theorem primeCharacterError_primitive_difference (x : ℝ) {q : ℕ} (hq : 0<q)
    (χ : DirichletCharacter ℂ q) :
    ‖primeCharacterError x χ-primeCharacterError x χ.primitiveCharacter‖≤
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  have he : primeCharacterError x χ-primeCharacterError x χ.primitiveCharacter=
      primeCharacterPrefix x χ-primeCharacterPrefix x χ.primitiveCharacter := by
    simp only [primeCharacterError,primitiveCharacter_eq_one_iff hq χ]
    ring
  rw [he]
  exact primeCharacterPrefix_primitive_difference x hq χ

theorem primeCharacterError_le_primitive (x : ℝ) {q : ℕ} (hq : 0<q)
    (χ : DirichletCharacter ℂ q) :
    ‖primeCharacterError x χ‖≤‖primeCharacterError x χ.primitiveCharacter‖+
      (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
  have hn := norm_add_le (primeCharacterError x χ.primitiveCharacter)
    (primeCharacterError x χ-primeCharacterError x χ.primitiveCharacter)
  rw [add_sub_cancel] at hn
  exact hn.trans (add_le_add_right (primeCharacterError_primitive_difference x hq χ) _)

end LargePrimeGaps
end OAI

end

open Finset Filter MeasureTheory
open scoped Topology

namespace GoldbachMajorArc

noncomputable section

def primeWeight (k : ℕ) : ℝ := if k.Prime then Real.log (k : ℝ) else 0

def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def primeSum (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n + 1), (primeWeight k : ℂ) * phase ((k : ℝ) * t)

private theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  push_cast
  congr 1
  ring

/-- The geometric sum in the rational-frequency approximation, with the same endpoints as the prime sum. -/
def kernel (n : ℕ) (β : ℝ) : ℂ := ∑ k ∈ range (n + 1), phase ((k : ℝ) * β)

def unitMean (q a : ℕ) : ℂ :=
  (∑ r ∈ (range q).filter (fun r => Nat.Coprime r q), phase ((r : ℝ) * ((a : ℝ) / q))) /
    (q.totient : ℂ)

def centerErrorTerm (r : ℝ) (A : ℂ) (k : ℕ) : ℂ :=
  (primeWeight k : ℂ) * phase ((k : ℝ) * r) - A

/-- The largest initial segment discrepancy at the center, through the last term k = n. -/
def prefixError (n : ℕ) (r : ℝ) (A : ℂ) : ℝ :=
  (range (n + 2)).sup' ⟨0, by simp⟩ (fun m => ‖∑ k ∈ range m, centerErrorTerm r A k‖)

private theorem prefix_le {m n : ℕ} (hm : m ≤ n + 1) (r : ℝ) (A : ℂ) :
    ‖∑ k ∈ range m, centerErrorTerm r A k‖ ≤ prefixError n r A :=
  Finset.le_sup' (fun m => ‖∑ k ∈ range m, centerErrorTerm r A k‖) (mem_range.mpr (by omega))

private theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private theorem phase_step (k : ℕ) (β : ℝ) :
    ‖phase (((k + 1 : ℕ) : ℝ) * β) - phase ((k : ℝ) * β)‖ ≤ 2 * Real.pi * |β| := by
  have shift : ((k + 1 : ℕ) : ℝ) * β = k * β + β := by push_cast; ring
  rw [shift, phase_add, ← mul_sub_one, norm_mul, norm_phase, one_mul]
  unfold phase
  rw [mul_comm _ Complex.I]
  calc
    _ ≤ ‖2 * Real.pi * β‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = _ := by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]

/-- Abel summation transports the finite initial segment discrepancies at r to a nearby frequency. -/
theorem shifted_sum_error (n : ℕ) (r β : ℝ) (A : ℂ) :
    ‖primeSum n (r + β) - A * kernel n β‖ ≤
      prefixError n r A * (1 + 2 * Real.pi * (n : ℝ) * |β|) := by
  let g := centerErrorTerm r A
  let v := fun k : ℕ => phase ((k : ℝ) * β)
  let D := prefixError n r A
  have hD : 0 ≤ D := (norm_nonneg _).trans (prefix_le (m := 0) (n := n) (by omega) r A)
  have expand : primeSum n (r + β) - A * kernel n β = ∑ k ∈ range (n + 1), v k * g k := by
    unfold primeSum kernel
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_add, phase_add]
    dsimp [v, g, centerErrorTerm]
    ring
  have habel := Finset.sum_range_by_parts (M := ℂ) v g (n + 1)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at habel
  have hfirst : ‖v n * ∑ k ∈ range (n + 1), g k‖ ≤ D := by
    rw [norm_mul, show ‖v n‖ = 1 from norm_phase _, one_mul]
    exact prefix_le le_rfl r A
  have htail : ‖∑ i ∈ range n, (v (i + 1) - v i) * ∑ k ∈ range (i + 1), g k‖ ≤
      (n : ℝ) * (2 * Real.pi * |β| * D) := by
    calc
      _ ≤ ∑ i ∈ range n, ‖(v (i + 1) - v i) * ∑ k ∈ range (i + 1), g k‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _i ∈ range n, 2 * Real.pi * |β| * D := by
        refine sum_le_sum fun i hi => ?_
        rw [norm_mul]
        exact mul_le_mul (phase_step i β) (prefix_le (by have := mem_range.mp hi; omega) r A)
          (norm_nonneg _) (by positivity)
      _ = _ := by simp
  rw [expand, habel]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ D + n * (2 * Real.pi * |β| * D) := add_le_add hfirst htail
    _ = _ := by dsimp [D]; ring

private theorem phase_nat (k : ℕ) : phase (k : ℝ) = 1 := by
  unfold phase
  convert Complex.exp_nat_mul_two_pi_mul_I k using 2
  push_cast
  ring

private theorem phase_modulo {q : ℕ} (hq : 0 < q) (k a : ℕ) :
    phase ((k : ℝ) * ((a : ℝ) / q)) = phase (((k % q : ℕ) : ℝ) * ((a : ℝ) / q)) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hk : (k : ℝ) = ((k % q : ℕ) : ℝ) + q * ((k / q : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div k q).symm
  have harg : (k : ℝ) * ((a : ℝ) / q) =
      ((k % q : ℕ) : ℝ) * ((a : ℝ) / q) + (((k / q * a : ℕ) : ℝ)) := by
    push_cast
    nth_rw 1 [hk]
    field_simp
  rw [harg, phase_add, phase_nat, mul_one]

/-- Logarithmic prime weight in one residue class for the initial segment 0 ≤ k < m. -/
def classMass (m q b : ℕ) : ℝ := ∑ k ∈ (range m).filter (fun k => k % q = b), primeWeight k

def classError (m q b : ℕ) : ℝ :=
  classMass m q b - if b.Coprime q then (m : ℝ) / q.totient else 0

/-- Exact expansion of the initial segment discrepancy at a rational center in progression errors. -/
theorem center_prefix_eq {q : ℕ} (hq : 0 < q) (a m : ℕ) :
    ∑ k ∈ range m, centerErrorTerm ((a : ℝ) / q) (unitMean q a) k =
      ∑ b ∈ range q, (classError m q b : ℂ) * phase ((b : ℝ) * ((a : ℝ) / q)) := by
  let e := fun k : ℕ => phase ((k : ℝ) * ((a : ℝ) / q))
  have masses : (∑ k ∈ range m, (primeWeight k : ℂ) * e k) =
      ∑ b ∈ range q, (classMass m q b : ℂ) * e b := by
    symm
    calc
      _ = ∑ b ∈ range q, ∑ k ∈ (range m).filter (fun k => k % q = b),
          (primeWeight k : ℂ) * e k := by
        refine sum_congr rfl fun b _ => ?_
        rw [classMass, Complex.ofReal_sum, sum_mul]
        refine sum_congr rfl fun k hk => ?_
        have he : e k = e b := by
          dsimp [e]
          rw [phase_modulo hq k a, (mem_filter.mp hk).2]
        rw [he]
      _ = _ := sum_fiberwise_of_maps_to (fun k _ => mem_range.mpr (Nat.mod_lt k hq)) _
  have model : (m : ℂ) * unitMean q a =
      ∑ b ∈ range q, (↑(if b.Coprime q then (m : ℝ) / q.totient else 0) : ℂ) * e b := by
    calc
      _ = ((m : ℂ) / q.totient) * ∑ b ∈ (range q).filter (fun b => b.Coprime q), e b := by
        unfold unitMean
        dsimp [e]
        ring
      _ = _ := by
        rw [mul_sum, sum_filter]
        refine sum_congr rfl fun b _ => ?_
        by_cases h : b.Coprime q
        · rw [ite_eq_left h, ite_eq_left h, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_natCast]
        · rw [ite_eq_right h, ite_eq_right h, Complex.ofReal_zero, zero_mul]
  change (∑ k ∈ range m, ((primeWeight k : ℂ) * e k - unitMean q a)) = _
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, masses, model, ← sum_sub_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [← sub_mul, classError, Complex.ofReal_sub]

/-- A useful bound even without a uniform prime number theorem in progressions. -/
theorem center_prefix_bound {q : ℕ} (hq : 0 < q) (a m : ℕ) :
    ‖∑ k ∈ range m, centerErrorTerm ((a : ℝ) / q) (unitMean q a) k‖ ≤
      ∑ b ∈ range q, |classError m q b| := by
  rw [center_prefix_eq hq]
  refine (norm_sum_le _ _).trans ?_
  apply sum_le_sum
  intro b _
  rw [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs]

end

end GoldbachMajorArc

namespace GoldbachMajorArc

open Finset Filter MeasureTheory
open OAI.LargePrimeGaps

noncomputable section

/-- The character form of Siegel–Walfisz gives a uniform bound for a reduced class.
The second term pays for replacing the character by its primitive character. -/
theorem progression_error (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → ∀ q b : ℕ, 0 < q → (q : ℝ) ≤ (Real.log x) ^ B →
        b < q → b.Coprime q →
        |residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q b - x / q.totient| ≤
          M * x * (Real.log x) ^ (-A) + (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log q := by
  obtain ⟨M, hM, x₀, hx₀, hχ⟩ := siegelWalfisz A B hA hB
  refine ⟨M, hM, x₀, hx₀, ?_⟩
  intro x hx q b hq hqlog hb hcop
  let : NeZero q := ⟨hq.ne'⟩
  have hchar (χ : DirichletCharacter ℂ q) :
      ‖primeCharacterError x χ‖ ≤
        M * x * (Real.log x) ^ (-A) + (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log q := by
    have hcond : (χ.conductor : ℝ) ≤ q := by
      exact_mod_cast Nat.le_of_dvd hq χ.conductor_dvd_level
    exact (primeCharacterError_le_primitive x hq χ).trans (add_le_add
      (hχ x hx χ.conductor (Nat.pos_of_ne_zero χ.conductor_ne_zero) (hcond.trans hqlog) χ.primitiveCharacter
        χ.primitiveCharacter_isPrimitive) (le_refl _))
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  apply (endpointClassError_le_character_sum x hq hb hcop).trans
  apply (div_le_iff₀ hφ).mpr
  calc
    _ ≤ ∑ _χ : DirichletCharacter ℂ q,
        (M * x * (Real.log x) ^ (-A) + (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log q) :=
      sum_le_sum fun χ _ => hchar χ
    _ = _ := by rw [sum_const, card_univ, hcard, nsmul_eq_mul, mul_comm]

private theorem primeWeight_le_mangoldt (k : ℕ) :
    primeWeight k ≤ ArithmeticFunction.vonMangoldt k := by
  by_cases hk : k.Prime
  · simp [primeWeight, hk, ArithmeticFunction.vonMangoldt_apply_prime hk]
  · simp [primeWeight, hk]

private theorem classMass_succ (N q b : ℕ) :
    classMass (N + 1) q b =
      ∑ k ∈ (Ioc 0 N).filter (fun k => k % q = b), primeWeight k := by
  rw [classMass, Nat.range_succ_eq_Icc_zero, sum_filter, sum_filter, ← add_sum_Ioc_eq_sum_Icc]
  · simp [primeWeight]
  · exact Nat.zero_le _

/-- Restriction to one class can discard no more prime-power mass than ψ(N) − θ(N). -/
theorem prime_power_correction (N q b : ℕ) :
    |classMass (N + 1) q b - residuePrefix ArithmeticFunction.vonMangoldt N q b| ≤
      Chebyshev.psi N - Chebyshev.theta N := by
  rw [classMass_succ, residuePrefix, residueSlice, abs_sub_comm, ← sum_sub_distrib,
    abs_of_nonneg (sum_nonneg fun k _ => sub_nonneg.mpr (primeWeight_le_mangoldt k))]
  have htotal : (∑ k ∈ Ioc 0 N, (ArithmeticFunction.vonMangoldt k - primeWeight k)) =
      Chebyshev.psi N - Chebyshev.theta N := by
    simp only [sum_sub_distrib, Chebyshev.psi, Chebyshev.theta, Nat.floor_natCast, sum_filter,
      primeWeight]
  rw [← htotal]
  apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
  exact fun k _ _ => sub_nonneg.mpr (primeWeight_le_mangoldt k)

/-- Siegel–Walfisz for the actual logarithmic prime weights, uniformly in reduced residue
classes. The additive terms account for nonprimitive characters and proper prime powers. -/
theorem prime_progression_error (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
      ∀ N q b : ℕ, x₀ ≤ N → 0 < q → (q : ℝ) ≤ (Real.log N) ^ B →
        b < q → b.Coprime q →
        |classMass (N + 1) q b - (N : ℝ) / q.totient| ≤
          M * N * (Real.log N) ^ (-A) + (Nat.log 2 N : ℝ) * Real.log q +
            2 * Real.sqrt N * Real.log N := by
  obtain ⟨M, hM, x₀, hx₀, h⟩ := progression_error A B hA hB
  refine ⟨M, hM, x₀, hx₀, ?_⟩
  intro N q b hN hq hlog hb hcop
  have he := h (N : ℝ) hN q b hq hlog hb hcop
  simp only [Nat.floor_natCast] at he
  have hpow := (prime_power_correction N q b).trans (Chebyshev.psi_sub_theta_le (hx₀.le.trans hN))
  exact (abs_sub_le _ (residuePrefix ArithmeticFunction.vonMangoldt N q b) _).trans
    ((add_le_add hpow he).trans_eq (add_comm _ _))

end
end GoldbachMajorArc

open Filter GoldbachMajorArc
open scoped Topology

private theorem logarithmicGrowth (k : ℕ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ n : ℕ in atTop, (Real.log n)^k ≤ (n : ℝ)^s := by
  have h : Tendsto (fun n : ℕ => (Real.log n)^k / (n : ℝ)^s) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_natCast] using
      ((isLittleO_log_rpow_rpow_atTop (k : ℝ) hs).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [(tendsto_order.mp h).2 1 zero_lt_one, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hp : (0 : ℝ) < n := by exact_mod_cast hn1
  simpa using (div_le_iff₀ (Real.rpow_pos_of_pos hp _)).mp hn.le

private theorem uniformAP (h b : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ q r : ℕ, 0 < q →
      (q : ℝ) ≤ (Real.log n)^h → r < q → r.Coprime q →
      |classMass (n+1) q r - (n : ℝ)/q.totient| ≤ C*(n:ℝ)/(Real.log n)^b := by
  obtain ⟨M,hM,x,hx,hs⟩ := prime_progression_error (b+1 : ℕ) (h+1 : ℕ) (by positivity) (by positivity)
  refine ⟨M+4, by linarith, ?_⟩
  have hl := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hl.eventually_ge_atTop 1,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop x,
    logarithmicGrowth (h+1+b) (s := 1) (by norm_num),
    logarithmicGrowth (b+1) (s := 1/2) (by norm_num)] with n hL hnx hnb hnroot q r hq hqh hr hcop
  change 1 ≤ Real.log n at hL
  change x ≤ (n : ℝ) at hnx
  have hn : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hlog : 0 < Real.log n := by linarith
  have hQ : (q : ℝ) ≤ (Real.log n)^(h+1) := hqh.trans (by
    rw [pow_succ]; exact le_mul_of_one_le_right (by positivity) hL)
  have he := hs n q r hnx hq (by simpa only [Real.rpow_natCast] using hQ) hr hcop
  rw [Real.rpow_neg hlog.le, Real.rpow_natCast, ← div_eq_mul_inv] at he
  apply he.trans
  have main : M * n / (Real.log n)^(b+1) ≤ M*n/(Real.log n)^b := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    rw [pow_succ]; exact le_mul_of_one_le_right (by positivity) hL
  have hnat := Real.natLog_le_logb n 2
  simp only [Nat.cast_ofNat,Real.logb] at hnat
  have h2 := Real.log_two_gt_d9
  have hnlog : (Nat.log 2 n : ℝ) ≤ 2 * Real.log n := hnat.trans ((div_le_iff₀ (by linarith)).mpr
    (by nlinarith only [mul_nonneg hlog.le (show 0 ≤ 2 * Real.log 2 - 1 by linarith)]))
  have hqlog := (Real.log_le_self (Nat.cast_nonneg q)).trans hqh
  have hq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have corr := mul_le_mul hnlog hqlog hq0 (by positivity)
  rw [Real.rpow_one] at hnb
  rw [← Real.sqrt_eq_rpow] at hnroot
  have ec : (Nat.log 2 n : ℝ)*Real.log q ≤ 2*n/(Real.log n)^b := by
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ ≤ (2 * Real.log n * (Real.log n)^h) * (Real.log n)^b := mul_le_mul_of_nonneg_right corr (by positivity)
      _ = 2 * (Real.log n)^(h+1+b) := by simp only [pow_add,pow_one]; ring
      _ ≤ _ := by linarith
  have er : 2 * Real.sqrt n * Real.log n ≤ 2*n/(Real.log n)^b := by
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ = 2 * Real.sqrt n * (Real.log n)^(b+1) := by rw [pow_succ]; ring
      _ ≤ 2 * Real.sqrt n * Real.sqrt n := mul_le_mul_of_nonneg_left hnroot (by positivity)
      _ = _ := by nlinarith only [Real.sq_sqrt hn.le]
  calc
    _ ≤ M*n/(Real.log n)^b + 2*n/(Real.log n)^b + 2*n/(Real.log n)^b :=
      by linarith only [main, ec, er]
    _ = _ := by ring

theorem PEqualNP.Outside.L_goldbach_coset_logrange_ap :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q=r); let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; ∀ h b : ℕ, ∃ C : ℝ, 0<C ∧ ∃ X : ℕ, ∀ n≥X, ∀ q : ℕ, 0<q → (q:ℝ) ≤ (Real.log (n:ℝ))^h → ∀ r<q, r.Coprime q → |A n q r - (n:ℝ)/(q.totient:ℝ)| ≤ C*(n:ℝ)/(Real.log (n:ℝ))^b := by
  intro F w A h b
  obtain ⟨C,hC,he⟩ := uniformAP h b
  obtain ⟨X,hX⟩ := eventually_atTop.mp he
  exact ⟨C,hC,X,fun n hn q hq hqh r hr hc => hX n hn q r hq hqh hr hc⟩

namespace Conjectures.TwinPrimes.PrimeSquareMinusTwoUpperSieve_aux

noncomputable section

namespace AP


/-! ### Definitions -/

private noncomputable def th (a n : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range (n+1)).filter (fun k => k % 8 = a),
    (if k.Prime then Real.log (k:ℝ) else 0)

private noncomputable def g (n : ℕ) : ℝ :=
  if n ≤ 1 then 1 else 1 / ((n:ℝ) * Real.log (n:ℝ))

private def u (i : ℕ) : ℝ := if i = 0 then 0 else 1

private noncomputable def E (a n : ℕ) : ℝ := th a n - (n:ℝ)/4

private noncomputable def e (a i : ℕ) : ℝ :=
  if i.Prime ∧ i % 8 = a then Real.log (i:ℝ) else 0

/-! ### Elementary facts about `g` -/

private lemma g_of_two {n : ℕ} (hn : 2 ≤ n) : g n = 1 / ((n:ℝ) * Real.log (n:ℝ)) := by
  unfold g; split_ifs with h; omega; rfl

private lemma g_one : g 1 = 1 := by simp [g]

private lemma g_zero : g 0 = 1 := by simp [g]

private lemma u_one : u 1 = 1 := by simp [u]

private lemma u_of_pos {i : ℕ} (hi : i ≠ 0) : u i = 1 := by simp [u, hi]

private lemma g_antitone_of_two {n : ℕ} (hn : 2 ≤ n) : g (n+1) ≤ g n := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hL0 : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hL1 : 0 < Real.log ((n+1:ℕ):ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n+1))
  have h1 : (n:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.le_succ n
  have h2 : Real.log (n:ℝ) ≤ Real.log ((n+1:ℕ):ℝ) := Real.log_le_log hn0 h1
  have hmono : (n:ℝ) * Real.log (n:ℝ) ≤ ((n+1:ℕ):ℝ) * Real.log ((n+1:ℕ):ℝ) :=
    mul_le_mul h1 h2 hL0.le (by positivity)
  rw [g_of_two (by omega), g_of_two hn]
  exact one_div_le_one_div_of_le (by positivity) hmono

private lemma g_antitone (i : ℕ) : g (i+1) ≤ g i := by
  rcases i with _ | _ | i
  · rw [g_zero, g_one]
  · have h : (1:ℝ) ≤ (2:ℝ) * Real.log 2 := by linarith [Real.log_two_gt_d9]
    rw [g_one, g_of_two (by norm_num)]
    exact (div_le_one (by positivity)).mpr h
  · exact g_antitone_of_two (by omega)

private lemma log_succ_sub_log_le (i : ℕ) (hi : 1 ≤ i) :
    Real.log ((i+1:ℕ):ℝ) - Real.log (i:ℝ) ≤ 1/(i:ℝ) := by
  have hcast : ((i+1:ℕ):ℝ) = (i:ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hi0 : (0:ℝ) < (i:ℝ) := by exact_mod_cast (by omega : 0 < i)
  have hx : (0:ℝ) < ((i:ℝ)+1)/(i:ℝ) := by positivity
  have h := Real.log_le_sub_one_of_pos hx
  rw [Real.log_div (by positivity) hi0.ne'] at h
  have h2 : ((i:ℝ)+1)/(i:ℝ) - 1 = 1/(i:ℝ) := by field_simp; ring
  linarith

private lemma log_succ_sub_log_ge (i : ℕ) (hi : 1 ≤ i) :
    1 ≤ ((i+1:ℕ):ℝ) * (Real.log ((i+1:ℕ):ℝ) - Real.log (i:ℝ)) := by
  have hcast : ((i+1:ℕ):ℝ) = (i:ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hi0 : (0:ℝ) < (i:ℝ) := by exact_mod_cast (by omega : 0 < i)
  have hx : (0:ℝ) < ((i:ℝ)+1)/(i:ℝ) := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hx
  have hinv : (((i:ℝ)+1)/(i:ℝ))⁻¹ = (i:ℝ)/((i:ℝ)+1) := by rw [inv_div]
  rw [hinv, Real.log_div (by positivity) hi0.ne'] at h
  have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ (i:ℝ)+1)
  have h3 : ((i:ℝ)+1) * (1 - (i:ℝ)/((i:ℝ)+1)) = 1 := by field_simp; ring
  linarith

private lemma log_succ_le_two_log (i : ℕ) (hi : 2 ≤ i) :
    Real.log ((i+1:ℕ):ℝ) ≤ 2 * Real.log (i:ℝ) := by
  have hcast : ((i+1:ℕ):ℝ) = (i:ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have h := log_succ_sub_log_le i (by omega)
  rw [hcast] at h
  have hiR : (2:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi
  have hlog2 : (1:ℝ)/2 ≤ Real.log (i:ℝ) := by
    have h1 := Real.log_two_gt_d9
    have h2 := Real.log_le_log (by norm_num : (0:ℝ) < 2) hiR
    linarith
  have h3 : (1:ℝ)/(i:ℝ) ≤ 1/2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hiR
  linarith

private lemma two_le_log {n : ℕ} (hn : 9 ≤ n) : 2 ≤ Real.log (n:ℝ) := by
  have h1 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
    have h : (2:ℝ) = ((2:ℕ):ℝ) * 1 := by norm_num
    rw [h, Real.exp_nat_mul]
  have h3 : (9:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have h4 : Real.exp 2 ≤ (n:ℝ) := by
    rw [h2]; nlinarith [Real.exp_nonneg 1]
  rw [← Real.log_exp 2]
  exact Real.log_le_log (Real.exp_pos 2) h4

private lemma eight_le_cube_of_two_le {L : ℝ} (h : 2 ≤ L) : 8 ≤ L^3 := by
  have h2 : 4 ≤ L^2 := by nlinarith
  have h3 : L^3 = L^2 * L := by ring
  rw [h3]; nlinarith

private lemma one_le_cube_of_two_le {L : ℝ} (h : 2 ≤ L) : 1 ≤ L^3 := by
  have := eight_le_cube_of_two_le h; linarith

private lemma one_le_log_of_three {i : ℕ} (hi : 3 ≤ i) : 1 ≤ Real.log (i:ℝ) := by
  have h3 : (3:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi
  have hexp := Real.exp_one_lt_d9
  have h := Real.log_le_log (Real.exp_pos 1) (by linarith : Real.exp 1 ≤ (i:ℝ))
  rw [Real.log_exp] at h
  exact h

private lemma g_ge_loglog {i : ℕ} (hi : 2 ≤ i) :
    Real.log (Real.log ((i+1:ℕ):ℝ)) - Real.log (Real.log (i:ℝ)) ≤ g i := by
  have hcast : ((i+1:ℕ):ℝ) = (i:ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hi0 : (0:ℝ) < (i:ℝ) := by exact_mod_cast (by omega : 0 < i)
  have hL0 : 0 < Real.log (i:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < i))
  have hL1 : 0 < Real.log ((i:ℝ)+1) := Real.log_pos (by linarith)
  have hd1 := log_succ_sub_log_le i (by omega)
  rw [hcast] at hd1
  have hlog : Real.log (Real.log ((i:ℝ)+1)) - Real.log (Real.log (i:ℝ)) =
      Real.log (1 + (Real.log ((i:ℝ)+1) - Real.log (i:ℝ)) / Real.log (i:ℝ)) := by
    rw [(Real.log_div hL1.ne' hL0.ne').symm]
    congr 1
    field_simp; ring
  have hd0 : 0 ≤ Real.log ((i:ℝ)+1) - Real.log (i:ℝ) := by
    have h := Real.log_le_log hi0 (by linarith : (i:ℝ) ≤ (i:ℝ)+1); linarith
  have ht0 : 0 ≤ (Real.log ((i:ℝ)+1) - Real.log (i:ℝ)) / Real.log (i:ℝ) := by positivity
  have hstep := Real.log_le_sub_one_of_pos
    (by linarith : (0:ℝ) < 1 + (Real.log ((i:ℝ)+1) - Real.log (i:ℝ)) / Real.log (i:ℝ))
  have hdiv : (Real.log ((i:ℝ)+1) - Real.log (i:ℝ)) / Real.log (i:ℝ) ≤
      1 / ((i:ℝ) * Real.log (i:ℝ)) := by
    rw [div_le_div_iff₀ hL0 (by positivity)]
    have h := mul_le_mul_of_nonneg_right hd1 (by positivity : (0:ℝ) ≤ (i:ℝ) * Real.log (i:ℝ))
    have h2 : (1/(i:ℝ)) * ((i:ℝ) * Real.log (i:ℝ)) = Real.log (i:ℝ) := by field_simp
    linarith
  rw [g_of_two hi, hlog]
  linarith

private lemma g_sub_le {i : ℕ} (hi : 2 ≤ i) :
    g i - g (i+1) ≤ 2 / ((i:ℝ)^2 * Real.log (i:ℝ)) := by
  have hcast : ((i+1:ℕ):ℝ) = (i:ℝ) + 1 := by push_cast; ring
  have hi0 : (0:ℝ) < (i:ℝ) := by exact_mod_cast (by omega : 0 < i)
  have hL0 : 0 < Real.log (i:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < i))
  have hL1 : 0 < Real.log ((i:ℝ)+1) := Real.log_pos (by linarith)
  have hL1ge : 1 ≤ Real.log ((i:ℝ)+1) := by
    have h := one_le_log_of_three (i := i+1) (by omega)
    rwa [hcast] at h
  have hd := log_succ_sub_log_le i (by omega)
  rw [hcast] at hd
  have hmul : (i:ℝ) * (Real.log ((i:ℝ)+1) - Real.log (i:ℝ)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hd hi0.le
    have h2 : (i:ℝ) * (1/(i:ℝ)) = 1 := by field_simp
    linarith
  have hkey : (i:ℝ) * (((i:ℝ)+1) * Real.log ((i:ℝ)+1) - (i:ℝ) * Real.log (i:ℝ)) ≤
      2 * ((i:ℝ)+1) * Real.log ((i:ℝ)+1) := by
    have h1 : (i:ℝ) * (((i:ℝ)+1) * Real.log ((i:ℝ)+1) - (i:ℝ) * Real.log (i:ℝ)) =
        (i:ℝ) * Real.log ((i:ℝ)+1) +
          (i:ℝ) * ((i:ℝ) * (Real.log ((i:ℝ)+1) - Real.log (i:ℝ))) := by ring
    have h2 := mul_le_mul_of_nonneg_left hmul hi0.le
    have h3 : (i:ℝ) * Real.log ((i:ℝ)+1) + (i:ℝ) ≤
        2 * ((i:ℝ)+1) * Real.log ((i:ℝ)+1) := by nlinarith
    linarith
  rw [g_of_two hi, g_of_two (by omega), hcast]
  have hpos3 : (0:ℝ) < (i:ℝ)^2 * Real.log (i:ℝ) := by positivity
  calc 1 / ((i:ℝ) * Real.log (i:ℝ)) - 1 / (((i:ℝ)+1) * Real.log ((i:ℝ)+1))
      = (((i:ℝ)+1) * Real.log ((i:ℝ)+1) - (i:ℝ) * Real.log (i:ℝ)) /
          ((i:ℝ) * Real.log (i:ℝ) * (((i:ℝ)+1) * Real.log ((i:ℝ)+1))) := by
        field_simp
    _ ≤ 2 / ((i:ℝ)^2 * Real.log (i:ℝ)) := by
        rw [div_le_div_iff₀ (by positivity) hpos3]
        have h := mul_le_mul_of_nonneg_left hkey (by positivity : (0:ℝ) ≤ (i:ℝ) * Real.log (i:ℝ))
        have hl : (i:ℝ) * Real.log (i:ℝ) * ((i:ℝ) * (((i:ℝ)+1) * Real.log ((i:ℝ)+1) -
            (i:ℝ) * Real.log (i:ℝ))) =
            (((i:ℝ)+1) * Real.log ((i:ℝ)+1) - (i:ℝ) * Real.log (i:ℝ)) *
              ((i:ℝ)^2 * Real.log (i:ℝ)) := by ring
        have hr : (i:ℝ) * Real.log (i:ℝ) * (2 * ((i:ℝ)+1) * Real.log ((i:ℝ)+1)) =
            2 * ((i:ℝ) * Real.log (i:ℝ) * (((i:ℝ)+1) * Real.log ((i:ℝ)+1))) := by ring
        linarith

private lemma tele_bound {i : ℕ} (hi : 2 ≤ i) :
    1 / ((i:ℝ) * (Real.log (i:ℝ))^2) ≤
      4 * (1 / Real.log (i:ℝ) - 1 / Real.log ((i+1:ℕ):ℝ)) := by
  have hcast : ((i+1:ℕ):ℝ) = (i:ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hi0 : (0:ℝ) < (i:ℝ) := by exact_mod_cast (by omega : 0 < i)
  have hL0 : 0 < Real.log (i:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < i))
  have hL1 : 0 < Real.log ((i:ℝ)+1) := Real.log_pos (by linarith)
  have hd := log_succ_sub_log_ge i (by omega)
  rw [hcast] at hd
  have hL1' := log_succ_le_two_log i hi
  rw [hcast] at hL1'
  have hnn : 0 ≤ Real.log ((i:ℝ)+1) - Real.log (i:ℝ) := by
    have h := Real.log_le_log hi0 (by linarith : (i:ℝ) ≤ (i:ℝ)+1); linarith
  have h1 : 1 ≤ (2:ℝ) * (i:ℝ) * (Real.log ((i:ℝ)+1) - Real.log (i:ℝ)) := by
    have h2 : ((i:ℝ)+1) ≤ 2 * (i:ℝ) := by
      have h' : (1:ℝ) ≤ (i:ℝ) := by exact_mod_cast (by omega)
      linarith
    have h3 : 0 ≤ (2 * (i:ℝ) - ((i:ℝ)+1)) * (Real.log ((i:ℝ)+1) - Real.log (i:ℝ)) :=
      mul_nonneg (by linarith) hnn
    nlinarith
  have hkey : Real.log ((i:ℝ)+1) ≤
      4 * (i:ℝ) * Real.log (i:ℝ) * (Real.log ((i:ℝ)+1) - Real.log (i:ℝ)) := by
    have h4 := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ 2 * Real.log (i:ℝ))
    have h5 : (2:ℝ) * Real.log (i:ℝ) * (2 * (i:ℝ) * (Real.log ((i:ℝ)+1) - Real.log (i:ℝ))) =
        4 * (i:ℝ) * Real.log (i:ℝ) * (Real.log ((i:ℝ)+1) - Real.log (i:ℝ)) := by ring
    linarith
  rw [div_sub_div (1:ℝ) (1:ℝ) hL0.ne' hL1.ne', ← mul_div_assoc]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h5 := mul_le_mul_of_nonneg_left hkey hL0.le
  have h6 : Real.log (i:ℝ) * (4 * (i:ℝ) * Real.log (i:ℝ) * (Real.log ((i:ℝ)+1) - Real.log (i:ℝ))) =
      4 * (Real.log ((i:ℝ)+1) - Real.log (i:ℝ)) * ((i:ℝ) * (Real.log (i:ℝ))^2) := by ring
  linarith

private lemma tail_term {C : ℝ} (hC : 0 ≤ C) {i : ℕ} (hi : 3 ≤ i) :
    C * (i:ℝ) / (Real.log (i:ℝ))^2 * (g i - g (i+1)) ≤
      8 * C * (1 / Real.log (i:ℝ) - 1 / Real.log ((i+1:ℕ):ℝ)) := by
  have hcast : ((i+1:ℕ):ℝ) = (i:ℝ) + 1 := by push_cast; ring
  have hi0 : (0:ℝ) < (i:ℝ) := by exact_mod_cast (by omega : 0 < i)
  have hL0 : 0 < Real.log (i:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < i))
  have hL0ge : 1 ≤ Real.log (i:ℝ) := one_le_log_of_three hi
  have hgs := g_sub_le (by omega : 2 ≤ i)
  have h1 := mul_le_mul_of_nonneg_left hgs (by positivity : (0:ℝ) ≤ C * (i:ℝ) / (Real.log (i:ℝ))^2)
  have h2 : C * (i:ℝ) / (Real.log (i:ℝ))^2 * (2 / ((i:ℝ)^2 * Real.log (i:ℝ))) =
      2 * C / ((i:ℝ) * (Real.log (i:ℝ))^3) := by field_simp
  have h3 : (2:ℝ) * C / ((i:ℝ) * (Real.log (i:ℝ))^3) ≤
      2 * C / ((i:ℝ) * (Real.log (i:ℝ))^2) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have : (Real.log (i:ℝ))^2 ≤ (Real.log (i:ℝ))^3 := by nlinarith
    nlinarith
  have h5 := tele_bound (by omega : 2 ≤ i)
  rw [hcast] at h5
  have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : (0:ℝ) ≤ 2 * C)
  have h7 : (2:ℝ) * C * (4 * (1 / Real.log (i:ℝ) - 1 / Real.log ((i:ℝ)+1))) =
      8 * C * (1 / Real.log (i:ℝ) - 1 / Real.log ((i:ℝ)+1)) := by ring
  have h8 : (2:ℝ) * C / ((i:ℝ) * (Real.log (i:ℝ))^2) =
      2 * C * (1 / ((i:ℝ) * (Real.log (i:ℝ))^2)) := by field_simp
  rw [hcast]
  linarith

/-! ### Abel summation -/

private lemma sum_e_eq_th (a N : ℕ) : ∑ i ∈ Finset.range (N+1), e a i = th a N := by
  unfold th
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hm : i % 8 = a
  · by_cases hp : i.Prime <;> simp [e, hm, hp]
  · simp [e, hm]

private lemma abel (a N : ℕ) :
    ∑ i ∈ Finset.range (N+1), g i * e a i =
      g N * th a N - ∑ i ∈ Finset.range N, (g (i+1) - g i) * th a i := by
  have h := Finset.sum_range_by_parts (M := ℝ) (R := ℝ) g (e a) (N + 1)
  rw [Nat.add_sub_cancel] at h
  simp only [smul_eq_mul] at h
  rw [h]
  simp only [sum_e_eq_th]

private lemma lhs_eq (a N : ℕ) (ha : a = 1 ∨ a = 3 ∨ a = 5 ∨ a = 7) :
    ∑ i ∈ Finset.range (N+1), g i * e a i =
      ∑ p ∈ (Finset.range (N+1)).filter (fun p => Nat.Prime p ∧ p % 8 = a), (1:ℝ)/(p:ℝ) := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i.Prime ∧ i % 8 = a
  · obtain ⟨hp, hm⟩ := h
    have hi3 : 3 ≤ i := by
      have h2 : i ≠ 2 := by
        intro h2; rw [h2] at hm; omega
      have := Nat.Prime.two_le hp; omega
    have hne : ¬ (i ≤ 1) := by omega
    have hlog : Real.log (i:ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < i))).ne'
    have hi : (i:ℝ) ≠ 0 := by exact_mod_cast (by omega : i ≠ 0)
    simp [e, hp, hm, g, hne]
    field_simp
  · simp [e, h]

private lemma sum_u (n : ℕ) (hn : 1 ≤ n) : ∑ i ∈ Finset.range n, u i = (n:ℝ) - 1 := by
  have h : ∀ i, u i = 1 - (if i = 0 then (1:ℝ) else 0) := by
    intro i; by_cases hi : i = 0 <;> simp [u, hi]
  simp_rw [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Finset.sum_ite_eq']
  have hmem : 0 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  rw [ite_eq_left_iff.mpr (fun h => absurd hmem h)]
  ring

private lemma main_part (N : ℕ) :
    (N:ℝ) * g N - ∑ i ∈ Finset.range N, (g (i+1) - g i) * (i:ℝ) =
      ∑ i ∈ Finset.range (N+1), g i * u i := by
  have h := Finset.sum_range_by_parts (M := ℝ) (R := ℝ) g u (N + 1)
  rw [Nat.add_sub_cancel] at h
  simp only [smul_eq_mul] at h
  rw [h]
  have h1 : ∑ i ∈ Finset.range (N+1), u i = (N:ℝ) := by
    rw [sum_u (N+1) (by omega)]; push_cast; ring
  have h2 : ∀ i, ∑ j ∈ Finset.range (i+1), u j = (i:ℝ) := by
    intro i; rw [sum_u (i+1) (by omega)]; push_cast; ring
  simp only [h1, h2]
  ring

private lemma main_lower {N : ℕ} (hN : 2 ≤ N) :
    Real.log (Real.log (N:ℝ)) ≤ ∑ i ∈ Finset.range (N+1), g i * u i := by
  have hf : ∀ i ∈ Finset.range (N+1),
      Real.log (Real.log ((i+1:ℕ):ℝ)) - Real.log (Real.log (i:ℝ)) ≤ g i * u i := by
    intro i _
    by_cases h0 : i = 0
    · subst h0; simp [u, g, Real.log_one, Real.log_zero]
    · rw [u_of_pos h0, mul_one]
      by_cases h1 : i = 1
      · subst h1
        have h11 : ((1+1:ℕ):ℝ) = (2:ℝ) := by push_cast; ring
        have hlog1 : Real.log (Real.log ((1:ℕ):ℝ)) = 0 := by
          rw [Nat.cast_one, Real.log_one, Real.log_zero]
        rw [h11, hlog1, sub_zero, g_one]
        have hpos : 0 < Real.log (2:ℝ) := by linarith [Real.log_two_gt_d9]
        have hle : Real.log (2:ℝ) ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
        have : Real.log (Real.log (2:ℝ)) ≤ 0 := by
          calc Real.log (Real.log (2:ℝ)) ≤ Real.log 1 := Real.log_le_log hpos hle
            _ = 0 := Real.log_one
        linarith
      · exact g_ge_loglog (by omega)
  have h1 : ∑ i ∈ Finset.range (N+1),
      (Real.log (Real.log ((i+1:ℕ):ℝ)) - Real.log (Real.log (i:ℝ))) =
      Real.log (Real.log ((N+1:ℕ):ℝ)) - Real.log (Real.log ((0:ℕ):ℝ)) :=
    Finset.sum_range_sub (fun i => Real.log (Real.log (i:ℝ))) (N+1)
  have hlog0 : Real.log (Real.log ((0:ℕ):ℝ)) = 0 := by
    rw [Nat.cast_zero, Real.log_zero, Real.log_zero]
  calc Real.log (Real.log (N:ℝ)) ≤ Real.log (Real.log ((N+1:ℕ):ℝ)) :=
        Real.log_le_log (Real.log_pos (by exact_mod_cast (by omega : 1 < N)))
          (Real.log_le_log (by exact_mod_cast (by omega : 0 < N)) (by exact_mod_cast Nat.le_succ N))
    _ ≤ Real.log (Real.log ((N+1:ℕ):ℝ)) - Real.log (Real.log ((0:ℕ):ℝ)) := by
        rw [hlog0]; linarith
    _ = ∑ i ∈ Finset.range (N+1),
          (Real.log (Real.log ((i+1:ℕ):ℝ)) - Real.log (Real.log (i:ℝ))) := h1.symm
    _ ≤ ∑ i ∈ Finset.range (N+1), g i * u i := Finset.sum_le_sum hf

/-! ### The arithmetic-progression input -/

private lemma ap_bound (a : ℕ) (ha : a = 1 ∨ a = 3 ∨ a = 5 ∨ a = 7) :
    ∃ C : ℝ, 0 < C ∧ ∃ X0 : ℕ, 9 ≤ X0 ∧ ∀ n : ℕ, X0 ≤ n →
      |th a n - (n:ℝ)/4| ≤ C * (n:ℝ) / (Real.log (n:ℝ))^2 := by
  obtain ⟨C, hC, X, hX⟩ := PEqualNP.Outside.L_goldbach_coset_logrange_ap 3 2
  refine ⟨C, hC, max X 9, le_max_right _ _, ?_⟩
  intro n hn
  have hn9 : 9 ≤ n := le_trans (le_max_right _ _) hn
  have hnX : X ≤ n := le_trans (le_max_left _ _) hn
  have hlog2 := two_le_log hn9
  have h8 : (8:ℝ) ≤ (Real.log (n:ℝ))^3 := eight_le_cube_of_two_le hlog2
  have htot : (8:ℕ).totient = 4 := by decide
  have h := hX n hnX 8 (by norm_num) h8 a (by omega)
    (by rcases ha with rfl | rfl | rfl | rfl <;> decide)
  rw [htot] at h
  exact h

/-! ### The theorem -/

theorem ap_recip_lower (a : ℕ) (ha : a = 1 ∨ a = 3 ∨ a = 5 ∨ a = 7) :
    ∃ K : ℝ, ∀ y : ℕ, 3 ≤ y →
      (1/4 : ℝ) * Real.log (Real.log (y : ℝ)) ≤
        K + ∑ p ∈ (Finset.range (y + 1)).filter (fun p => Nat.Prime p ∧ p % 8 = a),
          (1 : ℝ) / (p : ℝ) := by
  obtain ⟨C, hC, X0, hX0, hAP⟩ := ap_bound a ha
  let M0 : ℝ := (X0:ℝ) + 1
  refine ⟨max ((1/4) * Real.log (Real.log (X0:ℝ))) (M0 + 5 * C), ?_⟩
  intro y hy
  have hS0 : 0 ≤ ∑ p ∈ (Finset.range (y + 1)).filter (fun p => Nat.Prime p ∧ p % 8 = a),
      (1:ℝ) / (p:ℝ) := Finset.sum_nonneg (fun p _ => by positivity)
  by_cases hyX : X0 ≤ y
  · -- the large range: Abel summation
    have hy9 : 9 ≤ y := le_trans hX0 hyX
    have hS : (∑ p ∈ (Finset.range (y+1)).filter (fun p => Nat.Prime p ∧ p % 8 = a),
        (1:ℝ)/(p:ℝ)) =
        (1/4) * (∑ i ∈ Finset.range (y+1), g i * u i) + g y * E a y -
          ∑ i ∈ Finset.range y, (g (i+1) - g i) * E a i := by
      rw [← lhs_eq a y ha, abel a y]
      have hsplit : (∑ i ∈ Finset.range y, (g (i+1) - g i) * th a i) =
          (1/4) * (∑ i ∈ Finset.range y, (g (i+1) - g i) * (i:ℝ)) +
            ∑ i ∈ Finset.range y, (g (i+1) - g i) * E a i := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hE : th a i = (i:ℝ)/4 + E a i := by unfold E; ring
        rw [hE]; ring
      have hth : th a y = (y:ℝ)/4 + E a y := by unfold E; ring
      rw [hsplit, hth]
      linear_combination (1/4) * main_part y
    have hM : Real.log (Real.log (y:ℝ)) ≤ ∑ i ∈ Finset.range (y+1), g i * u i :=
      main_lower (by omega)
    -- the last term
    have hEy : |E a y| ≤ C * (y:ℝ) / (Real.log (y:ℝ))^2 := hAP y hyX
    have hgy : g y = 1 / ((y:ℝ) * Real.log (y:ℝ)) := g_of_two (by omega)
    have hgypos : 0 < g y := by
      rw [hgy]
      have := two_le_log hy9
      positivity
    have hbound : g y * |E a y| ≤ C := by
      calc g y * |E a y| ≤ g y * (C * (y:ℝ) / (Real.log (y:ℝ))^2) :=
            mul_le_mul_of_nonneg_left hEy hgypos.le
        _ = C / (Real.log (y:ℝ))^3 := by rw [hgy]; field_simp
        _ ≤ C := div_le_self hC.le (one_le_cube_of_two_le (two_le_log hy9))
    have hterm1 : -(C) ≤ g y * E a y := by
      have h1 : |g y * E a y| ≤ C := by rw [abs_mul, abs_of_pos hgypos]; exact hbound
      have h2 := neg_abs_le (g y * E a y)
      linarith
    -- the sum over i < y
    have hneg : (∑ i ∈ Finset.range y, (g i - g (i+1)) * E a i) =
        -(∑ i ∈ Finset.range y, (g (i+1) - g i) * E a i) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hsplit2 : (∑ i ∈ Finset.range y, (g i - g (i+1)) * E a i) =
        (∑ i ∈ Finset.range X0, (g i - g (i+1)) * E a i) +
          (∑ i ∈ Finset.Ico X0 y, (g i - g (i+1)) * E a i) := by
      rw [← Nat.Ico_zero_eq_range, ← Nat.Ico_zero_eq_range,
        ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le X0) hyX,
        Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive _ _ _)]
    have hhead : -(M0) ≤ ∑ i ∈ Finset.range X0, (g i - g (i+1)) * E a i := by
      have hper : ∀ i ∈ Finset.range X0, -(M0) * (g i - g (i+1)) ≤
          (g i - g (i+1)) * E a i := by
        intro i hi
        have hiX : i < X0 := Finset.mem_range.mp hi
        have hnn : 0 ≤ g i - g (i+1) := sub_nonneg.mpr (g_antitone i)
        have hE : -(M0) ≤ E a i := by
          have hthnn : 0 ≤ th a i := by
            unfold th
            refine Finset.sum_nonneg fun k _ => ?_
            by_cases hk : k.Prime
            · simp [hk]; exact Real.log_nonneg (by exact_mod_cast Nat.Prime.one_le hk)
            · simp [hk]
          have h1 : (i:ℝ)/4 ≤ M0 := by
            have h2 : (i:ℝ) ≤ (X0:ℝ) := by exact_mod_cast (le_of_lt hiX)
            have h3 : (0:ℝ) ≤ (X0:ℝ) := Nat.cast_nonneg X0
            dsimp [M0]; linarith
          unfold E; linarith
        have := mul_le_mul_of_nonneg_left hE hnn
        linarith
      have h1 : (-(M0)) * (∑ i ∈ Finset.range X0, (g i - g (i+1))) ≤
          ∑ i ∈ Finset.range X0, (g i - g (i+1)) * E a i := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum hper
      rw [Finset.sum_range_sub'] at h1
      have hgX0 : 0 ≤ g X0 := by rw [g_of_two (by omega)]; positivity
      have hM0 : 0 ≤ M0 := by dsimp [M0]; positivity
      have h2 : g 0 - g X0 ≤ 1 := by rw [g_zero]; linarith
      nlinarith
    have htel : (∑ i ∈ Finset.Ico X0 y,
        (1 / Real.log (i:ℝ) - 1 / Real.log ((i+1:ℕ):ℝ))) =
        1 / Real.log (X0:ℝ) - 1 / Real.log (y:ℝ) := by
      rw [Finset.sum_Ico_eq_sum_range]
      have h : ∀ k ∈ Finset.range (y - X0),
          (1 / Real.log ((X0 + k : ℕ):ℝ) - 1 / Real.log ((X0 + k + 1 : ℕ):ℝ)) =
          (1 / Real.log ((X0 + k : ℕ):ℝ) - 1 / Real.log ((X0 + (k+1) : ℕ):ℝ)) := by
        intro k _
        have hk : X0 + k + 1 = X0 + (k + 1) := by omega
        rw [hk]
      rw [Finset.sum_congr rfl h, Finset.sum_range_sub']
      have h1 : X0 + (y - X0) = y := Nat.add_sub_of_le hyX
      rw [h1]
      simp
    have htail : -(4 * C) ≤ ∑ i ∈ Finset.Ico X0 y, (g i - g (i+1)) * E a i := by
      have hper : ∀ i ∈ Finset.Ico X0 y,
          (-(8 * C)) * (1 / Real.log (i:ℝ) - 1 / Real.log ((i+1:ℕ):ℝ)) ≤
            (g i - g (i+1)) * E a i := by
        intro i hi
        have hiX : X0 ≤ i := (Finset.mem_Ico.mp hi).1
        have hi3 : 3 ≤ i := by omega
        have hEi : |E a i| ≤ C * (i:ℝ) / (Real.log (i:ℝ))^2 := hAP i hiX
        have hnn : 0 ≤ g i - g (i+1) := sub_nonneg.mpr (g_antitone i)
        have hstep : -(g i - g (i+1)) * |E a i| ≤ (g i - g (i+1)) * E a i := by
          have h := mul_le_mul_of_nonneg_left (neg_abs_le (E a i)) hnn
          linarith
        have h2 : (g i - g (i+1)) * |E a i| ≤
            C * (i:ℝ) / (Real.log (i:ℝ))^2 * (g i - g (i+1)) := by
          have h := mul_le_mul_of_nonneg_left hEi hnn
          linarith
        have h3 := tail_term hC.le hi3
        linarith
      have hsum : (-(8 * C)) * (∑ i ∈ Finset.Ico X0 y,
          (1 / Real.log (i:ℝ) - 1 / Real.log ((i+1:ℕ):ℝ))) ≤
          ∑ i ∈ Finset.Ico X0 y, (g i - g (i+1)) * E a i := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum hper
      rw [htel] at hsum
      have hX0log : 2 ≤ Real.log (X0:ℝ) := two_le_log hX0
      have h1 : 1 / Real.log (X0:ℝ) ≤ 1/2 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hX0log
      have h2 : 0 < 1 / Real.log (y:ℝ) := by
        have := two_le_log hy9; positivity
      have h3 : 1 / Real.log (X0:ℝ) - 1 / Real.log (y:ℝ) ≤ 1/2 := by linarith
      have h4 := mul_le_mul_of_nonpos_left h3 (by linarith : (-(8*C) : ℝ) ≤ 0)
      linarith
    have hterm2 : -(M0 + 4 * C) ≤ ∑ i ∈ Finset.range y, (g i - g (i+1)) * E a i := by
      rw [hsplit2]; linarith
    have h3 : -(M0 + 4 * C) ≤ -(∑ i ∈ Finset.range y, (g (i+1) - g i) * E a i) := by
      rw [← hneg]; exact hterm2
    have h4 : (1/4) * Real.log (Real.log (y:ℝ)) ≤
        (1/4) * (∑ i ∈ Finset.range (y+1), g i * u i) :=
      mul_le_mul_of_nonneg_left hM (by norm_num)
    have hfinal : (1/4) * Real.log (Real.log (y:ℝ)) ≤
        (M0 + 5 * C) + ∑ p ∈ (Finset.range (y+1)).filter (fun p => Nat.Prime p ∧ p % 8 = a),
          (1:ℝ)/(p:ℝ) := by
      linarith [hS]
    linarith [le_max_right ((1/4) * Real.log (Real.log (X0:ℝ))) (M0 + 5 * C)]
  · have hlog : Real.log (Real.log (y:ℝ)) ≤ Real.log (Real.log (X0:ℝ)) := by
      apply Real.log_le_log
      · exact Real.log_pos (by exact_mod_cast (by omega : 1 < y))
      · exact Real.log_le_log (by exact_mod_cast (by omega : 0 < y))
          (by exact_mod_cast (by omega : y ≤ X0))
    linarith [le_max_left ((1/4) * Real.log (Real.log (X0:ℝ))) (M0 + 5 * C)]


end AP

open scoped BigOperators
open Finset
open Conjectures.TwinPrimes.CofactorTwoLinearSieve_aux.OAI.Problem337

/-- Residue classes removed by the sieve for `r * (r^2 - 2)`. -/
def SqRoot (d : ℕ) :=
  {x : ZMod d // x * (x ^ 2 - 2) = 0}

/-- Local number of roots of `x * (x^2 - 2)` modulo `d`. -/
def sqRootCount (d : ℕ) : ℕ :=
  Nat.card (SqRoot d)

instance sqRootFintype (d : ℕ) [NeZero d] : Fintype (SqRoot d) :=
  inferInstanceAs (Fintype {x : ZMod d // x * (x ^ 2 - 2) = 0})

instance sqRootNonempty (d : ℕ) : Nonempty (SqRoot d) :=
  ⟨⟨0, by simp⟩⟩

/-- The Chinese remainder theorem separates the local root conditions. -/
def sqRootEquiv (a b : ℕ) (hab : a.Coprime b) :
    SqRoot (a * b) ≃ SqRoot a × SqRoot b := by
  let e := ZMod.chineseRemainder hab
  apply (Equiv.subtypeEquiv e.toEquiv ?_).trans Equiv.subtypeProdEquivProd
  intro x
  change x * ((x : ZMod (a * b)) ^ 2 - 2) = 0 ↔
    (e x).1 * ((e x).1 ^ 2 - 2) = 0 ∧ (e x).2 * ((e x).2 ^ 2 - 2) = 0
  have h := e.injective.eq_iff (a := x * ((x : ZMod (a * b)) ^ 2 - 2)) (b := 0)
  rw [map_mul, map_sub, map_pow, map_ofNat, map_zero] at h
  constructor
  · intro hx
    have hz : (e x) * ((e x) ^ 2 - 2) = 0 := h.mpr hx
    constructor
    · have h1 := congrArg Prod.fst hz
      simpa using h1
    · have h2 := congrArg Prod.snd hz
      simpa using h2
  · rintro ⟨h1, h2⟩
    apply h.mp
    ext
    · simpa using h1
    · simpa using h2

theorem sqRootCount_mul (a b : ℕ) (hab : a.Coprime b) :
    sqRootCount (a * b) = sqRootCount a * sqRootCount b := by
  unfold sqRootCount
  rw [Nat.card_congr (sqRootEquiv a b hab), Nat.card_prod]

@[simp] theorem sqRootCount_one : sqRootCount 1 = 1 := by
  unfold sqRootCount SqRoot
  have e : {x : ZMod 1 // x * (x ^ 2 - 2) = 0} ≃ ZMod 1 :=
    Equiv.subtypeUnivEquiv (fun x => Subsingleton.elim _ _)
  rw [Nat.card_congr e, Nat.card_zmod]

theorem sqRootCount_pos (d : ℕ) [NeZero d] : 0 < sqRootCount d := Nat.card_pos

private lemma zmod_two_eq_zero_iff (p : ℕ) : (2 : ZMod p) = 0 ↔ p ∣ 2 := by
  constructor
  · intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by simpa using h
    exact (ZMod.natCast_eq_zero_iff 2 p).mp h'
  · intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff 2 p).mpr h
    simpa using h'

private lemma prime_eq_two_of_two_dvd {p : ℕ} (hp : p.Prime) (hd : 2 ∣ p) : p = 2 := by
  rcases hp.eq_one_or_self_of_dvd 2 hd with h | h
  · omega
  · exact h.symm

/-- At an odd prime the roots are zero and the two square roots of two, when they exist. -/
theorem sqRootCount_prime (p : ℕ) (hp : p.Prime) :
    sqRootCount p = if p = 2 then 1 else (if p % 8 = 1 ∨ p % 8 = 7 then 3 else 1) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard0 : sqRootCount p =
      (Finset.univ.filter (fun x : ZMod p => x * (x ^ 2 - 2) = 0)).card := by
    unfold sqRootCount SqRoot
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard0]
  by_cases h2 : p = 2
  · subst h2
    have hz : (2 : ZMod 2) = 0 := by
      have hz' : ((2 : ℕ) : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff 2 2).mpr (dvd_refl 2)
      simpa using hz'
    have hfilter : (Finset.univ.filter (fun x : ZMod 2 => x * (x ^ 2 - 2) = 0)) = {0} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [hz, sub_zero]
      constructor
      · intro h
        rcases mul_eq_zero.mp h with h0 | h0
        · exact h0
        · exact sq_eq_zero_iff.mp h0
      · rintro rfl
        rw [zero_mul]
    rw [hfilter]
    norm_num
  · have hodd : ¬ (2 ∣ p) := fun hd => h2 (prime_eq_two_of_two_dvd hp hd)
    have htwo : (2 : ZMod p) ≠ 0 := by
      intro h
      have hd : p ∣ 2 := (zmod_two_eq_zero_iff p).mp h
      have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
      have := hp.two_le
      exact h2 (by omega)
    have hsplit : (Finset.univ.filter (fun x : ZMod p => x * (x ^ 2 - 2) = 0)) =
        insert 0 (Finset.univ.filter (fun x : ZMod p => x ^ 2 = 2)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro h
        rcases mul_eq_zero.mp h with h0 | h0
        · exact Or.inl h0
        · exact Or.inr (sub_eq_zero.mp h0)
      · rintro (rfl | h)
        · rw [zero_mul]
        · exact mul_eq_zero.mpr (Or.inr (sub_eq_zero.mpr h))
    have h0notmem : (0 : ZMod p) ∉ (Finset.univ.filter (fun x : ZMod p => x ^ 2 = 2)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro h
      have h' : (0 : ZMod p) ^ 2 = (2 : ZMod p) := h
      have h'' : (0 : ZMod p) = (2 : ZMod p) := by simpa using h'
      exact htwo h''.symm
    have hcount : (Finset.univ.filter (fun x : ZMod p => x * (x ^ 2 - 2) = 0)).card =
        1 + (Finset.univ.filter (fun x : ZMod p => x ^ 2 = 2)).card := by
      rw [hsplit, Finset.card_insert_of_notMem h0notmem]
      omega
    rw [hcount]
    have hmododd : p % 8 % 2 = 1 := by omega
    have hmodlt : p % 8 < 8 := Nat.mod_lt p (by norm_num)
    have hres : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
    have hisq : IsSquare (2 : ZMod p) ↔ p % 8 ≠ 3 ∧ p % 8 ≠ 5 := by
      have h := FiniteField.isSquare_two_iff (F := ZMod p)
      rwa [ZMod.card p] at h
    by_cases hsq2 : IsSquare (2 : ZMod p)
    · have hmod : p % 8 ≠ 3 ∧ p % 8 ≠ 5 := hisq.mp hsq2
      have hfinal : p % 8 = 1 ∨ p % 8 = 7 := by omega
      rw [if_neg h2, if_pos hfinal]
      obtain ⟨r, hr0⟩ := hsq2
      have hr : r ^ 2 = 2 := by rw [sq]; exact hr0.symm
      have hrne : r ≠ 0 := by
        intro h
        have h1 : (0 : ZMod p) ^ 2 = (2 : ZMod p) := by rw [← h]; exact hr
        have h2' : (0 : ZMod p) = (2 : ZMod p) := by simpa using h1
        exact htwo h2'.symm
      have hreq : (Finset.univ.filter (fun x : ZMod p => x ^ 2 = 2)) = {r, -r} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · intro hx
          have hfac : (x - r) * (x + r) = 0 := by
            calc (x - r) * (x + r) = x ^ 2 - r ^ 2 := by ring
              _ = 0 := by rw [hx, hr]; ring
          rcases mul_eq_zero.mp hfac with h1 | h1
          · exact Or.inl (sub_eq_zero.mp h1)
          · exact Or.inr (eq_neg_of_add_eq_zero_left h1)
        · rintro (rfl | rfl)
          · exact hr
          · rw [neg_sq]; exact hr
      rw [hreq]
      have hne : r ≠ -r := by
        intro h
        have hsum : (2 : ZMod p) * r = 0 := by
          have h1 : r + r = -r + r := congrArg (fun t => t + r) h
          have h2 : r + r = 0 := by rw [h1, neg_add_cancel]
          linear_combination h2
        rcases mul_eq_zero.mp hsum with h1 | h1
        · exact htwo h1
        · exact hrne h1
      rw [Finset.card_pair hne]
    · have hmod : ¬ (p % 8 ≠ 3 ∧ p % 8 ≠ 5) := fun hh => hsq2 (hisq.mpr hh)
      have hfinal : ¬ (p % 8 = 1 ∨ p % 8 = 7) := by omega
      rw [if_neg h2, if_neg hfinal]
      have hemp : (Finset.univ.filter (fun x : ZMod p => x ^ 2 = 2)) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        exact hsq2 ⟨x, by rw [← sq]; exact hx.symm⟩
      rw [hemp]
      norm_num


theorem sqRootCount_prime_le_three (p : ℕ) (hp : p.Prime) : sqRootCount p ≤ 3 := by
  rw [sqRootCount_prime p hp]
  split_ifs <;> omega

theorem sqRootCount_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    sqRootCount (∏ p ∈ s, p) = ∏ p ∈ s, sqRootCount p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      have hpp := hs p (Finset.mem_insert_self p s)
      have hsp : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
      have hcop : p.Coprime (∏ q ∈ s, q) := by
        apply Nat.Coprime.prod_right
        intro q hq
        apply (Nat.coprime_primes hpp (hsp q hq)).mpr
        intro heq
        exact hp (heq ▸ hq)
      rw [Finset.prod_insert hp, sqRootCount_mul p _ hcop, ih hsp, Finset.prod_insert hp]

theorem sqRootCount_squarefree (d : ℕ) (hd : Squarefree d) :
    sqRootCount d = ∏ p ∈ d.primeFactors, sqRootCount p := by
  calc
    sqRootCount d = sqRootCount (∏ p ∈ d.primeFactors, p) := by
          rw [Nat.prod_primeFactors_of_squarefree hd]
    _ = ∏ p ∈ d.primeFactors, sqRootCount p :=
      sqRootCount_prod_primes d.primeFactors (fun p hp => (Nat.mem_primeFactors.mp hp).1)

theorem sqRootCount_le_three_pow (d : ℕ) (hd : Squarefree d) :
    sqRootCount d ≤ 3 ^ d.primeFactors.card := by
  rw [sqRootCount_squarefree d hd]
  calc
    _ ≤ ∏ _p ∈ d.primeFactors, 3 := by
      apply Finset.prod_le_prod
      intro p hp
      exact sqRootCount_prime_le_three p (Nat.mem_primeFactors.mp hp).1
    _ = 3 ^ d.primeFactors.card := by
      rw [Finset.prod_const]

/-- Reduction modulo the least common multiple embeds the roots. -/
def sqRootLCMEmbedding (a b : ℕ) :
    SqRoot (a.lcm b) ↪ SqRoot a × SqRoot b := by
  let e : ZMod (a.lcm b) →+* ZMod a × ZMod b :=
    ZMod.castHom (dvd_refl (a.lcm b)) _
  have einj : Function.Injective e := ZMod.castHom_injective _
  have he (x : SqRoot (a.lcm b)) :
      (e x.val).1 * ((e x.val).1 ^ 2 - 2) = 0 ∧
        (e x.val).2 * ((e x.val).2 ^ 2 - 2) = 0 := by
    have h := congrArg e x.property
    have h' : (e x.val) * ((e x.val) ^ 2 - 2) = 0 := by
      rw [map_mul, map_sub, map_pow, map_ofNat, map_zero] at h
      exact h
    exact ⟨by have h1 := congrArg Prod.fst h'; simpa using h1,
      by have h2 := congrArg Prod.snd h'; simpa using h2⟩
  refine ⟨fun x => (⟨(e x.val).1, (he x).1⟩, ⟨(e x.val).2, (he x).2⟩), ?_⟩
  intro x y hxy
  apply Subtype.ext
  apply einj
  apply Prod.ext
  · exact congrArg (fun z : SqRoot a × SqRoot b => z.1.val) hxy
  · exact congrArg (fun z : SqRoot a × SqRoot b => z.2.val) hxy

theorem sqRootCount_lcm_le (a b : ℕ) [NeZero a] [NeZero b] :
    sqRootCount (a.lcm b) ≤ sqRootCount a * sqRootCount b := by
  unfold sqRootCount
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective (sqRootLCMEmbedding a b)
    (sqRootLCMEmbedding a b).injective

/-- The exact finite local root density, normalized as an arithmetic function. -/
def sqDensity : ArithmeticFunction ℝ where
  toFun d := (sqRootCount d : ℝ) / (d : ℝ)
  map_zero' := by simp

@[simp] theorem sqDensity_apply (d : ℕ) :
    sqDensity d = (sqRootCount d : ℝ) / (d : ℝ) := rfl

theorem sqDensity_isMultiplicative : sqDensity.IsMultiplicative := by
  constructor
  · simp
  · intro a b hab
    simp only [sqDensity_apply, sqRootCount_mul a b hab, Nat.cast_mul, mul_div_mul_comm]

theorem sqDensity_prime (p : ℕ) (hp : p.Prime) :
    sqDensity p = ((if p = 2 then 1 else (if p % 8 = 1 ∨ p % 8 = 7 then 3 else 1) : ℕ) : ℝ) /
      (p : ℝ) := by
  rw [sqDensity_apply, sqRootCount_prime p hp]

theorem sqDensity_prime_pos (p : ℕ) (hp : p.Prime) : 0 < sqDensity p := by
  rw [sqDensity_apply]
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h := sqRootCount_pos p
  have hd : (0 : ℝ) < p := by exact_mod_cast hp.pos
  positivity

theorem sqDensity_prime_lt_one (p : ℕ) (hp : p.Prime) : sqDensity p < 1 := by
  rw [sqDensity_apply, div_lt_one (by exact_mod_cast hp.pos)]
  have h := sqRootCount_prime p hp
  have hlt : sqRootCount p < p := by
    by_cases h2 : p = 2
    · have h1 : sqRootCount p = 1 := by rw [h, if_pos h2]
      rw [h1, h2]
      decide
    · by_cases h8 : p % 8 = 1 ∨ p % 8 = 7
      · have h3 : sqRootCount p = 3 := by rw [h, if_neg h2, if_pos h8]
        rw [h3]
        by_contra hle
        have hsmall : p = 2 ∨ p = 3 := by
          have := hp.two_le
          omega
        rcases hsmall with rfl | rfl
        · revert h8; decide
        · revert h8; decide
      · have h1 : sqRootCount p = 1 := by rw [h, if_neg h2, if_neg h8]
        rw [h1]
        exact hp.one_lt
  exact_mod_cast hlt

/-- The multiplicity-preserving sieve for the quadratic square-minus-two sequence. -/
def sqSieve (U y : ℕ) : BoundingSieve :=
  PrimePairSieve.imageSieve (Finset.Ioc U (2 * U)) (fun r => r * (r ^ 2 - 2))
    (primorial y) (squarefree_primorial y) sqDensity sqDensity_isMultiplicative
    (fun p hp _ => sqDensity_prime_pos p hp)
    (fun p hp _ => sqDensity_prime_lt_one p hp)

theorem sqSieve_multSum (U y d : ℕ) :
    (sqSieve U y).multSum d =
      (((Finset.Ioc U (2 * U)).filter (fun r => d ∣ r * (r ^ 2 - 2))).card : ℝ) :=
  PrimePairSieve.imageSieve_multSum (Finset.Ioc U (2 * U)) (fun r => r * (r ^ 2 - 2))
    (primorial y) (squarefree_primorial y) sqDensity sqDensity_isMultiplicative
    (fun p hp _ => sqDensity_prime_pos p hp) (fun p hp _ => sqDensity_prime_lt_one p hp) d

theorem sqSieve_siftedSum (U y : ℕ) :
    (sqSieve U y).siftedSum =
      (((Finset.Ioc U (2 * U)).filter
        (fun r => (primorial y).Coprime (r * (r ^ 2 - 2)))).card : ℝ) :=
  PrimePairSieve.imageSieve_siftedSum (Finset.Ioc U (2 * U)) (fun r => r * (r ^ 2 - 2))
    (primorial y) (squarefree_primorial y) sqDensity sqDensity_isMultiplicative
    (fun p hp _ => sqDensity_prime_pos p hp) (fun p hp _ => sqDensity_prime_lt_one p hp)

theorem sqSieve_totalMass (U y : ℕ) : (sqSieve U y).totalMass = (U : ℝ) := by
  have h : (sqSieve U y).totalMass = (((Finset.Ioc U (2 * U)).card : ℕ) : ℝ) := rfl
  rw [h, Nat.card_Ioc]
  have : 2 * U - U = U := by omega
  rw [this]

theorem sqSieve_rem (U y d : ℕ) :
    (sqSieve U y).rem d =
      (((Finset.Ioc U (2 * U)).filter (fun r => d ∣ r * (r ^ 2 - 2))).card : ℝ) -
        sqDensity d * (U : ℝ) := by
  have hm := sqSieve_multSum U y d
  have ht := sqSieve_totalMass U y
  have hnu : (sqSieve U y).nu d = sqDensity d := rfl
  unfold BoundingSieve.rem
  rw [hm, ht, hnu]

/-- Divisibility by the polynomial value is a residue condition. -/
theorem dvd_iff_sqRoot (d r : ℕ) [NeZero d] (hr : 2 ≤ r) :
    d ∣ r * (r ^ 2 - 2) ↔ (r : ZMod d) * ((r : ZMod d) ^ 2 - 2) = 0 := by
  have hcast : ((r * (r ^ 2 - 2) : ℕ) : ZMod d) = (r : ZMod d) * ((r : ZMod d) ^ 2 - 2) := by
    rw [Nat.cast_mul, Nat.cast_sub (by nlinarith), Nat.cast_pow, Nat.cast_ofNat]
  rw [← hcast, ZMod.natCast_eq_zero_iff]

theorem sqSieve_rem_bound (U y d : ℕ) [NeZero d] (hU : 1 ≤ U) :
    |(sqSieve U y).rem d| ≤ sqRootCount d := by
  classical
  rw [sqSieve_rem]
  have hI : Finset.Ioc U (2 * U) = Finset.Ico (U + 1) ((U + 1) + U) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have hfilt : (Finset.Ioc U (2 * U)).filter (fun r => d ∣ r * (r ^ 2 - 2)) =
      (Finset.Ico (U + 1) ((U + 1) + U)).filter
        (fun r : ℕ => (r : ZMod d) * ((r : ZMod d) ^ 2 - 2) = 0) := by
    rw [← hI]
    apply Finset.filter_congr
    intro r hr
    have hr2 : 2 ≤ r := by have := (Finset.mem_Ioc.mp hr).1; omega
    exact dvd_iff_sqRoot d r hr2
  have hcard : (((Finset.Ioc U (2 * U)).filter (fun r => d ∣ r * (r ^ 2 - 2))).card : ℝ) =
      (((Finset.Ico (U + 1) ((U + 1) + U)).filter
        (fun r : ℕ => (r : ZMod d) * ((r : ZMod d) ^ 2 - 2) = 0)).card : ℝ) := by
    rw [hfilt]
  rw [hcard]
  have hcount : sqRootCount d =
      (Finset.univ.filter (fun x : ZMod d => x * (x ^ 2 - 2) = 0)).card := by
    unfold sqRootCount SqRoot
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hz := zmod_predicate_Ico_discrepancy d
    (fun x : ZMod d => x * (x ^ 2 - 2) = 0) (U + 1) U
  have hgoal :
      (((Finset.Ico (U + 1) ((U + 1) + U)).filter
        (fun r : ℕ => (r : ZMod d) * ((r : ZMod d) ^ 2 - 2) = 0)).card : ℝ) -
          sqDensity d * (U : ℝ) =
      (((Finset.Ico (U + 1) ((U + 1) + U)).filter
        (fun r : ℕ => (r : ZMod d) * ((r : ZMod d) ^ 2 - 2) = 0)).card : ℝ) -
          (U : ℝ) * (sqRootCount d : ℝ) / (d : ℝ) := by
    rw [sqDensity_apply]
    ring
  rw [hgoal, hcount]
  exact hz

/-- The factorizable remainder envelope with base three. -/
theorem sqSieve_rem_lcm_bound (U y : ℕ) (hU : 1 ≤ U)
    (a : ℕ) (ha : a ∈ (primorial y).divisors) (b : ℕ) (hb : b ∈ (primorial y).divisors) :
    |(sqSieve U y).rem (Nat.lcm a b)| ≤
      (3 : ℝ) ^ a.primeFactors.card * (3 : ℝ) ^ b.primeFactors.card := by
  let : NeZero a := ⟨(Nat.pos_of_mem_divisors ha).ne'⟩
  let : NeZero b := ⟨(Nat.pos_of_mem_divisors hb).ne'⟩
  let : NeZero (Nat.lcm a b) := ⟨Nat.lcm_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  have ha2 := sqRootCount_le_three_pow a
    ((squarefree_primorial y).squarefree_of_dvd (Nat.dvd_of_mem_divisors ha))
  have hb2 := sqRootCount_le_three_pow b
    ((squarefree_primorial y).squarefree_of_dvd (Nat.dvd_of_mem_divisors hb))
  calc
    _ ≤ (sqRootCount (Nat.lcm a b) : ℝ) := sqSieve_rem_bound U y _ hU
    _ ≤ (sqRootCount a : ℝ) * sqRootCount b := by
      exact_mod_cast sqRootCount_lcm_le a b
    _ ≤ _ := by exact_mod_cast Nat.mul_le_mul ha2 hb2


/-- The optimal weights have a logarithmically bounded weighted mass with base three. -/
theorem optimalWeight_primeFactor_mass_le_three (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    (∑ d ∈ s.prodPrimes.divisors, |SelbergOptimal.optimalWeight s z d| *
      (3 : ℝ) ^ d.primeFactors.card) ≤ (z : ℝ) * (1 + Real.log z) ^ 3 := by
  calc
    _ ≤ ∑ d ∈ s.prodPrimes.divisors,
        if d ≤ z then (3 : ℝ) ^ d.primeFactors.card else 0 := by
      apply sum_le_sum
      intro d hd
      by_cases hdz : d ≤ z
      · rw [ite_eq_left hdz]
        have hw : |SelbergOptimal.optimalWeight s z d| ≤ 1 := by
          rw [SelbergOptimal.optimalWeight_formula s z d (Nat.dvd_of_mem_divisors hd)]
          convert SelbergOptimal.abs_normalized_complement_le_one s hz
            (Nat.dvd_of_mem_divisors hd) using 1
          unfold SelbergOptimal.complementNormalizer
          congr 1
          ring
        simpa using mul_le_mul_of_nonneg_right hw
          (by positivity : 0 ≤ (3 : ℝ) ^ d.primeFactors.card)
      · rw [ite_eq_right hdz, SelbergOptimal.optimalWeight_eq_zero_of_lt s (lt_of_not_ge hdz)]
        simp
    _ = ∑ d ∈ s.prodPrimes.divisors.filter (fun d => d ≤ z),
        (3 : ℝ) ^ d.primeFactors.card := (sum_filter _ _).symm
    _ ≤ _ := SelbergError.sum_squarefree_pow_le _ 3 z
      (fun d hd => s.squarefree_of_mem_divisors_prodPrimes (mem_filter.mp hd).1)
      (by
        intro d hd
        obtain ⟨hdP, hdz⟩ := mem_filter.mp hd
        exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdP, hdz⟩)

/-- A dimension-three local remainder envelope gives an explicit logarithmic error. -/
theorem errSum_optimalWeight_le_log_three (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z)
    (hrem : ∀ a ∈ s.prodPrimes.divisors, ∀ b ∈ s.prodPrimes.divisors,
      |s.rem (Nat.lcm a b)| ≤
        (3 : ℝ) ^ a.primeFactors.card * (3 : ℝ) ^ b.primeFactors.card) :
    s.errSum (BoundingSieve.lambdaSquared (SelbergOptimal.optimalWeight s z)) ≤
      (z : ℝ) ^ 2 * (1 + Real.log z) ^ 6 := by
  calc
    _ ≤ (∑ d ∈ s.prodPrimes.divisors, |SelbergOptimal.optimalWeight s z d| *
        (3 : ℝ) ^ d.primeFactors.card) ^ 2 :=
      SelbergError.errSum_lambdaSquared_le_sq s (SelbergOptimal.optimalWeight s z)
        (fun d => (3 : ℝ) ^ d.primeFactors.card) hrem
    _ ≤ ((z : ℝ) * (1 + Real.log z) ^ 3) ^ 2 :=
      pow_le_pow_left₀ (sum_nonneg (by intros; positivity))
        (optimalWeight_primeFactor_mass_le_three s hz) 2
    _ = _ := by ring

/-- Fully optimized finite Selberg inequality with explicit logarithmic error, base three. -/
theorem siftedSum_le_log_error_three (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z)
    (hrem : ∀ a ∈ s.prodPrimes.divisors, ∀ b ∈ s.prodPrimes.divisors,
      |s.rem (Nat.lcm a b)| ≤
        (3 : ℝ) ^ a.primeFactors.card * (3 : ℝ) ^ b.primeFactors.card) :
    s.siftedSum ≤ s.totalMass / SelbergOptimal.normalizer s z +
      (z : ℝ) ^ 2 * (1 + Real.log z) ^ 6 :=
  (SelbergOptimal.siftedSum_le s hz).trans
    (add_le_add le_rfl (errSum_optimalWeight_le_log_three s hz hrem))

/-- The sifted count for the quadratic sequence is bounded by the Selberg main term. -/
theorem sq_sifted_le (U y z : ℕ) (hU : 1 ≤ U) (hz : 1 ≤ z) :
    (((Finset.Ioc U (2 * U)).filter
        (fun r => (primorial y).Coprime (r * (r ^ 2 - 2)))).card : ℝ) ≤
      (U : ℝ) / SelbergOptimal.normalizer (sqSieve U y) z +
        (z : ℝ) ^ 2 * (1 + Real.log z) ^ 6 := by
  have he := siftedSum_le_log_error_three (sqSieve U y) hz
    (fun a ha b hb => sqSieve_rem_lcm_bound U y hU a ha b hb)
  rwa [sqSieve_siftedSum, sqSieve_totalMass] at he


/-- The local sieve weight. -/
def wgt (p : ℕ) : ℝ := sqDensity p * (1 - sqDensity p)⁻¹

/-- The finite Euler product of local factors. -/
def mass (y : ℕ) : ℝ := ∏ p ∈ y.primesLE, (1 + wgt p)

def index (t : Finset ℕ) : ℕ := ∏ p ∈ t, p

def weight (t : Finset ℕ) : ℝ := ∏ p ∈ t, wgt p

theorem sqDensity_bounds (p : ℕ) (hp : p.Prime) :
    0 < sqDensity p ∧ sqDensity p < 1 :=
  ⟨sqDensity_prime_pos p hp, sqDensity_prime_lt_one p hp⟩

theorem wgt_pos (p : ℕ) (hp : p.Prime) : 0 < wgt p := by
  have h := sqDensity_bounds p hp
  exact mul_pos h.1 (inv_pos.mpr (by linarith [h.2]))

theorem wgt_ratio (p : ℕ) (hp : p.Prime) : wgt p / (1 + wgt p) = sqDensity p := by
  have h := (sqDensity_bounds p hp).2
  have hpos := wgt_pos p hp
  unfold wgt at *
  field_simp
  ring

theorem wgt_le (p : ℕ) (hp : p.Prime) : wgt p / (1 + wgt p) ≤ 3 / (p : ℝ) := by
  rw [wgt_ratio p hp, sqDensity_apply]
  have h := sqRootCount_prime_le_three p hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) hpR.le

/-- The Selberg normalizer is a sum over subsets of the sieving primes. -/
theorem normalizer_eq_powerset (U y z : ℕ) :
    SelbergOptimal.normalizer (sqSieve U y) z =
      ∑ t ∈ y.primesLE.powerset, if index t ≤ z then weight t else 0 := by
  classical
  let P := primorial y
  have prime (t : Finset ℕ) (ht : t ∈ y.primesLE.powerset) : ∀ p ∈ t, p.Prime :=
    fun p hp => Nat.prime_of_mem_primesLE ((Finset.mem_powerset.mp ht) hp)
  have hfac (t : Finset ℕ) (ht : t ∈ y.primesLE.powerset) :
      (index t).primeFactors = t := Nat.primeFactors_prod (prime t ht)
  have hmap : P.divisors = y.primesLE.powerset.image index := by
    ext d
    constructor
    · intro hd
      have hsq := (squarefree_primorial y).squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
      have hmono := Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) (primorial_ne_zero y)
      rw [primeFactors_primorial] at hmono
      exact Finset.mem_image.mpr ⟨d.primeFactors, Finset.mem_powerset.mpr hmono,
        Nat.prod_primeFactors_of_squarefree hsq⟩
    · rintro hd
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hd
      exact Nat.mem_divisors.mpr ⟨Finset.prod_dvd_prod_of_subset _ _ _
        (Finset.mem_powerset.mp ht), primorial_ne_zero y⟩
  unfold SelbergOptimal.normalizer
  change (∑ d ∈ P.divisors, if d ≤ z then (sqSieve U y).selbergTerms d else 0) = _
  rw [hmap, Finset.sum_image (fun a ha b hb hh =>
    (hfac a ha).symm.trans ((congrArg Nat.primeFactors hh).trans (hfac b hb)))]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [BoundingSieve.selbergTerms_apply]
  have hnu : ∀ d, (sqSieve U y).nu d = sqDensity d := fun d => rfl
  simp only [hnu]
  split_ifs
  · rw [hfac t ht, index, (sqDensity_isMultiplicative).map_prod_of_prime t (prime t ht)]
    unfold weight wgt
    rw [Finset.prod_mul_distrib]
  · rfl

/-- The truncated normalizer retains half of the Euler product at cutoff `y^12`. -/
theorem mass_le_two_mul_normalizer (U y : ℕ) (hy : 2 ≤ y) :
    mass y ≤ 2 * SelbergOptimal.normalizer (sqSieve U y) (y ^ 12) := by
  classical
  let T := y.primesLE.powerset
  let W := weight
  have wp (t : Finset ℕ) (ht : t ∈ T) : 0 ≤ W t :=
    Finset.prod_nonneg fun p hp =>
      (wgt_pos p (Nat.prime_of_mem_primesLE ((Finset.mem_powerset.mp ht) hp))).le
  have total : (∑ t ∈ T, W t) = mass y := by
    unfold mass
    exact (Finset.prod_one_add _).symm
  have heavy_point (t : Finset ℕ) (ht : t ∈ T) :
      (if y ^ 12 < index t then W t else 0) * (12 * Real.log y) ≤ W t * Real.log (index t) := by
    have hip : 0 < index t := Finset.prod_pos fun p hp =>
      (Nat.prime_of_mem_primesLE ((Finset.mem_powerset.mp ht) hp)).pos
    split
    · rename_i hl
      apply mul_le_mul_of_nonneg_left _ (wp t ht)
      have hlog := Real.log_le_log (show (0 : ℝ) < ((y ^ 12 : ℕ) : ℝ) by positivity)
        (show ((y ^ 12 : ℕ) : ℝ) ≤ index t by exact_mod_cast hl.le)
      simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using hlog
    · rw [zero_mul]
      exact mul_nonneg (wp t ht) (Real.log_nonneg (by exact_mod_cast hip))
  have mean := Conjectures.TwinPrimes.CofactorTwoLinearSieve_aux.CentralSelberg.powerset_moment
    y.primesLE wgt (fun p => Real.log (p : ℝ))
    (fun p hp => (wgt_pos p (Nat.prime_of_mem_primesLE hp)).le)
  have hsumlog (t : Finset ℕ) (ht : t ∈ T) :
      Real.log (index t) = ∑ p ∈ t, Real.log (p : ℝ) := by
    unfold index
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    exact_mod_cast (Nat.prime_of_mem_primesLE ((Finset.mem_powerset.mp ht) hp)).ne_zero
  have bound : (∑ p ∈ y.primesLE, wgt p / (1 + wgt p) * Real.log p) ≤ 6 * Real.log y := by
    calc
      _ ≤ ∑ p ∈ y.primesLE, 3 * (Real.log p / p) := by
        refine sum_le_sum fun p hp => ?_
        have hpP := Nat.prime_of_mem_primesLE hp
        have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpP.one_le)
        have hw := wgt_le p hpP
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hpP.pos
        calc
          wgt p / (1 + wgt p) * Real.log p ≤ (3 / (p : ℝ)) * Real.log p :=
            mul_le_mul_of_nonneg_right hw hlog
          _ = 3 * (Real.log p / p) := by ring
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        have hwh :=
          Conjectures.TwinPrimes.CofactorTwoLinearSieve_aux.CentralSelberg.weighted_harmonic
            y (by omega)
        linarith
  have hmass : 0 ≤ mass y := by
    unfold mass
    exact Finset.prod_nonneg (fun p hp => by
      linarith [wgt_pos p (Nat.prime_of_mem_primesLE hp)])
  have moment : (∑ t ∈ T, W t * Real.log (index t)) ≤ mass y * (6 * Real.log y) := by
    calc
      _ = ∑ t ∈ y.primesLE.powerset, (∏ p ∈ t, wgt p) * (∑ p ∈ t, Real.log p) :=
        sum_congr rfl (fun t ht => by rw [hsumlog t ht]; rfl)
      _ = _ := mean
      _ ≤ _ := mul_le_mul_of_nonneg_left bound hmass
  have hdiff : (∑ t ∈ T, if y ^ 12 < index t then W t else 0) =
      mass y - SelbergOptimal.normalizer (sqSieve U y) (y ^ 12) := by
    rw [← total, normalizer_eq_powerset U y (y ^ 12), ← Finset.sum_sub_distrib]
    apply sum_congr rfl
    intro t _
    by_cases h : index t ≤ y ^ 12
    · rw [if_neg (not_lt.mpr h), if_pos h]
      dsimp [W]
      ring
    · rw [if_pos (lt_of_not_ge h), if_neg h]
      dsimp [W]
      ring
  have hh := (sum_le_sum heavy_point).trans moment
  rw [← Finset.sum_mul, hdiff] at hh
  have hl : 0 < Real.log y := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  change mass y ≤ 2 * SelbergOptimal.normalizer (sqSieve U y) (y ^ 12)
  apply (le_of_mul_le_mul_right (a := Real.log y) ?_ hl)
  linarith only [hh]


/-- The Euler product dominates the exponential of the summed local densities. -/
theorem mass_ge_exp_sum (y : ℕ) :
    Real.exp (∑ p ∈ y.primesLE, sqDensity p) ≤ mass y := by
  unfold mass
  rw [Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro p _
    positivity
  · intro p hp
    have hpP := Nat.prime_of_mem_primesLE hp
    have h := sqDensity_bounds p hpP
    have hne : 1 - sqDensity p ≠ 0 := by linarith [h.2]
    have h1 : 1 + wgt p = (1 - sqDensity p)⁻¹ := by
      unfold wgt
      field_simp
      ring
    rw [h1]
    have h2 : 1 - sqDensity p ≤ Real.exp (-(sqDensity p)) := by
      have := Real.add_one_le_exp (-(sqDensity p))
      linarith
    have h3 : (Real.exp (-(sqDensity p)))⁻¹ ≤ (1 - sqDensity p)⁻¹ :=
      inv_anti₀ (by linarith [h.2]) h2
    rw [Real.exp_neg, inv_inv] at h3
    exact h3

/-- The harmonic sum of the local densities splits over the residue classes mod eight. -/
theorem sum_sqDensity_split (y : ℕ) :
    (∑ p ∈ y.primesLE, sqDensity p) =
      (if 2 ∈ y.primesLE then (1 : ℝ) / 2 else 0) +
        3 * (∑ p ∈ y.primesLE.filter (fun p => p % 8 = 1), (1 : ℝ) / (p : ℝ)) +
        3 * (∑ p ∈ y.primesLE.filter (fun p => p % 8 = 7), (1 : ℝ) / (p : ℝ)) +
        (∑ p ∈ y.primesLE.filter (fun p => p % 8 = 3), (1 : ℝ) / (p : ℝ)) +
        (∑ p ∈ y.primesLE.filter (fun p => p % 8 = 5), (1 : ℝ) / (p : ℝ)) := by
  classical
  have key (p : ℕ) (hp : p ∈ y.primesLE) : sqDensity p =
      (if p = 2 then (1 : ℝ) / 2 else 0) +
        3 * (if p % 8 = 1 then (1 : ℝ) / (p : ℝ) else 0) +
        3 * (if p % 8 = 7 then (1 : ℝ) / (p : ℝ) else 0) +
        (if p % 8 = 3 then (1 : ℝ) / (p : ℝ) else 0) +
        (if p % 8 = 5 then (1 : ℝ) / (p : ℝ) else 0) := by
    have hpP := Nat.prime_of_mem_primesLE hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpP.pos
    rw [sqDensity_prime p hpP]
    by_cases h2 : p = 2
    · subst h2
      have hmod : (2 : ℕ) % 8 = 2 := by norm_num
      simp [hmod, hpR.ne']
    · have hodd : ¬ (2 ∣ p) := by
        intro hd
        rcases hpP.eq_one_or_self_of_dvd 2 hd with h | h
        · omega
        · exact h2 h.symm
      have hmododd : p % 8 % 2 = 1 := by omega
      have hmodlt : p % 8 < 8 := Nat.mod_lt p (by norm_num)
      have hres : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
      rcases hres with h1 | h3 | h5 | h7
      · rw [h1]; simp [h2, hpR.ne'] <;> ring
      · rw [h3]; simp [h2, hpR.ne'] <;> ring
      · rw [h5]; simp [h2, hpR.ne'] <;> ring
      · rw [h7]; simp [h2, hpR.ne'] <;> ring
  have e2 : (∑ p ∈ y.primesLE, (if p = 2 then (1 : ℝ) / 2 else 0)) =
      if 2 ∈ y.primesLE then (1 : ℝ) / 2 else 0 := by
    by_cases h : 2 ∈ y.primesLE
    · rw [if_pos h]; simp [h]
    · rw [if_neg h]; simp [h]
  have eclass (a : ℕ) :
      (∑ p ∈ y.primesLE, (if p % 8 = a then (1 : ℝ) / (p : ℝ) else 0)) =
        ∑ p ∈ y.primesLE.filter (fun p => p % 8 = a), (1 : ℝ) / (p : ℝ) :=
    (Finset.sum_filter (fun p => p % 8 = a) (fun p => (1 : ℝ) / (p : ℝ))).symm
  calc
    (∑ p ∈ y.primesLE, sqDensity p) =
        ∑ p ∈ y.primesLE, ((if p = 2 then (1 : ℝ) / 2 else 0) +
          3 * (if p % 8 = 1 then (1 : ℝ) / (p : ℝ) else 0) +
          3 * (if p % 8 = 7 then (1 : ℝ) / (p : ℝ) else 0) +
          (if p % 8 = 3 then (1 : ℝ) / (p : ℝ) else 0) +
          (if p % 8 = 5 then (1 : ℝ) / (p : ℝ) else 0)) :=
      Finset.sum_congr rfl (fun p hp => key p hp)
    _ = (∑ p ∈ y.primesLE, (if p = 2 then (1 : ℝ) / 2 else 0)) +
          3 * (∑ p ∈ y.primesLE, (if p % 8 = 1 then (1 : ℝ) / (p : ℝ) else 0)) +
          3 * (∑ p ∈ y.primesLE, (if p % 8 = 7 then (1 : ℝ) / (p : ℝ) else 0)) +
          (∑ p ∈ y.primesLE, (if p % 8 = 3 then (1 : ℝ) / (p : ℝ) else 0)) +
          (∑ p ∈ y.primesLE, (if p % 8 = 5 then (1 : ℝ) / (p : ℝ) else 0)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = (if 2 ∈ y.primesLE then (1 : ℝ) / 2 else 0) +
          3 * (∑ p ∈ y.primesLE.filter (fun p => p % 8 = 1), (1 : ℝ) / (p : ℝ)) +
          3 * (∑ p ∈ y.primesLE.filter (fun p => p % 8 = 7), (1 : ℝ) / (p : ℝ)) +
          (∑ p ∈ y.primesLE.filter (fun p => p % 8 = 3), (1 : ℝ) / (p : ℝ)) +
          (∑ p ∈ y.primesLE.filter (fun p => p % 8 = 5), (1 : ℝ) / (p : ℝ)) := by
        rw [e2, eclass 1, eclass 7, eclass 3, eclass 5]

/-- Under the arithmetic-progression harmonic input, the Euler product is at least
a constant times the square of the logarithm. -/
theorem mass_lower (hAP : ∀ a : ℕ, (a = 1 ∨ a = 3 ∨ a = 5 ∨ a = 7) →
      ∃ K : ℝ, ∀ y : ℕ, 3 ≤ y →
        (1 / 4 : ℝ) * Real.log (Real.log (y : ℝ)) ≤
          K + ∑ p ∈ (Finset.range (y + 1)).filter (fun p => Nat.Prime p ∧ p % 8 = a),
            (1 : ℝ) / (p : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : ℕ, 5 ≤ y → c * (Real.log (y : ℝ)) ^ 2 ≤ mass y := by
  obtain ⟨K1, hK1⟩ := hAP 1 (Or.inl rfl)
  obtain ⟨K3, hK3⟩ := hAP 3 (Or.inr (Or.inl rfl))
  obtain ⟨K5, hK5⟩ := hAP 5 (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨K7, hK7⟩ := hAP 7 (Or.inr (Or.inr (Or.inr rfl)))
  let L1 : ℝ := max K1 0
  let L3 : ℝ := max K3 0
  let L5 : ℝ := max K5 0
  let L7 : ℝ := max K7 0
  have hL1 : 0 ≤ L1 := le_max_right _ _
  have hL3 : 0 ≤ L3 := le_max_right _ _
  have hL5 : 0 ≤ L5 := le_max_right _ _
  have hL7 : 0 ≤ L7 := le_max_right _ _
  refine ⟨Real.exp (-(8 * (L1 + L3 + L5 + L7))), Real.exp_pos _, ?_⟩
  intro y hy
  have hy3 : 3 ≤ y := by omega
  have hfilter (a : ℕ) :
      (Finset.range (y + 1)).filter (fun p => Nat.Prime p ∧ p % 8 = a) =
        y.primesLE.filter (fun p => p % 8 = a) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_primesLE]
    constructor
    · rintro ⟨hpy, hpp, hmod⟩
      exact ⟨⟨by omega, hpp⟩, hmod⟩
    · rintro ⟨⟨hpy, hpp⟩, hmod⟩
      exact ⟨by omega, hpp, hmod⟩
  have h1 : (1 / 4 : ℝ) * Real.log (Real.log (y : ℝ)) ≤
      L1 + ∑ p ∈ y.primesLE.filter (fun p => p % 8 = 1), (1 : ℝ) / (p : ℝ) := by
    have h := hK1 y hy3
    rw [hfilter 1] at h
    exact h.trans (add_le_add_left (le_max_left K1 0) _)
  have h3 : (1 / 4 : ℝ) * Real.log (Real.log (y : ℝ)) ≤
      L3 + ∑ p ∈ y.primesLE.filter (fun p => p % 8 = 3), (1 : ℝ) / (p : ℝ) := by
    have h := hK3 y hy3
    rw [hfilter 3] at h
    exact h.trans (add_le_add_left (le_max_left K3 0) _)
  have h5 : (1 / 4 : ℝ) * Real.log (Real.log (y : ℝ)) ≤
      L5 + ∑ p ∈ y.primesLE.filter (fun p => p % 8 = 5), (1 : ℝ) / (p : ℝ) := by
    have h := hK5 y hy3
    rw [hfilter 5] at h
    exact h.trans (add_le_add_left (le_max_left K5 0) _)
  have h7 : (1 / 4 : ℝ) * Real.log (Real.log (y : ℝ)) ≤
      L7 + ∑ p ∈ y.primesLE.filter (fun p => p % 8 = 7), (1 : ℝ) / (p : ℝ) := by
    have h := hK7 y hy3
    rw [hfilter 7] at h
    exact h.trans (add_le_add_left (le_max_left K7 0) _)
  have hsplit := sum_sqDensity_split y
  have hmem2 : 2 ∈ y.primesLE := Nat.mem_primesLE.mpr ⟨by omega, Nat.prime_two⟩
  rw [if_pos hmem2] at hsplit
  have hsum : 2 * Real.log (Real.log (y : ℝ)) ≤
      8 * (L1 + L3 + L5 + L7) + ∑ p ∈ y.primesLE, sqDensity p := by
    have h1' := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 3)
    have h7' := mul_le_mul_of_nonneg_left h7 (by norm_num : (0 : ℝ) ≤ 3)
    linarith
  have hmass := mass_ge_exp_sum y
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hexp : Real.exp (2 * Real.log (Real.log (y : ℝ))) = (Real.log (y : ℝ)) ^ 2 := by
    rw [show (2 : ℝ) * Real.log (Real.log (y : ℝ)) =
      Real.log ((Real.log (y : ℝ)) ^ 2) by rw [Real.log_pow]; ring]
    exact Real.exp_log (by positivity)
  have hmono : Real.exp (2 * Real.log (Real.log (y : ℝ))) ≤
      Real.exp (8 * (L1 + L3 + L5 + L7) + ∑ p ∈ y.primesLE, sqDensity p) :=
    Real.exp_le_exp.mpr (by linarith)
  have hexp2 : Real.exp (8 * (L1 + L3 + L5 + L7) + ∑ p ∈ y.primesLE, sqDensity p) =
      Real.exp (8 * (L1 + L3 + L5 + L7)) * Real.exp (∑ p ∈ y.primesLE, sqDensity p) :=
    Real.exp_add _ _
  have hmono' : (Real.log (y : ℝ)) ^ 2 ≤
      Real.exp (8 * (L1 + L3 + L5 + L7) + ∑ p ∈ y.primesLE, sqDensity p) := by
    rw [← hexp]
    exact hmono
  calc
    Real.exp (-(8 * (L1 + L3 + L5 + L7))) * (Real.log (y : ℝ)) ^ 2
        ≤ Real.exp (-(8 * (L1 + L3 + L5 + L7))) *
            Real.exp (8 * (L1 + L3 + L5 + L7) + ∑ p ∈ y.primesLE, sqDensity p) :=
          mul_le_mul_of_nonneg_left hmono' (Real.exp_pos _).le
    _ = Real.exp (∑ p ∈ y.primesLE, sqDensity p) := by
          rw [← Real.exp_add]
          congr 1
          ring
    _ ≤ mass y := hmass


/-- The truncated normalizer is at least a constant times `(log y)^2`. -/
theorem normalizer_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ (U y : ℕ), 5 ≤ y →
      c * (Real.log (y : ℝ)) ^ 2 ≤ SelbergOptimal.normalizer (sqSieve U y) (y ^ 12) := by
  obtain ⟨c, hc, hmass⟩ := mass_lower (fun a ha => AP.ap_recip_lower a ha)
  refine ⟨c / 2, by linarith, ?_⟩
  intro U y hy
  have h1 := mass_le_two_mul_normalizer U y (by omega)
  have h2 := hmass y hy
  linarith

open Filter Topology

set_option maxRecDepth 2000000 in
/-- A choice of the sieving level for which the error term is negligible. -/
theorem scales :
    ∀ᶠ U : ℕ in atTop, ∃ y : ℕ, 5 ≤ y ∧ y ≤ U ∧
       Real.log (U:ℝ) ≤ 64*Real.log ((y:ℝ)+1) ∧
       (((y^12:ℕ):ℝ)^2*(1+Real.log ((y^12:ℕ):ℝ))^6) * (Real.log (U:ℝ))^2 ≤ 64*(U:ℝ) := by
  have hs := (isLittleO_log_rpow_rpow_atTop (8:ℝ) (by norm_num : (0:ℝ)<1/2)).bound
    (by norm_num : (0:ℝ)<1)
  have hs' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hs
  have hl := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
  filter_upwards [hs', hl, eventually_ge_atTop (5^64:ℕ)] with U hU hlog hU64
  change 1 ≤ Real.log (U:ℝ) at hlog
  have hU0 : 0 < (U:ℝ) := by exact_mod_cast (show 0<U by omega)
  have hU1 : 1 ≤ (U:ℝ) := by linarith [show (5:ℝ)^64 ≤ U by exact_mod_cast hU64]
  have hbig : (Real.log U)^8 ≤ Real.sqrt U := by
    have hr : (U:ℝ)^(1/2:ℝ) = Real.sqrt U := (Real.sqrt_eq_rpow _).symm
    simpa only [Real.norm_eq_abs, Real.rpow_natCast_mul, Real.rpow_ofNat,
      abs_of_nonneg (by positivity : 0≤(Real.log U)^8),
      abs_of_nonneg (Real.rpow_nonneg hU0.le _), one_mul, hr,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hU
  let u : ℝ := (U:ℝ)^(1/64:ℝ)
  let y := ⌊u⌋₊
  have hu : 0≤u := Real.rpow_nonneg hU0.le _
  have hu64 : u^64 = U := by
    rw [show u^64 = (U:ℝ)^((1/64:ℝ)*64) from (Real.rpow_mul_natCast hU0.le _ _).symm]
    norm_num
  have hy5 : 5≤y := by
    apply (Nat.le_floor_iff hu).mpr
    by_contra! h
    have hp : u ^ (64 : ℕ) < (5 : ℝ) ^ (64 : ℕ) := pow_lt_pow_left₀ h hu (by norm_num)
    rw [hu64] at hp
    exact (not_lt_of_ge (show (5:ℝ)^64 ≤ U by exact_mod_cast hU64)) hp
  have hyU : y ≤ U := by
    have h1 : (y:ℝ) ≤ u := Nat.floor_le hu
    have h2 : u ≤ (U:ℝ) := by
      have hx := Real.rpow_le_rpow_of_exponent_le hU1 (show (1/64:ℝ) ≤ 1 by norm_num)
      simpa [u] using hx
    exact_mod_cast h1.trans h2
  have hyp : (0:ℝ)<y := by exact_mod_cast (show 0<y by omega)
  have hyr : (1:ℝ)≤y := by exact_mod_cast (show 1≤y by omega)
  have hlow := pow_le_pow_left₀ hyp.le (Nat.floor_le hu : (y:ℝ) ≤ u) 64
  have hhigh := pow_le_pow_left₀ hu (Nat.lt_floor_add_one u).le 64
  rw [hu64] at hlow hhigh
  have hylog : Real.log (U:ℝ) ≤ 64*Real.log ((y:ℝ)+1) := by
    have hh := Real.log_le_log hU0 hhigh
    simpa only [Real.log_pow, Nat.cast_ofNat, y] using hh
  have hy32 : (y:ℝ)^32 ≤ Real.sqrt U := by
    apply (Real.le_sqrt (by positivity) hU0.le).mpr
    convert hlow using 1 <;> ring
  have hy24a : (y:ℝ)^(24:ℕ) ≤ (y:ℝ)^(32:ℕ) := pow_le_pow_right₀ hyr (by norm_num)
  have hy24 : (y:ℝ)^24 ≤ Real.sqrt U := hy24a.trans hy32
  have hly : Real.log ((y^12:ℕ):ℝ) ≤ Real.log U := by
    apply Real.log_le_log (by positivity)
    rw [Nat.cast_pow]
    exact (pow_le_pow_right₀ hyr (by norm_num : 12≤64)).trans hlow
  have hp6 : (1+Real.log ((y^12:ℕ):ℝ))^6 ≤ (2*Real.log U)^6 :=
    pow_le_pow_left₀ (by have := Real.log_nonneg (show (1:ℝ)≤((y^12:ℕ):ℝ) by
      exact_mod_cast (Nat.one_le_pow _ _ (by omega : 1≤y))); linarith) (by linarith) _
  rw [Nat.cast_pow] at hp6
  have hsqr := Real.sq_sqrt hU0.le
  have hmain : Real.sqrt U*(Real.log U)^8 ≤ U := by
    nlinarith [mul_le_mul_of_nonneg_left hbig (Real.sqrt_nonneg U)]
  have h24 : ((y:ℝ)^12)^2 = (y:ℝ)^24 := by ring
  refine ⟨y, hy5, hyU, hylog, ?_⟩
  rw [Nat.cast_pow]
  calc
    _ ≤ ((y:ℝ)^24*(2*Real.log U)^6)*(Real.log U)^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      rw [h24]
      exact mul_le_mul (le_refl _) hp6 (by positivity) (by positivity)
    _ ≤ (Real.sqrt U*(2*Real.log U)^6)*(Real.log U)^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right hy24 (by positivity)
    _ = 64*(Real.sqrt U*(Real.log U)^8) := by ring
    _ ≤ 64*(U:ℝ) := by linarith

/-- Both factors of a prime pair avoid every prime up to the sieving level. -/
theorem prime_pair_coprime (U y r : ℕ) (hyU : y ≤ U) (hrI : r ∈ Finset.Ioc U (2 * U))
    (hrP : r.Prime) (hrQ : (r ^ 2 - 2).Prime) :
    (primorial y).Coprime (r * (r ^ 2 - 2)) := by
  have hrU : U < r := (Finset.mem_Ioc.mp hrI).1
  have hry : ¬ (r ∣ primorial y) := by
    intro hd
    have hmem : r ∈ (primorial y).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hrP, hd, primorial_ne_zero y⟩
    rw [primeFactors_primorial] at hmem
    have := (Nat.mem_primesLE.mp hmem).1
    omega
  have hq : y < r ^ 2 - 2 := by
    have hr2 : 2 ≤ r := hrP.two_le
    have hsq : 2 ≤ r ^ 2 := by nlinarith
    have hsub : r ^ 2 - 2 + 2 = r ^ 2 := Nat.sub_add_cancel hsq
    have hle : r ≤ r ^ 2 - 2 := by nlinarith
    omega
  have hqy : ¬ ((r ^ 2 - 2) ∣ primorial y) := by
    intro hd
    have hmem : r ^ 2 - 2 ∈ (primorial y).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hrQ, hd, primorial_ne_zero y⟩
    rw [primeFactors_primorial] at hmem
    have := (Nat.mem_primesLE.mp hmem).1
    omega
  exact ((hrP.coprime_iff_not_dvd.mpr hry).symm).mul_right
    ((hrQ.coprime_iff_not_dvd.mpr hqy).symm)

/-- The upper bound for prime pairs `r, r^2 - 2`. -/
theorem prime_square_minus_two_upper :
    ∃ C : ℝ, 0<C ∧ ∀ U : ℕ, 3≤U →
      (((Finset.Ioc U (2*U)).filter fun r => r.Prime ∧ (r^2-2).Prime).card : ℝ) ≤
        C*U/(Real.log U)^2 := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp scales
  obtain ⟨c, hc, hnorm⟩ := normalizer_lower
  refine ⟨16384 / c + 64 + (Real.log ((max X 3 : ℕ) : ℝ))^2, by positivity, ?_⟩
  intro U hU
  have hU1 : 1 ≤ U := by omega
  have hUpos : 0 < U := by omega
  have hlogUpos : 0 < Real.log U := Real.log_pos (by exact_mod_cast (show 1 < U by omega))
  have hcardIoc : (Finset.Ioc U (2 * U)).card = U := by
    rw [Nat.card_Ioc]
    omega
  rw [le_div_iff₀ (pow_pos hlogUpos 2)]
  by_cases hcase : U < max X 3
  · have hcardT : ((((Finset.Ioc U (2*U)).filter
        (fun r => r.Prime ∧ (r^2-2).Prime)).card : ℕ) : ℝ) ≤ (U : ℝ) := by
      have h1 : ((Finset.Ioc U (2*U)).filter
          (fun r => r.Prime ∧ (r^2-2).Prime)).card ≤ (Finset.Ioc U (2*U)).card := by
        apply Finset.card_le_card
        intro r hr
        exact (Finset.mem_filter.mp hr).1
      rw [hcardIoc] at h1
      exact_mod_cast h1
    have hmono : Real.log U ≤ Real.log ((max X 3 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast hUpos) (by exact_mod_cast (le_of_lt hcase))
    have hsq : (Real.log U)^2 ≤ (Real.log ((max X 3 : ℕ) : ℝ))^2 :=
      pow_le_pow_left₀ hlogUpos.le hmono 2
    calc _ ≤ (U:ℝ) * (Real.log U)^2 :=
          mul_le_mul_of_nonneg_right hcardT (sq_nonneg (Real.log U))
      _ ≤ (U:ℝ) * (Real.log ((max X 3 : ℕ) : ℝ))^2 :=
          mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg U)
      _ ≤ (16384 / c + 64 + (Real.log ((max X 3 : ℕ) : ℝ))^2) * (U:ℝ) := by
          calc (U:ℝ) * (Real.log ((max X 3 : ℕ) : ℝ))^2
              ≤ (U:ℝ) * (Real.log ((max X 3 : ℕ) : ℝ))^2 + (16384 / c + 64) * (U:ℝ) :=
                le_add_of_nonneg_right (by positivity)
            _ = (16384 / c + 64 + (Real.log ((max X 3 : ℕ) : ℝ))^2) * (U:ℝ) := by ring
  · have hcase' : max X 3 ≤ U := by omega
    obtain ⟨y, hy5, hyU, hlog, herr⟩ := hX U ((le_max_left X 3).trans hcase')
    have hzpos : 1 ≤ y ^ 12 := Nat.one_le_pow _ _ (by omega)
    set N := SelbergOptimal.normalizer (sqSieve U y) (y ^ 12)
    have hN : c * (Real.log (y : ℝ)) ^ 2 ≤ N := hnorm U y hy5
    have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN
    have hyle : Real.log ((y : ℝ) + 1) ≤ 2 * Real.log (y : ℝ) := by
      have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast (show 2 ≤ y by omega)
      have h1 : ((y : ℝ) + 1) ≤ (y : ℝ) ^ 2 := by nlinarith
      have h2 := Real.log_le_log (by positivity) h1
      rw [Real.log_pow, Nat.cast_ofNat] at h2
      exact h2
    have hsq1 : (Real.log U)^2 ≤ (64 * Real.log ((y : ℝ) + 1))^2 :=
      pow_le_pow_left₀ hlogUpos.le hlog 2
    have hsq2 : (Real.log ((y : ℝ) + 1))^2 ≤ 4 * (Real.log (y : ℝ))^2 := by
      nlinarith [hyle]
    have hDen : (Real.log U)^2 ≤ (16384 / c) * N := by
      calc (Real.log U)^2 ≤ (64 * Real.log ((y : ℝ) + 1))^2 := hsq1
        _ = 4096 * (Real.log ((y : ℝ) + 1))^2 := by ring
        _ ≤ 4096 * (4 * (Real.log (y : ℝ))^2) := mul_le_mul_of_nonneg_left hsq2 (by norm_num)
        _ = (16384 / c) * (c * (Real.log (y : ℝ))^2) := by field_simp; ring
        _ ≤ (16384 / c) * N := mul_le_mul_of_nonneg_left hN (by positivity)
    have hfirst : ((U : ℝ) / N) * (Real.log U)^2 ≤ (16384 / c) * (U : ℝ) := by
      calc _ ≤ ((U : ℝ) / N) * ((16384 / c) * N) :=
            mul_le_mul_of_nonneg_left hDen (by positivity)
        _ = _ := by field_simp
    have hsub : (Finset.Ioc U (2 * U)).filter (fun r => r.Prime ∧ (r ^ 2 - 2).Prime) ⊆
        (Finset.Ioc U (2 * U)).filter
          (fun r => (primorial y).Coprime (r * (r ^ 2 - 2))) := by
      intro r hr
      obtain ⟨hrI, hrP, hrQ⟩ := Finset.mem_filter.mp hr
      exact Finset.mem_filter.mpr ⟨hrI, prime_pair_coprime U y r hyU hrI hrP hrQ⟩
    have hcardle : ((((Finset.Ioc U (2 * U)).filter
        (fun r => r.Prime ∧ (r ^ 2 - 2).Prime)).card : ℕ) : ℝ) ≤
        (U : ℝ) / N + ((y ^ 12 : ℕ) : ℝ) ^ 2 * (1 + Real.log ((y ^ 12 : ℕ) : ℝ)) ^ 6 := by
      calc _ ≤ ((((Finset.Ioc U (2 * U)).filter
              (fun r => (primorial y).Coprime (r * (r ^ 2 - 2)))).card : ℕ) : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ _ := sq_sifted_le U y (y ^ 12) hU1 hzpos
    have hmul := mul_le_mul_of_nonneg_right hcardle (sq_nonneg (Real.log U))
    calc _ ≤ ((U : ℝ) / N + ((y ^ 12 : ℕ) : ℝ) ^ 2 * (1 + Real.log ((y ^ 12 : ℕ) : ℝ)) ^ 6) *
          (Real.log U)^2 := hmul
      _ = ((U : ℝ) / N) * (Real.log U)^2 +
          ((y ^ 12 : ℕ) : ℝ) ^ 2 * (1 + Real.log ((y ^ 12 : ℕ) : ℝ)) ^ 6 * (Real.log U)^2 := by ring
      _ ≤ (16384 / c) * (U : ℝ) + 64 * (U : ℝ) := add_le_add hfirst herr
      _ ≤ (16384 / c + 64 + (Real.log ((max X 3 : ℕ) : ℝ))^2) * (U : ℝ) := by
          calc (16384 / c) * (U : ℝ) + 64 * (U : ℝ) = (16384 / c + 64) * (U : ℝ) := by ring
            _ ≤ (16384 / c + 64) * (U : ℝ) +
                  (Real.log ((max X 3 : ℕ) : ℝ))^2 * (U : ℝ) :=
                le_add_of_nonneg_right
                  (mul_nonneg (sq_nonneg (Real.log ((max X 3 : ℕ) : ℝ))) (Nat.cast_nonneg U))
            _ = (16384 / c + 64 + (Real.log ((max X 3 : ℕ) : ℝ))^2) * (U : ℝ) := by ring

end
end Conjectures.TwinPrimes.PrimeSquareMinusTwoUpperSieve_aux

theorem Conjectures.TwinPrimes.PrimeSquareMinusTwoUpperSieve :
  ∃ C : ℝ, 0<C ∧ ∀ U : ℕ, 3≤U → (((Finset.Ioc U (2*U)).filter fun r => r.Prime ∧ (r^2-2).Prime).card : ℝ) ≤ C*U/(Real.log U)^2 :=
  Conjectures.TwinPrimes.PrimeSquareMinusTwoUpperSieve_aux.prime_square_minus_two_upper

theorem Conjectures.TwinPrimes.SquareNeighbourModThree :
    (∀ n : ℕ, 10 ≤ n → ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2) ≠ 0 → (¬ n.Prime ∨ ¬ (n+2).Prime) → (∃ p a : ℕ, p.Prime ∧ 3 ≤ a ∧ (p^a=n ∨ p^a=n+2)) ∨ (n.Prime ∧ ∃ p : ℕ, p.Prime ∧ p^2=n+2)) := by
  intro n hN hNonzero hBad
  obtain ⟨hL, hR⟩ := mul_ne_zero_iff.mp hNonzero
  obtain ⟨p, a, hp, ha, hPowL⟩ :=
    (isPrimePow_nat_iff n).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hL)
  obtain ⟨q, b, hq, hb, hPowR⟩ :=
    (isPrimePow_nat_iff (n+2)).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hR)
  by_cases haLarge : 3 ≤ a
  · exact Or.inl ⟨p, a, hp, haLarge, Or.inl hPowL⟩
  by_cases hbLarge : 3 ≤ b
  · exact Or.inl ⟨q, b, hq, hbLarge, Or.inr hPowR⟩
  by_cases hNPrime : n.Prime
  · have hNotPrime : ¬(n+2).Prime := hBad.resolve_left (fun h => h hNPrime)
    have hNotOne : b ≠ 1 := by
      intro h
      apply hNotPrime
      rwa [← hPowR, h, pow_one]
    have hTwo : b = 2 := by omega
    exact Or.inr ⟨hNPrime, q, hq, by simpa only [hTwo] using hPowR⟩
  · have hNotOne : a ≠ 1 := by
      intro h
      apply hNPrime
      rwa [← hPowL, h, pow_one]
    have hTwo : a = 2 := by omega
    have hSquare : p^2 = n := by simpa only [hTwo] using hPowL
    have hp3 : p ≠ 3 := by
      rintro rfl
      norm_num at hSquare
      omega
    have hNotZero : p % 3 ≠ 0 := by
      intro h
      exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.dvd_of_mod_eq_zero h)).symm
    have hRem : (p^2+2) % 3 = 0 := by
      rw [Nat.add_mod, pow_two, Nat.mul_mod p p 3]
      have hSmall := Nat.mod_lt p (by decide : 0 < 3)
      interval_cases (p % 3) <;> norm_num at *
    have hDiv : 3 ∣ q^b := by
      rw [hPowR, ← hSquare]
      exact Nat.dvd_of_mod_eq_zero hRem
    have hq3 : q = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp
      (Nat.prime_three.dvd_of_dvd_pow hDiv)).symm
    have hUpper := Nat.pow_le_pow_right hq.pos (show b ≤ 2 by omega)
    rw [hPowR, hq3] at hUpper
    norm_num at hUpper
    omega

open scoped BigOperators

namespace TwinWindowSquareRoot

private def SquareSieve : Prop :=
  ∃ C : ℝ, 0<C ∧ ∀ U : ℕ, 3≤U → (((Finset.Ioc U (2*U)).filter fun r =>
    r.Prime ∧ (r^2-2).Prime).card : ℝ) ≤ C*U/(Real.log U)^2

private def badWindow (X : ℕ) : Finset ℕ :=
  (Finset.Ioo X (2*X)).filter (fun n => 50*n<51*X ∧ (¬n.Prime ∨ ¬(n+2).Prime))

private noncomputable def higherPowers (Y : ℕ) : Finset ℕ :=
  @Finset.filter ℕ (fun n => ∃ p k : ℕ, p.Prime ∧ 3 ≤ k ∧ n = p^k)
    (fun _ => Classical.propDecidable _) (Finset.range (Y+1))

private def sieveSet (U : ℕ) : Finset ℕ :=
  (Finset.Ioc U (2*U)).filter (fun p => p.Prime ∧ (p^2-2).Prime)

private noncomputable def weight (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2)

private lemma weight_nonneg (n : ℕ) : 0 ≤ weight n :=
  mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg

private lemma sqrt_span (X : ℕ) (hX : 9 ≤ X) :
    3 ≤ X.sqrt ∧ 2*X+2 ≤ (2*X.sqrt)^2 ∧ (2*X.sqrt)^2 ≤ X.sqrt^4 := by
  have hU : 3 ≤ X.sqrt := Nat.le_sqrt'.mpr (by norm_num; omega)
  have hcap := Nat.sqrt_le_add X
  have hmul := Nat.mul_le_mul_left X.sqrt hU
  refine ⟨hU, ?_, ?_⟩
  · nlinarith
  · calc
      (2*X.sqrt)^2 ≤ (X.sqrt^2)^2 := Nat.pow_le_pow_left (by nlinarith) 2
      _ = X.sqrt^4 := by ring

private lemma high_power_log_budget {C : ℝ} (hC : 0 ≤ C) (X : ℕ) (hX : 2 ≤ X) :
    2 * C * ((2*X+2 : ℕ) : ℝ)^(1/3:ℝ) *
      (Real.log (2 + ((2*X+2 : ℕ) : ℝ)))^2 ≤ 576*C*Real.sqrt X := by
  let Y : ℝ := ((2*X+2 : ℕ) : ℝ)
  let A : ℝ := 2 + Y
  have hY : 0 ≤ Y := Nat.cast_nonneg _
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hA1 : 1 ≤ A := by dsimp [A]; linarith
  have hYThird : Y^(1/3:ℝ) ≤ A^(1/3:ℝ) :=
    Real.rpow_le_rpow hY (by dsimp [A]; linarith) (by norm_num)
  have hL : Real.log A ^ 2 ≤ 144 * A^(1/6:ℝ) := by
    calc
      _ ≤ (A^(1/12:ℝ) / (1/12:ℝ))^2 :=
        pow_le_pow_left₀ (Real.log_nonneg hA1) (Real.log_le_rpow_div hA (by norm_num)) 2
      _ = 144 * A^(1/6:ℝ) := by
        rw [div_pow, ← Real.rpow_mul_natCast hA]
        norm_num
        ring
  have hA4 : A ≤ 4*(X:ℝ) := by
    have hXr : (2:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX
    dsimp [A, Y]
    push_cast
    linarith
  have hroot : Real.sqrt A ≤ 2*Real.sqrt X := by
    calc
      _ ≤ Real.sqrt (4*(X:ℝ)) := Real.sqrt_le_sqrt hA4
      _ = _ := by rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by norm_num]
  change 2 * C * Y^(1/3:ℝ) * (Real.log A)^2 ≤ _
  calc
    _ ≤ 2*C * (A^(1/3:ℝ) * (144*A^(1/6:ℝ))) := by
      rw [mul_assoc]
      gcongr
    _ = 288*C*Real.sqrt A := by
      rw [Real.sqrt_eq_rpow, show (1/2:ℝ) = 1/3+1/6 by norm_num,
        Real.rpow_add (show 0 < A by linarith)]
      ring
    _ ≤ _ := by nlinarith

private lemma mainWindow
    {H C : ℝ} (hH : 0 ≤ H) (hC : 0 < C)
    (hMass : ∀ Y : ℕ, 2 ≤ Y →
      (higherPowers Y).sum ArithmeticFunction.vonMangoldt ≤
        H*(Y:ℝ)^(1/3:ℝ)*Real.log (2 + (Y:ℝ)))
    (hSieve : ∀ U : ℕ, 3 ≤ U → ((sieveSet U).card : ℝ) ≤ C*U/(Real.log U)^2)
    (X : ℕ) (hX : 9 ≤ X) :
    (badWindow X).sum weight ≤ (576*H + 16*C)*Real.sqrt X := by
  classical
  let Λ := ArithmeticFunction.vonMangoldt
  let Y : ℕ := 2*X+2
  let U : ℕ := X.sqrt
  let W := Real.log (Y:ℝ)
  let A := higherPowers Y
  let B := badWindow X
  let InSieve (n : ℕ) : Prop := ∃ p ∈ sieveSet U, p^2 = n+2
  let L := B.filter (fun n => n ∈ A)
  let R := B.filter (fun n => n+2 ∈ A)
  let S := B.filter InSieve
  have hY : 2 ≤ Y := by dsimp [Y]; omega
  have hW : 0 ≤ W := Real.log_nonneg (by exact_mod_cast (show 1 ≤ Y by omega))
  obtain ⟨hU, hSpan, hSpan4⟩ := sqrt_span X hX
  have hBounds (n : ℕ) (hn : n ∈ B) : X < n ∧ n < 2*X ∧
      (¬ n.Prime ∨ ¬ (n+2).Prime) := by
    have hh := Finset.mem_filter.mp (show n ∈ badWindow X from hn)
    exact ⟨(Finset.mem_Ioo.mp hh.1).1, (Finset.mem_Ioo.mp hh.1).2, hh.2.2⟩
  have hΛLe (n : ℕ) (hn : 0 < n) (hnY : n ≤ Y) : Λ n ≤ W :=
    ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast hnY))
  have hWinLog (n : ℕ) (hn : n ∈ B) : Λ n ≤ W ∧ Λ (n+2) ≤ W := by
    obtain ⟨hl, hu, _⟩ := hBounds n hn
    exact ⟨hΛLe n (by omega) (by dsimp [Y]; omega),
      hΛLe (n+2) (by omega) (by dsimp [Y]; omega)⟩
  have hLeftBound (n : ℕ) (hn : n ∈ B) : weight n ≤ Λ n * W :=
    mul_le_mul_of_nonneg_left (hWinLog n hn).2 ArithmeticFunction.vonMangoldt_nonneg
  have hRightBound (n : ℕ) (hn : n ∈ B) : weight n ≤ Λ (n+2) * W := by
    rw [weight, mul_comm]
    exact mul_le_mul_of_nonneg_left (hWinLog n hn).1 ArithmeticFunction.vonMangoldt_nonneg
  have hCover (n : ℕ) (hn : n ∈ B) (hw : weight n ≠ 0) :
      n ∈ A ∨ n+2 ∈ A ∨ InSieve n := by
    obtain ⟨hl, hu, hbad⟩ := hBounds n hn
    rcases Conjectures.TwinPrimes.SquareNeighbourModThree n (by omega) hw hbad with
      ⟨p, e, hp, he, heq | heq⟩ | ⟨hnp, p, hp, heq⟩
    · exact Or.inl (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by dsimp [Y]; omega), p, e, hp, he, heq.symm⟩)
    · exact Or.inr (Or.inl (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by dsimp [Y]; omega), p, e, hp, he, heq.symm⟩))
    · right
      right
      have hlo : U < p := Nat.sqrt_lt'.mpr (by omega)
      have hhi : p ≤ 2*U := by
        rw [← Nat.sqrt_eq' p, ← Nat.sqrt_eq' (2*U)]
        apply Nat.sqrt_le_sqrt
        calc
          p^2 = n+2 := heq
          _ ≤ 2*X+2 := by omega
          _ ≤ (2*U)^2 := hSpan
      have hsub : p^2-2 = n := by omega
      exact ⟨p, Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨hlo, hhi⟩, hp, hsub ▸ hnp⟩, heq⟩
  have hSplit : B.sum weight ≤ L.sum weight + R.sum weight + S.sum weight := by
    simp only [L, R, S, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n hn
    by_cases hw : weight n = 0
    · simp [hw]
    have hl : 0 ≤ (if n ∈ A then weight n else 0) := by split <;> simp [weight_nonneg]
    have hr : 0 ≤ (if n+2 ∈ A then weight n else 0) := by split <;> simp [weight_nonneg]
    have hs : 0 ≤ (if InSieve n then weight n else 0) := by split <;> simp [weight_nonneg]
    rcases hCover n hn hw with hm | hm | hm
    · rw [ite_eq_left hm]
      linarith
    · rw [ite_eq_left hm]
      linarith
    · rw [ite_eq_left hm]
      linarith
  have hLeft : L.sum weight ≤ A.sum Λ * W := by
    calc
      _ ≤ ∑ n ∈ L, Λ n * W := Finset.sum_le_sum
        (fun n hn => hLeftBound n (Finset.mem_filter.mp hn).1)
      _ = L.sum Λ * W := by rw [Finset.sum_mul]
      _ ≤ _ := by
        have hsub : L ⊆ A := fun _ hn => (Finset.mem_filter.mp hn).2
        exact mul_le_mul_of_nonneg_right
          (Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)) hW
  have hRight : R.sum weight ≤ A.sum Λ * W := by
    let shift : ℕ ↪ ℕ := ⟨fun n => n+2, by intro a b he; change a+2=b+2 at he; omega⟩
    have hsub : R.map shift ⊆ A := by
      intro n hn
      obtain ⟨m, hm, rfl⟩ := Finset.mem_map.mp hn
      exact (Finset.mem_filter.mp hm).2
    calc
      _ ≤ ∑ n ∈ R, Λ (n+2) * W := Finset.sum_le_sum
        (fun n hn => hRightBound n (Finset.mem_filter.mp hn).1)
      _ = (R.map shift).sum Λ * W := by rw [Finset.sum_map, Finset.sum_mul]; rfl
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)) hW
  have hHigh : 2 * (A.sum Λ * W) ≤ 576*H*Real.sqrt X := by
    let V := Real.log (2+(Y:ℝ))
    have hWV : W ≤ V := Real.log_le_log (by exact_mod_cast (show 0 < Y by omega)) (by linarith)
    have hV : 0 ≤ V := hW.trans hWV
    have hMass := hMass Y hY
    calc
      _ ≤ 2 * (H*(Y:ℝ)^(1/3:ℝ)*V*V) := by
        gcongr
      _ = 2*H*(Y:ℝ)^(1/3:ℝ)*V^2 := by ring
      _ ≤ _ := high_power_log_budget hH X (by omega)
  have hSCard : S.card ≤ (sieveSet U).card := by
    apply Finset.card_le_card_of_injOn (fun n : ℕ => (n+2).sqrt)
    · intro n hn
      obtain ⟨p, hp, hpow⟩ := (Finset.mem_filter.mp (show n ∈ S from hn)).2
      change (n+2).sqrt ∈ sieveSet U
      rwa [← hpow, Nat.sqrt_eq']
    · intro n hn m hm he
      obtain ⟨p, _, hnp⟩ := (Finset.mem_filter.mp (show n ∈ S from hn)).2
      obtain ⟨q, _, hmq⟩ := (Finset.mem_filter.mp (show m ∈ S from hm)).2
      change (n+2).sqrt = (m+2).sqrt at he
      rw [← hnp, ← hmq, Nat.sqrt_eq', Nat.sqrt_eq'] at he
      subst q
      omega
  have hWL : W ≤ 4*Real.log (U:ℝ) := by
    have hy : (Y:ℝ) ≤ (U:ℝ)^4 := by exact_mod_cast hSpan.trans hSpan4
    have h := Real.log_le_log (by exact_mod_cast (show 0 < Y by omega)) hy
    rw [Real.log_pow, Nat.cast_ofNat] at h
    exact h
  have hDistRoot : ((U:ℕ):ℝ) ≤ Real.sqrt X := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast Nat.sqrt_le' X
  have hLogU : 0 < Real.log (U:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < U by omega))
  have hSquare : S.sum weight ≤ 16*C*Real.sqrt X := by
    have hc : (S.card:ℝ) ≤ C*(U:ℝ)/(Real.log (U:ℝ))^2 :=
      (by exact_mod_cast hSCard : (S.card:ℝ) ≤ ((sieveSet U).card:ℝ)).trans (hSieve U hU)
    calc
      _ ≤ ∑ n ∈ S, W^2 := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨hl, hr⟩ := hWinLog n (Finset.mem_filter.mp hn).1
        rw [weight, pow_two]
        exact mul_le_mul hl hr ArithmeticFunction.vonMangoldt_nonneg hW
      _ = (S.card:ℝ)*W^2 := by simp [nsmul_eq_mul]
      _ ≤ (C*(U:ℝ)/(Real.log (U:ℝ))^2) * (4*Real.log (U:ℝ))^2 := by gcongr
      _ = 16*C*(U:ℝ) := by field_simp; ring
      _ ≤ _ := by gcongr
  change B.sum weight ≤ _
  calc
    _ ≤ L.sum weight + R.sum weight + S.sum weight := hSplit
    _ ≤ 2 * (A.sum Λ * W) + 16*C*Real.sqrt X := by linarith
    _ ≤ _ := by nlinarith

private theorem window_contamination_square_root_of_square_sieve (hSieve : SquareSieve) :
    ∃ C : ℝ, 0<C ∧ ∀ X : ℕ, 2≤X →
      (∑ n ∈ (Finset.Ioo X (2*X)).filter
          (fun n => 50*n<51*X ∧ (¬n.Prime ∨ ¬(n+2).Prime)),
        ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2))
      ≤ C*Real.sqrt X := by
  obtain ⟨C, hC, hS⟩ := hSieve
  obtain ⟨H, hH, hPower⟩ := Conjectures.TwinPrimes.HigherPowerLogMass
  let F := ∑ k ∈ Finset.range 9, (badWindow k).sum weight
  have hF : 0 ≤ F := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => weight_nonneg _
  refine ⟨576*H+16*C+(1+F), by positivity, ?_⟩
  intro X hX
  change (badWindow X).sum weight ≤ _
  have hs : (1:ℝ) ≤ Real.sqrt X := Real.le_sqrt_of_sq_le (by exact_mod_cast (show 1^2 ≤ X by omega))
  by_cases h9 : 9 ≤ X
  · have hmain := mainWindow hH.le hC hPower hS X h9
    calc
      _ ≤ (576*H+16*C)*Real.sqrt X := hmain
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  · have hbound : (badWindow X).sum weight ≤ F := by
      apply Finset.single_le_sum (fun _ _ => Finset.sum_nonneg fun _ _ => weight_nonneg _)
      exact Finset.mem_range.mpr (by omega)
    calc
      _ ≤ F := hbound
      _ ≤ (576*H+16*C+(1+F))*1 := by nlinarith
      _ ≤ _ := by gcongr

end TwinWindowSquareRoot

theorem Conjectures.TwinPrimes.WindowContaminationSquareRoot :
    ∃ C : ℝ, 0<C ∧ ∀ X : ℕ, 2≤X →
      (∑ n ∈ (Finset.Ioo X (2*X)).filter
          (fun n => 50*n<51*X ∧ (¬n.Prime ∨ ¬(n+2).Prime)),
        ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2))
      ≤ C*Real.sqrt X :=
  TwinWindowSquareRoot.window_contamination_square_root_of_square_sieve
    Conjectures.TwinPrimes.PrimeSquareMinusTwoUpperSieve
