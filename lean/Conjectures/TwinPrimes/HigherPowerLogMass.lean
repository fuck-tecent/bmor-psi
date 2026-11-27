import Mathlib

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
