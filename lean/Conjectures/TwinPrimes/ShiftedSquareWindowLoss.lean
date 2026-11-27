import Mathlib

/-!
# PREPUB twin-primes: `L-twin-primes-shifted-square-window-loss`
短窗中 `p+2 = q²`（`q` 素）的素数组 `Q`：每个 `p ∈ Q` 唯一对应 `q = √(p+2)`，
`L p ≤ 4 log²(X+2)`；而这类 `q` 落在短区间 `(√(X+2), √(2X+2)]` 中且均为素数，
用 Chebyshev `θ` 的上界控制其个数（`#·log(√(X+2)+1) ≤ Σ log q ≤ θ(√(2X+2)) ≤ log4·√(2X+2)`），
总损失 `≤ 16 log4 · √X · log(2+X)`。仅 Mathlib。
-/

theorem Conjectures.TwinPrimes.ShiftedSquareWindowLoss :
    let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let Q := fun (X : ℕ) => ((w X).filter (fun p => p.Prime ∧ (Nat.sqrt (p+2)).Prime ∧ p+2=(Nat.sqrt (p+2))^2)); let L := fun (p : ℕ) => Real.log p * Real.log (p+2); ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X → (Q X).sum L ≤ C*Real.sqrt X*Real.log (2+(X:ℝ)) := by
  dsimp only
  refine ⟨16 * Real.log 4, by positivity, ?_⟩
  intro X hX
  set w : Finset ℕ := (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X) with hw
  set Q : Finset ℕ := w.filter (fun p => p.Prime ∧ (Nat.sqrt (p+2)).Prime ∧ p+2=(Nat.sqrt (p+2))^2) with hQ
  set L : ℕ → ℝ := fun p => Real.log (p:ℝ) * Real.log ((p:ℝ)+2) with hL
  have hX2 : (2:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX
  have hlogpos : (0:ℝ) < Real.log (2 + (X:ℝ)) := by
    apply Real.log_pos; linarith
  have hlog2pos : (0:ℝ) < Real.log ((X:ℝ)+2) := by
    have h : (1:ℝ) < (X:ℝ)+2 := by linarith
    exact Real.log_pos h
  -- membership information
  have hQmem : ∀ p, p ∈ Q ↔ p ∈ w ∧ p.Prime ∧ (Nat.sqrt (p+2)).Prime ∧ p+2 = (Nat.sqrt (p+2))^2 := by
    intro p; rw [hQ]; simp only [Finset.mem_filter, and_assoc]
  have hwmem : ∀ p, p ∈ w ↔ p < 2*X+1 ∧ X < p ∧ 50*p < 51*X := by
    intro p; rw [hw]; simp only [Finset.mem_filter, Finset.mem_range]
  -- per-term bound
  have hper : ∀ p ∈ Q, L p ≤ 4 * (Real.log (2 + (X:ℝ)))^2 := by
    intro p hp
    rw [hQmem] at hp
    obtain ⟨hpw, hpprime, -, hsq⟩ := hp
    rw [hwmem] at hpw
    obtain ⟨hp2X, hpX, -⟩ := hpw
    have hp_pos : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpprime.one_lt.le
    have hp_le : (p:ℝ) ≤ (X:ℝ)^2 + 4*(X:ℝ) + 4 := by
      have : (p:ℝ) ≤ 2*(X:ℝ) := by
        have : p ≤ 2*X := by omega
        exact_mod_cast this
      nlinarith
    have hp2_le : (p:ℝ) + 2 ≤ (X:ℝ)^2 + 4*(X:ℝ) + 4 := by
      have : (p:ℝ) ≤ 2*(X:ℝ) := by
        have : p ≤ 2*X := by omega
        exact_mod_cast this
      nlinarith
    have hbase : (0:ℝ) < (X:ℝ) + 2 := by linarith
    have hq : ((X:ℝ) + 2)^2 = (X:ℝ)^2 + 4*(X:ℝ) + 4 := by ring
    have h1 : Real.log (p:ℝ) ≤ 2 * Real.log (2 + (X:ℝ)) := by
      have h := Real.log_le_log (by linarith : (0:ℝ) < (p:ℝ)) (by linarith : (p:ℝ) ≤ (2+(X:ℝ))^2)
      rw [Real.log_pow] at h
      have h2 : (2:ℝ) * Real.log (2 + (X:ℝ)) = Real.log (2+(X:ℝ)) * 2 := by ring
      calc Real.log (p:ℝ) ≤ (2:ℝ) * Real.log (2+(X:ℝ)) := h
        _ = 2 * Real.log (2 + (X:ℝ)) := rfl
    have h2 : Real.log ((p:ℝ)+2) ≤ 2 * Real.log (2 + (X:ℝ)) := by
      have hp2pos : (0:ℝ) < (p:ℝ)+2 := by linarith
      have h := Real.log_le_log hp2pos (by linarith : (p:ℝ)+2 ≤ (2+(X:ℝ))^2)
      rw [Real.log_pow] at h
      exact h
    have h1nn : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg hp_pos
    have h2nn : 0 ≤ Real.log ((p:ℝ)+2) := by
      apply Real.log_nonneg; linarith
    rw [hL]; change Real.log (p:ℝ) * Real.log ((p:ℝ)+2) ≤ 4 * (Real.log (2 + (X:ℝ)))^2
    have hstep : Real.log (p:ℝ) * Real.log ((p:ℝ)+2) ≤
        (2 * Real.log (2+(X:ℝ))) * (2 * Real.log (2+(X:ℝ))) := by
      apply mul_le_mul h1 h2 h2nn (by linarith [hlogpos])
    calc Real.log (p:ℝ) * Real.log ((p:ℝ)+2) ≤ (2*Real.log (2+(X:ℝ)))*(2*Real.log (2+(X:ℝ))) := hstep
      _ = 4 * (Real.log (2 + (X:ℝ)))^2 := by ring
  -- the counting set `T` and injection `Q → T`
  set T : Finset ℕ := (Finset.range (Nat.sqrt (2*X+2) + 1)).filter (fun q => q.Prime ∧ Nat.sqrt (X+2) < q) with hT
  have hTmem : ∀ q, q ∈ T ↔ q < Nat.sqrt (2*X+2) + 1 ∧ q.Prime ∧ Nat.sqrt (X+2) < q := by
    intro q; rw [hT]; simp only [Finset.mem_filter, Finset.mem_range, and_assoc]
  have hcard : Q.card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (fun p => Nat.sqrt (p+2))
    · intro p hp
      rw [Finset.mem_coe] at hp
      rw [hQmem] at hp
      obtain ⟨hpw, hpprime, hqprime, hsq⟩ := hp
      rw [hwmem] at hpw
      obtain ⟨hp2X, hpX, -⟩ := hpw
      change Nat.sqrt (p+2) ∈ T
      rw [hTmem]
      have hle : p+2 ≤ 2*X+2 := by omega
      have hsle : Nat.sqrt (p+2) ≤ Nat.sqrt (2*X+2) := Nat.sqrt_le_sqrt hle
      have hgt : Nat.sqrt (X+2) < Nat.sqrt (p+2) := by
        rw [Nat.sqrt_lt]
        have hsq' : (Nat.sqrt (p+2)) * (Nat.sqrt (p+2)) = p+2 := by
          rw [← pow_two, ← hsq]
        rw [hsq']; omega
      exact ⟨Nat.lt_succ_of_le hsle, hqprime, hgt⟩
    · intro a ha b hb hab
      rw [Finset.mem_coe] at ha hb
      rw [hQmem] at ha hb
      obtain ⟨-, -, -, hsa⟩ := ha
      obtain ⟨-, -, -, hsb⟩ := hb
      have h1 : (Nat.sqrt (a+2)) * (Nat.sqrt (a+2)) = a+2 := by rw [← pow_two, ← hsa]
      have h2 : (Nat.sqrt (b+2)) * (Nat.sqrt (b+2)) = b+2 := by rw [← pow_two, ← hsb]
      have hab' : Nat.sqrt (a+2) = Nat.sqrt (b+2) := hab
      have h3 : a+2 = b+2 := by rw [← h1, ← h2, hab']
      omega
  -- upper/lower bounds for the logarithmic mass of `T`
  have hTsum_upper : (∑ q ∈ T, Real.log (q:ℝ)) ≤ Real.log 4 * Real.sqrt (2*X+2) := by
    have hsub : T ⊆ (Nat.sqrt (2*X+2)).primesLE := by
      intro q hq
      rw [hTmem] at hq
      obtain ⟨h1, h2, -⟩ := hq
      rw [Nat.primesLE_eq_filter_range, Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr h1, h2⟩
    have hnonneg : ∀ q ∈ (Nat.sqrt (2*X+2)).primesLE, q ∉ T → 0 ≤ Real.log (q:ℝ) := by
      intro q hq _
      rw [Nat.primesLE_eq_filter_range, Finset.mem_filter] at hq
      have hq2 : (2:ℕ) ≤ q := hq.2.two_le
      apply Real.log_nonneg
      exact_mod_cast (by omega : 1 ≤ q)
    calc (∑ q ∈ T, Real.log (q:ℝ)) ≤ ∑ q ∈ (Nat.sqrt (2*X+2)).primesLE, Real.log (q:ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
      _ = Chebyshev.theta ((Nat.sqrt (2*X+2) : ℕ) : ℝ) :=
          (Chebyshev.theta_eq_sum_primesLE_log (Nat.sqrt (2*X+2))).symm
      _ ≤ Real.log 4 * ((Nat.sqrt (2*X+2) : ℕ) : ℝ) :=
          Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)
      _ ≤ Real.log 4 * Real.sqrt (2*(X:ℝ)+2) := by
          have hcast : ((2*X+2 : ℕ) : ℝ) = 2*(X:ℝ)+2 := by push_cast; ring
          rw [← hcast]
          exact mul_le_mul_of_nonneg_left Real.nat_sqrt_le_real_sqrt (by positivity)
  have hTsum_lower : (T.card : ℝ) * Real.log ((Nat.sqrt (X+2) : ℕ) + 1) ≤ ∑ q ∈ T, Real.log (q:ℝ) := by
    have h1 : (∑ q ∈ T, Real.log (((Nat.sqrt (X+2) : ℕ) : ℝ) + 1)) ≤ ∑ q ∈ T, Real.log (q:ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      rw [hTmem] at hq
      obtain ⟨-, hqprime, hqgt⟩ := hq
      have hqpos : (0:ℝ) < (q:ℝ) := by
        have : (2:ℕ) ≤ q := hqprime.two_le
        exact_mod_cast (by omega : 0 < q)
      apply Real.log_le_log (by positivity)
      have : Nat.sqrt (X+2) + 1 ≤ q := by omega
      exact_mod_cast this
    calc (T.card : ℝ) * Real.log ((Nat.sqrt (X+2) : ℕ) + 1)
        = ∑ q ∈ T, Real.log (((Nat.sqrt (X+2) : ℕ) : ℝ) + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ q ∈ T, Real.log (q:ℝ) := h1
  -- convert to a cardinality bound
  have hlog_lower : Real.log (((Nat.sqrt (X+2) : ℕ) : ℝ) + 1) ≥ Real.log (2 + (X:ℝ)) / 2 := by
    have hcast : ((X+2 : ℕ) : ℝ) = (X:ℝ) + 2 := by push_cast; ring
    have hN := Nat.lt_succ_sqrt' (X+2)
    have hN' : ((X+2 : ℕ) : ℝ) < (((Nat.sqrt (X+2) : ℕ) : ℝ) + 1)^2 := by exact_mod_cast hN
    rw [hcast] at hN'
    have hy : (0:ℝ) < ((Nat.sqrt (X+2) : ℕ) : ℝ) + 1 := by positivity
    have hsq_lt_r : Real.sqrt ((X:ℝ)+2) < ((Nat.sqrt (X+2) : ℕ) : ℝ) + 1 := by
      rw [Real.sqrt_lt' hy]
      exact hN'
    have hlog : Real.log (Real.sqrt ((X:ℝ)+2)) ≤ Real.log (((Nat.sqrt (X+2) : ℕ) : ℝ) + 1) :=
      Real.log_le_log (by positivity) (le_of_lt hsq_lt_r)
    rw [Real.log_sqrt (by positivity : (0:ℝ) ≤ (X:ℝ)+2)] at hlog
    have e2 : Real.log ((X:ℝ)+2) = Real.log (2 + (X:ℝ)) := by congr 1; ring
    rw [e2] at hlog
    linarith
  have hcard_bound : (T.card : ℝ) ≤ 2 * Real.log 4 * Real.sqrt (2*(X:ℝ)+2) / Real.log (2 + (X:ℝ)) := by
    have hcard0 : (0:ℝ) ≤ (T.card : ℝ) := Nat.cast_nonneg _
    have hlt : (0:ℝ) < Real.log (((Nat.sqrt (X+2) : ℕ) : ℝ) + 1) := by
      apply Real.log_pos
      have hs2 : (2:ℕ) ≤ Nat.sqrt (X+2) := by
        rw [Nat.le_sqrt]; norm_num; omega
      have hs2' : (2:ℝ) ≤ ((Nat.sqrt (X+2) : ℕ) : ℝ) := by exact_mod_cast hs2
      linarith
    -- card * log ≤ log4 * sqrt(2X+2), and log ≥ log(X+2)/2
    have hstep : (T.card : ℝ) * Real.log (((Nat.sqrt (X+2) : ℕ) : ℝ) + 1) ≤ Real.log 4 * Real.sqrt (2*(X:ℝ)+2) := by
      calc (T.card : ℝ) * Real.log (((Nat.sqrt (X+2) : ℕ) : ℝ) + 1) ≤ ∑ q ∈ T, Real.log (q:ℝ) := hTsum_lower
        _ ≤ Real.log 4 * Real.sqrt (2*(X:ℝ)+2) := hTsum_upper
    have hhalf : Real.log (((Nat.sqrt (X+2) : ℕ) : ℝ) + 1) ≥ Real.log (2 + (X:ℝ)) / 2 := hlog_lower
    have := hstep
    rw [le_div_iff₀ hlogpos]
    calc (T.card : ℝ) * Real.log (2 + (X:ℝ))
        ≤ (T.card : ℝ) * (2 * Real.log (((Nat.sqrt (X+2) : ℕ) : ℝ) + 1)) := by
          apply mul_le_mul_of_nonneg_left _ hcard0
          linarith
      _ = 2 * ((T.card : ℝ) * Real.log (((Nat.sqrt (X+2) : ℕ) : ℝ) + 1)) := by ring
      _ ≤ 2 * (Real.log 4 * Real.sqrt (2*(X:ℝ)+2)) := by nlinarith [hstep]
      _ = 2 * Real.log 4 * Real.sqrt (2*(X:ℝ)+2) := by ring
  -- final assembly
  have hsumQ : (∑ p ∈ Q, L p) ≤ (Q.card : ℝ) * (4 * (Real.log (2 + (X:ℝ)))^2) := by
    calc (∑ p ∈ Q, L p) ≤ ∑ p ∈ Q, (4 * (Real.log (2 + (X:ℝ)))^2) :=
          Finset.sum_le_sum hper
      _ = (Q.card : ℝ) * (4 * (Real.log (2 + (X:ℝ)))^2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcardQ : (Q.card : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hcard
  have hsqrt_le : Real.sqrt (2*(X:ℝ)+2) ≤ 2 * Real.sqrt (X:ℝ) := by
    have h4 : Real.sqrt (4 * (X:ℝ)) = 2 * Real.sqrt (X:ℝ) := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
      norm_num
    rw [← h4]
    apply Real.sqrt_le_sqrt
    nlinarith [hX2]
  calc (Q.sum L) ≤ (Q.card : ℝ) * (4 * (Real.log (2 + (X:ℝ)))^2) := hsumQ
    _ ≤ (T.card : ℝ) * (4 * (Real.log (2 + (X:ℝ)))^2) := by
        apply mul_le_mul_of_nonneg_right hcardQ (by positivity)
    _ ≤ (2 * Real.log 4 * Real.sqrt (2*(X:ℝ)+2) / Real.log (2 + (X:ℝ))) *
          (4 * (Real.log (2 + (X:ℝ)))^2) := by
        apply mul_le_mul_of_nonneg_right hcard_bound (by positivity)
    _ = 8 * Real.log 4 * Real.sqrt (2*(X:ℝ)+2) * Real.log (2 + (X:ℝ)) := by
        field_simp
        ring
    _ ≤ 8 * Real.log 4 * (2 * Real.sqrt (X:ℝ)) * Real.log (2 + (X:ℝ)) := by
        have hA : (0:ℝ) ≤ 8 * Real.log 4 := by positivity
        have hD : (0:ℝ) ≤ Real.log (2 + (X:ℝ)) := le_of_lt hlogpos
        have hAD : (0:ℝ) ≤ 8 * Real.log 4 * Real.log (2 + (X:ℝ)) := mul_nonneg hA hD
        calc 8 * Real.log 4 * Real.sqrt (2*(X:ℝ)+2) * Real.log (2 + (X:ℝ))
            = (8 * Real.log 4 * Real.log (2 + (X:ℝ))) * Real.sqrt (2*(X:ℝ)+2) := by ring
          _ ≤ (8 * Real.log 4 * Real.log (2 + (X:ℝ))) * (2 * Real.sqrt (X:ℝ)) := by
              apply mul_le_mul_of_nonneg_left hsqrt_le hAD
          _ = 8 * Real.log 4 * (2 * Real.sqrt (X:ℝ)) * Real.log (2 + (X:ℝ)) := by ring
    _ = 16 * Real.log 4 * Real.sqrt (X:ℝ) * Real.log (2 + (X:ℝ)) := by ring

theorem PEqualNP.Outside.L_twin_primes_shifted_square_window_loss :
    let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let Q := fun (X : ℕ) => ((w X).filter (fun p => p.Prime ∧ (Nat.sqrt (p+2)).Prime ∧ p+2=(Nat.sqrt (p+2))^2)); let L := fun (p : ℕ) => Real.log p * Real.log (p+2); ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X → (Q X).sum L ≤ C*Real.sqrt X*Real.log (2+(X:ℝ)) :=
  Conjectures.TwinPrimes.ShiftedSquareWindowLoss
