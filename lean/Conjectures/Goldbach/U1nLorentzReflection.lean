import Mathlib

theorem Conjectures.Goldbach.U1nLorentzReflection :
    ∀ (N : ℕ) (a : ℕ → ℝ), 2 ≤ N → let z : ℕ → ℂ := fun ξ => ((N : ℝ).sqrt : ℂ)⁻¹ * ∑ n ∈ Finset.Ico 1 N, (a n : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * (n : ℂ) * (ξ : ℂ) / (N : ℂ)); (∑ ξ ∈ Finset.Ico 1 N, (z ξ) ^ 2 + (z 0) ^ 2 = ((∑ n ∈ Finset.Ico 1 N, a n * a (N - n) : ℝ) : ℂ)) ∧ (‖z 0‖ ^ 2 - ∑ ξ ∈ Finset.Ico 1 N, ‖z ξ‖ ^ 2 = 2 / (N : ℝ) * (∑ n ∈ Finset.Ico 1 N, a n) ^ 2 - ∑ n ∈ Finset.Ico 1 N, (a n) ^ 2) := by
  intro N a hN z
  have hN0 : N ≠ 0 := by omega
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  let c : ℂ := ((N : ℝ).sqrt : ℂ)⁻¹
  let rho : ℂ := Complex.exp (-(2 * (Real.pi:ℂ) * Complex.I) / (N : ℂ))
  have hs : ((N:ℝ).sqrt : ℂ) ≠ 0 := by
    have hp : (0:ℝ) < (N:ℝ).sqrt := Real.sqrt_pos.mpr hNpos
    exact_mod_cast hp.ne'
  have hs_sq : ((N:ℝ).sqrt : ℂ) * ((N:ℝ).sqrt : ℂ) = (N:ℂ) := by
    have h : ((N:ℝ).sqrt) ^ 2 = (N:ℝ) := Real.sq_sqrt hNpos.le
    have h2 : ((N:ℝ).sqrt : ℂ) ^ 2 = (N:ℂ) := by exact_mod_cast h
    rwa [pow_two] at h2
  have hc_sq : c * c = (N:ℂ)⁻¹ := by
    dsimp only [c]
    rw [← mul_inv_rev, hs_sq]
  have hNc : (N:ℂ) ≠ 0 := by exact_mod_cast hN0
  have hrhoN : rho ^ N = 1 := by
    dsimp only [rho]
    rw [← Complex.exp_nat_mul]
    have harg : (N:ℂ) * (-(2 * (Real.pi:ℂ) * Complex.I) / (N:ℂ)) = -(2 * (Real.pi:ℂ) * Complex.I) := by
      field_simp
    rw [harg]
    simp [Complex.exp_neg, Complex.exp_two_pi_mul_I]
  have hζr : IsPrimitiveRoot (Complex.exp (2 * (Real.pi:ℂ) * Complex.I / (N:ℂ))) N := by
    have h0 := Complex.isPrimitiveRoot_exp_of_coprime 1 N hN0 (by simp [Nat.Coprime])
    simpa [div_eq_mul_inv] using h0
  have hrho_eq : rho = (Complex.exp (2 * (Real.pi:ℂ) * Complex.I / (N:ℂ)))⁻¹ := by
    dsimp only [rho]
    have hneg : -(2 * (Real.pi:ℂ) * Complex.I) / (N:ℂ) = -((2 * (Real.pi:ℂ) * Complex.I) / (N:ℂ)) := by ring
    rw [hneg, Complex.exp_neg]
  have hζinv : IsPrimitiveRoot rho N := by
    rw [hrho_eq]
    exact hζr.inv
  have hTgen : ∀ d : ℂ, d ^ N = 1 → (∑ ξ ∈ Finset.Ico 1 N, d ^ ξ) = if d = 1 then (N:ℂ) - 1 else -1 := by
    intro d hd
    by_cases h1 : d = 1
    · rw [if_pos h1, h1]
      simp only [one_pow]
      rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Ico]
      rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    · rw [if_neg h1, geom_sum_Ico h1 (by omega : 1 ≤ N), hd, pow_one]
      field_simp
      ring
  have hExp : ∀ n ξ : ℕ, Complex.exp (-2 * Real.pi * Complex.I * (n:ℂ) * (ξ:ℂ) / (N:ℂ)) = (rho ^ n) ^ ξ := by
    intro n ξ
    dsimp only [rho]
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have hz : ∀ ξ, z ξ = c * ∑ n ∈ Finset.Ico 1 N, (a n : ℂ) * (rho ^ n) ^ ξ := by
    intro ξ
    dsimp only [c, z]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [hExp n ξ]
  have hprod : ∀ n m ξ : ℕ, (rho ^ n) ^ ξ * (rho ^ m) ^ ξ = (rho ^ (n + m)) ^ ξ := by
    intro n m ξ
    rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring
  have hTval : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * N - 2 →
      (∑ ξ ∈ Finset.Ico 1 N, (rho ^ k) ^ ξ) = if k = N then ((N:ℂ) - 1) else -1 := by
    intro k hk1 hk2
    have hd : (rho ^ k) ^ N = 1 := by
      rw [← pow_mul, mul_comm k N, pow_mul, hrhoN, one_pow]
    have hT := hTgen (rho ^ k) hd
    by_cases hkN : k = N
    · rw [if_pos hkN]
      rw [if_pos (by rw [hkN, hrhoN] : rho ^ k = 1)] at hT
      exact hT
    · rw [if_neg hkN]
      have hkne : rho ^ k ≠ 1 := by
        rcases lt_or_gt_of_ne hkN with hlt | hgt
        · exact hζinv.pow_ne_one_of_pos_of_lt (by omega) hlt
        · have h2 : k - N < N := by omega
          have hk_eq : rho ^ k = rho ^ (k - N) := by
            have hsub : k = (k - N) + N := by omega
            nth_rewrite 1 [hsub]
            rw [pow_add, hrhoN, mul_one]
          rw [hk_eq]
          exact hζinv.pow_ne_one_of_pos_of_lt (by omega) h2
      rw [if_neg hkne] at hT
      exact hT
  let A : ℂ := ∑ n ∈ Finset.Ico 1 N, (a n : ℂ)
  have hz0 : z 0 = c * A := by
    rw [hz 0]
    congr 1
    dsimp only [A]
    simp_rw [pow_zero, mul_one]
  have hsq : ∀ ξ, (z ξ) ^ 2 = c ^ 2 * ∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N,
      (a n : ℂ) * (a m : ℂ) * (rho ^ (n + m)) ^ ξ := by
    intro ξ
    rw [hz ξ, pow_two]
    have hSS : (∑ n ∈ Finset.Ico 1 N, (a n : ℂ) * (rho ^ n) ^ ξ) *
        (∑ n ∈ Finset.Ico 1 N, (a n : ℂ) * (rho ^ n) ^ ξ) =
        ∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N,
          (a n : ℂ) * (a m : ℂ) * (rho ^ (n + m)) ^ ξ := by
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      calc (a n : ℂ) * (rho ^ n) ^ ξ * ((a m : ℂ) * (rho ^ m) ^ ξ)
          = (a n : ℂ) * (a m : ℂ) * ((rho ^ n) ^ ξ * (rho ^ m) ^ ξ) := by ring
        _ = (a n : ℂ) * (a m : ℂ) * (rho ^ (n + m)) ^ ξ := by rw [hprod n m ξ]
    calc (c * ∑ n ∈ Finset.Ico 1 N, (a n : ℂ) * (rho ^ n) ^ ξ) *
          (c * ∑ n ∈ Finset.Ico 1 N, (a n : ℂ) * (rho ^ n) ^ ξ)
        = c * c * ((∑ n ∈ Finset.Ico 1 N, (a n : ℂ) * (rho ^ n) ^ ξ) *
            (∑ n ∈ Finset.Ico 1 N, (a n : ℂ) * (rho ^ n) ^ ξ)) := by ring
      _ = c * c * (∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N,
            (a n : ℂ) * (a m : ℂ) * (rho ^ (n + m)) ^ ξ) := by rw [hSS]
      _ = c ^ 2 * (∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N,
            (a n : ℂ) * (a m : ℂ) * (rho ^ (n + m)) ^ ξ) := by ring
  have hsumz : ∑ ξ ∈ Finset.Ico 1 N, (z ξ) ^ 2 =
      c ^ 2 * ∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N,
        (a n : ℂ) * (a m : ℂ) * (if n + m = N then ((N:ℂ) - 1) else -1) := by
    simp_rw [hsq]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    calc ∑ ξ ∈ Finset.Ico 1 N, (a n : ℂ) * (a m : ℂ) * (rho ^ (n + m)) ^ ξ
        = (a n : ℂ) * (a m : ℂ) * ∑ ξ ∈ Finset.Ico 1 N, (rho ^ (n + m)) ^ ξ := by
          rw [Finset.mul_sum]
      _ = (a n : ℂ) * (a m : ℂ) * (if n + m = N then ((N:ℂ) - 1) else -1) := by
          have hn1 : 1 ≤ n := (Finset.mem_Ico.mp hn).1
          have hn2 : n < N := (Finset.mem_Ico.mp hn).2
          have hm1 : 1 ≤ m := (Finset.mem_Ico.mp hm).1
          have hm2 : m < N := (Finset.mem_Ico.mp hm).2
          rw [hTval (n + m) (by omega) (by omega)]
  have hsumid : ∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N,
        (a n : ℂ) * (a m : ℂ) * (if n + m = N then ((N:ℂ) - 1) else -1)
      = -(A * A) + (N:ℂ) * (∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N,
          (if n + m = N then (a n : ℂ) * (a m : ℂ) else 0)) := by
    have hpt : ∀ n m : ℕ, (a n : ℂ) * (a m : ℂ) * (if n + m = N then ((N:ℂ) - 1) else -1)
        = -((a n : ℂ) * (a m : ℂ)) + (N:ℂ) *
            (if n + m = N then (a n : ℂ) * (a m : ℂ) else 0) := by
      intro n m
      by_cases h : n + m = N
      · rw [if_pos h, if_pos h]; ring
      · rw [if_neg h, if_neg h]; ring
    have hneg : ∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N, -((a n : ℂ) * (a m : ℂ)) = -(A * A) := by
      simp_rw [Finset.sum_neg_distrib]
      congr 1
      dsimp only [A]
      rw [Finset.sum_mul_sum]
    have hNs : ∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N,
          (N:ℂ) * (if n + m = N then (a n : ℂ) * (a m : ℂ) else 0)
        = (N:ℂ) * (∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N,
          (if n + m = N then (a n : ℂ) * (a m : ℂ) else 0)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
    simp_rw [hpt]
    simp_rw [Finset.sum_add_distrib]
    rw [hneg, hNs]
  have hS : (∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N,
        (if n + m = N then (a n : ℂ) * (a m : ℂ) else 0))
      = ∑ n ∈ Finset.Ico 1 N, ((a n : ℂ) * (a (N - n) : ℂ)) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Ico.mp hn).1
    have hn2 : n < N := (Finset.mem_Ico.mp hn).2
    have hmN : N - n ∈ Finset.Ico 1 N := by
      rw [Finset.mem_Ico]
      constructor <;> omega
    rw [Finset.sum_eq_single (N - n)]
    · rw [if_pos (Nat.add_sub_of_le (Nat.le_of_lt hn2))]
    · intro m hm hne
      rw [if_neg]
      intro h
      exact hne (by omega)
    · intro hnot
      exact absurd hmN hnot
  have hcast : ((∑ n ∈ Finset.Ico 1 N, a n * a (N - n) : ℝ) : ℂ)
      = ∑ n ∈ Finset.Ico 1 N, (a n : ℂ) * (a (N - n) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Complex.ofReal_mul]
  have hc2N : c ^ 2 * (N:ℂ) = 1 := by
    rw [pow_two, hc_sq, inv_mul_cancel₀ hNc]
  constructor
  · calc (∑ ξ ∈ Finset.Ico 1 N, (z ξ) ^ 2) + (z 0) ^ 2
        = c ^ 2 * (∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N,
            (a n : ℂ) * (a m : ℂ) * (if n + m = N then ((N:ℂ) - 1) else -1)) + (c * A) ^ 2 := by
          rw [hsumz, hz0]
      _ = ((∑ n ∈ Finset.Ico 1 N, a n * a (N - n) : ℝ) : ℂ) := by
          rw [hsumid]
          rw [show ((∑ n ∈ Finset.Ico 1 N, a n * a (N - n) : ℝ) : ℂ)
              = ∑ n ∈ Finset.Ico 1 N, (a n : ℂ) * (a (N - n) : ℂ) from hcast]
          rw [← hS]
          have hA2 : (c * A) ^ 2 = c ^ 2 * (A * A) := by ring
          rw [hA2]
          have key : c ^ 2 * (-(A * A) + (N:ℂ) * (∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N,
                (if n + m = N then (a n : ℂ) * (a m : ℂ) else 0))) + c ^ 2 * (A * A)
              = c ^ 2 * (N:ℂ) * (∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N,
                (if n + m = N then (a n : ℂ) * (a m : ℂ) else 0)) := by ring
          rw [key, hc2N, one_mul]
  · -- second conjunct
    have hnorm_complex : ∀ (w : ℂ), ((‖w‖^2 : ℝ) : ℂ) = w * star w := by
      intro w
      rw [Complex.star_def, Complex.ofReal_pow]
      exact (RCLike.mul_conj w).symm
    have hnorm_rho : ‖rho‖ = 1 := by
      have h1 : rho = Complex.exp (((-(2 * Real.pi / (N:ℝ))) : ℝ) * Complex.I) := by
        dsimp only [rho]
        congr 1
        push_cast
        field_simp
      rw [h1, Complex.norm_exp_ofReal_mul_I]
    have hstar_rho : star rho = rho⁻¹ := by
      rw [Complex.star_def]
      exact (RCLike.inv_eq_conj hnorm_rho).symm
    have hstar_rho_m : ∀ m : ℕ, m ≤ N → star (rho^m) = rho^(N-m) := by
      intro m hm
      have h2 : star (rho^m) = (rho^m)⁻¹ := by
        rw [star_pow, hstar_rho, inv_pow]
      rw [h2]
      exact inv_eq_of_mul_eq_one_right (by rw [← pow_add, show m + (N - m) = N by omega, hrhoN])
    have hstarpow : ∀ m ξ : ℕ, m < N → star ((rho^m)^ξ) = (rho^(N-m))^ξ := by
      intro m ξ hm
      rw [star_pow, hstar_rho_m m (by omega)]
    have hTstar : ∀ m ξ : ℕ, m < N → star ((a m : ℂ) * (rho^m)^ξ) = (a m : ℂ) * (rho^(N-m))^ξ := by
      intro m ξ hm
      rw [star_mul, hstarpow m ξ hm, Complex.star_def, Complex.conj_ofReal, mul_comm]
    have hS : ∀ ξ : ℕ, (∑ n ∈ Finset.Ico 1 N, (a n : ℂ) * (rho^n)^ξ) * star (∑ m ∈ Finset.Ico 1 N, (a m : ℂ) * (rho^m)^ξ)
        = ∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N, ((a n * a m : ℝ) : ℂ) * (rho^(n + N - m))^ξ := by
      intro ξ
      have h1 : star (∑ m ∈ Finset.Ico 1 N, (a m : ℂ) * (rho^m)^ξ)
          = ∑ m ∈ Finset.Ico 1 N, (a m : ℂ) * (rho^(N-m))^ξ := by
        rw [star_sum]
        apply Finset.sum_congr rfl
        intro m hm
        exact hTstar m ξ (Finset.mem_Ico.mp hm).2
      rw [h1, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      have hnN : n < N := (Finset.mem_Ico.mp hn).2
      have hmN : m < N := (Finset.mem_Ico.mp hm).2
      have hbase : rho^n * rho^(N-m) = rho^(n + N - m) := by
        rw [← pow_add]
        congr 1
        omega
      rw [← hbase, mul_pow, Complex.ofReal_mul]
      ring
    have hsumT : (∑ ξ ∈ Finset.Ico 1 N, (∑ n ∈ Finset.Ico 1 N, (a n : ℂ) * (rho^n)^ξ) * star (∑ m ∈ Finset.Ico 1 N, (a m : ℂ) * (rho^m)^ξ))
        = ∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N, ((a n * a m : ℝ) : ℂ) * (if n = m then ((N:ℂ) - 1) else -1) := by
      simp_rw [hS]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Ico.mp hn).1
      have hn2 : n < N := (Finset.mem_Ico.mp hn).2
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      have hm1 : 1 ≤ m := (Finset.mem_Ico.mp hm).1
      have hm2 : m < N := (Finset.mem_Ico.mp hm).2
      rw [← Finset.mul_sum]
      congr 1
      rw [hTval (n + N - m) (by omega) (by omega)]
      by_cases h : n = m
      · rw [if_pos (by omega : n + N - m = N), if_pos h]
      · rw [if_neg (by omega : ¬ n + N - m = N), if_neg h]
    have hdouble : (∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N, (a n * a m) * (if n = m then ((N:ℝ) - 1) else -1))
        = (N:ℝ) * (∑ n ∈ Finset.Ico 1 N, (a n)^2) - (∑ n ∈ Finset.Ico 1 N, a n)^2 := by
      have hiff : ∀ n m : ℕ, (if n = m then ((N:ℝ) - 1) else -1) = -1 + (N:ℝ) * (if n = m then (1:ℝ) else 0) := by
        intro n m
        by_cases h : n = m
        · rw [if_pos h, if_pos h]; ring
        · rw [if_neg h, if_neg h]; ring
      have hterm : ∀ n m : ℕ, (a n * a m) * (if n = m then ((N:ℝ) - 1) else -1)
          = -(a n * a m) + (N:ℝ) * (a n * a m * (if n = m then (1:ℝ) else 0)) := by
        intro n m
        rw [hiff]
        ring
      simp_rw [hterm]
      simp_rw [Finset.sum_add_distrib]
      have hneg : (∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N, -(a n * a m))
          = - (∑ n ∈ Finset.Ico 1 N, a n)^2 := by
        simp_rw [Finset.sum_neg_distrib]
        have hsq : (∑ n ∈ Finset.Ico 1 N, a n)^2 = ∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N, a n * a m := by
          rw [pow_two, Finset.sum_mul_sum]
        rw [hsq]
      have hNs : (∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N, (N:ℝ) * (a n * a m * (if n = m then (1:ℝ) else 0)))
          = (N:ℝ) * (∑ n ∈ Finset.Ico 1 N, (a n)^2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        have hinner : (∑ m ∈ Finset.Ico 1 N, a n * a m * (if n = m then (1:ℝ) else 0)) = (a n)^2 := by
          rw [Finset.sum_eq_single n]
          · rw [if_pos rfl]; ring
          · intro m hm hne; rw [if_neg (Ne.symm hne)]; ring
          · intro hnnot; exact absurd hn hnnot
        rw [← Finset.mul_sum]
        rw [hinner]
      rw [hneg, hNs]
      ring
    have hsumR : (∑ ξ ∈ Finset.Ico 1 N, ‖∑ n ∈ Finset.Ico 1 N, (a n : ℂ) * (rho^n)^ξ‖^2)
        = ∑ n ∈ Finset.Ico 1 N, ∑ m ∈ Finset.Ico 1 N, (a n * a m) * (if n = m then ((N:ℝ) - 1) else -1) := by
      apply Complex.ofReal_inj.mp
      rw [Complex.ofReal_sum]
      simp_rw [hnorm_complex]
      rw [hsumT]
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro m hm
      by_cases h : n = m
      · rw [if_pos h, if_pos h]; push_cast; ring
      · rw [if_neg h, if_neg h]; push_cast; ring
    have hT0 : (∑ n ∈ Finset.Ico 1 N, (a n : ℂ) * (rho^n)^0) = A := by
      dsimp only [A]
      simp
    have hAcast : A = ((∑ n ∈ Finset.Ico 1 N, a n : ℝ) : ℂ) := by
      dsimp only [A]
      rw [Complex.ofReal_sum]
    have hAnorm : ‖A‖^2 = (∑ n ∈ Finset.Ico 1 N, a n)^2 := by
      rw [hAcast, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hc_norm2 : ‖c‖^2 = (N:ℝ)⁻¹ := by
      have hc : ‖c‖ = ((N:ℝ).sqrt)⁻¹ := by
        dsimp only [c]
        rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg (N:ℝ))]
      rw [hc, inv_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ (N:ℝ))]
    have hnormzξ : ∀ ξ : ℕ, ‖z ξ‖^2 = (N:ℝ)⁻¹ * ‖∑ n ∈ Finset.Ico 1 N, (a n : ℂ) * (rho^n)^ξ‖^2 := by
      intro ξ
      rw [hz ξ, norm_mul, mul_pow, hc_norm2]
    have hzsum : (∑ ξ ∈ Finset.Ico 1 N, ‖z ξ‖^2)
        = (N:ℝ)⁻¹ * (∑ ξ ∈ Finset.Ico 1 N, ‖∑ n ∈ Finset.Ico 1 N, (a n : ℂ) * (rho^n)^ξ‖^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ξ hξ
      exact hnormzξ ξ
    calc ‖z 0‖^2 - ∑ ξ ∈ Finset.Ico 1 N, ‖z ξ‖^2
        = (N:ℝ)⁻¹ * ‖A‖^2 - (N:ℝ)⁻¹ * (∑ ξ ∈ Finset.Ico 1 N, ‖∑ n ∈ Finset.Ico 1 N, (a n : ℂ) * (rho^n)^ξ‖^2) := by
          rw [hzsum, hnormzξ 0, hT0]
      _ = (N:ℝ)⁻¹ * (∑ n ∈ Finset.Ico 1 N, a n)^2 - (N:ℝ)⁻¹ * ((N:ℝ) * (∑ n ∈ Finset.Ico 1 N, (a n)^2) - (∑ n ∈ Finset.Ico 1 N, a n)^2) := by
          rw [hAnorm, hsumR, hdouble]
      _ = 2 / (N:ℝ) * (∑ n ∈ Finset.Ico 1 N, a n)^2 - ∑ n ∈ Finset.Ico 1 N, (a n)^2 := by
          have hNne : (N:ℝ) ≠ 0 := by positivity
          field_simp
          ring
