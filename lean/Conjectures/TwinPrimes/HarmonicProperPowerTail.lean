import Mathlib

open Finset
open scoped BigOperators

noncomputable section

/-!
New route · Levent GRH methods and extensions · Bound the harmonic tail from nonprime endpoints
(`L-twin-primes-harmonic-proper-power-tail`).

The weighted twin term `Λ(n)Λ(n+2)/(n+2)` vanishes unless `n` and `n+2` are prime powers, so on a
nonprime endpoint one of the two factors sits on a proper prime power.  The weighted Chebyshev
estimate `ψ - θ ≪ √x` (Mathlib's `Chebyshev.psi_sub_theta_le_mul_sqrt`) bounds the total `Λ`-mass
of the nonprimes below `4M`, hence a dyadic block `[M, 4M)` contributes `≪ log(2+M)/√M`, and the
blocks `[4^j L, 4^{j+1} L)` sum geometrically.
-/

/-- The weighted twin term `Λ(n)Λ(n+2)/(n+2)`. -/
private def twinTerm (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n + 2) / ((n + 2 : ℕ) : ℝ)

/-- `Λ` restricted to the nonprimes. -/
private def npLam (m : ℕ) : ℝ :=
  if ¬ m.Prime then ArithmeticFunction.vonMangoldt m else 0

private lemma npLam_nonneg (m : ℕ) : 0 ≤ npLam m := by
  unfold npLam
  split_ifs
  · exact le_rfl
  · exact ArithmeticFunction.vonMangoldt_nonneg

private lemma sum_npLam_Ioc (B : ℕ) :
    (∑ m ∈ Finset.Ioc 0 B, npLam m) =
      Chebyshev.psi (B : ℝ) - Chebyshev.theta (B : ℝ) := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [npLam]

/-- On a block `[M, 4M)` the total weighted mass of the bad endpoints is `≪ log(2+M)/√M`. -/
private lemma block_bound (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ x : ℝ, Chebyshev.psi x - Chebyshev.theta x ≤ C * Real.sqrt x)
    (M : ℕ) (hM : 1 ≤ M) (T : Finset ℕ)
    (hT : ∀ n ∈ T, M ≤ n ∧ n < 4 * M ∧ (¬ n.Prime ∨ ¬ (n + 2).Prime)) :
    (∑ n ∈ T, twinTerm n) ≤
      10 * C * Real.log (2 + (M : ℝ)) * Real.sqrt (M : ℝ) / (M : ℝ) := by
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hM2pos : (0 : ℝ) < (M : ℝ) + 2 := by linarith
  set c : ℝ := Real.log (4 * (M : ℝ) + 2) / ((M : ℝ) + 2)
  have hc0 : 0 ≤ c := by
    apply div_nonneg
    · exact Real.log_nonneg (by linarith)
    · linarith
  have hterm : ∀ n ∈ T, twinTerm n ≤ c * (npLam n + npLam (n + 2)) := by
    intro n hn
    obtain ⟨hlo, hhi, hbad⟩ := hT n hn
    have hnlo : (M : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : M + 2 ≤ n + 2)
    have hnhi : ((n + 2 : ℕ) : ℝ) ≤ 4 * (M : ℝ) + 2 := by
      exact_mod_cast (by omega : n + 2 ≤ 4 * M + 2)
    have hnpos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
    have hloghi : Real.log ((n + 2 : ℕ) : ℝ) ≤ Real.log (4 * (M : ℝ) + 2) :=
      Real.log_le_log hnpos hnhi
    have hratio : Real.log ((n + 2 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) ≤ c := by
      unfold c
      exact div_le_div₀ (Real.log_nonneg (by linarith)) hloghi hM2pos hnlo
    by_cases hnp : n.Prime
    · have hn2p : ¬ (n + 2).Prime := by
        rcases hbad with h | h
        · exact absurd hnp h
        · exact h
      have hg : npLam n = 0 := by simp [npLam, hnp]
      have hg2 : npLam (n + 2) = ArithmeticFunction.vonMangoldt (n + 2) := by simp [npLam, hn2p]
      have hnl : Real.log (n : ℝ) ≤ Real.log (4 * (M : ℝ) + 2) := by
        apply Real.log_le_log
        · exact_mod_cast (by omega : 0 < n)
        · exact_mod_cast (by omega : n ≤ 4 * M + 2)
      calc twinTerm n
          = ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n + 2) /
              ((n + 2 : ℕ) : ℝ) := rfl
        _ ≤ Real.log (n : ℝ) * ArithmeticFunction.vonMangoldt (n + 2) / ((n + 2 : ℕ) : ℝ) := by
            apply div_le_div_of_nonneg_right _ (le_of_lt hnpos)
            exact mul_le_mul_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log
              ArithmeticFunction.vonMangoldt_nonneg
        _ ≤ Real.log (4 * (M : ℝ) + 2) * ArithmeticFunction.vonMangoldt (n + 2) /
              ((M : ℝ) + 2) := by
            apply div_le_div₀ _ _ hM2pos hnlo
            · exact mul_nonneg (Real.log_nonneg (by linarith))
                ArithmeticFunction.vonMangoldt_nonneg
            · exact mul_le_mul_of_nonneg_right hnl ArithmeticFunction.vonMangoldt_nonneg
        _ = c * (npLam n + npLam (n + 2)) := by
            rw [hg, hg2]
            unfold c
            ring
    · have hg : npLam n = ArithmeticFunction.vonMangoldt n := by simp [npLam, hnp]
      have hg2 : 0 ≤ npLam (n + 2) := npLam_nonneg _
      calc twinTerm n
          = ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n + 2) /
              ((n + 2 : ℕ) : ℝ) := rfl
        _ ≤ ArithmeticFunction.vonMangoldt n * Real.log ((n + 2 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) := by
            apply div_le_div_of_nonneg_right _ (le_of_lt hnpos)
            exact mul_le_mul_of_nonneg_left ArithmeticFunction.vonMangoldt_le_log
              ArithmeticFunction.vonMangoldt_nonneg
        _ = ArithmeticFunction.vonMangoldt n *
              (Real.log ((n + 2 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) := by ring
        _ ≤ ArithmeticFunction.vonMangoldt n * c :=
            mul_le_mul_of_nonneg_left hratio ArithmeticFunction.vonMangoldt_nonneg
        _ ≤ c * (npLam n + npLam (n + 2)) := by
            rw [hg]
            have : 0 ≤ c * npLam (n + 2) := mul_nonneg hc0 hg2
            linarith
  have hsum : (∑ n ∈ T, twinTerm n) ≤
      c * ((∑ n ∈ T, npLam n) + (∑ n ∈ T, npLam (n + 2))) := by
    calc (∑ n ∈ T, twinTerm n) ≤ ∑ n ∈ T, c * (npLam n + npLam (n + 2)) :=
          Finset.sum_le_sum hterm
      _ = c * ((∑ n ∈ T, npLam n) + (∑ n ∈ T, npLam (n + 2))) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have hTsub : T ⊆ Finset.Ioc 0 (4 * M) := by
    intro n hn
    obtain ⟨hlo, hhi, -⟩ := hT n hn
    exact Finset.mem_Ioc.mpr ⟨by omega, le_of_lt hhi⟩
  have hA : (∑ n ∈ T, npLam n) ≤ C * Real.sqrt (4 * (M : ℝ)) := by
    calc (∑ n ∈ T, npLam n) ≤ ∑ n ∈ Finset.Ioc 0 (4 * M), npLam n :=
          Finset.sum_le_sum_of_subset_of_nonneg hTsub (fun i _ _ => npLam_nonneg i)
      _ = Chebyshev.psi ((4 * M : ℕ) : ℝ) - Chebyshev.theta ((4 * M : ℕ) : ℝ) :=
          sum_npLam_Ioc (4 * M)
      _ = Chebyshev.psi (4 * (M : ℝ)) - Chebyshev.theta (4 * (M : ℝ)) := by
          simp only [Nat.cast_mul, Nat.cast_ofNat]
      _ ≤ C * Real.sqrt (4 * (M : ℝ)) := hC _
  have hB : (∑ n ∈ T, npLam (n + 2)) ≤ C * Real.sqrt (4 * (M : ℝ) + 2) := by
    calc (∑ n ∈ T, npLam (n + 2)) ≤ ∑ n ∈ Finset.Ioc 0 (4 * M), npLam (n + 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hTsub (fun i _ _ => npLam_nonneg (i + 2))
      _ = ∑ m ∈ (Finset.Ioc 0 (4 * M)).image (fun n => n + 2), npLam m := by
          rw [Finset.sum_image]
          intro a _ b _ hab
          dsimp only at hab
          omega
      _ ≤ ∑ m ∈ Finset.Ioc 0 (4 * M + 2), npLam m := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => npLam_nonneg i)
          intro m hm
          obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
          obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hn
          exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
      _ = Chebyshev.psi ((4 * M + 2 : ℕ) : ℝ) - Chebyshev.theta ((4 * M + 2 : ℕ) : ℝ) :=
          sum_npLam_Ioc (4 * M + 2)
      _ = Chebyshev.psi (4 * (M : ℝ) + 2) - Chebyshev.theta (4 * (M : ℝ) + 2) := by
          simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      _ ≤ C * Real.sqrt (4 * (M : ℝ) + 2) := hC _
  have hsq1 : Real.sqrt (4 * (M : ℝ)) = 2 * Real.sqrt (M : ℝ) := by
    rw [show (4 : ℝ) * (M : ℝ) = (2 : ℝ) ^ 2 * (M : ℝ) by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have hsq2 : Real.sqrt (4 * (M : ℝ) + 2) ≤ 3 * Real.sqrt (M : ℝ) := by
    have h1 : 4 * (M : ℝ) + 2 ≤ 9 * (M : ℝ) := by linarith
    calc Real.sqrt (4 * (M : ℝ) + 2) ≤ Real.sqrt (9 * (M : ℝ)) := Real.sqrt_le_sqrt h1
      _ = 3 * Real.sqrt (M : ℝ) := by
          rw [show (9 : ℝ) * (M : ℝ) = (3 : ℝ) ^ 2 * (M : ℝ) by ring, Real.sqrt_mul (by norm_num),
            Real.sqrt_sq (by norm_num)]
  have hclog : Real.log (4 * (M : ℝ) + 2) ≤ 2 * Real.log (2 + (M : ℝ)) := by
    have h1 : 4 * (M : ℝ) + 2 ≤ (2 + (M : ℝ)) ^ 2 := by nlinarith
    calc Real.log (4 * (M : ℝ) + 2) ≤ Real.log ((2 + (M : ℝ)) ^ 2) :=
          Real.log_le_log (by linarith) h1
      _ = 2 * Real.log (2 + (M : ℝ)) := by rw [Real.log_pow]; ring
  have hc_le : c ≤ 2 * Real.log (2 + (M : ℝ)) / (M : ℝ) := by
    unfold c
    calc Real.log (4 * (M : ℝ) + 2) / ((M : ℝ) + 2)
        ≤ 2 * Real.log (2 + (M : ℝ)) / ((M : ℝ) + 2) :=
          div_le_div_of_nonneg_right hclog (by linarith)
      _ ≤ 2 * Real.log (2 + (M : ℝ)) / (M : ℝ) := by
          apply div_le_div_of_nonneg_left
          · exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
          · exact hMpos
          · linarith
  calc (∑ n ∈ T, twinTerm n)
      ≤ c * ((∑ n ∈ T, npLam n) + (∑ n ∈ T, npLam (n + 2))) := hsum
    _ ≤ c * (C * Real.sqrt (4 * (M : ℝ)) + C * Real.sqrt (4 * (M : ℝ) + 2)) := by
        apply mul_le_mul_of_nonneg_left _ hc0
        linarith
    _ ≤ c * (C * (2 * Real.sqrt (M : ℝ) + 3 * Real.sqrt (M : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hc0
        calc C * Real.sqrt (4 * (M : ℝ)) + C * Real.sqrt (4 * (M : ℝ) + 2)
            = C * (2 * Real.sqrt (M : ℝ)) + C * Real.sqrt (4 * (M : ℝ) + 2) := by rw [hsq1]
          _ ≤ C * (2 * Real.sqrt (M : ℝ)) + C * (3 * Real.sqrt (M : ℝ)) := by
              have := mul_le_mul_of_nonneg_left hsq2 hC0
              linarith
          _ = C * (2 * Real.sqrt (M : ℝ) + 3 * Real.sqrt (M : ℝ)) := by ring
    _ ≤ (2 * Real.log (2 + (M : ℝ)) / (M : ℝ)) *
          (C * (2 * Real.sqrt (M : ℝ) + 3 * Real.sqrt (M : ℝ))) := by
        apply mul_le_mul_of_nonneg_right hc_le
        exact mul_nonneg hC0 (by positivity)
    _ = 10 * C * Real.log (2 + (M : ℝ)) * Real.sqrt (M : ℝ) / (M : ℝ) := by ring

private lemma sum_half_pow (I : ℕ) :
    (∑ i ∈ Finset.range I, ((1 : ℝ) / 2) ^ i) ≤ 2 := by
  have h : ∀ n : ℕ, (∑ i ∈ Finset.range n, ((1 : ℝ) / 2) ^ i) = 2 - 2 / (2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have h2 : ((1 : ℝ) / 2) ^ n = 1 / (2 : ℝ) ^ n := by rw [div_pow, one_pow]
      have hp : (2 : ℝ) ^ (n + 1) = 2 ^ n * 2 := by ring
      have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
      rw [h2, hp]
      field_simp
      ring
  rw [h I]
  have : (0 : ℝ) ≤ 2 / (2 : ℝ) ^ I := by positivity
  linarith

private lemma sum_mul_half_pow (I : ℕ) :
    (∑ i ∈ Finset.range I, (i : ℝ) * ((1 : ℝ) / 2) ^ i) ≤ 2 := by
  have h : ∀ n : ℕ, (∑ i ∈ Finset.range n, (i : ℝ) * ((1 : ℝ) / 2) ^ i) =
      2 - (2 * (n : ℝ) + 2) / (2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have h2 : ((1 : ℝ) / 2) ^ n = 1 / (2 : ℝ) ^ n := by rw [div_pow, one_pow]
      have hp : (2 : ℝ) ^ (n + 1) = 2 ^ n * 2 := by ring
      have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
      rw [h2, hp]
      push_cast
      field_simp
      ring
  rw [h I]
  have : (0 : ℝ) ≤ (2 * (I : ℝ) + 2) / (2 : ℝ) ^ I := by positivity
  linarith

/-- New route · Levent GRH methods and extensions · Bound the harmonic tail from nonprime
endpoints. -/
theorem Conjectures.TwinPrimes.HarmonicProperPowerTail :
    ∃ C : ℝ, 0<C ∧ ∀ U V : ℕ, 2≤U → (∑ n ∈ (Finset.range V).filter (fun n => U<n+2 ∧ (¬n.Prime ∨ ¬(n+2).Prime)), ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2)/(n+2 : ℝ)) ≤ C*Real.log (2+U)/Real.sqrt U := by
  obtain ⟨C₀, hC₀⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  set C : ℝ := max C₀ 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hC0 : 0 ≤ C := le_of_lt hCpos
  have hC : ∀ x : ℝ, Chebyshev.psi x - Chebyshev.theta x ≤ C * Real.sqrt x := fun x =>
    le_trans (hC₀ x) (mul_le_mul_of_nonneg_right (le_max_left C₀ 1) (Real.sqrt_nonneg x))
  refine ⟨200 * C, mul_pos (by norm_num) hCpos, ?_⟩
  intro U V hU
  set S : Finset ℕ :=
    (Finset.range V).filter (fun n => U < n + 2 ∧ (¬ n.Prime ∨ ¬ (n + 2).Prime))
  have hS : ∀ n ∈ S, U - 1 ≤ n ∧ n < V ∧ (¬ n.Prime ∨ ¬ (n + 2).Prime) := by
    intro n hn
    obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.mp hn
    exact ⟨by omega, Finset.mem_range.mp h1, h3⟩
  set L : ℕ := U - 1
  have hL : 1 ≤ L := by omega
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  set e₀ : ℕ := Nat.log 4 L
  set K : ℕ := Nat.log 4 V
  have hmaps : ∀ n ∈ S, Nat.log 4 n ∈ Finset.Ico e₀ (K + 1) := by
    intro n hn
    obtain ⟨hlo, hhi, -⟩ := hS n hn
    refine Finset.mem_Ico.mpr ⟨Nat.log_mono_right hlo, ?_⟩
    have h1 : Nat.log 4 n ≤ Nat.log 4 V := Nat.log_mono_right (by omega)
    omega
  have hfib : (∑ n ∈ S, twinTerm n) =
      ∑ e ∈ Finset.Ico e₀ (K + 1), ∑ n ∈ S with Nat.log 4 n = e, twinTerm n :=
    (Finset.sum_fiberwise_of_maps_to hmaps twinTerm).symm
  have hblk : ∀ e ∈ Finset.Ico e₀ (K + 1),
      (∑ n ∈ S with Nat.log 4 n = e, twinTerm n) ≤
        10 * C * Real.log (2 + ((4 ^ e : ℕ) : ℝ)) * Real.sqrt ((4 ^ e : ℕ) : ℝ) /
          ((4 ^ e : ℕ) : ℝ) := by
    intro e _
    refine block_bound C hC0 hC (4 ^ e) (Nat.one_le_pow e 4 (by norm_num))
      (S.filter (fun n => Nat.log 4 n = e)) ?_
    intro n hn
    obtain ⟨hnS, hne⟩ := Finset.mem_filter.mp hn
    obtain ⟨hlo, hhi, hbad⟩ := hS n hnS
    have h1 : 4 ^ e ≤ n := by
      rw [← hne]
      exact Nat.pow_log_le_self 4 (by omega)
    have h2 : n < 4 ^ (e + 1) := by
      rw [← hne]
      exact Nat.lt_pow_succ_log_self (by norm_num) n
    have h3 : 4 ^ (e + 1) = 4 * 4 ^ e := by ring
    exact ⟨h1, by omega, hbad⟩
  have hsum1 : (∑ n ∈ S, twinTerm n) ≤
      ∑ e ∈ Finset.Ico e₀ (K + 1), 10 * C * Real.log (2 + ((4 ^ e : ℕ) : ℝ)) *
        Real.sqrt ((4 ^ e : ℕ) : ℝ) / ((4 ^ e : ℕ) : ℝ) := by
    rw [hfib]
    exact Finset.sum_le_sum hblk
  have hterm_eq : ∀ e : ℕ, 10 * C * Real.log (2 + ((4 ^ e : ℕ) : ℝ)) *
        Real.sqrt ((4 ^ e : ℕ) : ℝ) / ((4 ^ e : ℕ) : ℝ) =
      10 * C * (Real.log (2 + (4 : ℝ) ^ e) / (2 : ℝ) ^ e) := by
    intro e
    have h1 : ((4 ^ e : ℕ) : ℝ) = (4 : ℝ) ^ e := by push_cast; ring
    have h4 : (4 : ℝ) ^ e = ((2 : ℝ) ^ e) ^ 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul, ← pow_mul]
      ring
    rw [h1, h4, Real.sqrt_sq (by positivity)]
    have h2e : ((2 : ℝ) ^ e) ≠ 0 := by positivity
    field_simp
  have hsum2 : (∑ n ∈ S, twinTerm n) ≤
      10 * C * ∑ e ∈ Finset.Ico e₀ (K + 1), Real.log (2 + (4 : ℝ) ^ e) / (2 : ℝ) ^ e := by
    calc (∑ n ∈ S, twinTerm n)
        ≤ ∑ e ∈ Finset.Ico e₀ (K + 1), 10 * C * Real.log (2 + ((4 ^ e : ℕ) : ℝ)) *
            Real.sqrt ((4 ^ e : ℕ) : ℝ) / ((4 ^ e : ℕ) : ℝ) := hsum1
      _ = ∑ e ∈ Finset.Ico e₀ (K + 1),
            10 * C * (Real.log (2 + (4 : ℝ) ^ e) / (2 : ℝ) ^ e) :=
          Finset.sum_congr rfl fun e _ => hterm_eq e
      _ = 10 * C * ∑ e ∈ Finset.Ico e₀ (K + 1), Real.log (2 + (4 : ℝ) ^ e) / (2 : ℝ) ^ e := by
          rw [Finset.mul_sum]
  have hA_le : (4 : ℝ) ^ e₀ ≤ (L : ℝ) := by
    have : (4 : ℝ) ^ e₀ = ((4 ^ e₀ : ℕ) : ℝ) := by push_cast; ring
    rw [this]
    exact_mod_cast Nat.pow_log_le_self 4 (by omega)
  have hB_sq : (L : ℝ) < 4 * ((2 : ℝ) ^ e₀) ^ 2 := by
    have h1 : L < 4 ^ (Nat.log 4 L + 1) := Nat.lt_pow_succ_log_self (by norm_num) L
    have h2 : ((4 ^ (Nat.log 4 L + 1) : ℕ) : ℝ) = 4 * ((2 : ℝ) ^ e₀) ^ 2 := by
      have h3 : (4 ^ (Nat.log 4 L + 1) : ℕ) = 4 * 4 ^ e₀ := by ring
      rw [h3]
      push_cast
      have h4 : (4 : ℝ) ^ e₀ = ((2 : ℝ) ^ e₀) ^ 2 := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul, ← pow_mul]
        ring
      rw [h4]
    have h3 : (L : ℝ) < ((4 ^ (Nat.log 4 L + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  have hBpos : (0 : ℝ) < (2 : ℝ) ^ e₀ := by positivity
  have hBge : Real.sqrt (L : ℝ) / 2 ≤ (2 : ℝ) ^ e₀ := by
    have h4 : (Real.sqrt (L : ℝ) / 2) ^ 2 ≤ ((2 : ℝ) ^ e₀) ^ 2 := by
      rw [div_pow, Real.sq_sqrt (le_of_lt hLpos)]
      linarith
    nlinarith [hBpos, Real.sqrt_nonneg (L : ℝ)]
  have hlogL : 0 ≤ Real.log (2 + (L : ℝ)) := Real.log_nonneg (by linarith)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlogL2 : 0 ≤ Real.log (2 + (L : ℝ)) * 2 + Real.log 4 * 2 := by
    have := hlogL; have := hlog4; linarith
  have hinner : (∑ e ∈ Finset.Ico e₀ (K + 1), Real.log (2 + (4 : ℝ) ^ e) / (2 : ℝ) ^ e) ≤
      12 * Real.log (2 + (L : ℝ)) / Real.sqrt (L : ℝ) := by
    rw [Finset.sum_Ico_eq_sum_range]
    set A : ℝ := (4 : ℝ) ^ e₀
    set B : ℝ := (2 : ℝ) ^ e₀
    have hAeq : ∀ i : ℕ, (4 : ℝ) ^ (e₀ + i) = A * (4 : ℝ) ^ i := fun i => by
      rw [pow_add]
    have hBeq : ∀ i : ℕ, (2 : ℝ) ^ (e₀ + i) = B * (2 : ℝ) ^ i := fun i => by
      rw [pow_add]
    have hterm : ∀ i : ℕ, Real.log (2 + (4 : ℝ) ^ (e₀ + i)) / (2 : ℝ) ^ (e₀ + i) ≤
        (Real.log (2 + (L : ℝ)) + (i : ℝ) * Real.log 4) / (B * (2 : ℝ) ^ i) := by
      intro i
      rw [hAeq i, hBeq i]
      have h4i : (1 : ℝ) ≤ (4 : ℝ) ^ i := by
        exact_mod_cast Nat.one_le_pow i 4 (by norm_num)
      have hle : 2 + A * (4 : ℝ) ^ i ≤ (2 + A) * (4 : ℝ) ^ i := by nlinarith
      have hlog : Real.log (2 + A * (4 : ℝ) ^ i) ≤
          Real.log (2 + (L : ℝ)) + (i : ℝ) * Real.log 4 := by
        calc Real.log (2 + A * (4 : ℝ) ^ i) ≤ Real.log ((2 + A) * (4 : ℝ) ^ i) :=
              Real.log_le_log (by positivity) hle
          _ = Real.log (2 + A) + Real.log ((4 : ℝ) ^ i) :=
              Real.log_mul (by positivity) (by positivity)
          _ = Real.log (2 + A) + (i : ℝ) * Real.log 4 := by rw [Real.log_pow]
          _ ≤ Real.log (2 + (L : ℝ)) + (i : ℝ) * Real.log 4 := by
              have : Real.log (2 + A) ≤ Real.log (2 + (L : ℝ)) :=
                Real.log_le_log (by positivity) (by linarith [hA_le])
              linarith
      exact div_le_div_of_nonneg_right hlog (by positivity)
    have hsplit : ∀ i : ℕ, (Real.log (2 + (L : ℝ)) + (i : ℝ) * Real.log 4) / (B * (2 : ℝ) ^ i) =
        (1 / B) * (Real.log (2 + (L : ℝ)) * ((1 : ℝ) / 2) ^ i +
          Real.log 4 * ((i : ℝ) * ((1 : ℝ) / 2) ^ i)) := by
      intro i
      have h2i : ((2 : ℝ) ^ i) ≠ 0 := by positivity
      have hb : ((1 : ℝ) / 2) ^ i = 1 / (2 : ℝ) ^ i := by rw [div_pow, one_pow]
      rw [hb]
      field_simp
    calc (∑ i ∈ Finset.range (K + 1 - e₀), Real.log (2 + (4 : ℝ) ^ (e₀ + i)) / (2 : ℝ) ^ (e₀ + i))
        ≤ ∑ i ∈ Finset.range (K + 1 - e₀),
            (Real.log (2 + (L : ℝ)) + (i : ℝ) * Real.log 4) / (B * (2 : ℝ) ^ i) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = ∑ i ∈ Finset.range (K + 1 - e₀), (1 / B) *
            (Real.log (2 + (L : ℝ)) * ((1 : ℝ) / 2) ^ i +
              Real.log 4 * ((i : ℝ) * ((1 : ℝ) / 2) ^ i)) :=
          Finset.sum_congr rfl fun i _ => hsplit i
      _ = (1 / B) * ((∑ i ∈ Finset.range (K + 1 - e₀),
            Real.log (2 + (L : ℝ)) * ((1 : ℝ) / 2) ^ i) +
          (∑ i ∈ Finset.range (K + 1 - e₀),
            Real.log 4 * ((i : ℝ) * ((1 : ℝ) / 2) ^ i))) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ = (1 / B) * (Real.log (2 + (L : ℝ)) *
            (∑ i ∈ Finset.range (K + 1 - e₀), ((1 : ℝ) / 2) ^ i) +
          Real.log 4 * (∑ i ∈ Finset.range (K + 1 - e₀), (i : ℝ) * ((1 : ℝ) / 2) ^ i)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
      _ ≤ (1 / B) * (Real.log (2 + (L : ℝ)) * 2 + Real.log 4 * 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h1 := sum_half_pow (K + 1 - e₀)
          have h2 := sum_mul_half_pow (K + 1 - e₀)
          have ha : Real.log (2 + (L : ℝ)) *
              (∑ i ∈ Finset.range (K + 1 - e₀), ((1 : ℝ) / 2) ^ i) ≤
              Real.log (2 + (L : ℝ)) * 2 :=
            mul_le_mul_of_nonneg_left h1 (Real.log_nonneg (by linarith))
          have hb : Real.log 4 * (∑ i ∈ Finset.range (K + 1 - e₀), (i : ℝ) * ((1 : ℝ) / 2) ^ i) ≤
              Real.log 4 * 2 :=
            mul_le_mul_of_nonneg_left h2 (Real.log_nonneg (by norm_num))
          linarith
      _ ≤ (2 / Real.sqrt (L : ℝ)) * (Real.log (2 + (L : ℝ)) * 2 + Real.log 4 * 2) := by
          apply mul_le_mul_of_nonneg_right _ hlogL2
          have hinv : 1 / B ≤ 2 / Real.sqrt (L : ℝ) := by
            rw [div_le_div_iff₀ hBpos (by positivity)]
            linarith [hBge]
          exact hinv
      _ ≤ (2 / Real.sqrt (L : ℝ)) * (6 * Real.log (2 + (L : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hlog4 : Real.log 4 ≤ 2 * Real.log (2 + (L : ℝ)) := by
            have h5 : Real.log 4 = 2 * Real.log 2 := by
              rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]; ring
            have h6 : Real.log 2 ≤ Real.log (2 + (L : ℝ)) :=
              Real.log_le_log (by norm_num) (by linarith)
            linarith
          linarith
      _ = 12 * Real.log (2 + (L : ℝ)) / Real.sqrt (L : ℝ) := by ring
  have hLcast : (L : ℝ) = (U : ℝ) - 1 := by
    have : L = U - 1 := rfl
    rw [this, Nat.cast_sub (by omega)]
    ring
  have hU2 : (2 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU
  have hlogU : 0 ≤ Real.log (2 + (U : ℝ)) := Real.log_nonneg (by linarith)
  have hfinal : (∑ n ∈ S, twinTerm n) ≤
      200 * C * Real.log (2 + (U : ℝ)) / Real.sqrt (U : ℝ) := by
    calc (∑ n ∈ S, twinTerm n)
        ≤ 10 * C * ∑ e ∈ Finset.Ico e₀ (K + 1), Real.log (2 + (4 : ℝ) ^ e) / (2 : ℝ) ^ e := hsum2
      _ ≤ 10 * C * (12 * Real.log (2 + (L : ℝ)) / Real.sqrt (L : ℝ)) := by
          apply mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = 120 * C * Real.log (2 + (L : ℝ)) / Real.sqrt (L : ℝ) := by ring
      _ ≤ 120 * C * Real.log (2 + (U : ℝ)) / Real.sqrt (L : ℝ) := by
          apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Real.log_le_log (by positivity)
          linarith
      _ ≤ 120 * C * Real.log (2 + (U : ℝ)) * Real.sqrt 2 / Real.sqrt (U : ℝ) := by
          have hnn : 0 ≤ 120 * C * Real.log (2 + (U : ℝ)) :=
            mul_nonneg (mul_nonneg (by norm_num) hC0) hlogU
          have hinv : 1 / Real.sqrt (L : ℝ) ≤ Real.sqrt 2 / Real.sqrt (U : ℝ) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            have hUle : (U : ℝ) ≤ 2 * (L : ℝ) := by linarith
            have hsq : Real.sqrt (U : ℝ) ≤ Real.sqrt (2 * (L : ℝ)) := Real.sqrt_le_sqrt hUle
            rw [Real.sqrt_mul (by norm_num)] at hsq
            linarith
          calc 120 * C * Real.log (2 + (U : ℝ)) / Real.sqrt (L : ℝ)
              = 120 * C * Real.log (2 + (U : ℝ)) * (1 / Real.sqrt (L : ℝ)) := by ring
            _ ≤ 120 * C * Real.log (2 + (U : ℝ)) * (Real.sqrt 2 / Real.sqrt (U : ℝ)) :=
                mul_le_mul_of_nonneg_left hinv hnn
            _ = 120 * C * Real.log (2 + (U : ℝ)) * Real.sqrt 2 / Real.sqrt (U : ℝ) := by ring
      _ ≤ 200 * C * Real.log (2 + (U : ℝ)) / Real.sqrt (U : ℝ) := by
          have hsq2 : Real.sqrt 2 ≤ 5 / 3 := by
            rw [Real.sqrt_le_iff]
            constructor
            · norm_num
            · nlinarith
          have hnn : 0 ≤ 120 * C * Real.log (2 + (U : ℝ)) / Real.sqrt (U : ℝ) :=
            div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0) hlogU) (Real.sqrt_nonneg _)
          calc 120 * C * Real.log (2 + (U : ℝ)) * Real.sqrt 2 / Real.sqrt (U : ℝ)
              = (120 * C * Real.log (2 + (U : ℝ)) / Real.sqrt (U : ℝ)) * Real.sqrt 2 := by ring
            _ ≤ (120 * C * Real.log (2 + (U : ℝ)) / Real.sqrt (U : ℝ)) * (5 / 3) :=
                mul_le_mul_of_nonneg_left hsq2 hnn
            _ = 200 * C * Real.log (2 + (U : ℝ)) / Real.sqrt (U : ℝ) := by ring
  have hconv : (∑ n ∈ S, ArithmeticFunction.vonMangoldt n *
      ArithmeticFunction.vonMangoldt (n + 2) / ((n : ℝ) + 2)) = ∑ n ∈ S, twinTerm n := by
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold twinTerm
    rw [Nat.cast_add]
    ring
  calc (∑ n ∈ S, ArithmeticFunction.vonMangoldt n *
        ArithmeticFunction.vonMangoldt (n + 2) / ((n : ℝ) + 2))
      = ∑ n ∈ S, twinTerm n := hconv
    _ ≤ 200 * C * Real.log (2 + (U : ℝ)) / Real.sqrt (U : ℝ) := hfinal
