import Mathlib

namespace Conjectures.Goldbach.VaughanHighExactSplit_aux

open ArithmeticFunction MeasureTheory
open scoped BigOperators ArithmeticFunction zeta Moebius

noncomputable section

def E (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def S (n : ℕ) (w : ℕ → ℝ) (t : ℝ) : ℂ :=
  Finset.sum (Finset.range (n + 1)) (fun k => (w k : ℂ) * E ((k : ℝ) * t))

def Q (n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ 2

def arcs (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))}

def I (n : ℕ) (a b : ℕ → ℝ) : ℂ :=
  intervalIntegral
    (fun t => (arcs n)ᶜ.indicator
      (fun u => S n a u * S n b u * E (-(n : ℝ) * u)) t)
    (0 : ℝ) 1 MeasureTheory.volume

private theorem arcs_measurable (n : ℕ) : MeasurableSet (arcs n) := by
  classical
  let piece (q a : ℕ) := {t : ℝ |
    1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))}
  have cover : arcs n = ⋃ q : ℕ, ⋃ a : ℕ, piece q a := by
    ext t
    simp only [Set.mem_iUnion]
    rfl
  rw [cover]
  apply MeasurableSet.iUnion
  intro q
  apply MeasurableSet.iUnion
  intro a
  by_cases h : 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q
  · obtain ⟨hq, hQ, ha, hc⟩ := h
    have sublevel : piece q a = {t : ℝ |
        |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))} := by
      ext t
      exact ⟨fun ht => ht.2.2.2.2, fun ht => ⟨hq, hQ, ha, hc, ht⟩⟩
    rw [sublevel]
    have hcDist : Continuous (fun t : ℝ => |t - (a : ℝ) / (q : ℝ)|) :=
      (continuous_id.sub
        (continuous_const : Continuous (fun _ : ℝ => (a : ℝ) / (q : ℝ)))).abs
    exact (isClosed_le hcDist
      (continuous_const : Continuous (fun _ : ℝ =>
        (Q n : ℝ) / ((q : ℝ) * (n : ℝ))))).measurableSet
  · have empty : piece q a = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro t ⟨hq, hQ, ha, hc, _⟩
      exact h ⟨hq, hQ, ha, hc⟩
    rw [empty]
    exact MeasurableSet.empty

private theorem E_continuous : Continuous E := by
  unfold E
  fun_prop

private theorem S_continuous (n : ℕ) (w : ℕ → ℝ) : Continuous (S n w) := by
  classical
  unfold S E
  fun_prop

private theorem S_add (n : ℕ) (a b : ℕ → ℝ) :
    S n (a + b) = S n a + S n b := by
  classical
  funext t
  simp [S, Finset.sum_add_distrib, add_mul]

private theorem integrand_continuous (n : ℕ) (a b : ℕ → ℝ) :
    Continuous (fun u : ℝ => S n a u * S n b u * E (-(n : ℝ) * u)) := by
  apply Continuous.mul
  · exact (S_continuous n a).mul (S_continuous n b)
  · apply E_continuous.comp
    fun_prop

private theorem integrand_intervalIntegrable (n : ℕ) (a b : ℕ → ℝ) :
    IntervalIntegrable
      (fun t => (arcs n)ᶜ.indicator
        (fun u => S n a u * S n b u * E (-(n : ℝ) * u)) t)
      MeasureTheory.volume (0 : ℝ) 1 := by
  have hi : IntervalIntegrable
      (fun u : ℝ => S n a u * S n b u * E (-(n : ℝ) * u))
      volume (0 : ℝ) 1 := (integrand_continuous n a b).intervalIntegrable 0 1
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hi ⊢
  exact hi.indicator (arcs_measurable n).compl

private theorem integrand_pointwise_expansion (n : ℕ) (a b c : ℕ → ℝ)
    (h : ∀ k, a k = b k + c k) (u : ℝ) :
    S n a u * S n a u * E (-(n : ℝ) * u) =
      S n b u * S n b u * E (-(n : ℝ) * u) +
        2 * (S n b u * S n c u * E (-(n : ℝ) * u)) +
        S n c u * S n c u * E (-(n : ℝ) * u) := by
  have hs : S n a u = S n b u + S n c u := by
    rw [show a = b + c by
      funext k
      exact h k]
    exact congrFun (S_add n b c) u
  rw [hs]
  ring

theorem generic_bilinear_expansion (n : ℕ) (a b c : ℕ → ℝ)
    (h : ∀ k, a k = b k + c k) :
    I n a a = I n b b + 2 * I n b c + I n c c := by
  have hfun : ∀ u : ℝ,
      (arcs n)ᶜ.indicator
          (fun x => S n a x * S n a x * E (-(n : ℝ) * x)) u =
        (arcs n)ᶜ.indicator
            (fun x => S n b x * S n b x * E (-(n : ℝ) * x)) u +
          2 * (arcs n)ᶜ.indicator
            (fun x => S n b x * S n c x * E (-(n : ℝ) * x)) u +
          (arcs n)ᶜ.indicator
            (fun x => S n c x * S n c x * E (-(n : ℝ) * x)) u := by
    intro u
    by_cases hu : u ∈ (arcs n)ᶜ
    · simp only [Set.indicator_of_mem hu]
      rw [integrand_pointwise_expansion n a b c h u]
    · simp [Set.indicator_of_notMem hu]
  have hbb := integrand_intervalIntegrable n b b
  have hbc := integrand_intervalIntegrable n b c
  have hcc := integrand_intervalIntegrable n c c
  rw [I, I, I, I]
  rw [intervalIntegral.integral_congr (fun u _ => hfun u)]
  rw [intervalIntegral.integral_add (hbb.add (hbc.const_mul 2)) (hcc)]
  rw [intervalIntegral.integral_add hbb (hbc.const_mul 2)]
  rw [intervalIntegral.integral_const_mul]

def low (U : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun m => if m ≤ U then f m else 0, by simp⟩

def high (U : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun m => if U < m then f m else 0, by simp⟩

private theorem low_add_high (U : ℕ) (f : ArithmeticFunction ℝ) :
    low U f + high U f = f := by
  ext m
  change (if m ≤ U then f m else 0) + (if U < m then f m else 0) = f m
  by_cases h : m ≤ U
  · simp [h, not_lt_of_ge h]
  · simp [h, lt_of_not_ge h]

private theorem vaughan_identity (U : ℕ) :
    (Λ : ArithmeticFunction ℝ) =
      low U Λ + low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log -
        low U (μ : ArithmeticFunction ℝ) * low U Λ * (ζ : ArithmeticFunction ℝ) +
        high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) * high U Λ := by
  have hμ : (low U (μ : ArithmeticFunction ℝ) + high U (μ : ArithmeticFunction ℝ)) *
      (ζ : ArithmeticFunction ℝ) = 1 := by
    rw [low_add_high, coe_moebius_mul_coe_zeta]
  have hlog : (ζ : ArithmeticFunction ℝ) * (low U Λ + high U Λ) =
      ArithmeticFunction.log := by
    rw [low_add_high, zeta_mul_vonMangoldt]
  calc
    _ = low U Λ + high U Λ := (low_add_high U Λ).symm
    _ = low U Λ + (low U (μ : ArithmeticFunction ℝ) + high U (μ : ArithmeticFunction ℝ)) *
        (ζ : ArithmeticFunction ℝ) * high U Λ := by rw [hμ, one_mul]
    _ = _ := by rw [← hlog]; ring

private theorem low_moebius_log_coeff (U m : ℕ) :
    (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) m =
      ∑ d ∈ m.divisors.filter (fun d => d ≤ U),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log ((m / d : ℕ) : ℝ) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d l =>
      low U (μ : ArithmeticFunction ℝ) d * ArithmeticFunction.log l)]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdu : d ≤ U
  · simp [low, hdu]
  · simp [low, hdu]

private theorem low_moebius_low_lambda_zeta_coeff (U m : ℕ) :
    (low U (μ : ArithmeticFunction ℝ) * low U Λ * (ζ : ArithmeticFunction ℝ)) m =
      ∑ d ∈ m.divisors.filter (fun d => d ≤ U),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          ∑ l ∈ (m / d).divisors.filter (fun l => l ≤ U), Λ l := by
  rw [mul_assoc, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d l =>
      low U (μ : ArithmeticFunction ℝ) d * (low U Λ * (ζ : ArithmeticFunction ℝ)) l)]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  rw [coe_mul_zeta_apply]
  by_cases hdu : d ≤ U
  · simp [low, hdu]
  · simp [low, hdu]

private theorem high_moebius_zeta_high_lambda_coeff (U m : ℕ) :
    (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) * high U Λ) m =
      ∑ a ∈ m.divisors.filter (fun a => U < m / a),
        (∑ d ∈ a.divisors.filter (fun d => U < d),
          ((ArithmeticFunction.moebius d : ℤ) : ℝ)) * Λ (m / a) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b =>
      (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) a * high U Λ b),
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  have hcoef : (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) a =
      ∑ d ∈ a.divisors.filter (fun d => U < d),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) := by
    simp only [coe_mul_zeta_apply, Finset.sum_filter]
    rfl
  rw [hcoef]
  by_cases hlarge : U < m / a
  · simp [high, hlarge]
  · simp [high, hlarge]

theorem exact_split (U m : ℕ) (hm : U < m) :
    Λ m =
      (∑ d ∈ m.divisors.filter (fun d => d ≤ U),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log ((m / d : ℕ) : ℝ)) -
      (∑ d ∈ m.divisors.filter (fun d => d ≤ U),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          ∑ l ∈ (m / d).divisors.filter (fun l => l ≤ U), Λ l) +
      ∑ a ∈ m.divisors.filter (fun a => U < m / a),
        (∑ d ∈ a.divisors.filter (fun d => U < d),
          ((ArithmeticFunction.moebius d : ℤ) : ℝ)) * Λ (m / a) := by
  have hidentity := congrArg (fun f : ArithmeticFunction ℝ => f m) (vaughan_identity U)
  have hlow : low U Λ m = 0 := by simp [low, not_le_of_gt hm]
  change Λ m = low U Λ m + (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) m -
      (low U (μ : ArithmeticFunction ℝ) * low U Λ * (ζ : ArithmeticFunction ℝ)) m +
      (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) * high U Λ) m at hidentity
  rw [hlow, low_moebius_log_coeff, low_moebius_low_lambda_zeta_coeff,
    high_moebius_zeta_high_lambda_coeff] at hidentity
  simpa using hidentity

theorem cutoff_lt_of_cube_lt {n m : ℕ} (h : ¬ m ^ 3 ≤ n) :
    ⌊(n : ℝ) ^ (1 / 6 : ℝ)⌋₊ < m := by
  have hnm : n < m ^ 3 := Nat.lt_of_not_ge h
  have hm3pos : 0 < m ^ 3 := (Nat.zero_le n).trans_lt hnm
  have hm3le : m ^ 3 ≤ m ^ 6 := by
    calc
      m ^ 3 ≤ (m ^ 3) ^ 2 :=
        le_self_pow (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm3pos)) (by norm_num)
      _ = m ^ 6 := by ring
  have hnm6 : n < m ^ 6 := hnm.trans_le hm3le
  have hnm6_real : (n : ℝ) < (m : ℝ) ^ 6 := by exact_mod_cast hnm6
  have hroot : ((m : ℝ) ^ 6) ^ (1 / 6 : ℝ) = (m : ℝ) := by
    calc
      ((m : ℝ) ^ 6) ^ (1 / 6 : ℝ) =
          ((m : ℝ) ^ ((6 : ℕ) : ℝ)) ^ (1 / 6 : ℝ) := by rw [Real.rpow_natCast]
      _ = (m : ℝ) ^ (((6 : ℕ) : ℝ) * (1 / 6 : ℝ)) :=
        (Real.rpow_mul (Nat.cast_nonneg m) _ _).symm
      _ = (m : ℝ) := by norm_num [Real.rpow_one]
  have hroot_lt : (n : ℝ) ^ (1 / 6 : ℝ) < ((m : ℝ) ^ 6) ^ (1 / 6 : ℝ) :=
    (Real.rpow_lt_rpow_iff (Nat.cast_nonneg n) (by positivity) (by norm_num)).2 hnm6_real
  rw [hroot] at hroot_lt
  exact (Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg n) _)).2 hroot_lt

end

end Conjectures.Goldbach.VaughanHighExactSplit_aux

theorem Conjectures.Goldbach.VaughanHighExactSplit :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let Λ := ArithmeticFunction.vonMangoldt; let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let U := fun n : ℕ => ⌊(n : ℝ) ^ (1 / 6 : ℝ)⌋₊; let u := fun (n m : ℕ) => if m ^ 3 ≤ n then 0 else (∑ d ∈ (Nat.divisors m).filter (fun d => d ≤ U n), μ d * Real.log ((m / d : ℕ) : ℝ)) - (∑ d ∈ (Nat.divisors m).filter (fun d => d ≤ U n), μ d * ∑ l ∈ (Nat.divisors (m / d)).filter (fun l => l ≤ U n), Λ l); let v := fun (n m : ℕ) => if m ^ 3 ≤ n then 0 else ∑ a ∈ (Nat.divisors m).filter (fun a => U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let highLambda := fun (n k : ℕ) => if k ^ 3 ≤ n then 0 else Λ k; (∀ n m : ℕ, highLambda n m = u n m + v n m) ∧ (∀ n : ℕ, I n (highLambda n) (highLambda n) = I n (u n) (u n) + 2 * I n (u n) (v n) + I n (v n) (v n)) := by
  classical
  intro E S Q arcs I lam mu U u v highLambda
  have hpoint : ∀ n m : ℕ, highLambda n m = u n m + v n m := by
    intro n m
    by_cases hmn : m ^ 3 ≤ n
    · simp [highLambda, u, v, hmn]
    · have hmU : U n < m := by
        simpa [U] using
          (Conjectures.Goldbach.VaughanHighExactSplit_aux.cutoff_lt_of_cube_lt
            (n := n) (m := m) hmn)
      have hsplit :=
        Conjectures.Goldbach.VaughanHighExactSplit_aux.exact_split (U n) m hmU
      simpa [highLambda, u, v, hmn, mu] using hsplit
  refine ⟨hpoint, ?_⟩
  intro n
  have hgeneric :=
    Conjectures.Goldbach.VaughanHighExactSplit_aux.generic_bilinear_expansion
      n (highLambda n) (u n) (v n) (fun k => hpoint n k)
  simpa only [I, Conjectures.Goldbach.VaughanHighExactSplit_aux.I,
    arcs, Conjectures.Goldbach.VaughanHighExactSplit_aux.arcs,
    S, Conjectures.Goldbach.VaughanHighExactSplit_aux.S,
    E, Conjectures.Goldbach.VaughanHighExactSplit_aux.E,
    Q, Conjectures.Goldbach.VaughanHighExactSplit_aux.Q] using hgeneric
