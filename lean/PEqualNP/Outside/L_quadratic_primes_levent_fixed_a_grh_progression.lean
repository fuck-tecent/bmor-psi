import Mathlib

/-!
A uniform error bound for the von Mangoldt sum in a reduced residue class
under the generalized Riemann hypothesis for Dirichlet L-functions.

Character orthogonality and the prime-power correction reduce the problem to
primitive characters. Jensen estimates count their zeros with multiplicities.
Taking the unit difference of two triangular Perron integrals gives the
sharp cutoff at an integer. Shifting the resulting integral to real part
one quarter yields the zero contributions, the pole of the principal
character, and boundary integrals with uniform bounds.
-/

namespace GoldbachProgression

open scoped BigOperators Classical
open ArithmeticFunction

/-- Removing all indices that are not coprime to the modulus loses at most
one logarithm of the cutoff per distinct prime divisor of the modulus. -/
private theorem sum_vonMangoldt_not_coprime_le (q X : ℕ) (hq : 0 < q) (hX : 0 < X) :
    (∑ n ∈ (Finset.range (X + 1)).filter (fun n => ¬n.Coprime q), vonMangoldt n) ≤
      (q.primeFactors.card : ℝ) * Real.log (X : ℝ) := by
  classical
  let bad := (Finset.range (X + 1)).filter (fun n => ¬n.Coprime q)
  let powers := bad.filter IsPrimePow
  have hsupport : ∑ n ∈ powers, vonMangoldt n = ∑ n ∈ bad, vonMangoldt n := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hn'
    exact vonMangoldt_eq_zero_iff.mpr
      (fun hpow => hn' (Finset.mem_filter.mpr ⟨hn, hpow⟩))
  have hinfo {n : ℕ} (hn : n ∈ powers) :
      n ≤ X ∧ ¬n.Coprime q ∧ IsPrimePow n := by
    obtain ⟨hbad, hp⟩ := Finset.mem_filter.mp hn
    obtain ⟨hrange, hnc⟩ := Finset.mem_filter.mp hbad
    exact ⟨Nat.le_of_lt_succ (Finset.mem_range.mp hrange), hnc, hp⟩
  have hmaps : ∀ n ∈ powers, n.minFac ∈ q.primeFactors := by
    intro n hn
    obtain ⟨_, hnc, hpow⟩ := hinfo hn
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpow
    rw [hp.pow_minFac hk.ne']
    apply hp.mem_primeFactors _ hq.ne'
    by_contra hnd
    exact hnc ((Nat.coprime_pow_left_iff hk p q).2 (hp.coprime_iff_not_dvd.mpr hnd))
  have hfiber (p : ℕ) (hpq : p ∈ q.primeFactors) :
      (∑ n ∈ powers.filter (fun n => n.minFac = p), vonMangoldt n) ≤
        Real.log (X : ℝ) := by
    have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors hpq
    have hsub : powers.filter (fun n => n.minFac = p) ⊆ (p ^ Nat.log p X).divisors := by
      intro n hn
      obtain ⟨hn', hmin⟩ := Finset.mem_filter.mp hn
      obtain ⟨hnX, _, hpow⟩ := hinfo hn'
      obtain ⟨k, _, _, heq⟩ := (isPrimePow_nat_iff_bounded_log_minFac n).mp hpow
      rw [hmin] at heq
      have hk : k ≤ Nat.log p X := (Nat.le_log_iff_pow_le hp.one_lt hX.ne').2
        (heq ▸ hnX)
      apply Nat.mem_divisors.mpr
      refine ⟨?_, pow_ne_zero _ hp.ne_zero⟩
      rw [heq]
      exact pow_dvd_pow p hk
    calc
      _ ≤ ∑ n ∈ (p ^ Nat.log p X).divisors, vonMangoldt n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => vonMangoldt_nonneg)
      _ = Real.log ((p ^ Nat.log p X : ℕ) : ℝ) := vonMangoldt_sum
      _ ≤ _ := Real.log_le_log (by exact_mod_cast pow_pos hp.pos (Nat.log p X))
        (by exact_mod_cast Nat.pow_log_le_self p hX.ne')
  calc
    _ = ∑ n ∈ powers, vonMangoldt n := hsupport.symm
    _ = ∑ p ∈ q.primeFactors, ∑ n ∈ powers.filter (fun n => n.minFac = p),
          vonMangoldt n := (Finset.sum_fiberwise_of_maps_to hmaps (fun n => vonMangoldt n)).symm
    _ ≤ ∑ _p ∈ q.primeFactors, Real.log (X : ℝ) := Finset.sum_le_sum hfiber
    _ = _ := by simp [nsmul_eq_mul]

/-- The total contribution of noncoprime terms is bounded by a product of
two logarithms, uniformly in the modulus and cutoff. -/
private theorem sum_vonMangoldt_not_coprime_le_logs (q X : ℕ) (hq : 0 < q) (hX : 0 < X) :
    (∑ n ∈ (Finset.range (X + 1)).filter (fun n => ¬n.Coprime q), vonMangoldt n) ≤
      (Real.log (q : ℝ) / Real.log 2) * Real.log (X : ℝ) := by
  have hpow : (2 : ℕ) ^ q.primeFactors.card ≤ q := by
    calc
      _ = ∏ _p ∈ q.primeFactors, (2 : ℕ) := by simp
      _ ≤ ∏ p ∈ q.primeFactors, p :=
        Finset.prod_le_prod (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      _ ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  have hreal : (2 : ℝ) ^ q.primeFactors.card ≤ (q : ℝ) := by exact_mod_cast hpow
  have hcard : (q.primeFactors.card : ℝ) ≤ Real.log (q : ℝ) / Real.log 2 := by
    apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
    simpa only [Real.log_pow] using Real.log_le_log (by positivity) hreal
  exact (sum_vonMangoldt_not_coprime_le q X hq hX).trans
    (mul_le_mul_of_nonneg_right hcard
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ X from hX))))

/-- Raising the level of a Dirichlet character changes its finite twisted
von Mangoldt sum by at most the logarithmic cost of the excluded prime powers. -/
private theorem changeLevel_twisted_sum_sub_le {d q : ℕ} (hd : d ∣ q) (hq : 0 < q)
    (χ : DirichletCharacter ℂ d) (X : ℕ) (hX : 0 < X) :
    ‖(∑ n ∈ Finset.range (X + 1),
        (DirichletCharacter.changeLevel hd χ) (n : ZMod q) * (vonMangoldt n : ℂ)) -
      (∑ n ∈ Finset.range (X + 1), χ (n : ZMod d) * (vonMangoldt n : ℂ))‖ ≤
      (Real.log (q : ℝ) / Real.log 2) * Real.log (X : ℝ) := by
  classical
  let ψ := DirichletCharacter.changeLevel hd χ
  let δ (n : ℕ) := ψ (n : ZMod q) * (vonMangoldt n : ℂ) -
    χ (n : ZMod d) * (vonMangoldt n : ℂ)
  have hterm (n : ℕ) : ‖δ n‖ ≤ if ¬n.Coprime q then vonMangoldt n else 0 := by
    by_cases hn : n.Coprime q
    · have hi : IsCoprime (n : ℤ) (q : ℤ) := hn.cast
      have heq : ψ (n : ZMod q) = χ (n : ZMod d) := by
        simpa [ψ] using χ.changeLevel_eq_cast_of_dvd' hd hi
      simp [δ, heq, hn]
    · have hz : ψ (n : ZMod q) = 0 :=
        MulChar.map_nonunit ψ (fun hu => hn ((ZMod.isUnit_iff_coprime n q).mp hu))
      simp only [δ, hz, zero_mul, zero_sub, norm_neg, norm_mul,
        Complex.norm_of_nonneg (vonMangoldt_nonneg (n := n)), ite_eq_left hn]
      exact mul_le_of_le_one_left vonMangoldt_nonneg (χ.norm_le_one _)
  calc
    _ = ‖∑ n ∈ Finset.range (X + 1), δ n‖ := by rw [← Finset.sum_sub_distrib]
    _ ≤ ∑ n ∈ Finset.range (X + 1), ‖δ n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range (X + 1), (if ¬n.Coprime q then vonMangoldt n else 0) :=
      Finset.sum_le_sum fun n _ => hterm n
    _ = ∑ n ∈ (Finset.range (X + 1)).filter (fun n => ¬n.Coprime q), vonMangoldt n := by
      rw [Finset.sum_filter]
    _ ≤ _ := sum_vonMangoldt_not_coprime_le_logs q X hq hX



private noncomputable def twistedError {q : ℕ} (X : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  (∑ k ∈ Finset.range (X + 1), χ (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℂ)) -
    (if χ = 1 then (X : ℂ) else 0)

/-- Character orthogonality transfers a common error bound to every reduced residue class
without increasing it. -/
private theorem progression_error_of_character_error (q a X : ℕ) [NeZero q] (ha : Nat.Coprime a q)
    (B : ℝ) (hχ : ∀ χ : DirichletCharacter ℂ q, ‖twistedError X χ‖ ≤ B) :
    |(∑ k ∈ (Finset.range (X + 1)).filter (fun k => k % q = a % q),
          ArithmeticFunction.vonMangoldt k) - (X : ℝ) / (q.totient : ℝ)| ≤ B := by
  let R := Finset.range (X + 1)
  let S : ℝ := ∑ k ∈ R.filter (fun k => k % q = a % q),
    ArithmeticFunction.vonMangoldt k
  let ψ (χ : DirichletCharacter ℂ q) : ℂ :=
    ∑ k ∈ R, χ (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℂ)
  let M (χ : DirichletCharacter ℂ q) : ℂ := if χ = 1 then (X : ℂ) else 0
  let t := (a : ZMod q)⁻¹
  have ha' : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 ha
  have ht : IsUnit t := isUnit_of_dvd_one ⟨(a : ZMod q), (ZMod.inv_mul_of_unit _ ha').symm⟩
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr q.pos_of_neZero
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hres : S = ∑ k ∈ R, ArithmeticFunction.vonMangoldt.residueClass (a : ZMod q) k := by
    simp only [S, Finset.sum_filter, ArithmeticFunction.vonMangoldt.residueClass,
      Set.indicator_apply, Set.mem_ofPred_eq, ZMod.natCast_eq_natCast_iff']
  -- Sum the pointwise character orthogonality identity over k ≤ X.
  have hexpand : (S : ℂ) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ t * ψ χ := by
    rw [hres, Complex.ofReal_sum]
    simp_rw [ArithmeticFunction.vonMangoldt.residueClass_apply ha']
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro χ _
    simp only [ψ, t, Finset.mul_sum, mul_assoc]
  -- Only the principal character contributes a main term.
  have hmain : (∑ χ : DirichletCharacter ℂ q, χ t * M χ) = (X : ℂ) := by
    simp [M, mul_ite, MulChar.one_apply ht]
  have herr : ((S - (X : ℝ) / q.totient : ℝ) : ℂ) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ t * (ψ χ - M χ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_div]
    simp only [Complex.ofReal_natCast, hexpand, mul_sub, Finset.sum_sub_distrib, hmain,
      div_eq_mul_inv]
    ring
  -- Bound each weighted error and count the φ(q) characters.
  have hsum : ‖∑ χ : DirichletCharacter ℂ q, χ t * (ψ χ - M χ)‖ ≤ (q.totient : ℝ) * B := by
    calc
      _ ≤ ∑ _χ : DirichletCharacter ℂ q, B := by
        apply norm_sum_le_of_le
        intro χ _
        rw [norm_mul]
        calc
          _ ≤ 1 * ‖ψ χ - M χ‖ :=
            mul_le_mul_of_nonneg_right (χ.norm_le_one t) (norm_nonneg _)
          _ ≤ B := by
            by_cases h : χ = 1 <;> simpa [twistedError, ψ, R, M, h] using hχ χ
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  change |S - (X : ℝ) / q.totient| ≤ B
  calc
    _ = ‖((S - (X : ℝ) / q.totient : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ = (q.totient : ℝ)⁻¹ * ‖∑ χ : DirichletCharacter ℂ q, χ t * (ψ χ - M χ)‖ := by
      rw [herr, norm_mul, norm_inv]
      simp
    _ ≤ (q.totient : ℝ)⁻¹ * ((q.totient : ℝ) * B) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hφ.le)
    _ = B := by rw [← mul_assoc, inv_mul_cancel₀ hφ.ne', one_mul]


/-- A common bound for primitive characters, including the character of conductor one,
implies a common progression bound. Raising the level costs at most
`log(q) log(X) / log(2)`. -/
private theorem progression_error_of_primitive_character_error (K : ℝ)
    (hprim : ∀ (d X : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d),
      χ.IsPrimitive → 2 ≤ X → ‖twistedError X χ‖ ≤
        K * Real.sqrt (X : ℝ) * (Real.log (2 * (d : ℝ) * X)) ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ q a X : ℕ, 0 < q → Nat.Coprime a q → 2 ≤ X →
      |(Finset.sum ((Finset.range (X + 1)).filter (fun k => k % q = a % q))
          (fun k => ArithmeticFunction.vonMangoldt k)) - (X : ℝ) / (Nat.totient q : ℝ)| ≤
        C * Real.sqrt (X : ℝ) * (Real.log (2 * (q : ℝ) * X)) ^ 2 := by
  let M := max K 0
  let D := (Real.log 2)⁻¹
  have hM : 0 ≤ M := le_max_right _ _
  have hD : 0 < D := inv_pos.mpr (Real.log_pos (by norm_num))
  refine ⟨M + D, add_pos_of_nonneg_of_pos hM hD, ?_⟩
  intro q a X hq ha hX
  let : NeZero q := ⟨hq.ne'⟩
  let L := Real.log (2 * (q : ℝ) * X)
  have hx1 : 1 ≤ (X : ℝ) := by exact_mod_cast (show 1 ≤ X by omega)
  have hq1 : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q from hq)
  have hxpos : 0 < (X : ℝ) := by linarith
  have hqpos : 0 < (q : ℝ) := by linarith
  have hroot : 1 ≤ Real.sqrt (X : ℝ) := by simpa using Real.sqrt_le_sqrt hx1
  have hlogq : Real.log (q : ℝ) ≤ L := by
    apply Real.log_le_log hqpos
    calc
      (q : ℝ) ≤ 2 * q * 1 := by linarith
      _ ≤ 2 * q * X := mul_le_mul_of_nonneg_left hx1 (by positivity)
  have hlogX : Real.log (X : ℝ) ≤ L := by
    apply Real.log_le_log hxpos
    calc
      (X : ℝ) = 1 * X := (one_mul _).symm
      _ ≤ 2 * q * X := mul_le_mul_of_nonneg_right (by linarith) hxpos.le
  have hL : 0 ≤ L := (Real.log_nonneg hq1).trans hlogq
  have hprod : Real.log (q : ℝ) * Real.log (X : ℝ) ≤ L ^ 2 := by
    simpa only [pow_two] using mul_le_mul hlogq hlogX (Real.log_nonneg hx1) hL
  have hcost : Real.log (q : ℝ) / Real.log 2 * Real.log (X : ℝ) ≤
      D * Real.sqrt X * L ^ 2 := by
    calc
      _ = D * (Real.log (q : ℝ) * Real.log (X : ℝ)) := by
        dsimp only [D]
        rw [div_eq_mul_inv]
        ring
      _ ≤ D * L ^ 2 := mul_le_mul_of_nonneg_left hprod hD.le
      _ = D * 1 * L ^ 2 := by rw [mul_one]
      _ ≤ D * Real.sqrt X * L ^ 2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hroot hD.le) (sq_nonneg _)
  apply progression_error_of_character_error q a X ha
  intro χ
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hdpos : 0 < χ.conductor := Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hdq : (χ.conductor : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hq χ.conductor_dvd_level
  have hd1 : 1 ≤ (χ.conductor : ℝ) := by exact_mod_cast (show 1 ≤ χ.conductor from hdpos)
  let Ld := Real.log (2 * (χ.conductor : ℝ) * X)
  have hLd0 : 0 ≤ Ld := by
    apply Real.log_nonneg
    exact one_le_mul_of_one_le_of_one_le (by linarith) hx1
  have hLd : Ld ≤ L := by
    apply Real.log_le_log (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdq (by norm_num)) hxpos.le
  have hLd2 : Ld ^ 2 ≤ L ^ 2 := by
    simpa only [pow_two] using mul_le_mul hLd hLd hLd0 hL
  have hprimitive : ‖twistedError X χ.primitiveCharacter‖ ≤ M * Real.sqrt X * L ^ 2 := by
    calc
      _ ≤ K * Real.sqrt X * Ld ^ 2 := hprim _ X χ.primitiveCharacter
        χ.primitiveCharacter_isPrimitive hX
      _ ≤ M * Real.sqrt X * Ld ^ 2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)) (sq_nonneg _)
      _ ≤ M * Real.sqrt X * L ^ 2 := mul_le_mul_of_nonneg_left hLd2
        (mul_nonneg hM (Real.sqrt_nonneg _))
  have hone : χ = 1 ↔ χ.primitiveCharacter = 1 := by
    simpa only [χ.changeLevel_primitiveCharacter] using
      (DirichletCharacter.changeLevel_eq_one_iff (χ := χ.primitiveCharacter) χ.conductor_dvd_level)
  have hcorr : ‖twistedError X χ - twistedError X χ.primitiveCharacter‖ ≤
      Real.log (q : ℝ) / Real.log 2 * Real.log (X : ℝ) := by
    have h := changeLevel_twisted_sum_sub_le χ.conductor_dvd_level hq χ.primitiveCharacter
      X (show 0 < X by omega)
    rw [χ.changeLevel_primitiveCharacter] at h
    have cancel (u v m : ℂ) : (u - m) - (v - m) = u - v := by abel
    by_cases hprincipal : χ.primitiveCharacter = 1
    · have hprincipal' := hone.mpr hprincipal
      simpa only [twistedError, ite_eq_left hprincipal, ite_eq_left hprincipal', cancel] using h
    · have hprincipal' := mt hone.mp hprincipal
      simpa only [twistedError, ite_eq_right hprincipal, ite_eq_right hprincipal', cancel] using h
  calc
    _ = ‖(twistedError X χ - twistedError X χ.primitiveCharacter) +
        twistedError X χ.primitiveCharacter‖ := by rw [sub_add_cancel]
    _ ≤ _ := norm_add_le _ _
    _ ≤ D * Real.sqrt X * L ^ 2 + M * Real.sqrt X * L ^ 2 := by
      exact add_le_add (hcorr.trans hcost) hprimitive
    _ = (M + D) * Real.sqrt X * L ^ 2 := by ring

section

open Set Filter Complex DirichletCharacter

private theorem finite_compact_zeros {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {b : ℂ} (hb : f b ≠ 0) {K : Set ℂ} (hK : IsCompact K) :
    {z ∈ K | f z = 0}.Finite := by
  have ha : AnalyticOnNhd ℂ f univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hd := ha.preimage_zero_mem_codiscreteWithin hb
    (show b ∈ (univ : Set ℂ) from mem_univ b) isConnected_univ
  exact (hK.finite_sdiff_of_mem_codiscreteWithin
    (Filter.codiscreteWithin_mono (subset_univ K) hd)).subset fun z hz => ⟨hz.1, by simp [hz.2]⟩

private theorem finite_character_zeros_on_compact {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {K : Set ℂ} (hK : IsCompact K) :
    {z ∈ K | z ≠ 1 ∧ LFunction χ z = 0}.Finite := by
  by_cases hχ : χ = 1
  · subst χ
    refine (finite_compact_zeros (differentiable_LFunctionTrivChar₁ q)
      (LFunctionTrivChar₁_apply_one_ne_zero q) hK).subset ?_
    intro z hz
    refine ⟨hz.1, ?_⟩
    rw [LFunctionTrivChar₁, Function.update_of_ne hz.2.1]
    exact mul_eq_zero_of_right _ hz.2.2
  · have h₂ : LFunction χ 2 ≠ 0 := LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)
    exact (finite_compact_zeros (differentiable_LFunction hχ) h₂ hK).subset
      fun _ hz => ⟨hz.1, hz.2.2⟩

private theorem finite_character_zeros_in_window {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t R : ℝ) :
    {z : ℂ | 0 < z.re ∧ z.re < 1 ∧ |z.im - t| ≤ R ∧ LFunction χ z = 0}.Finite := by
  let K := (Icc (0 : ℝ) 1) ×ℂ (Icc (t - R) (t + R))
  have hk : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  apply (finite_character_zeros_on_compact χ hk).subset
  intro z hz
  obtain ⟨h₀, h₁, him, hL⟩ := hz
  obtain ⟨hl, hr⟩ := abs_le.mp him
  refine ⟨⟨⟨h₀.le, h₁.le⟩, ⟨by linarith, by linarith⟩⟩, ?_, hL⟩
  intro he
  simp [he] at h₁

private theorem positive_multiplicity_of_character_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {z : ℂ} (hz : z ≠ 1) (hL : LFunction χ z = 0) :
    0 < analyticOrderNatAt (LFunction χ) z := by
  let U := ({1}ᶜ : Set ℂ)
  have ha : AnalyticOnNhd ℂ (LFunction χ) U :=
    (show DifferentiableOn ℂ (LFunction χ) U from
      fun w hw => (differentiableAt_LFunction χ w (.inl hw)).differentiableWithinAt).analyticOnNhd
        isOpen_compl_singleton
  have hc : IsConnected U := isConnected_compl_singleton_of_one_lt_rank (by simp) 1
  have h₂ : (2 : ℂ) ∈ U := by simp [U]
  have hn : LFunction χ 2 ≠ 0 := LFunction_ne_zero_of_one_le_re χ (.inr (by norm_num)) (by norm_num)
  have hf : analyticOrderAt (LFunction χ) z ≠ ⊤ :=
    (ha.exists_analyticOrderAt_ne_top_iff_forall hc).mp
      ⟨⟨2, h₂⟩, by rw [(ha 2 h₂).analyticOrderAt_eq_zero.mpr hn]; simp⟩ ⟨z, hz⟩
  exact ENat.toNat_pos ((ha z hz).analyticOrderAt_ne_zero.mpr hL) hf

end

/-- On the line of real part three, the tail of the Dirichlet series has norm at
most one half. The lower bound is uniform in both the character and its modulus. -/
private theorem half_le_norm_LFunction_of_re_eq_three {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s.re = 3) :
    (1 / 2 : ℝ) ≤ ‖χ.LFunction s‖ := by
  have hhalf : 1 < s.re := by rw [hs]; norm_num
  let f := LSeries.term (fun n : ℕ => χ (n : ZMod q)) s
  let u (k : ℕ) : ℝ := 1 / (2 * ((k : ℝ) + 1))
  have hf : Summable f := χ.LSeriesSummable_of_one_lt_re hhalf
  have hterm (k : ℕ) : ‖f (k + 2)‖ ≤ u k - u (k + 1) := by
    have hk : k + 2 ≠ 0 := by omega
    have hnorm : ‖f (k + 2)‖ =
        ‖χ ((k + 2 : ℕ) : ZMod q)‖ / (((k : ℝ) + 2) ^ 3) := by
      simp only [f, LSeries.norm_term_eq, ite_eq_right hk, hs]
      norm_cast
    rw [hnorm]
    calc
      _ ≤ 1 / (((k : ℝ) + 2) ^ 3) :=
        div_le_div_of_nonneg_right (χ.norm_le_one _) (by positivity)
      _ ≤ _ := by
        simp only [u, Nat.cast_add_one]
        have h1 : 0 < (k : ℝ) + 1 := by positivity
        have h2 : 0 < (k : ℝ) + 2 := by positivity
        rw [show (k : ℝ) + 1 + 1 = k + 2 by ring]
        field_simp
        nlinarith [sq_nonneg (k : ℝ)]
  have htail : ‖∑' k : ℕ, f (k + 2)‖ ≤ 1 / 2 := by
    have hshift := (summable_nat_add_iff (f := f) 2).mpr hf
    apply le_of_tendsto hshift.hasSum.tendsto_sum_nat.norm
    apply Filter.Eventually.of_forall
    intro n
    calc
      _ ≤ ∑ k ∈ Finset.range n, (u k - u (k + 1)) :=
        norm_sum_le_of_le _ (fun k _ => hterm k)
      _ = u 0 - u n := Finset.sum_range_sub' u n
      _ ≤ 1 / 2 := by
        have hn : 0 ≤ u n := by dsimp [u]; positivity
        simpa [u] using sub_le_self (u 0) hn
  have hfirst : (∑ k ∈ Finset.range 2, f k) = 1 := by
    simp [Finset.sum_range_succ, f]
  have hsplit : (1 : ℂ) + (∑' k : ℕ, f (k + 2)) = χ.LFunction s := by
    rw [χ.LFunction_eq_LSeries hhalf, ← hfirst]
    exact hf.sum_add_tsum_nat_add 2
  have htriangle := norm_sub_le (χ.LFunction s) (∑' k : ℕ, f (k + 2))
  rw [← hsplit, add_sub_cancel_right, norm_one, hsplit] at htriangle
  linarith

section

open Metric MeromorphicOn

/-- On the critical line, a unit-height window lies inside the radius 11/4 disk
about 3 + it. Jensen's inequality on a slightly larger disk counts its zeros
with multiplicity. -/
private theorem window_multiplicity_le_of_circle_bound (f : ℂ → ℂ) (t M : ℝ) (Z : Finset ℂ)
    (hZ : ∀ z ∈ Z, z.re = 1 / 2 ∧ |z.im - t| ≤ 1)
    (hf : AnalyticOnNhd ℂ f (closedBall (⟨3, t⟩ : ℂ) (23 / 8)))
    (hcenter : f (⟨3, t⟩ : ℂ) ≠ 0) (hM : 1 ≤ M)
    (hbound : ∀ z ∈ sphere (⟨3, t⟩ : ℂ) (23 / 8), ‖f z‖ ≤ M) :
    (∑ z ∈ Z, (analyticOrderNatAt f z : ℤ) : ℤ) ≤
      Real.log (M / ‖f (⟨3, t⟩ : ℂ)‖) / Real.log (23 / 22) := by
  classical
  let c : ℂ := ⟨3, t⟩
  let r : ℝ := 11 / 4
  let R : ℝ := 23 / 8
  have hr : 0 < r := by norm_num [r]
  have hR : 0 < R := by norm_num [R]
  have hrR : r < R := by norm_num [r, R]
  have han : AnalyticOnNhd ℂ f (closedBall c r) := hf.mono (closedBall_subset_closedBall hrR.le)
  have hmem (z : ℂ) (hz : z ∈ Z) : z ∈ closedBall c r := by
    obtain ⟨hre, him⟩ := hZ z hz
    have hs := sq_le_sq' (abs_le.mp him).1 (abs_le.mp him).2
    rw [mem_closedBall, dist_eq_norm]
    have heq := Complex.sq_norm_sub_sq_re (z - c)
    simp only [Complex.sub_re, Complex.sub_im, c, hre] at heq
    dsimp [r]
    nlinarith
  let d := divisor f (closedBall c r)
  have hd (z : ℂ) (hz : z ∈ Z) : (analyticOrderNatAt f z : ℤ) = d z := by
    change _ = divisor f (closedBall c r) z
    rw [han.divisor_apply (hmem z hz)]
    unfold analyticOrderNatAt
    cases h : analyticOrderAt f z using ENat.recTopCoe <;> simp
  have hsupp := d.finiteSupport (isCompact_closedBall c r)
  let U := Z ∪ hsupp.toFinset
  have hu : Function.support d ⊆ (U : Set ℂ) := by
    intro z hz
    exact Finset.mem_union_right _ (hsupp.mem_toFinset.mpr hz)
  have hsum : (∑ z ∈ Z, (analyticOrderNatAt f z : ℤ)) ≤ ∑ᶠ z, d z := by
    rw [finsum_eq_sum_of_support_subset _ hu]
    calc
      _ = ∑ z ∈ Z, d z := Finset.sum_congr rfl hd
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun z _ _ => han.divisor_nonneg z)
  have hj := AnalyticOnNhd.sum_divisor_le (c := c) (r := r) (R := R) (M := M)
    (by simpa only [abs_of_pos hr] using hr) (by simpa only [abs_of_pos hr, abs_of_pos hR] using hrR)
    hM (by simpa only [abs_of_pos hR] using hf) hcenter
    (by simpa only [abs_of_pos hR] using hbound)
  have hratio : R / r = 23 / 22 := by norm_num [R,r]
  rw [abs_of_pos hr, hratio] at hj
  exact le_trans (by exact_mod_cast hsum) hj

end

section

open Finset Filter Set MeasureTheory Complex Asymptotics
open scoped BigOperators Topology

private theorem complete_character_sum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) :
    ∑ k ∈ range q, χ (k : ZMod q) = 0 := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
    rw [← Fin.sum_univ_eq_sum_range]
    convert χ.sum_eq_zero_of_ne_one hne using 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt i.isLt)

private theorem char_partial_norm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)‖ ≤ (q : ℝ) + 1 := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hr (m : ℕ) : ‖∑ k ∈ range m, χ (k : ZMod q)‖ ≤ (q : ℝ) := by
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      by_cases hm : m < q
      · calc
          _ ≤ ∑ k ∈ range m, ‖χ (k : ZMod q)‖ := norm_sum_le _ _
          _ ≤ ∑ _k ∈ range m, (1 : ℝ) := Finset.sum_le_sum fun k _ => χ.norm_le_one _
          _ ≤ (q : ℝ) := by simpa using (Nat.cast_le.mpr hm.le : (m : ℝ) ≤ q)
      · have hmq : m = q + (m - q) := by omega
        conv_lhs => rw [hmq, sum_range_add, complete_character_sum χ hne, zero_add]
        simpa only [Nat.cast_add, ZMod.natCast_self, zero_add] using ih (m - q) (by omega)
  have htotal : ∑ k ∈ range (n+1), χ (k : ZMod q) =
      χ 0 + ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q) := by
    rw [Nat.range_succ_eq_Icc_zero,
      ← Finset.insert_Icc_add_one_left_eq_Icc n.zero_le, Finset.sum_insert (by simp)]
    simp
  have hdiff : (∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)) =
      (∑ k ∈ range (n+1), χ (k : ZMod q)) - χ 0 := by rw [htotal]; abel
  rw [hdiff]
  exact (norm_sub_le ..).trans (add_le_add (hr _) (χ.norm_le_one _))

private noncomputable def charSum {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod q)

private theorem charSum_measurable {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Measurable (charSum χ) :=
  (measurable_of_countable (f := fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q))).comp
    Nat.measurable_floor

private noncomputable def charMellin {q : ℕ} (χ : DirichletCharacter ℂ q) :=
  (Ioi (1 : ℝ)).indicator (charSum χ)

private theorem charMellin_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) :
    mellin (charMellin χ) (-s) =
      ∫ t in Ioi (1 : ℝ), charSum χ t * (t : ℂ) ^ (-(s + 1)) := by
  have hf : (fun t : ℝ => (t : ℂ) ^ (-s - 1) • charMellin χ t) =
      (Set.Ioi (1 : ℝ)).indicator (fun t : ℝ => charSum χ t * (t : ℂ) ^ (-(s+1))) := by
    funext t
    by_cases ht : t ∈ Ioi (1 : ℝ) <;>
      simp [charMellin, Set.indicator, ht, smul_eq_mul, show -s-1 = -(s+1) by ring, mul_comm]
  rw [mellin, hf, setIntegral_indicator measurableSet_Ioi,
    Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))]

private theorem nonprincipal_LFunction_eq_partial_integral {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    χ.LFunction s = s * ∫ t in Ioi (1 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(s + 1)) := by
  let F := charMellin χ
  have hbound (t : ℝ) : ‖F t‖ ≤ (q : ℝ) + 1 := by
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · simpa [F, charMellin, Set.indicator_of_mem ht, charSum] using char_partial_norm χ hne ⌊t⌋₊
    · simp [F, charMellin, Set.indicator_of_notMem ht]
      positivity
  have hmeas : Measurable F := (charSum_measurable χ).indicator measurableSet_Ioi
  have hloc : LocallyIntegrableOn F (Ioi 0) := by
    apply (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).2
    intro K _ hK
    exact Measure.integrableOn_of_bounded hK.measure_lt_top.ne hmeas.aestronglyMeasurable
      (Eventually.of_forall hbound)
  have htop : F =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
    apply Asymptotics.IsBigO.of_bound ((q : ℝ) + 1)
    exact Eventually.of_forall (fun t => by simpa using hbound t)
  have hbot (b : ℝ) : F =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
    apply Asymptotics.IsBigO.of_bound 0
    have hsm : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hsm] with t ht
    simp [F, charMellin, not_lt.mpr ht.le]
  let U := {z : ℂ | 0 < z.re}
  have ho : IsOpen U := continuous_re.isOpen_preimage (Set.Ioi (0:ℝ)) isOpen_Ioi
  have hd : AnalyticOnNhd ℂ (fun z : ℂ => z * mellin F (-z)) U := by
    apply DifferentiableOn.analyticOnNhd _ ho
    intro z hz
    have hm := mellin_differentiableAt_of_isBigO_rpow (s := -z) hloc htop
      (show (-z).re < 0 by simpa using (show 0 < z.re from hz)) (hbot ((-z).re - 1)) (by linarith)
    exact (differentiableAt_id.mul (hm.comp z differentiableAt_id.neg)).differentiableWithinAt
  have hχ : AnalyticOnNhd ℂ χ.LFunction U := by
    exact (χ.differentiable_LFunction hne).differentiableOn.analyticOnNhd ho
  have hagree : χ.LFunction =ᶠ[𝓝 (2:ℂ)] fun z => z * mellin F (-z) := by
    filter_upwards [(continuous_re.isOpen_preimage (Set.Ioi (1:ℝ)) isOpen_Ioi).mem_nhds
      (show 1 < (2:ℂ).re by norm_num)] with z hz
    have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q))
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ (0 : ℝ)) := by
      apply Asymptotics.IsBigO.of_bound ((q : ℝ) + 1)
      exact Eventually.of_forall (fun n => by simpa using char_partial_norm χ hne n)
    rw [show F = charMellin χ from rfl, charMellin_eq, χ.LFunction_eq_LSeries hz]
    exact LSeries_eq_mul_integral _ le_rfl (zero_lt_one.trans hz) (χ.LSeriesSummable_of_one_lt_re hz) hO
  have hh := hχ.eqOn_of_preconnected_of_eventuallyEq hd (convex_halfSpace_re_gt 0).isPreconnected
    (show (2:ℂ) ∈ U by change 0 < (2:ℂ).re; norm_num) hagree hs
  simpa only [F, charMellin_eq, charSum] using hh

/-- The elementary vertical-growth bound from the bounded sums of a
nonprincipal character, throughout the open right half-plane. -/
private theorem nonprincipal_LFunction_norm_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    ‖χ.LFunction s‖ ≤ ‖s‖ * ((q : ℝ) + 1) / s.re := by
  rw [nonprincipal_LFunction_eq_partial_integral χ hne s hs, norm_mul, mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have he : -(s.re + 1) < -1 := by linarith
  calc
    _ ≤ ∫ t in Set.Ioi (1 : ℝ), ((q : ℝ) + 1) * t ^ (-(s.re + 1)) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_Ioi_rpow_of_lt he zero_lt_one).const_mul ((q : ℝ) + 1))
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
      have ht' : (0 : ℝ) < t := zero_lt_one.trans ht
      simp only [norm_mul, norm_cpow_eq_rpow_re_of_pos ht', neg_re, add_re, one_re]
      exact mul_le_mul_of_nonneg_right (char_partial_norm χ hne _) (Real.rpow_nonneg ht'.le _)
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt he zero_lt_one,
        Real.one_rpow, show -(s.re + 1) + 1 = -s.re by ring]
      simp [div_eq_mul_inv]

/-- A uniform upper bound on the strip used to count zeros by Jensen's formula. -/
private theorem nonprincipal_LFunction_norm_le_on_strip {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (s : ℂ) (hs : 1 / 8 ≤ s.re) :
    ‖χ.LFunction s‖ ≤ 16 * (q : ℝ) * ‖s‖ := by
  have hs' : 0 < s.re := by linarith
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  apply (nonprincipal_LFunction_norm_le χ hne s hs').trans
  apply (div_le_iff₀ hs').2
  have h1 := mul_le_mul_of_nonneg_right hs (show 0 ≤ 16 * (q : ℝ) * ‖s‖ by positivity)
  have h2 := mul_le_mul_of_nonneg_left hq (norm_nonneg s)
  linarith only [h1, h2]

end

section

open scoped BigOperators
open Metric

/-- Count nontrivial zeros of a nonprincipal character in a unit window
with their analytic multiplicities, uniformly in the modulus and height. -/
private theorem nonprincipal_character_window_count {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ) (Z : Finset ℂ)
    (hGRH : ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.re = 1 / 2)
    (hZ : ∀ z ∈ Z, 0 < z.re ∧ z.re < 1 ∧ χ.LFunction z = 0 ∧ |z.im - t| ≤ 1) :
    (∑ z ∈ Z, (analyticOrderNatAt χ.LFunction z : ℝ)) ≤
      (8 / Real.log (23 / 22)) * Real.log ((q : ℝ) * (2 + |t|)) := by
  let c : ℂ := ⟨3, t⟩
  let U : ℝ := (q : ℝ) * (2 + |t|)
  let M := 64 * U
  have hq : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q from q.pos_of_neZero)
  have hU : 2 ≤ U := calc
    (2 : ℝ) ≤ 2 + |t| := le_add_of_nonneg_right (abs_nonneg _)
    _ ≤ U := le_mul_of_one_le_left (by positivity) hq
  have hUpos : 0 < U := by linarith
  have hM : 1 ≤ M := by dsimp only [M]; linarith
  have hc : ‖c‖ ≤ 3 + |t| := by
    simpa [c] using Complex.norm_le_abs_re_add_abs_im c
  have hbound (z : ℂ) (hz : z ∈ sphere c (23 / 8)) : ‖χ.LFunction z‖ ≤ M := by
    have hdist : ‖z - c‖ = 23 / 8 := by simpa only [mem_sphere, dist_eq_norm] using hz
    have hre : |z.re - 3| ≤ 23 / 8 := by
      simpa only [Complex.sub_re, hdist, c] using Complex.abs_re_le_norm (z - c)
    have hl := (abs_le.mp hre).1
    have hzNorm : ‖z‖ ≤ 23 / 8 + (3 + |t|) := by
      calc ‖z‖ ≤ ‖z - c‖ + ‖c‖ := norm_le_norm_sub_add _ _
           _ ≤ _ := by rw [hdist]; linarith
    calc
      _ ≤ 16 * (q : ℝ) * ‖z‖ := nonprincipal_LFunction_norm_le_on_strip χ hχ z (by linarith)
      _ ≤ 16 * (q : ℝ) * (4 * (2 + |t|)) :=
        mul_le_mul_of_nonneg_left (by linarith [abs_nonneg t]) (by positivity)
      _ = M := by dsimp only [M, U]; ring
  have hlower : 1 / 2 ≤ ‖χ.LFunction c‖ := half_le_norm_LFunction_of_re_eq_three χ rfl
  have hcenter : 0 < ‖χ.LFunction c‖ := by linarith
  have hj := window_multiplicity_le_of_circle_bound χ.LFunction t M Z
    (fun z hz => ⟨hGRH z (hZ z hz).1 (hZ z hz).2.1 (hZ z hz).2.2.1, (hZ z hz).2.2.2⟩)
    (fun z _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z)
    (norm_pos_iff.mp hcenter) hM hbound
  have hratio : M / ‖χ.LFunction c‖ ≤ 128 * U := by
    apply (div_le_iff₀ hcenter).2
    calc
      M = 128 * U * (1 / 2) := by dsimp only [M]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlower (by positivity)
  have hlog : Real.log (M / ‖χ.LFunction c‖) ≤ 8 * Real.log U := by
    calc
      _ ≤ Real.log (128 * U) := Real.log_le_log (div_pos (by linarith) hcenter) hratio
      _ = 7 * Real.log 2 + Real.log U := by
        rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_mul (by norm_num) hUpos.ne', Real.log_pow]
        norm_num
      _ ≤ _ := by linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hU]
  have hden : 0 < Real.log (23 / 22) := Real.log_pos (by norm_num)
  calc
    _ ≤ Real.log (M / ‖χ.LFunction c‖) / Real.log (23 / 22) := by exact_mod_cast hj
    _ ≤ (8 * Real.log U) / Real.log (23 / 22) := div_le_div_of_nonneg_right hlog hden.le
    _ = _ := by dsimp only [U]; ring


end

section

open Set Complex MeasureTheory

private noncomputable def perronWeight (t : ℝ) : ℂ :=
  (Ioc (0 : ℝ) 1).indicator (fun x => 1 - (x : ℂ)) t

private theorem perronWeight_hasMellin {s : ℂ} (hs : 0 < s.re) :
    HasMellin perronWeight s (1 / (s * (s + 1))) := by
  have h₁ := hasMellin_one_Ioc hs
  have h₂ := hasMellin_cpow_Ioc 1 (s := s) (by simp; linarith)
  have h := hasMellin_sub h₁.1 h₂.1
  rw [h₁.2, h₂.2] at h
  have hfun : (fun t : ℝ => (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t -
      (Ioc (0 : ℝ) 1).indicator (fun u => (u : ℂ) ^ (1 : ℂ)) t) = perronWeight := by
    funext t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1 <;> simp [perronWeight, ht]
  rw [hfun] at h
  convert h using 1
  have hz : s ≠ 0 := by intro h; simp [h] at hs
  have ho : s + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  field_simp
  ring

/-- The inverse Mellin transform on the line of real part two gives the usual
linear smoothing of a sharp cutoff. -/
private theorem perronWeight_inversion {x : ℝ} (hx : 0 < x) :
    mellinInv 2 (fun s : ℂ => 1 / (s * (s + 1))) x = perronWeight x := by
  let s (t : ℝ) : ℂ := 2 + (t : ℂ) * I
  have hline (t : ℝ) : (s t).re = 2 := by simp [s]
  have htransform (t : ℝ) : mellin perronWeight (s t) = 1 / (s t * (s t + 1)) :=
    (perronWeight_hasMellin (by rw [hline]; norm_num)).2
  have hb (t : ℝ) : 1 + t ^ 2 ≤ ‖s t‖ * ‖s t + 1‖ := by
    have h1 := Complex.sq_norm (s t)
    have h2 := Complex.sq_norm (s t + 1)
    simp [s, Complex.normSq_apply] at h1 h2
    have hn : ‖s t‖ ≤ ‖s t + 1‖ := by nlinarith [norm_nonneg (s t + 1)]
    nlinarith [mul_le_mul_of_nonneg_left hn (norm_nonneg (s t))]
  have hv : VerticalIntegrable (mellin perronWeight) 2 := by
    change Integrable fun y : ℝ => mellin perronWeight (s y)
    simp_rw [htransform]
    apply integrable_inv_one_add_sq.mono'
    · exact (by fun_prop : Measurable (fun y : ℝ => 1 / (s y * (s y + 1)))).aestronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro t
      rw [norm_div, norm_one, norm_mul, one_div]
      exact inv_anti₀ (by positivity) (hb t)
  have hcont : ContinuousAt perronWeight x := by
    have heq : perronWeight =ᶠ[nhds x] fun u : ℝ => ((max (1-u) 0 : ℝ) : ℂ) := by
      filter_upwards [lt_mem_nhds hx] with y hy
      by_cases h : y ≤ 1
      · simp [perronWeight, hy, h]
      · simp [perronWeight, h, max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]
    exact (by fun_prop : ContinuousAt (fun u : ℝ => ((max (1-u) 0 : ℝ) : ℂ)) x).congr_of_eventuallyEq heq
  have hi := mellinInv_mellin_eq 2 perronWeight hx (perronWeight_hasMellin (by norm_num)).1 hv hcont
  unfold mellinInv at hi ⊢
  simpa only [show ∀ t : ℝ, mellin perronWeight ((2 : ℝ) + (t : ℂ) * I) =
      1 / (((2 : ℝ) + (t : ℂ) * I) * (((2 : ℝ) + (t : ℂ) * I) + 1)) from htransform] using hi

end


section

open Finset Filter Set MeasureTheory Complex Asymptotics
open scoped BigOperators Topology

private noncomputable def fracPart (t : ℝ) : ℂ := ((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ)

private theorem measurable_fracPart : Measurable fracPart := by
  unfold fracPart
  fun_prop

private theorem frac_norm {t : ℝ} (ht : 0 ≤ t) : ‖fracPart t‖ ≤ 1 := by
  rw [fracPart, Complex.norm_of_nonneg (Nat.zero_le_self_sub_floor ht)]
  exact (Nat.self_sub_floor_lt_one t).le

private noncomputable def fracMellinFun := (Set.Ioi (1 : ℝ)).indicator fracPart

private theorem mellin_frac_eq (s : ℂ) :
    mellin fracMellinFun (-s) = ∫ t in Set.Ioi (1 : ℝ), fracPart t * (t : ℂ) ^ (-(s + 1)) := by
  have hf : (fun t : ℝ => (t : ℂ) ^ (-s - 1) • fracMellinFun t) =
      (Set.Ioi (1 : ℝ)).indicator (fun t : ℝ => fracPart t * (t : ℂ) ^ (-(s+1))) := by
    funext t
    by_cases ht : t ∈ Set.Ioi (1 : ℝ) <;>
      simp [fracMellinFun, Set.indicator, ht, smul_eq_mul, show -s-1 = -(s+1) by ring, mul_comm]
  rw [mellin, hf, setIntegral_indicator measurableSet_Ioi,
    Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))]

private theorem frac_kernel_bound (s : ℂ) {t : ℝ} (ht : 1 < t) :
    ‖fracPart t * (t : ℂ) ^ (-(s+1))‖ ≤ t ^ (-(s.re+1)) := by
  have ht' := zero_lt_one.trans ht
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht', neg_re, add_re, one_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg ht'.le _) (frac_norm ht'.le)

private theorem frac_kernel_integrable (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => fracPart t * (t : ℂ) ^ (-(s+1))) (Set.Ioi 1) := by
  apply (integrableOn_Ioi_rpow_of_lt (show -(s.re+1) < -1 by linarith) zero_lt_one).mono'
  · exact (measurable_fracPart.mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    exact frac_kernel_bound s ht

private theorem zeta_mellin_right (s : ℂ) (hs : 1 < s.re) :
    riemannZeta₁ s = s - (s - 1) * s * mellin fracMellinFun (-s) := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have h0 : 0 < s.re := zero_lt_one.trans hs
  have hZ : riemannZeta s =
      s * ∫ t in Set.Ioi (1 : ℝ), (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s+1)) := by
    rw [← LSeries_one_eq_riemannZeta hs, LSeries_eq_mul_integral (1 : ℕ → ℂ) zero_le_one
      hs (LSeriesSummable_one_iff.mpr hs)]
    · simp [Nat.card_Icc]
    · apply Asymptotics.IsBigO.of_bound 1
      exact Eventually.of_forall (fun n => by simp [Nat.card_Icc])
  have he : (-s).re < -1 := by simpa using hs
  have hI := integral_Ioi_cpow_of_lt he zero_lt_one
  have hc : (s - 1) * (∫ t : ℝ in Set.Ioi 1, (t : ℂ) ^ (-s)) = 1 := by
    rw [hI, ofReal_one, one_cpow, show -s + 1 = -(s - 1) by ring, neg_div_neg_eq]
    field_simp [sub_ne_zero.mpr hs1]
  have hsplit : (∫ t in Set.Ioi (1:ℝ), (⌊t⌋₊ : ℂ) * (t:ℂ)^(-(s+1))) =
      (∫ t : ℝ in Set.Ioi 1, (t:ℂ)^(-s)) - mellin fracMellinFun (-s) := by
    rw [mellin_frac_eq, ← integral_sub (integrableOn_Ioi_cpow_of_lt he zero_lt_one)
      (frac_kernel_integrable s h0)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have hz : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'
    have hp : (t:ℂ) ^ (-s) = (t:ℂ) * (t:ℂ) ^ (-(s+1)) := by
      conv_lhs => rw [show -s = 1 + (-(s+1)) by ring, cpow_add _ _ hz, cpow_one]
    dsimp only
    rw [hp, fracPart, ofReal_sub, ofReal_natCast]
    ring
  have hreg : riemannZeta₁ s = (s-1) * riemannZeta s := by
    rw [riemannZeta_eq_inv_sub_mul hs1, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs1), one_mul]
  rw [hreg, hZ, hsplit]
  linear_combination s * hc

/-- Euler's integral representation of the zeta function after removal of its
simple pole. The entire function on the left takes the value one at one. -/
private theorem zeta_pole_removed_eq_floor_integral (s : ℂ) (hs : 0 < s.re) :
    riemannZeta₁ s = s - (s - 1) * s * ∫ t in Set.Ioi (1 : ℝ),
      (((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
  have hbound (t : ℝ) : ‖fracMellinFun t‖ ≤ 1 := by
    by_cases ht : t ∈ Set.Ioi (1 : ℝ)
    · simpa only [fracMellinFun, Set.indicator_of_mem ht] using frac_norm (zero_lt_one.trans ht).le
    · simp [fracMellinFun, Set.indicator_of_notMem ht]
  have hloc : LocallyIntegrableOn fracMellinFun (Set.Ioi 0) := by
    apply (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).2
    intro K _ hK
    exact Measure.integrableOn_of_bounded hK.measure_lt_top.ne
      (measurable_fracPart.indicator measurableSet_Ioi).aestronglyMeasurable
      (Eventually.of_forall hbound)
  have htop : fracMellinFun =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
    apply Asymptotics.IsBigO.of_bound 1
    exact Eventually.of_forall (fun t => by simpa using hbound t)
  have hbot (b : ℝ) : fracMellinFun =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
    apply Asymptotics.IsBigO.of_bound 0
    have hsm : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hsm] with t ht
    simp [fracMellinFun, not_lt.mpr ht.le]
  let U := {z : ℂ | 0 < z.re}
  have ho : IsOpen U := continuous_re.isOpen_preimage (Set.Ioi (0:ℝ)) isOpen_Ioi
  have hd : AnalyticOnNhd ℂ (fun z : ℂ => z - (z - 1) * z * mellin fracMellinFun (-z)) U := by
    apply DifferentiableOn.analyticOnNhd _ ho
    intro z hz
    have hm := mellin_differentiableAt_of_isBigO_rpow (s := -z) hloc htop
      (show (-z).re < 0 by simpa using (show 0 < z.re from hz)) (hbot ((-z).re - 1)) (by linarith)
    exact (differentiableAt_id.sub (((differentiableAt_id.sub_const 1).mul differentiableAt_id).mul
      (hm.comp z differentiableAt_id.neg))).differentiableWithinAt
  have hZ := differentiable_riemannZeta₁.differentiableOn.analyticOnNhd ho
  have hagree : riemannZeta₁ =ᶠ[𝓝 (2:ℂ)] fun z => z - (z-1)*z*mellin fracMellinFun (-z) := by
    filter_upwards [(continuous_re.isOpen_preimage (Set.Ioi (1:ℝ)) isOpen_Ioi).mem_nhds
      (show 1 < (2:ℂ).re by norm_num)] with z hz
    exact zeta_mellin_right z hz
  have hh := hZ.eqOn_of_preconnected_of_eventuallyEq hd (convex_halfSpace_re_gt 0).isPreconnected
    (show (2:ℂ) ∈ U by change 0 < (2:ℂ).re; norm_num) hagree hs
  simpa only [mellin_frac_eq, fracPart] using hh

/-- Uniform polynomial growth of the entire pole-removed zeta function on
the half-plane containing the nonprincipal character strip. -/
private theorem zeta_pole_removed_norm_le_on_strip (s : ℂ) (hs : 1 / 8 ≤ s.re) :
    ‖riemannZeta₁ s‖ ≤ 9 * (1 + ‖s‖)^2 := by
  have hs' : 0 < s.re := by linarith
  have he : -(s.re+1) < -1 := by linarith
  have hI : ‖∫ t in Set.Ioi (1:ℝ), fracPart t * (t:ℂ)^(-(s+1))‖ ≤ 8 := by
    calc
      _ ≤ ∫ t in Set.Ioi (1:ℝ), t ^ (-(s.re+1)) := by
        apply norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt he zero_lt_one)
        filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
        exact frac_kernel_bound s ht
      _ ≤ 8 := by
        rw [integral_Ioi_rpow_of_lt he zero_lt_one, Real.one_rpow,
          show -(s.re+1)+1 = -s.re by ring, neg_div_neg_eq, div_le_iff₀ hs']
        linarith
  rw [zeta_pole_removed_eq_floor_integral s hs']
  apply (norm_sub_le ..).trans
  rw [norm_mul, norm_mul]
  have hsub : ‖s - 1‖ ≤ ‖s‖ + 1 := by simpa using norm_sub_le s (1:ℂ)
  calc
    _ ≤ ‖s‖ + (‖s‖ + 1) * ‖s‖ * 8 := by
      gcongr
      exact hI
    _ ≤ _ := by nlinarith [sq_nonneg ‖s‖, norm_nonneg s]

end

section

open scoped BigOperators Topology
open Metric

private theorem regular_zeta_eq_mul {z : ℂ} (hz : z ≠ 1) :
    riemannZeta₁ z = (z - 1) * riemannZeta z := by
  rw [riemannZeta_eq_inv_sub_mul hz, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hz), one_mul]

private theorem regular_zeta_order {z : ℂ} (hz : z ≠ 1) :
    analyticOrderNatAt riemannZeta₁ z = analyticOrderNatAt riemannZeta z := by
  have he : riemannZeta₁ =ᶠ[𝓝 z] fun w => (w - 1) * riemannZeta w := by
    filter_upwards [compl_singleton_mem_nhds hz] with w hw using regular_zeta_eq_mul hw
  have hfactor : AnalyticAt ℂ (fun w : ℂ => w - 1) z := by fun_prop
  have hζ := analyticOn_riemannZeta z hz
  rw [analyticOrderNatAt, analyticOrderAt_congr he, analyticOrderAt_fun_mul hfactor hζ,
    hfactor.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hz), zero_add]
  rfl

/-- Count zeros of the Riemann zeta function with multiplicity inside a unit
height window, assuming that its nontrivial zeros are on the critical line. -/
private theorem zeta_window_multiplicity (t : ℝ) (Z : Finset ℂ)
    (hRH : ∀ z : ℂ, 0 < z.re → z.re < 1 → riemannZeta z = 0 → z.re = 1 / 2)
    (hZ : ∀ z ∈ Z, 0 < z.re ∧ z.re < 1 ∧ riemannZeta z = 0 ∧ |z.im - t| ≤ 1) :
    (∑ z ∈ Z, (analyticOrderNatAt riemannZeta z : ℝ)) ≤
      (10 / Real.log (23 / 22)) * Real.log (2 + |t|) := by
  let c : ℂ := ⟨3, t⟩
  let U : ℝ := 2 + |t|
  let M : ℝ := 256 * U^2
  have hU : 2 ≤ U := le_add_of_nonneg_right (abs_nonneg t)
  have hUpos : 0 < U := by linarith
  have hM : 1 ≤ M := by dsimp only [M]; nlinarith [sq_nonneg (U-2)]
  have hc : ‖c‖ ≤ 3 + |t| := by simpa [c] using Complex.norm_le_abs_re_add_abs_im c
  have hbound (z : ℂ) (hz : z ∈ sphere c (23 / 8)) : ‖riemannZeta₁ z‖ ≤ M := by
    have hdist : ‖z-c‖ = 23/8 := by simpa only [mem_sphere, dist_eq_norm] using hz
    have hre : |z.re - 3| ≤ 23/8 := by
      simpa only [Complex.sub_re, hdist, c] using Complex.abs_re_le_norm (z-c)
    have hzN : 1 + ‖z‖ ≤ 4 * U := by
      have h := norm_le_norm_sub_add z c
      rw [hdist] at h
      dsimp only [U]
      linarith [abs_nonneg t]
    calc
      _ ≤ 9 * (1 + ‖z‖)^2 := zeta_pole_removed_norm_le_on_strip _ (by linarith [(abs_le.mp hre).1])
      _ ≤ 9 * (4 * U)^2 := by gcongr
      _ ≤ M := by dsimp only [M]; nlinarith [sq_nonneg U]
  have hfac : 2 ≤ ‖c - 1‖ := by
    convert Complex.abs_re_le_norm (c-1) using 1
    norm_num [c]
  have hζ : (1/2 : ℝ) ≤ ‖riemannZeta c‖ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      (half_le_norm_LFunction_of_re_eq_three (1 : DirichletCharacter ℂ 1) (s := c) rfl)
  have hcne : c ≠ 1 := by intro h; have := congrArg Complex.re h; norm_num [c] at this
  have hcen : 1 ≤ ‖riemannZeta₁ c‖ := by
    rw [regular_zeta_eq_mul hcne, norm_mul]
    calc (1:ℝ) = 2 * (1/2) := by norm_num
         _ ≤ _ := mul_le_mul hfac hζ (by norm_num) (norm_nonneg _)
  have hcenpos : 0 < ‖riemannZeta₁ c‖ := zero_lt_one.trans_le hcen
  have hj := window_multiplicity_le_of_circle_bound riemannZeta₁ t M Z
    (fun z hz => ⟨hRH z (hZ z hz).1 (hZ z hz).2.1 (hZ z hz).2.2.1, (hZ z hz).2.2.2⟩)
    (fun z _ => differentiable_riemannZeta₁.analyticAt z)
    (norm_pos_iff.mp hcenpos) hM hbound
  have hlog : Real.log (M / ‖riemannZeta₁ c‖) ≤ 10 * Real.log U := by
    calc
      _ ≤ Real.log M := Real.log_le_log (div_pos (by linarith) hcenpos) (div_le_self (by linarith) hcen)
      _ = 8 * Real.log 2 + 2 * Real.log U := by
        rw [show M = (2 : ℝ)^8 * U^2 by norm_num [M],
          Real.log_mul (by norm_num) (pow_ne_zero _ hUpos.ne'), Real.log_pow, Real.log_pow]
        norm_num
      _ ≤ _ := by linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hU]
  have hden : 0 < Real.log (23/22) := Real.log_pos (by norm_num)
  calc
    _ = ∑ z ∈ Z, (analyticOrderNatAt riemannZeta₁ z : ℝ) := by
      apply Finset.sum_congr rfl
      intro z hz
      have hne : z ≠ 1 := by
        intro h; have := (hZ z hz).2.1; simp [h] at this
      rw [regular_zeta_order hne]
    _ ≤ Real.log (M / ‖riemannZeta₁ c‖) / Real.log (23/22) := by exact_mod_cast hj
    _ ≤ (10 * Real.log U) / Real.log (23/22) := div_le_div_of_nonneg_right hlog hden.le
    _ = _ := by dsimp only [U]; ring

/-- The same logarithmic count for all primitive Dirichlet characters,
including the principal character of conductor one. -/
private theorem primitive_character_window_count {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (t : ℝ) (Z : Finset ℂ)
    (hGRH : ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.re = 1 / 2)
    (hZ : ∀ z ∈ Z, 0 < z.re ∧ z.re < 1 ∧ χ.LFunction z = 0 ∧ |z.im - t| ≤ 1) :
    (∑ z ∈ Z, (analyticOrderNatAt χ.LFunction z : ℝ)) ≤
      (10 / Real.log (23 / 22)) * Real.log ((q : ℝ) * (2 + |t|)) := by
  by_cases hχ : χ = 1
  · subst χ
    have h : (1 : DirichletCharacter ℂ q).conductor = q := hprim
    have hq : q = 1 := by simpa only [DirichletCharacter.conductor_one] using h.symm
    subst q
    simp only [DirichletCharacter.LFunction_modOne_eq, Nat.cast_one, one_mul] at *
    exact zeta_window_multiplicity t Z hGRH hZ
  · apply (nonprincipal_character_window_count χ hχ t Z hGRH hZ).trans
    have hq : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q from q.pos_of_neZero)
    have hlog : 0 ≤ Real.log ((q : ℝ) * (2 + |t|)) :=
      Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq (by linarith [abs_nonneg t]))
    gcongr
    norm_num

private theorem primitive_character_full_window_count {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (t : ℝ)
    (hGRH : ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.re = 1 / 2) :
    (∑ z ∈ (finite_character_zeros_in_window χ t 1).toFinset,
        (analyticOrderNatAt χ.LFunction z : ℝ)) ≤
      (10 / Real.log (23 / 22)) * Real.log ((q : ℝ) * (2 + |t|)) := by
  apply primitive_character_window_count χ hprim t _ hGRH
  intro z hz
  obtain ⟨h₀,h₁,hdist,hL⟩ := (finite_character_zeros_in_window χ t 1).mem_toFinset.mp hz
  exact ⟨h₀,h₁,hL,hdist⟩

end

section

open scoped BigOperators

/-- Sum the unit-window counts over the positive and negative heights.
The zero bin uses the real-part lower bound from GRH. -/
private theorem reciprocal_zero_sum_of_windows {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) (hT : 2 ≤ T) (Z : Finset ℂ)
    (hGRH : ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.re = 1 / 2)
    (hZ : ∀ z ∈ Z, 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T ∧ χ.LFunction z = 0)
    (A : ℝ) (hA : 0 ≤ A)
    (hwin : ∀ (t : ℝ) (S : Finset ℂ),
      (∀ z ∈ S, 0 < z.re ∧ z.re < 1 ∧ χ.LFunction z = 0 ∧ |z.im - t| ≤ 1) →
      (∑ z ∈ S, (analyticOrderNatAt χ.LFunction z : ℝ)) ≤ A * Real.log ((q : ℝ) * (2 + |t|))) :
    (∑ z ∈ Z, (analyticOrderNatAt χ.LFunction z : ℝ) / ‖z‖) ≤
      (12 * A) * (Real.log (2 * (q : ℝ) * T)) ^ 2 := by
  classical
  let w (z : ℂ) : ℝ := analyticOrderNatAt χ.LFunction z
  let level (z : ℂ) := ⌊|z.im|⌋₊
  let J := ⌊T⌋₊ + 1
  let shell (j : ℕ) := Z.filter (fun z => level z = j)
  let L := Real.log (2 * (q : ℝ) * T)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q from q.pos_of_neZero)
  have h2T : 2 * T ≤ 2 * (q : ℝ) * T := by
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hLhalf : 1 / 2 ≤ L := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show 2 ≤ 2 * (q : ℝ) * T by linarith)
    dsimp only [L]
    linarith only [hh, Real.log_two_gt_d9]
  have hL : 0 ≤ L := by linarith
  have hjT {j : ℕ} (hj : j < J) : (j : ℝ) ≤ T := by
    have hj' : j ≤ ⌊T⌋₊ := Nat.le_of_lt_succ hj
    exact (Nat.cast_le.mpr hj').trans (Nat.floor_le (by linarith))
  have hmaps (z : ℂ) (hz : z ∈ Z) : level z ∈ Finset.range J :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (hZ z hz).2.2.1))
  have hloc {j : ℕ} {z : ℂ} (hz : z ∈ shell j) :
      z ∈ Z ∧ (j : ℝ) ≤ |z.im| ∧ |z.im| < (j : ℝ) + 1 := by
    obtain ⟨hzZ, hj⟩ := Finset.mem_filter.mp hz
    rw [← hj]
    exact ⟨hzZ, Nat.floor_le (abs_nonneg _), Nat.lt_floor_add_one _⟩
  have hcount (j : ℕ) (hj : j < J) : (∑ z ∈ shell j, w z) ≤ 2 * A * L := by
    have hlog : Real.log ((q : ℝ) * (2 + (j : ℝ))) ≤ L := by
      apply Real.log_le_log (by positivity)
      calc
        _ ≤ (q : ℝ) * (2 * T) :=
          mul_le_mul_of_nonneg_left (by linarith [hjT hj]) (by positivity)
        _ = _ := by ring
    have hw (S : Finset ℂ) (t : ℝ) (ht : |t| = (j : ℝ))
        (hS : ∀ z ∈ S, z ∈ Z ∧ |z.im - t| ≤ 1) : (∑ z ∈ S, w z) ≤ A * L := by
      have hc := hwin t S (fun z hz =>
        let v := hZ z (hS z hz).1
        ⟨v.1, v.2.1, v.2.2.2, (hS z hz).2⟩)
      rw [ht] at hc
      exact hc.trans (mul_le_mul_of_nonneg_left hlog hA)
    have hp : (∑ z ∈ (shell j).filter (fun z => 0 ≤ z.im), w z) ≤ A * L := by
      apply hw _ j (abs_of_nonneg (Nat.cast_nonneg _))
      intro z hz
      obtain ⟨hs, him⟩ := Finset.mem_filter.mp hz
      obtain ⟨hzZ, hlo, hhi⟩ := hloc hs
      rw [abs_of_nonneg him] at hlo hhi
      exact ⟨hzZ, abs_le.mpr ⟨by linarith, by linarith⟩⟩
    have hn : (∑ z ∈ (shell j).filter (fun z => ¬0 ≤ z.im), w z) ≤ A * L := by
      apply hw _ (-(j : ℝ)) (by simp)
      intro z hz
      obtain ⟨hs, him⟩ := Finset.mem_filter.mp hz
      obtain ⟨hzZ, hlo, hhi⟩ := hloc hs
      rw [abs_of_neg (lt_of_not_ge him)] at hlo hhi
      exact ⟨hzZ, abs_le.mpr ⟨by linarith, by linarith⟩⟩
    rw [← Finset.sum_filter_add_sum_filter_not (shell j) (fun z => 0 ≤ z.im) w]
    linarith only [hp, hn]
  have hbin (j : ℕ) (hj : j < J) :
      (∑ z ∈ shell j, w z / ‖z‖) ≤ (4 * A * L) * ((j : ℝ) + 1)⁻¹ := by
    have hjpos : 0 < (j : ℝ) + 1 := by positivity
    have hi (z : ℂ) (hz : z ∈ shell j) : ‖z‖⁻¹ ≤ 2 / ((j : ℝ) + 1) := by
      obtain ⟨hzZ, hlo, _⟩ := hloc hz
      obtain ⟨hz0, hz1, _, hroot⟩ := hZ z hzZ
      have hre := Complex.abs_re_le_norm z
      rw [hGRH z hz0 hz1 hroot] at hre
      norm_num at hre
      have hnorm : 0 < ‖z‖ := by linarith
      rw [← one_div, div_le_div_iff₀ hnorm hjpos]
      rcases Nat.eq_zero_or_pos j with rfl | hj'
      · norm_num
        linarith
      · have hj1 : 1 ≤ (j : ℝ) := by exact_mod_cast hj'
        linarith only [hj1, hlo, Complex.abs_im_le_norm z]
    calc
      _ ≤ ∑ z ∈ shell j, w z * (2 / ((j : ℝ) + 1)) := by
        apply Finset.sum_le_sum
        intro z hz
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (hi z hz) (Nat.cast_nonneg _)
      _ = (∑ z ∈ shell j, w z) * (2 / ((j : ℝ) + 1)) := (Finset.sum_mul ..).symm
      _ ≤ (2 * A * L) * (2 / ((j : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right (hcount j hj) (by positivity)
      _ = _ := by ring
  have hJ : (J : ℝ) ≤ 2 * (q : ℝ) * T := by
    have hf := Nat.floor_le (show 0 ≤ T by linarith)
    dsimp only [J]
    rw [Nat.cast_add_one]
    linarith
  have hharm : (harmonic J : ℝ) ≤ 3 * L := by
    have hJpos : (0 : ℝ) < J := by dsimp [J]; positivity
    have hlJ : Real.log (J : ℝ) ≤ L := Real.log_le_log hJpos hJ
    linarith only [harmonic_le_one_add_log J, hlJ, hLhalf]
  calc
    _ = ∑ j ∈ Finset.range J, ∑ z ∈ shell j, w z / ‖z‖ :=
      (Finset.sum_fiberwise_of_maps_to hmaps (fun z => w z / ‖z‖)).symm
    _ ≤ ∑ j ∈ Finset.range J, (4 * A * L) * ((j : ℝ) + 1)⁻¹ :=
      Finset.sum_le_sum fun j hj => hbin j (Finset.mem_range.mp hj)
    _ = (4 * A * L) * (harmonic J : ℝ) := by
      rw [← Finset.mul_sum]
      simp [harmonic]
    _ ≤ (4 * A * L) * (3 * L) := mul_le_mul_of_nonneg_left hharm (by positivity)
    _ = _ := by dsimp only [L]; ring



/-- For primitive characters the same argument includes the zeros of the
Riemann zeta function at conductor one. -/
private theorem primitive_reciprocal_zero_sum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (T : ℝ) (hT : 2 ≤ T) (Z : Finset ℂ)
    (hGRH : ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.re = 1 / 2)
    (hZ : ∀ z ∈ Z, 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T ∧ χ.LFunction z = 0) :
    (∑ z ∈ Z, (analyticOrderNatAt χ.LFunction z : ℝ) / ‖z‖) ≤
      (120 / Real.log (23 / 22)) * (Real.log (2 * (q : ℝ) * T)) ^ 2 := by
  have h := reciprocal_zero_sum_of_windows χ T hT Z hGRH hZ
    (10 / Real.log (23 / 22)) (div_nonneg (by norm_num) (Real.log_nonneg (by norm_num)))
    (fun t S => primitive_character_window_count χ hprim t S hGRH)
  convert h using 1
  ring


end

section

open Complex MeasureTheory Filter ArithmeticFunction DirichletCharacter Finset

private noncomputable def perronLine (t : ℝ) : ℂ := 2 + (t : ℂ) * I

private theorem perronLine_re (t : ℝ) : (perronLine t).re = 2 := by simp [perronLine]

private noncomputable def perronKernelAt (s : ℂ) := 1 / (s * (s + 1))

private theorem perronKernel_integrable : Integrable (fun t : ℝ => perronKernelAt (perronLine t)) := by
  apply integrable_inv_one_add_sq.mono'
  · exact (by unfold perronKernelAt perronLine; fun_prop : Measurable _).aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  have h1 : ‖perronLine t‖ ^ 2 = 2 * 2 + t * t := by
    simpa [perronLine, Complex.normSq_apply] using Complex.sq_norm (perronLine t)
  have h2 : ‖perronLine t + 1‖ ^ 2 = (2+1) * (2+1) + t * t := by
    simpa [perronLine, Complex.normSq_apply] using Complex.sq_norm (perronLine t + 1)
  have hn : ‖perronLine t‖ ≤ ‖perronLine t + 1‖ := by nlinarith [norm_nonneg (perronLine t + 1)]
  rw [perronKernelAt, norm_div, norm_one, norm_mul, one_div]
  apply inv_anti₀ (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hn (norm_nonneg (perronLine t))]

private theorem smoothed_lseries_perron (a : ℕ → ℂ) (ha₀ : a 0 = 0) (ha : LSeriesSummable a 2)
    {x : ℝ} (hx : 0 < x) :
    mellinInv 2 (fun s => LSeries a s * (1 / (s * (s + 1)))) x =
      ∑' n : ℕ, a n * perronWeight (n * x) := by
  let F (n : ℕ) (t : ℝ) := ((x : ℂ) ^ (-perronLine t) * perronKernelAt (perronLine t)) *
      LSeries.term a (perronLine t) n
  let b (n : ℕ) := x ^ (-2 : ℝ) * ‖LSeries.term a 2 n‖
  have hnorm (n : ℕ) (t : ℝ) : ‖F n t‖ = b n * ‖perronKernelAt (perronLine t)‖ := by
    simp only [F, b, norm_mul, norm_cpow_eq_rpow_re_of_pos hx, neg_re, perronLine_re,
      LSeries.norm_term_eq, re_ofNat]
    ring
  have hmeas (n : ℕ) : Measurable (F n) := by
    simp only [F, perronKernelAt, perronLine, LSeries.term_def₀ ha₀]
    fun_prop
  have hi (n : ℕ) : Integrable (F n) := by
    apply (perronKernel_integrable.norm.const_mul (b n)).mono' (hmeas n).aestronglyMeasurable
    exact Eventually.of_forall fun t => (hnorm n t).le
  have hs : Summable (fun n => ∫ t : ℝ, ‖F n t‖) := by
    simp_rw [hnorm, integral_const_mul]
    exact (ha.norm.mul_left (x ^ (-2 : ℝ))).mul_right _
  have hsum (t : ℝ) : (∑' n, F n t) =
      (x : ℂ) ^ (-perronLine t) * (LSeries a (perronLine t) * perronKernelAt (perronLine t)) := by
    rw [show (∑' n, F n t) = _ from tsum_mul_left]
    change _ * LSeries a (perronLine t) = _
    ring
  have hsingle (n : ℕ) : (1 / (2 * Real.pi) : ℝ) • (∫ t : ℝ, F n t) =
      a n * perronWeight (n * x) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [F, ha₀]
    have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hfun (t : ℝ) : F n t = a n * ((((n : ℝ) * x : ℝ) : ℂ) ^ (-perronLine t) *
          perronKernelAt (perronLine t)) := by
      rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hn'.le hx.le]
      simp only [F, LSeries.term_def₀ ha₀, Complex.ofReal_natCast]
      ring
    rw [← perronWeight_inversion (mul_pos hn' hx)]
    unfold mellinInv
    simp_rw [hfun]
    rw [integral_const_mul]
    change _ • (a n * _) = a n * (_ • _)
    rw [mul_smul_comm]
    rfl
  have hsm := (hasSum_integral_of_summable_integral_norm hi hs).const_smul
    (1 / (2 * Real.pi) : ℝ)
  simp_rw [hsingle, hsum] at hsm
  exact hsm.tsum_eq.symm

private theorem twisted_smoothed_perron {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {X : ℝ} (hX : 0 < X) :
    mellinInv 2 (fun s : ℂ => (-deriv (LFunction χ) s / LFunction χ s) *
      (1 / (s * (s + 1)))) (1 / X) =
    ∑ n ∈ Icc 1 ⌊X⌋₊, χ (n : ZMod q) * (vonMangoldt n : ℂ) * (1 - (n : ℂ) / (X : ℂ)) := by
  let a (n : ℕ) := χ (n : ZMod q) * (vonMangoldt n : ℂ)
  have ha₀ : a 0 = 0 := by simp [a]
  have ha : LSeriesSummable a 2 := LSeriesSummable_twist_vonMangoldt χ (by norm_num)
  calc
    _ = mellinInv 2 (fun s => LSeries a s * (1 / (s * (s + 1)))) (1 / X) := by
      unfold mellinInv
      congr 1
      apply integral_congr_ae
      apply Eventually.of_forall
      intro t
      have hs : 1 < (((2 : ℝ) : ℂ) + (t : ℂ) * I).re := by norm_num
      dsimp only
      rw [deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs,
        ← LSeries_twist_vonMangoldt_eq χ hs]
      rfl
    _ = ∑' n : ℕ, a n * perronWeight ((n : ℝ) * (1 / X)) :=
      smoothed_lseries_perron a ha₀ ha (one_div_pos.mpr hX)
    _ = _ := by
      rw [tsum_eq_sum (s := Icc 1 ⌊X⌋₊) (fun n hn => ?_)]
      · apply sum_congr rfl
        intro n hn
        obtain ⟨hnp, hnf⟩ := mem_Icc.mp hn
        have hnℝ : 0 < (n : ℝ) := Nat.cast_pos.mpr hnp
        have hnx : (n : ℝ) ≤ X := (Nat.le_floor_iff hX.le).mp hnf
        have hm : (n : ℝ) * (1 / X) ∈ Set.Ioc (0 : ℝ) 1 := by
          rw [mul_one_div]
          exact ⟨div_pos hnℝ hX, (div_le_one hX).mpr hnx⟩
        rw [perronWeight, Set.indicator_of_mem hm]
        simp only [mul_one_div, Complex.ofReal_div, Complex.ofReal_natCast, a]
      · by_cases hz : n = 0
        · simp [hz, ha₀]
        · have hn' : ⌊X⌋₊ < n := by
            by_contra! h
            exact hn (mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hz, h⟩)
          have hx : X < (n : ℝ) := (Nat.floor_lt hX.le).mp hn'
          have hm : (n : ℝ) * (1 / X) ∉ Set.Ioc (0 : ℝ) 1 := by
            intro h
            rw [mul_one_div] at h
            exact (not_le.mpr hx) ((div_le_one hX).mp h.2)
          rw [perronWeight, Set.indicator_of_notMem hm, mul_zero]

end

section

open Filter Set
open scoped Topology

/-- Subtracting the pole of the logarithmic derivative at a zero of finite
order leaves a holomorphic germ. -/
private theorem logDeriv_principal_part {f : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ)
    (hord : analyticOrderAt f ρ ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧
      ∀ᶠ z in 𝓝[≠] ρ, logDeriv f z = (analyticOrderNatAt f ρ : ℂ) / (z - ρ) + g z := by
  let m := analyticOrderNatAt f ρ
  obtain ⟨u, hanu, hu, heq⟩ := hf.analyticOrderAt_ne_top.mp hord
  refine ⟨logDeriv u, hanu.deriv.div hanu hu, ?_⟩
  have hprod : f =ᶠ[𝓝 ρ] fun z => (z - ρ)^m * u z := heq
  filter_upwards [(logDeriv_congr_nhds hprod).filter_mono nhdsWithin_le_nhds,
    hanu.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    (hanu.continuousAt.eventually_ne hu).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz haz hn hne
  have hzρ : z - ρ ≠ 0 := sub_ne_zero.mpr hne
  rw [hz, logDeriv_fun_mul (f := fun v : ℂ => (v - ρ) ^ m) (g := u) z
    (pow_ne_zero _ hzρ) hn (by fun_prop) haz.differentiableAt,
    logDeriv_fun_pow (f := fun v : ℂ => v - ρ) (by fun_prop)]
  simp [logDeriv_apply, m, div_eq_mul_inv]


end

section

open scoped BigOperators
open ArithmeticFunction DirichletCharacter

/-- The triangularly weighted sum with unnormalised weight `X - n`. -/
private noncomputable def triangularTwist {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (X + 1),
    χ (n : ZMod q) * (vonMangoldt n : ℂ) * ((X : ℂ) - n)


/-- The unnormalised triangular sum is the cutoff times its Perron integral. -/
private theorem triangularTwist_eq_mellinInv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (X : ℕ) (hX : 0 < X) :
    triangularTwist χ X = (X : ℂ) * mellinInv 2 (fun s : ℂ =>
      (-deriv χ.LFunction s / χ.LFunction s) * (1 / (s * (s + 1)))) (1 / (X : ℝ)) := by
  have hc : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  rw [twisted_smoothed_perron χ (by exact_mod_cast hX), Nat.floor_natCast, Finset.mul_sum]
  let a (n : ℕ) : ℂ := χ (n : ZMod q) * (vonMangoldt n : ℂ)
  calc
    _ = ∑ n ∈ Finset.Icc 1 X, a n * ((X : ℂ) - n) := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sub _ (by omega)]
      simp [triangularTwist, a]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      simp only [a, Complex.ofReal_natCast]
      field_simp


end

section

/-- Choose a height within one unit of T, quantitatively separated from
every member of a given finite set of ordinates. -/
private theorem exists_height_avoiding (B : Finset ℝ) (T : ℝ) :
    ∃ t ∈ Set.Icc T (T + 1), ∀ b ∈ B, 1 / (3 * (B.card + 1 : ℝ)) ≤ |t - b| := by
  classical
  let N : ℝ := B.card + 1
  have hN : 0 < N := by dsimp [N]; positivity
  let grid (j : Fin (B.card + 1)) : ℝ := T + (j.val : ℝ) / N
  have hI (j) : grid j ∈ Set.Icc T (T + 1) := by
    constructor
    · exact le_add_of_nonneg_right (div_nonneg (by positivity) hN.le)
    · change T + (j.val : ℝ) / N ≤ T + 1
      apply add_le_add_right
      apply (div_le_one hN).2
      dsimp [N]
      exact_mod_cast j.isLt.le
  by_contra! hall
  have hchoice (j) : ∃ b : B, |grid j - (b : ℝ)| < 1 / (3 * N) := by
    obtain ⟨b, hb, h⟩ := hall (grid j) (hI j)
    exact ⟨⟨b, hb⟩, h⟩
  choose f hf using hchoice
  have hinj : Function.Injective f := by
    intro i j hij
    have ha := (abs_lt.mp (hf i))
    have hb := (abs_lt.mp (hf j))
    rw [hij] at ha
    have hdiff : |grid i - grid j| < 1 / N := by
      have hthird : (3 : ℝ) * (1 / (3 * N)) = 1 / N := by field_simp
      rw [abs_lt]
      constructor <;> linarith [one_div_pos.mpr hN]
    have hid : grid i - grid j = ((i.val : ℝ) - j.val) / N := by simp [grid]; ring
    rw [hid, abs_div, abs_of_pos hN, div_lt_div_iff_of_pos_right hN, abs_lt] at hdiff
    have hi : i.val < j.val + 1 := by exact_mod_cast (show (i.val : ℝ) < j.val + 1 by linarith [hdiff.2])
    have hj : j.val < i.val + 1 := by exact_mod_cast (show (j.val : ℝ) < i.val + 1 by linarith [hdiff.1])
    exact Fin.ext (by omega)
  have hcard := Fintype.card_le_of_injective f hinj
  simp at hcard

end

section

open scoped BigOperators Topology
open Filter Metric

/-- Divide out the prescribed multiplicities of the zeros in the inner
closed disk. The corrected quotient extends analytically across every
removed zero, remains analytic on the outer disk, and has no inner zeros. -/
private theorem remove_prescribed_disk_zeros (f : ℂ → ℂ) (c : ℂ) (r R : ℝ)
    (hr : 0 ≤ r) (hrR : r ≤ R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hc : f c ≠ 0) (Z : Finset ℂ)
    (hZ : ∀ z : ℂ, z ∈ Z ↔ z ∈ closedBall c r ∧ f z = 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall c R) ∧
      (∀ z ∈ closedBall c r, g z ≠ 0) ∧
      ∀ w, f w = (∏ z ∈ Z, (w - z) ^ analyticOrderNatAt f z) * g w := by
  classical
  have hR := hr.trans hrR
  have hcenter : c ∈ closedBall c R := by simpa using hR
  have hfinite := (hf.exists_analyticOrderAt_ne_top_iff_forall (isConnected_closedBall hR)).mp
    ⟨⟨c, hcenter⟩, by rw [(hf c hcenter).analyticOrderAt_eq_zero.mpr hc]; simp⟩
  let m (z : ℂ) := analyticOrderNatAt f z
  let P (w : ℂ) := ∏ z ∈ Z, (w - z) ^ m z
  let Q (z w : ℂ) := ∏ a ∈ Z.erase z, (w - a) ^ m a
  have hsplit {z : ℂ} (hz : z ∈ Z) (w : ℂ) : P w = (w - z) ^ m z * Q z w :=
    (Z.mul_prod_erase (fun a => (w - a) ^ m a) hz).symm
  have hprod {F : Finset ℂ} {w : ℂ} (hw : w ∉ F) :
      (∏ a ∈ F, (w - a) ^ m a) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    exact pow_ne_zero _ (sub_ne_zero.mpr (fun he => hw (he ▸ ha)))
  have hprodAn (F : Finset ℂ) (w : ℂ) : AnalyticAt ℂ (fun b => ∏ a ∈ F, (b - a) ^ m a) w := by
    fun_prop
  have hlocal (z : ℂ) (hz : z ∈ Z) :
      ∃ u : ℂ → ℂ, AnalyticAt ℂ u z ∧ u z ≠ 0 ∧
        ∀ᶠ w in 𝓝 z, f w = (w - z) ^ m z * u w := by
    have hzR := closedBall_subset_closedBall hrR ((hZ z).mp hz).1
    exact (hf z hzR).analyticOrderAt_ne_top.mp (hfinite ⟨z, hzR⟩)
  choose u hu hune hfac using hlocal
  let g (w : ℂ) := if hw : w ∈ Z then u w hw w / Q w w else f w / P w
  refine ⟨g, ?_, ?_, ?_⟩
  · intro z hzR
    by_cases hz : z ∈ Z
    · have hQ : Q z z ≠ 0 := hprod (Finset.notMem_erase _ _)
      apply ((hu z hz).div (hprodAn (Z.erase z) z) hQ).congr
      have havoid : ∀ᶠ w in 𝓝 z, w ∉ Z.erase z :=
        (Z.erase z).isClosed.isOpen_compl.mem_nhds (Finset.notMem_erase _ _)
      filter_upwards [havoid, hfac z hz] with w hw hfw
      change u z hz w / Q z w = g w
      by_cases hwz : w = z
      · subst w
        simp [g, hz]
      · have hwZ : w ∉ Z := fun h => hw (Finset.mem_erase.mpr ⟨hwz, h⟩)
        have hpow := pow_ne_zero (m z) (sub_ne_zero.mpr hwz)
        simp only [g, dite_eq_right hwZ, hfw, hsplit hz w]
        field_simp
    · apply ((hf z hzR).div (hprodAn Z z) (hprod hz)).congr
      filter_upwards [Z.isClosed.isOpen_compl.mem_nhds (show z ∉ Z from hz)] with w hw
      change w ∉ Z at hw
      simp [g, hw, P]
  · intro z hzr
    by_cases hz : z ∈ Z
    · simp only [g, dite_eq_left hz]
      exact div_ne_zero (hune z hz) (hprod (Finset.notMem_erase _ _))
    · simp only [g, dite_eq_right hz]
      exact div_ne_zero (fun he => hz ((hZ z).mpr ⟨hzr, he⟩)) (hprod hz)
  · intro w
    change f w = P w * g w
    by_cases hw : w ∈ Z
    · have h := (hfac w hw).self_of_nhds
      rw [h, hsplit hw w]
      simp only [g, dite_eq_left hw]
      have hQ : Q w w ≠ 0 := hprod (Finset.notMem_erase _ _)
      field_simp
    · simp only [g, dite_eq_right hw]
      have hP : P w ≠ 0 := hprod hw
      field_simp

/-- A finite list of all inner zeros and its exact analytic factorization
exist on every nested pair of closed disks with a nonzero central value. -/
private theorem remove_disk_zeros (f : ℂ → ℂ) (c : ℂ) (r R : ℝ)
    (hr : 0 ≤ r) (hrR : r ≤ R) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0) :
    ∃ (Z : Finset ℂ) (g : ℂ → ℂ), (∀ z : ℂ, z ∈ Z ↔ z ∈ closedBall c r ∧ f z = 0) ∧
      AnalyticOnNhd ℂ g (closedBall c R) ∧ (∀ z ∈ closedBall c r, g z ≠ 0) ∧
      ∀ w, f w = (∏ z ∈ Z, (w - z) ^ analyticOrderNatAt f z) * g w := by
  classical
  have hrAn : AnalyticOnNhd ℂ f (closedBall c r) := hf.mono (closedBall_subset_closedBall hrR)
  have hd := hrAn.preimage_zero_mem_codiscreteWithin hc (mem_closedBall_self hr)
    (isConnected_closedBall hr)
  have hfinite : {z ∈ closedBall c r | f z = 0}.Finite :=
    ((isCompact_closedBall c r).finite_sdiff_of_mem_codiscreteWithin hd).subset
      (fun z hz => ⟨hz.1, by simp [hz.2]⟩)
  let Z := hfinite.toFinset
  have hZ (z : ℂ) : z ∈ Z ↔ z ∈ closedBall c r ∧ f z = 0 := hfinite.mem_toFinset
  obtain ⟨g, han, hnz, hfac⟩ := remove_prescribed_disk_zeros f c r R hr hrR hf hc Z hZ
  exact ⟨Z, g, hZ, han, hnz, hfac⟩

end

section

open Complex Metric Set MeromorphicOn

private theorem logDeriv_bound_nonvanishing_disk (f : ℂ → ℂ) {M : ℝ} (hM : 0 < M)
    (hf : DifferentiableOn ℂ f (ball 0 (23 / 8)))
    (hn : ∀ z ∈ ball (0 : ℂ) (23 / 8), f z ≠ 0)
    (hbound : ∀ z ∈ ball (0 : ℂ) (23 / 8), ‖f z‖ ≤ ‖f 0‖ * Real.exp M)
    {z : ℂ} (hz : ‖z‖ ≤ 11 / 4) :
    ‖logDeriv f z‖ ≤ 1440 * M := by
  have h0 : (0 : ℂ) ∈ ball 0 (23 / 8) := mem_ball_self (by norm_num)
  have hh : DifferentiableOn ℂ (logDeriv f) (ball 0 (23 / 8)) :=
    (hf.deriv isOpen_ball).div hf hn
  obtain ⟨g, hg₀, hg⟩ := hh.isExactOn_ball.with_val_at (0 : ℂ) 0
  have hgd : DifferentiableOn ℂ g (ball 0 (23 / 8)) :=
    fun x hx => (hg x hx).differentiableAt.differentiableWithinAt
  have heg : DifferentiableOn ℂ (fun x => Complex.exp (g x)) (ball 0 (23 / 8)) :=
    fun x hx => (hg x hx).cexp.differentiableAt.differentiableWithinAt
  have hrel := (logDeriv_eqOn_iff hf heg isOpen_ball (convex_ball _ _).isPreconnected
    (fun x _ => Complex.exp_ne_zero (g x)) hn).mp
  obtain ⟨k, hk, hfac⟩ := hrel (by
    intro x hx
    rw [logDeriv_apply (fun x => Complex.exp (g x)), (hg x hx).cexp.deriv]
    field_simp)
  have hk₀ : f 0 = k := by simpa [hg₀] using hfac h0
  have hre (w : ℂ) (hw : w ∈ ball 0 (23 / 8)) : (g w).re ≤ M := by
    apply Real.exp_le_exp.mp
    have heq : f w = f 0 * Complex.exp (g w) := by simpa [hk₀] using hfac hw
    have h := hbound w hw
    rw [heq, norm_mul, Complex.norm_exp] at h
    exact (mul_le_mul_iff_right₀ (norm_pos_iff.mpr (hn 0 h0))).mp h
  have hgeo (w : ℂ) (hw : w ∈ closedBall z (1 / 16)) : ‖w‖ ≤ 45 / 16 := by
    have hs : ‖w - z‖ ≤ 1 / 16 := by simpa [mem_closedBall, dist_eq_norm] using hw
    linarith [norm_le_norm_sub_add w z]
  have hsub : closedBall z (1 / 16) ⊆ ball (0 : ℂ) (23 / 8) := by
    intro w hw
    rw [mem_ball_zero_iff]
    linarith [hgeo w hw]
  have hC : ∀ w ∈ sphere z (1 / 16), ‖g w‖ ≤ 90 * M := by
    intro w hw
    have hb := sphere_subset_closedBall hw
    have hle := hgeo w hb
    have hd : 0 < 23 / 8 - ‖w‖ := by linarith
    apply (borelCaratheodory_zero hM hgd (fun w hw => hre w hw) (by norm_num) (hsub hb) hg₀).trans
    apply (div_le_iff₀ hd).2
    nlinarith [mul_nonneg hM.le (sub_nonneg.mpr hle)]
  have hzb : z ∈ ball (0 : ℂ) (23 / 8) := mem_ball_zero_iff.mpr (by linarith)
  rw [← (hg z hzb).deriv]
  apply (Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ) < 1/16)
    (hgd.diffContOnCl_ball hsub) hC).trans
  linarith

private theorem logDeriv_bound_after_removing_zeros (f g : ℂ → ℂ) (Z : Finset ℂ) (m : ℂ → ℕ)
    (hroots : ∀ ρ ∈ Z, ‖ρ‖ ≤ 23 / 8)
    (hfac : ∀ w ∈ closedBall (0 : ℂ) (47 / 16),
      f w = (∏ ρ ∈ Z, (w - ρ) ^ m ρ) * g w)
    (hg : DiffContOnCl ℂ g (ball 0 (47 / 16)))
    (hgn : ∀ w ∈ ball (0 : ℂ) (23 / 8), g w ≠ 0)
    {M : ℝ} (hM : 0 < M)
    (hfbound : ∀ w ∈ sphere (0 : ℂ) (47 / 16), ‖f w‖ ≤ ‖f 0‖ * Real.exp M)
    {z : ℂ} (hz : ‖z‖ ≤ 11 / 4) (hzZ : z ∉ Z) :
    ‖logDeriv f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)‖ ≤
      1440 * (M + (∑ ρ ∈ Z, m ρ : ℕ) * Real.log 48) := by
  classical
  let P : ℂ → ℂ := fun w => ∏ ρ ∈ Z, (w - ρ) ^ m ρ
  let N := ∑ ρ ∈ Z, m ρ
  have hcenter : ‖f 0‖ ≤ (3 : ℝ) ^ N * ‖g 0‖ := by
    rw [hfac 0 (mem_closedBall_self (by norm_num)), norm_mul, norm_prod,
      ← Finset.prod_pow_eq_pow_sum Z m (3 : ℝ)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro ρ hρ
    rw [norm_pow, zero_sub, norm_neg]
    exact pow_le_pow_left₀ (norm_nonneg _) (by linarith [hroots ρ hρ]) _
  have hboundary (w : ℂ) (hw : w ∈ sphere 0 (47 / 16)) :
      ‖g w‖ ≤ ‖g 0‖ * Real.exp (M + (N : ℝ) * Real.log 48) := by
    have hnw : ‖w‖ = 47/16 := by simpa [mem_sphere, dist_zero_right] using hw
    have hP : (1/16 : ℝ) ^ N ≤ ‖P w‖ := by
      rw [show ‖P w‖ = _ from norm_prod .., ← Finset.prod_pow_eq_pow_sum Z m (1/16 : ℝ)]
      apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
      intro ρ hρ
      rw [norm_pow]
      apply pow_le_pow_left₀ (by norm_num)
      linarith [norm_le_norm_sub_add w ρ, hroots ρ hρ]
    have hU := hfbound w hw
    rw [hfac w (sphere_subset_closedBall hw), norm_mul] at hU
    have hval : (1/16 : ℝ) ^ N * ‖g w‖ ≤ (3 : ℝ) ^ N * ‖g 0‖ * Real.exp M :=
      (mul_le_mul_of_nonneg_right hP (norm_nonneg _)).trans
        (hU.trans (mul_le_mul_of_nonneg_right hcenter (Real.exp_pos M).le))
    rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 48)]
    apply (mul_le_mul_iff_right₀ (show 0 < (1 / 16 : ℝ) ^ N by positivity)).mp
    calc
      _ ≤ _ := hval
      _ = _ := by
        have hk : ((1/16 : ℝ) ^ N) * (48 : ℝ) ^ N = 3 ^ N := by rw [← mul_pow]; norm_num
        linear_combination -(‖g 0‖ * Real.exp M) * hk
  have hUpos : 0 < M + (N : ℝ) * Real.log 48 := by
    exact add_pos_of_pos_of_nonneg hM (mul_nonneg (Nat.cast_nonneg N) (Real.log_nonneg (by norm_num)))
  have hsubset : ball (0 : ℂ) (23 / 8) ⊆ ball 0 (47 / 16) := ball_subset_ball (by norm_num)
  have hregular := logDeriv_bound_nonvanishing_disk g hUpos (hg.1.mono hsubset) hgn
    (fun w hw => norm_le_of_forall_mem_frontier_norm_le isBounded_ball hg
      (fun v hv => hboundary v (by rwa [frontier_ball (0 : ℂ) (by norm_num : (47 / 16 : ℝ) ≠ 0)] at hv))
      (subset_closure (hsubset hw))) hz
  have hzin : z ∈ ball (0 : ℂ) (23/8) := mem_ball_zero_iff.mpr (by linarith)
  have heq : f =ᶠ[nhds z] fun w => P w * g w := by
    filter_upwards [isOpen_ball.mem_nhds (hsubset hzin)] with w hw
    exact hfac w (ball_subset_closedBall hw)
  have hpz (ρ : ℂ) (hρ : ρ ∈ Z) : z - ρ ≠ 0 := sub_ne_zero.mpr (fun e => hzZ (e ▸ hρ))
  have hPdiff : DifferentiableAt ℂ P z := by dsimp [P]; fun_prop
  have hPz : P z ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun ρ hρ => pow_ne_zero _ (hpz ρ hρ))
  have hPder : logDeriv P z = ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) := by
    rw [show logDeriv P z = _ from logDeriv_fun_prod
      (f := fun ρ (w : ℂ) => (w - ρ) ^ m ρ) (fun ρ hρ => pow_ne_zero _ (hpz ρ hρ))
      (fun _ _ => by fun_prop)]
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [logDeriv_fun_pow (f := fun w : ℂ => w - ρ) (by fun_prop)]
    simp [logDeriv_apply, div_eq_mul_inv]
  rw [(logDeriv_congr_nhds heq).eq_of_nhds,
    logDeriv_fun_mul z hPz (hgn z hzin) hPdiff
      (hg.1.differentiableAt (isOpen_ball.mem_nhds (hsubset hzin))), hPder, add_sub_cancel_left]
  exact hregular

private theorem inner_disk_multiplicity_bound {f : ℂ → ℂ} (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, ‖ρ‖ ≤ 23 / 8)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 (47 / 16))) (hf₀ : f 0 ≠ 0)
    {B : ℝ} (hB : 1 ≤ B) (hboundary : ∀ z ∈ sphere 0 (47 / 16), ‖f z‖ ≤ B) :
    ((∑ ρ ∈ Z, analyticOrderNatAt f ρ : ℕ) : ℝ) ≤
      Real.log (B / ‖f 0‖) / Real.log (47 / 46) := by
  classical
  let K := closedBall (0 : ℂ) (23 / 8)
  let d := MeromorphicOn.divisor f K
  have ha : AnalyticOnNhd ℂ f K := hf.mono (closedBall_subset_closedBall (by norm_num))
  have hs := d.finiteSupport (isCompact_closedBall 0 (23 / 8))
  let U := Z ∪ hs.toFinset
  have hu : Function.support d ⊆ (U : Set ℂ) :=
    fun _ hi => Finset.mem_union_right _ (hs.mem_toFinset.mpr hi)
  have hcount : ((∑ ρ ∈ Z, analyticOrderNatAt f ρ : ℕ) : ℤ) ≤ ∑ᶠ w, d w := by
    rw [finsum_eq_sum_of_support_subset _ hu, Nat.cast_sum]
    calc
      _ = ∑ w ∈ Z, d w := by
        apply Finset.sum_congr rfl
        intro w hw
        change _ = MeromorphicOn.divisor f K w
        rw [ha.divisor_apply (mem_closedBall_zero_iff.mpr (hZ w hw))]
        unfold analyticOrderNatAt
        cases h : analyticOrderAt f w using ENat.recTopCoe <;> simp
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun w _ _ => ha.divisor_nonneg w)
  have hJ := AnalyticOnNhd.sum_divisor_le (c := (0 : ℂ)) (r := (23/8 : ℝ))
    (R := (47/16 : ℝ)) (M := B) (by norm_num) (by norm_num) hB
    (by simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 47 / 16)] using hf) hf₀
    (by simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 47 / 16)] using hboundary)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 23 / 8),
    show (47 / 16 : ℝ) / (23 / 8) = 47 / 46 by norm_num] at hJ
  exact le_trans (by exact_mod_cast hcount) hJ

private theorem local_logDeriv_bound_of_distance (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 (47/16))) (hf₀ : f 0 ≠ 0)
    {B D δ : ℝ} (hB : 1 ≤ B) (hD : 0 < D) (hδ : 0 < δ)
    (hboundary : ∀ w ∈ sphere 0 (47 / 16), ‖f w‖ ≤ B)
    (hlog : Real.log (B / ‖f 0‖) ≤ D)
    {z : ℂ} (hz : ‖z‖ ≤ 11/4)
    (hsep : ∀ ρ ∈ closedBall (0 : ℂ) (23/8), f ρ = 0 → δ ≤ ‖z-ρ‖) :
    ‖logDeriv f z‖ ≤ (1440 + (1440 * Real.log 48 + 1/δ) / Real.log (47/46)) * D := by
  classical
  obtain ⟨Z, g, hZ, hg, hgn, hfac⟩ :=
    remove_disk_zeros f 0 (23 / 8) (47 / 16) (by norm_num) (by norm_num) hf hf₀
  let N := ∑ ρ ∈ Z, analyticOrderNatAt f ρ
  have hr (ρ) (hρ : ρ ∈ Z) := (hZ ρ).mp hρ
  have hd (ρ) (hρ : ρ ∈ Z) : δ ≤ ‖z-ρ‖ := hsep ρ (hr ρ hρ).1 (hr ρ hρ).2
  have hroot (ρ) (hρ : ρ ∈ Z) : ‖ρ‖ ≤ 23 / 8 := mem_closedBall_zero_iff.mp (hr ρ hρ).1
  have hfrel (w : ℂ) (hw : w ∈ sphere 0 (47/16)) : ‖f w‖ ≤ ‖f 0‖ * Real.exp D := by
    apply (hboundary w hw).trans
    have hn := norm_pos_iff.mpr hf₀
    have h := (Real.log_le_iff_le_exp (div_pos (by linarith) hn)).mp hlog
    simpa only [mul_comm] using (div_le_iff₀ hn).mp h
  have hzZ : z ∉ Z := by
    intro hzZ
    have := hd z hzZ
    simp at this
    linarith
  have hlogder := logDeriv_bound_after_removing_zeros f g Z (analyticOrderNatAt f)
    hroot (fun w _ => hfac w)
    (hg.differentiableOn.diffContOnCl_ball Set.Subset.rfl)
    (fun w hw => hgn w (ball_subset_closedBall hw)) hD hfrel hz hzZ
  have hN : (N : ℝ) ≤ D / Real.log (47/46) :=
    (inner_disk_multiplicity_bound Z hroot hf hf₀ hB hboundary).trans
      (div_le_div_of_nonneg_right hlog (Real.log_nonneg (by norm_num)))
  have hsum : ‖∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (z-ρ)‖ ≤ (N : ℝ) * (1/δ) := by
    apply (norm_sum_le ..).trans
    rw [show (N : ℝ) = ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ) by simp [N], Finset.sum_mul]
    apply Finset.sum_le_sum
    intro ρ hρ
    rw [norm_div, Complex.norm_natCast, mul_one_div]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (hd ρ hρ)
  have hK : 0 ≤ 1440 * Real.log 48 + 1/δ := by positivity
  calc
    _ ≤ _ := norm_le_norm_sub_add (logDeriv f z) (∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (z-ρ))
    _ ≤ 1440 * (D + (N : ℝ) * Real.log 48) + N * (1/δ) := add_le_add hlogder hsum
    _ = 1440 * D + (N : ℝ) * (1440 * Real.log 48 + 1 / δ) := by ring
    _ ≤ 1440 * D + (D / Real.log (47/46)) * (1440 * Real.log 48 + 1 / δ) := by gcongr
    _ = _ := by ring

end

section

open scoped BigOperators Interval
open ArithmeticFunction

/-- A unit step recovers every von Mangoldt coefficient through the cutoff
with its exact weight. -/
private theorem triangularTwist_unit_difference {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℕ) :
    triangularTwist χ (X+1) - triangularTwist χ X =
      ∑ n ∈ Finset.range (X+1), χ (n : ZMod q) * (vonMangoldt n : ℂ) := by
  unfold triangularTwist
  rw [Finset.sum_range_succ]
  simp only [sub_self, mul_zero, add_zero, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  push_cast
  ring

/-- The difference kernel is bounded by the average of the absolute values
of the complex powers on the intervening unit interval. -/
private noncomputable def unitPerronKernel (x : ℝ) (s : ℂ) : ℂ :=
  (((x + 1 : ℝ) : ℂ) ^ (s + 1) - (x : ℂ) ^ (s + 1)) / (s * (s + 1))

private theorem unitPerronKernel_norm {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖unitPerronKernel x s‖ ≤ (x + 1) ^ s.re / ‖s‖ := by
  have h := integral_cpow (a := x) (b := x+1) (r := s) (Or.inl (by linarith))
  have he : unitPerronKernel x s = (∫ y : ℝ in x..x+1, (y : ℂ) ^ s) / s := by
    rw [h]
    unfold unitPerronKernel
    rw [div_div, mul_comm s (s+1)]
  have hb : ‖∫ y : ℝ in x..x+1, (y : ℂ) ^ s‖ ≤ (x+1) ^ s.re := by
    calc
      _ ≤ (x+1) ^ s.re * |(x+1)-x| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro y hy
        rw [Set.uIoc_of_le (by linarith)] at hy
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (hx.trans hy.1)]
        exact Real.rpow_le_rpow (hx.trans hy.1).le hy.2 hs
      _ = _ := by simp
  rw [he, norm_div]
  exact div_le_div_of_nonneg_right hb (norm_nonneg _)

/-- When the principal pole is crossed, the unit difference contributes
the midpoint of the two cutoffs. -/
private theorem unitPerronKernel_one (x : ℝ) : unitPerronKernel x 1 = (x : ℂ) + 1 / 2 := by
  unfold unitPerronKernel
  norm_num [Complex.cpow_ofNat_mul, show (1+1:ℂ) = (2:ℕ) by norm_num]
  ring

/-- Under the zero-line hypothesis the sum of the residues of the unit
difference kernel has the required square-logarithmic bound. -/
private theorem unitPerronKernel_zero_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) {x T : ℝ} (hx : 0 < x) (hT : 2 ≤ T) (Z : Finset ℂ)
    (hGRH : ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.re = 1/2)
    (hZ : ∀ z ∈ Z, 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T ∧ χ.LFunction z = 0) :
    ‖∑ z ∈ Z, (analyticOrderNatAt χ.LFunction z : ℂ) * unitPerronKernel x z‖ ≤
      Real.sqrt (x+1) * ((120 / Real.log (23/22)) * (Real.log (2*q*T))^2) := by
  have H := primitive_reciprocal_zero_sum χ hprim T hT Z hGRH hZ
  calc
    _ ≤ ∑ z ∈ Z, ‖(analyticOrderNatAt χ.LFunction z : ℂ) * unitPerronKernel x z‖ :=
      norm_sum_le _ _
    _ ≤ ∑ z ∈ Z, Real.sqrt (x+1) * ((analyticOrderNatAt χ.LFunction z : ℝ) / ‖z‖) := by
      apply Finset.sum_le_sum
      intro z hz
      obtain ⟨h₀,h₁,_,hL⟩ := hZ z hz
      have h := unitPerronKernel_norm hx h₀.le
      rw [hGRH z h₀ h₁ hL, ← Real.sqrt_eq_rpow] at h
      rw [norm_mul, Complex.norm_natCast]
      calc
        _ ≤ (analyticOrderNatAt χ.LFunction z : ℝ) * (Real.sqrt (x+1) / ‖z‖) :=
          mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
        _ = _ := by ring
    _ = _ := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left H (Real.sqrt_nonneg _)

end

section

open scoped BigOperators

/-- There is a horizontal contour in every unit height interval whose
distance from every nontrivial zero ordinate has an explicit lower bound. -/
private theorem primitive_good_height {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (T : ℝ)
    (hGRH : ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.re = 1/2) :
    ∃ t ∈ Set.Icc T (T+1), ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 →
      1 / (3 * ((10 / Real.log (23/22)) * Real.log ((q : ℝ) * (2 + |T + 1/2|)) + 1)) ≤
        |t - z.im| := by
  classical
  let Z := (finite_character_zeros_in_window χ (T+1/2) 1).toFinset
  let B := Z.image Complex.im
  let W := (10 / Real.log (23/22)) * Real.log ((q : ℝ) * (2 + |T+1/2|))
  have hcard : (B.card : ℝ) ≤ W := calc
    _ ≤ (Z.card : ℝ) := by exact_mod_cast Finset.card_image_le
    _ = ∑ _z ∈ Z, (1 : ℝ) := by simp
    _ ≤ ∑ z ∈ Z, (analyticOrderNatAt χ.LFunction z : ℝ) := by
      apply Finset.sum_le_sum
      intro z hz
      obtain ⟨_,h₁,_,hL⟩ := (finite_character_zeros_in_window χ (T+1/2) 1).mem_toFinset.mp hz
      have hne : z ≠ 1 := by intro he; simp [he] at h₁
      exact_mod_cast positive_multiplicity_of_character_zero χ hne hL
    _ ≤ W := primitive_character_full_window_count χ hprim _ hGRH
  obtain ⟨t, ht, hsep⟩ := exists_height_avoiding B T
  refine ⟨t, ht, ?_⟩
  intro z h₀ h₁ hL
  have hc : 0 ≤ (B.card : ℝ) := Nat.cast_nonneg _
  have hmono : 1 / (3 * (W+1)) ≤ 1 / (3 * (B.card+1 : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  apply hmono.trans
  by_cases hwin : |z.im - (T+1/2)| ≤ 1
  · apply hsep
    apply Finset.mem_image.mpr
    exact ⟨z,(finite_character_zeros_in_window χ (T+1/2) 1).mem_toFinset.mpr
      ⟨h₀,h₁,hwin,hL⟩,rfl⟩
  · have hhalf : 1 / (3 * (B.card + 1 : ℝ)) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    apply hhalf.trans
    rw [abs_le] at hwin
    rcases lt_or_ge (t-z.im) 0 with h | h
    · rw [abs_of_neg h]
      by_contra! hn
      exact hwin ⟨by linarith [ht.1],by linarith [ht.2]⟩
    · rw [abs_of_nonneg h]
      by_contra! hn
      exact hwin ⟨by linarith [ht.1],by linarith [ht.2]⟩

end

section

open Complex Set Filter MeasureTheory
open scoped BigOperators Topology Interval

/-- Counterclockwise integration over the four directed edges of a rectangle. -/
private noncomputable def rectangleBoundary (a b u v : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ x in a..b, f (x + u * I)) - (∫ x in a..b, f (x + v * I)) +
  I * (∫ y in u..v, f (b + y * I)) - I * (∫ y in u..v, f (a + y * I))

private theorem integral_linear_pole_edge (γ : ℝ → ℂ) (V ρ k : ℂ) (a b : ℝ)
    (hγ : ∀ x, HasDerivAt γ V x) (hk : k ≠ 0)
    (hcut : ∀ x ∈ Set.uIcc a b, k * (γ x - ρ) ∈ slitPlane) :
    V * (∫ x in a..b, (γ x - ρ)⁻¹) =
      Complex.log (k * (γ b - ρ)) - Complex.log (k * (γ a - ρ)) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have h := (((hγ x).sub_const ρ).const_mul k).clog_real (hcut x hx)
    simpa only [mul_div_mul_left _ _ hk, div_eq_mul_inv] using h
  · apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.mul
    have hγc : ContinuousOn γ (Set.uIcc a b) := fun x _ => (hγ x).continuousAt.continuousWithinAt
    exact (hγc.sub continuousOn_const).inv₀
      (fun x hx => (mul_ne_zero_iff.mp (slitPlane_ne_zero (hcut x hx))).2)

private theorem log_neg_above {z : ℂ} (hz : 0 < z.im) :
    Complex.log (-z) = Complex.log z - Real.pi * I := by
  simp only [Complex.log, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos hz, ofReal_sub]
  ring

private theorem log_neg_below {z : ℂ} (hz : z.im < 0) :
    Complex.log (-z) = Complex.log z + Real.pi * I := by
  simp only [Complex.log, norm_neg, arg_neg_eq_arg_add_pi_of_im_neg hz, ofReal_add]
  ring

/-- The logarithmic kernel at any interior point has winding number one. -/
private theorem rectangleBoundary_inv_sub (a b u v : ℝ) (ρ : ℂ)
    (ha : a < ρ.re) (hb : ρ.re < b) (hu : u < ρ.im) (hv : ρ.im < v) :
    rectangleBoundary a b u v (fun z => (z - ρ)⁻¹) = 2 * Real.pi * I := by
  let H (y x : ℝ) := (x:ℂ) + (y:ℂ) * I
  let V (x y : ℝ) := (x:ℂ) + (y:ℂ) * I
  have hHd (y x : ℝ) : HasDerivAt (H y) 1 x := by
    simpa [H] using ((hasDerivAt_id x).ofReal_comp.add_const ((y:ℂ) * I))
  have hVd (x y : ℝ) : HasDerivAt (V x) I y := by
    simpa [V] using (((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (x : ℂ))
  have below (x : ℝ) : (H u x - ρ).im < 0 := by simpa [H] using sub_neg.mpr hu
  have above (x : ℝ) : 0 < (H v x - ρ).im := by simpa [H] using sub_pos.mpr hv
  have hbottom := integral_linear_pole_edge (H u) 1 ρ 1 a b (hHd u) one_ne_zero
    (fun x _ => by rw [one_mul]; exact mem_slitPlane_iff.mpr (.inr (below x).ne))
  have htop := integral_linear_pole_edge (H v) 1 ρ 1 a b (hHd v) one_ne_zero
    (fun x _ => by rw [one_mul]; exact mem_slitPlane_iff.mpr (.inr (above x).ne'))
  have hright := integral_linear_pole_edge (V b) I ρ 1 u v (hVd b) one_ne_zero
    (fun y _ => by rw [one_mul]; exact mem_slitPlane_iff.mpr (.inl (by simpa [V] using sub_pos.mpr hb)))
  have hleft := integral_linear_pole_edge (V a) I ρ (-1) u v (hVd a) (by norm_num)
    (fun y _ => by
      rw [neg_one_mul]
      exact mem_slitPlane_iff.mpr (.inl (by simp [V]; linarith)))
  dsimp only [H,V] at *
  simp only [one_mul, neg_one_mul] at hbottom htop hleft hright
  rw [rectangleBoundary, hbottom, htop, hright, hleft,
    log_neg_above (above a), log_neg_below (below a)]
  ring

private theorem rect_principal_edge (a b : ℝ) (γ : ℝ → ℂ) (f G : ℂ → ℂ)
    (P : Finset ℂ) (r : ℂ → ℂ) (hγ : Continuous γ)
    (hG : ContinuousOn (fun x => G (γ x)) (Set.uIcc a b))
    (havoid : ∀ x ∈ Set.uIcc a b, ∀ ρ ∈ P, γ x ≠ ρ)
    (hdecomp : ∀ x ∈ Set.uIcc a b, f (γ x) =
      G (γ x) + ∑ ρ ∈ P, r ρ * (γ x - ρ)⁻¹) :
    (∫ x in a..b, f (γ x)) = (∫ x in a..b, G (γ x)) +
      ∑ ρ ∈ P, r ρ * (∫ x in a..b, (γ x - ρ)⁻¹) := by
  have hi (ρ : ℂ) (hρ : ρ ∈ P) : IntervalIntegrable
      (fun x => r ρ * (γ x - ρ)⁻¹) volume a b :=
    (continuousOn_const.mul ((hγ.continuousOn.sub continuousOn_const).inv₀
      (fun x hx => sub_ne_zero.mpr (havoid x hx ρ hρ)))).intervalIntegrable
  have his : IntervalIntegrable (fun x => ∑ ρ ∈ P, r ρ * (γ x - ρ)⁻¹) volume a b := by
    convert IntervalIntegrable.sum P hi using 1
    ext x
    simp only [Finset.sum_apply]
  rw [intervalIntegral.integral_congr hdecomp,
    intervalIntegral.integral_add hG.intervalIntegrable his,
    intervalIntegral.integral_finsetSum hi]
  simp only [intervalIntegral.integral_const_mul]

/-- The rectangle residue formula, given an analytic regular part after
subtracting the finitely many interior simple principal parts. The pointwise
values assigned to the original function at its poles play no role. -/
private theorem rectangle_residues_of_regular_part (a b u v : ℝ) (hab : a ≤ b) (huv : u ≤ v)
    (f G : ℂ → ℂ) (P : Finset ℂ) (r : ℂ → ℂ)
    (hP : ∀ ρ ∈ P, a < ρ.re ∧ ρ.re < b ∧ u < ρ.im ∧ ρ.im < v)
    (hG : DifferentiableOn ℂ G (Set.Icc a b ×ℂ Set.Icc u v))
    (hf : ∀ z ∈ Set.Icc a b ×ℂ Set.Icc u v, z ∉ P →
      f z = G z + ∑ ρ ∈ P, r ρ * (z-ρ)⁻¹) :
    rectangleBoundary a b u v f = (2 * Real.pi * I) * ∑ ρ ∈ P, r ρ := by
  let H (y x : ℝ) := (x:ℂ) + (y:ℂ) * I
  let V (x y : ℝ) := (x:ℂ) + (y:ℂ) * I
  have edge (m n : ℝ) (γ : ℝ → ℂ) (hc : Continuous γ)
      (hγ : ∀ x ∈ Set.uIcc m n, γ x ∈ Set.Icc a b ×ℂ Set.Icc u v)
      (hn : ∀ x ∈ Set.uIcc m n, γ x ∉ P) :
      (∫ x in m..n, f (γ x)) = (∫ x in m..n, G (γ x)) +
        ∑ ρ ∈ P, r ρ * (∫ x in m..n, (γ x - ρ)⁻¹) :=
    rect_principal_edge m n γ f G P r hc (hG.continuousOn.comp hc.continuousOn hγ)
      (fun x hx ρ hρ he => hn x hx (he ▸ hρ)) (fun x hx => hf _ (hγ x hx) (hn x hx))
  have hor (y : ℝ) (hy : y ∈ Set.Icc u v) (hey : y = u ∨ y = v) := edge a b (H y)
    (by dsimp [H]; fun_prop)
    (by intro x hx; rw [Set.uIcc_of_le hab] at hx; simpa [H, Complex.mem_reProdIm] using
          And.intro hx hy)
    (by intro x _ hp; obtain ⟨_,_,hlo,hhi⟩ := hP _ hp
        simp [H] at hlo hhi
        rcases hey with rfl | rfl <;> linarith)
  have ver (x : ℝ) (hx : x ∈ Set.Icc a b) (hex : x = a ∨ x = b) := edge u v (V x)
    (by dsimp [V]; fun_prop)
    (by intro y hy; rw [Set.uIcc_of_le huv] at hy; simpa [V, Complex.mem_reProdIm] using
          And.intro hx hy)
    (by intro y _ hp; obtain ⟨hlo,hhi,_,_⟩ := hP _ hp
        simp [V] at hlo hhi
        rcases hex with rfl | rfl <;> linarith)
  have hreg : rectangleBoundary a b u v G = 0 := by
    simpa only [rectangleBoundary, smul_eq_mul] using
      Complex.integral_boundary_rect_eq_zero_of_differentiableOn G (⟨a,u⟩ : ℂ) (⟨b,v⟩ : ℂ)
        (by simpa only [Set.uIcc_of_le hab, Set.uIcc_of_le huv] using hG)
  calc
    rectangleBoundary a b u v f = rectangleBoundary a b u v G +
        ∑ ρ ∈ P, r ρ * rectangleBoundary a b u v (fun z => (z-ρ)⁻¹) := by
      change (∫ x in a..b, f (H u x)) - (∫ x in a..b, f (H v x)) +
        I * (∫ y in u..v, f (V b y)) - I * (∫ y in u..v, f (V a y)) = _
      rw [hor u ⟨le_rfl,huv⟩ (.inl rfl), hor v ⟨huv,le_rfl⟩ (.inr rfl),
        ver b ⟨hab,le_rfl⟩ (.inr rfl), ver a ⟨le_rfl,hab⟩ (.inl rfl)]
      simp only [H,V,rectangleBoundary,mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib,
        Finset.mul_sum, mul_left_comm (r _) I]
      ring
    _ = _ := by
      rw [hreg, zero_add, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ hρ
      obtain ⟨h1,h2,h3,h4⟩ := hP ρ hρ
      rw [rectangleBoundary_inv_sub a b u v ρ h1 h2 h3 h4, mul_comm]

/-- Residue theorem for finitely many simple poles in a rectangle. Each pole
has a local holomorphic remainder after removal of its simple principal part.
Only differentiability near the other points of the closed rectangle is needed. -/
private theorem rectangle_residues_of_local_principal_parts (a b u v : ℝ) (hab : a ≤ b) (huv : u ≤ v)
    (f : ℂ → ℂ) (P : Finset ℂ) (r : ℂ → ℂ)
    (hP : ∀ ρ ∈ P, a < ρ.re ∧ ρ.re < b ∧ u < ρ.im ∧ ρ.im < v)
    (hhol : ∀ z ∈ Set.Icc a b ×ℂ Set.Icc u v, z ∉ P → DifferentiableAt ℂ f z)
    (hlocal : ∀ ρ ∈ P, ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧
      f =ᶠ[𝓝[≠] ρ] fun z => g z + r ρ * (z-ρ)⁻¹) :
    rectangleBoundary a b u v f = (2 * Real.pi * I) * ∑ ρ ∈ P, r ρ := by
  classical
  choose! g hg hprincipal using hlocal
  let term (p z : ℂ) := r p * (z-p)⁻¹
  let G (z : ℂ) := if z ∈ P then g z z - ∑ p ∈ P.erase z, term p z
                    else f z - ∑ p ∈ P, term p z
  have dsum (S : Finset ℂ) (z : ℂ) (hn : z ∉ S) :
      DifferentiableAt ℂ (fun w => ∑ p ∈ S, term p w) z := by
    apply DifferentiableAt.fun_sum
    intro p hp
    have hzp : z-p ≠ 0 := sub_ne_zero.mpr (fun h => hn (h ▸ hp))
    change DifferentiableAt ℂ (fun w : ℂ => r p * (w-p)⁻¹) z
    fun_prop (disch := assumption)
  apply rectangle_residues_of_regular_part a b u v hab huv f G P r hP
  · intro z hz
    by_cases hp : z ∈ P
    · let H (w : ℂ) := g z w - ∑ p ∈ P.erase z, term p w
      have hnear : G =ᶠ[𝓝 z] H := by
        apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE _ (by simp [G,H,hp])
        have havoid : ∀ᶠ w in 𝓝[≠] z, w ∉ P :=
          nhdsNE_le_cofinite z P.finite_toSet.compl_mem_cofinite
        filter_upwards [hprincipal z hp, havoid] with w hfw hw
        simp only [G, H, ite_eq_right hw]
        rw [← Finset.sum_erase_add _ _ hp, hfw]
        dsimp [term]
        ring
      exact (((hg z hp).differentiableAt.sub (dsum (P.erase z) z (by simp))).congr_of_eventuallyEq
        hnear).differentiableWithinAt
    · have hnear : G =ᶠ[𝓝 z] fun w => f w - ∑ p ∈ P, term p w := by
        filter_upwards [P.finite_toSet.isClosed.compl_mem_nhds hp] with w hw
        exact ite_eq_right hw
      exact (((hhol z hz hp).sub (dsum P z hp)).congr_of_eventuallyEq hnear).differentiableWithinAt
  · intro z _ hz
    simp [G, hz, term]

end

section

open Complex Metric Set MeromorphicOn

private theorem nonprincipal_strip_logDeriv_of_separation {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ)
    (hs₀ : 1 / 4 ≤ s.re) (hs₁ : s.re ≤ 2) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → χ.LFunction ρ = 0 → δ ≤ ‖s - ρ‖) :
    ‖logDeriv χ.LFunction s‖ ≤
      (1440 + (1440 * Real.log 48 + 1 / δ) / Real.log (47/46)) *
      (9 * Real.log ((q : ℝ) * (2 + |s.im|))) := by
  let c : ℂ := ⟨3, s.im⟩
  let F (w : ℂ) := χ.LFunction (w + c)
  let U : ℝ := (q : ℝ) * (2 + |s.im|)
  let B := 128 * U
  have hq : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q from q.pos_of_neZero)
  have hU : 2 ≤ U := calc
    (2 : ℝ) ≤ 2 + |s.im| := le_add_of_nonneg_right (abs_nonneg _)
    _ ≤ U := le_mul_of_one_le_left (by positivity) hq
  have hUpos : 0 < U := by linarith
  have hB : 1 ≤ B := by dsimp only [B]; linarith
  have hc : ‖c‖ ≤ 3 + |s.im| := by simpa [c] using Complex.norm_le_abs_re_add_abs_im c
  have hboundary (w : ℂ) (hw : w ∈ sphere 0 (47/16)) : ‖F w‖ ≤ B := by
    have hwN : ‖w‖ = 47 / 16 := by simpa only [mem_sphere, dist_zero_right] using hw
    have hwre := (abs_le.mp ((Complex.abs_re_le_norm w).trans_eq hwN)).1
    have hRe : 1 / 16 ≤ (w + c).re := by simp only [Complex.add_re, c]; linarith
    have hRepos : 0 < (w + c).re := by linarith
    have hnorm : ‖w + c‖ ≤ 4 * (2 + |s.im|) := by
      linarith [norm_add_le w c, abs_nonneg s.im]
    calc
      _ ≤ ‖w+c‖ * ((q : ℝ) + 1) / (w+c).re :=
        nonprincipal_LFunction_norm_le χ hχ (w+c) hRepos
      _ ≤ 32 * (q:ℝ) * ‖w+c‖ := by
        apply (div_le_iff₀ hRepos).mpr
        have h₁ := mul_le_mul_of_nonneg_right hRe (show 0 ≤ 32 * (q : ℝ) * ‖w+c‖ by positivity)
        have h₂ := mul_le_mul_of_nonneg_left hq (norm_nonneg (w+c))
        linarith only [h₁, h₂]
      _ ≤ 32 * (q:ℝ) * (4 * (2+|s.im|)) := by gcongr
      _ = B := by dsimp only [B, U]; ring
  have hlower : 1/2 ≤ ‖F 0‖ := by
    simpa only [F, zero_add] using (half_le_norm_LFunction_of_re_eq_three χ (s := c) rfl)
  have hFpos : 0 < ‖F 0‖ := by linarith
  have hratio : B / ‖F 0‖ ≤ 256 * U := by
    apply (div_le_iff₀ hFpos).mpr
    calc B = 256 * U * (1/2) := by dsimp only [B]; ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hlower (by positivity)
  have hlog : Real.log (B / ‖F 0‖) ≤ 9 * Real.log U := by
    calc
      _ ≤ Real.log (256 * U) := Real.log_le_log (div_pos (by linarith) hFpos) hratio
      _ = 8 * Real.log 2 + Real.log U := by
        rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_mul (by norm_num) hUpos.ne', Real.log_pow]
        norm_num
      _ ≤ _ := by linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hU]
  have hFa : AnalyticOnNhd ℂ F (closedBall 0 (47/16)) := fun w _ =>
    ((χ.differentiable_LFunction hχ).comp (differentiable_id.add_const c)).analyticAt w
  have hz : ‖s-c‖ ≤ 11 / 4 := by
    have heq : s-c = ((s.re - 3 : ℝ) : ℂ) := by apply Complex.ext <;> simp [c]
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hdist (ρ : ℂ) (hρ : ρ ∈ closedBall 0 (23/8)) (hzero : F ρ = 0) :
      δ ≤ ‖s - c - ρ‖ := by
    have hre := (abs_le.mp ((Complex.abs_re_le_norm ρ).trans (mem_closedBall_zero_iff.mp hρ))).1
    have hpos : 0 < (ρ+c).re := by simp only [Complex.add_re, c]; linarith
    have hlt : (ρ+c).re < 1 := by
      by_contra! h
      exact (χ.LFunction_ne_zero_of_one_le_re (.inl hχ) h) hzero
    rw [show s - c - ρ = s - (ρ+c) by ring]
    exact hsep _ hpos hlt hzero
  have hD : 0 < 9 * Real.log U := mul_pos (by norm_num) (Real.log_pos (by linarith))
  have hh := local_logDeriv_bound_of_distance F hFa (norm_pos_iff.mp hFpos)
    hB hD hδ hboundary hlog hz hdist
  have htrans : logDeriv F (s-c) = logDeriv χ.LFunction s := by
    simp only [F, logDeriv_apply, deriv_comp_add_const, sub_add_cancel]
  rwa [htrans] at hh

/-- Under GRH, the entire line of real part one quarter is at distance
at least one quarter from every nontrivial zero. -/
private theorem nonprincipal_quarter_line_logDeriv {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ)
    (hGRH : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → χ.LFunction ρ = 0 → ρ.re = 1/2) :
    ‖logDeriv χ.LFunction (⟨1/4,t⟩ : ℂ)‖ ≤
      (1440 + (1440 * Real.log 48 + 4) / Real.log (47/46)) *
      (9 * Real.log ((q : ℝ) * (2 + |t|))) := by
  have hdist (ρ : ℂ) (h₀ : 0 < ρ.re) (h₁ : ρ.re < 1) (hL : χ.LFunction ρ = 0) :
      1/4 ≤ ‖(⟨1/4,t⟩ : ℂ) - ρ‖ := by
    have h := Complex.abs_re_le_norm ((⟨1/4,t⟩ : ℂ) - ρ)
    simpa only [Complex.sub_re, hGRH ρ h₀ h₁ hL,
      show |(1 : ℝ)/4 - 1/2| = 1/4 by norm_num] using h
  simpa only [show (1:ℝ) / (1/4) = 4 by norm_num] using
    nonprincipal_strip_logDeriv_of_separation χ hχ (⟨1/4,t⟩ : ℂ)
      (by norm_num) (by norm_num) (by norm_num : (0:ℝ) < 1/4) hdist

end

section

open Complex Metric Filter MeasureTheory Set
open scoped Topology

/-- Growth of the pole-removed zeta function down to the left edge of the
larger disk used for the logarithmic derivative estimate. -/
private theorem zeta_regular_norm_le_sixteenth (s : ℂ) (hs : 1/16 ≤ s.re) :
    ‖riemannZeta₁ s‖ ≤ 17 * (1 + ‖s‖)^2 := by
  have hs' : 0 < s.re := by linarith
  have he : -(s.re+1) < -1 := by linarith
  have hI : ‖∫ t in Ioi (1:ℝ), (((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) * (t:ℂ)^(-(s+1)))‖ ≤ 16 := by
    calc
      _ ≤ ∫ t in Ioi (1:ℝ), t ^ (-(s.re+1)) := by
        apply norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt he zero_lt_one)
        filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
        have ht' : 0 < t := zero_lt_one.trans (show 1 < t from ht)
        rw [norm_mul, Complex.norm_of_nonneg (Nat.zero_le_self_sub_floor ht'.le),
          norm_cpow_eq_rpow_re_of_pos ht', neg_re, add_re, one_re]
        exact mul_le_of_le_one_left (Real.rpow_nonneg ht'.le _) (Nat.self_sub_floor_lt_one _).le
      _ ≤ 16 := by
        rw [integral_Ioi_rpow_of_lt he zero_lt_one, Real.one_rpow, show -(s.re+1)+1 = -s.re by ring,
          neg_div_neg_eq, div_le_iff₀ hs']
        linarith
  rw [zeta_pole_removed_eq_floor_integral s hs']
  apply (norm_sub_le ..).trans
  rw [norm_mul, norm_mul]
  have hsub : ‖s - 1‖ ≤ ‖s‖ + 1 := by simpa using norm_sub_le s (1:ℂ)
  calc
    _ ≤ ‖s‖ + (‖s‖ + 1) * ‖s‖ * 16 := by gcongr
    _ ≤ _ := by nlinarith [sq_nonneg ‖s‖, norm_nonneg s]

/-- Away from the zeros and pole this is the exact pole subtraction for ζ'/ζ. -/
private theorem zeta_logDeriv_subtract_pole {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    logDeriv riemannZeta s = logDeriv riemannZeta₁ s - (s - 1)⁻¹ := by
  have hs' := sub_ne_zero.mpr hs
  have hreg : riemannZeta₁ s ≠ 0 := by
    intro h
    exact hz (by rw [riemannZeta_eq_inv_sub_mul hs, h, mul_zero])
  rw [logDeriv_apply, logDeriv_apply, deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs,
    riemannZeta_eq_inv_sub_mul hs]
  field_simp
  ring


/-- A uniform bound for the logarithmic derivative of ζ away from its
nontrivial zeros, on the full strip traversed by the rectangle. -/
private theorem zeta_logDeriv_of_zero_separation (s : ℂ) (hs₀ : 1/4 ≤ s.re) (hs₁ : s.re ≤ 2)
    (hsne : s ≠ 1) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → riemannZeta ρ = 0 → δ ≤ ‖s - ρ‖) :
    ‖logDeriv riemannZeta s‖ ≤
      (1440 + (1440 * Real.log 48 + 1/δ) / Real.log (47/46)) *
        (11 * Real.log (2 + |s.im|)) + ‖s - 1‖⁻¹ := by
  let c : ℂ := ⟨3, s.im⟩
  let U : ℝ := 2 + |s.im|
  let f (w : ℂ) := riemannZeta₁ (c + w)
  let B : ℝ := 512 * U^2
  have hU : 2 ≤ U := le_add_of_nonneg_right (abs_nonneg _)
  have hUpos : 0 < U := by linarith
  have hB : 1 ≤ B := by dsimp only [B]; nlinarith [sq_nonneg (U-2)]
  have hc : ‖c‖ ≤ 3 + |s.im| := by simpa [c] using Complex.norm_le_abs_re_add_abs_im c
  have hcenter : 1 ≤ ‖f 0‖ := by
    have hfac : 2 ≤ ‖c - 1‖ := by
      have hb := Complex.abs_re_le_norm (c-1)
      norm_num [c] at hb
      exact hb
    have hz : (1/2 : ℝ) ≤ ‖riemannZeta c‖ := by
      simpa only [DirichletCharacter.LFunction_modOne_eq] using
        (half_le_norm_LFunction_of_re_eq_three (1 : DirichletCharacter ℂ 1) (s := c) rfl)
    have hne : c ≠ 1 := by intro h; have := congrArg Complex.re h; norm_num [c] at this
    have hreg : riemannZeta₁ c = (c-1) * riemannZeta c := by
      rw [riemannZeta_eq_inv_sub_mul hne, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hne), one_mul]
    simp only [f, add_zero, hreg, norm_mul]
    calc (1:ℝ) = 2 * (1/2) := by norm_num
         _ ≤ _ := mul_le_mul hfac hz (by norm_num) (norm_nonneg _)
  have hpos := zero_lt_one.trans_le hcenter
  have hbound (w : ℂ) (hw : w ∈ sphere 0 (47/16)) : ‖f w‖ ≤ B := by
    have hwN : ‖w‖ = 47/16 := by simpa [mem_sphere] using hw
    have hrew : - (47 /16) ≤ w.re := by
      have := Complex.abs_re_le_norm w
      rw [hwN] at this
      exact (abs_le.mp this).1
    have hzre : 1/16 ≤ (c+w).re := by simp only [add_re, c]; linarith
    have hn : 1 + ‖c + w‖ ≤ 4 * U := by
      have h := norm_add_le c w
      rw [hwN] at h
      dsimp only [U]
      linarith [abs_nonneg s.im]
    calc
      _ ≤ 17 * (1 + ‖c + w‖)^2 := zeta_regular_norm_le_sixteenth _ hzre
      _ ≤ 17 * (4 * U)^2 := by gcongr
      _ ≤ B := by dsimp only [B]; nlinarith [sq_nonneg U]
  have hlog : Real.log (B / ‖f 0‖) ≤ 11 * Real.log U := by
    calc
      _ ≤ Real.log B := Real.log_le_log (div_pos (by linarith) hpos) (div_le_self (by linarith) hcenter)
      _ = 9 * Real.log 2 + 2 * Real.log U := by
        rw [show B = (2 : ℝ)^9 * U^2 by norm_num [B], Real.log_mul (by norm_num) (pow_ne_zero _ hUpos.ne'),
          Real.log_pow, Real.log_pow]
        norm_num
      _ ≤ _ := by linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hU]
  let z := s - c
  have hz0 : c + z = s := by dsimp [z]; abel
  have hzN : ‖z‖ ≤ 11/4 := by
    have hz' : z = ((s.re - 3 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [z,c]
    rw [hz', Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hloc (w : ℂ) (hw : w ∈ closedBall 0 (23/8)) (hfw : f w = 0) : δ ≤ ‖z - w‖ := by
    have hwN : ‖w‖ ≤ 23/8 := mem_closedBall_zero_iff.mp hw
    have hwb := (abs_le.mp ((Complex.abs_re_le_norm w).trans hwN)).1
    have hre : 0 < (c+w).re := by simp only [c, add_re]; linarith
    have hne : c+w ≠ 1 := by
      intro h
      have : riemannZeta₁ (c+w) = 0 := hfw
      simp [h,riemannZeta₁_one] at this
    have hζ : riemannZeta (c+w) = 0 := by
      rw [riemannZeta_eq_inv_sub_mul hne, show riemannZeta₁ (c+w) = 0 from hfw, mul_zero]
    have hlt : (c+w).re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hζ
    have h := hsep _ hre hlt hζ
    rwa [show s - (c+w) = z - w by dsimp [z]; abel] at h
  have han : AnalyticOnNhd ℂ f (closedBall 0 (47/16)) := by
    intro w _
    exact (differentiable_riemannZeta₁.analyticAt (c+w)).comp (by fun_prop)
  have hL := local_logDeriv_bound_of_distance f han (norm_pos_iff.mp hpos) hB
    (show 0 < 11 * Real.log U from mul_pos (by norm_num) (Real.log_pos (by linarith))) hδ
    hbound hlog hzN hloc
  have heq : logDeriv f z = logDeriv riemannZeta₁ s := by
    simp only [logDeriv_apply, f, deriv_comp_const_add, hz0]
  rw [heq] at hL
  have hζ : riemannZeta s ≠ 0 := by
    intro h
    have hlt : s.re < 1 := lt_of_not_ge fun hle => riemannZeta_ne_zero_of_one_le_re hle h
    have hbad := hsep s (by linarith) hlt h
    simp at hbad
    linarith
  rw [zeta_logDeriv_subtract_pole hsne hζ]
  exact (norm_sub_le ..).trans (by rw [norm_inv]; exact add_le_add hL le_rfl)

/-- On the left vertical edge GRH supplies the fixed horizontal distance
one quarter to all nontrivial zeros. -/
private theorem zeta_logDeriv_quarter_line (s : ℂ) (hs : s.re = 1/4)
    (hRH : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → riemannZeta ρ = 0 → ρ.re = 1/2) :
    ‖logDeriv riemannZeta s‖ ≤
      (1440 + (1440 * Real.log 48 + 4) / Real.log (47/46)) *
        (11 * Real.log (2 + |s.im|)) + 4/3 := by
  have hsep (ρ : ℂ) (h₀ : 0 < ρ.re) (h₁ : ρ.re < 1) (hzero : riemannZeta ρ = 0) :
      (1/4 : ℝ) ≤ ‖s-ρ‖ := by
    have hb := Complex.abs_re_le_norm (s-ρ)
    norm_num [Complex.sub_re, hs, hRH ρ h₀ h₁ hzero] at hb
    exact hb
  have hne : s ≠ 1 := by intro h; norm_num [h] at hs
  have hn : (3/4 : ℝ) ≤ ‖s-1‖ := by
    have hb := Complex.abs_re_le_norm (s-1)
    norm_num [Complex.sub_re, hs] at hb
    exact hb
  have hi : ‖s-1‖⁻¹ ≤ 4/3 := by
    have := inv_anti₀ (by norm_num : (0:ℝ)<3/4) hn
    norm_num at this ⊢
    exact this
  have h := zeta_logDeriv_of_zero_separation s hs.ge (by linarith) hne (by norm_num) hsep
  norm_num only [one_div_div, div_one] at h
  linarith only [h, hi]

/-- On a horizontal edge separated from the ordinates of all nontrivial
zeros, the pole contributes at most one when the height has modulus at least one. -/
private theorem zeta_logDeriv_horizontal (s : ℂ) (hs₀ : 1/4 ≤ s.re) (hs₁ : s.re ≤ 2)
    (ht : 1 ≤ |s.im|) {δ : ℝ} (hδ : 0 < δ)
    (hheight : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → riemannZeta ρ = 0 → δ ≤ |s.im - ρ.im|) :
    ‖logDeriv riemannZeta s‖ ≤
      (1440 + (1440 * Real.log 48 + 1/δ) / Real.log (47/46)) *
        (11 * Real.log (2 + |s.im|)) + 1 := by
  have hn : 1 ≤ ‖s-1‖ := ht.trans (by simpa using Complex.abs_im_le_norm (s-1))
  have hi : ‖s-1‖⁻¹ ≤ 1 := by simpa using inv_anti₀ zero_lt_one hn
  have hsne : s ≠ 1 := by intro he; norm_num [he] at ht
  have h := zeta_logDeriv_of_zero_separation s hs₀ hs₁ hsne hδ (fun ρ h₀ h₁ hzero =>
    (hheight ρ h₀ h₁ hzero).trans (by simpa only [Complex.sub_im] using Complex.abs_im_le_norm (s-ρ)))
  linarith only [h, hi]

end

section

open Complex MeasureTheory Set Filter
open scoped Interval

private theorem inv_shift_abs_integral {u v : ℝ} (hu : u ≤ 0) (hv : 0 ≤ v) :
    (∫ t : ℝ in u..v, (1 + |t|)⁻¹) = Real.log (1 + |u|) + Real.log (1+v) := by
  have hc : Continuous (fun t : ℝ => (1 + |t|)⁻¹) :=
    (continuous_const.add continuous_abs).inv₀ (fun t => (show 1 + |t| ≠ 0 by positivity))
  have posint (w : ℝ) (hw : 0 ≤ w) :
      (∫ t : ℝ in 0..w, (1 + |t|)⁻¹) = Real.log (1+w) := by
    calc
      _ = ∫ t : ℝ in 0..w, (t+1)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hw] at ht
        change (1+|t|)⁻¹ = (t+1)⁻¹
        rw [abs_of_nonneg ht.1, add_comm]
      _ = ∫ t : ℝ in (0+1)..(w+1), t⁻¹ := intervalIntegral.integral_comp_add_right _ _
      _ = _ := by rw [integral_inv_of_pos (by norm_num) (by linarith)]; simp [add_comm]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable u 0)
    (hc.intervalIntegrable 0 v), posint _ hv, abs_of_nonpos hu]
  congr 1
  have hn := intervalIntegral.integral_comp_neg (a := 0) (b := -u)
    (fun t : ℝ => (1 + |t|)⁻¹)
  simpa only [abs_neg, neg_neg, neg_zero] using
    (hn.symm.trans (by simpa only [abs_neg] using posint (-u) (by linarith)))

/-- Bound the new vertical edge using the uniform logarithmic-derivative bound
on that edge. The unit difference saves one full power of the cutoff. -/
private theorem unit_kernel_left_edge (G : ℂ → ℂ) {x M u v : ℝ} (hx : 0 < x)
    (hu : u ≤ 0) (hv : 0 ≤ v) (hM : 0 ≤ M)
    (hG : ∀ t ∈ Icc u v, ‖G ((1/4 : ℂ) + (t : ℂ) * I)‖ ≤ M) :
    ‖∫ t : ℝ in u..v, G ((1/4 : ℂ) + (t : ℂ) * I) *
      unitPerronKernel x ((1/4 : ℂ) + (t : ℂ) * I)‖ ≤
      (5 * M * (x+1) ^ (1/4 : ℝ)) * (Real.log (1+|u|) + Real.log (1+v)) := by
  let D := 5 * M * (x+1)^(1/4 : ℝ)
  have hc : Continuous (fun t : ℝ => D * (1 + |t|)⁻¹) :=
    continuous_const.mul ((continuous_const.add continuous_abs).inv₀
      (fun t => (show 1 + |t| ≠ 0 by positivity)))
  rw [← inv_shift_abs_integral hu hv, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.norm_integral_le_of_norm_le (hu.trans hv) _ (hc.intervalIntegrable _ _)
  apply Eventually.of_forall
  intro t ht
  let s : ℂ := 1/4 + (t : ℂ) * I
  have hr : s.re = 1/4 := by norm_num [s]
  have hi : s.im = t := by norm_num [s]
  have hσ := Complex.abs_re_le_norm s
  have hτ := Complex.abs_im_le_norm s
  rw [hr] at hσ
  rw [hi] at hτ
  have hden : 1 + |t| ≤ 5 * ‖s‖ := by norm_num at hσ; linarith
  have hp : 0 < ‖s‖ := by norm_num at hσ; linarith
  have h := unitPerronKernel_norm (s := s) hx (by rw [hr]; norm_num)
  rw [hr] at h
  rw [norm_mul]
  apply (mul_le_mul (hG t ⟨ht.1.le,ht.2⟩) h (norm_nonneg _) hM).trans
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc
    _ ≤ (M * ((x+1) ^ (1/4 : ℝ) / ‖s‖)) * (5 * ‖s‖) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    _ = _ := by dsimp only [D]; field_simp

/-- On the two horizontal edges the first-order kernel bound and the whole
width of the strip suffice. -/
private theorem unit_kernel_horizontal_edge (G : ℂ → ℂ) {x M t : ℝ} (hx : 0 < x)
    (ht : t ≠ 0) (hM : 0 ≤ M)
    (hG : ∀ σ ∈ Icc (1/4 : ℝ) 2, ‖G ((σ : ℂ) + (t : ℂ) * I)‖ ≤ M) :
    ‖∫ σ : ℝ in (1/4)..2, G ((σ : ℂ) + (t : ℂ) * I) *
      unitPerronKernel x ((σ : ℂ) + (t : ℂ) * I)‖ ≤ 2 * M * (x+1)^2 / |t| := by
  have hb (σ : ℝ) (hσ : σ ∈ Set.uIoc (1/4 : ℝ) 2) :
      ‖G ((σ : ℂ) + (t : ℂ) * I) * unitPerronKernel x ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        M * ((x+1)^2 / |t|) := by
    rw [uIoc_of_le (by norm_num)] at hσ
    let s : ℂ := (σ : ℂ) + (t : ℂ) * I
    have hr : s.re = σ := by simp [s]
    have hi : s.im = t := by simp [s]
    have hden := Complex.abs_im_le_norm s
    rw [hi] at hden
    have h := unitPerronKernel_norm (s := s) hx (by rw [hr]; linarith [hσ.1])
    rw [hr] at h
    rw [norm_mul]
    refine mul_le_mul (hG σ ⟨hσ.1.le,hσ.2⟩) (h.trans ?_) (norm_nonneg _) hM
    apply div_le_div₀ (by positivity) _ (abs_pos.mpr ht) hden
    calc
      _ ≤ (x+1)^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hσ.2
      _ = _ := by norm_num
  apply (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans
  norm_num
  have hp : 0 ≤ M * ((x+1)^2 / |t|) := by positivity
  calc
    _ ≤ (M * ((x+1)^2 / |t|)) * 2 := mul_le_mul_of_nonneg_left (by norm_num) hp
    _ = _ := by ring

end

section

open Complex Filter Set DirichletCharacter
open scoped Classical Topology

/-- Multiplication by an analytic weight multiplies the simple residue by
the value of the weight at the pole. -/
private theorem analytic_weight_principal_part {f w : ℂ → ℂ} {ρ r : ℂ}
    (hw : AnalyticAt ℂ w ρ)
    (hf : ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧
      f =ᶠ[𝓝[≠] ρ] fun z => g z + r * (z-ρ)⁻¹) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G ρ ∧
      (fun z => f z * w z) =ᶠ[𝓝[≠] ρ] fun z => G z + (r * w ρ) * (z-ρ)⁻¹ := by
  obtain ⟨g,hg,he⟩ := hf
  refine ⟨fun z => g z * w z + r * dslope w ρ z, ?_, ?_⟩
  · fun_prop (disch := assumption)
  · filter_upwards [he, self_mem_nhdsWithin] with z hz hne
    have hn : z ≠ ρ := hne
    rw [hz, dslope_of_ne w hn, slope_def_field]
    ring

private theorem unitPerronKernel_analyticAt {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (unitPerronKernel x) s := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hs
  have h1 : s + 1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  have hpow {y : ℝ} (hy : 0 < y) : AnalyticAt ℂ (fun z : ℂ => (y : ℂ) ^ (z+1)) s := by
    exact ((show Differentiable ℂ (fun z : ℂ => z+1) by fun_prop).const_cpow
      (.inl (by exact_mod_cast hy.ne'))).analyticAt s
  unfold unitPerronKernel
  exact (hpow (show 0 < x+1 by linarith) |>.sub (hpow hx)).div
    (by fun_prop) (mul_ne_zero h0 h1)

private theorem neg_logDeriv_zero_principal_part {f : ℂ → ℂ} {ρ : ℂ}
    (hf : AnalyticAt ℂ f ρ) (ho : analyticOrderAt f ρ ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ (fun z => -logDeriv f z) =ᶠ[𝓝[≠] ρ]
      fun z => g z + (-(analyticOrderNatAt f ρ : ℂ)) * (z-ρ)⁻¹ := by
  obtain ⟨g,hg,he⟩ := logDeriv_principal_part hf ho
  refine ⟨fun z => -g z, hg.neg, ?_⟩
  filter_upwards [he] with z hz
  rw [hz, div_eq_mul_inv]
  ring

private theorem neg_logDeriv_principal_character_pole (q : ℕ) [NeZero q] :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧
      (fun z => -logDeriv (LFunction (1 : DirichletCharacter ℂ q)) z) =ᶠ[𝓝[≠] (1 : ℂ)]
        fun z => g z + 1 * (z-1)⁻¹ := by
  let F := LFunctionTrivChar₁ q
  have ha : AnalyticAt ℂ F 1 := (differentiable_LFunctionTrivChar₁ q).analyticAt 1
  have hn : F 1 ≠ 0 := LFunctionTrivChar₁_apply_one_ne_zero q
  refine ⟨fun z => -logDeriv F z, (ha.deriv.div ha hn).neg, ?_⟩
  filter_upwards [(ha.continuousAt.eventually_ne hn).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hF hz
  have hz' : z ≠ 1 := hz
  have he : F z = (z-1) * LFunction (1 : DirichletCharacter ℂ q) z :=
    Function.update_of_ne hz' _ _
  have hL : LFunction (1 : DirichletCharacter ℂ q) z ≠ 0 := right_ne_zero_of_mul (he ▸ hF)
  simp only [logDeriv_apply, F, deriv_LFunctionTrivChar₁_apply_of_ne_one q hz', one_mul]
  rw [show LFunctionTrivChar₁ q z = _ from he]
  change _ = -(((z-1) * deriv (LFunction (1 : DirichletCharacter ℂ q)) z +
    LFunction (1 : DirichletCharacter ℂ q) z) / _) + _
  field_simp [sub_ne_zero.mpr hz', hL]
  ring

/-- Exact Perron residue identity throughout a positive-real-part rectangle
straddling the point 1. It covers principal and nonprincipal characters of any modulus.
`Z` consists of the zeros in the closed rectangle away from 1, and all
these zeros are assumed strictly inside the rectangle. -/
private theorem character_unitPerron_rectangle {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x a b u v : ℝ} (hx : 0 < x) (ha : 0 < a) (ha1 : a < 1) (hb1 : 1 < b)
    (hu : u < 0) (hv : 0 < v) (Z : Finset ℂ)
    (hZ : ∀ z : ℂ, z ∈ Z ↔ z ∈ Icc a b ×ℂ Icc u v ∧ z ≠ 1 ∧ χ.LFunction z = 0)
    (hint : ∀ z ∈ Z, a < z.re ∧ z.re < b ∧ u < z.im ∧ z.im < v) :
    rectangleBoundary a b u v (fun z => -logDeriv χ.LFunction z * unitPerronKernel x z) =
      (2 * Real.pi * I) * ((if χ = 1 then (x : ℂ) + 1/2 else 0) -
        ∑ z ∈ Z, (analyticOrderNatAt χ.LFunction z : ℂ) * unitPerronKernel x z) := by
  classical
  let P := if χ = 1 then insert (1 : ℂ) Z else Z
  let r (z : ℂ) := if χ = 1 ∧ z = 1 then unitPerronKernel x 1
                    else -(analyticOrderNatAt χ.LFunction z : ℂ) * unitPerronKernel x z
  have memP (z : ℂ) : z ∈ P ↔ (χ = 1 ∧ z = 1) ∨ z ∈ Z := by
    by_cases hχ : χ = 1 <;> simp [P,hχ]
  have hane (z : ℂ) (hz : z ≠ 1 ∨ χ ≠ 1) : AnalyticAt ℂ χ.LFunction z := by
    rcases hz with h | h
    · have han : AnalyticOnNhd ℂ χ.LFunction ({1}ᶜ : Set ℂ) :=
        (show DifferentiableOn ℂ χ.LFunction ({1}ᶜ : Set ℂ) from fun w hw =>
          (differentiableAt_LFunction χ w (.inl hw)).differentiableWithinAt).analyticOnNhd
          isOpen_compl_singleton
      exact han z h
    · exact (differentiable_LFunction h).analyticAt z
  have hrect := rectangle_residues_of_local_principal_parts a b u v
    (ha1.trans hb1).le (hu.trans hv).le (fun z => -logDeriv χ.LFunction z * unitPerronKernel x z) P r
  have hgeom (z : ℂ) (hz : z ∈ P) : a < z.re ∧ z.re < b ∧ u < z.im ∧ z.im < v := by
    rcases (memP z).mp hz with ⟨_,rfl⟩ | h
    · exact ⟨ha1,hb1,hu,hv⟩
    · exact hint z h
  have he := hrect hgeom (by
    intro z hz hn
    have hns : ¬(χ = 1 ∧ z = 1) := fun h => hn ((memP z).2 (.inl h))
    have hne : z ≠ 1 ∨ χ ≠ 1 := by tauto
    have hnL : χ.LFunction z ≠ 0 := by
      intro h
      by_cases h1 : z = 1
      · subst z
        exact LFunction_ne_zero_of_one_le_re χ (.inl (by tauto)) (by simp) h
      · exact hn ((memP z).2 <| .inr <| (hZ z).2 ⟨hz,h1,h⟩)
    have hL := hane z hne
    exact ((hL.deriv.div hL hnL).neg.mul (unitPerronKernel_analyticAt hx (ha.trans_le hz.1.1))).differentiableAt) (by
    intro z hz
    have hw := unitPerronKernel_analyticAt (s := z) hx (ha.trans (hgeom z hz).1)
    rcases (memP z).1 hz with ⟨hχ,rfl⟩ | h
    · subst χ
      simpa [r] using analytic_weight_principal_part hw (neg_logDeriv_principal_character_pole q)
    · obtain ⟨_,h1,hL⟩ := (hZ z).1 h
      have ho : analyticOrderAt χ.LFunction z ≠ ⊤ := by
        intro ho
        have hp := positive_multiplicity_of_character_zero χ h1 hL
        simp [analyticOrderNatAt,ho] at hp
      simpa [r,h1] using analytic_weight_principal_part hw
        (neg_logDeriv_zero_principal_part (hane z (.inl h1)) ho))
  rw [he]
  congr 1
  have hn1 : (1 : ℂ) ∉ Z := by intro h; exact ((hZ 1).1 h).2.1 rfl
  have hsum : ∑ z ∈ Z, r z = - ∑ z ∈ Z, (analyticOrderNatAt χ.LFunction z : ℂ) * unitPerronKernel x z := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun z hz => by simp [r,((hZ z).1 hz).2.1]
  by_cases hχ : χ = 1
  · rw [show P = insert (1 : ℂ) Z from ite_eq_left hχ, Finset.sum_insert hn1, hsum]
    simp [r,hχ,unitPerronKernel_one,sub_eq_add_neg]
  · simp [P,hχ,hsum]

/-- Under GRH, avoiding the zero ordinates on the two horizontal sides suffices.
The finite sum ranges precisely over the nontrivial zeros between those sides. -/
private theorem character_unitPerron_rectangle_of_GRH {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x a b u v : ℝ} (hx : 0 < x) (ha : 0 < a) (ha' : a < 1/2) (hb : 1 < b)
    (hu : u < 0) (hv : 0 < v)
    (hGRH : ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.re = 1/2)
    (hsafe : ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.im ≠ u ∧ z.im ≠ v) :
    ∃ Z : Finset ℂ,
      (∀ z : ℂ, z ∈ Z ↔ 0 < z.re ∧ z.re < 1 ∧ u < z.im ∧ z.im < v ∧ χ.LFunction z = 0) ∧
      rectangleBoundary a b u v (fun z => -logDeriv χ.LFunction z * unitPerronKernel x z) =
        (2 * Real.pi * I) * ((if χ = 1 then (x : ℂ) + 1/2 else 0) -
          ∑ z ∈ Z, (analyticOrderNatAt χ.LFunction z : ℂ) * unitPerronKernel x z) := by
  classical
  let K := Icc a b ×ℂ Icc u v
  have hfin := finite_character_zeros_on_compact χ
    (show IsCompact K from isCompact_Icc.reProdIm isCompact_Icc)
  let Z := hfin.toFinset
  have hZ (z : ℂ) : z ∈ Z ↔ z ∈ Icc a b ×ℂ Icc u v ∧ z ≠ 1 ∧ χ.LFunction z = 0 :=
    hfin.mem_toFinset
  have hcrit (z : ℂ) (hz : z ∈ Z) :
      0 < z.re ∧ z.re < 1 ∧ u < z.im ∧ z.im < v ∧ χ.LFunction z = 0 := by
    obtain ⟨hbox, hne, hzero⟩ := (hZ z).1 hz
    have h₀ := ha.trans_le hbox.1.1
    have h₁ : z.re < 1 := lt_of_not_ge fun h =>
      LFunction_ne_zero_of_one_le_re χ (.inr hne) h hzero
    obtain ⟨hs₁,hs₂⟩ := hsafe z h₀ h₁ hzero
    exact ⟨h₀,h₁,lt_of_le_of_ne hbox.2.1 hs₁.symm,lt_of_le_of_ne hbox.2.2 hs₂,hzero⟩
  refine ⟨Z,fun z => ⟨hcrit z, ?_⟩, character_unitPerron_rectangle χ hx ha
    (by linarith) hb hu hv Z hZ ?_⟩
  · rintro ⟨h₀,h₁,hu',hv',hzero⟩
    have hline := hGRH z h₀ h₁ hzero
    have hn : z ≠ 1 := by intro h; simp [h] at h₁
    exact (hZ z).2 ⟨⟨⟨by linarith,by linarith⟩,hu'.le,hv'.le⟩,hn,hzero⟩
  · intro z hz
    obtain ⟨h₀,h₁,hu',hv',hzero⟩ := hcrit z hz
    have hline := hGRH z h₀ h₁ hzero
    exact ⟨by linarith,by linarith,hu',hv'⟩

/-- The normalized contour integral differs from its principal-character
main term by the GRH bound for the sum of the enclosed zeros. -/
private theorem primitive_unitPerron_rectangle_error {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) {x a b u v T : ℝ} (hx : 0 < x) (ha : 0 < a)
    (ha' : a < 1/2) (hb : 1 < b) (hu : u < 0) (hv : 0 < v) (hT : 2 ≤ T)
    (huT : -T ≤ u) (hvT : v ≤ T)
    (hGRH : ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.re = 1/2)
    (hsafe : ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.im ≠ u ∧ z.im ≠ v) :
    ‖rectangleBoundary a b u v (fun z => -logDeriv χ.LFunction z * unitPerronKernel x z) /
        (2 * Real.pi * I) - (if χ = 1 then (x : ℂ) + 1/2 else 0)‖ ≤
      Real.sqrt (x+1) * ((120 / Real.log (23/22)) * (Real.log (2*q*T))^2) := by
  obtain ⟨Z,hZ,he⟩ := character_unitPerron_rectangle_of_GRH χ hx ha ha' hb hu hv hGRH hsafe
  have hc : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  rw [he,mul_div_cancel_left₀ _ hc,sub_sub_cancel_left,norm_neg]
  apply unitPerronKernel_zero_sum χ hprim hx hT Z hGRH
  intro z hz
  obtain ⟨h₀,h₁,hlo,hhi,hzero⟩ := (hZ z).1 hz
  exact ⟨h₀,h₁,abs_le.mpr ⟨huT.trans hlo.le,hhi.le.trans hvT⟩,hzero⟩

end

section

private noncomputable def logDerivDiskFactor : ℝ :=
  1440 + (1440 * Real.log 48 + 4) / Real.log (47/46)

/-- An absolute constant valid on both the left and horizontal contour edges. -/
private noncomputable def contourLogDerivBound : ℝ :=
  11 * logDerivDiskFactor + 2 / Real.log 2

private theorem logDerivDiskFactor_pos : 0 < logDerivDiskFactor := by
  unfold logDerivDiskFactor
  have : 0 < Real.log (47/46) := Real.log_pos (by norm_num)
  positivity

private theorem contourLogDerivBound_pos : 0 < contourLogDerivBound := by
  unfold contourLogDerivBound
  positivity [logDerivDiskFactor_pos]

private theorem contour_log_lower {q : ℕ} [NeZero q] (t : ℝ) :
    Real.log 2 ≤ Real.log ((q : ℝ) * (2 + |t|)) := by
  apply Real.log_le_log (by norm_num)
  have hq : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q from q.pos_of_neZero)
  exact (le_add_of_nonneg_right (abs_nonneg t)).trans (le_mul_of_one_le_left (by positivity) hq)

private theorem absorb_regularized_bound {L : ℝ} (hL : Real.log 2 ≤ L) :
    logDerivDiskFactor * (11 * L) + 2 ≤ contourLogDerivBound * L := by
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hadd : 2 ≤ (2 / Real.log 2) * L := by
    calc (2:ℝ) = (2 / Real.log 2) * Real.log 2 := (div_mul_cancel₀ _ hpos.ne').symm
         _ ≤ _ := mul_le_mul_of_nonneg_left hL (by positivity)
  dsimp only [contourLogDerivBound]
  linarith only [hadd]

private theorem disk_factor_of_separation {u : ℝ} (hu : 0 ≤ u) :
    1440 + (1440 * Real.log 48 + u) / Real.log (47/46) ≤ logDerivDiskFactor * (1+u) := by
  have hd : 0 < Real.log (47/46) := Real.log_pos (by norm_num)
  have hl : 0 ≤ Real.log 48 := Real.log_nonneg (by norm_num)
  have hbase : 1440 + (1440 * Real.log 48) / Real.log (47/46) ≤ logDerivDiskFactor := by
    unfold logDerivDiskFactor
    gcongr
    linarith
  have hinv : 1 / Real.log (47/46) ≤ logDerivDiskFactor := by
    unfold logDerivDiskFactor
    have : 1 / Real.log (47/46) ≤ (1440 * Real.log 48 + 4) / Real.log (47/46) :=
      div_le_div_of_nonneg_right (by linarith) hd.le
    linarith
  calc
    _ = (1440 + (1440 * Real.log 48) / Real.log (47/46)) +
      (1 / Real.log (47/46)) * u := by ring
    _ ≤ logDerivDiskFactor + logDerivDiskFactor * u := by
      exact add_le_add hbase (mul_le_mul_of_nonneg_right hinv hu)
    _ = _ := by ring

private theorem absorb_horizontal_bound {L u : ℝ} (hL : Real.log 2 ≤ L) (hu : 0 ≤ u) :
    (1440 + (1440 * Real.log 48 + u) / Real.log (47/46)) * (11 * L) + 1 ≤
      contourLogDerivBound * (1+u) * L := by
  have hL0 : 0 ≤ L := (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)).trans hL
  calc
    _ ≤ (logDerivDiskFactor * (1+u)) * (11*L) + 1 := by
      exact add_le_add (mul_le_mul_of_nonneg_right (disk_factor_of_separation hu) (by positivity : 0 ≤ 11*L)) le_rfl
    _ ≤ (logDerivDiskFactor * (11*L) + 2) * (1+u) := by linarith
    _ ≤ (contourLogDerivBound * L) * (1+u) :=
      mul_le_mul_of_nonneg_right (absorb_regularized_bound hL) (by positivity)
    _ = _ := by ring

/-- The left contour estimate, including the primitive principal character. -/
private theorem primitive_logDeriv_left {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (s : ℂ) (hs : s.re = 1/4)
    (hGRH : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → χ.LFunction ρ = 0 → ρ.re = 1/2) :
    ‖logDeriv χ.LFunction s‖ ≤ contourLogDerivBound * Real.log ((q : ℝ) * (2 + |s.im|)) := by
  have habs := absorb_regularized_bound (contour_log_lower (q := q) s.im)
  by_cases hχ : χ = 1
  · subst χ
    have hc : (1 : DirichletCharacter ℂ q).conductor = q := hprim
    have hq : q = 1 := by simpa only [DirichletCharacter.conductor_one] using hc.symm
    subst q
    simp only [DirichletCharacter.LFunction_modOne_eq, Nat.cast_one, one_mul] at *
    have h := zeta_logDeriv_quarter_line s hs hGRH
    exact h.trans ((add_le_add le_rfl (by norm_num : (4:ℝ)/3 ≤ 2)).trans habs)
  · have heq : (⟨1/4,s.im⟩ : ℂ) = s := Complex.ext hs.symm rfl
    have h := nonprincipal_quarter_line_logDeriv χ hχ s.im hGRH
    rw [heq] at h
    apply h.trans (le_trans _ habs)
    change logDerivDiskFactor * (9 * _) ≤ logDerivDiskFactor * (11 * _) + 2
    have hl := (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)).trans (contour_log_lower (q:=q) s.im)
    nlinarith [mul_nonneg logDerivDiskFactor_pos.le hl]

/-- At a height separated from every zero ordinate, the logarithmic derivative
is uniformly bounded for every primitive character on the horizontal edge. -/
private theorem primitive_logDeriv_horizontal {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (s : ℂ) (hs₀ : 1/4 ≤ s.re) (hs₁ : s.re ≤ 2)
    (ht : 1 ≤ |s.im|) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → χ.LFunction ρ = 0 → δ ≤ |s.im - ρ.im|) :
    ‖logDeriv χ.LFunction s‖ ≤
      contourLogDerivBound * (1 + 1/δ) * Real.log ((q : ℝ) * (2 + |s.im|)) := by
  have habs := absorb_horizontal_bound (contour_log_lower (q := q) s.im) (by positivity : 0 ≤ 1/δ)
  by_cases hχ : χ = 1
  · subst χ
    have hc : (1 : DirichletCharacter ℂ q).conductor = q := hprim
    have hq : q = 1 := by simpa only [DirichletCharacter.conductor_one] using hc.symm
    subst q
    simp only [DirichletCharacter.LFunction_modOne_eq, Nat.cast_one, one_mul] at *
    exact (zeta_logDeriv_horizontal s hs₀ hs₁ ht hδ hsep).trans habs
  · have h := nonprincipal_strip_logDeriv_of_separation χ hχ s hs₀ hs₁ hδ
      (fun ρ h₀ h₁ hL => (hsep ρ h₀ h₁ hL).trans
        (by simpa only [Complex.sub_im] using Complex.abs_im_le_norm (s-ρ)))
    apply h.trans (le_trans _ habs)
    have hp : 0 ≤ 1440 + (1440 * Real.log 48 + 1/δ) / Real.log (47/46) := by
      have : 0 < Real.log (47/46) := Real.log_pos (by norm_num)
      positivity
    have hl := (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)).trans (contour_log_lower (q:=q) s.im)
    nlinarith [mul_nonneg hp hl]

end

section

open Complex MeasureTheory
open scoped Interval

/-- Passing from the normalized rectangular residue identity to the sharp
sum. The vertical integrals use the real height parameter on both sides.
The horizontal bounds are for integration in the real direction. -/
private theorem sharp_sum_error_of_rectangle (F : ℂ → ℂ) (principal : Prop) [Decidable principal]
    {x sharp : ℂ} {a b u v S R A B : ℝ}
    (hsharp : sharp = (1 / (2 * Real.pi) : ℝ) •
      ∫ t : ℝ, F ((b : ℂ) + (t : ℂ) * I))
    (hres : ‖rectangleBoundary a b u v F / (2 * Real.pi * I) -
      (if principal then x + 1/2 else 0)‖ ≤ S)
    (htail : ‖(∫ t : ℝ, F ((b : ℂ) + (t : ℂ) * I)) -
      (∫ t : ℝ in u..v, F ((b : ℂ) + (t : ℂ) * I))‖ ≤ R)
    (hleft : ‖∫ t : ℝ in u..v, F ((a : ℂ) + (t : ℂ) * I)‖ ≤ A)
    (hbot : ‖∫ s : ℝ in a..b, F ((s : ℂ) + (u : ℂ) * I)‖ ≤ B)
    (htop : ‖∫ s : ℝ in a..b, F ((s : ℂ) + (v : ℂ) * I)‖ ≤ B) :
    ‖sharp - (if principal then x else 0)‖ ≤ S + R + A + 2*B + 1 := by
  let W := ∫ t : ℝ, F ((b : ℂ) + (t : ℂ) * I)
  let V (s : ℝ) := ∫ t : ℝ in u..v, F ((s : ℂ) + (t : ℂ) * I)
  let H (t : ℝ) := ∫ s : ℝ in a..b, F ((s : ℂ) + (t : ℂ) * I)
  let N := rectangleBoundary a b u v F / (2 * Real.pi * I)
  let m : ℂ := if principal then x+1/2 else 0
  let m₀ : ℂ := if principal then x else 0
  have hrect : rectangleBoundary a b u v F = H u - H v + I * V b - I * V a := rfl
  have hc : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hN : 1 ≤ ‖(2 * Real.pi * I : ℂ)‖ := by
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    linarith [Real.pi_gt_three]
  have he : sharp - N = (I * (W - V b) + I * V a - H u + H v) / (2 * Real.pi * I) := by
    rw [hsharp]
    change (1 / (2 * Real.pi) : ℝ) • W - rectangleBoundary a b u v F / _ = _
    rw [hrect,Complex.real_smul]
    push_cast
    field_simp [hc,I_ne_zero]
    ring
  change ‖W - V b‖ ≤ R at htail
  change ‖V a‖ ≤ A at hleft
  change ‖H u‖ ≤ B at hbot
  change ‖H v‖ ≤ B at htop
  have hgap : ‖sharp-N‖ ≤ R + A + 2*B := by
    rw [he,norm_div]
    apply (div_le_self (norm_nonneg _) hN).trans
    have h₁ := norm_add_le (I * (W-V b)) (I * V a)
    have h₂ := norm_sub_le (I * (W-V b) + I * V a) (H u)
    have h₃ := norm_add_le (I * (W-V b) + I * V a - H u) (H v)
    simp only [norm_mul,Complex.norm_I,one_mul] at h₁
    linarith
  have hmid : ‖m - m₀‖ ≤ 1 := by
    by_cases hp : principal <;> norm_num [m,m₀,hp]
  change ‖N-m‖ ≤ S at hres
  change ‖sharp - m₀‖ ≤ _
  have h₁ := norm_add_le (sharp-N) (N-m)
  have h₂ := norm_add_le (sharp-N+(N-m)) (m-m₀)
  rw [show sharp-N+(N-m)+(m-m₀) = sharp-m₀ by abel] at h₂
  linarith

end

section

/-- Choose both horizontal edges of a Perron rectangle, bound the logarithmic
derivative there, and bound it on the entire intervening left edge. -/
private theorem primitive_good_contour {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (T : ℝ) (hT : 2 ≤ T)
    (hGRH : ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.re = 1/2) :
    let D := 10 / Real.log (23/22)
    let Y := Real.log ((q : ℝ) * (2 + (T+1)))
    ∃ u ∈ Set.Icc (-T-1) (-T), ∃ v ∈ Set.Icc T (T+1),
      (∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → χ.LFunction ρ = 0 → ρ.im ≠ u ∧ ρ.im ≠ v) ∧
      (∀ s : ℂ, 1/4 ≤ s.re → s.re ≤ 2 → (s.im = u ∨ s.im = v) →
        ‖logDeriv χ.LFunction s‖ ≤ contourLogDerivBound * (1 + 3*(D*Y+1)) * Y) ∧
      (∀ s : ℂ, s.re = 1/4 → s.im ∈ Set.Icc u v →
        ‖logDeriv χ.LFunction s‖ ≤ contourLogDerivBound * Y) := by
  let D := 10 / Real.log (23/22)
  let Y := Real.log ((q : ℝ) * (2 + (T+1)))
  let δ := 1 / (3 * (D*Y+1))
  have hD : 0 < D := div_pos (by norm_num) (Real.log_pos (by norm_num))
  have hq : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q from q.pos_of_neZero)
  have hY : 0 ≤ Y := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq (by linarith))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hlog (t : ℝ) (ht : |t| ≤ T+1) : Real.log ((q : ℝ) * (2+|t|)) ≤ Y := by
    apply Real.log_le_log (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  have good (a : ℝ) (ha : |a+1/2| ≤ T+1) :
      ∃ t ∈ Set.Icc a (a+1), ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → χ.LFunction ρ = 0 →
        δ ≤ |t-ρ.im| := by
    obtain ⟨t, ht, hsep⟩ := primitive_good_height χ hprim a hGRH
    refine ⟨t, ht, fun ρ h₀ h₁ hL => le_trans ?_ (hsep ρ h₀ h₁ hL)⟩
    have hl : 0 ≤ Real.log ((q : ℝ) * (2 + |a+1/2|)) :=
      Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq (by linarith [abs_nonneg (a+1/2)]))
    change 1 / (3 * (D*Y+1)) ≤ 1 / (3 * (D * Real.log ((q:ℝ)*(2+|a+1/2|)) + 1))
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
    exact hlog _ ha
  obtain ⟨u, hu', hus⟩ := good (-T-1) (by rw [abs_le]; constructor <;> linarith)
  obtain ⟨v, hv, hvs⟩ := good T (by rw [abs_le]; constructor <;> linarith)
  have hu : u ∈ Set.Icc (-T-1) (-T) := by simpa using hu'
  refine ⟨u, hu, v, hv, ?_, ?_, ?_⟩
  · intro ρ h₀ h₁ hL
    have h₁' := hus ρ h₀ h₁ hL
    have h₂' := hvs ρ h₀ h₁ hL
    constructor
    · intro he
      simp [he] at h₁'
      linarith
    · intro he
      simp [he] at h₂'
      linarith
  · intro s hs₀ hs₁ he
    have hb : 1 ≤ |s.im| ∧ |s.im| ≤ T+1 := by
      rcases he with he | he
      · rw [he, abs_of_nonpos (by linarith [hu.2])]
        exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
      · rw [he, abs_of_nonneg (by linarith [hv.1])]
        exact ⟨by linarith [hv.1], hv.2⟩
    have hsep (ρ : ℂ) (h₀ : 0 < ρ.re) (h₁ : ρ.re < 1) (hL : χ.LFunction ρ = 0) :
        δ ≤ |s.im - ρ.im| := by
      rcases he with he | he
      · simpa only [he] using hus ρ h₀ h₁ hL
      · simpa only [he] using hvs ρ h₀ h₁ hL
    have h := primitive_logDeriv_horizontal χ hprim s hs₀ hs₁ hb.1 hδ hsep
    have hdiv : 1 / δ = 3 * (D*Y+1) := by simp [δ]
    rw [hdiv] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hlog _ hb.2) (by positivity [contourLogDerivBound_pos]))
  · intro s hs him
    have hti : |s.im| ≤ T+1 := abs_le.mpr ⟨by linarith [hu.1, him.1], him.2.trans hv.2⟩
    exact (primitive_logDeriv_left χ hprim s hs hGRH).trans
      (mul_le_mul_of_nonneg_left (hlog _ hti) contourLogDerivBound_pos.le)

end

section

/-- The three logarithms produced by the contour of height `x³+1`
are controlled by the same logarithm as the progression estimate. -/
private theorem contour_scale_logs (q x : ℝ) (hq : 1 ≤ q) (hx : 2 ≤ x) :
    let H := x^3 + 1
    let L := Real.log (2*q*x)
    1 ≤ L ∧ Real.log (2*q*H) ≤ 3*L ∧ Real.log (q*(2+H)) ≤ 3*L ∧
      Real.log (1+H) ≤ 3*L := by
  dsimp only
  have hx1 : 1 ≤ x := by linarith
  have hq0 : 0 < q := by linarith
  have hx0 : 0 < x := by linarith
  have h3 : 1 ≤ x^3 := one_le_pow₀ hx1
  have hq3 : q ≤ q^3 := calc
    q = q * 1 := (mul_one q).symm
    _ ≤ q * q^2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hq) hq0.le
    _ = q^3 := by ring
  have hcap : 4*q*x^3 ≤ (2*q*x)^3 := calc
    _ ≤ 8*q^3*x^3 := by gcongr; norm_num
    _ = _ := by ring
  have hlog (y : ℝ) (hy : 0 < y) (hycap : y ≤ 4*q*x^3) :
      Real.log y ≤ 3*Real.log (2*q*x) := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hy (hycap.trans hcap)
  have hfour : 4 ≤ 2*q*x := by
    calc (4:ℝ) = 2*1*2 := by norm_num
         _ ≤ _ := by gcongr
  have hLL := Real.log_le_log (by norm_num : (0:ℝ)<4) hfour
  rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow] at hLL
  norm_num at hLL
  refine ⟨by linarith only [Real.log_two_gt_d9, hLL], ?_, ?_, ?_⟩
  · apply hlog _ (by positivity)
    calc 2*q*(x^3+1) ≤ 2*q*(2*x^3) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
         _ = _ := by ring
  · apply hlog _ (by positivity)
    calc q*(2+(x^3+1)) ≤ q*(4*x^3) := mul_le_mul_of_nonneg_left (by linarith) hq0.le
         _ = _ := by ring
  · apply hlog _ (by positivity)
    calc 1+(x^3+1) ≤ 4*x^3 := by linarith
         _ ≤ 4*q*x^3 := by gcongr; linarith

/-- Algebraic comparisons for the step of length one and the cubic truncation height. -/
private theorem contour_scale_powers (x : ℝ) (hx : 2 ≤ x) :
    1 ≤ Real.sqrt x ∧ Real.sqrt (x+1) ≤ 2*Real.sqrt x ∧
    (x+1)^(1/4 : ℝ) ≤ 2*Real.sqrt x ∧ (x+1)^2/x^3 ≤ 4 ∧
    ((x+1)^3 + x^3) / x^3 ≤ 9 := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hroot : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt hx1
  have hroot' : Real.sqrt (x+1) ≤ 2*Real.sqrt x := by
    calc _ ≤ Real.sqrt (4*x) := Real.sqrt_le_sqrt (by linarith)
         _ = _ := by rw [Real.sqrt_mul (by norm_num)]; norm_num
  have hh : x+1 ≤ 2*x := by linarith
  refine ⟨hroot, hroot', ?_, ?_, ?_⟩
  · apply le_trans _ hroot'
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  · apply (div_le_iff₀ (pow_pos hx0 3)).2
    calc
      _ ≤ (2*x)^2 := by gcongr
      _ = 4*x^2 := by ring
      _ ≤ (4*x^2)*x := le_mul_of_one_le_right (by positivity) hx1
      _ = _ := by ring
  · apply (div_le_iff₀ (pow_pos hx0 3)).2
    calc
      _ ≤ (2*x)^3 + x^3 := by gcongr
      _ = _ := by ring

/-- A single constant for the contributions of the three displaced contour
edges, the zero sum, the two right tails, and the additive unit error. -/
private def contourScaleConstant (K D E B : ℝ) : ℝ :=
  1 + 180*K + 48*K*(4+9*D) + 18*E + 18*B

private theorem contourScaleConstant_pos {K D E B : ℝ}
    (hK : 0 ≤ K) (hD : 0 ≤ D) (hE : 0 ≤ E) (hB : 0 ≤ B) :
    0 < contourScaleConstant K D E B := by unfold contourScaleConstant; positivity

private theorem contour_scale_total (K D E B q x : ℝ) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hE : 0 ≤ E) (hB : 0 ≤ B) (hq : 1 ≤ q) (hx : 2 ≤ x) :
    let T := x^3
    let H := T+1
    let Y := Real.log (q*(2+H))
    let Z := Real.log (2*q*H)
    let L := Real.log (2*q*x)
    5*(K*Y)*(x+1)^(1/4:ℝ)*(2*Real.log (1+H)) +
        2*(2*K*(1+3*(D*Y+1))*Y*(x+1)^2/T) +
        Real.sqrt (x+1)*E*Z^2 + 2*B*((x+1)^3+x^3)/T + 1 ≤
      contourScaleConstant K D E B * Real.sqrt x * L^2 := by
  intro T H Y Z L
  obtain ⟨hL, hZ, hY, hlogH⟩ := contour_scale_logs q x hq hx
  obtain ⟨hr, hsqrt, hpow, hr2, hr3⟩ := contour_scale_powers x hx
  change 1 ≤ L at hL
  change Z ≤ 3*L at hZ
  change Y ≤ 3*L at hY
  change Real.log (1+H) ≤ 3*L at hlogH
  have hx0 : 0 ≤ x := by linarith
  have hH : 1 ≤ H := by dsimp [H,T]; linarith [pow_nonneg hx0 3]
  have hY0 : 0 ≤ Y := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq (by linarith))
  have hZ0 : 0 ≤ Z := Real.log_nonneg (one_le_mul_of_one_le_of_one_le (by linarith) hH)
  have hlog0 : 0 ≤ Real.log (1+H) := Real.log_nonneg (by linarith)
  have hL0 : 0 ≤ L := by linarith
  let V := Real.sqrt x * L^2
  have hV : 1 ≤ V := one_le_mul_of_one_le_of_one_le hr (one_le_pow₀ hL)
  have hSV : L^2 ≤ V := le_mul_of_one_le_left (sq_nonneg _) hr
  have hleft : 5*(K*Y)*(x+1)^(1/4:ℝ)*(2*Real.log (1+H)) ≤ 180*K*V := calc
    _ ≤ 5*(K*(3*L))*(2*Real.sqrt x)*(2*(3*L)) := by gcongr
    _ = _ := by dsimp [V]; ring
  have hweight : 1+3*(D*Y+1) ≤ (4+9*D)*L := by
    have hw := mul_le_mul_of_nonneg_left hY hD
    linarith
  have hedge : 2*K*(1+3*(D*Y+1))*Y*(x+1)^2/T ≤ 24*K*(4+9*D)*V := calc
    _ = 2*K*(1+3*(D*Y+1))*Y*((x+1)^2/T) := by ring
    _ ≤ 2*K*((4+9*D)*L)*(3*L)*4 := by
      gcongr
    _ = 24*K*(4+9*D)*L^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hSV (by positivity)
  have hzeros : Real.sqrt (x+1)*E*Z^2 ≤ 18*E*V := calc
    _ ≤ (2*Real.sqrt x)*E*(3*L)^2 := by gcongr
    _ = _ := by dsimp [V]; ring
  have hright : 2*B*((x+1)^3+x^3)/T ≤ 18*B*V := calc
    _ = 2*B*(((x+1)^3+x^3)/T) := by ring
    _ ≤ 2*B*9 := mul_le_mul_of_nonneg_left hr3 (by positivity)
    _ = 18*B := by ring
    _ ≤ _ := le_mul_of_one_le_right (by positivity) hV
  rw [mul_assoc (contourScaleConstant K D E B)]
  change _ ≤ contourScaleConstant K D E B * V
  unfold contourScaleConstant
  linarith only [hleft, hedge, hzeros, hright, hV]

end

section

open Complex ArithmeticFunction DirichletCharacter MeasureTheory Filter
open scoped BigOperators Topology

private noncomputable def negLogL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  -deriv χ.LFunction s / χ.LFunction s

private noncomputable def rightLineBound : ℝ :=
  ∑' n : ℕ, ‖LSeries.term (fun k => (vonMangoldt k : ℂ)) 2 n‖

private theorem rightLineBound_nonneg : 0 ≤ rightLineBound := tsum_nonneg fun _ => norm_nonneg _

private theorem negLogL_bound_right {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : s.re = 2) : ‖negLogL χ s‖ ≤ rightLineBound := by
  have h : 1 < s.re := by linarith
  rw [negLogL, deriv_LFunction_eq_deriv_LSeries χ h, LFunction_eq_LSeries χ h,
    ← LSeries_twist_vonMangoldt_eq χ h]
  apply (norm_tsum_le_tsum_norm (LSeriesSummable_twist_vonMangoldt χ h).norm).trans
  apply Summable.tsum_le_tsum _ (LSeriesSummable_twist_vonMangoldt χ h).norm
    (LSeriesSummable_vonMangoldt (s := 2) (by norm_num)).norm
  intro n
  simp only [LSeries.norm_term_eq, hs, Complex.re_ofNat]
  split_ifs
  · rfl
  · apply div_le_div_of_nonneg_right _ (by positivity)
    change ‖χ (n : ZMod q) * (vonMangoldt n : ℂ)‖ ≤ ‖(vonMangoldt n : ℂ)‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

private noncomputable def verticalPoint (σ t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * I

private theorem continuous_verticalPoint (σ : ℝ) : Continuous (verticalPoint σ) :=
  continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

set_option maxHeartbeats 1000000 in
private theorem negLogL_continuous_right {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Continuous (fun t : ℝ => negLogL χ (verticalPoint 2 t)) := by
  let U := ({1}ᶜ : Set ℂ)
  have ha : AnalyticOnNhd ℂ χ.LFunction U :=
    (show DifferentiableOn ℂ χ.LFunction U from fun w hw =>
      (differentiableAt_LFunction χ w (.inl hw)).differentiableWithinAt).analyticOnNhd
      isOpen_compl_singleton
  apply continuous_iff_continuousAt.mpr
  intro t
  let s := verticalPoint 2 t
  have hre : s.re = 2 := by simp [s, verticalPoint]
  have hs : s ≠ 1 := by intro he; simp [he] at hre
  have hn := LFunction_ne_zero_of_one_le_re χ (s := s) (Or.inr hs) (by linarith)
  have h : AnalyticAt ℂ χ.LFunction s := ha s hs
  have hC : ContinuousAt (fun w => -deriv χ.LFunction w / χ.LFunction w) s :=
    h.deriv.continuousAt.neg.div h.continuousAt hn
  exact ContinuousAt.comp (x := t) hC (continuous_verticalPoint 2).continuousAt

private theorem right_denominator (t : ℝ) :
    1 + t ^ 2 ≤ ‖verticalPoint 2 t‖ * ‖verticalPoint 2 t + 1‖ := by
  let s := verticalPoint 2 t
  have ha : ‖s‖^2 = 2*2 + t*t := by
    simpa [s, verticalPoint, Complex.normSq_apply] using Complex.sq_norm s
  have hb : ‖s+1‖^2 = (2+1)*(2+1) + t*t := by
    simpa [s, verticalPoint, Complex.normSq_apply] using Complex.sq_norm (s+1)
  have h : ‖s‖ ≤ ‖s+1‖ := by nlinarith [norm_nonneg (s+1)]
  change _ ≤ ‖s‖ * ‖s+1‖
  nlinarith [mul_le_mul_of_nonneg_left h (norm_nonneg s)]

private noncomputable def perronTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (x t : ℝ) : ℂ :=
  let s := verticalPoint 2 t
  negLogL χ s * (x : ℂ) ^ (s + 1) / (s * (s+1))

private theorem perronTerm_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖perronTerm χ x t‖ ≤ (rightLineBound * x^3) * (1 + t^2)⁻¹ := by
  let s := verticalPoint 2 t
  have hs : s.re = 2 := by simp [s, verticalPoint]
  have hn := negLogL_bound_right χ hs
  have hd := right_denominator t
  change 1 + t^2 ≤ ‖s‖ * ‖s+1‖ at hd
  simp only [perronTerm, ← show s = verticalPoint 2 t from rfl, norm_div, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.add_re, Complex.one_re, hs]
  norm_num
  rw [← div_eq_mul_inv]
  apply div_le_div₀ (by positivity [rightLineBound_nonneg]) _ (by positivity) hd
  exact mul_le_mul_of_nonneg_right hn (by positivity)

private theorem perronTerm_integrable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) : Integrable (perronTerm χ x) := by
  apply (integrable_inv_one_add_sq.const_mul (rightLineBound * x^3)).mono'
  · unfold perronTerm
    have h := (negLogL_continuous_right χ).measurable
    have v := (continuous_verticalPoint 2).measurable
    have hw : Measurable (fun t : ℝ => (x : ℂ) ^ (verticalPoint 2 t + 1)) := by
      unfold verticalPoint
      fun_prop
    exact ((h.mul hw).div
      (v.mul (v.add measurable_const))).aestronglyMeasurable
  exact Eventually.of_forall (perronTerm_bound χ hx)

private theorem cutoff_perronTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (X : ℕ) (hX : 0 < X) :
    triangularTwist χ X = (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, perronTerm χ X t := by
  rw [triangularTwist_eq_mellinInv χ X hX, mellinInv, mul_smul_comm,
    ← integral_const_mul]
  apply congrArg (fun w : ℂ => (1 / (2 * Real.pi) : ℝ) • w)
  apply integral_congr_ae
  filter_upwards with t
  let s := verticalPoint 2 t
  change (X : ℂ) * (((1 / (X : ℝ) : ℝ) : ℂ) ^ (-s) *
    (negLogL χ s * (1 / (s * (s+1))))) = _
  have hxc : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  rw [one_div, Complex.ofReal_inv, Complex.cpow_neg,
    Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg X), Complex.ofReal_natCast]
  unfold perronTerm
  change _ = negLogL χ s * (X : ℂ) ^ (s+1) / _
  rw [Complex.cpow_add _ _ hxc, Complex.cpow_one]
  simp only [inv_inv]
  ring

/-- On the line of absolute convergence the sharp sum is exactly the
integral of the unit difference kernel times the logarithmic derivative. -/
private theorem unit_perron_line_integral {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (X : ℕ) (hX : 0 < X) :
    (∑ n ∈ Finset.range (X+1), χ (n : ZMod q) * (vonMangoldt n : ℂ)) =
      (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        negLogL χ (verticalPoint 2 t) * unitPerronKernel X (verticalPoint 2 t) := by
  rw [← triangularTwist_unit_difference, cutoff_perronTerm χ _ (by omega),
    cutoff_perronTerm χ _ hX, ← smul_sub, ← integral_sub
      (perronTerm_integrable χ (by exact_mod_cast Nat.succ_pos X))
      (perronTerm_integrable χ (by exact_mod_cast hX))]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  simp only [perronTerm, unitPerronKernel, Nat.cast_add, Nat.cast_one, Complex.ofReal_add,
    Complex.ofReal_natCast, Complex.ofReal_one]
  ring

private theorem right_tail_one_side (F : ℝ → ℂ) {D c : ℝ} (hD : 0 ≤ D) (hc : 0 < c)
    (hF : ∀ t, ‖F t‖ ≤ D * (1+t^2)⁻¹) :
    ‖∫ t in Set.Ioi c, F t‖ ≤ D/c := by
  have hi := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hc).const_mul D
  calc
    _ ≤ ∫ t in Set.Ioi c, D * (t ^ (-2 : ℝ)) := by
      apply MeasureTheory.norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht' : 0 < t := hc.trans ht
      apply (hF t).trans
      apply mul_le_mul_of_nonneg_left _ hD
      rw [Real.rpow_neg ht'.le]
      norm_num only [Real.rpow_two]
      exact inv_anti₀ (sq_pos_of_pos ht') (by linarith)
    _ = D/c := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hc]
      norm_num [div_eq_mul_inv, Real.rpow_neg_one]

/-- The integral outside a finite segment on the line of convergence has
an explicit reciprocal-height error at both ends. -/
private theorem right_line_truncation {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x u v T : ℝ} (hx : 0 < x) (hT : 0 < T) (hu : u ≤ -T) (hv : T ≤ v) :
    let F := fun t : ℝ => negLogL χ (verticalPoint 2 t) * unitPerronKernel x (verticalPoint 2 t)
    ‖(∫ t : ℝ, F t) - ∫ t in u..v, F t‖ ≤ 2 * rightLineBound * ((x+1)^3 + x^3) / T := by
  let F := fun t : ℝ => negLogL χ (verticalPoint 2 t) * unitPerronKernel x (verticalPoint 2 t)
  let D := rightLineBound * ((x+1)^3+x^3)
  have hD : 0 ≤ D := by dsimp only [D]; positivity [rightLineBound_nonneg]
  have he : F = fun t : ℝ => perronTerm χ (x+1) t - perronTerm χ x t := by
    funext t
    simp only [F, unitPerronKernel, perronTerm]
    ring
  have hF : ∀ t, ‖F t‖ ≤ D * (1+t^2)⁻¹ := by
    intro t
    rw [he]
    apply (norm_sub_le _ _).trans
    calc
      _ ≤ (rightLineBound * (x+1)^3) * (1+t^2)⁻¹ + (rightLineBound*x^3) * (1+t^2)⁻¹ := by
        exact add_le_add (perronTerm_bound χ (by linarith) t) (perronTerm_bound χ hx t)
      _ = _ := by dsimp only [D]; ring
  have hi : Integrable F := by
    rw [he]
    exact (perronTerm_integrable χ (by linarith)).sub (perronTerm_integrable χ hx)
  have hlo : ‖∫ t in Set.Iic u, F t‖ ≤ D/T := by
    have hn (t : ℝ) : ‖F (-t)‖ ≤ D*(1+t^2)⁻¹ := by simpa using hF (-t)
    have h := right_tail_one_side (fun t => F (-t)) hD (show 0 < -u by linarith) hn
    rw [integral_comp_neg_Ioi, neg_neg] at h
    exact h.trans (div_le_div_of_nonneg_left hD hT (by linarith))
  have hhi : ‖∫ t in Set.Ioi v, F t‖ ≤ D/T :=
    (right_tail_one_side F hD (hT.trans_le hv) hF).trans
      (div_le_div_of_nonneg_left hD hT hv)
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (b := v) hi.integrableOn hi.integrableOn
  have hfinite := intervalIntegral.integral_Iic_sub_Iic (a := u) (b := v)
    hi.integrableOn hi.integrableOn
  change ‖(∫ t : ℝ, F t) - ∫ t in u..v, F t‖ ≤ _
  rw [← hsplit, ← hfinite, show (∫ t in Set.Iic v, F t) + (∫ t in Set.Ioi v, F t) -
       ((∫ t in Set.Iic v, F t) - ∫ t in Set.Iic u, F t) =
       (∫ t in Set.Iic u, F t) + ∫ t in Set.Ioi v, F t by ring]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ D/T + D/T := by exact add_le_add hlo hhi
    _ = _ := by dsimp only [D]; ring

end

section

open Complex MeasureTheory Set DirichletCharacter
open scoped BigOperators Classical Interval

/-- A uniform bound for the sharp von Mangoldt sum twisted by a primitive
character, assuming GRH for that character. -/
private theorem primitive_twisted_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (X : ℕ) (hX : 2 ≤ X)
    (hGRH : ∀ z : ℂ, 0 < z.re → z.re < 1 → χ.LFunction z = 0 → z.re = 1/2) :
    ‖twistedError X χ‖ ≤
      contourScaleConstant contourLogDerivBound (10 / Real.log (23/22))
        (120 / Real.log (23/22)) rightLineBound *
      Real.sqrt X * (Real.log (2 * (q : ℝ) * X))^2 := by
  let x : ℝ := X
  let T := x^3
  let H := T+1
  let K := contourLogDerivBound
  let D := 10 / Real.log (23/22)
  let E := 120 / Real.log (23/22)
  let Y := Real.log ((q : ℝ)*(2+H))
  let M := K*(1+3*(D*Y+1))*Y
  let G := fun s : ℂ => -logDeriv χ.LFunction s
  let F := fun s : ℂ => G s * unitPerronKernel x s
  have hx : 2 ≤ x := by dsimp only [x]; exact_mod_cast hX
  have hx0 : 0 < x := by linarith
  have hT : 2 ≤ T := by dsimp [T]; nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ x-2 by linarith)]
  have hTp : 0 < T := by linarith
  have hH : 2 ≤ H := by dsimp [H]; linarith
  have hK : 0 ≤ K := contourLogDerivBound_pos.le
  have hD : 0 ≤ D := div_nonneg (by norm_num) (Real.log_nonneg (by norm_num))
  have hE : 0 ≤ E := div_nonneg (by norm_num) (Real.log_nonneg (by norm_num))
  have hq : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q from q.pos_of_neZero)
  have hY : 0 ≤ Y := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq (by linarith))
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  obtain ⟨u,hu,v,hv,hsafe,hhor,hvert⟩ := primitive_good_contour χ hprim T hT hGRH
  have hu0 : u < 0 := by linarith [hu.2]
  have hv0 : 0 < v := by linarith [hv.1]
  have huH : |u| ≤ H := by rw [abs_of_neg hu0]; dsimp only [H]; linarith [hu.1]
  have huH' : -H ≤ u := by linarith [(abs_le.mp huH).1]
  have hvH : v ≤ H := hv.2
  have hmatch (s : ℂ) : negLogL χ s = G s := by simp [negLogL,G,logDeriv_apply,neg_div]
  have hsharp := unit_perron_line_integral χ X (by omega)
  simp only [hmatch] at hsharp
  have htail := right_line_truncation χ hx0 hTp hu.2 hv.1
  dsimp only at htail
  simp only [hmatch] at htail
  have hres := primitive_unitPerron_rectangle_error χ hprim (a := 1/4) (b := 2) hx0
    (by norm_num) (by norm_num) (by norm_num) hu0 hv0 hH huH' hvH hGRH hsafe
  have hleft := unit_kernel_left_edge G hx0 hu0.le hv0.le (mul_nonneg hK hY) (by
    intro t ht
    simp only [G,norm_neg]
    apply hvert
    · norm_num
    · simpa using ht)
  have hlogu := Real.log_le_log (show 0 < 1+|u| by positivity)
    (show 1+|u| ≤ 1+H by linarith)
  have hlogv := Real.log_le_log (show 0 < 1+v by linarith)
    (show 1+v ≤ 1+H by linarith)
  have hleft' := hleft.trans (mul_le_mul_of_nonneg_left (show
    Real.log (1+|u|) + Real.log (1+v) ≤ 2*Real.log (1+H) by linarith)
    (by positivity))
  have hedges (t : ℝ) (ht : t = u ∨ t = v) (htT : T ≤ |t|) :
      ‖∫ σ : ℝ in (1/4)..2, G ((σ : ℂ) + (t : ℂ) * I) *
        unitPerronKernel x ((σ : ℂ) + (t : ℂ) * I)‖ ≤ 2*M*(x+1)^2/T := by
    have ht0 : t ≠ 0 := abs_pos.mp (hTp.trans_le htT)
    have hh := unit_kernel_horizontal_edge G hx0 ht0 hM (by
      intro σ hσ
      simp only [G,norm_neg]
      apply hhor
      · simpa using hσ.1
      · simpa using hσ.2
      · simpa using ht)
    exact hh.trans (div_le_div_of_nonneg_left (by positivity) hTp htT)
  have hbot := hedges u (.inl rfl) (by rw [abs_of_neg hu0]; linarith [hu.2])
  have htop := hedges v (.inr rfl) (by rw [abs_of_pos hv0]; exact hv.1)
  have hasm := sharp_sum_error_of_rectangle F (χ=1) (a := 1/4) (b := 2) (u := u) (v := v)
    (x := (X : ℂ))
    (sharp := ∑ n ∈ Finset.range (X+1), χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ))
    (by simpa only [F,verticalPoint,x,Complex.ofReal_ofNat] using hsharp)
    (by simpa only [F,G,x,Complex.ofReal_natCast] using hres)
    (by simpa only [F,verticalPoint,Complex.ofReal_ofNat] using htail)
    (by simpa only [F,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using hleft')
    hbot htop
  have hscale := contour_scale_total K D E rightLineBound q x hK hD hE rightLineBound_nonneg hq hx
  have hfinal := hasm.trans (le_trans (by
    apply le_of_eq
    dsimp only [M,K,D,E,Y,H,T,x]
    ring) hscale)
  by_cases hχ : χ = 1 <;> simpa [twistedError,hχ] using hfinal

/-- The GRH progression estimate with a single absolute implied constant. -/
private theorem progression_grh_complete :
    (∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
      0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2) →
    ∃ C : ℝ, 0 < C ∧ ∀ q a X : ℕ, 0 < q → Nat.Coprime a q → 2 ≤ X →
      |(Finset.sum ((Finset.range (X + 1)).filter (fun k => k % q = a % q))
        (fun k => ArithmeticFunction.vonMangoldt k)) - (X : ℝ) / (Nat.totient q : ℝ)| ≤
        C * Real.sqrt (X : ℝ) * (Real.log (2 * (q : ℝ) * (X : ℝ))) ^ 2 := by
  intro hGRH
  apply progression_error_of_primitive_character_error
    (contourScaleConstant contourLogDerivBound (10 / Real.log (23/22))
      (120 / Real.log (23/22)) rightLineBound)
  intro d X hd χ hprim hX
  exact primitive_twisted_bound χ hprim X hX (hGRH d χ)

end

end GoldbachProgression

namespace PEqualNP.Outside

private lemma w11c_mod_sq_add_dvd {r q a : ℕ} :
    q ∣ r ^ 2 + a ↔ q ∣ (r % q) ^ 2 + a := by
  have hdiv : q * (r / q) + r % q = r := Nat.div_add_mod r q
  have h_id : r ^ 2 + a = q * (q * (r / q) ^ 2 + 2 * (r / q) * (r % q)) + ((r % q) ^ 2 + a) := by
    calc r ^ 2 + a = (q * (r / q) + r % q) ^ 2 + a := by rw [hdiv]
      _ = q * (q * (r / q) ^ 2 + 2 * (r / q) * (r % q)) + ((r % q) ^ 2 + a) := by ring
  rw [h_id]
  exact Nat.dvd_add_right (dvd_mul_right q _)

private lemma w11c_fixed_a_core :
    let block := fun x : ℕ => Finset.Ioc x (2*x); let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a); (∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ), 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2) → ∃ C : ℝ, 0<C ∧ ∀ a q x : ℕ, 0<q → Nat.Coprime a q → 2≤x → |(∑ n ∈ (block x).filter (fun n => q ∣ n^2+a), ArithmeticFunction.vonMangoldt n) - ((roots a q).card : ℝ)*x/(Nat.totient q : ℝ)| ≤ C*((roots a q).card : ℝ)*Real.sqrt x*Real.log (4*(q : ℝ)*x)^2 := by
  intro block roots hGRH
  obtain ⟨C₀, hC₀_pos, h_prog⟩ := GoldbachProgression.progression_grh_complete hGRH
  refine ⟨3 * C₀, by positivity, fun a q x hq hcop hx => ?_⟩
  let apSum : ℕ → ℕ → ℝ := fun Y r =>
    ∑ k ∈ (Finset.range (Y + 1)).filter (fun k => k % q = r % q), ArithmeticFunction.vonMangoldt k
  have h_root_cop : ∀ r ∈ roots a q, Nat.Coprime r q := by
    intro r hr
    dsimp only [roots] at hr
    rw [Finset.mem_filter, Finset.mem_range] at hr
    refine Nat.coprime_of_dvd' fun p _hp hp_r hp_q => ?_
    have hp_r2 : p ∣ r ^ 2 := dvd_trans hp_r (dvd_pow_self r (by omega))
    have hp_sum : p ∣ r ^ 2 + a := dvd_trans hp_q hr.2
    have hp_a : p ∣ a := (Nat.dvd_add_right hp_r2).mp hp_sum
    have hg : p ∣ Nat.gcd a q := Nat.dvd_gcd hp_a hp_q
    rwa [hcop.gcd_eq_one] at hg
  have h_decomp : (∑ n ∈ (block x).filter (fun n => q ∣ n ^ 2 + a), ArithmeticFunction.vonMangoldt n) =
      ∑ r ∈ roots a q, (apSum (2 * x) r - apSum x r) := by
    have h_maps : ∀ n ∈ (block x).filter (fun n => q ∣ n ^ 2 + a), n % q ∈ roots a q := by
      intro n hn
      rw [Finset.mem_filter] at hn
      dsimp only [roots]
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.mod_lt n hq, w11c_mod_sq_add_dvd.mp hn.2⟩
    rw [← Finset.sum_fiberwise_of_maps_to h_maps]
    refine Finset.sum_congr rfl fun r hr => ?_
    dsimp only [roots] at hr
    rw [Finset.mem_filter, Finset.mem_range] at hr
    have hr_mod : r % q = r := Nat.mod_eq_of_lt hr.1
    have h_fib : ((block x).filter (fun n => q ∣ n ^ 2 + a)).filter (fun n => n % q = r) =
        (Finset.Ioc x (2 * x)).filter (fun k => k % q = r % q) := by
      ext n
      simp only [block, Finset.mem_filter, Finset.mem_Ioc, hr_mod]
      constructor
      · rintro ⟨⟨hn1, _⟩, hn2⟩
        exact ⟨hn1, hn2⟩
      · rintro ⟨hn1, hn2⟩
        refine ⟨⟨hn1, ?_⟩, hn2⟩
        rw [w11c_mod_sq_add_dvd, hn2]
        exact hr.2
    rw [h_fib]
    have h_union : (Finset.range (2 * x + 1)).filter (fun k => k % q = r % q) =
        (Finset.range (x + 1)).filter (fun k => k % q = r % q) ∪
        (Finset.Ioc x (2 * x)).filter (fun k => k % q = r % q) := by
      ext k
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
      omega
    have h_disj : Disjoint ((Finset.range (x + 1)).filter (fun k => k % q = r % q))
        ((Finset.Ioc x (2 * x)).filter (fun k => k % q = r % q)) := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at hk1 hk2
      omega
    dsimp only [apSum]
    rw [h_union, Finset.sum_union h_disj]
    ring
  rw [h_decomp]
  have h_main_sum : ((roots a q).card : ℝ) * (x : ℝ) / (Nat.totient q : ℝ) =
      ∑ _r ∈ roots a q, (x : ℝ) / (Nat.totient q : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_div_assoc]
  rw [h_main_sum, ← Finset.sum_sub_distrib]
  have hq_real : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hx_real : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have h_term_bound : ∀ r ∈ roots a q,
      |(apSum (2 * x) r - apSum x r) - (x : ℝ) / (Nat.totient q : ℝ)| ≤
        3 * C₀ * Real.sqrt (x : ℝ) * Real.log (4 * (q : ℝ) * (x : ℝ)) ^ 2 := by
    intro r hr
    have hr_cop : Nat.Coprime r q := h_root_cop r hr
    have hb1 := h_prog q r (2 * x) hq hr_cop (by omega)
    have hb2 := h_prog q r x hq hr_cop hx
    change |apSum (2 * x) r - ((2 * x : ℕ) : ℝ) / (Nat.totient q : ℝ)| ≤ _ at hb1
    change |apSum x r - (x : ℝ) / (Nat.totient q : ℝ)| ≤ _ at hb2
    have h_sqrt2 : Real.sqrt ((2 * x : ℕ) : ℝ) ≤ 2 * Real.sqrt (x : ℝ) := by
      push_cast
      rw [Real.sqrt_mul zero_le_two]
      gcongr
      rw [Real.sqrt_le_iff]
      norm_num
    have h_4qx : 2 * (q : ℝ) * ((2 * x : ℕ) : ℝ) = 4 * (q : ℝ) * (x : ℝ) := by
      push_cast; ring
    have hb1' : |apSum (2 * x) r - ((2 * x : ℕ) : ℝ) / (Nat.totient q : ℝ)| ≤
        2 * C₀ * Real.sqrt (x : ℝ) * Real.log (4 * (q : ℝ) * (x : ℝ)) ^ 2 := by
      rw [h_4qx] at hb1
      calc |apSum (2 * x) r - ((2 * x : ℕ) : ℝ) / (Nat.totient q : ℝ)|
        _ ≤ C₀ * Real.sqrt ((2 * x : ℕ) : ℝ) * Real.log (4 * (q : ℝ) * (x : ℝ)) ^ 2 := hb1
        _ ≤ C₀ * (2 * Real.sqrt (x : ℝ)) * Real.log (4 * (q : ℝ) * (x : ℝ)) ^ 2 := by gcongr
        _ = 2 * C₀ * Real.sqrt (x : ℝ) * Real.log (4 * (q : ℝ) * (x : ℝ)) ^ 2 := by ring
    have h_log_mono : Real.log (2 * (q : ℝ) * (x : ℝ)) ^ 2 ≤ Real.log (4 * (q : ℝ) * (x : ℝ)) ^ 2 := by
      have h_le : 2 * (q : ℝ) * (x : ℝ) ≤ 4 * (q : ℝ) * (x : ℝ) := by nlinarith
      have h_lg_nn : 0 ≤ Real.log (2 * (q : ℝ) * (x : ℝ)) :=
        Real.log_nonneg (by nlinarith)
      have h_lg_le : Real.log (2 * (q : ℝ) * (x : ℝ)) ≤ Real.log (4 * (q : ℝ) * (x : ℝ)) :=
        Real.log_le_log (by positivity) h_le
      exact pow_le_pow_left₀ h_lg_nn h_lg_le 2
    have hb2' : |apSum x r - (x : ℝ) / (Nat.totient q : ℝ)| ≤
        C₀ * Real.sqrt (x : ℝ) * Real.log (4 * (q : ℝ) * (x : ℝ)) ^ 2 := by
      calc |apSum x r - (x : ℝ) / (Nat.totient q : ℝ)|
        _ ≤ C₀ * Real.sqrt (x : ℝ) * Real.log (2 * (q : ℝ) * (x : ℝ)) ^ 2 := hb2
        _ ≤ C₀ * Real.sqrt (x : ℝ) * Real.log (4 * (q : ℝ) * (x : ℝ)) ^ 2 := by gcongr
    have h_id_diff : (apSum (2 * x) r - apSum x r) - (x : ℝ) / (Nat.totient q : ℝ) =
        (apSum (2 * x) r - ((2 * x : ℕ) : ℝ) / (Nat.totient q : ℝ)) -
        (apSum x r - (x : ℝ) / (Nat.totient q : ℝ)) := by
      push_cast; ring
    rw [h_id_diff]
    calc |(apSum (2 * x) r - ((2 * x : ℕ) : ℝ) / (Nat.totient q : ℝ)) -
            (apSum x r - (x : ℝ) / (Nat.totient q : ℝ))|
      _ ≤ |apSum (2 * x) r - ((2 * x : ℕ) : ℝ) / (Nat.totient q : ℝ)| +
            |apSum x r - (x : ℝ) / (Nat.totient q : ℝ)| := abs_sub _ _
      _ ≤ 2 * C₀ * Real.sqrt (x : ℝ) * Real.log (4 * (q : ℝ) * (x : ℝ)) ^ 2 +
            C₀ * Real.sqrt (x : ℝ) * Real.log (4 * (q : ℝ) * (x : ℝ)) ^ 2 := add_le_add hb1' hb2'
      _ = 3 * C₀ * Real.sqrt (x : ℝ) * Real.log (4 * (q : ℝ) * (x : ℝ)) ^ 2 := by ring
  calc |∑ r ∈ roots a q, ((apSum (2 * x) r - apSum x r) - (x : ℝ) / (Nat.totient q : ℝ))|
    _ ≤ ∑ r ∈ roots a q, |(apSum (2 * x) r - apSum x r) - (x : ℝ) / (Nat.totient q : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ roots a q, (3 * C₀ * Real.sqrt (x : ℝ) * Real.log (4 * (q : ℝ) * (x : ℝ)) ^ 2) :=
        Finset.sum_le_sum h_term_bound
    _ = ((roots a q).card : ℝ) * (3 * C₀ * Real.sqrt (x : ℝ) * Real.log (4 * (q : ℝ) * (x : ℝ)) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = 3 * C₀ * ((roots a q).card : ℝ) * Real.sqrt (x : ℝ) * Real.log (4 * (q : ℝ) * (x : ℝ)) ^ 2 := by ring

theorem L_quadratic_primes_levent_fixed_a_grh_progression :
    let block := fun x : ℕ => Finset.Ioc x (2*x); let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a); (∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ), 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2) → ∃ C : ℝ, 0<C ∧ ∀ a q x : ℕ, 0<q → Nat.Coprime a q → 2≤x → |(∑ n ∈ (block x).filter (fun n => q ∣ n^2+a), ArithmeticFunction.vonMangoldt n) - ((roots a q).card : ℝ)*x/(Nat.totient q : ℝ)| ≤ C*((roots a q).card : ℝ)*Real.sqrt x*Real.log (4*(q : ℝ)*x)^2 :=
  w11c_fixed_a_core

end PEqualNP.Outside
