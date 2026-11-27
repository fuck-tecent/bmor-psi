import Mathlib

/-!
# The quadratic Gauss sum over `ZMod p` has norm `√p`

For an odd prime `p` and a natural number `a` coprime to `p`, the Fourier sum of the Jacobi
symbol at frequency `a` is the Gauss sum of the quadratic character of `ZMod p`, with the
additive character twisted by the unit `a`.

* At a prime, the Jacobi symbol is the Legendre symbol, which is the quadratic character of
  `ZMod p` (`jacobiSym.legendreSym.to_jacobiSym`).
* The phase `E (b * (a / p))` is the standard additive character `ZMod.stdAddChar` at `a * b`.
* Twisting the additive character by a unit multiplies the Gauss sum by a value of norm `1`
  (`gaussSum_mulShift`).
* `gaussSum_sq`: the square of the Gauss sum is `χ (-1) * p`, and `χ (-1) = 1` or `-1`, so the
  norm squared is `p`.
-/

open MulChar

/-- The quadratic character of `ZMod p`, viewed as a `ℂ`-valued multiplicative character. -/
private def quadCharC (p : ℕ) [Fact p.Prime] : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

private theorem quadCharC_isQuadratic (p : ℕ) [Fact p.Prime] : (quadCharC p).IsQuadratic :=
  MulChar.IsQuadratic.comp (quadraticChar_isQuadratic (F := ZMod p)) (Int.castRingHom ℂ)

/-- If `y : ZMod p` is a unit, the complex quadratic character at `y` has norm `1`. -/
private theorem quadCharC_norm (p : ℕ) [Fact p.Prime] {y : ZMod p} (hy : IsUnit y) :
    ‖quadCharC p y‖ = 1 := by
  have hnn : quadCharC p y ≠ 0 := (MulChar.apply_ne_zero_iff).2 hy
  rcases quadCharC_isQuadratic p y with h | h | h
  · exact absurd h hnn
  · rw [h, norm_one]
  · rw [h, norm_neg, norm_one]

/-- The complex quadratic character at `x : ZMod p` is the Jacobi symbol of `x` at `p`. -/
private theorem quadCharC_apply (p : ℕ) [Fact p.Prime] (x : ZMod p) :
    quadCharC p x = (jacobiSym (x.val : ℤ) p : ℂ) := by
  have h1 : jacobiSym (x.val : ℤ) p = legendreSym p (x.val : ℤ) :=
    (jacobiSym.legendreSym.to_jacobiSym p _).symm
  have h2 : ((x.val : ℤ) : ZMod p) = x := by simp
  have h3 : legendreSym p (x.val : ℤ) = quadraticChar (ZMod p) ((x.val : ℤ) : ZMod p) := rfl
  show ((quadraticChar (ZMod p) x : ℤ) : ℂ) = jacobiSym (x.val : ℤ) p
  rw [h1, h3, h2]

/-- The standard additive character `ZMod p → ℂ` at a natural number, written with a real phase. -/
private theorem stdAddChar_nat (p : ℕ) [NeZero p] (j : ℕ) :
    ZMod.stdAddChar (j : ZMod p) =
      Complex.exp (((2 * Real.pi * ((j : ℝ) / (p : ℝ)) : ℝ) : ℂ) * Complex.I) := by
  have h := ZMod.stdAddChar_coe (N := p) ((j : ℤ))
  rw [Int.cast_natCast] at h
  rw [h]
  congr 1
  push_cast
  ring

/-- The quadratic Gauss sum over `ZMod p` (with the standard additive character) has norm `√p`. -/
private theorem quadGaussNorm (p : ℕ) [Fact p.Prime] (hp2 : 2 < p) :
    ‖gaussSum (quadCharC p) ZMod.stdAddChar‖ = Real.sqrt (p : ℝ) := by
  have hne : quadCharC p ≠ 1 :=
    (ringHomComp_ne_one_iff Int.cast_injective).2
      (quadraticChar_ne_one (by rw [ZMod.ringChar_zmod_n]; linarith))
  have hsq := gaussSum_sq hne (quadCharC_isQuadratic p) (ZMod.isPrimitive_stdAddChar p)
  have hcard : ((Fintype.card (ZMod p) : ℕ) : ℂ) = ((p : ℝ) : ℂ) := by simp
  have hpc : ‖((p : ℝ) : ℂ)‖ = (p : ℝ) := by simp
  rw [hcard] at hsq
  have hn1 : ‖quadCharC p (-1 : ZMod p)‖ = 1 := quadCharC_norm p (by simp)
  have hnormsq : (‖gaussSum (quadCharC p) ZMod.stdAddChar‖ : ℝ) ^ 2 = (p : ℝ) := by
    have h := congrArg norm hsq
    rw [norm_mul, hn1, hpc, one_mul] at h
    rw [← h]
    exact (norm_pow (gaussSum (quadCharC p) ZMod.stdAddChar) 2).symm
  rw [← hnormsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- A sum over `Finset.range p` of a function factoring through `ZMod p` is a sum over `ZMod p`. -/
private theorem sum_range_eq_zmod (p : ℕ) [NeZero p] (F : ZMod p → ℂ) :
    ∑ b ∈ Finset.range p, F ((b : ℕ) : ZMod p) = ∑ x : ZMod p, F x := by
  refine @Finset.sum_bij ℕ (ZMod p) ℂ _ (Finset.range p) Finset.univ (fun b : ℕ => F ↑b) F
    (fun b _ => ((b : ℕ) : ZMod p)) (fun b _ => Finset.mem_univ _) ?_ ?_ (fun b _ => rfl)
  · intro b hb c hc h
    have hb' : b < p := Finset.mem_range.1 hb
    have hc' : c < p := Finset.mem_range.1 hc
    have h' := congrArg ZMod.val h
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hb', Nat.mod_eq_of_lt hc'] at h'
    exact h'
  · intro x _
    exact ⟨x.val, Finset.mem_range.2 x.val_lt, by simp⟩

theorem Conjectures.Goldbach.QuadraticGaussNormPrime : let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); ∀ p a : ℕ, Nat.Prime p → 2 < p → Nat.Coprime a p → ‖∑ b ∈ Finset.range p, (jacobiSym (b : ℤ) p : ℂ) * E ((b : ℝ) * ((a : ℝ) / p))‖ = Real.sqrt (p : ℝ) := by
  intro E p a hp hp2 hcop
  have : Fact p.Prime := ⟨hp⟩
  -- identify the sum in the statement with the Gauss sum twisted by the unit `a`
  have hu : IsUnit (a : ZMod p) := (ZMod.isUnit_iff_coprime a p).2 hcop
  have hsum : gaussSum (quadCharC p) (ZMod.stdAddChar.mulShift hu.unit) =
      ∑ b ∈ Finset.range p, (jacobiSym (b : ℤ) p : ℂ) * E ((b : ℝ) * ((a : ℝ) / p)) := by
    rw [gaussSum, ← sum_range_eq_zmod]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxlt : x < p := Finset.mem_range.1 hx
    have hxval : ((x : ℕ) : ZMod p).val = x := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hxlt]
    rw [AddChar.mulShift_apply, quadCharC_apply, hxval]
    refine congrArg₂ (· * ·) rfl ?_
    have hy : ((hu.unit : ZMod p) * ((x : ℕ) : ZMod p) : ZMod p) = ((a * x : ℕ) : ZMod p) := by
      simp
    rw [hy, stdAddChar_nat]
    congr 1
    push_cast
    ring
  rw [← hsum]
  -- twisting by the unit `a` does not change the norm
  have h := congrArg norm (gaussSum_mulShift (quadCharC p) ZMod.stdAddChar hu.unit)
  rw [norm_mul, quadCharC_norm p hu.unit.isUnit, one_mul] at h
  rw [h]
  exact quadGaussNorm p hp2
