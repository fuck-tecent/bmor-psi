import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Primality
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026, original Hex ECPP rights holder.
Original author: Kim Morrison. The full upstream credit appears in the PR.
Licensed under Apache License 2.0, included as LICENSE in this repository.
Changes: projective arithmetic with coprimality guards, an elementary point
bound, embedded PARI certificate data, and consolidation into one module.
https://github.com/leanprover/hex-ecpp/tree/c3127662195cab3c24c729c4bd5f0e8324835c79
https://github.com/leanprover/hex-ecpp-theory/tree/2911ff9bb39ce993181c03d4c035279744d700bf
-/

namespace Rfc11CutpointCertificate

inductive Point where
  | infinity
  | projective (x y z : ℕ)
deriving Repr, BEq, DecidableEq

def Point.affine (x y : ℕ) : Point := .projective x y 1

def modSub (n a b : Nat) : Nat := (a % n + n - b % n) % n

def onCurve (n a b x y : Nat) : Bool :=
  (y*y) % n == (x*x*x+a*x+b) % n

/-- Homogenize the usual affine formulas with slope v/d. -/
def projectiveSum (n x y z u w v d : ℕ) : Point :=
  let B := (d*d*z*w) % n
  let A := modSub n (v*v*z*w) (d*d*(x*w+u*z))
  .projective ((A*z*d)%n)
    (modSub n (v*modSub n (x*B) (A*z)) (y*B*d))
    ((d*z*B)%n)

def add? (n a : Nat) (P Q : Point) : Option Point :=
  match P, Q with
  | .infinity, Q => some Q
  | P, .infinity => some P
  | .projective x y z, .projective u v w =>
    let dx := modSub n (u*z) (x*w)
    if dx = 0 then
      if (y*w+v*z)%n = 0 then some .infinity
      else if modSub n (v*z) (y*w) = 0 then
        let d := (2*y*z)%n
        if d.gcd n = 1 then
          some (projectiveSum n x y z x z ((3*x*x+a*z*z)%n) d)
        else none
      else none
    else
      if dx.gcd n = 1 then
        some (projectiveSum n x y z u w (modSub n (v*z) (y*w)) dx)
      else none

/-- Read the scalar bits from high to low, doubling the accumulated point
and adding the fixed point for each set bit. -/
def replayBits (n a q : Nat) (Q : Point) : (bits : Nat) → Point → Option Point
  | 0, R => some R
  | bits + 1, R => do
      let D ← add? n a R R
      let S ← if q.testBit bits then add? n a D Q else some D
      replayBits n a q Q bits S

def replay (n a q : Nat) (Q : Point) : Option Point :=
  replayBits n a q Q (q.log2 + 1) .infinity

def replayDone (n a q : Nat) (Q : Point) : Bool :=
  match replay n a q Q with
  | some .infinity => true
  | _ => false

theorem replayDone_eq_true_iff {n a q : Nat} {Q : Point} :
    replayDone n a q Q = true ↔ replay n a q Q = some .infinity := by
  unfold replayDone
  cases h : replay n a q Q with
  | none => simp
  | some P => cases P <;> simp
/-- The next binary digit extends the truncated scalar by its positional value. -/
theorem bit_mod_succ (q k : Nat) :
    q % 2 ^ (k + 1) =
      q % 2 ^ k + (q.testBit k).toNat * 2 ^ k := by
  rw [Nat.mod_pow_succ, Nat.toNat_testBit, Nat.mul_comm]


open WeierstrassCurve

/-- The short Weierstrass curve supplied by an ECPP step, reduced modulo `p`. -/
def shortCurve (p a b : ℕ) : WeierstrassCurve (ZMod p) :=
  ⟨0, 0, 0, a, b⟩

/-- The checker's short curve has zero coefficients `a₁`, `a₂` and `a₃`. -/
instance shortCurveIsShortNF (p a b : ℕ) : (shortCurve p a b).IsShortNF :=
  ⟨rfl, rfl, rfl⟩

/-- The checker coprimality guard excludes characteristics two and three. -/
theorem prime_divisor_gt_three {p n : ℕ} (prime : p.Prime) (hp : p ∣ n)
    (hmod : n % 6 = 1 ∨ n % 6 = 5) : 3 < p := by
  have hp2 := prime.two_le
  by_contra h
  have hsmall : p = 2 ∨ p = 3 := by omega
  rcases hsmall with rfl | rfl
  · obtain ⟨k, rfl⟩ := hp
    rcases hmod with hmod | hmod <;> omega
  · obtain ⟨k, rfl⟩ := hp
    rcases hmod with hmod | hmod <;> omega

/-- Reduction modulo a multiple of `p` preserves the residue in `ZMod p`. -/
theorem cast_mod {p n : ℕ} (hp : p ∣ n) (t : ℕ) :
    ((t % n : ℕ) : ZMod p) = t := by
  exact (ZMod.natCast_eq_natCast_iff _ _ p).mpr
    ((Nat.mod_modEq t n).of_dvd hp)

/-- The checker's natural modular subtraction is field subtraction after
reduction at any prime divisor. -/
theorem cast_modSub {p n : ℕ} (hp : p ∣ n) (hn : 0 < n) (a b : ℕ) :
    ((modSub n a b : ℕ) : ZMod p) = (a : ZMod p) - b := by
  have hle : b % n ≤ a % n + n := by
    have hb := Nat.mod_lt b hn
    omega
  simp only [modSub, cast_mod hp, Nat.cast_sub hle, Nat.cast_add]
  rw [(ZMod.natCast_eq_zero_iff n p).mpr hp]
  ring

/-- A checked raw point lies on the reduced short curve. -/
theorem onCurve_reduced {p n a b x y : ℕ} (hp : p ∣ n)
    (h : onCurve n a b x y = true) :
    (shortCurve p a b).toAffine.Equation (x : ZMod p) (y : ZMod p) := by
  have heq : (y * y) % n = (x * x * x + a * x + b) % n := by
    simpa only [onCurve, beq_iff_eq] using h
  have heq' := congrArg (fun t : ℕ => (t : ZMod p)) heq
  simp only [cast_mod hp, Nat.cast_mul, Nat.cast_add] at heq'
  rw [WeierstrassCurve.Affine.equation_iff]
  dsimp [shortCurve]
  simp only [zero_mul, add_zero]
  calc
    (y : ZMod p) ^ 2 = y * y := by ring
    _ = x * x * x + (a : ZMod p) * x + b := heq'
    _ = x ^ 3 + (a : ZMod p) * x + b := by ring

/-- The checked discriminant inverse makes the reduced short curve nonsingular. -/
theorem shortCurve_elliptic {p n a b inv : ℕ} (prime : p.Prime)
    (hp3 : 3 < p) (hp : p ∣ n)
    (h : ((4 * a * a * a + 27 * b * b) * inv) % n = 1) :
    (shortCurve p a b).toAffine.IsElliptic := by
  have : Fact p.Prime := ⟨prime⟩
  have hcast := congrArg (fun t : ℕ => (t : ZMod p)) h
  simp only [cast_mod hp, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hcast
  have hfactor : (4 * (a : ZMod p) ^ 3 + 27 * (b : ZMod p) ^ 2) * inv = 1 := by
    calc
      _ = (4 * (a : ZMod p) * a * a + 27 * (b : ZMod p) * b) * inv := by ring
      _ = 1 := hcast
  have hD : (4 * (a : ZMod p) ^ 3 + 27 * (b : ZMod p) ^ 2) ≠ 0 := by
    intro hz
    have hzero : (0 : ZMod p) = 1 := by simpa only [hz, zero_mul] using hfactor
    exact zero_ne_one hzero
  have h16 : (16 : ZMod p) ≠ 0 := by
    intro hz
    have hdiv : p ∣ 16 := (ZMod.natCast_eq_zero_iff 16 p).mp hz
    have hpow : p ∣ 2 ^ 4 := by simpa using hdiv
    have h2 : p ∣ 2 := prime.dvd_of_dvd_pow hpow
    have : p ≤ 2 := Nat.le_of_dvd (by omega) h2
    omega
  apply (WeierstrassCurve.isElliptic_iff (shortCurve p a b)).2
  rw [WeierstrassCurve.Δ_of_isShortNF]
  dsimp [shortCurve]
  have hne : (-16 * (4 * (a : ZMod p) ^ 3 + 27 * (b : ZMod p) ^ 2)) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr h16) hD
  exact isUnit_iff_ne_zero.mpr hne

theorem ne_zero_of_gcd_one {n p d : ℕ} [Fact p.Prime] (hp : p ∣ n)
    (hg : d.gcd n = 1) : (d : ZMod p) ≠ 0 := by
  intro hd
  have hdp := (ZMod.natCast_eq_zero_iff d p).mp hd
  have h := Nat.dvd_gcd hdp hp
  rw [hg] at h
  exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp h)

-- Reduce homogeneous coordinates only over the prime divisor.
def Point.Rep (p a b : ℕ) [Fact p.Prime] (raw : Point)
    (P : (shortCurve p a b).toAffine.Point) : Prop :=
  match raw with
  | .infinity => P = 0
  | .projective x y z =>
      (z : ZMod p) ≠ 0 ∧
        ∃ h : (shortCurve p a b).toAffine.Nonsingular (x / (z : ZMod p)) (y / (z : ZMod p)),
          P = .some _ _ h

theorem startingPoint_rep {p n a b x y inv : ℕ} (prime : p.Prime)
    (hp3 : 3 < p) (hp : p ∣ n)
    (hdisc : ((4 * a * a * a + 27 * b * b) * inv) % n = 1)
    (hcurve : onCurve n a b x y = true) :
    letI : Fact p.Prime := ⟨prime⟩
    ∃ P : (shortCurve p a b).toAffine.Point,
      (Point.affine x y).Rep p a b P ∧ P ≠ 0 := by
  have : Fact p.Prime := ⟨prime⟩
  have : (shortCurve p a b).toAffine.IsElliptic :=
    shortCurve_elliptic prime hp3 hp hdisc
  have heq := onCurve_reduced hp hcurve
  have hnon : (shortCurve p a b).toAffine.Nonsingular (x : ZMod p) (y : ZMod p) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp heq
  refine ⟨.some _ _ hnon, ?_, WeierstrassCurve.Affine.Point.some_ne_zero hnon⟩
  simp only [Point.affine, Point.Rep, Nat.cast_one, div_one]
  exact ⟨one_ne_zero, hnon, trivial⟩

theorem sum_coordinates {p n x y z u w v d : ℕ} [Fact p.Prime]
    (hp : p ∣ n) (hn : 0 < n)
    (hz : (z : ZMod p) ≠ 0) (hw : (w : ZMod p) ≠ 0)
    (hd : (d : ZMod p) ≠ 0) :
    ∃ X Y Z : ℕ, projectiveSum n x y z u w v d = .projective X Y Z ∧
      (Z : ZMod p) ≠ 0 ∧
      (X : ZMod p)/Z = ((v : ZMod p)/d)^2 - (x : ZMod p)/z - (u : ZMod p)/w ∧
      (Y : ZMod p)/Z = ((v : ZMod p)/d)*((x : ZMod p)/z-(X : ZMod p)/Z) - (y : ZMod p)/z := by
  simp only [projectiveSum]
  refine ⟨_, _, _, rfl, ?_, ?_, ?_⟩
  · simp only [cast_mod hp, Nat.cast_mul]
    exact mul_ne_zero (mul_ne_zero hd hz) (mul_ne_zero (mul_ne_zero (mul_ne_zero hd hd) hz) hw)
  · simp only [cast_mod hp, cast_modSub hp hn, Nat.cast_mul, Nat.cast_add]
    field_simp
    ring
  · simp only [cast_mod hp, cast_modSub hp hn, Nat.cast_mul, Nat.cast_add]
    field_simp

theorem projective_sum_rep {p n a b x y z u t w v d : ℕ} [Fact p.Prime]
    (hp : p ∣ n) (hn : 0 < n)
    (hz : (z : ZMod p) ≠ 0) (hw : (w : ZMod p) ≠ 0)
    (hd : (d : ZMod p) ≠ 0)
    (hP : (shortCurve p a b).toAffine.Nonsingular (x/(z : ZMod p)) (y/(z : ZMod p)))
    (hQ : (shortCurve p a b).toAffine.Nonsingular (u/(w : ZMod p)) (t/(w : ZMod p)))
    (hxy : ¬((x : ZMod p)/z = u/w ∧ (y : ZMod p)/z =
      (shortCurve p a b).toAffine.negY (u/w) (t/w)))
    (hs : (shortCurve p a b).toAffine.slope (x/z) (u/w) (y/z) (t/w) = (v : ZMod p)/d) :
    (projectiveSum n x y z u w v d).Rep p a b (.some _ _ hP + .some _ _ hQ) := by
  obtain ⟨X,Y,Z,he,hZ,hX,hY⟩ := sum_coordinates hp hn hz hw hd
    (x:=x) (y:=y) (u:=u) (v:=v)
  rw [he]
  have hX' : (X : ZMod p)/Z =
      (shortCurve p a b).toAffine.addX (x/z) (u/w)
        ((shortCurve p a b).toAffine.slope (x/z) (u/w) (y/z) (t/w)) := by
    rw [hs]
    simpa only [WeierstrassCurve.Affine.addX, shortCurve, zero_mul, add_zero, sub_zero] using hX
  have hY' : (Y : ZMod p)/Z =
      (shortCurve p a b).toAffine.addY (x/z) (u/w) (y/z)
        ((shortCurve p a b).toAffine.slope (x/z) (u/w) (y/z) (t/w)) := by
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY]
    rw [← hX', hs]
    simp only [WeierstrassCurve.Affine.negY, shortCurve, zero_mul, sub_zero]
    linear_combination hY
  have hh : (shortCurve p a b).toAffine.Nonsingular (X/(Z : ZMod p)) (Y/(Z : ZMod p)) := by
    rw [hX', hY']
    exact (shortCurve p a b).toAffine.nonsingular_add hP hQ hxy
  refine ⟨hZ, hh, ?_⟩
  rw [WeierstrassCurve.Affine.Point.add_some hxy]
  simp only [← hX', ← hY']

theorem add_rep {p n a b : ℕ} [Fact p.Prime] (hp : p ∣ n) (hn : 0 < n)
    {P Q R : Point} {U V : (shortCurve p a b).toAffine.Point}
    (hP : P.Rep p a b U) (hQ : Q.Rep p a b V)
    (h : add? n a P Q = some R) :
    R.Rep p a b (U + V) := by
  cases P with
  | infinity =>
    simp only [Point.Rep] at hP
    simp only [add?] at h
    cases h
    simpa [hP] using hQ
  | projective x y z =>
    cases Q with
    | infinity =>
      simp only [Point.Rep] at hQ
      simp only [add?] at h
      cases h
      simpa [hQ] using hP
    | projective u t w =>
      obtain ⟨hz, h₁, rfl⟩ := hP
      obtain ⟨hw, h₂, rfl⟩ := hQ
      let dx := modSub n (u*z) (x*w)
      let dy := modSub n (t*z) (y*w)
      let d := (2*y*z)%n
      let vv := (3*x*x+a*z*z)%n
      change (if dx = 0 then
        if (y*w+t*z)%n = 0 then some .infinity
        else if dy = 0 then
          if d.gcd n = 1 then some (projectiveSum n x y z x z vv d) else none
        else none
        else if dx.gcd n = 1 then some (projectiveSum n x y z u w dy dx)
        else none) = some R at h
      have hxcast : (dx : ZMod p) = (u : ZMod p)*z - (x : ZMod p)*w :=
        by simp [dx, cast_modSub hp hn]
      have hycast : (dy : ZMod p) = (t : ZMod p)*z - (y : ZMod p)*w :=
        by simp [dy, cast_modSub hp hn]
      by_cases hdx : dx = 0
      · have hx : (x : ZMod p)/z = (u : ZMod p)/w := by
          rw [div_eq_div_iff hz hw]
          rw [hdx, Nat.cast_zero] at hxcast
          exact sub_eq_zero.mp hxcast.symm |>.symm
        by_cases hnY : (y*w+t*z)%n = 0
        · have hcast := congrArg (fun i : ℕ => (i : ZMod p)) hnY
          simp only [cast_mod hp, Nat.cast_add, Nat.cast_mul, Nat.cast_zero] at hcast
          have hy : (y : ZMod p)/z = (shortCurve p a b).toAffine.negY (u/w) (t/w) := by
            simp only [WeierstrassCurve.Affine.negY, shortCurve, zero_mul, sub_zero]
            rw [← neg_div, div_eq_div_iff hz hw]
            linear_combination hcast
          have hgroup := WeierstrassCurve.Affine.Point.add_of_Y_eq (h₁:=h₁) (h₂:=h₂) hx hy
          simp only [ite_eq_left hdx, ite_eq_left hnY, Option.some.injEq] at h
          subst R
          exact hgroup
        · by_cases hdy : dy = 0
          · by_cases hg : d.gcd n = 1
            · have hd := ne_zero_of_gcd_one hp hg
              have hd' : (2 : ZMod p)*y*z ≠ 0 := by
                simpa [d, cast_mod hp] using hd
              have hy : (y : ZMod p)/z = (t : ZMod p)/w := by
                rw [div_eq_div_iff hz hw]
                rw [hdy, Nat.cast_zero] at hycast
                exact sub_eq_zero.mp hycast.symm |>.symm
              have hsame : (WeierstrassCurve.Affine.Point.some _ _ h₁ :
                  (shortCurve p a b).toAffine.Point) = .some _ _ h₂ := by
                simp only [hx, hy]
              have hyne : (y : ZMod p)/z ≠ (shortCurve p a b).toAffine.negY (x/z) (y/z) := by
                simp only [WeierstrassCurve.Affine.negY, shortCurve, zero_mul, sub_zero]
                intro he
                rw [← neg_div, div_eq_div_iff hz hz] at he
                apply hd'
                linear_combination he
              have hs : (shortCurve p a b).toAffine.slope (x/z) (x/z) (y/z) (y/z) =
                  (vv : ZMod p)/d := by
                rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyne]
                simp only [vv, d, cast_mod hp, Nat.cast_add, Nat.cast_mul,
                  WeierstrassCurve.Affine.negY, shortCurve, zero_mul, sub_zero]
                field_simp [hd']
                ring
              simp only [ite_eq_left hdx, ite_eq_right hnY, ite_eq_left hdy, ite_eq_left hg, Option.some.injEq] at h
              subst R
              rw [← hsame]
              exact projective_sum_rep hp hn hz hz hd h₁ h₁ (fun hh => hyne hh.2) hs
            · simp only [ite_eq_left hdx, ite_eq_right hnY, ite_eq_left hdy, ite_eq_right hg, reduceCtorEq] at h
          · simp only [ite_eq_left hdx, ite_eq_right hnY, ite_eq_right hdy, reduceCtorEq] at h
      · by_cases hg : dx.gcd n = 1
        · have hd := ne_zero_of_gcd_one hp hg
          have hxne : (x : ZMod p)/z ≠ (u : ZMod p)/w := by
            intro he
            rw [div_eq_div_iff hz hw] at he
            apply hd
            rw [hxcast, he, sub_self]
          have hs : (shortCurve p a b).toAffine.slope (x/z) (u/w) (y/z) (t/w) =
              (dy : ZMod p)/dx := by
            rw [WeierstrassCurve.Affine.slope_of_X_ne hxne, hycast, hxcast]
            have hd' : (u : ZMod p)*z - (x : ZMod p)*w ≠ 0 := hxcast ▸ hd
            have hdiff (s t : ZMod p) :
                s/(z : ZMod p)-t/(w : ZMod p) =
                  (s*w-t*z)/((z : ZMod p)*w) := by
              field_simp
            rw [hdiff, hdiff,
              show (y : ZMod p)*w-t*z = -((t : ZMod p)*z-y*w) by ring,
              show (x : ZMod p)*w-u*z = -((u : ZMod p)*z-x*w) by ring]
            simp only [neg_div, div_neg, neg_neg]
            field_simp [hd']
          simp only [ite_eq_right hdx, ite_eq_left hg, Option.some.injEq] at h
          subst R
          exact projective_sum_rep hp hn hz hw hd h₁ h₂ (fun hh => hxne hh.1) hs
        · simp only [ite_eq_right hdx, ite_eq_right hg, reduceCtorEq] at h
/-- The structurally recursive raw replay computes the canonical binary
initial bits of the scalar in the actual elliptic-curve group. -/
theorem replayBits_rep {p n a b q : ℕ} [Fact p.Prime] (hp : p ∣ n) (hn : 0 < n)
    (Q : Point) (V : (shortCurve p a b).toAffine.Point)
    (hQ : Q.Rep p a b V) :
    ∀ (k : ℕ) {R S : Point}
      (U : (shortCurve p a b).toAffine.Point),
      R.Rep p a b U → replayBits n a q Q k R = some S →
      S.Rep p a b ((2 ^ k) • U + (q % 2 ^ k) • V)
  | 0, R, S, U, hR, h => by
      simp only [replayBits, Option.some.injEq] at h
      subst S
      simpa [Nat.mod_one] using hR
  | k + 1, R, S, U, hR, h => by
      cases hD : add? n a R R with
      | none => simp [replayBits, hD] at h
      | some D =>
        have hDrep := add_rep hp hn hR hR hD
        cases hbit : q.testBit k with
        | false =>
          have hrec : replayBits n a q Q k D = some S := by
            simpa [replayBits, hD, hbit] using h
          have hrecRep := replayBits_rep hp hn Q V hQ k (U + U) hDrep hrec
          have hscalar : (2 ^ k) • (U + U) + (q % 2 ^ k) • V =
              (2 ^ (k + 1)) • U + (q % 2 ^ (k + 1)) • V := by
            rw [bit_mod_succ]
            simp [hbit, pow_succ, mul_nsmul, nsmul_add, two_nsmul]
          rw [← hscalar]
          exact hrecRep
        | true =>
          cases hT : add? n a D Q with
          | none => simp [replayBits, hD, hbit, hT] at h
          | some T =>
            have hrec : replayBits n a q Q k T = some S := by
              simpa [replayBits, hD, hbit, hT] using h
            have hTrep := add_rep hp hn hDrep hQ hT
            have hrecRep := replayBits_rep hp hn Q V hQ k
              ((U + U) + V) hTrep hrec
            have hscalar : (2 ^ k) • ((U + U) + V) + (q % 2 ^ k) • V =
                (2 ^ (k + 1)) • U + (q % 2 ^ (k + 1)) • V := by
              rw [bit_mod_succ]
              simp [hbit, pow_succ, mul_nsmul, nsmul_add, add_nsmul, two_nsmul]
              abel
            rw [← hscalar]
            exact hrecRep

/-- If the complete replay returns infinity, its field point is annihilated
by the child subject. -/
theorem replay_zero {p n a b q : ℕ} [Fact p.Prime] (hp : p ∣ n) (hn : 0 < n)
    (Q : Point) (V : (shortCurve p a b).toAffine.Point)
    (hQ : Q.Rep p a b V)
    (h : replay n a q Q = some .infinity) : q • V = 0 := by
  have hrep := replayBits_rep hp hn Q V hQ ((q.log2 + 1))
    (R := .infinity) (S := .infinity)
    0 (by rfl) h
  change (2 ^ (q.log2 + 1)) • (0 : (shortCurve p a b).toAffine.Point) +
    (q % 2 ^ (q.log2 + 1)) • V = 0 at hrep
  have ht : q < 2 ^ (q.log2 + 1) := by
    by_cases hq : q = 0
    · subst q
      decide
    · exact (Nat.log2_lt hq).mp (Nat.lt_succ_self _)
  simpa [Nat.mod_eq_of_lt ht] using hrep


/-- A nonzero point annihilated by a prime has that order, which divides the
cardinality of its finite group. -/
theorem prime_order_dvd_card {G : Type*} [AddGroup G] [Fintype G]
    {q : ℕ} (hq : q.Prime) {Q : G} (hne : Q ≠ 0) (hzero : q • Q = 0) :
    q ∣ Fintype.card G := by
  have : Fact q.Prime := ⟨hq⟩
  have hord : addOrderOf Q = q := addOrderOf_eq_prime hzero hne
  rw [← hord]
  exact addOrderOf_dvd_card

/-- A prime annihilating a nonzero point is at most the finite group order. -/
theorem prime_order_le_card {G : Type*} [AddGroup G] [Fintype G]
    {q : ℕ} (hq : q.Prime) {Q : G} (hne : Q ≠ 0) (hzero : q • Q = 0) :
    q ≤ Fintype.card G := by
  exact Nat.le_of_dvd Fintype.card_pos (prime_order_dvd_card hq hne hzero)


/-- An affine point is determined by its abscissa and which of its two
opposite ordinates has the smaller canonical representative. -/
private def pointCode {p a b : ℕ} (P : (shortCurve p a b).toAffine.Point) :
    Option (ZMod p × Bool) :=
  match P with
  | .zero => none
  | .some x y _ => some (x, decide (y.val ≤ (-y).val))

private theorem pointCode_injective {p a b : ℕ} [Fact p.Prime] :
    Function.Injective (pointCode (p := p) (a := a) (b := b)) := by
  intro P Q he
  cases P with
  | zero =>
    cases Q with
    | zero => rfl
    | some x y h => simp [pointCode] at he
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => simp [pointCode] at he
    | some x₂ y₂ h₂ =>
      simp only [pointCode, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, he⟩ := he
      have hy : y₁ = y₂ := by
        rcases (shortCurve p a b).toAffine.Y_eq_of_X_eq h₁.1 h₂.1 rfl with h | h
        · exact h
        · have hyneg : y₁ = -y₂ := by
            simpa [WeierstrassCurve.Affine.negY, shortCurve] using h
          rw [hyneg, neg_neg] at he
          rw [hyneg]
          have hle₁ : (-y₂).val ≤ y₂.val := by
            by_contra hh
            have hh' : y₂.val ≤ (-y₂).val := by omega
            simp [hh, hh'] at he
          have hle₂ : y₂.val ≤ (-y₂).val := by
            by_contra hh
            simp [hle₁, hh] at he
          exact ZMod.val_injective p (Nat.le_antisymm hle₁ hle₂)
      subst y₂
      rfl

/-- A checked point of order q would give at least q points over every
prime divisor p. Each x permits at most two y, so q ≤ 2p+1. -/
theorem prime_of_row {n a b x y discInv q : ℕ} (hq : q.Prime)
    (hn : 3 < n) (hmod : n % 6 = 1 ∨ n % 6 = 5)
    (hcurve : onCurve n a b x y = true)
    (hdisc : (4 * a * a * a + 27 * b * b) * discInv % n = 1)
    (hsize : 4 * n < (q - 1) ^ 2)
    (hstep : replay n a q (.affine x y) = some .infinity) :
    n.Prime := by
  by_contra hnp
  let p := Nat.minFac n
  have hpPrime : p.Prime := Nat.minFac_prime (by omega : n ≠ 1)
  have hpDiv : p ∣ n := Nat.minFac_dvd n
  have hpSq : p ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  have : Fact p.Prime := ⟨hpPrime⟩
  have hp3 : 3 < p := prime_divisor_gt_three hpPrime hpDiv hmod
  have : (shortCurve p a b).toAffine.IsElliptic :=
    shortCurve_elliptic hpPrime hp3 hpDiv hdisc
  obtain ⟨P, hP, hP0⟩ := startingPoint_rep hpPrime hp3 hpDiv hdisc hcurve
  have hzero : q • P = 0 := replay_zero hpDiv (by omega) _ P hP hstep
  have : Fintype (shortCurve p a b).toAffine.Point :=
    Fintype.ofInjective pointCode pointCode_injective
  have hcard := Fintype.card_le_of_injective
    (pointCode (p := p) (a := a) (b := b)) pointCode_injective
  have horder := prime_order_le_card hq hP0 hzero
  have hqle : q ≤ 2 * p + 1 := by
    apply horder.trans
    simpa [Fintype.card_option, Fintype.card_prod, ZMod.card, mul_comm] using hcard
  have hs : q - 1 ≤ 2 * p := by omega
  have hsq : (q - 1) ^ 2 ≤ (2 * p) ^ 2 := Nat.pow_le_pow_left hs 2
  nlinarith only [hsize, hsq, hpSq]

private theorem prime_of_check {n a b x y d q : ℕ} (hq : q.Prime)
    (h : (decide (3 < n) && (n % 6 == 1 || n % 6 == 5) &&
      onCurve n a b x y && ((4 * a * a * a + 27 * b * b) * d % n == 1) &&
      decide (4 * n < (q - 1) ^ 2)) = true)
    (hstep : replayDone n a q (.affine x y) = true) :
    n.Prime := by
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_iff, beq_iff_eq] at h
  exact prime_of_row hq h.1.1.1.1 h.1.1.1.2 h.1.1.2 h.1.2 h.2
    (replayDone_eq_true_iff.mp hstep)


-- PARI/GP primecert supplies the curve and point data. For each row, the
-- point below is the certificate point multiplied by its cofactor. Its child
-- prime kills that point, so the full curve order is not a premise.
private theorem terminalPrime : Nat.Prime 795068271529560031 := by
  primality (cert := .witnesses [
    .lucas { root := 3, primeFactors := [2, 3, 5, 26502275717652001] },
    .lucas { root := 23, primeFactors := [2, 3, 5, 7, 17, 1489, 254369] },
    .lucas { root := 3, primeFactors := [2, 7949] },
    .lucas { root := 2, primeFactors := [2, 1987] },
    .lucas { root := 2, primeFactors := [2, 3, 331] },
    .lucas { root := 14, primeFactors := [2, 3, 31] }])


set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row38 : Nat.Prime
    3129150349463449754112584232918451 := by
  refine prime_of_check (a := 0)
    (b := 311643145235160839257486078337572)
    (x := 770697609435986089673713463143923)
    (y := 1731887906265689121902141763985937)
    (d := 1089850293589078134310548545841023)
    terminalPrime (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row37 : Nat.Prime
    814982022009776017399035908912507173505898503689 := by
  refine prime_of_check (a := 0)
    (b := 813340490045477669805931843214581265434840358079)
    (x := 774918466259342501412552010630998897460729443747)
    (y := 217306607567623205369999184416399527616028311697)
    (d := 744743168836532234625518584102751430475554823340)
    row38 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row36 : Nat.Prime
    40629464999585853789701686565572722847120423548671564717 := by
  refine prime_of_check (a := 1)
    (b := 0)
    (x := 38278392834534261066453943115288786163662204507919336674)
    (y := 2708838642496452047368005070362455867318886188572023948)
    (d := 30472098749689390342276264924179542135340317661503673538)
    row37 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row35 : Nat.Prime
    16683758471709938313372782957796077646071440782175322837313469 := by
  refine prime_of_check (a := 16683758471709938313372782957796077646071440782175322837313468)
    (b := 0)
    (x := 12851947506677729621147546875147959431368241730946540792351803)
    (y := 15017767171154893113857355965253191063330875841855538310295595)
    (d := 4170939617927484578343195739449019411517860195543830709328367)
    row36 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row34 : Nat.Prime
    70362080309188138369228244706563904139882114819964441099393053232499049 := by
  refine prime_of_check (a := 1)
    (b := 0)
    (x := 53306232766303680740569593488708056015992262882446129337651538459650532)
    (y := 43193953475184229302467915165716107532643498644588148352217593358816193)
    (d := 52771560231891103776921183529922928104911586114973330824544789924374287)
    row35 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row33 : Nat.Prime
    234404462878066208406320397668785797171133852642596439874004863603545058286695717 := by
  refine prime_of_check (a := 99036002647312485952679335186860520552037291688328185395437052578589231653321028)
    (b := 233394807174275200369223788090027786273883467610243407936174619950531505342966857)
    (x := 76942708523591926248770447501258467467120690663533928831395442030640938657026506)
    (y := 96201968593919291765399514748715068335012179328947456443892277443445226695462626)
    (d := 112911352048680080812884958216750245874091266699464610874994349428375501949887988)
    row34 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row32 : Nat.Prime
    1682237850896022342294385656648100916125029097539890014752017407953016279466904487377397 := by
  refine prime_of_check (a := 816955118830503451839275597138539330132624690296011033566441264457350327393889522721594)
    (b := 345441553527217324401837810038735656991112198575260692885436047886040425715151360041117)
    (x := 454879201040995469973418628506488556521033532067316241003216392244169094371643549490503)
    (y := 1482134664279248720350145650205989143054577321886369034417731684900971301088883092113821)
    (d := 623068815177888275335538899938947467026981181918007895979919532022764045925944717640397)
    row33 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row31 : Nat.Prime
    185268218994880732601565281137968650094681704548448722796499649797708572040882927629553755759 := by
  refine prime_of_check (a := 20939777661574871772592154540048484390575258431397115794484784986880703930892511074559102474)
    (b := 59144807547056282704333021685818527078678928437306666612597792649967081424669894728791394541)
    (x := 158596338760451308520108631216560344302063574729628720194196130313312971604162367577818243766)
    (y := 83157683229756365376160682833917963628504748188908978914991198903657176781139959630541628961)
    (d := 48862834298711599121670094869333057666624880594792616638100496989836252583555965446303733286)
    row32 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row30 : Nat.Prime
    14625814280331864554497969554155797113074552483871372933322394860282078472663779348823324081266277 := by
  refine prime_of_check (a := 6941386981319516890310635834552400004866480961017070427889293571429117928784803213923043492469667)
    (b := 7249564158595504437038088201034294502874519633756253760935956693946723230532439348428132927894926)
    (x := 12297482470023289484985834153632570592923763400744095502084729845864818228037915052756906821462806)
    (y := 11864515389893571150340593632757295745644002209521409649491408769806791983447362321309542336242174)
    (d := 9864264738605429852052680214657191678020411335204490586871627326628039919707193961861382303826452)
    row31 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row29 : Nat.Prime
    91838649513850942596521632102124802377501251259164236986153800349316690654391194092951827178556478942339801 := by
  refine prime_of_check (a := 21017300815522817219702324025465732640564601239826844626877498407888072851695009355499890705418444406695590)
    (b := 75564920572251868886723799282784099865870246768423044811002714864184946174588926083092511251927643492095976)
    (x := 82589817694122137563937720555322805340329349693008229804989233131428448480332203296809597486162940598894213)
    (y := 46113284736133652566615634622229170347539044468958485342014689057601162368248062927391596969873577715038183)
    (d := 61390506628957710241768708526588781488638576909290595285464686571447528253291057690058787150574198066275450)
    row30 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row28 : Nat.Prime
    94777486298294172759610324329392796053581291299457492550850129727433818288770447426497205334765956237396396713 := by
  refine prime_of_check (a := 63883437504294442974882581814981800454832658071287920105127450620605814920903651793180735507316668167055475836)
    (b := 44884835269948916282136571072587078869457823877420207608177204298552433823054233827435198528994400999681681713)
    (x := 12241441280402452455979538689426464177563377973430657245639248138466025179434680766162318432620215174181216766)
    (y := 88559902620358172039079700454969796085749844684969820777920748969783395819460682712155500560778053940972175391)
    (d := 82060066307824244557879687532422071106751948765837929555956268959099407504201248741319438997337430515649483473)
    row29 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row27 : Nat.Prime
    4180503748576719121291312105480644354293732602711911547248326574701614459595278074598799407279803780903514558003588217 := by
  refine prime_of_check (a := 4180503748576719121291312105480644354293732602711911547248326574701614459595278074598799407279803780903514557853060217)
    (b := 629407744000)
    (x := 3530551120905312220233325929506267645849207766894514810670430735360199512293108581289986115021391725822447927048739508)
    (y := 1554357555763122531203131159986103581420569096608658595737500895904405050755442094758652194567118433711171933287291273)
    (d := 3481076242933412219246943746258269594967897503500416666714484592415041456216303231971013617814740500722411362841932403)
    row28 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row26 : Nat.Prime
    21935312193969474065371579183062214959196929653059535483989331749407585268653368759027600296461008578167674256089895583245857 := by
  refine prime_of_check (a := 6321856216758588375046585299951966572037995851121192858843343108386561089859126817840723231866576875171720656403440422615011)
    (b := 0)
    (x := 5216970606707448167392987178184265385179246820647591930837233318500437996845171440314231537782055564889965007733260820721220)
    (y := 19043371120862979130976923326533335579585340148818579296261872763676135760754822224869170153714568405180473326811061424573843)
    (d := 2155656218250301308347477730311727854211106224465486267224018023569452527132893519712405372232476603058922034427136926540830)
    row27 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row25 : Nat.Prime
    4554431600025425073875064199311089648578843727146738786208109869082020675124153489753380151751621716058748612879866717382056969545803113 := by
  refine prime_of_check (a := 3564437901406848445616832426150271154400869397437085881107938821529435229472295896441903505678717970878966673845171523570520449982789625)
    (b := 0)
    (x := 601742125887353876402723958127488475323617996309495232965285167220232721946361333997536850899391329804745930743752160609054383831099067)
    (y := 2919779315559411785248772186880354904469661463663728107147378046217400980271169986303799376175406669478750309828655483815583369884473160)
    (d := 4306933175370780916810506256020885025034350144719325559933067107193874313711189091425510990233395779763803128121192918929172839655049741)
    row26 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row24 : Nat.Prime
    4021563102822450340231681687991692159695119011070570348221761014399426255652167610270861910253016086584135438525108870543079163776294031601 := by
  refine prime_of_check (a := 4021563102822450340231681687991692159695119011070570348221761014399426255652167610270861910253016086584135438525108870540730885820734607601)
    (b := 4021563102822450340231681687991692159695119011070570348221761014399426255652167610270861910253016086584135438523723797141003077270461583601)
    (x := 3143211871691375361745876088079734135138929477522209263306255521816120854943199003873135390410735442651536695693280739545201609231689232729)
    (y := 3035141326572737715212667973946526117431891746608912744405216787763976279709347189187746081925877858175832840113260315709055125043775977462)
    (d := 392262438678000319195166426243725260166593531511903787343101677733356023074832241160606122219533052317624205495789737946875556413611678474)
    row25 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row23 : Nat.Prime
    362005024263665689826295058826260161447115832900528460465530039472178754178946598036010807099376154304758217619603535101462353582757478229959609 := by
  refine prime_of_check (a := 1)
    (b := 0)
    (x := 289411976403462093477153818883871558067275797386395858471377962577465059913293818919926809243713314013998365551381902809601979629820178703729094)
    (y := 271381882134051527626079008792697479549020179373431508829567231831273293376033233597617066859383260191138267944755259468573154009451801647610815)
    (d := 271503768197749267369721294119695121085336874675396345349147529604134065634209948527008105324532115728568663214702651326096765187068108672469707)
    row24 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row22 : Nat.Prime
    303020287615168265991688368236168157001084226203549253645737040370621420150685042298791784355871615438229140786970886054563597067506848330437326465611 := by
  refine prime_of_check (a := 303020287615168265991688368236168157001084226203549253645737040370621420150685042298791784355871615438229140786970886054563597067504500052481767041611)
    (b := 303020287615168265991688368236168157001084226203549253645737040370621420150685042298791784355871615438229140786970886054562211994104772243931494017611)
    (x := 237356616056169035516944417018376281593912535944716555896157997046586941221875845564217432583419378401902139284682759023099194095482087845885391402341)
    (y := 7978649945889742554883434300071900594181163984429106734953894591653702369812705662357965571143835277504462452722201095150859184394213247637595588490)
    (d := 157207120577414276558852984101716596963101676840505269316368268766347873122633091518366335327897986536233447890761523018820309932370030705705841314190)
    row23 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row21 : Nat.Prime
    686734574801968226048697357245259658043400180760877469988080208854898953866077887728433234485802478217206410506357747204900723016608292279319313784357825967 := by
  refine prime_of_check (a := 0)
    (b := 645924165116617872037162337736833898320602894967047544785115843965422828711003185871011518698638378161320905084265239288594170803975286278141162106839932316)
    (x := 473370640987397954339332578926932225973227222699582167918952265280961423246216393234278225543199569075524833997007724660685143486099272780214472068812883721)
    (y := 376480580572039662334537506602308918002432793847200937367734851262673718407582138191634990565639673155260874636902469640013151253893458260467453475363918274)
    (d := 498451171969365981345771238516423434700001153292514125018502039271096457178965798567576559609971803493351399033023926921039572044743084289675550900965438786)
    row22 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row20 : Nat.Prime
    24221977427742852137210939268681316281058604236899526301008044252820281744780296876595784655226169677579737343282948339396757715379177946925154726657453210074085953027977 := by
  refine prime_of_check (a := 0)
    (b := 8900757169795799877700067228443980916510239390698125222228250734852673630228712215695745490802799147502095957027304177881313417130576033387206364156372077683167906326667)
    (x := 7298023809676061150387976243750509652767866318983183001839531939275667271447209786505609478244986192467390085238174849410743578277213518537115623117136693621160631928629)
    (y := 19730417521417984701066506064654010368389978676377595678108050755652528340762567098066198067366640213860710784459145923300366438945467640873793151991916398427798920509779)
    (d := 6569040459726201904300940561411024765173756684318513942347915807911706035552428555863330008633703946317299746372326651535751615771924497887573618415701422219851881523389)
    row21 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row19 : Nat.Prime
    29089184105865863962110458347739495778965909711171157111500785235107697110991193565180256978722190126836855009991320071431465471549560415685272370729172890550431554359259151105731 := by
  refine prime_of_check (a := 2928006529399707044905271850850561953093234723796036075540097388481653801963059453134777877314996363356442463497027091241580974223612239419653411764020857085807109899769133185063)
    (b := 6328414529118224007589132696216501907897151595714095997429400583736147750289663545469031198151721808251286510636216387198410138827505203988415549086608625096796962823503754200666)
    (x := 27112024308912248350016612188116369736409364626190948574649874184857077784366169942356583869418965537512165348986251536564144874210617572012566900140917273631504363408495300923952)
    (y := 19031342662889648306042187131662927355019999864319097593801014340901733806893279871120743599472930859477346229890152272659134294487228377864742212519250959250529360023964427504673)
    (d := 2513284741206305223891881347492981974675365735362418479566611047973182047879778351929744601541099535432457309273714208444670676332764841280314707755073544601942703937812658792407)
    row20 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row18 : Nat.Prime
    2692721757741535557894232094642744921423925255307703583271757207679896593221453668224564335978832079200820580918634400045871981246404285040116685722819319971258612862032619054725043210336583 := by
  refine prime_of_check (a := 2442887012733481409925449208821014203458525316120783648362454548925143124356123495194427731843090889442786045699885471395525805189537247638128841644194601764536598728851972297774386469370863)
    (b := 110722090040385416912511383286078784631583546451020258452053885153214208546785627399235009684287428181550505099752772727834859534112157818861206349785870481804189171445842023137656983488936)
    (x := 2593837074843685697066699513440866798818025581993883271540437877727342860376260132647832656711931404383274607195555283368906219746108379884636654358445190857883712879558537884904221641549134)
    (y := 2477354559013494891529423074574913148599984430139629271860932754041020701987879470096167799473614568902290073862203765415010021294991887432682410137741513297709541138127108787795071148174398)
    (d := 1361284305070424394986472806469740691969145494342701934597152230832593798893152821441100658981856280064490642369594803319787079190723041701725268982652819104542789711989390736721287566216386)
    row19 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row17 : Nat.Prime
    9261199113879561613365737683549051531774770207216273780607801793447813948413240566539814226127116219326202756194564239214392031636064892628262852598572633980997504839655103349130868046139485939427 := by
  refine prime_of_check (a := 2973833912145082407089884280635239634219541174814324493432295186279945731425272370760856900831942553548174498694891494880681420777948518615549056377281667373040994968040067071446351188312685987959)
    (b := 5440545659350112677199451563412228255679207382600173476149286394754424085024047776300353712566726281624723266295348195563674340551231712915928022029234389271765035475124049896962027218622507257299)
    (x := 492695529215370660938583940781896511718611423743423777207792602682984716058771562414499531240343054493705152287778224839601811616835336764851150916048932663293504120917207077376902953475739067223)
    (y := 7552952315660550747451628599687530738373079526294072902658702142007315269342298813221723875481846632405811790283434189649310715017401306658551750697345591416840769246372232836060750271704621903759)
    (d := 4096535184974457876056343927683352926051303174335782524766381348332672835515264995334922563747905929781183513431668332659886952232303486001166353410055711802796909757278167588233052199829118134165)
    row18 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row16 : Nat.Prime
    48963959715081242249864655132923835448493210085552439478073448081958592345260802875295997813534063438544672858599386638627868046447446509874804902584800505647918157844005441737188729494435428783656419 := by
  refine prime_of_check (a := 7462032411105967384732266667403908235573699196141094882822911390073187909790799018555879830013316550031573381633861980331263234428985704166865167721918287950609363376504134349516350745205842335266379)
    (b := 17848063711737661476610724054849506370583920573377728265725475465525776037644080739605076866043780143845092971861374378231948578947653821453811499639618985938183508452606179148205150989877078617009219)
    (x := 17576650352181397319602092780824794041475975574500015961737663938283037566970141589572332905160038237399456655784032571952250709979605587862069295515623379469111215159031091508581839480358422608937699)
    (y := 33740264762745147279818688876764677769616929705590515467227340664332975959150270932007299444980095884982568151836945800093776572528746074392412308430746249466159915656432080274863535116826494252225349)
    (d := 48925602734631848298203633173553312141888830489064752025978440748212750989265272326559110300826390876738430717981505349516899417241928306980262461008811791434956767381156908862256764679091500977428007)
    row17 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row15 : Nat.Prime
    8274909191848729940227126717464128190795352504458362271794412725851002106349075685925023630487256721036428380523941233266204452755815725968407839369573085478360157270088150454116235602765433386168481749 := by
  refine prime_of_check (a := 825154533925616190586928363522011932258060998113143755861705504170138799614830377613145986544603493956691751399274451836735969056208865127846934750770422894765959375705179373797364808627110841764303411)
    (b := 1188565992692285215466439954731925163226856714742233061167877212405558783515987012000325227088663443332789670997402327577094583011812762188884845002148554508915780208671817676741493892190083243594919092)
    (x := 7112909213067096937078838680354965268665908760429066073086131242002073404310406428227161637862925511789256436526280495697109013407415028563456286719984525898513523677491556501825023202025365497364524276)
    (y := 7605297023281668874974656722746317248375977413870320637788604357363719857827737107842928263359568124053270166481615219784822400649885932473842984085413499989540299572392135651888030021362056737094006432)
    (d := 1807736962127359742434636136493018516171026082188427656728727723654660628661676271371727058268582637626782270210249177977313934544947204943017418088755869146151302046580946590063128114796488915847002885)
    row16 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row14 : Nat.Prime
    4865646604807053204853550509868907376187667272621517015815114682800389238533256503323913894726506951965091853681873007884791576862971627894977654226805982670651048232223219143063164132630673875126552481321 := by
  refine prime_of_check (a := 2685850472004941402198322892592159748903392742008819720616539154738322154360681421409057637107912417628831195205917740569913553449123407234456477876629593971798788238815450706575023415081850177887338598015)
    (b := 4798625485675700237874621953667529160774688225990620282243395396348415850768855540419162242314585176614524570573418866148836204395600026884996499526949208886497232958197129921229002918270256391154436692473)
    (x := 2704768239630308282989483993679045134679543628206477262065861464769071346232924631035437456505459675779358637845537951387421218967793084765850730113090175939485804328723037982691785207618723575237134339775)
    (y := 2697174792013514201388855432345372013698535590982911459630709711725139308639549302145132469248453921723561967537667536235545127989665817036455505242162508278026442339637687839543636725615600599761292894918)
    (d := 1922009833092120050870854338838679742996381907124041381924335009408480560139434629544877140169151671279678023612490906475838685551636668045974617235891895640570108913631459301708833613655710563630049473607)
    row15 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row13 : Nat.Prime
    13930346229562593325495715109754681818025291401515403216278673336857514389920713369016365480601989403476212412430368322138229478663138606966624695279608105690834568289233417937066494690544379415625662133994639 := by
  refine prime_of_check (a := 0)
    (b := 11978630442995116794361233595136807876287579545242344076037190913799885729713743094060912676685117623543704948563627620010691859429364664879274066353241095068410136675178653184358908150025147948387791644085064)
    (x := 7326174857051501895714351778621053552985075177289824465347228215560722515114456369993925520690484266081827795239449311196128750080718484655934918202655309519589019273026499520513965419671256134298306273221967)
    (y := 3135276965628508923274317283260177572913925436319917703471377684471740229593126314868661851368419811771428261150307990348710173235889767131270052886576728557808971102916436790953553218728673565706151093314087)
    (d := 12524076365412529118918144949353659758920896284961177419530366034422791218721070752833730160601396899028457352111711251646870787845655457103662698447614670989216236203677485498011861934552170692733813839745025)
    row14 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row12 : Nat.Prime
    30577779260522749932140564199106006369058019742325411724021695210141693579284627837786817842598580861827225864821107211379369674569085483766573591588322714683015524639989474425478905459019235219675630848391828370685500051 := by
  refine prime_of_check (a := 26420514988852290335110889601765418528487194235338739572897735188707958372461616233283345531231420659135018770841862775417221634489144048077997408025909773948171361762136660386631982028757202175663457786355204452065007794)
    (b := 15237685032391279697561505489039742101226156274098777937001880695134757125970191775715748386411203913168451207634483436066315376856233356281744685607725031676484368957936779078415775239010657754078228081787193716384826572)
    (x := 1282118802711752611278343874673136149260550600133958919593023025441611760243406959700500698690040072170736710299680733382819653968151182505225068431922193574599354699407163541113539364907884729849948375167009453212211855)
    (y := 23808735859113166367901079206063958899635217885612626254246433875595143763952266295606232799442704270477460269126924461284969200063897746093617749659398564955002106957600134806217463673126858493045370745450743322465845905)
    (d := 9701939257916754790436698879278162776644773624476574386646414233719320441108080325764644229163388446204978299137878758190072019227556361995245429541415759320773477764993057300836083578660357424557884179249170871916438146)
    row13 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row11 : Nat.Prime
    865351153072793823079577966834699980244341958707809151789813974447009928293754967809366944945539838389710491974439810676189078404427234529243112839310959620746692168181600424420914787550593460341551530741079511142383532632171 := by
  refine prime_of_check (a := 865351153072793823079577966834699980244341958707809151789813974447009928293754967809366944945539838389710491974439810676189078404427234529243112839310959620746692168181600424420914787550593460341551530676077799160326437464171)
    (b := 865351153072793823079577966834699980244341958707809151789813974447009928293754967809366944945539838389710491974439810676189078404427234529243112839310959620746692168181600424420914787550593453962805535690663870613479275096171)
    (x := 506472088806519160861325335218415568401672245554913648857624596089728996829388206937073593474714496775278598228060030317823757029566104324242293343527252243675186736970756088971246392925195453905565765027766009254563040804240)
    (y := 100101078937612773234584129338597302841880669234538394370828868517466894050811386932726807127418385561125339036718155699770355281105867733255147637011842334970414935304520975346688525096792472142673568526526151538166032194583)
    (d := 739295158946153843465242710260814237087725292599059999725874859910881200314655877101227702421941684237802083706484878768396222164864988512526779566168103248542043087584630124360375217025600462154197143184071028028209483995882)
    row12 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row10 : Nat.Prime
    96919329144152908184912732285486397787366299375274625000459165138065111968900556394649097833900461899647575101136958364291723968808140202443906053337798625889299702688367578758836808119204038464654867369348265881495342421961049 := by
  refine prime_of_check (a := 0)
    (b := 76046348203231209463031694503767605180572856160711900251464408224998714116272832259840128875244375841725046838065488035911846880742815127460437399520311645737520788575845441987295582376964071754682324267622127467615899400418240)
    (x := 67142419690456769707416201787377977354488631145296257485492650332753994940019677070501112380284842917478782137374224588555716679983671394902377319173317644564120104496983169861339888590399077067650950718853605622765372837814809)
    (y := 61388133588210818695057985998399491505180887794310388770173857151491899742019812639146700896314045740155067302722985719422825497538511994439651969558092884627922571641693381350200446104154342785911856305030130767268903692949681)
    (d := 32101159889386072574735812738034599071787829867917652862302753677369414988045628148988043050233385214177242522116886169060010494670029178138428508646316298630276316224777786318521653461235320407970345062997949564910232018254464)
    row11 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row9 : Nat.Prime
    276652156082538064570352559618742104790587628058955693578617749234499369819396038362942860477132313643313192855132707798671314143148963854871090011035310414863422923503387782724711745259875589625928700969786226874676886098936575482758400671 := by
  refine prime_of_check (a := 0)
    (b := 7102928762053036178113681117717879024137348220836845679675542319508320193981895314100860505256731400687487549318947802072644940682540589543256641840778548859043315886996052187908561812876964989146769895863824022369151826124532878975841816)
    (x := 114961504095735786740856888135035789601215032946670906401364040983257156510562782636742280940810173504898130787595625038536816124360546224217191386502715872764450684302281420512939085667098553794424751559582121563897941105956166737746756198)
    (y := 40515550488187943297490098264027496852224775963827803343055952307013292159294648006420137752436810653523450452989817855366408446363522827901662333737503080678417444040966024327892562882031992913710715448669155725000069850529192683307264198)
    (d := 185703580072342621362724879412624192559139331972292155328903598685442751337894513696364415112572087559863030226152766889750559994672815933095116441593090002269286778647483362039441732126969816644622116558438734495312516949625639840777934694)
    row10 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row8 : Nat.Prime
    45370953597536242589537819777473705185656371001668733746893310874457896650380950291522629118249699437503363628241764078969645855139444717082829333449352298299840593052120982182410591906353995381662084047549503340996757749278855235358614641589 := by
  refine prime_of_check (a := 39796380952973011146055466799400324794214888970384475977284941873057804920524543898695024088460621537103781490867037231510430284854980341330797120140040607670240220644952037826678710349003011698616335546510691240867162620037753604896896562557)
    (b := 15387616444750731977455508919762411323737891427911525960439285602488925339826293047345586494548642087900425703785336478672711009514553576931899730532944493971445096622183345742889462349974264308664365159273098152551615336037167766628588858243)
    (x := 1183467576083552254845869623623603123416445605090460779538331683662513104090940100916381867072023994248833985832020731213187189428685085372370353717363833841235952268900934145789770998018641156558350009623809900680352734199567566287796680080)
    (y := 34467712296364713916464303235126437236262029202180538146866626468881303178151761545097383849396868800130835108772332273183676606412430419325959874672818047432323571359408421607758052834615116473608645105710990332932130098794290780424677448723)
    (d := 3780769014787582874789983707317874090718769201731429918755160207282278014275511186197777085095353143099774421266163204206849543002576708115084897469818778646695961511067489032868426502281689282802147316177641752367637999597795862949826020050)
    row9 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row7 : Nat.Prime
    673958309626693499011065295137121942156664385228975116401660068314818926003041827086960912091540831786797776040544648736151373579579004107611207241404865618920051301077181401082003134791489448080828078124437393568698051226411879860981065851186445560920829619183 := by
  refine prime_of_check (a := 362786397983357278679026994497509016632459370879595167881260566484825548783206437023147864742841849044111303204769106414636815413637320812740886092583568284174642843836188116378581007247483211906128678029652590886016855258220751925422796668970252235560213393449)
    (b := 534099574824583624540171204676139617312369368697042482470189795608570210904303703778359788173185523580085964652574785070741433098313741659583285569428904041691004515632400358062131417856470530383844279428758937925512250205307426739863781468942476365248130320400)
    (x := 203788222829028693648409353517856733880077881597475129638377343583680577270814065777105105552437180730425879184943641015561462179460265636865103608371944779233150276220873931772374492409711843710265018255973546781314709629333784729011962487050860621840301005950)
    (y := 390849674585501818648777444414995038685797051500497104534423120079940795306000074294126742464881675635217547178611593024798214183789654937152129761171287273517968600463138568113927049871494396386456246982765102149199372001520850270287692008316531025029048563194)
    (d := 643004731595519593948735489970282331415056178441506731959543311465240709806813438103332588424616084308761543576485638295988176867692793254106153901510220905790775496560788026914575343861237659933243788334318227566938417287866352091119661494938264053358465859014)
    row8 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row6 : Nat.Prime
    2695833238506773996044261180548487768626657540915900465606640273259275704012167308347843648366163327147191104162178594944605494318319222804646959961631714017221466466702243691299100423407948771300826769202225589992900094931759498625280782376894108726265773266779 := by
  refine prime_of_check (a := 2695833238506773996044261180548487768626657540915900465606640273259275704012167308347843648366163327147191104162178594944605494318319222804646959961631714017221466466702243691299100423407948771300826769202225589992900094931759498625280782376891760448310213842779)
    (b := 1385073402076086505832448000)
    (x := 437649454245511004752121621115020057485605051500458169721679195569958267853295342465349401425215373964079322654284802272625175088673325966165373429107248640655344940702051320743728164906693808850846755540339642312677715808122301949292965386461320343484208597318)
    (y := 1006610354333905999414613054449251609095829861485363160489920355901237442097783136070092504361357922990840843901661881502685663087274575860283600488741112372341821328500035732212339184256939655904618211057396479789768122942775422795071917469204032170184011619220)
    (d := 1643575098976321803242779322401941311301628922509199009255495265270193967854361549552334239073980232690421423038126549169757149039641979712812878025070064996631570027993499834672239253462010826748745877556576597083432266943415033550903632664861621796448561636381)
    row7 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row5 : Nat.Prime
    16452158677116503221383992649620232887598589765914831094829569278003264301873009509905453849080918932229367894834703524963679073818467399798721813411054178207494450634168632240039433896017561170432918507781726388748996955960647873262979243717174086439124788132632060412763 := by
  refine prime_of_check (a := 15397335669799682021320060154894274399285004137663789180831080457620080314529824233382759345290642968164634632068698410753984583878871477954640004479518531187741813764014870559337052632154740409690554749307379189027612484381626104632797698842886274073846227599413336450042)
    (b := 4943558603504993536660935622008081997488136454793433507312794717409635845070707979853620742829828861371180328156130734234989847004937059937071655483612201499137041542122771473699969431152885126621569168322622754290125649588182875625916711758397343243801084131705146408568)
    (x := 4001866309623685205633250768800210551018691728426309835266733475136457003174106150096688932430329234219799383071015350165401324965730691858080802391430778229411414128527332783177766602573285244139245676154272033304137858804447316189737762769135842910531322017474452336422)
    (y := 370532473492407099120695857519033632941837171556123132022651362222725458956442681047184141838752141662723071788238482436838471461692343402002846640884001432247713395577568674036423946894423170387673310175495265613131651386949847001065104594451170053367028379949464946814)
    (d := 2768200562951587181711120892718456284754525324016036971867338718194159465216707568293204387281762727779861364143159322151991027479733698490732600018938205262694461752627173460175780799067356350115235104299915149812847808753026687311947935832730708059197967550158010086834)
    row6 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row4 : Nat.Prime
    253889712705261877712397774568939433921421437267597673455409913098146374706504282756860963799016740962163605353089144797239495467166588912841472474919172627790724585228433607911543720270756931614480032867112043978292958342788170435928640000934168123642333430312830516685237521 := by
  refine prime_of_check (a := 106561025071809733985538752611188145494200773217553811296563180166764683199852482993626613189897708195020525971738262073464570718536915097846450174037491809766159373915067000944607396112622508445655660099644526086057447556124903992542920696941830837136884425942344600548767681)
    (b := 7593601039864399418914635928112511365303503185431509812958459787350948185835021432648900672329976299416137518048124193303723394907190685297563761831480062143388298783979955001612972630073353374543407205747924979466445797261966496735589141441567553917731573331598378767282116)
    (x := 117915511906770884108572188044433462636427621415728971208446740675481476243418652285348636693411769788510504541800988453367262262210246979491609103123152153018636618753690202289723643827135105702893139978344902543990080271123051802498043620984524098941130972356646387422509002)
    (y := 42370408228707627024619953025644703160707797879818814316703596029431494845090835909107377658940539814482378468358744098041462622419998316756506260500740653789937927379574010917295730711552156093359521790444905310749213199719818963382207229106209929129329959001862398406386612)
    (d := 222227385617914033975583581679527663196061644342090221287983374826118602431388077774870039416299160391247235973526066954809281927262183008586657556742295933898301271072487215662129006313641709036439067055555983618496590182205467722585320941649780328625487855512433848308809599)
    row5 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row3 : Nat.Prime
    89005608803658245945879863035083959470964870420027181187916142414990978288109793397507234357093700845623770801421755313278655446933656741997496623016164783945899541015725709797056707201114711627375017449788870544203721189826568418475791939681621594372198070223558752804306149744297 := by
  refine prime_of_check (a := 24360992039880195290937381385317983465510652775783593346067444797284090319840241303717932723210005306261700458399025348175128173589427991333288322041441839558211215597622531097074181265171539035905981556694100924965155738330725758931059110345889530853587759024133476091140525276141)
    (b := 45386140323030645606484038219310317017987957104784803341889750364263107667147174343290287399879831584207104022187374422722455520526923399121678313910731888315818739115541989761612008795721989454033582135507063970346623504277610447504873379609596421736335333152993671717135548727710)
    (x := 58050636505732596445637778668125983750658765705305226614778764722751960460401568314631629376567969120385149913226219921668525578409433345101030761886376096518872053368774191505874543895455263433209668089382979650364978704221103146119023013986545382207638413335305373072938101974615)
    (y := 68851568433794226438630509439159823579973431421478764643007665265556690995473408856940863288017346992820928075901224570189037854552129080810017539859762102327373810643257027554714325985390966996801294940407288899231575749865612792871853946378465387370063217930388060812376575353578)
    (d := 12505273489564756051755907960433347104531384805285746426039382792313187823160918318032438368558938527535437046517389581056646084015234739301929959584428707186581919703135990110807106039179800374343209647132117672127851805734098686442706809017295469456651343771329677617308941097141)
    row4 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row2 : Nat.Prime
    216424820947287910957674299831023655626566119425016567196707337928143375271092634873134452767974484880290466632658821636886655441709267680857526503404286238779892266592701501800268741445461149367310897329171026899427344743833774806969476639118963439156601509339754876741334961939865146330903725584557549 := by
  refine prime_of_check (a := 189882096020688210652686684531890695255275818638674939965991709160065790775114702149433732719811882952380278521353656448196457588365572863021020732560416452587669504129278797372290240800842825750314603876633284214025944305542308574073480047594528016136754715543633889017336604753334275489950158439089196)
    (b := 1003780667743988123219632979677486046466067963535123410801055521489634008521505740664935725400413335374810584764411300784145881970340168589123628969307125933141704485566530046764759441472122052024977520370591502476312958529205266526491558491015779793272923841898146961482452988112901105550814551294848)
    (x := 33399001975681982186766898724036503114079654989782206401107925371531430823237107722833595892931798337627104723064038048366983254055733706840333031818181767698986548640104349677383266839940393548970569329041271743800372903410081850454060220596951661072572625432490502405493103619083244312644726069088009)
    (y := 209412796011968110165584503020378309260764891680725755934202295294609306088404656279450549027042258997919870541873600029975073385724795264226483875793267791135840075864075338472173698528785970064122858399314951994203885875883930625240576884669526000303728827245874246762525976920780530449298236818411622)
    (d := 207011747425881221504340468669995230287758606560595488070451905344649781439266912512917339186765986590668923776028825039145027598001038049806029137040638096671232375260954145914729764586112892063873093213296476779463223942386950072572720734540544102945934639586109809969587413945909349731998755730004468)
    row3 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row1 : Nat.Prime
    19911083527150487808106035584454176317644082987101524182097075089389190524940522408328369654653652608986722930204611590593572300637252626638892438313194384831058728760389162623063843991495986189046678065967808876509929271282353118197287487284561316865241583054243447324368133865979947697586877876155639877 := by
  refine prime_of_check (a := 19911083527150487808106035584454176317644082987101524182097075089389190524940522408328369654653652608986722930204611590593572300637252626638892438313194384831058728760389162623063843991495986189046678065967808876509929271282353118197287487284561316865241583054243447324368133865979947697586877876103972002)
    (b := 19911083527150487808106035584454176317644082987101524182097075089389190524940522408328369654653652608986722930204611590593572300637252626638892438313194384831058728760389162623063843991495986189046678065967808876509929271282353118197287487284561316865241583054243447324368133865979947697586877700381529127)
    (x := 13928161580822725620292919837016425761510107013736519751250045069711682989243346464933720599076052369927276126256686515685707878019763391701134530069671326565196584919421471186842683541987046312133324596209794280956722474630630579463556696255074769624953667660790610403136239341228306243774812062184683413)
    (y := 13479576592869399452901976949624858900666818855159352696828804661044278815079559453330607016020788968194030909156226610240542079467337049275109067603999711179722045361594209739279413461071542879836417689639447362144400390792885243857104601433461491670689835229190267675752414236332142189919327940312158857)
    (d := 7501370912499151315049817982625646693609921136631556233155610019626481004258554250390449692538121725892433328152906869480630362710739967594322308131874965217194652264969086907601623776916042168768249842676489860732092935929875635653791821366715182728069913373527744028706596641111096383672272087004026701)
    row2 (by rfl) ?_
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem row0 : Nat.Prime
    9999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999997793 := by
  refine prime_of_check (a := 1105266768478904207204981280965949346564587965060668597758396371313500666713359038842134472811016360921354542357567986124304106269675182219698035849833407388986516227284144574927442664533589782863064448213080945645648885989196868415976958402795025435321790455009725767441215560658916063921794778377272314140680641952)
    (b := 6236831463752588823176950055437724355689102035841031356539460265358003123276412544783515829861328399410142465358869315086405609691374052716305516046539964104731087095322032524873089676479984562118161338933360883489879632105897770768247827501588491200216051870167583206894935408247971578217850896263728388574342448315)
    (x := 4890104778155375379268044005869619571513309421385795636894260084425695564473805935716880815678636798083869343750424494700707016621906562426369573435315465897182383914917857963728712681915504608336240621724482203660916132937684188800442972265816529825346392902090175983725371523411178730698925549359082470842445521405)
    (y := 5480898357851251378413511266288060096927262193002480751518949639833774494365810409814313969140650726838449819177600394676579982919086714159639706961588840419100286448961167600423262116776890350967141370053172853778984339763941829946852106619931383352302207237932824712205892404164931845643102743923873565489684010225)
    (d := 2290895026137120378583130431077944454794571663161714552158256172355641238633597272666183781720930023768175517577116458817249684423248648999941203905571457491324176099072224896748219821080368261128173824420202689228345440486147783840958886173774619832758803569058623795537265631252859837678073833739677186438636070463)
    row1 (by rfl) ?_
  decide +kernel

end Rfc11CutpointCertificate

/-- V16: the two specified addends at the RFC1.1–RFC1.2 cutpoint. -/
theorem Conjectures.Goldbach.Rfc11Rfc12CutpointWitness :
    Nat.Prime 2207 ∧ Nat.Prime (10^316-2207) := by
  constructor
  · norm_num
  · apply Eq.mp (congrArg Nat.Prime ?_) Rfc11CutpointCertificate.row0
    decide +kernel
