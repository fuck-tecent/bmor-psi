import Mathlib
import Conjectures.Goldbach.SharpSingularSeriesRatios

/-! The CRT reduction below adapts the proof of `reduced_gap_sharp` in
`SharpSingularSeriesRatios.lean` (goldbach-proofs, Apache-2.0).
Here we retain the prime responsible for the loss, including whether it divides the target. -/

namespace Conjectures.Goldbach.NearExtremalProof

open SharpSingularSeriesRatiosProof
open Finset DirichletCharacter Real TwistedGoldbachLocalProduct TwistedGoldbachConductorRatio
open TwistedGoldbachConductorValue TwistedGoldbachConductorComponents TwistedGoldbachExceptionalGap
open B13BilateralVaughanReductionProof
open scoped BigOperators Classical

private theorem large_prime {p : ℕ} (h : 7 ≤ p) : sqrt 2 * sqrt p ≤ (p:ℝ) - 2 := by
  have h' : (7:ℝ) ≤ p := by exact_mod_cast h
  apply (sq_le_sq₀ (by positivity) (by linarith)).mp
  rw [mul_pow, sq_sqrt (by norm_num : (0:ℝ) ≤ 2), sq_sqrt (Nat.cast_nonneg _)]
  nlinarith [mul_nonneg (sub_nonneg.mpr h') (show 0 ≤ (p:ℝ)+1 by positivity)]

private def Bad (p t m : ℕ) : Prop :=
  (p=2 ∧ 8 ≤ t) ∨ (p=3 ∧ 27 ≤ t) ∨ (p=5 ∧ (25 ≤ t ∨ 5 ∣ m)) ∨ 7 ≤ p

private theorem arithmetic_bound {p t m : ℕ} (pt : p ≤ t) (he : Even m) (bad : Bad p t m) :
    sqrt 2 * (p:ℝ) ≤ (if p ∣ m then (p:ℝ)-1 else (p:ℝ)-2) * sqrt t := by
  have s2 := sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have st := sq_sqrt (Nat.cast_nonneg t : (0:ℝ) ≤ t)
  have hs := sqrt_nonneg (t:ℝ)
  have root : sqrt 2 ≤ 3/2 := (sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
  rcases bad with ⟨rfl,ht⟩ | ⟨rfl,ht⟩ | ⟨rfl,ht | hd⟩ | large
  · rw [ite_eq_left (even_iff_two_dvd.mp he)]
    have ht' : (8:ℝ) ≤ t := by exact_mod_cast ht
    norm_num
    apply (sq_le_sq₀ (by positivity) hs).mp
    nlinarith only [s2, st, ht', show (sqrt 2 * 2)^2 = (sqrt 2)^2 * 4 by ring]
  · have ht' : (27:ℝ) ≤ t := by exact_mod_cast ht
    have z : (5:ℝ) ≤ sqrt t := le_sqrt_of_sq_le (by linarith)
    split_ifs <;> norm_num <;> linarith
  · have ht' : (25:ℝ) ≤ t := by exact_mod_cast ht
    have z : (5:ℝ) ≤ sqrt t := le_sqrt_of_sq_le (by linarith)
    split_ifs <;> norm_num <;> linarith
  · rw [ite_eq_left hd]
    have ht' : (5:ℝ) ≤ t := by exact_mod_cast pt
    have z : (2:ℝ) ≤ sqrt t := le_sqrt_of_sq_le (by linarith)
    norm_num
    linarith
  · have hl : (7:ℝ) ≤ p := by exact_mod_cast large
    have prod := mul_le_mul (large_prime large) (sqrt_le_sqrt (by exact_mod_cast pt : (p:ℝ) ≤ t))
      (sqrt_nonneg _) (show 0 ≤ (p:ℝ)-2 by linarith)
    rw [mul_assoc,mul_self_sqrt (Nat.cast_nonneg p)] at prod
    split_ifs
    · exact prod.trans (mul_le_mul_of_nonneg_right (by linarith) hs)
    · exact prod

private theorem local_power {p : ℕ} [hp : Fact p.Prime] (n m : ℕ) (he : Even m)
    {A B : DirichletCharacter ℂ (p*p^n)} (hA : A.IsPrimitive) (hB : B.IsPrimitive) :
    let q := p*p^n
    let t := q/(m.gcd q)
    p ≤ t → Bad p t m →
    sqrt 2 * ‖J A B (m:ZMod q)‖ ≤ ‖J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q)‖ := by
  intro q t pt bad
  have bound := prime_power_bound n m hA hB (hp.out.one_lt.trans_le pt)
  have G := arithmetic_bound pt he bad
  have P : 0 < sqrt (t:ℝ) := sqrt_pos.mpr (by exact_mod_cast hp.out.pos.trans_le pt)
  apply le_of_mul_le_mul_right (a := sqrt (t:ℝ)) _ P
  rw [ordinary_prime_power n m]
  change ‖J A B (m:ZMod q)‖*sqrt t ≤ (↑(p*p^n):ℝ) at bound
  push_cast at bound ⊢
  calc
    _ = sqrt 2 * (‖J A B (m:ZMod q)‖ * sqrt t) := by ring
    _ ≤ sqrt 2 * ((p:ℝ) * (p:ℝ)^n) := mul_le_mul_of_nonneg_left bound (sqrt_nonneg _)
    _ = (p:ℝ)^n * (sqrt 2 * p) := by ring
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left G (by positivity : 0 ≤ (p:ℝ)^n)

private theorem local_prime {p : ℕ} [Fact p.Prime] (m : ℕ)
    (A B : DirichletCharacter ℂ p) (mp : ¬p ∣ m) (hab : A ≠ 1 ∨ B ≠ 1) (big : 7 ≤ p) :
    sqrt 2 * ‖J A B (m:ZMod p)‖ ≤ ‖J (1 : DirichletCharacter ℂ p) 1 (m:ZMod p)‖ := by
  have nonzero : (m:ZMod p) ≠ 0 := mt (ZMod.natCast_eq_zero_iff m p).mp mp
  have top := SquarefreeTwistedGoldbachDensity.local_norm A B (m:ZMod p)
  have ordinary := SquarefreeTwistedGoldbachDensity.local_norm (1 : DirichletCharacter ℂ p) 1 (m:ZMod p)
  have pair : ¬(A=1 ∧ B=1) := by tauto
  simp only [nonzero,ite_false,pair] at top
  simp only [nonzero,ite_false,and_self,ite_true] at ordinary
  change sqrt 2*‖SquarefreeTwistedGoldbachDensity.localSum A B (m:ZMod p)‖ ≤
    ‖SquarefreeTwistedGoldbachDensity.localSum (1 : DirichletCharacter ℂ p) 1 (m:ZMod p)‖
  rw [top,ordinary]
  split_ifs
  · have h : (7:ℝ) ≤ p := by exact_mod_cast big
    have hb : sqrt 2 ≤ 2 := (sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
    linarith
  · exact large_prime big

private theorem reduced_prime_part {L p : ℕ} (hp : p.Prime) (hL : L ≠ 0) (m : ℕ) :
    let q := p^L.factorization p
    q/(m.gcd q) = p^(L/(m.gcd L)).factorization p := by
  intro q
  let g := m.gcd L
  have gd : g ∣ L := Nat.gcd_dvd_right ..
  have Q : q ∣ L := Nat.ordProj_dvd L p
  have same : m.gcd q = q.gcd g := by
    change m.gcd q = q.gcd (m.gcd L)
    rw [Nat.gcd_left_comm,Nat.gcd_eq_left Q]
  have gq := prime_part_gcd hp hL gd
  change q.gcd g = p^g.factorization p at gq
  have le := (Nat.factorization_le_iff_dvd (Nat.gcd_pos_of_pos_right m (Nat.pos_of_ne_zero hL)).ne' hL).mpr gd p
  rw [same,gq,Nat.factorization_div gd]
  exact Nat.pow_div le hp.pos


private theorem primitive_source_dvd {p L r n : ℕ} (hp : p.Prime)
    (hr : r ∣ L) (good : TwistedGoldbachConductorValue.admissible r L)
    (hd : p^(n+2) ∣ L) : p^(n+2) ∣ r := by
  let a := L/r
  have eqn : r*a=L := Nat.mul_div_cancel' hr
  have hpow : p^(n+2) ∣ r*a := eqn ▸ hd
  by_cases hdpa : p ∣ a
  · have cop : p.Coprime r := good.2.of_dvd_left hdpa
    have all : p^(n+2) ∣ a := (cop.pow_left _).dvd_of_dvd_mul_left hpow
    have bad : p*p ∣ a := (show p*p ∣ p^(n+2) by rw [← pow_two]; exact pow_dvd_pow _ (by omega)).trans all
    exact False.elim (Nat.squarefree_iff_prime_squarefree.mp good.1 p hp bad)
  · exact ((hp.coprime_iff_not_dvd.mpr hdpa).pow_left _).dvd_of_dvd_mul_right hpow

private theorem complementary_odd {L r m : ℕ} (rL : r ∣ L) (he : Even m)
    (good : TwistedGoldbachConductorValue.admissible r L)
    (div : L/r ∣ L/(m.gcd L)) : ¬2 ∣ L/r := by
  let a := L/r
  let g := m.gcd L
  let j := L/g
  have ra : r*a=L := Nat.mul_div_cancel' rL
  have gj : g*j=L := Nat.mul_div_cancel' (Nat.gcd_dvd_right m L)
  intro ha
  have cp : Nat.Coprime 2 r := good.2.of_dvd_left ha
  have twoL : 2 ∣ L := ra ▸ ha.trans (dvd_mul_left a r)
  have hdg : 2 ∣ g := Nat.dvd_gcd (even_iff_two_dvd.mp he) twoL
  have bad : 2*2 ∣ L := gj ▸ Nat.mul_dvd_mul hdg (ha.trans div)
  have badA : 2*2 ∣ a := (cp.pow_left 2).dvd_of_dvd_mul_left (ra ▸ bad)
  exact Nat.squarefree_iff_prime_squarefree.mp good.1 2 Nat.prime_two badA

private theorem small_complement {a : ℕ} (h : a ∣ 36) (hs : Squarefree a)
    (odd : ¬2 ∣ a) : a ∣ 3 := by
  have le := Nat.le_of_dvd (by decide : 0 < 36) h
  have hn : ¬ 9 ∣ a := Nat.squarefree_iff_prime_squarefree.mp hs 3 Nat.prime_three
  interval_cases a <;> norm_num at *


private theorem local_power_cast {p q : ℕ} [Fact p.Prime] [NeZero q] (n : ℕ)
    (eqn : q=p*p^n) (m : ℕ) (he : Even m) (A B : DirichletCharacter ℂ q)
    (hA : A.IsPrimitive) (hB : B.IsPrimitive) :
    let t := q/(m.gcd q)
    p ≤ t → Bad p t m →
    sqrt 2 * ‖J A B (m:ZMod q)‖ ≤ ‖J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q)‖ := by
  subst q
  exact local_power n m he hA hB


private theorem locate {j m : ℕ} (jp : 0 < j) (outside : ¬ j ∣ 36)
    (clean : ∀ p : ℕ, p.Prime → p ∣ j → ¬ Bad p (p^j.factorization p) m) :
    5 ∣ j ∧ j ∣ 180 ∧ ¬5 ∣ m := by
  have bound : j ∣ 180 := by
    apply (Nat.factorization_le_iff_dvd jp.ne' (by decide : (180:ℕ) ≠ 0)).mp
    intro p
    by_cases hp : p.Prime
    · by_cases d : p ∣ j
      · have no := clean p hp d
        have hsmall : p < 7 := by by_contra! h; exact no (.inr (.inr (.inr h)))
        have which : p=2 ∨ p=3 ∨ p=5 := by interval_cases p <;> norm_num at *
        have expBound (k : ℕ) (deny : ¬ p^k ≤ p^j.factorization p) : j.factorization p < k := by
          by_contra! h
          exact deny (Nat.pow_le_pow_right hp.pos h)
        rcases which with rfl | rfl | rfl
        · have h := expBound 3 (fun hh => no (.inl ⟨rfl,hh⟩))
          exact le_trans (by omega : j.factorization 2 ≤ 2)
            ((Nat.prime_two.pow_dvd_iff_le_factorization (by decide : (180:ℕ) ≠ 0)).mp (by decide : 2^2 ∣ 180))
        · have h := expBound 3 (fun hh => no (.inr (.inl ⟨rfl,hh⟩)))
          exact le_trans (by omega : j.factorization 3 ≤ 2)
            ((Nat.prime_three.pow_dvd_iff_le_factorization (by decide : (180:ℕ) ≠ 0)).mp (by decide : 3^2 ∣ 180))
        · have h := expBound 2 (fun hh => no (.inr (.inr (.inl ⟨rfl,.inl hh⟩))))
          exact le_trans (by omega : j.factorization 5 ≤ 1)
            (((by decide : Nat.Prime 5).pow_dvd_iff_le_factorization (by decide : (180:ℕ) ≠ 0)).mp (by decide : 5^1 ∣ 180))
      · simp [Nat.factorization_eq_zero_of_not_dvd d]
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  have five : 5 ∣ j := by
    by_contra nd
    have cop := ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr nd).symm
    exact outside (cop.dvd_of_dvd_mul_left (show j ∣ 5*36 from bound))
  exact ⟨five, bound, fun dm => clean 5 (by decide) five (.inr (.inr (.inl ⟨rfl,.inr dm⟩)))⟩

private theorem strong_localization {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m)
    (out : ¬(r/(m.gcd r) ∣ 36 ∧ s/(m.gcd s) ∣ 36 ∧ r/(r.gcd s) ∣ 3 ∧
      s/(r.gcd s) ∣ 3 ∧ (inversePair α β).conductor ∣ 36))
    (high : ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ <
      sqrt 2 * ‖series α β m‖) :
    let j := Nat.lcm r s / m.gcd (Nat.lcm r s)
    5 ∣ j ∧ j ∣ 180 ∧ ¬5 ∣ m := by
  classical
  let L := Nat.lcm r s
  let j := L/(m.gcd L)
  let d := (inversePair α β).conductor
  have nv : series α β m ≠ 0 := by
    intro h
    rw [h, norm_zero, mul_zero] at high
    exact (not_lt_of_ge (norm_nonneg _)) high
  have good : supported r s L d j := (full_support hα hβ m hm he).mp nv
  have hr : r ∣ L := Nat.dvd_lcm_left ..
  have hs : s ∣ L := Nat.dvd_lcm_right ..
  have outside : ¬j ∣ 36 := by
    intro h36
    obtain ⟨ra,sa⟩ := TwistedGoldbachConductorSuppression.complementary_dvd hα hβ (m := m) good
    have rj := ra.trans good.2.2.1
    have sj := sa.trans good.2.2.1
    have rsmall := small_complement (rj.trans h36) good.1.1 (complementary_odd hr he good.1 rj)
    have ssmall := small_complement (sj.trans h36) good.2.1.1 (complementary_odd hs he good.2.1 sj)
    have eqr : L/r=s/(r.gcd s) := by
      change (Nat.lcm r s)/r=s/(r.gcd s)
      rw [Nat.lcm_eq_mul_div,Nat.mul_div_assoc _ (Nat.gcd_dvd_right r s),Nat.mul_div_cancel_left _ (NeZero.pos r)]
    have eqs : L/s=r/(r.gcd s) := by
      change (Nat.lcm r s)/s=r/(r.gcd s)
      rw [Nat.lcm_comm,Nat.lcm_eq_mul_div,Nat.mul_div_assoc _ (Nat.gcd_dvd_right s r),
        Nat.mul_div_cancel_left _ (NeZero.pos s),Nat.gcd_comm]
    have splitj : j=Nat.lcm (r/(m.gcd r)) (s/(m.gcd s)) := TwistedGoldbachConductorSuppression.reduced_lcm m
    exact out ⟨(splitj ▸ Nat.dvd_lcm_left ..).trans h36, (splitj ▸ Nat.dvd_lcm_right ..).trans h36,
      eqs ▸ ssmall, eqr ▸ rsmall, good.2.2.1.trans h36⟩
  have lp : 0 < L := Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)
  let _ : NeZero L := ⟨lp.ne'⟩
  have jd : j ∣ L := Nat.div_dvd_of_dvd (Nat.gcd_dvd_right m L)
  have jp : 0 < j := Nat.pos_of_dvd_of_pos jd lp
  apply locate jp outside
  intro p hp pj bad
  let _ : Fact p.Prime := ⟨hp⟩
  have pl : p ∣ L := pj.trans jd
  let i : L.primeFactors := ⟨p,Nat.mem_primeFactors.mpr ⟨hp,pl,lp.ne'⟩⟩
  let (k : L.primeFactors) : NeZero ((k:ℕ)^L.factorization k) := ⟨(Nat.ordProj_pos L k).ne'⟩
  let e := ZMod.equivPi L lp.ne'
  let Q := p^L.factorization p
  let _ : NeZero Q := ⟨(Nat.ordProj_pos L p).ne'⟩
  let A := component e (changeLevel hr α) i
  let B := component e (changeLevel hs β) i
  let t := Q/(m.gcd Q)
  have qpos : 0 < Q := Nat.ordProj_pos ..
  have tpos : 0 < t := Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right m Q)) qpos
  have eqt : t=p^j.factorization p := reduced_prime_part hp lp.ne' m
  have pt : p ≤ t := by
    rw [eqt]
    have hd := (hp.dvd_iff_one_le_factorization jp.ne').mp pj
    simpa only [pow_one] using Nat.pow_le_pow_right hp.pos hd
  have ob : Bad p t m := eqt ▸ bad
  have ha : A.conductor=Q.gcd r := by
    dsimp only [A]
    rw [component_conductor e (fun k : L.primeFactors => Nat.ordProj_dvd L k)
      L.pairwise_coprime_pow_primeFactors_factorization,conductor_changeLevel,hα]
  have hb : B.conductor=Q.gcd s := by
    dsimp only [B]
    rw [component_conductor e (fun k : L.primeFactors => Nat.ordProj_dvd L k)
      L.pairwise_coprime_pow_primeFactors_factorization,conductor_changeLevel,hβ]
  have vpos := (hp.dvd_iff_one_le_factorization lp.ne').mp pl
  have loc : sqrt 2 * ‖J A B (m:ZMod Q)‖ ≤ ‖J (1 : DirichletCharacter ℂ Q) 1 (m:ZMod Q)‖ := by
    by_cases v : L.factorization p=1
    · have Qp : Q=p := by simp [Q,v]
      let _ : Fact Q.Prime := ⟨Qp ▸ hp⟩
      have tl : t ≤ p := Qp ▸ Nat.div_le_self Q (m.gcd Q)
      have mp : ¬Q ∣ m := by
        intro H
        have te : t=1 := by dsimp only [t]; rw [Nat.gcd_eq_right H,Nat.div_self qpos]
        have := hp.one_lt
        omega
      have large : 7 ≤ Q := by
        rw [Qp]
        rcases ob with ⟨h2,ht⟩ | ⟨h3,ht⟩ | ⟨h5,ht | hd⟩ | h7
        · omega
        · omega
        · omega
        · exact False.elim (mp (by simpa [Qp,h5] using hd))
        · exact h7
      have neq (χ : DirichletCharacter ℂ Q) (H : χ.conductor=Q) : χ ≠ 1 := by
        intro E
        rw [E,conductor_one] at H
        omega
      apply local_prime m A B mp _ large
      rcases hp.dvd_mul.mp (pl.trans (Nat.lcm_dvd_mul r s)) with pr | ps
      · exact .inl (neq A (ha.trans (Nat.gcd_eq_left (Qp ▸ pr))))
      · exact .inr (neq B (hb.trans (Nat.gcd_eq_left (Qp ▸ ps))))
    · obtain ⟨n,hn⟩ : ∃ n : ℕ, L.factorization p=n+2 := ⟨L.factorization p-2,by omega⟩
      have Qd : p^(n+2) ∣ L := by simpa [hn] using Nat.ordProj_dvd L p
      have Qr : Q ∣ r := by simpa [Q,hn] using primitive_source_dvd hp hr good.1 Qd
      have Qs : Q ∣ s := by simpa [Q,hn] using primitive_source_dvd hp hs good.2.1 Qd
      have eqQ : Q = p*p^(n+1) := by dsimp only [Q]; rw [hn,pow_succ' p (n+1)]
      exact local_power_cast (n+1) eqQ m he A B (ha.trans (Nat.gcd_eq_left Qr))
        (hb.trans (Nat.gcd_eq_left Qs)) pt ob
  have full := single_factor e hα hβ hr hs m hm he i
  let O := ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖
  let V := ‖J A B (m:ZMod Q)‖
  let W := ‖J (1 : DirichletCharacter ℂ Q) 1 (m:ZMod Q)‖
  have wp : 0 < W := norm_pos_iff.mpr (principal_ne_zero Q m he)
  change ‖series α β m‖*W ≤ O*V at full
  change sqrt 2*V ≤ W at loc
  have contracted : sqrt 2 * ‖series α β m‖ ≤ O := by
    apply le_of_mul_le_mul_right (a := W) _ wp
    calc
      _ = sqrt 2 * (‖series α β m‖ * W) := by ring
      _ ≤ sqrt 2 * (O * V) := mul_le_mul_of_nonneg_left full (sqrt_nonneg _)
      _ = O * (sqrt 2 * V) := by ring
      _ ≤ O * W := mul_le_mul_of_nonneg_left loc (norm_nonneg _)
  exact (not_lt_of_ge contracted) high

end Conjectures.Goldbach.NearExtremalProof

open Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachConductorValue in
theorem Conjectures.Goldbach.NearExtremalReducedConductor :
by
  classical
  let S := fun {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) =>
    ∑' q : ℕ, if hq : q ≠ 0 then
      let _ : NeZero q := ⟨hq⟩
      if h : r ∣ q ∧ s ∣ q then
        let A := DirichletCharacter.changeLevel h.1 α
        let B := DirichletCharacter.changeLevel h.2 β
        gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
          gaussSum (A*B)⁻¹ (ZMod.stdAddChar.mulShift (-(m:ZMod q))) / (q.totient:ℂ)^2
      else 0
    else 0
  let O := S (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)
  let X := fun {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) =>
    r/(m.gcd r) ∣ 36 ∧ s/(m.gcd s) ∣ 36 ∧ r/(r.gcd s) ∣ 3 ∧ s/(r.gcd s) ∣ 3 ∧
      ((DirichletCharacter.changeLevel (Nat.dvd_lcm_left r s) α)*
       (DirichletCharacter.changeLevel (Nat.dvd_lcm_right r s) β)).conductor ∣ 36
  exact ∀ (r s : ℕ) [NeZero r] [NeZero s] (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
    α.IsPrimitive → β.IsPrimitive → ∀ m : ℕ, 0 < m → Even m → ¬X α β m →
    ‖O m‖ < Real.sqrt 2 * ‖S α β m‖ →
    let j := Nat.lcm r s / Nat.gcd m (Nat.lcm r s)
    5 ∣ j ∧ j ∣ 180 ∧ ¬ 5 ∣ m := by
  classical
  intro S O X r s _ _ α β hα hβ m hm he out high
  refine Conjectures.Goldbach.NearExtremalProof.strong_localization hα hβ m hm he ?_ high
  simpa only [X, inversePair, DirichletCharacter.conductor_inv] using out
