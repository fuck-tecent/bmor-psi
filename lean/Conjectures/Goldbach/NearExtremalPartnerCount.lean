import Mathlib
import Conjectures.Goldbach.NearExtremalReducedConductor

open DirichletCharacter

private theorem partner_eq_of_common_lift {q r s : ℕ} [NeZero q]
    {a : DirichletCharacter ℂ r} {b : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive) (hb : b.IsPrimitive) (hr : r ∣ q) (hs : s ∣ q)
    (h : changeLevel hr a = changeLevel hs b) :
    (⟨r, a⟩ : Σ k : ℕ, DirichletCharacter ℂ k) = ⟨s, b⟩ := by
  have he := congrArg DirichletCharacter.conductor h
  rw [conductor_changeLevel, conductor_changeLevel, ha, hb] at he
  subst s
  have hab := changeLevel_injective hr h
  cases hab
  rfl

private theorem partner_bound_of_twists {q d : ℕ} [NeZero q] [NeZero d]
    (hd : d ∣ q) (a : DirichletCharacter ℂ q)
    (F : Finset (Σ k : ℕ, DirichletCharacter ℂ k))
    (hF : ∀ b ∈ F, ∃ hb : b.1 ∣ q, b.2.IsPrimitive ∧
      ∃ c : DirichletCharacter ℂ d, a * changeLevel hb b.2 = changeLevel hd c) :
    F.card ≤ d.totient := by
  classical
  choose lvl prim twist eqn using fun b : F => hF b.1 b.2
  have inj : Function.Injective twist := by
    intro b c h
    apply Subtype.ext
    obtain ⟨⟨r, x⟩, hx⟩ := b
    obtain ⟨⟨s, y⟩, hy⟩ := c
    apply partner_eq_of_common_lift (prim ⟨⟨r,x⟩,hx⟩) (prim ⟨⟨s,y⟩,hy⟩)
      (lvl ⟨⟨r,x⟩,hx⟩) (lvl ⟨⟨s,y⟩,hy⟩)
    apply mul_left_cancel (a := a)
    exact (eqn _).trans ((congrArg (changeLevel hd) h).trans (eqn _).symm)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    (Nat.card_le_card_of_injective twist inj |>.trans_eq
      (DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d))

private theorem partner_bound_of_product_conductor {q d r : ℕ} [NeZero q] [NeZero d]
    (hd : d ∣ q) (hr : r ∣ q) (a : DirichletCharacter ℂ r)
    (F : Finset (Σ k : ℕ, DirichletCharacter ℂ k))
    (hF : ∀ b ∈ F, b.1 ∣ q ∧ b.2.IsPrimitive ∧
      ((changeLevel (Nat.dvd_lcm_left r b.1) a) *
       (changeLevel (Nat.dvd_lcm_right r b.1) b.2)).conductor ∣ d) :
    F.card ≤ d.totient := by
  apply partner_bound_of_twists hd (changeLevel hr a)
  intro b hb
  obtain ⟨hs, hp, hc⟩ := hF b hb
  let A := changeLevel (Nat.dvd_lcm_left r b.1) a
  let B := changeLevel (Nat.dvd_lcm_right r b.1) b.2
  have hl := Nat.lcm_dvd hr hs
  refine ⟨hs, hp, changeLevel hc (A*B).primitiveCharacter, ?_⟩
  calc
    _ = changeLevel hl (A*B) := by simp only [map_mul, A, B, ← changeLevel_trans]
    _ = _ := by
      rw [← changeLevel_trans]
      exact (congrArg (changeLevel hl) (changeLevel_primitiveCharacter (A*B))).symm.trans (by rw [← changeLevel_trans])

private theorem five_partner_choices (a : DirichletCharacter ℂ 5)
    (F : Finset (DirichletCharacter ℂ 5))
    (hf : ∀ b ∈ F, (a = 1 ∧ b = 1) ∨ (a ≠ 1 ∧ b ≠ 1 ∧ a*b ≠ 1)) :
    F.card ≤ 2 := by
  classical
  by_cases ha : a = 1
  · have sub : F ⊆ {1} := by
      intro b hb
      simpa [ha] using hf b hb
    simpa using (Finset.card_le_card sub).trans (show ({1} : Finset (DirichletCharacter ℂ 5)).card ≤ 2 by simp)
  have hu : Fintype.card (DirichletCharacter ℂ 5) = 4 := by
    rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
    decide
  have h1 : 1 ∉ F := by
    intro h
    simpa [ha] using hf 1 h
  have hi : a⁻¹ ∉ F := by
    intro h
    simpa [ha] using hf _ h
  have hi' : a⁻¹ ∉ insert 1 F := by simp [ha, hi]
  have h := Finset.card_le_univ (insert a⁻¹ (insert 1 F))
  rw [Finset.card_insert_of_notMem hi', Finset.card_insert_of_notMem h1, hu] at h
  omega

open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachConductorRatio SquarefreeTwistedGoldbachDensity

private theorem five_choices_of_high (a b : DirichletCharacter ℂ 5) (x : ZMod 5)
    (hx : x ≠ 0)
    (high : ‖J (1 : DirichletCharacter ℂ 5) 1 x‖ < Real.sqrt 2 * ‖J a b x‖) :
    (a = 1 ∧ b = 1) ∨ (a ≠ 1 ∧ b ≠ 1 ∧ a*b ≠ 1) := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  change ‖localSum (1 : DirichletCharacter ℂ 5) 1 x‖ <
    Real.sqrt 2 * ‖localSum a b x‖ at high
  rw [local_norm, local_norm] at high
  by_cases hp : a = 1 ∧ b = 1
  · exact Or.inl hp
  by_cases hbad : a = 1 ∨ b = 1 ∨ a*b = 1
  · simp [hx, hp, hbad] at high
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  · tauto

private theorem high_of_single_factor {u v j k : ℝ}
    (hu : 0 ≤ u) (hh : u < Real.sqrt 2 * v)
    (bound : v * j ≤ u * k) (hjpos : 0 < j) :
    j < Real.sqrt 2 * k := by
  by_contra! h
  have hleft := mul_lt_mul_of_pos_right hh hjpos
  have hright := mul_le_mul_of_nonneg_left bound (Real.sqrt_nonneg 2)
  have hend := mul_le_mul_of_nonneg_left h hu
  linarith only [hleft, hright, hend, show Real.sqrt 2 * (v*j) = (Real.sqrt 2*v)*j by ring,
    show Real.sqrt 2 * (u*k) = u*(Real.sqrt 2*k) by ring]

open TwistedGoldbachConductorValue TwistedGoldbachLocalProduct

private theorem level_dvd_target_mul {m L c : ℕ} (h : L / m.gcd L ∣ c) :
    L ∣ c*m := by
  conv_lhs => rw [← Nat.div_mul_cancel (Nat.gcd_dvd_right m L)]
  exact Nat.mul_dvd_mul h (Nat.gcd_dvd_left m L)

private theorem high_partner_support {r s : ℕ} [NeZero r] [NeZero s]
    {a : DirichletCharacter ℂ r} {b : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive) (hb : b.IsPrimitive) (m : ℕ) (hm : 0 < m) (he : Even m)
    (hh : ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ <
      Real.sqrt 2 * ‖series a b m‖) :
    r.lcm s ∣ 180*m ∧ (inversePair a b).conductor ∣ 180 ∧
      (5 ∣ m → (inversePair a b).conductor ∣ 36) := by
  classical
  let L := r.lcm s
  let d := (inversePair a b).conductor
  have hd36 : 36 ∣ 180 := by decide
  by_cases good : r/(m.gcd r) ∣ 36 ∧ s/(m.gcd s) ∣ 36 ∧ r/(r.gcd s) ∣ 3 ∧
      s/(r.gcd s) ∣ 3 ∧ d ∣ 36
  · obtain ⟨hr, hs, _, _, hd⟩ := good
    exact ⟨Nat.lcm_dvd (level_dvd_target_mul (hr.trans hd36))
      (level_dvd_target_mul (hs.trans hd36)), hd.trans hd36, fun _ => hd⟩
  have high' := Conjectures.Goldbach.NearExtremalReducedConductor r s a b ha hb m hm he
  have out : ¬(r/(m.gcd r) ∣ 36 ∧ s/(m.gcd s) ∣ 36 ∧ r/(r.gcd s) ∣ 3 ∧
      s/(r.gcd s) ∣ 3 ∧ ((changeLevel (Nat.dvd_lcm_left r s) a) *
        (changeLevel (Nat.dvd_lcm_right r s) b)).conductor ∣ 36) := by
    simpa only [d, inversePair, conductor_inv] using good
  obtain ⟨_, hj, hn⟩ := high' out hh
  have hnz : series a b m ≠ 0 := by
    intro hz
    rw [hz, norm_zero, mul_zero] at hh
    exact (not_lt_of_ge (norm_nonneg _)) hh
  have support := (full_support ha hb m hm he).mp hnz
  exact ⟨level_dvd_target_mul hj, support.2.2.1.trans hj, fun h => (hn h).elim⟩

open TwistedGoldbachConductorComponents Finset

private theorem partner_two_coordinates {t : ℕ} [NeZero t] (ht : Nat.Coprime 5 t)
    (ht36 : 36 ∣ t) {r : ℕ} [NeZero r] (a : DirichletCharacter ℂ r)
    (ha : a.IsPrimitive) (hr : r ∣ 5*t) (m : ℕ) (hm : 0 < m) (he : Even m)
    (hm5 : ¬ 5 ∣ m) (F : Finset (Σ k : ℕ, DirichletCharacter ℂ k))
    (hf : ∀ b ∈ F, ∃ hs : b.1 ∣ 5*t, b.1 ≠ 0 ∧ b.2.IsPrimitive ∧
      (inversePair a b.2).conductor ∣ 180 ∧
      ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ <
        Real.sqrt 2 * ‖series a b.2 m‖) : F.card ≤ 24 := by
  classical
  let q : Fin 2 → ℕ := ![5,t]
  letI nz (i : Fin 2) : NeZero (q i) := by fin_cases i <;> dsimp [q] <;> infer_instance
  let e : ZMod (5*t) ≃+* ∀ i, ZMod (q i) :=
    (ZMod.chineseRemainder ht).trans (RingEquiv.piFinTwo (fun i => ZMod (q i))).symm
  have hd (i) : q i ∣ 5*t := by
    fin_cases i
    · exact dvd_mul_right 5 t
    · exact dvd_mul_left t 5
  have cop : Pairwise (fun i j => (q i).Coprime (q j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | exact ht | exact ht.symm
  let A := changeLevel hr a
  choose lvl hne prim cond high using fun b : F => hf b.1 b.2
  let B (b : F) := changeLevel (lvl b) b.1.2
  let loc (b : F) : DirichletCharacter ℂ 5 := component e (B b) 0
  let W (b : F) : DirichletCharacter ℂ t := component e (A * B b) 1
  have wd (b : F) : (W b).conductor ∣ 36 := by
    have hb := lvl b
    have hl := Nat.lcm_dvd hr hb
    have hp : A * B b = changeLevel hl ((inversePair a b.1.2)⁻¹) := by
      simp only [A, B, inversePair, inv_inv, map_mul, ← changeLevel_trans]
    have all : (A * B b).conductor ∣ 180 := by
      rw [hp, conductor_changeLevel, conductor_inv]
      exact cond b
    have part : (W b).conductor ∣ (A * B b).conductor := by
      rw [global_conductor e hd cop, Fin.prod_univ_two]
      exact dvd_mul_left _ _
    have hcop : (W b).conductor.Coprime 5 := ht.symm.of_dvd_left (W b).conductor_dvd_level
    exact hcop.dvd_of_dvd_mul_left (show (W b).conductor ∣ 5*36 from part.trans all)
  let code (b : F) : DirichletCharacter ℂ 36 :=
    changeLevel (wd b) (W b).primitiveCharacter
  have lift (b : F) : changeLevel ht36 (code b) = W b := by
    simpa only [code, ← changeLevel_trans] using (W b).changeLevel_primitiveCharacter
  have limits : (F.attach.image loc).card ≤ 2 := by
    apply five_partner_choices (component e A 0)
    intro v hv
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hv
    letI : NeZero b.1.1 := ⟨hne b⟩
    have sx := single_factor e ha (prim b) hr (lvl b) m hm he (0 : Fin 2)
    have hn : (m : ZMod 5) ≠ 0 := mt (ZMod.natCast_eq_zero_iff m 5).mp hm5
    apply five_choices_of_high _ _ _ hn
    exact high_of_single_factor (norm_nonneg _) (high b) sx
      (norm_pos_iff.mpr (principal_ne_zero 5 m he))
  let f (b : F) : (F.attach.image loc) × (DirichletCharacter ℂ 36) :=
    (⟨loc b, Finset.mem_image.mpr ⟨b, F.mem_attach b, rfl⟩⟩, code b)
  have inj : Function.Injective f := by
    intro b c h
    have h0 := congrArg (fun z : (F.attach.image loc) × (DirichletCharacter ℂ 36) => z.1.val) h
    have h1 := congrArg (fun z : (F.attach.image loc) × (DirichletCharacter ℂ 36) => changeLevel ht36 z.2) h
    change changeLevel ht36 (code b) = changeLevel ht36 (code c) at h1
    rw [lift, lift] at h1
    change component e (A*B b) 1 = component e (A*B c) 1 at h1
    rw [component_mul, component_mul] at h1
    have same : B b = B c := by
      calc
        _ = _ := recovered e hd (B b)
        _ = _ := Finset.prod_congr rfl fun i _ => by
          apply congrArg (changeLevel (hd i))
          fin_cases i
          · exact h0
          · exact mul_left_cancel h1
        _ = _ := (recovered e hd (B c)).symm
    exact Subtype.ext (partner_eq_of_common_lift (prim b) (prim c) (lvl b) (lvl c) same)
  have count := Fintype.card_le_of_injective f inj
  have count36 : Fintype.card (DirichletCharacter ℂ 36) = 12 := by
    rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
    decide
  simp only [Fintype.card_coe, Fintype.card_prod, count36] at count
  omega

theorem Conjectures.Goldbach.NearExtremalPartnerCount :
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
  exact ∀ (r : ℕ) [NeZero r] (α : DirichletCharacter ℂ r), α.IsPrimitive →
    ∀ m : ℕ, 0 < m → Even m →
    ∀ F : Finset (Σ s : ℕ, DirichletCharacter ℂ s),
    (∀ b ∈ F, b.1 ≠ 0 ∧ b.2.IsPrimitive ∧ ‖O m‖ < Real.sqrt 2 * ‖S α b.2 m‖) →
    F.card ≤ 24 := by
  classical
  intro S O r _ a ha m hm he F good
  by_cases empty : F = ∅
  · simp [empty]
  have nonempty := Finset.nonempty_iff_ne_empty.mpr empty
  let Q := 180*m
  letI : NeZero Q := ⟨by dsimp [Q]; positivity⟩
  have facts (b) (hb : b ∈ F) :
      r.lcm b.1 ∣ Q ∧ (inversePair a b.2).conductor ∣ 180 ∧
        (5 ∣ m → (inversePair a b.2).conductor ∣ 36) := by
    obtain ⟨hn, hp, high⟩ := good b hb
    letI : NeZero b.1 := ⟨hn⟩
    exact high_partner_support ha hp m hm he high
  obtain ⟨b₀, hb₀⟩ := nonempty
  have hr := (Nat.dvd_lcm_left r b₀.1).trans (facts b₀ hb₀).1
  by_cases hm5 : 5 ∣ m
  · have hd : 36 ∣ Q := dvd_trans (by decide : 36 ∣ 180) (dvd_mul_right 180 m)
    apply le_trans (partner_bound_of_product_conductor hd hr a F ?_) (by decide)
    intro b hb
    exact ⟨(Nat.dvd_lcm_right r b.1).trans (facts b hb).1, (good b hb).2.1,
      by simpa only [inversePair, conductor_inv] using (facts b hb).2.2 hm5⟩
  · let t := 36*m
    letI : NeZero t := ⟨by dsimp [t]; positivity⟩
    have hQ : 5*t = Q := by dsimp [t,Q]; ring
    have cop : Nat.Coprime 5 t := Nat.Coprime.mul_right (by decide : Nat.Coprime 5 36)
      ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 5)).mpr hm5)
    apply partner_two_coordinates cop (dvd_mul_right 36 m) a ha (hQ.symm ▸ hr) m hm he hm5 F
    intro b hb
    obtain ⟨hn, hp, high⟩ := good b hb
    exact ⟨hQ.symm ▸ (Nat.dvd_lcm_right r b.1).trans (facts b hb).1, hn, hp,
      (facts b hb).2.1, high⟩
