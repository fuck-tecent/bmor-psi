import Mathlib

private lemma hjsw_combi (lv : Fin 2 × Fin 2 → ℕ) (m : ℤ)
    (hlv : lv = (fun ij => ij.1.val + ij.2.val) ∨ lv = (fun ij => ij.1.val + (1 - ij.2.val)))
    (hm : m = -1 ∨ m = 0 ∨ m = 1) (M N : Finset (Fin 2 × Fin 2))
    (h : ∀ k : ℕ, k < 3 → ∀ k' : ℕ, k' < 3 → (k : ℤ) = k' + m →
      (M.filter (fun ij => lv ij = k)).card + (N.filter (fun ij => lv ij = k')).card ≤ 2) :
    M.card + N.card ≤ 6 := by
  revert h M N
  rcases hlv with rfl | rfl <;> rcases hm with rfl | rfl | rfl <;> decide +kernel

private lemma hjsw_inj (p : ℕ) [NeZero p] (t : ZMod p)
    (Φ : ZMod p → Fin 2 → Fin 2 → ℤ × ℤ)
    (hΦ : ∀ x i j, Φ x i j = (((x + t).val : ℤ) + (i.val : ℤ) * p,
      ((x⁻¹).val : ℤ) + (j.val : ℤ) * p))
    (x y : ZMod p) (i j i' j' : Fin 2) (h : Φ x i j = Φ y i' j') :
    x = y ∧ i = i' ∧ j = j' := by
  rw [hΦ, hΦ, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hx := ZMod.val_lt (x + t)
  have hy := ZMod.val_lt (y + t)
  have hx' := ZMod.val_lt (x⁻¹)
  have hy' := ZMod.val_lt (y⁻¹)
  have key : ∀ (a a' : ℕ) (i i' : Fin 2), a < p → a' < p →
      (a : ℤ) + (i.val : ℤ) * p = a' + (i'.val : ℤ) * p → a = a' ∧ i = i' := by
    intro a a' i i' ha ha' h
    fin_cases i <;> fin_cases i' <;> simp at h ⊢ <;> omega
  obtain ⟨e1, e2⟩ := key _ _ _ _ hx hy h1
  obtain ⟨e3, e4⟩ := key _ _ _ _ hx' hy' h2
  refine ⟨?_, e2, e4⟩
  have := ZMod.val_injective p e1
  simpa using this

private lemma hjsw_line (p : ℕ) [NeZero p] (t : ZMod p)
    (Φ : ZMod p → Fin 2 → Fin 2 → ℤ × ℤ)
    (hΦ : ∀ x i j, Φ x i j = (((x + t).val : ℤ) + (i.val : ℤ) * p,
      ((x⁻¹).val : ℤ) + (j.val : ℤ) * p))
    (R : ZMod p → Finset (Fin 2 × Fin 2))
    (hNT : ∀ a ∈ (Finset.univ.filter (fun x : ZMod p => x ≠ 0)).biUnion
        (fun x => (R x).image (fun ij => Φ x ij.1 ij.2)),
      ∀ b ∈ (Finset.univ.filter (fun x : ZMod p => x ≠ 0)).biUnion
        (fun x => (R x).image (fun ij => Φ x ij.1 ij.2)),
      ∀ c ∈ (Finset.univ.filter (fun x : ZMod p => x ≠ 0)).biUnion
        (fun x => (R x).image (fun ij => Φ x ij.1 ij.2)),
      a ≠ b → a ≠ c → b ≠ c →
        (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) ≠ 0)
    (ε c : ℤ) (B : Finset (ZMod p × (Fin 2 × Fin 2)))
    (hB : ∀ z ∈ B, z.1 ≠ 0 ∧ z.2 ∈ R z.1 ∧
      (Φ z.1 z.2.1 z.2.2).1 + ε * (Φ z.1 z.2.1 z.2.2).2 = c) :
    B.card ≤ 2 := by
  by_contra hcon
  have h3 : 2 < B.card := by omega
  obtain ⟨a, b, d, ha, hb, hd, hab, had, hbd⟩ := Finset.two_lt_card_iff.1 h3
  have mem : ∀ z ∈ B, Φ z.1 z.2.1 z.2.2 ∈ (Finset.univ.filter (fun x : ZMod p => x ≠ 0)).biUnion
        (fun x => (R x).image (fun ij => Φ x ij.1 ij.2)) := by
    intro z hz
    obtain ⟨h1, h2, _⟩ := hB z hz
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    exact ⟨z.1, h1, z.2, h2, rfl⟩
  have ne : ∀ z ∈ B, ∀ w ∈ B, z ≠ w → Φ z.1 z.2.1 z.2.2 ≠ Φ w.1 w.2.1 w.2.2 := by
    intro z _ w _ hzw heq
    obtain ⟨e1, e2, e3⟩ := hjsw_inj p t Φ hΦ _ _ _ _ _ _ heq
    apply hzw
    obtain ⟨z1, z2, z3⟩ := z
    obtain ⟨w1, w2, w3⟩ := w
    simp only at e1 e2 e3
    subst e1 e2 e3
    rfl
  apply hNT _ (mem a ha) _ (mem b hb) _ (mem d hd) (ne a ha b hb hab) (ne a ha d hd had)
    (ne b hb d hd hbd)
  have ea := (hB a ha).2.2
  have eb := (hB b hb).2.2
  have ed := (hB d hd).2.2
  generalize Φ a.1 a.2.1 a.2.2 = P at *
  generalize Φ b.1 b.2.1 b.2.2 = Q at *
  generalize Φ d.1 d.2.1 d.2.2 = S at *
  linear_combination (S.2 - P.2) * (eb.trans ea.symm) - (Q.2 - P.2) * (ed.trans ea.symm)

private lemma hjsw_pair (p : ℕ) [NeZero p] (t : ZMod p)
    (Φ : ZMod p → Fin 2 → Fin 2 → ℤ × ℤ)
    (hΦ : ∀ x i j, Φ x i j = (((x + t).val : ℤ) + (i.val : ℤ) * p,
      ((x⁻¹).val : ℤ) + (j.val : ℤ) * p))
    (R : ZMod p → Finset (Fin 2 × Fin 2))
    (hNT : ∀ a ∈ (Finset.univ.filter (fun x : ZMod p => x ≠ 0)).biUnion
        (fun x => (R x).image (fun ij => Φ x ij.1 ij.2)),
      ∀ b ∈ (Finset.univ.filter (fun x : ZMod p => x ≠ 0)).biUnion
        (fun x => (R x).image (fun ij => Φ x ij.1 ij.2)),
      ∀ c ∈ (Finset.univ.filter (fun x : ZMod p => x ≠ 0)).biUnion
        (fun x => (R x).image (fun ij => Φ x ij.1 ij.2)),
      a ≠ b → a ≠ c → b ≠ c →
        (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) ≠ 0)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (x y : ZMod p) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) (m : ℤ)
    (hm : m = -1 ∨ m = 0 ∨ m = 1)
    (hσ : ((y + t).val : ℤ) + ε * ((y⁻¹).val : ℤ)
      = ((x + t).val : ℤ) + ε * ((x⁻¹).val : ℤ) + p * m) :
    (R x).card + (R y).card ≤ 6 := by
  have main : ∀ (lv : Fin 2 × Fin 2 → ℕ) (off : ℤ),
      (∀ ij : Fin 2 × Fin 2, (ij.1.val : ℤ) + ε * ij.2.val = (lv ij : ℤ) - off) →
      ∀ k k' : ℕ, (k : ℤ) = k' + m →
      ((R x).filter (fun ij => lv ij = k)).card
        + ((R y).filter (fun ij => lv ij = k')).card ≤ 2 := by
    intro lv off hlv k k' hk
    have hc := hjsw_line p t Φ hΦ R hNT ε
      (((x + t).val : ℤ) + ε * ((x⁻¹).val : ℤ) + p * ((k : ℤ) - off))
      (((R x).filter (fun ij => lv ij = k)).image (fun ij => (x, ij)) ∪
        ((R y).filter (fun ij => lv ij = k')).image (fun ij => (y, ij))) ?_
    · rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (Prod.mk_right_injective x),
        Finset.card_image_of_injective _ (Prod.mk_right_injective y)] at hc
      · exact hc
      · refine Finset.disjoint_left.2 ?_
        intro z hz1 hz2
        simp only [Finset.mem_image] at hz1 hz2
        obtain ⟨ij, _, rfl⟩ := hz1
        obtain ⟨ij', _, h⟩ := hz2
        exact hxy (congrArg Prod.fst h).symm
    · intro z hz
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hz
      rcases hz with ⟨ij, ⟨h1, h2⟩, rfl⟩ | ⟨ij, ⟨h1, h2⟩, rfl⟩
      · refine ⟨hx, h1, ?_⟩
        rw [hΦ]
        dsimp only
        have := hlv ij
        rw [h2] at this
        linear_combination (p : ℤ) * this
      · refine ⟨hy, h1, ?_⟩
        rw [hΦ]
        dsimp only
        have := hlv ij
        rw [h2] at this
        linear_combination hσ + (p : ℤ) * this - (p : ℤ) * hk
  rcases hε with rfl | rfl
  · apply hjsw_combi (fun ij => ij.1.val + ij.2.val) m (Or.inl rfl) hm
    intro k _ k' _ hkk
    exact main _ 0 (by intro ij; simp) k k' hkk
  · apply hjsw_combi (fun ij => ij.1.val + (1 - ij.2.val)) m (Or.inr rfl) hm
    intro k _ k' _ hkk
    refine main _ 1 ?_ k k' hkk
    intro ij
    have := ij.2.isLt
    omega

private lemma hjsw_exists_m (p : ℕ) [Fact p.Prime] (t : ZMod p) (ε : ℤ) (x y : ZMod p)
    (hcong : (x + t) + (ε : ZMod p) * x⁻¹ = (y + t) + (ε : ZMod p) * y⁻¹)
    (hε : ε = 1 ∨ ε = -1) :
    ∃ m : ℤ, (m = -1 ∨ m = 0 ∨ m = 1) ∧
      ((y + t).val : ℤ) + ε * ((y⁻¹).val : ℤ)
        = ((x + t).val : ℤ) + ε * ((x⁻¹).val : ℤ) + p * m := by
  have hd : ((((y + t).val : ℤ) + ε * ((y⁻¹).val : ℤ)
      - (((x + t).val : ℤ) + ε * ((x⁻¹).val : ℤ)) : ℤ) : ZMod p) = 0 := by
    push_cast
    simp only [ZMod.natCast_zmod_val]
    linear_combination (-1 : ZMod p) * hcong
  obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 hd
  have h1 := ZMod.val_lt (x + t)
  have h2 := ZMod.val_lt (y + t)
  have h3 := ZMod.val_lt (x⁻¹)
  have h4 := ZMod.val_lt (y⁻¹)
  have hp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hb : -(2 * (p : ℤ)) < (p : ℤ) * m ∧ (p : ℤ) * m < 2 * p := by
    rcases hε with rfl | rfl <;> push_cast at hm <;> constructor <;>
      [skip; skip; skip; skip] <;> omega
  have hm1 : m < 2 := by
    by_contra h
    push_neg at h
    nlinarith [hb.2]
  have hm2 : -2 < m := by
    by_contra h
    push_neg at h
    nlinarith [hb.1]
  refine ⟨m, by omega, ?_⟩
  linarith

private lemma hjsw_total (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) (t : ZMod p)
    (Φ : ZMod p → Fin 2 → Fin 2 → ℤ × ℤ)
    (hΦ : ∀ x i j, Φ x i j = (((x + t).val : ℤ) + (i.val : ℤ) * p,
      ((x⁻¹).val : ℤ) + (j.val : ℤ) * p))
    (R : ZMod p → Finset (Fin 2 × Fin 2))
    (hNT : ∀ a ∈ (Finset.univ.filter (fun x : ZMod p => x ≠ 0)).biUnion
        (fun x => (R x).image (fun ij => Φ x ij.1 ij.2)),
      ∀ b ∈ (Finset.univ.filter (fun x : ZMod p => x ≠ 0)).biUnion
        (fun x => (R x).image (fun ij => Φ x ij.1 ij.2)),
      ∀ c ∈ (Finset.univ.filter (fun x : ZMod p => x ≠ 0)).biUnion
        (fun x => (R x).image (fun ij => Φ x ij.1 ij.2)),
      a ≠ b → a ≠ c → b ≠ c →
        (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) ≠ 0) :
    ∑ x ∈ Finset.univ.filter (fun x : ZMod p => x ≠ 0), (R x).card ≤ 3 * (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  haveI : Fact (2 < p) := ⟨by omega⟩
  have hne : (1 : ZMod p) ≠ -1 := (ZMod.neg_one_ne_one).symm
  rw [Finset.filter_ne']
  set F := Finset.univ.erase (0 : ZMod p) with hF
  have h1F : (1 : ZMod p) ∈ F := by simp [hF]
  have hm1F : (-1 : ZMod p) ∈ F.erase 1 := by
    simp [hF, hne.symm]
  have hcardF : F.card = p - 1 := by simp [hF, ZMod.card]
  have hsym : ∑ x ∈ F, (R x⁻¹).card = ∑ x ∈ F, (R x).card := by
    apply Finset.sum_nbij' (fun x => x⁻¹) (fun x => x⁻¹) <;> simp [hF, inv_inv]
  have hpair1 : (R 1).card + (R (-1)).card ≤ 6 := by
    obtain ⟨m, hm, hσ⟩ := hjsw_exists_m p t (-1) 1 (-1) (by simp) (Or.inr rfl)
    exact hjsw_pair p t Φ hΦ R hNT (-1) (Or.inr rfl) 1 (-1) one_ne_zero
      (neg_ne_zero.2 one_ne_zero) hne m hm hσ
  have hgen : ∀ x ∈ (F.erase 1).erase (-1), (R x).card + (R x⁻¹).card ≤ 6 := by
    intro x hx
    simp only [hF, Finset.mem_erase, Finset.mem_univ, and_true] at hx
    obtain ⟨hxm, hx1, hx0⟩ := hx
    have hxx : x ≠ x⁻¹ := by
      intro h
      have h' := mul_inv_cancel₀ hx0
      rw [← h] at h'
      rcases mul_self_eq_one_iff.1 h' with h'' | h''
      · exact hx1 h''
      · exact hxm h''
    obtain ⟨m, hm, hσ⟩ := hjsw_exists_m p t 1 x x⁻¹ (by simp [inv_inv]; ring) (Or.inl rfl)
    exact hjsw_pair p t Φ hΦ R hNT 1 (Or.inl rfl) x x⁻¹ hx0 (inv_ne_zero hx0) hxx m hm hσ
  have e1 := Finset.add_sum_erase F (fun x => (R x).card + (R x⁻¹).card) h1F
  have e2 := Finset.add_sum_erase (F.erase 1) (fun x => (R x).card + (R x⁻¹).card) hm1F
  have e3 := Finset.sum_le_card_nsmul ((F.erase 1).erase (-1))
    (fun x => (R x).card + (R x⁻¹).card) 6 hgen
  have hc : ((F.erase 1).erase (-1)).card = p - 1 - 1 - 1 := by
    rw [Finset.card_erase_of_mem hm1F, Finset.card_erase_of_mem h1F, hcardF]
  have e4 := Finset.sum_add_distrib (s := F) (f := fun x => (R x).card)
    (g := fun x => (R x⁻¹).card)
  rw [hsym] at e4
  simp only [inv_one, inv_neg, smul_eq_mul] at e1 e2 e3
  rw [hc] at e3
  omega

theorem Conjectures.NoThreeInLine.HjswFoldUpperBound :
    ∀ (p : ℕ) [NeZero p] (hp : Nat.Prime p), p ≠ 2 →
  (let det3 : ℤ × ℤ → ℤ × ℤ → ℤ × ℤ → ℤ :=
     fun P Q R => (Q.1 - P.1) * (R.2 - P.2) - (Q.2 - P.2) * (R.1 - P.1)
   let cap : ZMod p → ZMod p → ZMod p × ZMod p := fun t x => (x + t, x⁻¹)
   let lift : ZMod p → ZMod p → Fin 2 → Fin 2 → ℤ × ℤ :=
     fun t x i j =>
       (((cap t x).1.val : ℤ) + (i.val : ℤ) * (p : ℤ),
        ((cap t x).2.val : ℤ) + (j.val : ℤ) * (p : ℤ))
   let Mask : Type := ZMod p → Finset (Fin 2 × Fin 2)
   let points : ZMod p → Mask → Finset (ℤ × ℤ) :=
     fun t R =>
       (Finset.univ.filter (fun x : ZMod p => x ≠ 0)).biUnion
         (fun x => (R x).image (fun ij => lift t x ij.1 ij.2))
   let NoThreeCollinear : Finset (ℤ × ℤ) → Prop :=
     fun S => ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c → det3 a b c ≠ 0
   ∀ (t : ZMod p) (R : Mask), NoThreeCollinear (points t R) →
     (∑ x ∈ Finset.univ.filter (fun x : ZMod p => x ≠ 0), (R x).card) ≤ 3 * (p - 1)) := by
  intro p _ hp hp2
  intro det3 cap lift Mask points NoThreeCollinear t R h
  exact hjsw_total p hp hp2 t (fun x i j => lift t x i j) (fun x i j => rfl) R h
