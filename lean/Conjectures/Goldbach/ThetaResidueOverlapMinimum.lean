import Mathlib

namespace Conjectures.Goldbach.ThetaResidueOverlapMinimum_aux

lemma nat_le_of_mul {m n b k : ℕ} (hn : 0 < n) (h : (k + 1) * n ≤ 2 * m + n - b) :
    b + k * n ≤ 2 * m := by
  have h1 : k * n + n ≤ 2 * m + n - b := by
    calc k * n + n = (k + 1) * n := by ring
      _ ≤ 2 * m + n - b := h
  have h2 : k * n + n + b ≤ (2 * m + n - b) + b := Nat.add_le_add_right h1 b
  have h3 : (2 * m + n - b) + b = 2 * m + n := Nat.sub_add_cancel (by omega)
  have h4 : b + k * n + n ≤ 2 * m + n := by
    calc b + k * n + n = k * n + n + b := by ring
      _ ≤ (2 * m + n - b) + b := h2
      _ = 2 * m + n := h3
  exact Nat.le_of_add_le_add_right h4

lemma nat_sub_le {q k a : ℕ} (hk : k < q) (h : q - 1 - k < a) : q - a ≤ k := by omega

lemma nat_sub_lt {q k a : ℕ} (hk : k < q) (h : q - a ≤ k) : q - 1 - k < a := by omega

lemma nat_sub_sub {x y q : ℕ} (h : y ≤ q) : x - (q - y) = x + y - q := by omega

lemma nat_q_split {q k : ℕ} (h : k < q) : (q - 1 - k) + 1 + k = q := by omega

lemma nat_lt_of_succ_le {a b : ℕ} (h : a + 1 ≤ b) : a < b := by omega

def cn (H L : ℕ) (U : Finset (Fin (2 * H + 1))) (b : ℕ) : ℕ :=
  (U.filter (fun i => i.val % L = b)).card

def cls (H L : ℕ) (b : ℕ) : Finset (Fin (2 * H + 1)) :=
  Finset.univ.filter (fun i => i.val % L = b)

def sres (H L : ℕ) (b : ℕ) : ℕ := (2 * H + L - b) % L

def hitt (H L : ℕ) (U : Finset (Fin (2 * H + 1))) : ℕ :=
  (U.filter (fun i => i.rev ∈ U)).card

def wit (H L : ℕ) (A : Finset (Fin (2 * H + 1))) : Finset (Fin (2 * H + 1)) :=
  Finset.univ.filter (fun i => i.val / L < cn H L A (i.val % L))

variable (H L : ℕ)

lemma mem_cls (b : ℕ) (i : Fin (2 * H + 1)) : i ∈ cls H L b ↔ i.val % L = b := by
  simp [cls]

lemma mem_wit (A : Finset (Fin (2 * H + 1))) (i : Fin (2 * H + 1)) :
    i ∈ wit H L A ↔ i.val / L < cn H L A (i.val % L) := by
  simp [wit]

lemma rev_val (i : Fin (2 * H + 1)) : i.rev.val = 2 * H - i.val := by
  have h := i.isLt
  rw [Fin.val_rev]
  omega

lemma sres_lt (hL : 0 < L) (b : ℕ) : sres H L b < L := Nat.mod_lt _ hL

lemma sres_invol (hL : 0 < L) (b : ℕ) (hb : b < L) : sres H L (sres H L b) = b := by
  have hbA : b ≤ 2 * H + L := by omega
  show (2 * H + L - (2 * H + L - b) % L) % L = b
  set u := 2 * H + L - b with hu
  set c := u % L with hc
  set P := L * (u / L) with hP
  have hmod : c + P = u := by rw [hc, hP]; exact Nat.mod_add_div _ _
  have huA : u + b = 2 * H + L := by rw [hu]; omega
  have h2 : 2 * H + L - c = b + P := by omega
  rw [h2, hP, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]

lemma res_rev (hL : 0 < L) (i : Fin (2 * H + 1)) : i.rev.val % L = sres H L (i.val % L) := by
  have hlt := i.isLt
  set m := i.val % L with hm
  set p := L * (i.val / L) with hp
  have h1 : m + p = i.val := by rw [hm, hp]; exact Nat.mod_add_div _ _
  have hmi : m ≤ i.val := by rw [hm]; exact Nat.mod_le _ _
  have hml : m ≤ 2 * H := le_trans hmi (by omega)
  have h2 : 2 * H - m = (2 * H - i.val) + p := by omega
  have h3 : 2 * H + L - m = (2 * H - m) + L := by omega
  have hLHS : (2 * H - i.val) % L = (2 * H - m) % L := by
    rw [h2, hp, Nat.add_mul_mod_self_left]
  show i.rev.val % L = (2 * H + L - m) % L
  rw [rev_val, hLHS, h3, Nat.add_mod_right]

lemma cls_val (b : ℕ) (i : Fin (2 * H + 1)) (hi : i ∈ cls H L b) :
    i.val = b + L * (i.val / L) := by
  have h := Nat.mod_add_div i.val L
  rw [(mem_cls H L b i).mp hi] at h
  exact h.symm

lemma le_of_mem_cls (b : ℕ) (i : Fin (2 * H + 1)) (hi : i ∈ cls H L b) : b ≤ 2 * H := by
  have h := (mem_cls H L b i).mp hi
  have h2 := Nat.mod_le i.val L
  have h3 := i.isLt
  omega

lemma cls_div_lt (hL : 0 < L) (b : ℕ) (hb : b < L) (i : Fin (2 * H + 1)) (hi : i ∈ cls H L b) :
    i.val / L < (2 * H + L - b) / L := by
  have hval := cls_val H L b i hi
  have hlt := i.isLt
  have h1 : (i.val / L + 1) * L = L * (i.val / L) + L := by ring
  have h2 : L * (i.val / L) = i.val - b := by
    conv_rhs => rw [hval]
    exact (Nat.add_sub_cancel_left _ _).symm
  have h3 : i.val - b ≤ 2 * H - b := Nat.sub_le_sub_right (by omega) b
  have h5 : (2 * H - b) + L = 2 * H + L - b := by
    have := le_of_mem_cls H L b i hi
    omega
  have h4 : (i.val / L + 1) * L ≤ 2 * H + L - b := by
    rw [h1, h2]
    calc i.val - b + L ≤ (2 * H - b) + L := Nat.add_le_add_right h3 L
      _ = 2 * H + L - b := h5
  exact nat_lt_of_succ_le ((Nat.le_div_iff_mul_le hL).mpr h4)

lemma exists_cls (hL : 0 < L) (b : ℕ) (hb : b < L) (k : ℕ) (hk : k < (2 * H + L - b) / L) :
    ∃ i : Fin (2 * H + 1), i ∈ cls H L b ∧ i.val / L = k := by
  have h1 : (k + 1) * L ≤ (2 * H + L - b) / L * L :=
    Nat.mul_le_mul_right L (Nat.succ_le_iff.mpr hk)
  have h2 : (2 * H + L - b) / L * L ≤ 2 * H + L - b := Nat.div_mul_le_self _ _
  have h3 : (k + 1) * L ≤ 2 * H + L - b := le_trans h1 h2
  have h4 : b + k * L ≤ 2 * H := nat_le_of_mul hL h3
  refine ⟨⟨b + k * L, Nat.lt_succ_of_le h4⟩, ?_, ?_⟩
  · rw [mem_cls]
    show (b + k * L) % L = b
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  · show (b + k * L) / L = k
    rw [Nat.mul_comm k L, Nat.add_mul_div_left _ _ hL, Nat.div_eq_of_lt hb, Nat.zero_add]

lemma cls_inj {b : ℕ} {i j : Fin (2 * H + 1)} (hi : i ∈ cls H L b) (hj : j ∈ cls H L b)
    (h : i.val / L = j.val / L) : i = j := by
  have hi' := cls_val H L b i hi
  have hj' := cls_val H L b j hj
  apply Fin.ext
  rw [hi', hj', h]

lemma cls_card (hL : 0 < L) (b : ℕ) (hb : b < L) :
    (cls H L b).card = (2 * H + L - b) / L := by
  have key := Finset.card_bij (s := cls H L b) (t := Finset.range ((2 * H + L - b) / L))
    (fun i _ => i.val / L)
    (fun i hi => Finset.mem_range.mpr (cls_div_lt H L hL b hb i hi))
    (fun i hi j hj h => cls_inj H L hi hj h)
    (fun k hk => by
      obtain ⟨i, hi, hic⟩ := exists_cls H L hL b hb k (Finset.mem_range.mp hk)
      exact ⟨i, hi, hic⟩)
  rw [key, Finset.card_range]

lemma cls_rev_card (hL : 0 < L) (b : ℕ) (hb : b < L) :
    (cls H L (sres H L b)).card = (cls H L b).card := by
  have himg : (cls H L b).image Fin.rev = cls H L (sres H L b) := by
    ext i
    constructor
    · intro hi
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
      rw [mem_cls, ← hji, res_rev H L hL j, (mem_cls H L b j).mp hj]
    · intro hi
      have h1 : i.val % L = sres H L b := (mem_cls H L (sres H L b) i).mp hi
      refine Finset.mem_image.mpr ⟨i.rev, ?_, Fin.rev_rev i⟩
      rw [mem_cls, res_rev H L hL i, h1, sres_invol H L hL b hb]
  rw [← himg, Finset.card_image_of_injective _ Fin.rev_injective]

lemma cls_rev_div (hL : 0 < L) (b : ℕ) (hb : b < L) (i : Fin (2 * H + 1)) (hi : i ∈ cls H L b) :
    i.rev.val / L = (2 * H + L - b) / L - 1 - i.val / L := by
  have hval := cls_val H L b i hi
  have hq := cls_div_lt H L hL b hb i hi
  have hb2 := le_of_mem_cls H L b i hi
  have hlt := i.isLt
  set q := i.val / L with hqdef
  set Q := (2 * H + L - b) / L with hQdef
  set c := (2 * H + L - b) % L with hcdef
  set p := L * q with hpdef
  set P := L * Q with hPdef
  set s := L * (Q - 1 - q) with hsdef
  have hcL : c < L := by rw [hcdef]; exact Nat.mod_lt _ hL
  have hQP : Q = (Q - 1 - q) + 1 + q := (nat_q_split hq).symm
  have hPs : P = s + L + p := by rw [hPdef, hQP, hsdef, hpdef]; ring
  have hcp : c + P = 2 * H + L - b := by rw [hcdef, hPdef, hQdef]; exact Nat.mod_add_div _ _
  have hival : i.val = b + p := by rw [hpdef, hqdef]; exact hval
  have hkey : c + s + p + b = 2 * H := by omega
  have hrep : 2 * H - i.val = c + s := by omega
  have hdiv : (c + s) / L = c / L + (Q - 1 - q) := by
    rw [hsdef]; exact Nat.add_mul_div_left _ _ hL
  have hfin : i.rev.val / L = Q - 1 - q := by
    rw [rev_val, hrep, hdiv, Nat.div_eq_of_lt hcL, Nat.zero_add]
  rw [hQdef, hqdef] at hfin
  exact hfin

lemma cn_le (A : Finset (Fin (2 * H + 1))) (b : ℕ) : cn H L A b ≤ (cls H L b).card :=
  Finset.card_le_card (fun i hi => (mem_cls H L b i).mpr (Finset.mem_filter.mp hi).2)

lemma filter_swap (U : Finset (Fin (2 * H + 1))) (P Q : Fin (2 * H + 1) → Prop)
    [DecidablePred P] [DecidablePred Q] :
    (U.filter P).filter Q = (U.filter Q).filter P := by
  ext i
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h3⟩, h2⟩
  · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨⟨h1, h2⟩, h3⟩

lemma card_eq_sum (hL : 0 < L) (S : Finset (Fin (2 * H + 1))) :
    S.card = ∑ b : Fin L, (S.filter (fun i => i.val % L = b.val)).card := by
  have h1 : ∀ i : Fin (2 * H + 1),
      (∑ b : Fin L, (if i.val % L = b.val then (1 : ℕ) else 0)) = 1 := by
    intro i
    have hb0 : ∀ b : Fin L, (i.val % L = b.val) ↔ b = (⟨i.val % L, Nat.mod_lt _ hL⟩ : Fin L) := by
      intro b; rw [Fin.ext_iff]; constructor <;> intro h <;> exact h.symm
    simp only [hb0]
    simp
  calc S.card = ∑ i ∈ S, 1 := by simp
    _ = ∑ i ∈ S, ∑ b : Fin L, (if i.val % L = b.val then (1 : ℕ) else 0) := by
        refine Finset.sum_congr rfl (fun i _ => (h1 i).symm)
    _ = ∑ b : Fin L, ∑ i ∈ S, (if i.val % L = b.val then (1 : ℕ) else 0) := Finset.sum_comm
    _ = ∑ b : Fin L, (S.filter (fun i => i.val % L = b.val)).card := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [← Finset.sum_filter]
        simp

lemma class_lower (hL : 0 < L) (U : Finset (Fin (2 * H + 1))) (b : ℕ) (hb : b < L) :
    cn H L U b + cn H L U (sres H L b) - (cls H L b).card
      ≤ ((U.filter (fun i => i.val % L = b)).filter (fun i => i.rev ∈ U)).card := by
  have hXsub : (U.filter (fun i => i.val % L = b)) ⊆ cls H L b := by
    intro i hi; exact (mem_cls H L b i).mpr (Finset.mem_filter.mp hi).2
  have hYsub : ((U.filter (fun i => i.val % L = sres H L b)).image Fin.rev) ⊆ cls H L b := by
    intro i hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
    have hj2 : j.val % L = sres H L b := (Finset.mem_filter.mp hj).2
    rw [mem_cls, ← hji, res_rev H L hL j, hj2, sres_invol H L hL b hb]
  have hinter : (U.filter (fun i => i.val % L = b)) ∩
      ((U.filter (fun i => i.val % L = sres H L b)).image Fin.rev)
      = (U.filter (fun i => i.val % L = b)).filter (fun i => i.rev ∈ U) := by
    ext i
    constructor
    · intro hi
      have h1 := (Finset.mem_inter.mp hi).1
      have h2 := (Finset.mem_inter.mp hi).2
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h2
      refine Finset.mem_filter.mpr ⟨h1, ?_⟩
      rw [← hji, Fin.rev_rev]
      exact (Finset.mem_filter.mp hj).1
    · intro hi
      have h1 := (Finset.mem_filter.mp hi).1
      have h2 := (Finset.mem_filter.mp hi).2
      refine Finset.mem_inter.mpr ⟨h1, ?_⟩
      refine Finset.mem_image.mpr ⟨i.rev, Finset.mem_filter.mpr ⟨h2, ?_⟩, Fin.rev_rev i⟩
      rw [res_rev H L hL i, (Finset.mem_filter.mp h1).2]
  have hcard : ((U.filter (fun i => i.val % L = b)).card
      + ((U.filter (fun i => i.val % L = sres H L b)).image Fin.rev).card
      - (cls H L b).card)
      ≤ ((U.filter (fun i => i.val % L = b)) ∩
        ((U.filter (fun i => i.val % L = sres H L b)).image Fin.rev)).card := by
    have h1 := Finset.card_union_add_card_inter (U.filter (fun i => i.val % L = b))
      ((U.filter (fun i => i.val % L = sres H L b)).image Fin.rev)
    have h2 := Finset.card_le_card (Finset.union_subset hXsub hYsub)
    omega
  calc cn H L U b + cn H L U (sres H L b) - (cls H L b).card
      = (U.filter (fun i => i.val % L = b)).card
        + ((U.filter (fun i => i.val % L = sres H L b)).image Fin.rev).card
        - (cls H L b).card := by
          unfold cn
          rw [Finset.card_image_of_injective _ Fin.rev_injective]
    _ ≤ ((U.filter (fun i => i.val % L = b)) ∩
        ((U.filter (fun i => i.val % L = sres H L b)).image Fin.rev)).card := hcard
    _ = ((U.filter (fun i => i.val % L = b)).filter (fun i => i.rev ∈ U)).card := by
          rw [hinter]

lemma cn_wit (hL : 0 < L) (A : Finset (Fin (2 * H + 1))) (b : ℕ) (hb : b < L) :
    cn H L (wit H L A) b = cn H L A b := by
  show ((wit H L A).filter (fun i => i.val % L = b)).card = cn H L A b
  have haQ : cn H L A b ≤ (2 * H + L - b) / L := by
    rw [← cls_card H L hL b hb]; exact cn_le H L A b
  have key : ((wit H L A).filter (fun i => i.val % L = b)).card
      = (Finset.range (cn H L A b)).card := by
    refine Finset.card_bij (fun i _ => i.val / L) ?_ ?_ ?_
    · intro i hi
      have h1 : i.val % L = b := (Finset.mem_filter.mp hi).2
      have h2 : i ∈ wit H L A := (Finset.mem_filter.mp hi).1
      have h := (mem_wit H L A i).mp h2
      rw [h1] at h
      exact Finset.mem_range.mpr h
    · intro i hi j hj h
      exact cls_inj H L ((mem_cls H L b i).mpr (Finset.mem_filter.mp hi).2)
        ((mem_cls H L b j).mpr (Finset.mem_filter.mp hj).2) h
    · intro k hk
      have hk1 : k < cn H L A b := Finset.mem_range.mp hk
      have hk2 : k < (2 * H + L - b) / L := lt_of_lt_of_le hk1 haQ
      obtain ⟨i, hi, hic⟩ := exists_cls H L hL b hb k hk2
      have hib : i.val % L = b := (mem_cls H L b i).mp hi
      exact ⟨i, Finset.mem_filter.mpr ⟨by rw [mem_wit, hib, hic]; exact hk1, hib⟩, hic⟩
  rw [key, Finset.card_range]

lemma hit_wit_term (hL : 0 < L) (A : Finset (Fin (2 * H + 1))) (b : ℕ) (hb : b < L) :
    (((wit H L A).filter (fun i => i.val % L = b)).filter
        (fun i => i.rev ∈ wit H L A)).card
      = cn H L A b + cn H L A (sres H L b) - (cls H L b).card := by
  have hcard := cls_card H L hL b hb
  have haQ : cn H L A b ≤ (2 * H + L - b) / L := by
    rw [← hcard]; exact cn_le H L A b
  have ha'Q : cn H L A (sres H L b) ≤ (2 * H + L - b) / L := by
    have h1 : cn H L A (sres H L b) ≤ (cls H L (sres H L b)).card := cn_le H L A _
    rw [cls_rev_card H L hL b hb, hcard] at h1
    exact h1
  have key : (((wit H L A).filter (fun i => i.val % L = b)).filter
        (fun i => i.rev ∈ wit H L A)).card
      = (Finset.Ico ((2 * H + L - b) / L - cn H L A (sres H L b)) (cn H L A b)).card := by
    refine Finset.card_bij (fun i _ => i.val / L) ?_ ?_ ?_
    · intro i hi
      have h1 : i.val % L = b := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
      have h2 : i ∈ wit H L A := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
      have h3 : i.rev ∈ wit H L A := (Finset.mem_filter.mp hi).2
      have h4 : i.val / L < cn H L A b := by
        have h := (mem_wit H L A i).mp h2
        rwa [h1] at h
      have h5 : i.rev.val / L < cn H L A (sres H L b) := by
        have h := (mem_wit H L A i.rev).mp h3
        rwa [res_rev H L hL i, h1] at h
      have h6 : i.val / L < (2 * H + L - b) / L :=
        cls_div_lt H L hL b hb i ((mem_cls H L b i).mpr h1)
      have h7 : i.rev.val / L = (2 * H + L - b) / L - 1 - i.val / L :=
        cls_rev_div H L hL b hb i ((mem_cls H L b i).mpr h1)
      rw [h7] at h5
      exact Finset.mem_Ico.mpr ⟨nat_sub_le h6 h5, h4⟩
    · intro i hi j hj h
      exact cls_inj H L
        ((mem_cls H L b i).mpr (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2)
        ((mem_cls H L b j).mpr (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2) h
    · intro k hk
      have hk1 : k < cn H L A b := (Finset.mem_Ico.mp hk).2
      have hk2 : (2 * H + L - b) / L - cn H L A (sres H L b) ≤ k := (Finset.mem_Ico.mp hk).1
      have hk3 : k < (2 * H + L - b) / L := lt_of_lt_of_le hk1 haQ
      obtain ⟨i, hi, hic⟩ := exists_cls H L hL b hb k hk3
      have hib : i.val % L = b := (mem_cls H L b i).mp hi
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, hib⟩, ?_⟩, hic⟩
      · rw [mem_wit, hib, hic]; exact hk1
      · rw [mem_wit, res_rev H L hL i, hib, cls_rev_div H L hL b hb i hi, hic]
        exact nat_sub_lt hk3 hk2
  rw [key, Nat.card_Ico, hcard]
  exact nat_sub_sub ha'Q

lemma hit_wit (hL : 0 < L) (A : Finset (Fin (2 * H + 1))) :
    hitt H L (wit H L A)
      = ∑ b : Fin L, (cn H L A b.val + cn H L A (sres H L b.val) - (cls H L b.val).card) := by
  show ((wit H L A).filter (fun i => i.rev ∈ wit H L A)).card = _
  rw [card_eq_sum H L hL]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [filter_swap]
  exact hit_wit_term H L hL A b.val b.isLt

end Conjectures.Goldbach.ThetaResidueOverlapMinimum_aux

open Conjectures.Goldbach.ThetaResidueOverlapMinimum_aux

theorem Conjectures.Goldbach.ThetaResidueOverlapMinimum :
    ∀ (H L : ℕ), 0 < L → ∀ A : Finset (Fin (2*H+1)), let cnt := fun (U : Finset (Fin (2*H+1))) (b : ℕ) => (U.filter (fun i => i.val % L = b)).card; let hit := fun (U : Finset (Fin (2*H+1))) => (U.filter (fun i => i.rev ∈ U)).card; let same := fun (U : Finset (Fin (2*H+1))) => ∀ b : Fin L, cnt U b.val = cnt A b.val; let lower := ∑ b : Fin L, (cnt A b.val + cnt A ((2*H+L-b.val) % L) - cnt Finset.univ b.val); (∀ U, same U → lower ≤ hit U) ∧ ∃ U, same U ∧ hit U = lower := by
  intro H L hL A
  show (∀ U : Finset (Fin (2*H+1)), (∀ b : Fin L, cn H L U b.val = cn H L A b.val) →
      (∑ b : Fin L, (cn H L A b.val + cn H L A (sres H L b.val) - (cls H L b.val).card))
        ≤ hitt H L U) ∧
    ∃ U : Finset (Fin (2*H+1)), (∀ b : Fin L, cn H L U b.val = cn H L A b.val) ∧
      hitt H L U = ∑ b : Fin L, (cn H L A b.val + cn H L A (sres H L b.val)
        - (cls H L b.val).card)
  refine ⟨?_, ?_⟩
  · intro U hU
    have hsum : hitt H L U
        = ∑ b : Fin L, ((U.filter (fun i => i.rev ∈ U)).filter
            (fun i => i.val % L = b.val)).card := by
      rw [hitt, card_eq_sum H L hL]
    rw [hsum]
    refine Finset.sum_le_sum (fun b _ => ?_)
    rw [filter_swap]
    have h1 := class_lower H L hL U b.val b.isLt
    rw [hU b] at h1
    have h2 : cn H L U (sres H L b.val) = cn H L A (sres H L b.val) :=
      hU ⟨sres H L b.val, sres_lt H L hL b.val⟩
    rw [h2] at h1
    exact h1
  · refine ⟨wit H L A, fun b => cn_wit H L hL A b.val b.isLt, ?_⟩
    exact hit_wit H L hL A
