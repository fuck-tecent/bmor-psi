import Mathlib

namespace Conjectures.Goldbach.FareyComplementQuadrature_aux

open Classical

def Dset (Q : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 Q) ×ˢ (Finset.Icc 1 Q)).filter (fun p => Q < p.1 + p.2 ∧ p.1.Coprime p.2)

def Frac (Q : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 0 Q) ×ˢ (Finset.Icc 1 Q)).filter (fun p => p.1 ≤ p.2 ∧ p.1.Coprime p.2)

def Aset (Q : ℕ) (δ : ℝ) : Set ℝ :=
  {x : ℝ | ∃ d c : ℕ, 1 ≤ d ∧ d ≤ Q ∧ c ≤ d ∧ c.Coprime d ∧ |x - (c : ℝ) / d| ≤ δ / d}

noncomputable def auxB (q s : ℕ) : ℕ :=
  if h : 1 < s ∧ q.Coprime s then Classical.choose (Nat.exists_mul_mod_eq_one_of_coprime h.2 h.1) else 1

noncomputable def abPair (p : ℕ × ℕ) : ℕ × ℕ :=
  ((auxB p.1 p.2 * p.1 - 1) / p.2, auxB p.1 p.2)

noncomputable def cell (p : ℕ × ℕ) : Set ℝ :=
  Set.Ioo (((abPair p).1 : ℝ) / (p.1 : ℝ)) (((abPair p).2 : ℝ) / (p.2 : ℝ))

noncomputable def gap (δ : ℝ) (p : ℕ × ℕ) : Set ℝ :=
  Set.Ioo ((((abPair p).1 : ℝ) + δ) / (p.1 : ℝ)) ((((abPair p).2 : ℝ) - δ) / (p.2 : ℝ))

theorem mem_Aset {Q : ℕ} {δ x : ℝ} :
    x ∈ Aset Q δ ↔ ∃ d c : ℕ, 1 ≤ d ∧ d ≤ Q ∧ c ≤ d ∧ c.Coprime d ∧ |x - (c : ℝ) / d| ≤ δ / d :=
  Iff.rfl

theorem mem_gap_iff {δ : ℝ} {p : ℕ × ℕ} {x : ℝ} :
    x ∈ gap δ p ↔
      ((((abPair p).1 : ℝ) + δ) / (p.1 : ℝ) < x ∧
        x < (((abPair p).2 : ℝ) - δ) / (p.2 : ℝ)) := Iff.rfl

theorem mem_cell_iff {p : ℕ × ℕ} {x : ℝ} :
    x ∈ cell p ↔
      (((abPair p).1 : ℝ) / (p.1 : ℝ) < x ∧ x < ((abPair p).2 : ℝ) / (p.2 : ℝ)) := Iff.rfl

theorem mem_Dset {Q : ℕ} {p : ℕ × ℕ} :
    p ∈ Dset Q ↔ (1 ≤ p.1 ∧ p.1 ≤ Q ∧ 1 ≤ p.2 ∧ p.2 ≤ Q ∧ Q < p.1 + p.2 ∧ p.1.Coprime p.2) := by
  constructor
  · intro hp
    have h1 : p ∈ ((Finset.Icc 1 Q) ×ˢ (Finset.Icc 1 Q)).filter
        (fun p => Q < p.1 + p.2 ∧ p.1.Coprime p.2) := hp
    have h2 := Finset.mem_filter.mp h1
    have h3 : p.1 ∈ Finset.Icc 1 Q ∧ p.2 ∈ Finset.Icc 1 Q := Finset.mem_product.mp h2.1
    have h4 : 1 ≤ p.1 ∧ p.1 ≤ Q := Finset.mem_Icc.mp h3.1
    have h5 : 1 ≤ p.2 ∧ p.2 ≤ Q := Finset.mem_Icc.mp h3.2
    have h6 : Q < p.1 + p.2 ∧ p.1.Coprime p.2 := h2.2
    exact ⟨h4.1, h4.2, h5.1, h5.2, h6.1, h6.2⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    show p ∈ ((Finset.Icc 1 Q) ×ˢ (Finset.Icc 1 Q)).filter
      (fun p => Q < p.1 + p.2 ∧ p.1.Coprime p.2)
    refine Finset.mem_filter.mpr ⟨?_, ⟨h5, h6⟩⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨h1, h2⟩, Finset.mem_Icc.mpr ⟨h3, h4⟩⟩

theorem mem_Frac {Q : ℕ} {p : ℕ × ℕ} :
    p ∈ Frac Q ↔ (1 ≤ p.2 ∧ p.2 ≤ Q ∧ p.1 ≤ p.2 ∧ p.1.Coprime p.2) := by
  constructor
  · intro hp
    have h1 : p ∈ ((Finset.Icc 0 Q) ×ˢ (Finset.Icc 1 Q)).filter
        (fun p => p.1 ≤ p.2 ∧ p.1.Coprime p.2) := hp
    have h2 := Finset.mem_filter.mp h1
    have h3 : p.1 ∈ Finset.Icc 0 Q ∧ p.2 ∈ Finset.Icc 1 Q := Finset.mem_product.mp h2.1
    have h4 : 1 ≤ p.2 ∧ p.2 ≤ Q := Finset.mem_Icc.mp h3.2
    have h5 : p.1 ≤ p.2 ∧ p.1.Coprime p.2 := h2.2
    exact ⟨h4.1, h4.2, h5.1, h5.2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    show p ∈ ((Finset.Icc 0 Q) ×ˢ (Finset.Icc 1 Q)).filter
      (fun p => p.1 ≤ p.2 ∧ p.1.Coprime p.2)
    refine Finset.mem_filter.mpr ⟨?_, ⟨h3, h4⟩⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, le_trans h3 h2⟩, Finset.mem_Icc.mpr ⟨h1, h2⟩⟩

theorem auxB_of {q s : ℕ} (h : 1 < s ∧ q.Coprime s) :
    auxB q s = Classical.choose (Nat.exists_mul_mod_eq_one_of_coprime h.2 h.1) := by
  rw [auxB, dif_pos h]

theorem auxB_lt {q s : ℕ} (h : 1 < s ∧ q.Coprime s) : auxB q s < s := by
  rw [auxB_of h]
  exact (Classical.choose_spec (Nat.exists_mul_mod_eq_one_of_coprime h.2 h.1)).1

theorem auxB_mod {q s : ℕ} (h : 1 < s ∧ q.Coprime s) : q * auxB q s % s = 1 := by
  rw [auxB_of h]
  exact (Classical.choose_spec (Nat.exists_mul_mod_eq_one_of_coprime h.2 h.1)).2

theorem abPair_spec {Q : ℕ} {p : ℕ × ℕ} (hp : p ∈ Dset Q) :
    (abPair p).1 ≤ p.1 ∧ (abPair p).2 ≤ p.2 ∧ (abPair p).2 * p.1 = (abPair p).1 * p.2 + 1 := by
  obtain ⟨hq1, hqQ, hs1, hsQ, hsum, hc⟩ := mem_Dset.mp hp
  have hs0 : 0 < p.2 := hs1
  have key : (auxB p.1 p.2 * p.1 - 1) / p.2 ≤ p.1 ∧ auxB p.1 p.2 ≤ p.2 ∧
      auxB p.1 p.2 * p.1 = (auxB p.1 p.2 * p.1 - 1) / p.2 * p.2 + 1 := by
    by_cases h1 : p.2 = 1
    · have hb1 : auxB p.1 p.2 = 1 := by
        have hx : ¬ (1 < p.2 ∧ p.1.Coprime p.2) := by
          rw [h1]
          simp
        rw [auxB, dif_neg hx]
      refine ⟨?_, ?_, ?_⟩
      · rw [hb1, h1, Nat.one_mul, Nat.div_one]; omega
      · have hb2 : auxB p.1 p.2 = 1 := hb1
        omega
      · rw [hb1, h1, Nat.one_mul, Nat.div_one, Nat.mul_one]; omega
    · have hlarge : 1 < p.2 := by omega
      have hcond : 1 < p.2 ∧ p.1.Coprime p.2 := ⟨hlarge, hc⟩
      have hlt : auxB p.1 p.2 < p.2 := auxB_lt hcond
      have hmod : p.1 * auxB p.1 p.2 % p.2 = 1 := auxB_mod hcond
      have hident : p.1 * auxB p.1 p.2 = p.2 * (p.1 * auxB p.1 p.2 / p.2) + 1 := by
        have h := Nat.mod_add_div (p.1 * auxB p.1 p.2) p.2
        rw [hmod] at h
        omega
      have hsub : auxB p.1 p.2 * p.1 - 1 = p.2 * (p.1 * auxB p.1 p.2 / p.2) := by
        have hcomm : auxB p.1 p.2 * p.1 = p.1 * auxB p.1 p.2 := Nat.mul_comm _ _
        omega
      have hdvd : p.2 ∣ auxB p.1 p.2 * p.1 - 1 :=
        ⟨p.1 * auxB p.1 p.2 / p.2, hsub⟩
      have hdm : (auxB p.1 p.2 * p.1 - 1) / p.2 * p.2 = auxB p.1 p.2 * p.1 - 1 :=
        Nat.div_mul_cancel hdvd
      have hpos : 1 ≤ auxB p.1 p.2 * p.1 := by
        by_contra hx
        have hz : auxB p.1 p.2 * p.1 = 0 := by omega
        have hz2 : p.1 * auxB p.1 p.2 = 0 := by
          rw [Nat.mul_comm]
          exact hz
        rw [hz2] at hmod
        have h4 := Nat.mod_le (0 : ℕ) p.2
        omega
      refine ⟨?_, Nat.le_of_lt hlt, ?_⟩
      · have h2 : auxB p.1 p.2 * p.1 ≤ p.1 * p.2 := by
          rw [Nat.mul_comm p.1 p.2]
          exact Nat.mul_le_mul_right p.1 (Nat.le_of_lt hlt)
        have h3 : (auxB p.1 p.2 * p.1 - 1) / p.2 * p.2 ≤ p.1 * p.2 := by
          rw [hdm]
          have h5 := Nat.sub_le (auxB p.1 p.2 * p.1) 1
          omega
        exact Nat.le_of_mul_le_mul_right h3 hs0
      · omega
  simpa only [abPair] using key

theorem det_coprime {a b q s : ℕ} (h : b * q = a * s + 1) :
    Nat.Coprime a q ∧ Nat.Coprime b s ∧ Nat.Coprime q s := by
  have key : ∀ k : ℕ, k ∣ b * q → k ∣ a * s → k = 1 := by
    intro k hk1 hk2
    have hsub : b * q - a * s = 1 := by omega
    have hk3 : k ∣ b * q - a * s := Nat.dvd_sub hk1 hk2
    rw [hsub] at hk3
    exact Nat.dvd_one.mp hk3
  refine ⟨?_, ?_, ?_⟩
  · show Nat.gcd a q = 1
    exact key _ (dvd_mul_of_dvd_right (Nat.gcd_dvd_right a q) b)
      (dvd_mul_of_dvd_left (Nat.gcd_dvd_left a q) s)
  · show Nat.gcd b s = 1
    exact key _ (dvd_mul_of_dvd_left (Nat.gcd_dvd_left b s) q)
      (dvd_mul_of_dvd_right (Nat.gcd_dvd_right b s) a)
  · show Nat.gcd q s = 1
    exact key _ (dvd_mul_of_dvd_right (Nat.gcd_dvd_left q s) b)
      (dvd_mul_of_dvd_right (Nat.gcd_dvd_right q s) a)

theorem ab_unique {q s a b a' b' : ℕ} (hq : 1 ≤ q) (hs : 1 ≤ s) (hb : b ≤ s) (hb' : b' ≤ s)
    (h1 : b * q = a * s + 1) (h2 : b' * q = a' * s + 1) : a = a' ∧ b = b' := by
  have hgsq : Nat.gcd s q = 1 := by
    have hx : Nat.gcd q s = 1 := (det_coprime h1).2.2
    rw [Nat.gcd_comm]
    exact hx
  have hb1 : 1 ≤ b := by
    by_contra hx
    have hz : b = 0 := by omega
    rw [hz] at h1
    omega
  have hb1' : 1 ≤ b' := by
    by_contra hx
    have hz : b' = 0 := by omega
    rw [hz] at h2
    omega
  have e1 : Nat.ModEq s 1 (b * q) := by
    have hpos : 1 ≤ b * q := by omega
    have h3 : b * q - 1 = a * s := by
      rw [h1]
      omega
    rw [Nat.modEq_iff_dvd' hpos, h3]
    exact dvd_mul_left s a
  have e2 : Nat.ModEq s 1 (b' * q) := by
    have hpos : 1 ≤ b' * q := by omega
    have h3 : b' * q - 1 = a' * s := by
      rw [h2]
      omega
    rw [Nat.modEq_iff_dvd' hpos, h3]
    exact dvd_mul_left s a'
  have hme : Nat.ModEq s b b' :=
    Nat.ModEq.cancel_right_of_coprime hgsq (Nat.ModEq.trans (Nat.ModEq.symm e1) e2)
  have heq : b % s = b' % s := hme
  have hbb : b = b' := by
    by_cases hbs : b = s
    · have hz : b' % s = 0 := by
        rw [← heq, hbs, Nat.mod_self]
      have hd : s ∣ b' := Nat.dvd_iff_mod_eq_zero.mpr hz
      have hle : s ≤ b' := Nat.le_of_dvd (by omega) hd
      omega
    · by_cases hbs' : b' = s
      · have hz : b % s = 0 := by
          rw [heq, hbs', Nat.mod_self]
        have hd : s ∣ b := Nat.dvd_iff_mod_eq_zero.mpr hz
        have hle : s ≤ b := Nat.le_of_dvd (by omega) hd
        omega
      · rw [Nat.mod_eq_of_lt (by omega : b < s), Nat.mod_eq_of_lt (by omega : b' < s)] at heq
        exact heq
  refine ⟨?_, hbb⟩
  have h3 : a * s = a' * s := by
    have f1 : a * s + 1 = b * q := h1.symm
    have f2 : b * q = b' * q := by rw [hbb]
    have f3 : b' * q = a' * s + 1 := h2
    omega
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < s) h3

theorem abPair_eq {Q : ℕ} {p : ℕ × ℕ} (hp : p ∈ Dset Q) (a b : ℕ) (hb : b ≤ p.2)
    (hdet : b * p.1 = a * p.2 + 1) : abPair p = (a, b) := by
  obtain ⟨hq1, hqQ, hs1, hsQ, hsum, hc⟩ := mem_Dset.mp hp
  obtain ⟨hle1, hle2, hspec⟩ := abPair_spec hp
  obtain ⟨ha, hb2⟩ := ab_unique hq1 hs1 hle2 hb hspec hdet
  exact Prod.ext ha hb2

theorem frac_unique {c d a q : ℕ} (hd : 1 ≤ d) (hq : 1 ≤ q) (hcd : Nat.Coprime c d)
    (haq : Nat.Coprime a q) (h : (c : ℝ) / d = (a : ℝ) / q) : c = a ∧ d = q := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have h1 : (c : ℝ) * q ≤ (a : ℝ) * d := (div_le_div_iff₀ hdpos hqpos).mp (le_of_eq h)
  have h2 : (a : ℝ) * d ≤ (c : ℝ) * q := (div_le_div_iff₀ hqpos hdpos).mp (le_of_eq h.symm)
  have cross : c * q = a * d := by
    have e1 : c * q ≤ a * d := by exact_mod_cast h1
    have e2 : a * d ≤ c * q := by exact_mod_cast h2
    omega
  have hqd : q ∣ d := by
    have hx : q ∣ c * q := dvd_mul_left q c
    rw [cross] at hx
    exact ((Nat.Coprime.symm haq).dvd_mul_left).mp hx
  have hdq : d ∣ q := by
    have hx : d ∣ a * d := dvd_mul_left d a
    rw [← cross] at hx
    exact ((Nat.Coprime.symm hcd).dvd_mul_left).mp hx
  have hdq' : d = q := Nat.dvd_antisymm hdq hqd
  refine ⟨?_, hdq'⟩
  have h3 : c * q = a * q := by
    rw [cross, hdq']
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) h3

private theorem denominator_eq_of_frac_eq {u v m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hcopu : Nat.Coprime u m) (hcopv : Nat.Coprime v n)
    (h : (u : ℝ) / m = (v : ℝ) / n) : m = n := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcrossR : (u : ℝ) * n = (v : ℝ) * m :=
    (div_eq_div_iff hmR.ne' hnR.ne').mp h
  have hcross : u * n = v * m := by exact_mod_cast hcrossR
  have hmprod : m ∣ u * n := by
    rw [hcross]
    exact ⟨v, mul_comm v m⟩
  have hmdvd : m ∣ n := by
    apply hcopu.symm.dvd_of_dvd_mul_right
    simpa [mul_comm] using hmprod
  have hnprod : n ∣ v * m := by
    rw [← hcross]
    exact ⟨u, mul_comm u n⟩
  have hndvd : n ∣ m := by
    apply hcopv.symm.dvd_of_dvd_mul_right
    simpa [mul_comm] using hnprod
  exact Nat.dvd_antisymm hmdvd hndvd

private theorem coprime_right_of_det {a b q s : ℕ} (hdet : b * q = a * s + 1) :
    Nat.Coprime b s := by
  apply Nat.coprime_of_dvd'
  intro p hp hpb hps
  have hpq : p ∣ b * q := hpb.mul_right q
  have hpa : p ∣ a * s := hps.mul_left a
  have hpdiff : p ∣ b * q - a * s := Nat.dvd_sub hpq hpa
  have hsub : b * q - a * s = 1 := by omega
  simpa [hsub] using hpdiff

private theorem margin_step {δ m d : ℝ} (hm : 0 < m) (hd : 0 < d)
    (hδ : 0 ≤ δ) (hδm : δ * m < 1) :
    δ / d < δ / m + 1 / (m * d) := by
  have hmd : 0 < m * d := mul_pos hm hd
  calc
    δ / d = (δ * m) / (m * d) := by field_simp [hm.ne', hd.ne']
    _ < (δ * d + 1) / (m * d) := by
      apply (div_lt_div_iff_of_pos_right hmd).2
      nlinarith [mul_nonneg hδ hd.le]
    _ = δ / m + 1 / (m * d) := by field_simp [hm.ne', hd.ne']

theorem sep_denom {a b c d q s : ℕ} (hq : 1 ≤ q) (hs : 1 ≤ s) (hd : 1 ≤ d)
    (hdet : b * q = a * s + 1) (h1 : (a : ℝ) / q < (c : ℝ) / d)
    (h2 : (c : ℝ) / d < (b : ℝ) / s) : q + s ≤ d := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h1R : (a : ℝ) * d < (c : ℝ) * q :=
    (div_lt_div_iff₀ hqR hdR).mp h1
  have h2R : (c : ℝ) * s < (b : ℝ) * d :=
    (div_lt_div_iff₀ hdR hsR).mp h2
  have h1N : a * d < c * q := by exact_mod_cast h1R
  have h2N : c * s < b * d := by exact_mod_cast h2R
  have hleftN : a * d + 1 ≤ c * q := Nat.succ_le_of_lt h1N
  have hrightN : c * s + 1 ≤ b * d := Nat.succ_le_of_lt h2N
  have hleftR : (a : ℝ) * d + 1 ≤ (c : ℝ) * q := by exact_mod_cast hleftN
  have hrightR : (c : ℝ) * s + 1 ≤ (b : ℝ) * d := by exact_mod_cast hrightN
  have hdetR : (b : ℝ) * q = (a : ℝ) * s + 1 := by exact_mod_cast hdet
  have hleft : 1 / ((d : ℝ) * q) ≤ (c : ℝ) / d - (a : ℝ) / q := by
    rw [div_sub_div _ _ hdR.ne' hqR.ne']
    apply div_le_div_of_nonneg_right
    · linarith
    · exact (mul_pos hdR hqR).le
  have hright : 1 / ((s : ℝ) * d) ≤ (b : ℝ) / s - (c : ℝ) / d := by
    rw [div_sub_div _ _ hsR.ne' hdR.ne']
    apply div_le_div_of_nonneg_right
    · linarith
    · exact (mul_pos hsR hdR).le
  have hgap : (b : ℝ) / s - (a : ℝ) / q = 1 / ((q : ℝ) * s) := by
    rw [div_sub_div _ _ hsR.ne' hqR.ne']
    have hnum : (b : ℝ) * q - (s : ℝ) * a = 1 := by
      rw [mul_comm (s : ℝ) a]
      linarith
    rw [hnum]
    field_simp [hqR.ne', hsR.ne']
  have hsum : 1 / ((s : ℝ) * d) + 1 / ((d : ℝ) * q) ≤
      (b : ℝ) / s - (a : ℝ) / q := by
    linarith
  have hsum' : ((q : ℝ) + s) / ((q : ℝ) * s * d) ≤ 1 / ((q : ℝ) * s) := by
    calc
      ((q : ℝ) + s) / ((q : ℝ) * s * d) =
          1 / ((s : ℝ) * d) + 1 / ((d : ℝ) * q) := by
            field_simp [hqR.ne', hsR.ne', hdR.ne']
      _ ≤ (b : ℝ) / s - (a : ℝ) / q := hsum
      _ = 1 / ((q : ℝ) * s) := hgap
  have hprod : (0 : ℝ) < (q : ℝ) * s * d := mul_pos (mul_pos hqR hsR) hdR
  have hcast : (q : ℝ) + s ≤ (d : ℝ) := by
    calc
      (q : ℝ) + s ≤ (1 / ((q : ℝ) * s)) * ((q : ℝ) * s * d) :=
        (div_le_iff₀ hprod).mp hsum'
      _ = (d : ℝ) := by field_simp [hqR.ne', hsR.ne', hdR.ne']
  exact_mod_cast hcast

theorem frac_sep {a c q d : ℕ} (hq : 1 ≤ q) (hd : 1 ≤ d) (hne : a * d ≠ c * q) :
    1 / ((q : ℝ) * (d : ℝ)) ≤ |(a : ℝ) / q - (c : ℝ) / d| := by
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  have hcross : (1 : ℝ) ≤ |(a : ℝ) * d - (c : ℝ) * q| := by
    rcases lt_or_gt_of_ne hne with h | h
    · have hstep : (a : ℝ) * d + 1 ≤ (c : ℝ) * q := by
        exact_mod_cast Nat.succ_le_of_lt h
      exact le_trans (by linarith) (neg_le_abs _)
    · have hstep : (c : ℝ) * q + 1 ≤ (a : ℝ) * d := by
        exact_mod_cast Nat.succ_le_of_lt h
      exact le_trans (by linarith) (le_abs_self _)
  have hquot : (a : ℝ) / q - (c : ℝ) / d =
      ((a : ℝ) * d - (c : ℝ) * q) / ((q : ℝ) * d) := by
    field_simp
  rw [hquot, abs_div, abs_of_pos (mul_pos hq' hd')]
  exact div_le_div_of_nonneg_right hcross (mul_pos hq' hd').le

theorem gap_nonempty_bound {δ : ℝ} {a b q s : ℕ} (hq : 1 ≤ q) (hs : 1 ≤ s)
    (hdet : b * q = a * s + 1) {x : ℝ} (hlo : ((a : ℝ) + δ) / q < x)
    (hhi : x < ((b : ℝ) - δ) / s) : δ * ((q : ℝ) + s) < 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hdetR : (b : ℝ) * q = (a : ℝ) * s + 1 := by exact_mod_cast hdet
  have hbetween : ((a : ℝ) + δ) / q < ((b : ℝ) - δ) / s := hlo.trans hhi
  have hcross : ((a : ℝ) + δ) * s < ((b : ℝ) - δ) * q :=
    (div_lt_div_iff₀ hqR hsR).mp hbetween
  ring_nf at hcross hdetR ⊢
  linarith

theorem gap_margin {δ x : ℝ} {a b c d q s : ℕ} (hδ : 0 ≤ δ) (hq : 1 ≤ q) (hs : 1 ≤ s)
    (hd : 1 ≤ d) (hdQ : d < q + s) (hdet : b * q = a * s + 1)
    (hcopq : Nat.Coprime a q) (hcopd : Nat.Coprime c d) (hb : b ≤ s)
    (hlt : δ * ((q : ℝ) + s) < 1)
    (hlo : ((a : ℝ) + δ) / q < x) (hhi : x < ((b : ℝ) - δ) / s) :
    δ / d < |x - (c : ℝ) / d| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hδq : δ * (q : ℝ) < 1 := by nlinarith
  have hδs : δ * (s : ℝ) < 1 := by nlinarith
  have hcopbs : Nat.Coprime b s := coprime_right_of_det hdet
  have hout : (c : ℝ) / d ≤ (a : ℝ) / q ∨ (b : ℝ) / s ≤ (c : ℝ) / d := by
    rcases lt_or_ge ((a : ℝ) / q) ((c : ℝ) / d) with hac | hca
    · right
      by_contra hbc
      have hcb : (c : ℝ) / d < (b : ℝ) / s := lt_of_not_ge hbc
      have hden : q + s ≤ d := sep_denom hq hs hd hdet hac hcb
      omega
    · exact Or.inl hca
  rcases hout with hca | hbc
  · have hax : (a : ℝ) / q ≤ ((a : ℝ) + δ) / q := by
      apply div_le_div_of_nonneg_right
      · linarith
      · exact hqR.le
    have hcx : (c : ℝ) / d < x := lt_of_le_of_lt (hca.trans hax) hlo
    rw [abs_of_pos (sub_pos.mpr hcx)]
    by_cases heq : (c : ℝ) / d = (a : ℝ) / q
    · have hdq : d = q := denominator_eq_of_frac_eq hd hq hcopd hcopq heq
      have hlo' : (a : ℝ) / q + δ / q < x := by
        convert hlo using 1 <;> ring
      rw [heq, hdq]
      linarith
    · have hstrict : (c : ℝ) / d < (a : ℝ) / q := lt_of_le_of_ne hca heq
      have hcrossR : (c : ℝ) * q < (a : ℝ) * d :=
        (div_lt_div_iff₀ hdR hqR).mp hstrict
      have hcrossN : c * q < a * d := by exact_mod_cast hcrossR
      have hne : a * d ≠ c * q := by omega
      have hsep := frac_sep hq hd hne
      have hsep' : 1 / ((q : ℝ) * d) ≤ (a : ℝ) / q - (c : ℝ) / d := by
        rw [abs_of_pos (sub_pos.mpr hstrict)] at hsep
        exact hsep
      have hdecomp : ((a : ℝ) + δ) / q - (c : ℝ) / d =
          δ / q + ((a : ℝ) / q - (c : ℝ) / d) := by ring
      have hbound : δ / q + 1 / ((q : ℝ) * d) < x - (c : ℝ) / d := by
        have hlo'' : ((a : ℝ) + δ) / q - (c : ℝ) / d < x - (c : ℝ) / d := by
          linarith
        rw [hdecomp] at hlo''
        exact lt_of_le_of_lt (by simpa [add_comm] using add_le_add_left hsep' (δ / q)) hlo''
      exact (margin_step hqR hdR hδ hδq).trans hbound
  · have hbx : ((b : ℝ) - δ) / s ≤ (b : ℝ) / s := by
      apply div_le_div_of_nonneg_right
      · linarith
      · exact hsR.le
    have hxc : x < (c : ℝ) / d := lt_of_lt_of_le (hhi.trans_le hbx) hbc
    rw [abs_of_neg (sub_neg.mpr hxc)]
    by_cases heq : (b : ℝ) / s = (c : ℝ) / d
    · have hsd : s = d := denominator_eq_of_frac_eq hs hd hcopbs hcopd heq
      have hsdR : (s : ℝ) = d := by exact_mod_cast hsd
      have hhi' : x < (b : ℝ) / s - δ / s := by
        convert hhi using 1 <;> ring
      rw [← heq, ← hsdR]
      linarith
    · have hstrict : (b : ℝ) / s < (c : ℝ) / d := lt_of_le_of_ne hbc heq
      have hcrossR : (b : ℝ) * d < (c : ℝ) * s :=
        (div_lt_div_iff₀ hsR hdR).mp hstrict
      have hcrossN : b * d < c * s := by exact_mod_cast hcrossR
      have hne : b * d ≠ c * s := by omega
      have hsep := frac_sep hs hd hne
      have hsep' : 1 / ((s : ℝ) * d) ≤ (c : ℝ) / d - (b : ℝ) / s := by
        rw [abs_of_neg (sub_neg.mpr hstrict)] at hsep
        linarith
      have hdecomp : (c : ℝ) / d - ((b : ℝ) - δ) / s =
          (c : ℝ) / d - (b : ℝ) / s + δ / s := by ring
      have hbound : δ / s + 1 / ((s : ℝ) * d) < (c : ℝ) / d - x := by
        have hhi'' : (c : ℝ) / d - ((b : ℝ) - δ) / s < (c : ℝ) / d - x := by
          linarith
        rw [hdecomp] at hhi''
        exact lt_of_le_of_lt (by simpa [add_comm] using add_le_add_left hsep' (δ / s)) hhi''
      simpa only [neg_sub] using (margin_step hsR hdR hδ hδs).trans hbound

set_option maxHeartbeats 1600000 in
theorem exists_cell (Q : ℕ) (hQ : 1 ≤ Q) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∃ a q b s : ℕ, 1 ≤ q ∧ q ≤ Q ∧ 1 ≤ s ∧ s ≤ Q ∧ a ≤ q ∧ b ≤ s ∧
      Nat.Coprime a q ∧ b * q = a * s + 1 ∧ Q < q + s ∧
      (a : ℝ) / q ≤ x ∧ x < (b : ℝ) / s := by
  classical
  have hzero : (0, 1) ∈ Frac Q := mem_Frac.mpr ⟨by simp, by simpa using hQ, by simp, by simp⟩
  let G : Finset ℝ := (Frac Q).image (fun p => (p.1 : ℝ) / (p.2 : ℝ))
  let H : Finset ℝ := G.filter (fun y => y ≤ x)
  have hG0 : (0 : ℝ) ∈ G := by
    show (0 : ℝ) ∈ (Frac Q).image (fun p => (p.1 : ℝ) / (p.2 : ℝ))
    refine Finset.mem_image.mpr ⟨(0, 1), hzero, ?_⟩
    simp
  have hHne : H.Nonempty := ⟨0, by
    show 0 ∈ G.filter (fun y => y ≤ x)
    exact Finset.mem_filter.mpr ⟨hG0, hx0⟩⟩
  obtain ⟨m, hmH, hmMax⟩ : ∃ m : ℝ, m ∈ H ∧ ∀ y ∈ H, y ≤ m :=
    ⟨H.max' hHne, Finset.max'_mem H hHne, fun y hy => Finset.le_max' H y hy⟩
  have hmG : m ∈ G := (Finset.mem_filter.mp hmH).1
  have hmx : m ≤ x := (Finset.mem_filter.mp hmH).2
  obtain ⟨p0, hp0, heq0⟩ := Finset.mem_image.mp hmG
  obtain ⟨a, q⟩ := p0
  have heq : (a : ℝ) / q = m := heq0
  have hq1 : 1 ≤ q := (mem_Frac.mp hp0).1
  have hqQ : q ≤ Q := (mem_Frac.mp hp0).2.1
  have haqle : a ≤ q := (mem_Frac.mp hp0).2.2.1
  have hac : Nat.Coprime a q := (mem_Frac.mp hp0).2.2.2
  have hax : (a : ℝ) / q ≤ x := by
    rw [heq]
    exact hmx
  have hmax : ∀ c d : ℕ, (c, d) ∈ Frac Q → (c : ℝ) / d ≤ x → (c : ℝ) / d ≤ (a : ℝ) / q := by
    intro c d hcd hcx
    rw [heq]
    have hmem : (c : ℝ) / d ∈ H := by
      show (c : ℝ) / d ∈ G.filter (fun y => y ≤ x)
      refine Finset.mem_filter.mpr ⟨?_, hcx⟩
      show (c : ℝ) / d ∈ (Frac Q).image (fun p => (p.1 : ℝ) / (p.2 : ℝ))
      exact Finset.mem_image.mpr ⟨(c, d), hcd, rfl⟩
    exact hmMax _ hmem
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have halt : a < q := by
    have h1 : (a : ℝ) / q < 1 := lt_of_le_of_lt hax hx1
    have h2 : (a : ℝ) < q := (div_lt_one hqpos).mp h1
    exact_mod_cast h2
  let T : Finset ℕ := (Finset.Icc 1 Q).filter (fun s => q ∣ a * s + 1)
  have hTne : T.Nonempty := by
    by_cases ha0 : a = 0
    · have hqone : q = 1 := by
        have h2 : Nat.gcd 0 q = 1 := by
          rw [← ha0]
          exact hac
        rw [Nat.gcd_zero_left] at h2
        exact h2
      refine ⟨1, ?_⟩
      show 1 ∈ (Finset.Icc 1 Q).filter (fun s => q ∣ a * s + 1)
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩, ?_⟩
      refine ⟨1, ?_⟩
      omega
    · have hqbig : 1 < q := by
        have h1 : 1 ≤ a := by omega
        omega
      obtain ⟨t, ht1, ht2⟩ := Nat.exists_mul_mod_eq_one_of_coprime hac hqbig
      have htpos : 1 ≤ t := by
        by_contra hx
        have ht0 : t = 0 := by omega
        rw [ht0] at ht2
        have h3 : (0 : ℕ) % q = 1 := by simpa using ht2
        have h4 := Nat.mod_le (0 : ℕ) q
        omega
      have hident : a * t = q * (a * t / q) + 1 := by
        have h := Nat.mod_add_div (a * t) q
        rw [ht2] at h
        omega
      have hk : a * t / q ≤ a := by
        have h5 : a * t / q * q ≤ a * t := Nat.div_mul_le_self (a * t) q
        have h6 : a * t ≤ a * q := Nat.mul_le_mul_left a (Nat.le_of_lt ht1)
        have h7 : a * t / q * q ≤ a * q := by omega
        exact Nat.le_of_mul_le_mul_right h7 (by omega : 0 < q)
      refine ⟨q - t, ?_⟩
      show q - t ∈ (Finset.Icc 1 Q).filter (fun s => q ∣ a * s + 1)
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      refine ⟨a - a * t / q, ?_⟩
      have e1 : a * (q - t) + a * t = a * q := by
        rw [← Nat.mul_add, Nat.sub_add_cancel (Nat.le_of_lt ht1)]
      have e2 : a * (q - t) + 1 + q * (a * t / q) = q * a := by
        have f1 : a * (q - t) + 1 + q * (a * t / q) = a * (q - t) + (q * (a * t / q) + 1) := by
          omega
        rw [f1, ← hident, e1, Nat.mul_comm a q]
      have e3 : q * (a - a * t / q) + q * (a * t / q) = q * a := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hk]
      omega
  obtain ⟨s, hsT, hsMax⟩ : ∃ s : ℕ, s ∈ T ∧ ∀ u ∈ T, u ≤ s :=
    ⟨T.max' hTne, Finset.max'_mem T hTne, fun u hu => Finset.le_max' T u hu⟩
  have hsIcc : s ∈ Finset.Icc 1 Q := (Finset.mem_filter.mp hsT).1
  have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hsIcc).1
  have hsQ : s ≤ Q := (Finset.mem_Icc.mp hsIcc).2
  have hsDvd : q ∣ a * s + 1 := (Finset.mem_filter.mp hsT).2
  have hsum : Q < q + s := by
    by_contra hx
    have hmem2 : s + q ∈ T := by
      show s + q ∈ (Finset.Icc 1 Q).filter (fun s => q ∣ a * s + 1)
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      have g1 : q ∣ (a * s + 1) + a * q := dvd_add hsDvd (dvd_mul_left q a)
      have g2 : a * (s + q) + 1 = (a * s + 1) + a * q := by ring
      rw [g2]
      exact g1
    have g3 := hsMax (s + q) hmem2
    omega
  obtain ⟨b, hbdet⟩ : ∃ b : ℕ, b * q = a * s + 1 := ⟨(a * s + 1) / q, Nat.div_mul_cancel hsDvd⟩
  have hbs : b ≤ s := by
    have h5 : a * s + 1 ≤ a * s + s := Nat.add_le_add_left hs1 (a * s)
    have h6 : a * s + s = (a + 1) * s := by
      rw [Nat.add_mul, Nat.one_mul]
    have h7 : (a + 1) * s ≤ q * s := Nat.mul_le_mul_right s (by omega : a + 1 ≤ q)
    have h8 : a * s + 1 ≤ q * s := by omega
    have h9 : b * q ≤ s * q := by
      rw [hbdet]
      have h10 : q * s = s * q := Nat.mul_comm q s
      omega
    exact Nat.le_of_mul_le_mul_right h9 (by omega : 0 < q)
  have hcopb : Nat.Coprime b s := (det_coprime hbdet).2.1
  have hsp : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hlt : (a : ℝ) / q < (b : ℝ) / s := by
    rw [div_lt_div_iff₀ hqpos hsp]
    have h9 : (b : ℝ) * q = (a : ℝ) * s + 1 := by exact_mod_cast hbdet
    linarith
  have hbx : x < (b : ℝ) / s := by
    by_contra hx
    have hmem3 : (b, s) ∈ Frac Q := mem_Frac.mpr ⟨hs1, hsQ, hbs, hcopb⟩
    have h9 : (b : ℝ) / s ≤ x := le_of_not_gt hx
    have h10 := hmax b s hmem3 h9
    linarith
  exact ⟨a, q, b, s, hq1, hqQ, hs1, hsQ, haqle, hbs, hac, hbdet, hsum, hax, hbx⟩

theorem cell_data {Q : ℕ} {p : ℕ × ℕ} (hp : p ∈ Dset Q) :
    1 ≤ p.1 ∧ 1 ≤ p.2 ∧ (abPair p).1 ≤ p.1 ∧ (abPair p).2 ≤ p.2 ∧
      Nat.Coprime (abPair p).1 p.1 ∧ Nat.Coprime (abPair p).2 p.2 ∧
      (abPair p).2 * p.1 = (abPair p).1 * p.2 + 1 := by
  obtain ⟨hq1, hqQ, hs1, hsQ, hsum, hcop⟩ := mem_Dset.mp hp
  obtain ⟨ha, hb, hdet⟩ := abPair_spec hp
  obtain ⟨hca, hcb, hcq⟩ := det_coprime hdet
  exact ⟨hq1, hs1, ha, hb, hca, hcb, hdet⟩

theorem gap_sub_Ac {Q : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) {p : ℕ × ℕ} (hp : p ∈ Dset Q) :
    gap δ p ⊆ (Aset Q δ)ᶜ := by
  intro x hx hmem
  rw [mem_Aset] at hmem
  obtain ⟨d, c, hd1, hdQ, hcd, hcopd, hclose⟩ := hmem
  obtain ⟨hq1, hs1, ha, hb, hca, hcb, hdet⟩ := cell_data hp
  have hsum : Q < p.1 + p.2 := (mem_Dset.mp hp).2.2.2.2.1
  have hx' := mem_gap_iff.mp hx
  have hlt : δ * ((p.1 : ℝ) + p.2) < 1 := gap_nonempty_bound hq1 hs1 hdet hx'.1 hx'.2
  have hdlt : d < p.1 + p.2 := by omega
  have hmar := gap_margin hδ hq1 hs1 hd1 hdlt hdet hca hcopd hb hlt hx'.1 hx'.2
  linarith

theorem gap_subset_cell {δ : ℝ} {p : ℕ × ℕ} (hδ : 0 ≤ δ) (hq1 : 1 ≤ p.1) (hs1 : 1 ≤ p.2) :
    gap δ p ⊆ cell p := by
  intro x hx
  have hq' : (0 : ℝ) < p.1 := by exact_mod_cast hq1
  have hs' : (0 : ℝ) < p.2 := by exact_mod_cast hs1
  have hx' := mem_gap_iff.mp hx
  rw [mem_cell_iff]
  constructor
  · have h1 : ((abPair p).1 : ℝ) / p.1 ≤ (((abPair p).1 : ℝ) + δ) / p.1 := by
      exact div_le_div_of_nonneg_right (by linarith) hq'.le
    linarith [hx'.1]
  · have h2 : (((abPair p).2 : ℝ) - δ) / p.2 ≤ ((abPair p).2 : ℝ) / p.2 := by
      exact div_le_div_of_nonneg_right (by linarith) hs'.le
    linarith [hx'.2]

theorem gap_subset_Icc {Q : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) {p : ℕ × ℕ} (hp : p ∈ Dset Q) :
    gap δ p ⊆ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨hq1, hs1, ha, hb, hca, hcb, hdet⟩ := cell_data hp
  have hq' : (0 : ℝ) < p.1 := by exact_mod_cast hq1
  have hs' : (0 : ℝ) < p.2 := by exact_mod_cast hs1
  intro x hx
  have hx' := mem_gap_iff.mp hx
  constructor
  · have h1 : (0 : ℝ) ≤ (((abPair p).1 : ℝ) + δ) / p.1 := by
      have h2 : (0 : ℝ) ≤ ((abPair p).1 : ℝ) + δ := by
        have h3 : (0 : ℝ) ≤ ((abPair p).1 : ℝ) := Nat.cast_nonneg _
        linarith
      exact div_nonneg h2 hq'.le
    linarith [hx'.1]
  · have h1 : (((abPair p).2 : ℝ) - δ) / p.2 ≤ 1 := by
      have h2 : ((abPair p).2 : ℝ) - δ ≤ (p.2 : ℝ) := by
        have h3 : ((abPair p).2 : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast hb
        linarith
      rw [div_le_iff₀ hs']
      linarith
    linarith [hx'.2]

theorem cell_disjoint {Q : ℕ} {p p' : ℕ × ℕ} (hp : p ∈ Dset Q) (hp' : p' ∈ Dset Q)
    (hne : p ≠ p') : Disjoint (cell p) (cell p') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have hxc := mem_cell_iff.mp hx
  have hxc' := mem_cell_iff.mp hx'
  obtain ⟨hq1, hs1, ha, hb, hca, hcb, hdet⟩ := cell_data hp
  obtain ⟨hq1', hs1', ha', hb', hca', hcb', hdet'⟩ := cell_data hp'
  obtain ⟨hqa, hqQ, hsa, hsQ, hsum, hcop⟩ := mem_Dset.mp hp
  obtain ⟨hqa', hqQ', hsa', hsQ', hsum', hcop'⟩ := mem_Dset.mp hp'
  have hle1 : ((abPair p').1 : ℝ) / p'.1 ≤ ((abPair p).1 : ℝ) / p.1 := by
    by_contra hcon
    have hcon' : ((abPair p).1 : ℝ) / p.1 < ((abPair p').1 : ℝ) / p'.1 := lt_of_not_ge hcon
    have hbad := sep_denom hq1 hs1 hq1' hdet hcon' (lt_trans hxc'.1 hxc.2)
    omega
  have hle2 : ((abPair p).1 : ℝ) / p.1 ≤ ((abPair p').1 : ℝ) / p'.1 := by
    by_contra hcon
    have hcon' : ((abPair p').1 : ℝ) / p'.1 < ((abPair p).1 : ℝ) / p.1 := lt_of_not_ge hcon
    have hbad := sep_denom hq1' hs1' hq1 hdet' hcon' (lt_trans hxc.1 hxc'.2)
    omega
  have hle3 : ((abPair p).2 : ℝ) / p.2 ≤ ((abPair p').2 : ℝ) / p'.2 := by
    by_contra hcon
    have hcon' : ((abPair p').2 : ℝ) / p'.2 < ((abPair p).2 : ℝ) / p.2 := lt_of_not_ge hcon
    have hbad := sep_denom hq1 hs1 hs1' hdet (lt_trans hxc.1 hxc'.2) hcon'
    omega
  have hle4 : ((abPair p').2 : ℝ) / p'.2 ≤ ((abPair p).2 : ℝ) / p.2 := by
    by_contra hcon
    have hcon' : ((abPair p).2 : ℝ) / p.2 < ((abPair p').2 : ℝ) / p'.2 := lt_of_not_ge hcon
    have hbad := sep_denom hq1' hs1' hs1 hdet' (lt_trans hxc'.1 hxc.2) hcon'
    omega
  have heq1 : ((abPair p).1 : ℝ) / p.1 = ((abPair p').1 : ℝ) / p'.1 := le_antisymm hle2 hle1
  have heq2 : ((abPair p).2 : ℝ) / p.2 = ((abPair p').2 : ℝ) / p'.2 := le_antisymm hle3 hle4
  obtain ⟨hca'', hq''⟩ := frac_unique hq1' hq1 hca' hca heq1.symm
  obtain ⟨hcb'', hs''⟩ := frac_unique hs1' hs1 hcb' hcb heq2.symm
  apply hne
  calc p = (p.1, p.2) := rfl
    _ = (p'.1, p'.2) := by rw [hq'', hs'']
    _ = p' := rfl

theorem Ac_sub {Q : ℕ} {δ : ℝ} (hQ : 1 ≤ Q) (hδ : 0 ≤ δ) {x : ℝ}
    (hx : x ∈ (Aset Q δ)ᶜ ∩ Set.Icc (0 : ℝ) 1) :
    ∃ p ∈ Dset Q, x ∈ gap δ p := by
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := hx.2
  have hx0 : (0 : ℝ) ≤ x := hxIcc.1
  have hx1 : x ≤ 1 := hxIcc.2
  have hnA : x ∉ Aset Q δ := hx.1
  have hxlt : x < 1 := by
    rcases lt_or_eq_of_le hx1 with h | h
    · exact h
    · exfalso
      apply hnA
      rw [mem_Aset]
      refine ⟨1, 1, by omega, hQ, le_rfl, by decide, ?_⟩
      rw [h]
      simpa using hδ
  obtain ⟨a, q, b, s, hq1, hqQ, hs1, hsQ, haq, hbs, hcopq, hdet, hsum, hax, hbx⟩ :=
    exists_cell Q hQ x hx0 hxlt
  have hcopbs : Nat.Coprime b s := (det_coprime hdet).2.1
  have hcopqs : Nat.Coprime q s := (det_coprime hdet).2.2
  have hnot1 : ¬ (|x - (a : ℝ) / q| ≤ δ / q) := by
    intro hcon
    apply hnA
    rw [mem_Aset]
    exact ⟨q, a, hq1, hqQ, haq, hcopq, hcon⟩
  have hnot2 : ¬ (|x - (b : ℝ) / s| ≤ δ / s) := by
    intro hcon
    apply hnA
    rw [mem_Aset]
    exact ⟨s, b, hs1, hsQ, hbs, hcopbs, hcon⟩
  have hmar1 : (((a : ℝ) + δ) / q) < x := by
    have habs : |x - (a : ℝ) / q| = x - (a : ℝ) / q := abs_of_nonneg (by linarith)
    rw [habs] at hnot1
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq1
    have hstep : ((a : ℝ) + δ) / q = (a : ℝ) / q + δ / q := by field_simp
    rw [hstep]
    linarith
  have hmar2 : x < (((b : ℝ) - δ) / s) := by
    have habs : |x - (b : ℝ) / s| = (b : ℝ) / s - x := by
      rw [abs_of_nonpos (by linarith)]
      ring
    rw [habs] at hnot2
    have hs' : (0 : ℝ) < s := by exact_mod_cast hs1
    have hstep : ((b : ℝ) - δ) / s = (b : ℝ) / s - δ / s := by field_simp
    rw [hstep]
    linarith
  have hp : (q, s) ∈ Dset Q := by
    rw [mem_Dset]
    exact ⟨hq1, hqQ, hs1, hsQ, hsum, hcopqs⟩
  have hab : abPair (q, s) = (a, b) := abPair_eq hp a b hbs hdet
  refine ⟨(q, s), hp, ?_⟩
  rw [mem_gap_iff, hab]
  exact ⟨hmar1, hmar2⟩

theorem key_eq {Q : ℕ} {δ : ℝ} (hQ : 1 ≤ Q) (hδ : 0 ≤ δ) :
    (Aset Q δ)ᶜ ∩ Set.Icc (0 : ℝ) 1 = ⋃ p ∈ Dset Q, gap δ p := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, hxp⟩ := Ac_sub hQ hδ hx
    exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, hxp⟩⟩
  · intro hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨p, hx2⟩ := hx
    rw [Set.mem_iUnion] at hx2
    obtain ⟨hp, hxp⟩ := hx2
    exact ⟨gap_sub_Ac hδ hp hxp, gap_subset_Icc hδ hp hxp⟩

theorem gap_disjoint {Q : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) :
    Set.PairwiseDisjoint (↑(Dset Q)) (gap δ) := by
  intro p hp p' hp' hne
  have hpD : p ∈ Dset Q := Finset.mem_coe.mp hp
  have hpD' : p' ∈ Dset Q := Finset.mem_coe.mp hp'
  obtain ⟨hq1, hs1, ha, hb, hca, hcb, hdet⟩ := cell_data hpD
  obtain ⟨hq1', hs1', ha', hb', hca', hcb', hdet'⟩ := cell_data hpD'
  exact (cell_disjoint hpD hpD' hne).mono (gap_subset_cell hδ hq1 hs1)
    (gap_subset_cell hδ hq1' hs1')

theorem measure_key {Q : ℕ} {δ : ℝ} (hQ : 1 ≤ Q) (hδ : 0 ≤ δ) :
    MeasureTheory.volume ((Aset Q δ)ᶜ ∩ Set.Icc (0 : ℝ) 1) =
      ∑ p ∈ Dset Q, ENNReal.ofReal ((1 - δ * ((p.1 : ℝ) + p.2)) / ((p.1 : ℝ) * p.2)) := by
  rw [key_eq hQ hδ]
  rw [MeasureTheory.measure_biUnion_finset (gap_disjoint hδ) (fun _ _ => measurableSet_Ioo)]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  obtain ⟨hq1, hs1, ha, hb, hca, hcb, hdet⟩ := cell_data hp
  have hq' : (0 : ℝ) < p.1 := by exact_mod_cast hq1
  have hs' : (0 : ℝ) < p.2 := by exact_mod_cast hs1
  have hdet' : ((abPair p).2 : ℝ) * p.1 = ((abPair p).1 : ℝ) * p.2 + 1 := by exact_mod_cast hdet
  simp only [gap, Real.volume_Ioo]
  congr 1
  have hgoal : (((abPair p).2 : ℝ) - δ) / p.2 - (((abPair p).1 : ℝ) + δ) / p.1
      = (1 - δ * ((p.1 : ℝ) + p.2)) / ((p.1 : ℝ) * p.2) := by
    field_simp
    linarith
  exact hgoal

theorem integral_key {Q : ℕ} {δ : ℝ} (hQ : 1 ≤ Q) (hδ : 0 ≤ δ) (f : ℝ → ℂ)
    (hf : MeasureTheory.IntegrableOn f (Set.Icc (0 : ℝ) 1)) :
    (∫ x in (Aset Q δ)ᶜ ∩ Set.Icc (0 : ℝ) 1, f x) = ∑ p ∈ Dset Q, ∫ x in gap δ p, f x := by
  rw [key_eq hQ hδ]
  exact MeasureTheory.integral_biUnion_finset (Dset Q)
    (fun _ _ => measurableSet_Ioo) (gap_disjoint hδ)
    (fun p hp => hf.mono_set (gap_subset_Icc hδ hp))

theorem coverage {Q : ℕ} {δ : ℝ} (hQ : 1 ≤ Q) (hδ : 0 ≤ δ) :
    Set.Icc (0 : ℝ) 1 ⊆ Aset Q δ ↔ 1 ≤ δ * ((Q : ℝ) + 1) := by
  constructor
  · intro hsub
    by_contra hcon
    have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    have hQ' : (0 : ℝ) < (Q : ℝ) := by linarith
    have hlt1 : δ * ((Q : ℝ) + 1) < 1 := lt_of_not_ge hcon
    have hδQ : δ * (Q : ℝ) < 1 - δ := by linarith
    have hsep : δ < (1 - δ) / (Q : ℝ) := (lt_div_iff₀ hQ').mpr hδQ
    obtain ⟨x, hx1, hx2⟩ := exists_between hsep
    have hp : ((1 : ℕ), Q) ∈ Dset Q := by
      rw [mem_Dset]
      exact ⟨by omega, hQ, hQ, le_rfl, by omega, Nat.coprime_one_left Q⟩
    have hdet0 : (1 : ℕ) * 1 = 0 * Q + 1 := by ring
    have hab : abPair ((1 : ℕ), Q) = (0, 1) := abPair_eq hp 0 1 hQ hdet0
    have hxg : x ∈ gap δ ((1 : ℕ), Q) := by
      rw [mem_gap_iff, hab]
      constructor
      · simpa using hx1
      · simpa using hx2
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · linarith
      · have h4 : (1 - δ) / (Q : ℝ) ≤ 1 := (div_le_iff₀ hQ').mpr (by linarith)
        linarith
    exact (gap_sub_Ac hδ hp hxg) (hsub hxIcc)
  · intro hδQ x hx
    by_contra hxA
    obtain ⟨p, hp, hxp⟩ := Ac_sub hQ hδ ⟨hxA, hx⟩
    obtain ⟨hq1, hs1, ha, hb, hca, hcb, hdet⟩ := cell_data hp
    obtain ⟨hqa, hqQ, hsa, hsQ, hsum, hcop⟩ := mem_Dset.mp hp
    have hx' := mem_gap_iff.mp hxp
    have hlt : δ * ((p.1 : ℝ) + p.2) < 1 := gap_nonempty_bound hq1 hs1 hdet hx'.1 hx'.2
    have hge : (Q : ℝ) + 1 ≤ (p.1 : ℝ) + p.2 := by
      have h5 : Q + 1 ≤ p.1 + p.2 := by omega
      exact_mod_cast h5
    have hmul : δ * ((Q : ℝ) + 1) ≤ δ * ((p.1 : ℝ) + p.2) :=
      mul_le_mul_of_nonneg_left hge hδ
    linarith

end Conjectures.Goldbach.FareyComplementQuadrature_aux

theorem Conjectures.Goldbach.FareyComplementQuadrature :
    ∀ (Q : ℕ) (δ : ℝ), 0 < Q → 0 ≤ δ →
      let A := {x : ℝ | ∃ d c : ℕ, 1 ≤ d ∧ d ≤ Q ∧ c ≤ d ∧ c.Coprime d ∧ |x-(c:ℝ)/d| ≤ δ/d}
      let D := ((Finset.Icc 1 Q) ×ˢ (Finset.Icc 1 Q)).filter (fun p => Q < p.1+p.2 ∧ p.1.Coprime p.2)
      (Set.Icc (0:ℝ) 1 ⊆ A ↔ 1 ≤ δ*((Q:ℝ)+1)) ∧
      MeasureTheory.volume (Aᶜ ∩ Set.Icc (0:ℝ) 1) =
        ∑ p ∈ D, ENNReal.ofReal ((1-δ*((p.1:ℝ)+p.2))/((p.1:ℝ)*p.2)) ∧
      ∃ ab : ℕ × ℕ → ℕ × ℕ,
        (∀ p ∈ D, (ab p).1 ≤ p.1 ∧ (ab p).2 ≤ p.2 ∧ (ab p).2*p.1 = (ab p).1*p.2+1) ∧
        ∀ f : ℝ → ℂ, MeasureTheory.IntegrableOn f (Set.Icc 0 1) →
          (∫ x in Aᶜ ∩ Set.Icc (0:ℝ) 1, f x) =
            ∑ p ∈ D, ∫ x in Set.Ioo ((((ab p).1:ℝ)+δ)/p.1) ((((ab p).2:ℝ)-δ)/p.2), f x := by
  intro Q δ hQ hδ
  have hQ1 : 1 ≤ Q := hQ
  refine ⟨?_, ?_, ?_⟩
  · exact Conjectures.Goldbach.FareyComplementQuadrature_aux.coverage hQ1 hδ
  · exact Conjectures.Goldbach.FareyComplementQuadrature_aux.measure_key hQ1 hδ
  · refine ⟨Conjectures.Goldbach.FareyComplementQuadrature_aux.abPair, ?_, ?_⟩
    · intro p hp
      exact Conjectures.Goldbach.FareyComplementQuadrature_aux.abPair_spec hp
    · intro f hf
      exact Conjectures.Goldbach.FareyComplementQuadrature_aux.integral_key hQ1 hδ f hf
