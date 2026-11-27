import Mathlib

namespace Conjectures.QuadraticPrimes.SieveDivisorRemainders_aux

def f (k : ℕ) : ℕ := 4 * k ^ 2 + 1
def roots (q : ℕ) : Finset ℕ := (Finset.range q).filter (fun r => q ∣ f r)
def rho (q : ℕ) : ℝ := ((roots q).card : ℝ)
def count (A B d : ℕ) : ℕ := ((Finset.Ioc A B).filter (fun k => d ∣ f k)).card

lemma modEq_f (d k : ℕ) : f k ≡ f (k % d) [MOD d] := by
  show 4 * k ^ 2 + 1 ≡ 4 * (k % d) ^ 2 + 1 [MOD d]
  have h : k ≡ k % d [MOD d] := (Nat.mod_modEq k d).symm
  exact (h.pow 2).mul_left 4 |>.add_right 1

lemma dvd_f_mod (d k : ℕ) : d ∣ f k ↔ d ∣ f (k % d) := by
  constructor
  · intro h
    exact Nat.modEq_zero_iff_dvd.mp ((modEq_f d k).symm.trans h.modEq_zero_nat)
  · intro h
    exact Nat.modEq_zero_iff_dvd.mp ((modEq_f d k).trans h.modEq_zero_nat)

lemma injOn_mod (m d : ℕ) (hd : 0 < d) :
    Set.InjOn (fun k : ℕ => k % d) (Finset.Ioc m (m + d)) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_Ioc] at ha hb
  have hmod : a ≡ b [MOD d] := hab
  rcases le_total a b with hle | hle
  · have hdvd : d ∣ b - a := (Nat.modEq_iff_dvd' hle).mp hmod
    have hlt : b - a < d := by omega
    have hz : b - a = 0 := by
      rcases Nat.eq_zero_or_pos (b - a) with h0 | h0
      · exact h0
      · exact absurd (Nat.le_of_dvd h0 hdvd) (by omega)
    omega
  · have hdvd : d ∣ a - b := (Nat.modEq_iff_dvd' hle).mp hmod.symm
    have hlt : a - b < d := by omega
    have hz : a - b = 0 := by
      rcases Nat.eq_zero_or_pos (a - b) with h0 | h0
      · exact h0
      · exact absurd (Nat.le_of_dvd h0 hdvd) (by omega)
    omega

lemma card_block (m d : ℕ) (hd : 0 < d) :
    ((Finset.Ioc m (m + d)).filter (fun k => d ∣ f k)).card = (roots d).card := by
  have himg : (Finset.Ioc m (m + d)).image (fun k => k % d) = Finset.range d := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (Nat.mod_lt k hd)
    · rw [Finset.card_image_of_injOn (injOn_mod m d hd), Nat.card_Ioc]
      simp
  refine Finset.card_bij (fun k _ => k % d) ?_ ?_ ?_
  · intro k hk
    obtain ⟨hkIoc, hkdvd⟩ := Finset.mem_filter.mp hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt k hd), ?_⟩
    exact (dvd_f_mod d k).mp hkdvd
  · intro a ha b hb hab
    exact injOn_mod m d hd (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab
  · intro r hr
    obtain ⟨hrlt, hrdvd⟩ := Finset.mem_filter.mp hr
    have hmem : r ∈ (Finset.Ioc m (m + d)).image (fun k => k % d) := by
      rw [himg]; exact hrlt
    obtain ⟨k, hk, hkeq⟩ := Finset.mem_image.mp hmem
    refine ⟨k, Finset.mem_filter.mpr ⟨hk, ?_⟩, hkeq⟩
    have hk' : d ∣ f (k % d) := by rw [hkeq]; exact hrdvd
    exact (dvd_f_mod d k).mpr hk'

lemma card_blocks (A d : ℕ) (hd : 0 < d) : ∀ q : ℕ,
    ((Finset.Ioc A (A + q * d)).filter (fun k => d ∣ f k)).card = q * (roots d).card := by
  intro q
  induction q with
  | zero => simp
  | succ q ih =>
    have hring : A + (q + 1) * d = (A + q * d) + d := by ring
    rw [hring]
    have hsplit : Finset.Ioc A ((A + q * d) + d)
        = Finset.Ioc A (A + q * d) ∪ Finset.Ioc (A + q * d) ((A + q * d) + d) := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_union]
      constructor
      · intro h
        by_cases h' : k ≤ A + q * d
        · exact Or.inl ⟨h.1, h'⟩
        · exact Or.inr ⟨by omega, h.2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, by omega⟩
        · exact ⟨lt_of_le_of_lt (Nat.le_add_right A (q * d)) h1, h2⟩
    have hdisj : Disjoint ((Finset.Ioc A (A + q * d)).filter (fun k => d ∣ f k))
        ((Finset.Ioc (A + q * d) ((A + q * d) + d)).filter (fun k => d ∣ f k)) := by
      refine Finset.disjoint_left.mpr ?_
      intro k hk1 hk2
      have h1 := (Finset.mem_filter.mp hk1).1
      have h2 := (Finset.mem_filter.mp hk2).1
      simp only [Finset.mem_Ioc] at h1 h2
      omega
    rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint hdisj, ih,
      card_block (A + q * d) d hd]
    ring

lemma count_bounds (A B d : ℕ) (hAB : A ≤ B) (hd : 0 < d) :
    (B - A) / d * (roots d).card ≤ count A B d ∧
      count A B d ≤ (B - A) / d * (roots d).card + (roots d).card := by
  have hdm : (B - A) / d * d + (B - A) % d = B - A := by
    rw [mul_comm]; exact Nat.div_add_mod (B - A) d
  have hle : A + (B - A) / d * d ≤ B := by omega
  have hle' : B ≤ A + (B - A) / d * d + d := by
    have := Nat.mod_lt (B - A) hd
    omega
  have hsplit : Finset.Ioc A B
      = Finset.Ioc A (A + (B - A) / d * d) ∪ Finset.Ioc (A + (B - A) / d * d) B := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_union]
    constructor
    · intro h
      by_cases h' : k ≤ A + (B - A) / d * d
      · exact Or.inl ⟨h.1, h'⟩
      · exact Or.inr ⟨by omega, h.2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, le_trans h2 hle⟩
      · exact ⟨lt_of_le_of_lt (Nat.le_add_right A _) h1, h2⟩
  have hdisj : Disjoint ((Finset.Ioc A (A + (B - A) / d * d)).filter (fun k => d ∣ f k))
      ((Finset.Ioc (A + (B - A) / d * d) B).filter (fun k => d ∣ f k)) := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk1 hk2
    have h1 := (Finset.mem_filter.mp hk1).1
    have h2 := (Finset.mem_filter.mp hk2).1
    simp only [Finset.mem_Ioc] at h1 h2
    omega
  have hcount : count A B d = (B - A) / d * (roots d).card
      + ((Finset.Ioc (A + (B - A) / d * d) B).filter (fun k => d ∣ f k)).card := by
    simp only [count]
    rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint hdisj,
      card_blocks A d hd ((B - A) / d)]
  have htail : ((Finset.Ioc (A + (B - A) / d * d) B).filter (fun k => d ∣ f k)).card
      ≤ (roots d).card := by
    have hsub : (Finset.Ioc (A + (B - A) / d * d) B).filter (fun k => d ∣ f k)
        ⊆ (Finset.Ioc (A + (B - A) / d * d) ((A + (B - A) / d * d) + d)).filter
            (fun k => d ∣ f k) :=
      Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right hle')
    calc _ ≤ ((Finset.Ioc (A + (B - A) / d * d) ((A + (B - A) / d * d) + d)).filter
            (fun k => d ∣ f k)).card := Finset.card_le_card hsub
      _ = (roots d).card := card_block _ d hd
  constructor
  · rw [hcount]; exact Nat.le_add_right _ _
  · rw [hcount]; exact Nat.add_le_add_left htail _

theorem window_remainder (A B d : ℕ) (hAB : A ≤ B) (hd : 1 ≤ d) (hodd : Odd d) :
    |(count A B d : ℝ) - ((B - A : ℕ) : ℝ) * rho d / d| ≤ rho d := by
  have hd0 : 0 < d := hd
  obtain ⟨hlo, hhi⟩ := count_bounds A B d hAB hd0
  simp only [rho]
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hlo' : (((B - A) / d : ℕ) : ℝ) * ((roots d).card : ℝ) ≤ (count A B d : ℝ) := by
    exact_mod_cast hlo
  have hhi' : (count A B d : ℝ)
      ≤ (((B - A) / d : ℕ) : ℝ) * ((roots d).card : ℝ) + ((roots d).card : ℝ) := by
    exact_mod_cast hhi
  have hdm : (B - A) / d * d + (B - A) % d = B - A := by
    rw [mul_comm]; exact Nat.div_add_mod (B - A) d
  have hkey : ((B - A : ℕ) : ℝ) * ((roots d).card : ℝ) / (d : ℝ)
      = (((B - A) / d : ℕ) : ℝ) * ((roots d).card : ℝ)
        + (((B - A) % d : ℕ) : ℝ) * ((roots d).card : ℝ) / (d : ℝ) := by
    have hdm2 : d * ((B - A) / d) + (B - A) % d = B - A := Nat.div_add_mod (B - A) d
    have hcast : ((B - A : ℕ) : ℝ)
        = (d : ℝ) * (((B - A) / d : ℕ) : ℝ) + (((B - A) % d : ℕ) : ℝ) := by
      exact_mod_cast hdm2.symm
    rw [hcast]; field_simp
  have hsdR : (((B - A) % d : ℕ) : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.mod_lt (B - A) hd0
  have hpos : (0 : ℝ) ≤ (((B - A) % d : ℕ) : ℝ) * ((roots d).card : ℝ) / (d : ℝ) := by
    positivity
  have hρ0 : (0 : ℝ) ≤ ((roots d).card : ℝ) := Nat.cast_nonneg _
  have hle : (((B - A) % d : ℕ) : ℝ) * ((roots d).card : ℝ) / (d : ℝ)
      ≤ ((roots d).card : ℝ) := by
    rw [div_le_iff₀ hdR]
    calc _ ≤ (d : ℝ) * ((roots d).card : ℝ) :=
            mul_le_mul_of_nonneg_right (le_of_lt hsdR) hρ0
      _ = ((roots d).card : ℝ) * (d : ℝ) := by ring
  rw [abs_le, hkey]
  constructor
  · linarith
  · linarith


lemma key_prime {p u v x0 : ℕ} (hp : p.Prime) (hu : p ∣ u ^ 2 + 1) (hv : p ∣ v ^ 2 + 1)
    (hx0 : p ∣ x0 ^ 2 + 1) (h : (u ≡ x0 [MOD p]) ↔ (v ≡ x0 [MOD p])) :
    u ≡ v [MOD p] := by
  have aux : ∀ w : ℕ, p ∣ w ^ 2 + 1 → (w : ZMod p) ^ 2 = -1 := by
    intro w hw
    have h1 : ((w ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hw
    push_cast at h1
    linear_combination h1
  have key : ∀ w : ℕ, p ∣ w ^ 2 + 1 →
      (w : ZMod p) = (x0 : ZMod p) ∨ (w : ZMod p) + (x0 : ZMod p) = 0 := by
    intro w hw
    have hprod : ((w : ZMod p) - (x0 : ZMod p)) * ((w : ZMod p) + (x0 : ZMod p)) = 0 := by
      linear_combination aux w hw - aux x0 hx0
    letI : Fact p.Prime := ⟨hp⟩
    rcases mul_eq_zero.mp hprod with hzero | hzero
    · left; linear_combination hzero
    · right; linear_combination hzero
  by_cases hux : u ≡ x0 [MOD p]
  · exact hux.trans (h.mp hux).symm
  · have hvx : ¬ (v ≡ x0 [MOD p]) := fun hh => hux (h.mpr hh)
    rcases key u hu with hu' | hu'
    · exact absurd ((ZMod.natCast_eq_natCast_iff u x0 p).mp hu') hux
    rcases key v hv with hv' | hv'
    · exact absurd ((ZMod.natCast_eq_natCast_iff v x0 p).mp hv') hvx
    · exact (ZMod.natCast_eq_natCast_iff u v p).mp (by linear_combination hu' - hv')

lemma dvd_of_primeFactors {d n : ℕ} (hs : Squarefree d) (hn : n ≠ 0)
    (h : ∀ p ∈ d.primeFactors, p ∣ n) : d ∣ n := by
  have hprod : (∏ p ∈ d.primeFactors, p) = d := Nat.prod_primeFactors_of_squarefree hs
  rw [← hprod]
  refine (Nat.prod_primeFactors_dvd_iff hn).mpr ?_
  intro p hp
  rw [Nat.mem_primeFactors]
  exact ⟨(Nat.mem_primeFactors.mp hp).1, h p hp, hn⟩

lemma eq_of_lt_of_dvd_sub {d x y : ℕ} (hd : 0 < d) (hx : x < d) (hy : y < d) (hxy : x ≤ y)
    (hdvd : ∀ _h : y - x ≠ 0, d ∣ y - x) : x = y := by
  by_contra hne
  have hn0 : y - x ≠ 0 := by omega
  have hpos : 0 < y - x := by omega
  have hlt : y - x < d := by omega
  exact absurd (Nat.le_of_dvd hpos (hdvd hn0)) (by omega)

lemma modEq_iff_dvd_add_sub {p d x x0 : ℕ} (hpd : p ∣ d) (hx0 : x0 ≤ d) :
    p ∣ (x + (d - x0)) ↔ x ≡ x0 [MOD p] := by
  have hxd : x + d ≡ x [MOD p] := by
    have h := (Nat.modEq_zero_iff_dvd.mpr hpd).add_left x
    simpa using h
  have hkey : x + (d - x0) + x0 = x + d := by omega
  constructor
  · intro h
    have hA : x + (d - x0) ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr h
    have hB : x + (d - x0) + x0 ≡ 0 + x0 [MOD p] := hA.add_right x0
    rw [hkey, Nat.zero_add] at hB
    exact hxd.symm.trans hB
  · intro h
    have hB : x + (d - x0) + x0 ≡ x0 [MOD p] := by
      rw [hkey]; exact hxd.trans h
    have hB' : x + (d - x0) + x0 ≡ 0 + x0 [MOD p] := by
      rw [Nat.zero_add]; exact hB
    exact Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_right_cancel' x0 hB')

theorem roots_card_le_divisors_card (d : ℕ) (hd : Odd d) (hs : Squarefree d) :
    (roots d).card ≤ (Nat.divisors d).card := by
  have hd0 : 0 < d := by
    obtain ⟨k, hk⟩ := hd; omega
  have hodd2 : Nat.gcd d 2 = 1 := hd.coprime_two_right
  set S := (Finset.range d).filter (fun x => d ∣ x ^ 2 + 1) with hSdef
  have hstep1 : (roots d).card ≤ S.card := by
    refine Finset.card_le_card_of_injOn (fun r => (2 * r) % d) ?_ ?_
    · intro r hr
      have hr' := Finset.mem_filter.mp hr
      have hrlt := Finset.mem_range.mp hr'.1
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hd0), ?_⟩
      have hfr : d ∣ (2 * r) ^ 2 + 1 := by
        have hfeq : (2 * r) ^ 2 + 1 = f r := by unfold f; ring
        rw [hfeq]; exact hr'.2
      have hmod : (2 * r) ^ 2 + 1 ≡ ((2 * r) % d) ^ 2 + 1 [MOD d] := by
        have h : 2 * r ≡ (2 * r) % d [MOD d] := (Nat.mod_modEq (2 * r) d).symm
        exact (h.pow 2).add_right 1
      exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans hfr.modEq_zero_nat)
    · intro a ha b hb hab
      have ha' := Finset.mem_filter.mp ha
      have hb' := Finset.mem_filter.mp hb
      have halt := Finset.mem_range.mp ha'.1
      have hblt := Finset.mem_range.mp hb'.1
      have hmod : 2 * a ≡ 2 * b [MOD d] := hab
      have hmod' : a ≡ b [MOD d] := Nat.ModEq.cancel_left_of_coprime hodd2 hmod
      calc a = a % d := (Nat.mod_eq_of_lt halt).symm
        _ = b % d := hmod'
        _ = b := Nat.mod_eq_of_lt hblt
  have hstep2 : S.card ≤ (Nat.divisors d).card := by
    by_cases hne : S.Nonempty
    · obtain ⟨x0, hx0⟩ := hne
      have hx0' := Finset.mem_filter.mp hx0
      have hx0lt := Finset.mem_range.mp hx0'.1
      have hx0dvd : d ∣ x0 ^ 2 + 1 := hx0'.2
      refine Finset.card_le_card_of_injOn (fun x => Nat.gcd (x + (d - x0)) d) ?_ ?_
      · intro x hx
        refine Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, ?_⟩
        omega
      · intro x hx y hy heq
        have heq' : Nat.gcd (x + (d - x0)) d = Nat.gcd (y + (d - x0)) d := heq
        have hx' := Finset.mem_filter.mp hx
        have hy' := Finset.mem_filter.mp hy
        have hxlt := Finset.mem_range.mp hx'.1
        have hylt := Finset.mem_range.mp hy'.1
        have hall : ∀ p ∈ d.primeFactors, x ≡ y [MOD p] := by
          intro p hp
          have hpp := (Nat.mem_primeFactors.mp hp).1
          have hpd := (Nat.mem_primeFactors.mp hp).2.1
          have hxdvd : p ∣ x ^ 2 + 1 := hpd.trans hx'.2
          have hydvd : p ∣ y ^ 2 + 1 := hpd.trans hy'.2
          have hx0p : p ∣ x0 ^ 2 + 1 := hpd.trans hx0dvd
          refine key_prime hpp hxdvd hydvd hx0p ?_
          have hgx : p ∣ Nat.gcd (x + (d - x0)) d ↔ p ∣ x + (d - x0) := by
            constructor
            · intro hh; exact dvd_trans hh (Nat.gcd_dvd_left _ _)
            · intro hh; exact Nat.dvd_gcd hh hpd
          have hgy : p ∣ Nat.gcd (y + (d - x0)) d ↔ p ∣ y + (d - x0) := by
            constructor
            · intro hh; exact dvd_trans hh (Nat.gcd_dvd_left _ _)
            · intro hh; exact Nat.dvd_gcd hh hpd
          have hxiff : x ≡ x0 [MOD p] ↔ p ∣ x + (d - x0) :=
            (modEq_iff_dvd_add_sub hpd (le_of_lt hx0lt)).symm
          have hyiff : y ≡ x0 [MOD p] ↔ p ∣ y + (d - x0) :=
            (modEq_iff_dvd_add_sub hpd (le_of_lt hx0lt)).symm
          rw [hxiff, hyiff, ← hgx, ← hgy, heq']
        rcases le_total x y with hxy | hxy
        · refine eq_of_lt_of_dvd_sub hd0 hxlt hylt hxy ?_
          intro hn0
          refine dvd_of_primeFactors hs hn0 ?_
          intro p hp
          exact (Nat.modEq_iff_dvd' hxy).mp (hall p hp)
        · refine (eq_of_lt_of_dvd_sub hd0 hylt hxlt hxy ?_).symm
          intro hn0
          refine dvd_of_primeFactors hs hn0 ?_
          intro p hp
          exact (Nat.modEq_iff_dvd' hxy).mp (hall p hp).symm
    · have hSe : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [hSe, Finset.card_empty]
      exact Nat.zero_le _
  exact hstep1.trans hstep2

theorem divisor_sum_bound (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, ((Nat.divisors d).card : ℝ)) ≤ (D : ℝ) * (1 + Real.log D) := by
  have hIoc : ∀ n : ℕ, Finset.Ioc 0 n = Finset.Icc 1 n := by
    intro n
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hcard : ∀ d ∈ Finset.Icc 1 D, (Nat.divisors d).card
      = ((Finset.Icc 1 D).filter (fun a => a ∣ d)).card := by
    intro d hd
    have hd' := Finset.mem_Icc.mp hd
    congr 1
    ext a
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨had, hd0⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos had (by omega),
        le_trans (Nat.le_of_dvd (by omega) had) hd'.2⟩, had⟩
    · rintro ⟨_, had⟩
      exact ⟨had, by omega⟩
  have h1 : ∀ d : ℕ, ((Finset.Icc 1 D).filter (fun a => a ∣ d)).card
      = ∑ a ∈ Finset.Icc 1 D, (if a ∣ d then (1 : ℕ) else 0) := by
    intro d
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have h2 : ∀ a : ℕ, (∑ d ∈ Finset.Icc 1 D, (if a ∣ d then (1 : ℕ) else 0))
      = ((Finset.Icc 1 D).filter (fun d => a ∣ d)).card := by
    intro a
    rw [← Finset.sum_filter, Finset.card_eq_sum_ones]
  have h5 : ∀ a ∈ Finset.Icc 1 D,
      ((Finset.Icc 1 D).filter (fun d => a ∣ d)).card = D / a := by
    intro a ha
    have ha1 : 0 < a := (Finset.mem_Icc.mp ha).1
    rw [← hIoc D]
    exact Nat.Ioc_filter_dvd_card_eq_div D a
  have hnat : (∑ d ∈ Finset.Icc 1 D, (Nat.divisors d).card)
      ≤ ∑ a ∈ Finset.Icc 1 D, (D / a) := by
    calc (∑ d ∈ Finset.Icc 1 D, (Nat.divisors d).card)
        = ∑ d ∈ Finset.Icc 1 D, ((Finset.Icc 1 D).filter (fun a => a ∣ d)).card := by
          apply Finset.sum_congr rfl; intro d hd; rw [hcard d hd]
      _ = ∑ d ∈ Finset.Icc 1 D, ∑ a ∈ Finset.Icc 1 D, (if a ∣ d then (1 : ℕ) else 0) := by
          apply Finset.sum_congr rfl; intro d hd; rw [h1 d]
      _ = ∑ a ∈ Finset.Icc 1 D, ∑ d ∈ Finset.Icc 1 D, (if a ∣ d then (1 : ℕ) else 0) :=
          Finset.sum_comm
      _ = ∑ a ∈ Finset.Icc 1 D, ((Finset.Icc 1 D).filter (fun d => a ∣ d)).card := by
          apply Finset.sum_congr rfl; intro a ha; rw [h2 a]
      _ ≤ ∑ a ∈ Finset.Icc 1 D, (D / a) := by
          refine le_of_eq (Finset.sum_congr rfl ?_)
          intro a ha; rw [h5 a ha]
  have hdiv : ∀ a ∈ Finset.Icc 1 D, ((D / a : ℕ) : ℝ) ≤ (D : ℝ) / a := by
    intro a ha
    have ha1 : 0 < a := (Finset.mem_Icc.mp ha).1
    have hle : (D / a) * a ≤ D := Nat.div_mul_le_self D a
    have hcast : ((D / a : ℕ) : ℝ) * (a : ℝ) ≤ (D : ℝ) := by exact_mod_cast hle
    rw [le_div_iff₀ (by exact_mod_cast ha1)]
    linarith
  have hharm : (∑ a ∈ Finset.Icc 1 D, ((a : ℝ))⁻¹) ≤ 1 + Real.log D := by
    have h := harmonic_le_one_add_log D
    simpa [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using h
  calc (∑ d ∈ Finset.Icc 1 D, ((Nat.divisors d).card : ℝ))
      = ((∑ d ∈ Finset.Icc 1 D, (Nat.divisors d).card : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ ((∑ a ∈ Finset.Icc 1 D, (D / a) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = ∑ a ∈ Finset.Icc 1 D, ((D / a : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ ∑ a ∈ Finset.Icc 1 D, (D : ℝ) / a := Finset.sum_le_sum hdiv
    _ = (D : ℝ) * ∑ a ∈ Finset.Icc 1 D, ((a : ℝ))⁻¹ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i hi => by rw [div_eq_mul_inv])
    _ ≤ (D : ℝ) * (1 + Real.log D) :=
        mul_le_mul_of_nonneg_left hharm (Nat.cast_nonneg D)

theorem main_bound (A B D : ℕ) (hAB : A ≤ B) (hD : 1 ≤ D) :
    (∑ d ∈ (Finset.Icc 1 D).filter (fun d => Odd d ∧ Squarefree d),
      |(count A B d : ℝ) - ((B - A : ℕ) : ℝ) * rho d / d|) ≤ (D : ℝ) * (1 + Real.log D) := by
  have h1 : (∑ d ∈ (Finset.Icc 1 D).filter (fun d => Odd d ∧ Squarefree d),
      |(count A B d : ℝ) - ((B - A : ℕ) : ℝ) * rho d / d|)
      ≤ ∑ d ∈ (Finset.Icc 1 D).filter (fun d => Odd d ∧ Squarefree d),
          ((Nat.divisors d).card : ℝ) := by
    refine Finset.sum_le_sum fun d hd => ?_
    have hd' := Finset.mem_filter.mp hd
    have hmem := Finset.mem_Icc.mp hd'.1
    calc |(count A B d : ℝ) - ((B - A : ℕ) : ℝ) * rho d / d| ≤ rho d :=
           window_remainder A B d hAB hmem.1 hd'.2.1
      _ = ((roots d).card : ℝ) := rfl
      _ ≤ ((Nat.divisors d).card : ℝ) := by
            exact_mod_cast roots_card_le_divisors_card d hd'.2.1 hd'.2.2
  have h2 : (∑ d ∈ (Finset.Icc 1 D).filter (fun d => Odd d ∧ Squarefree d),
      ((Nat.divisors d).card : ℝ)) ≤ ∑ d ∈ Finset.Icc 1 D, ((Nat.divisors d).card : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro i hi hni
    positivity
  exact h1.trans (h2.trans (divisor_sum_bound D))

end Conjectures.QuadraticPrimes.SieveDivisorRemainders_aux

theorem Conjectures.QuadraticPrimes.SieveDivisorRemainders :
    let f := fun k : ℕ => 4*k^2+1; let roots := fun (q : ℕ) => (Finset.range q).filter (fun r => q ∣ f r); let rho := fun q : ℕ => ((roots q).card : ℝ); let count := fun A B d : ℕ => ((Finset.Ioc A B).filter (fun k => d ∣ f k)).card;
    ∀ A B D : ℕ, A≤B → 1≤D →
      (∑ d ∈ (Finset.Icc 1 D).filter (fun d => Odd d ∧ Squarefree d),
        |(count A B d : ℝ) - ((B-A : ℕ) : ℝ) * rho d / d|) ≤
        (D : ℝ) * (1 + Real.log D) := by
  dsimp only
  intro A B D hAB hD
  exact Conjectures.QuadraticPrimes.SieveDivisorRemainders_aux.main_bound A B D hAB hD
