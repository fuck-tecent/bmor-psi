import Mathlib
import Conjectures.QuadraticPrimes.SieveDivisorRemainders
import Conjectures.QuadraticPrimes.SieveMobiusCount

/-!
# QP-0078: Initial dimension-one lower-bound sieve for `4 * k^2 + 1`

We prove `Conjectures.QuadraticPrimes.SieveInitialLowerBound` via Brun's geometric-interval
combinatorial lower sieve with square-root cutoffs `cut z (j + 1) = Nat.sqrt (cut z j)`,
cutoff exponent `U = 24`, and the divisor remainder bound `SieveDivisorRemainders`.
-/

open scoped BigOperators
open Finset

namespace Conjectures.QuadraticPrimes.SieveInitialLowerBound_aux

private def f (k : ℕ) : ℕ := 4 * k ^ 2 + 1
private def block (x : ℕ) : Finset ℕ := Finset.Ioc (x / 2) x
private def primes (z : ℕ) : Finset ℕ := (Finset.Icc 3 z).filter (fun p => Nat.Prime p)
private def split (z : ℕ) : Finset ℕ := (Finset.Icc 5 z).filter (fun p => Nat.Prime p ∧ p % 4 = 1)
private def wheel (z : ℕ) : ℕ := ∏ p ∈ primes z, p
private def splitWheel (z : ℕ) : ℕ := ∏ p ∈ split z, p
private def rough (x z : ℕ) : Finset ℕ := (block x).filter (fun k => Nat.Coprime (f k) (wheel z))
private noncomputable def localProd (z : ℕ) : ℝ := ∏ p ∈ split z, (1 - 2 / (p : ℝ))
private def roots (q : ℕ) : Finset ℕ := (Finset.range q).filter (fun r => q ∣ f r)
private noncomputable def rho (q : ℕ) : ℝ := ((roots q).card : ℝ)
private def count (A B d : ℕ) : ℕ := ((Finset.Ioc A B).filter (fun k => d ∣ f k)).card

/-! ### 1. Inert primes, CRT multiplicativity, and root counts -/

private lemma f_odd (k : ℕ) : Odd (f k) := by
  refine ⟨2 * k ^ 2, ?_⟩
  unfold f; ring

private lemma not_dvd_f_of_mod_four_eq_three {p k : ℕ} (hp : p.Prime) (hmod : p % 4 = 3) :
    ¬ p ∣ f k := by
  intro hdvd
  let : Fact p.Prime := ⟨hp⟩
  have h1 : ((4 * k ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  have hsq : (((2 * k : ℕ) : ZMod p)) ^ 2 = -1 := by
    push_cast at h1 ⊢
    linear_combination h1
  have hex : IsSquare (-1 : ZMod p) := ⟨((2 * k : ℕ) : ZMod p), by rw [← sq]; exact hsq.symm⟩
  exact ((ZMod.exists_sq_eq_neg_one_iff (p := p)).mp hex) hmod

private lemma coprime_wheel_iff_coprime_splitWheel (k z : ℕ) :
    Nat.Coprime (f k) (wheel z) ↔ Nat.Coprime (f k) (splitWheel z) := by
  unfold wheel splitWheel
  rw [Nat.coprime_prod_right_iff, Nat.coprime_prod_right_iff]
  constructor
  · intro h p hp
    apply h p
    have hp' := Finset.mem_filter.mp hp
    have hbounds := Finset.mem_Icc.mp hp'.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hbounds.2⟩, hp'.2.1⟩
  · intro h p hp
    have hp' := Finset.mem_filter.mp hp
    have hbounds := Finset.mem_Icc.mp hp'.1
    have hpp : p.Prime := hp'.2
    have hp2 : p ≠ 2 := by omega
    have hodd : p % 2 = 1 := hpp.eq_two_or_odd.resolve_left hp2
    have hcases : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases hcases with h1 | h3
    · have hp5 : 5 ≤ p := by
        by_contra hlt
        have hp_le : p ≤ 4 := by omega
        interval_cases p <;> contradiction
      exact h p (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp5, hbounds.2⟩, hpp, h1⟩)
    · exact (hpp.coprime_iff_not_dvd.mpr (not_dvd_f_of_mod_four_eq_three hpp h3)).symm

private lemma split_mono {a b : ℕ} (hab : a ≤ b) : split a ⊆ split b := by
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hb := Finset.mem_Icc.mp hp'.1
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hb.1, hb.2.trans hab⟩, hp'.2⟩

private lemma splitWheel_pos (z : ℕ) : 0 < splitWheel z := by
  unfold splitWheel
  refine Finset.prod_pos ?_
  intro p hp
  have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  omega

private lemma coprime_splitWheel_iff_forall_not_dvd (k z : ℕ) :
    Nat.Coprime (f k) (splitWheel z) ↔ ∀ p ∈ split z, ¬ p ∣ f k := by
  unfold splitWheel
  rw [Nat.coprime_prod_right_iff]
  constructor
  · intro h p hp
    have hpp := (Finset.mem_filter.mp hp).2.1
    exact hpp.coprime_iff_not_dvd.mp (h p hp).symm
  · intro h p hp
    have hpp := (Finset.mem_filter.mp hp).2.1
    exact (hpp.coprime_iff_not_dvd.mpr (h p hp)).symm

private lemma prod_primes_dvd_iff' {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime) (m : ℕ) :
    (∏ p ∈ A, p) ∣ m ↔ ∀ p ∈ A, p ∣ m := by
  induction A using Finset.induction with
  | empty => simp
  | @insert a s has ih =>
      have ha : a.Prime := hA a (Finset.mem_insert_self a s)
      have hs : ∀ p ∈ s, p.Prime := fun p hp => hA p (Finset.mem_insert_of_mem hp)
      have hcop : Nat.Coprime a (∏ p ∈ s, p) := by
        rw [Nat.coprime_prod_right_iff]
        intro p hp
        exact (Nat.coprime_primes ha (hs p hp)).mpr (fun heq => has (heq ▸ hp))
      rw [Finset.prod_insert has]
      constructor
      · intro hdvd p hp
        rcases Finset.mem_insert.mp hp with rfl | hps
        · exact dvd_trans (dvd_mul_right _ _) hdvd
        · exact (ih hs).mp (dvd_trans (dvd_mul_left _ _) hdvd) p hps
      · intro h
        exact hcop.mul_dvd_of_dvd_of_dvd (h a (Finset.mem_insert_self a s))
          ((ih hs).mpr (fun p hp => h p (Finset.mem_insert_of_mem hp)))

private lemma prod_primes_primeFactors {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime) :
    (∏ p ∈ A, p).primeFactors = A := by
  induction A using Finset.induction with
  | empty => simp
  | @insert a s has ih =>
      have ha : a.Prime := hA a (Finset.mem_insert_self a s)
      have hs : ∀ p ∈ s, p.Prime := fun p hp => hA p (Finset.mem_insert_of_mem hp)
      have hs_pos : ∏ p ∈ s, p ≠ 0 := (Finset.prod_pos (fun p hp => (hs p hp).pos)).ne'
      rw [Finset.prod_insert has, Nat.primeFactors_mul ha.ne_zero hs_pos,
        ha.primeFactors, ih hs]
      ext p; simp

private lemma prod_primes_odd {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime ∧ 3 ≤ p) :
    Odd (∏ p ∈ A, p) := by
  induction A using Finset.induction with
  | empty => simp
  | @insert a s has ih =>
      have ha := hA a (Finset.mem_insert_self a s)
      have hs : ∀ p ∈ s, p.Prime ∧ 3 ≤ p := fun p hp => hA p (Finset.mem_insert_of_mem hp)
      have ha_odd : Odd a := ha.1.odd_iff.mpr (by omega)
      rw [Finset.prod_insert has]
      exact ha_odd.mul (ih hs)

private lemma prod_primes_squarefree {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime) :
    Squarefree (∏ p ∈ A, p) := by
  induction A using Finset.induction with
  | empty => simp
  | @insert a s has ih =>
      have ha : a.Prime := hA a (Finset.mem_insert_self a s)
      have hs : ∀ p ∈ s, p.Prime := fun p hp => hA p (Finset.mem_insert_of_mem hp)
      have hcop : Nat.Coprime a (∏ p ∈ s, p) := by
        rw [Nat.coprime_prod_right_iff]
        intro p hp
        exact (Nat.coprime_primes ha (hs p hp)).mpr (fun heq => has (heq ▸ hp))
      rw [Finset.prod_insert has, Nat.squarefree_mul hcop]
      exact ⟨ha.squarefree, ih hs⟩

private lemma roots_prime_card_eq_two {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 1) :
    (roots p).card = 2 := by
  let : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    omega
  have hne2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h0)
    have hle : p ≤ 2 := Nat.le_of_dvd (by omega) hd
    omega
  have hsq : IsSquare (-1 : ZMod p) :=
    (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr (by omega)
  obtain ⟨x0, hx0'⟩ := hsq
  have hx0 : x0 ^ 2 = -1 := by rw [sq, ← hx0']
  have hx0_ne : x0 ≠ -x0 := by
    intro heq
    have h2x : (2 : ZMod p) * x0 = 0 := by linear_combination heq
    rcases mul_eq_zero.mp h2x with h20 | hx0z
    · exact hne2 h20
    · rw [hx0z, zero_pow (by omega)] at hx0
      exact zero_ne_one (by linear_combination -hx0 : (0 : ZMod p) = 1)
  have hfilt : (Finset.univ.filter (fun r : ZMod p => (4 : ZMod p) * r ^ 2 + 1 = 0)).card = 2 := by
    have heqset : Finset.univ.filter (fun r : ZMod p => (4 : ZMod p) * r ^ 2 + 1 = 0)
        = {x0 * (2 : ZMod p)⁻¹, (-x0) * (2 : ZMod p)⁻¹} := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro hr
        have hfac : ((2 : ZMod p) * r - x0) * ((2 : ZMod p) * r + x0) = 0 := by
          linear_combination hr - hx0
        rcases mul_eq_zero.mp hfac with hL | hR
        · left
          have h2r : (2 : ZMod p) * r = x0 := by linear_combination hL
          calc r = ((2 : ZMod p) * r) * (2 : ZMod p)⁻¹ := by
                rw [mul_assoc, mul_comm r _, ← mul_assoc, mul_inv_cancel₀ hne2, one_mul]
            _ = x0 * (2 : ZMod p)⁻¹ := by rw [h2r]
        · right
          have h2r : (2 : ZMod p) * r = -x0 := by linear_combination hR
          calc r = ((2 : ZMod p) * r) * (2 : ZMod p)⁻¹ := by
                rw [mul_assoc, mul_comm r _, ← mul_assoc, mul_inv_cancel₀ hne2, one_mul]
            _ = (-x0) * (2 : ZMod p)⁻¹ := by rw [h2r]
      · rintro (rfl | rfl)
        · have h2inv : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ hne2
          calc (4 : ZMod p) * (x0 * (2 : ZMod p)⁻¹) ^ 2 + 1
              = x0 ^ 2 * ((2 : ZMod p) * (2 : ZMod p)⁻¹) ^ 2 + 1 := by ring
            _ = (-1) * 1 ^ 2 + 1 := by rw [hx0, h2inv]
            _ = 0 := by ring
        · have h2inv : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ hne2
          calc (4 : ZMod p) * ((-x0) * (2 : ZMod p)⁻¹) ^ 2 + 1
              = x0 ^ 2 * ((2 : ZMod p) * (2 : ZMod p)⁻¹) ^ 2 + 1 := by ring
            _ = (-1) * 1 ^ 2 + 1 := by rw [hx0, h2inv]
            _ = 0 := by ring
    rw [heqset, Finset.card_pair]
    intro heq
    apply hx0_ne
    calc x0 = (x0 * (2 : ZMod p)⁻¹) * 2 := by rw [mul_assoc, inv_mul_cancel₀ hne2, mul_one]
      _ = ((-x0) * (2 : ZMod p)⁻¹) * 2 := by rw [heq]
      _ = -x0 := by rw [mul_assoc, inv_mul_cancel₀ hne2, mul_one]
  rw [← hfilt]
  unfold roots f
  refine Finset.card_bij (fun r _ => (r : ZMod p)) ?_ ?_ ?_
  · intro r hr
    have hr' := (Finset.mem_filter.mp hr).2
    have h0 : ((4 * r ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hr'
    simpa [Finset.mem_filter] using h0
  · intro a ha b hb hab
    have halt := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have hblt := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    have hmodEq := (ZMod.natCast_eq_natCast_iff a b p).mp hab
    calc a = a % p := (Nat.mod_eq_of_lt halt).symm
      _ = b % p := hmodEq
      _ = b := Nat.mod_eq_of_lt hblt
  · intro r hr
    have hr' : (4 : ZMod p) * r ^ 2 + 1 = 0 := (Finset.mem_filter.mp hr).2
    refine ⟨r.val, ?_, ZMod.natCast_zmod_val r⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt r), ?_⟩
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    simpa [ZMod.natCast_zmod_val] using hr'

private lemma roots_mul_card {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) :
    (roots (a * b)).card = (roots a).card * (roots b).card := by
  letI : NeZero a := ⟨ha.ne'⟩
  letI : NeZero b := ⟨hb.ne'⟩
  letI : NeZero (a * b) := ⟨(Nat.mul_pos ha hb).ne'⟩
  have h1 : (roots (a * b)).card =
      (Finset.univ.filter (fun r : ZMod (a * b) => (4 : ZMod (a * b)) * r ^ 2 + 1 = 0)).card := by
    unfold roots f
    refine Finset.card_bij (fun r _ => (r : ZMod (a * b))) ?_ ?_ ?_
    · intro r hr
      have h0 : ((4 * r ^ 2 + 1 : ℕ) : ZMod (a * b)) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr (Finset.mem_filter.mp hr).2
      simpa [Finset.mem_filter] using h0
    · intro x hx y hy hxy
      have hxlt := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
      have hylt := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
      have hm := (ZMod.natCast_eq_natCast_iff x y (a * b)).mp hxy
      calc x = x % (a * b) := (Nat.mod_eq_of_lt hxlt).symm
        _ = y % (a * b) := hm
        _ = y := Nat.mod_eq_of_lt hylt
    · intro r hr
      refine ⟨r.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt r), ?_⟩,
        ZMod.natCast_zmod_val r⟩
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      simpa [ZMod.natCast_zmod_val] using (Finset.mem_filter.mp hr).2
  have h2a : (roots a).card =
      (Finset.univ.filter (fun r : ZMod a => (4 : ZMod a) * r ^ 2 + 1 = 0)).card := by
    unfold roots f
    refine Finset.card_bij (fun r _ => (r : ZMod a)) ?_ ?_ ?_
    · intro r hr
      have h0 : ((4 * r ^ 2 + 1 : ℕ) : ZMod a) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr (Finset.mem_filter.mp hr).2
      simpa [Finset.mem_filter] using h0
    · intro x hx y hy hxy
      have hxlt := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
      have hylt := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
      have hm := (ZMod.natCast_eq_natCast_iff x y a).mp hxy
      calc x = x % a := (Nat.mod_eq_of_lt hxlt).symm
        _ = y % a := hm
        _ = y := Nat.mod_eq_of_lt hylt
    · intro r hr
      refine ⟨r.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt r), ?_⟩,
        ZMod.natCast_zmod_val r⟩
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      simpa [ZMod.natCast_zmod_val] using (Finset.mem_filter.mp hr).2
  have h2b : (roots b).card =
      (Finset.univ.filter (fun r : ZMod b => (4 : ZMod b) * r ^ 2 + 1 = 0)).card := by
    unfold roots f
    refine Finset.card_bij (fun r _ => (r : ZMod b)) ?_ ?_ ?_
    · intro r hr
      have h0 : ((4 * r ^ 2 + 1 : ℕ) : ZMod b) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr (Finset.mem_filter.mp hr).2
      simpa [Finset.mem_filter] using h0
    · intro x hx y hy hxy
      have hxlt := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
      have hylt := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
      have hm := (ZMod.natCast_eq_natCast_iff x y b).mp hxy
      calc x = x % b := (Nat.mod_eq_of_lt hxlt).symm
        _ = y % b := hm
        _ = y := Nat.mod_eq_of_lt hylt
    · intro r hr
      refine ⟨r.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt r), ?_⟩,
        ZMod.natCast_zmod_val r⟩
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      simpa [ZMod.natCast_zmod_val] using (Finset.mem_filter.mp hr).2
  rw [h1, h2a, h2b, ← Finset.card_product]
  let e := ZMod.chineseRemainder hab
  refine Finset.card_bij (fun r _ => e r) ?_ ?_ ?_
  · intro r hr
    have hr' : ((4 : ℕ) : ZMod (a * b)) * r ^ 2 + 1 = 0 := by
      simpa using (Finset.mem_filter.mp hr).2
    have hpair : e (((4 : ℕ) : ZMod (a * b)) * r ^ 2 + 1) = (0, 0) := by
      rw [hr', map_zero]; rfl
    have he1 : (4 : ZMod a) * (e r).1 ^ 2 + 1 = 0 := by
      have := congrArg Prod.fst hpair
      simpa [map_add, map_mul, map_pow, map_one, map_ofNat] using this
    have he2 : (4 : ZMod b) * (e r).2 ^ 2 + 1 = 0 := by
      have := congrArg Prod.snd hpair
      simpa [map_add, map_mul, map_pow, map_one, map_ofNat] using this
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, he1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, he2⟩⟩
  · intro r₁ _ r₂ _ h
    exact e.injective h
  · intro p hp
    rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
    have h1' : ((4 : ℕ) : ZMod a) * p.1 ^ 2 + 1 = 0 := by simpa using (Finset.mem_filter.mp hp1).2
    have h2' : ((4 : ℕ) : ZMod b) * p.2 ^ 2 + 1 = 0 := by simpa using (Finset.mem_filter.mp hp2).2
    refine ⟨e.symm p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, e.apply_symm_apply p⟩
    apply e.injective
    rw [map_zero]
    ext
    · simpa [map_add, map_mul, map_pow, map_one, map_ofNat, e.apply_symm_apply p] using h1'
    · simpa [map_add, map_mul, map_pow, map_one, map_ofNat, e.apply_symm_apply p] using h2'

private lemma rho_prod_split {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime ∧ p % 4 = 1) :
    rho (∏ p ∈ A, p) / ((∏ p ∈ A, p : ℕ) : ℝ) = ∏ p ∈ A, (2 / (p : ℝ)) := by
  induction A using Finset.induction with
  | empty =>
      simp only [Finset.prod_empty, Nat.cast_one, div_one]
      have hroot1 : roots 1 = {0} := by
        ext r
        simp [roots]
      simp [rho, hroot1]
  | @insert a s has ih =>
      have ha := hA a (Finset.mem_insert_self a s)
      have hs : ∀ p ∈ s, p.Prime ∧ p % 4 = 1 := fun p hp => hA p (Finset.mem_insert_of_mem hp)
      have hcop : Nat.Coprime a (∏ p ∈ s, p) := by
        rw [Nat.coprime_prod_right_iff]
        intro p hp
        exact (Nat.coprime_primes ha.1 (hs p hp).1).mpr (fun heq => has (heq ▸ hp))
      have ha_pos : 0 < a := ha.1.pos
      have hs_pos : 0 < ∏ p ∈ s, p := Finset.prod_pos (fun p hp => (hs p hp).1.pos)
      rw [Finset.prod_insert has, Finset.prod_insert has]
      simp only [rho]
      rw [roots_mul_card hcop ha_pos hs_pos, roots_prime_card_eq_two ha.1 ha.2]
      push_cast
      have ih' := ih hs
      simp only [rho] at ih'
      rw [← ih', Nat.cast_prod]
      ring

/-! ### 2. Combinatorial Bonferroni and Brun Sieve Inequalities -/

private lemma bonferroni_binomial_sum (M n : ℕ) :
    ∑ j ∈ Finset.range (M + 1), (-1 : ℤ) ^ j * (n.choose j : ℤ) =
      if n = 0 then 1 else (-1 : ℤ) ^ M * ((n - 1).choose M : ℤ) := by
  cases n with
  | zero =>
      simp only [↓reduceIte]
      induction M with
      | zero => simp
      | succ M ih =>
          rw [Finset.sum_range_succ, ih]
          simp [Nat.choose_zero_succ]
  | succ m =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      induction M with
      | zero => simp
      | succ M ih =>
          rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ m M]
          push_cast
          ring

private noncomputable def truncSum (T : Finset ℕ) (M m : ℕ) : ℝ :=
  ∑ A ∈ T.powerset.filter (fun A => A.card ≤ M),
    if (∏ p ∈ A, p) ∣ m then (-1 : ℝ) ^ A.card else 0

private noncomputable def indCoprime (T : Finset ℕ) (m : ℕ) : ℝ :=
  if T.filter (fun p => p ∣ m) = ∅ then 1 else 0

private lemma truncSum_eq_binomial {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) (M m : ℕ) :
    truncSum T M m =
      ∑ j ∈ Finset.range (M + 1),
        (-1 : ℝ) ^ j * (((T.filter (fun p => p ∣ m)).card.choose j : ℕ) : ℝ) := by
  unfold truncSum
  set F := T.filter (fun p => p ∣ m)
  calc ∑ A ∈ T.powerset.filter (fun A => A.card ≤ M),
        (if (∏ p ∈ A, p) ∣ m then (-1 : ℝ) ^ A.card else 0)
      = ∑ A ∈ T.powerset.filter (fun A => A.card ≤ M) with (∏ p ∈ A, p) ∣ m,
          (-1 : ℝ) ^ A.card := by rw [← Finset.sum_filter]
    _ = ∑ A ∈ F.powerset.filter (fun A => A.card ≤ M), (-1 : ℝ) ^ A.card := by
          congr 1
          ext A
          simp only [Finset.mem_filter, Finset.mem_powerset, F]
          constructor
          · rintro ⟨⟨hAT, hcard⟩, hdvd⟩
            have hdvd' := (prod_primes_dvd_iff' (fun p hp => hT p (hAT hp)) m).mp hdvd
            exact ⟨fun p hp => Finset.mem_filter.mpr ⟨hAT hp, hdvd' p hp⟩, hcard⟩
          · rintro ⟨hAF, hcard⟩
            have hAT : A ⊆ T := fun p hp => (Finset.mem_filter.mp (hAF hp)).1
            have hdvd : (∏ p ∈ A, p) ∣ m :=
              (prod_primes_dvd_iff' (fun p hp => hT p (hAT hp)) m).mpr
                (fun p hp => (Finset.mem_filter.mp (hAF hp)).2)
            exact ⟨⟨hAT, hcard⟩, hdvd⟩
    _ = ∑ j ∈ Finset.range (M + 1),
          ∑ _A ∈ F.powersetCard j, (-1 : ℝ) ^ j := by
          have hunion : F.powerset.filter (fun A => A.card ≤ M) =
              (Finset.range (M + 1)).biUnion (fun j => F.powersetCard j) := by
            ext A
            simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion,
              Finset.mem_range, Finset.mem_powersetCard]
            constructor
            · rintro ⟨hAF, hcard⟩
              exact ⟨A.card, Nat.lt_succ_of_le hcard, hAF, rfl⟩
            · rintro ⟨j, hj, hAF, rfl⟩
              exact ⟨hAF, Nat.lt_succ_iff.mp hj⟩
          rw [hunion, Finset.sum_biUnion]
          · apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro A hA
            rw [(Finset.mem_powersetCard.mp hA).2]
          · intro i _ j _ hij
            refine Finset.disjoint_left.mpr ?_
            intro A hi hj
            have h1 := (Finset.mem_powersetCard.mp hi).2
            have h2 := (Finset.mem_powersetCard.mp hj).2
            omega
    _ = ∑ j ∈ Finset.range (M + 1), (-1 : ℝ) ^ j * ((F.card.choose j : ℕ) : ℝ) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, mul_comm]

private lemma truncSum_closed {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) (M m : ℕ) :
    truncSum T M m =
      if (T.filter (fun p => p ∣ m)).card = 0 then 1
      else (-1 : ℝ) ^ M * ((((T.filter (fun p => p ∣ m)).card - 1).choose M : ℕ) : ℝ) := by
  rw [truncSum_eq_binomial hT M m]
  have hz := bonferroni_binomial_sum M (T.filter (fun p => p ∣ m)).card
  have hr : ((∑ j ∈ Finset.range (M + 1),
      (-1 : ℤ) ^ j * (((T.filter (fun p => p ∣ m)).card.choose j : ℕ) : ℤ) : ℤ) : ℝ)
      = ((if (T.filter (fun p => p ∣ m)).card = 0 then (1 : ℤ)
          else (-1 : ℤ) ^ M *
            ((((T.filter (fun p => p ∣ m)).card - 1).choose M : ℕ) : ℤ) : ℤ) : ℝ) :=
    congrArg (Int.cast : ℤ → ℝ) hz
  push_cast at hr
  split_ifs at hr ⊢ with h0
  · exact hr
  · exact hr

private lemma indCoprime_nonneg (T : Finset ℕ) (m : ℕ) : 0 ≤ indCoprime T m := by
  unfold indCoprime; split_ifs <;> norm_num

private lemma indCoprime_le_truncSum_even {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) (b m : ℕ) :
    indCoprime T m ≤ truncSum T (2 * b) m := by
  unfold indCoprime
  rw [truncSum_closed hT]
  by_cases hemp : T.filter (fun p => p ∣ m) = ∅
  · simp [hemp]
  · have hne0 : (T.filter (fun p => p ∣ m)).card ≠ 0 := by
      rwa [Finset.card_ne_zero, Finset.nonempty_iff_ne_empty]
    rw [if_neg hemp, if_neg hne0]
    have hpow : (-1 : ℝ) ^ (2 * b) = 1 := by simp [pow_mul]
    rw [hpow]
    positivity

private lemma truncSum_odd_le_indCoprime {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime)
    {b : ℕ} (hb : 1 ≤ b) (m : ℕ) :
    truncSum T (2 * b - 1) m ≤ indCoprime T m := by
  unfold indCoprime
  rw [truncSum_closed hT]
  by_cases hemp : T.filter (fun p => p ∣ m) = ∅
  · simp [hemp]
  · have hne0 : (T.filter (fun p => p ∣ m)).card ≠ 0 := by
      rwa [Finset.card_ne_zero, Finset.nonempty_iff_ne_empty]
    rw [if_neg hemp, if_neg hne0]
    have hodd : Odd (2 * b - 1) := ⟨b - 1, by omega⟩
    rw [hodd.neg_one_pow]
    have hnonneg : (0 : ℝ) ≤ ((((T.filter (fun p => p ∣ m)).card - 1).choose (2 * b - 1) : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    linarith

private lemma truncSum_full_eq_indCoprime {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) (m : ℕ) :
    truncSum T T.card m = indCoprime T m := by
  rw [truncSum_closed hT, indCoprime]
  by_cases hemp : T.filter (fun p => p ∣ m) = ∅
  · simp [hemp]
  · have hne0 : (T.filter (fun p => p ∣ m)).card ≠ 0 := by
      rwa [Finset.card_ne_zero, Finset.nonempty_iff_ne_empty]
    rw [if_neg hemp, if_neg hne0]
    have hlt : (T.filter (fun p => p ∣ m)).card - 1 < T.card := by
      have hle : (T.filter (fun p => p ∣ m)).card ≤ T.card := Finset.card_filter_le _ _
      have hpos : 0 < (T.filter (fun p => p ∣ m)).card :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hemp)
      omega
    rw [Nat.choose_eq_zero_of_lt hlt]
    simp

private lemma truncSum_even_sub_odd (T : Finset ℕ) {b : ℕ} (hb : 1 ≤ b) (m : ℕ) :
    truncSum T (2 * b) m - truncSum T (2 * b - 1) m =
      ∑ A ∈ T.powerset.filter (fun A => A.card = 2 * b),
        if (∏ p ∈ A, p) ∣ m then (-1 : ℝ) ^ A.card else 0 := by
  unfold truncSum
  have hunion : T.powerset.filter (fun A => A.card ≤ 2 * b) =
      T.powerset.filter (fun A => A.card ≤ 2 * b - 1) ∪
      T.powerset.filter (fun A => A.card = 2 * b) := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_union]
    constructor
    · rintro ⟨hAT, hc⟩
      by_cases he : A.card = 2 * b
      · exact Or.inr ⟨hAT, he⟩
      · exact Or.inl ⟨hAT, by omega⟩
    · rintro (⟨hAT, hc⟩ | ⟨hAT, hc⟩) <;> exact ⟨hAT, by omega⟩
  have hdisj : Disjoint (T.powerset.filter (fun A => A.card ≤ 2 * b - 1))
      (T.powerset.filter (fun A => A.card = 2 * b)) := by
    refine Finset.disjoint_left.mpr ?_
    intro A h1 h2
    have c1 := (Finset.mem_filter.mp h1).2
    have c2 := (Finset.mem_filter.mp h2).2
    omega
  rw [hunion, Finset.sum_union hdisj, add_sub_cancel_left]

private lemma prod_diff_le_sum_diff (R : ℕ) (a u l : ℕ → ℝ) (c : ℝ)
    (hc : 0 ≤ c)
    (h : ∀ j ∈ Finset.range R, 0 ≤ a j ∧ a j ≤ u j ∧ l j ≤ a j) :
    ((∏ j ∈ Finset.range R, u j) - (∏ j ∈ Finset.range R, a j)) * c ≤
      (∑ r ∈ Finset.range R, (u r - l r) * (∏ j ∈ (Finset.range R).erase r, u j)) * c := by
  suffices hmain : (∏ j ∈ Finset.range R, u j) - (∏ j ∈ Finset.range R, a j) ≤
      ∑ r ∈ Finset.range R, (u r - l r) * (∏ j ∈ (Finset.range R).erase r, u j) by
    exact mul_le_mul_of_nonneg_right hmain hc
  induction R with
  | zero => simp
  | @succ R ih =>
      have hR : ∀ j ∈ Finset.range R, 0 ≤ a j ∧ a j ≤ u j ∧ l j ≤ a j :=
        fun j hj => h j (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hj)))
      have haR := h R (Finset.mem_range.mpr (Nat.lt_succ_self R))
      have huR0 : 0 ≤ u R := haR.1.trans haR.2.1
      have hprod_a_le_u : ∏ j ∈ Finset.range R, a j ≤ ∏ j ∈ Finset.range R, u j :=
        Finset.prod_le_prod₀ (fun j hj => (hR j hj).1) (fun j hj => (hR j hj).2.1)
      have hprod_a_nonneg : 0 ≤ ∏ j ∈ Finset.range R, a j :=
        Finset.prod_nonneg (fun j hj => (hR j hj).1)
      have hdiff_R : u R - a R ≤ u R - l R := sub_le_sub_left haR.2.2 (u R)
      rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.sum_range_succ]
      have hstep1 : (∏ j ∈ Finset.range R, u j) * u R - (∏ j ∈ Finset.range R, a j) * a R =
          ((∏ j ∈ Finset.range R, u j) - (∏ j ∈ Finset.range R, a j)) * u R +
            (∏ j ∈ Finset.range R, a j) * (u R - a R) := by ring
      have hstep2 : ((∏ j ∈ Finset.range R, u j) - (∏ j ∈ Finset.range R, a j)) * u R ≤
          (∑ r ∈ Finset.range R, (u r - l r) * (∏ j ∈ (Finset.range R).erase r, u j)) * u R :=
        mul_le_mul_of_nonneg_right (ih hR) huR0
      have hstep3 : (∏ j ∈ Finset.range R, a j) * (u R - a R) ≤
          (∏ j ∈ Finset.range R, u j) * (u R - l R) := by
        have hpos_ul : 0 ≤ u R - l R := sub_nonneg.mpr (haR.2.2.trans haR.2.1)
        calc (∏ j ∈ Finset.range R, a j) * (u R - a R)
            ≤ (∏ j ∈ Finset.range R, a j) * (u R - l R) :=
                mul_le_mul_of_nonneg_left hdiff_R hprod_a_nonneg
          _ ≤ (∏ j ∈ Finset.range R, u j) * (u R - l R) :=
                mul_le_mul_of_nonneg_right hprod_a_le_u hpos_ul
      have hsum_eq : (∑ r ∈ Finset.range R, (u r - l r) * (∏ j ∈ (Finset.range R).erase r, u j)) * u R =
          ∑ r ∈ Finset.range R, (u r - l r) * (∏ j ∈ (Finset.range (R + 1)).erase r, u j) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro r hr
        have hr_lt : r < R := Finset.mem_range.mp hr
        have herase : (Finset.range (R + 1)).erase r = insert R ((Finset.range R).erase r) := by
          ext j; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_insert]; omega
        have hRnot : R ∉ (Finset.range R).erase r := by simp
        rw [herase, Finset.prod_insert hRnot]
        ring
      have heraseR : (Finset.range (R + 1)).erase R = Finset.range R := by
        ext j; simp only [Finset.mem_erase, Finset.mem_range]; omega
      calc (∏ j ∈ Finset.range R, u j) * u R - (∏ j ∈ Finset.range R, a j) * a R
          = ((∏ j ∈ Finset.range R, u j) - (∏ j ∈ Finset.range R, a j)) * u R +
              (∏ j ∈ Finset.range R, a j) * (u R - a R) := hstep1
        _ ≤ (∑ r ∈ Finset.range R, (u r - l r) * (∏ j ∈ (Finset.range R).erase r, u j)) * u R +
              (∏ j ∈ Finset.range R, u j) * (u R - l R) := add_le_add hstep2 hstep3
        _ = (∑ r ∈ Finset.range R, (u r - l r) * (∏ j ∈ (Finset.range (R + 1)).erase r, u j)) +
              (u R - l R) * (∏ j ∈ (Finset.range (R + 1)).erase R, u j) := by
            rw [hsum_eq, heraseR]; ring

/-! ### 3. Weighted Bonferroni Bounds & Factorial Symmetrization -/

private noncomputable def wTrunc (T : Finset ℕ) (w : ℕ → ℝ) (M : ℕ) : ℝ :=
  ∑ A ∈ T.powerset.filter (fun A => A.card ≤ M), (-1 : ℝ) ^ A.card * ∏ p ∈ A, w p

private noncomputable def wElem (T : Finset ℕ) (w : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ A ∈ T.powerset.filter (fun A => A.card = k), ∏ p ∈ A, w p

private lemma wElem_nonneg {T : Finset ℕ} {w : ℕ → ℝ} (hw : ∀ p ∈ T, 0 ≤ w p) (k : ℕ) :
    0 ≤ wElem T w k := by
  unfold wElem
  refine Finset.sum_nonneg ?_
  intro A hA
  exact Finset.prod_nonneg (fun p hp => hw p ((Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1) hp))

private lemma wTrunc_insert {T : Finset ℕ} {w : ℕ → ℝ} {p : ℕ} (hp : p ∉ T) {M : ℕ} (hM : 1 ≤ M) :
    wTrunc (insert p T) w M =
      (1 - w p) * wTrunc T w M + w p * (-1 : ℝ) ^ M * wElem T w M := by
  unfold wTrunc wElem
  have hsplit : (insert p T).powerset.filter (fun A => A.card ≤ M) =
      T.powerset.filter (fun A => A.card ≤ M) ∪
      (T.powerset.filter (fun A => A.card ≤ M - 1)).image (insert p) := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨hA, hc⟩
      by_cases hpA : p ∈ A
      · right
        refine ⟨A.erase p, ⟨?_, ?_⟩, Finset.insert_erase hpA⟩
        · intro q hq
          have hqA := Finset.mem_of_mem_erase hq
          have hne : q ≠ p := (Finset.mem_erase.mp hq).1
          exact (Finset.mem_insert.mp (hA hqA)).resolve_left hne
        · have hc' : (A.erase p).card + 1 = A.card := Finset.card_erase_add_one hpA
          omega
      · left
        refine ⟨fun q hq => (Finset.mem_insert.mp (hA hq)).resolve_left (fun h => hpA (h ▸ hq)), hc⟩
    · rintro (⟨hA, hc⟩ | ⟨B, ⟨hB, hc⟩, rfl⟩)
      · exact ⟨fun q hq => Finset.mem_insert_of_mem (hA hq), hc⟩
      · have hpB : p ∉ B := fun h => hp (hB h)
        rw [Finset.card_insert_of_notMem hpB]
        exact ⟨Finset.insert_subset_insert p hB, by omega⟩
  have hdisj : Disjoint (T.powerset.filter (fun A => A.card ≤ M))
      ((T.powerset.filter (fun A => A.card ≤ M - 1)).image (insert p)) := by
    refine Finset.disjoint_left.mpr ?_
    intro A h1 h2
    rcases Finset.mem_image.mp h2 with ⟨B, _, rfl⟩
    exact hp ((Finset.mem_powerset.mp (Finset.mem_filter.mp h1).1) (Finset.mem_insert_self p B))
  rw [hsplit, Finset.sum_union hdisj, Finset.sum_image]
  · have himg : (∑ B ∈ T.powerset.filter (fun A => A.card ≤ M - 1),
        (-1 : ℝ) ^ (insert p B).card * ∏ q ∈ insert p B, w q) =
        - w p * (∑ B ∈ T.powerset.filter (fun A => A.card ≤ M - 1),
          (-1 : ℝ) ^ B.card * ∏ q ∈ B, w q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B hB
      have hpB : p ∉ B := fun h => hp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1) h)
      rw [Finset.card_insert_of_notMem hpB, Finset.prod_insert hpB, pow_succ]
      ring
    have hdiff : (∑ A ∈ T.powerset.filter (fun A => A.card ≤ M), (-1 : ℝ) ^ A.card * ∏ q ∈ A, w q) -
        (∑ B ∈ T.powerset.filter (fun A => A.card ≤ M - 1), (-1 : ℝ) ^ B.card * ∏ q ∈ B, w q) =
        (-1 : ℝ) ^ M * (∑ A ∈ T.powerset.filter (fun A => A.card = M), ∏ q ∈ A, w q) := by
      have hunion2 : T.powerset.filter (fun A => A.card ≤ M) =
          T.powerset.filter (fun A => A.card ≤ M - 1) ∪
          T.powerset.filter (fun A => A.card = M) := by
        ext A; simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_union]
        constructor
        · rintro ⟨hAT, hc⟩
          by_cases he : A.card = M
          · exact Or.inr ⟨hAT, he⟩
          · exact Or.inl ⟨hAT, by omega⟩
        · rintro (⟨hAT, hc⟩ | ⟨hAT, hc⟩) <;> exact ⟨hAT, by omega⟩
      have hdisj2 : Disjoint (T.powerset.filter (fun A => A.card ≤ M - 1))
          (T.powerset.filter (fun A => A.card = M)) := by
        refine Finset.disjoint_left.mpr ?_; intro A h1 h2
        have c1 := (Finset.mem_filter.mp h1).2; have c2 := (Finset.mem_filter.mp h2).2; omega
      rw [hunion2, Finset.sum_union hdisj2, add_sub_cancel_left, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A hA
      rw [(Finset.mem_filter.mp hA).2]
    rw [himg]
    linear_combination w p * hdiff
  · intro B₁ hB₁ B₂ hB₂ heq
    have hp1 : p ∉ B₁ := fun h => hp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hB₁).1) h)
    have hp2 : p ∉ B₂ := fun h => hp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hB₂).1) h)
    calc B₁ = (insert p B₁).erase p := (Finset.erase_insert hp1).symm
      _ = (insert p B₂).erase p := by rw [heq]
      _ = B₂ := Finset.erase_insert hp2

private lemma wTrunc_bounds {T : Finset ℕ} {w : ℕ → ℝ}
    (hw : ∀ p ∈ T, 0 ≤ w p ∧ w p ≤ 1) {b : ℕ} (hb : 1 ≤ b) :
    wTrunc T w (2 * b - 1) ≤ ∏ p ∈ T, (1 - w p) ∧
      ∏ p ∈ T, (1 - w p) ≤ wTrunc T w (2 * b) := by
  induction T using Finset.induction with
  | empty =>
      have hf1 : (∅ : Finset ℕ).powerset.filter (fun A => A.card ≤ 2 * b - 1) = {∅} := by
        ext A; simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_empty,
          Finset.mem_singleton]
        constructor
        · rintro ⟨rfl, _⟩; rfl
        · rintro rfl; exact ⟨rfl, by simp⟩
      have hf2 : (∅ : Finset ℕ).powerset.filter (fun A => A.card ≤ 2 * b) = {∅} := by
        ext A; simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_empty,
          Finset.mem_singleton]
        constructor
        · rintro ⟨rfl, _⟩; rfl
        · rintro rfl; exact ⟨rfl, by simp⟩
      have hwL : wTrunc ∅ w (2 * b - 1) = 1 := by unfold wTrunc; rw [hf1]; simp
      have hwU : wTrunc ∅ w (2 * b) = 1 := by unfold wTrunc; rw [hf2]; simp
      constructor
      · rw [hwL]; simp
      · rw [hwU]; simp
  | @insert p s hps ih =>
      have hs : ∀ q ∈ s, 0 ≤ w q ∧ w q ≤ 1 := fun q hq => hw q (Finset.mem_insert_of_mem hq)
      obtain ⟨ihL, ihU⟩ := ih hs
      have hp := hw p (Finset.mem_insert_self p s)
      have h1wp : 0 ≤ 1 - w p := by linarith
      rw [Finset.prod_insert hps]
      constructor
      · rw [wTrunc_insert hps (by omega : 1 ≤ 2 * b - 1)]
        have hodd : Odd (2 * b - 1) := ⟨b - 1, by omega⟩
        rw [hodd.neg_one_pow]
        have helem : 0 ≤ wElem s w (2 * b - 1) := wElem_nonneg (fun q hq => (hs q hq).1) _
        nlinarith
      · rw [wTrunc_insert hps (by omega : 1 ≤ 2 * b)]
        have heven : (-1 : ℝ) ^ (2 * b) = 1 := by simp [pow_mul]
        rw [heven]
        have helem : 0 ≤ wElem s w (2 * b) := wElem_nonneg (fun q hq => (hs q hq).1) _
        nlinarith

private lemma wTrunc_sub_eq_wElem (T : Finset ℕ) (w : ℕ → ℝ) {b : ℕ} (hb : 1 ≤ b) :
    wTrunc T w (2 * b) - wTrunc T w (2 * b - 1) = wElem T w (2 * b) := by
  unfold wTrunc wElem
  have hunion : T.powerset.filter (fun A => A.card ≤ 2 * b) =
      T.powerset.filter (fun A => A.card ≤ 2 * b - 1) ∪
      T.powerset.filter (fun A => A.card = 2 * b) := by
    ext A; simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_union]
    constructor
    · rintro ⟨hAT, hc⟩
      by_cases he : A.card = 2 * b
      · exact Or.inr ⟨hAT, he⟩
      · exact Or.inl ⟨hAT, by omega⟩
    · rintro (⟨hAT, hc⟩ | ⟨hAT, hc⟩) <;> exact ⟨hAT, by omega⟩
  have hdisj : Disjoint (T.powerset.filter (fun A => A.card ≤ 2 * b - 1))
      (T.powerset.filter (fun A => A.card = 2 * b)) := by
    refine Finset.disjoint_left.mpr ?_; intro A h1 h2
    have c1 := (Finset.mem_filter.mp h1).2; have c2 := (Finset.mem_filter.mp h2).2; omega
  rw [hunion, Finset.sum_union hdisj, add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro A hA
  have hc : A.card = 2 * b := (Finset.mem_filter.mp hA).2
  have heven : (-1 : ℝ) ^ (2 * b) = 1 := by simp [pow_mul]
  rw [hc, heven, one_mul]

private lemma sum_powerset_eq_prod_one_sub (T : Finset ℕ) (w : ℕ → ℝ) :
    (∑ A ∈ T.powerset, (-1 : ℝ) ^ A.card * ∏ p ∈ A, w p) = ∏ p ∈ T, (1 - w p) := by
  have := Finset.prod_sub (s := T) (fun _ => (1 : ℝ)) w
  simp only [Finset.prod_const_one, mul_one] at this
  exact this.symm

private lemma factorial_mul_wElem_le_pow {T : Finset ℕ} {w : ℕ → ℝ}
    (hw : ∀ p ∈ T, 0 ≤ w p) (k : ℕ) :
    (k.factorial : ℝ) * wElem T w k ≤ (∑ p ∈ T, w p) ^ k := by
  induction k with
  | zero =>
      have hf : T.powerset.filter (fun A => A.card = 0) = {∅} := by
        ext A; simp only [Finset.mem_filter, Finset.mem_powerset, Finset.card_eq_zero,
          Finset.mem_singleton]
        constructor
        · rintro ⟨_, rfl⟩; rfl
        · rintro rfl; exact ⟨Finset.empty_subset _, rfl⟩
      unfold wElem
      rw [hf]
      simp
  | @succ k ih =>
      have hcard : ((k + 1 : ℕ) : ℝ) * wElem T w (k + 1) ≤ (∑ p ∈ T, w p) * wElem T w k := by
        unfold wElem
        have hL : ((k + 1 : ℕ) : ℝ) * ∑ B ∈ T.powerset.filter (fun A => A.card = k + 1), ∏ q ∈ B, w q =
            ∑ B ∈ T.powerset.filter (fun A => A.card = k + 1), ∑ p ∈ B,
              w p * ∏ q ∈ B.erase p, w q := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro B hB
          have hc : B.card = k + 1 := (Finset.mem_filter.mp hB).2
          have hin : ∑ p ∈ B, w p * ∏ q ∈ B.erase p, w q = ∑ _p ∈ B, ∏ q ∈ B, w q := by
            apply Finset.sum_congr rfl
            intro p hp
            exact Finset.mul_prod_erase B w hp
          rw [hin, Finset.sum_const, hc, nsmul_eq_mul]
        have hR : (∑ p ∈ T, w p) * ∑ A ∈ T.powerset.filter (fun A => A.card = k), ∏ q ∈ A, w q =
            ∑ A ∈ T.powerset.filter (fun A => A.card = k), ∑ p ∈ T,
              w p * ∏ q ∈ A, w q := by
          rw [mul_comm, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro A _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _
          ring
        rw [hL, hR]
        let S1 := (T.powerset.filter (fun B => B.card = k + 1)).sigma (fun B => B)
        let S2 := (T.powerset.filter (fun A => A.card = k)).sigma (fun _ => T)
        let φ : (_ : Finset ℕ) × ℕ → (_ : Finset ℕ) × ℕ := fun x => ⟨x.1.erase x.2, x.2⟩
        let gsig : (_ : Finset ℕ) × ℕ → ℝ := fun x => w x.2 * ∏ q ∈ x.1, w q
        have hS1 : ∑ B ∈ T.powerset.filter (fun B => B.card = k + 1), ∑ p ∈ B,
              w p * ∏ q ∈ B.erase p, w q =
            ∑ x ∈ S1, gsig (φ x) := by
          exact Finset.sum_sigma' (T.powerset.filter (fun B => B.card = k + 1)) (fun B => B)
            (fun B p => w p * ∏ q ∈ B.erase p, w q)
        have hS2 : ∑ A ∈ T.powerset.filter (fun A => A.card = k), ∑ p ∈ T,
              w p * ∏ q ∈ A, w q =
            ∑ x ∈ S2, gsig x := by
          exact Finset.sum_sigma' (T.powerset.filter (fun A => A.card = k)) (fun _ => T)
            (fun A p => w p * ∏ q ∈ A, w q)
        have hinj : Set.InjOn φ (S1 : Set ((_ : Finset ℕ) × ℕ)) := by
          intro x hx y hy heq
          dsimp only [φ] at heq
          rcases Finset.mem_sigma.mp hx with ⟨_, hpx⟩
          rcases Finset.mem_sigma.mp hy with ⟨_, hpy⟩
          have hp_eq : x.2 = y.2 := congrArg Sigma.snd heq
          have ha_eq : x.1.erase x.2 = y.1.erase y.2 := congrArg Sigma.fst heq
          have hset : x.1 = y.1 := by
            calc x.1 = insert x.2 (x.1.erase x.2) := (Finset.insert_erase hpx).symm
              _ = insert y.2 (y.1.erase y.2) := by rw [ha_eq, hp_eq]
              _ = y.1 := Finset.insert_erase hpy
          exact Sigma.ext hset (by rw [hp_eq])
        have hsub : S1.image φ ⊆ S2 := by
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
          rcases Finset.mem_sigma.mp hx with ⟨hB, hpB⟩
          have hBT := Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1
          have hcB := (Finset.mem_filter.mp hB).2
          have hcard_er : (x.1.erase x.2).card = k := by
            have := Finset.card_erase_add_one hpB; omega
          refine Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, hcard_er⟩, hBT hpB⟩
          intro q hq; exact hBT (Finset.mem_of_mem_erase hq)
        rw [hS1, hS2, ← Finset.sum_image hinj]
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
        intro y hy _
        rcases Finset.mem_sigma.mp hy with ⟨hA, hpT⟩
        have hAT := Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1
        exact mul_nonneg (hw y.2 hpT) (Finset.prod_nonneg (fun q hq => hw q (hAT hq)))
      have hk0 : 0 ≤ (k.factorial : ℝ) := Nat.cast_nonneg _
      have hS0 : 0 ≤ ∑ p ∈ T, w p := Finset.sum_nonneg hw
      rw [Nat.factorial_succ, Nat.cast_mul, mul_assoc, pow_succ']
      calc ((k + 1 : ℕ) : ℝ) * ((k.factorial : ℝ) * wElem T w (k + 1))
          = (k.factorial : ℝ) * (((k + 1 : ℕ) : ℝ) * wElem T w (k + 1)) := by ring
        _ ≤ (k.factorial : ℝ) * ((∑ p ∈ T, w p) * wElem T w k) :=
            mul_le_mul_of_nonneg_left hcard hk0
        _ = (∑ p ∈ T, w p) * ((k.factorial : ℝ) * wElem T w k) := by ring
        _ ≤ (∑ p ∈ T, w p) * (∑ p ∈ T, w p) ^ k :=
            mul_le_mul_of_nonneg_left ih hS0

/-! ### 4. Recursive Partition Families & Product-Sum Factorization -/

private def goodSeq (R : ℕ) (T : ℕ → Finset ℕ) (Tbase : Finset ℕ) (cap : ℕ → ℕ) : Finset (Finset ℕ) :=
  match R with
  | 0 => Tbase.powerset
  | R + 1 =>
      ((T R).powerset.filter (fun B => B.card ≤ cap R)).biUnion
        (fun B => (goodSeq R T Tbase cap).image (fun A => B ∪ A))

private def errSeq (r R : ℕ) (T : ℕ → Finset ℕ) (Tbase : Finset ℕ) (cap : ℕ → ℕ) : Finset (Finset ℕ) :=
  match R with
  | 0 => ∅
  | R + 1 =>
      if r = R then
        ((T R).powerset.filter (fun B => B.card = cap R)).biUnion
          (fun B => (goodSeq R T Tbase cap).image (fun A => B ∪ A))
      else
        ((T R).powerset.filter (fun B => B.card ≤ cap R)).biUnion
          (fun B => (errSeq r R T Tbase cap).image (fun A => B ∪ A))

private lemma errSeq_subset_goodSeq (r R : ℕ) (T : ℕ → Finset ℕ) (Tbase : Finset ℕ) (cap : ℕ → ℕ) :
    errSeq r R T Tbase cap ⊆ goodSeq R T Tbase cap := by
  induction R with
  | zero => simp [errSeq]
  | @succ R ih =>
      simp only [errSeq, goodSeq]
      split_ifs with hr
      · refine Finset.biUnion_subset_biUnion_of_subset_left _ ?_
        intro B hB
        simp only [Finset.mem_filter, Finset.mem_powerset] at hB ⊢
        exact ⟨hB.1, le_of_eq hB.2⟩
      · refine Finset.biUnion_mono ?_
        intro B _
        exact Finset.image_subset_image ih

private lemma goodSeq_subset_union (R : ℕ) (T : ℕ → Finset ℕ) (Tbase : Finset ℕ) (cap : ℕ → ℕ)
    {A : Finset ℕ} (hA : A ∈ goodSeq R T Tbase cap) :
    A ⊆ Tbase ∪ (Finset.range R).biUnion T := by
  induction R generalizing A with
  | zero =>
      simp only [goodSeq, Finset.mem_powerset, Finset.range_zero, Finset.biUnion_empty,
        Finset.union_empty] at hA ⊢
      exact hA
  | @succ R ih =>
      simp only [goodSeq, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
        Finset.mem_powerset] at hA
      rcases hA with ⟨B, ⟨hBT, _⟩, C, hC, rfl⟩
      have hCsub := ih hC
      intro p hp
      rcases Finset.mem_union.mp hp with hpB | hpC
      · exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨R, Finset.mem_range.mpr (Nat.lt_succ_self R), hBT hpB⟩)
      · rcases Finset.mem_union.mp (hCsub hpC) with hp0 | hpi
        · exact Finset.mem_union_left _ hp0
        · rcases Finset.mem_biUnion.mp hpi with ⟨j, hj, hpj⟩
          exact Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hj)), hpj⟩)

private lemma biUnion_image_union_sum {α : Type*} [DecidableEq α]
    (S1 S2 : Finset (Finset α)) (U : Finset α)
    (hS1 : ∀ B ∈ S1, B ⊆ U) (hS2 : ∀ C ∈ S2, Disjoint U C)
    (g : Finset α → ℝ) (hg : ∀ B C, Disjoint B C → g (B ∪ C) = g B * g C) :
    (∑ A ∈ S1.biUnion (fun B => S2.image (fun C => B ∪ C)), g A) =
      (∑ B ∈ S1, g B) * (∑ C ∈ S2, g C) := by
  have hdisj_bi : ∀ B₁ ∈ S1, ∀ B₂ ∈ S1, B₁ ≠ B₂ →
      Disjoint (S2.image (fun C => B₁ ∪ C)) (S2.image (fun C => B₂ ∪ C)) := by
    intro B₁ h1 B₂ h2 hne
    refine Finset.disjoint_left.mpr ?_
    intro A hA1 hA2
    rcases Finset.mem_image.mp hA1 with ⟨C₁, hC₁, rfl⟩
    rcases Finset.mem_image.mp hA2 with ⟨C₂, hC₂, heq⟩
    apply hne
    ext p
    have hu1 : (C₁ ∪ B₁) ∩ U = B₁ := by
      have hd := Finset.disjoint_iff_inter_eq_empty.mp (hS2 C₁ hC₁).symm
      rw [Finset.union_inter_distrib_right, hd, Finset.empty_union,
        Finset.inter_eq_left.mpr (hS1 B₁ h1)]
    have hu2 : (C₂ ∪ B₂) ∩ U = B₂ := by
      have hd := Finset.disjoint_iff_inter_eq_empty.mp (hS2 C₂ hC₂).symm
      rw [Finset.union_inter_distrib_right, hd, Finset.empty_union,
        Finset.inter_eq_left.mpr (hS1 B₂ h2)]
    rw [Finset.union_comm B₁ C₁, Finset.union_comm B₂ C₂] at heq
    have hcap := congrArg (· ∩ U) heq
    rw [hu1, hu2] at hcap
    rw [hcap]
  rw [Finset.sum_biUnion (fun B₁ h1 B₂ h2 hne => hdisj_bi B₁ h1 B₂ h2 hne), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro B hB
  have hinj : Set.InjOn (fun C => B ∪ C) (S2 : Set (Finset α)) := by
    intro C₁ hC₁ C₂ hC₂ heq
    dsimp only at heq
    have hd1 : Disjoint B C₁ := (hS2 C₁ hC₁).mono_left (hS1 B hB)
    have hd2 : Disjoint B C₂ := (hS2 C₂ hC₂).mono_left (hS1 B hB)
    calc C₁ = (B ∪ C₁) \ B := by rw [Finset.union_sdiff_cancel_left hd1]
      _ = (B ∪ C₂) \ B := by rw [heq]
      _ = C₂ := by rw [Finset.union_sdiff_cancel_left hd2]
  rw [Finset.sum_image hinj, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro C hC
  exact hg B C ((hS2 C hC).mono_left (hS1 B hB))

private lemma sum_goodSeq_eq_prod (R : ℕ) (T : ℕ → Finset ℕ) (Tbase : Finset ℕ) (cap : ℕ → ℕ)
    (hdisj_base : ∀ j, Disjoint (T j) Tbase)
    (hdisj_T : ∀ i j, i ≠ j → Disjoint (T i) (T j))
    (g : Finset ℕ → ℝ) (hg : ∀ B C, Disjoint B C → g (B ∪ C) = g B * g C) :
    (∑ A ∈ goodSeq R T Tbase cap, g A) =
      (∏ j ∈ Finset.range R, ∑ B ∈ (T j).powerset.filter (fun B => B.card ≤ cap j), g B) *
        (∑ A ∈ Tbase.powerset, g A) := by
  induction R with
  | zero => simp [goodSeq]
  | @succ R ih =>
      simp only [goodSeq]
      rw [biUnion_image_union_sum _ _ (T R)
        (fun B hB => Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1)
        (fun C hC => by
          refine Finset.disjoint_left.mpr ?_
          intro p hpTR hpC
          rcases Finset.mem_union.mp (goodSeq_subset_union R T Tbase cap hC hpC) with h0 | hi
          · exact (Finset.disjoint_left.mp (hdisj_base R)) hpTR h0
          · rcases Finset.mem_biUnion.mp hi with ⟨j, hj, hpj⟩
            exact (Finset.disjoint_left.mp (hdisj_T R j (by have := Finset.mem_range.mp hj; omega)))
              hpTR hpj)
        g hg, ih, Finset.prod_range_succ]
      ring

private lemma sum_errSeq_eq_prod {r R : ℕ} (hr : r < R) (T : ℕ → Finset ℕ) (Tbase : Finset ℕ)
    (cap : ℕ → ℕ) (hdisj_base : ∀ j, Disjoint (T j) Tbase)
    (hdisj_T : ∀ i j, i ≠ j → Disjoint (T i) (T j))
    (g : Finset ℕ → ℝ) (hg : ∀ B C, Disjoint B C → g (B ∪ C) = g B * g C) :
    (∑ A ∈ errSeq r R T Tbase cap, g A) =
      (∑ B ∈ (T r).powerset.filter (fun B => B.card = cap r), g B) *
        (∏ j ∈ (Finset.range R).erase r,
          ∑ B ∈ (T j).powerset.filter (fun B => B.card ≤ cap j), g B) *
        (∑ A ∈ Tbase.powerset, g A) := by
  induction R with
  | zero => omega
  | @succ R ih =>
      simp only [errSeq]
      split_ifs with heq
      · subst heq
        rw [biUnion_image_union_sum _ _ (T r)
          (fun B hB => Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1)
          (fun C hC => by
            refine Finset.disjoint_left.mpr ?_
            intro p hpTR hpC
            rcases Finset.mem_union.mp (goodSeq_subset_union r T Tbase cap hC hpC) with h0 | hi
            · exact (Finset.disjoint_left.mp (hdisj_base r)) hpTR h0
            · rcases Finset.mem_biUnion.mp hi with ⟨j, hj, hpj⟩
              exact (Finset.disjoint_left.mp (hdisj_T r j (by have := Finset.mem_range.mp hj; omega)))
                hpTR hpj)
          g hg, sum_goodSeq_eq_prod r T Tbase cap hdisj_base hdisj_T g hg]
        have her : (Finset.range (r + 1)).erase r = Finset.range r := by
          ext j; simp only [Finset.mem_erase, Finset.mem_range]; omega
        rw [her]
        ring
      · have hr' : r < R := by omega
        rw [biUnion_image_union_sum _ _ (T R)
          (fun B hB => Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1)
          (fun C hC => by
            have hCg := errSeq_subset_goodSeq r R T Tbase cap hC
            refine Finset.disjoint_left.mpr ?_
            intro p hpTR hpC
            rcases Finset.mem_union.mp (goodSeq_subset_union R T Tbase cap hCg hpC) with h0 | hi
            · exact (Finset.disjoint_left.mp (hdisj_base R)) hpTR h0
            · rcases Finset.mem_biUnion.mp hi with ⟨j, hj, hpj⟩
              exact (Finset.disjoint_left.mp (hdisj_T R j (by have := Finset.mem_range.mp hj; omega)))
                hpTR hpj)
          g hg, ih hr']
        have her : (Finset.range (R + 1)).erase r = insert R ((Finset.range R).erase r) := by
          ext j; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_insert]; omega
        have hRnot : R ∉ (Finset.range R).erase r := by simp
        rw [her, Finset.prod_insert hRnot]
        ring

/-! ### 5. Geometric Cutoffs & Analytic Estimates -/

private def cut (z : ℕ) : ℕ → ℕ
  | 0 => z
  | j + 1 => Nat.sqrt (cut z j)

private lemma cut_antitone (z : ℕ) : ∀ j, cut z (j + 1) ≤ cut z j
  | _ => Nat.sqrt_le_self _

private lemma cut_le (z : ℕ) {i j : ℕ} (hij : i ≤ j) : cut z j ≤ cut z i := by
  induction hij with
  | refl => exact le_rfl
  | @step m _ ih => exact (cut_antitone z m).trans ih

private lemma cut_strict_half {z j : ℕ} (h4 : 4 ≤ cut z j) : 2 * cut z (j + 1) ≤ cut z j := by
  have hlt : cut z (j + 1) < cut z j / 2 + 1 := by
    rw [cut]
    exact Nat.sqrt_lt'.mpr (by nlinarith [Nat.div_add_mod (cut z j) 2, Nat.mod_lt (cut z j) (by omega : 0 < 2)])
  omega

private lemma cut_rpow_le (z j : ℕ) :
    (cut z j : ℝ) ≤ (z : ℝ) ^ ((1 / 2 : ℝ) ^ j) := by
  induction j with
  | zero => simp [cut]
  | @succ j ih =>
      have hz0 : 0 ≤ (z : ℝ) := Nat.cast_nonneg z
      have hsq : ((cut z (j + 1) : ℕ) : ℝ) ^ 2 ≤ (cut z j : ℝ) := by
        exact_mod_cast Nat.sqrt_le' (cut z j)
      have hle_sqrt : (cut z (j + 1) : ℝ) ≤ (cut z j : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.sqrt_eq_rpow]
        exact Real.le_sqrt_of_sq_le hsq
      calc (cut z (j + 1) : ℝ) ≤ (cut z j : ℝ) ^ (1 / 2 : ℝ) := hle_sqrt
        _ ≤ ((z : ℝ) ^ ((1 / 2 : ℝ) ^ j)) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) ih (by norm_num)
        _ = (z : ℝ) ^ ((1 / 2 : ℝ) ^ j * (1 / 2 : ℝ)) := by
            rw [← Real.rpow_mul hz0]
        _ = (z : ℝ) ^ ((1 / 2 : ℝ) ^ (j + 1)) := by ring_nf

private lemma sum_weighted_geom_le (R : ℕ) :
    ∑ j ∈ Finset.range R, (2 * (j + 2) : ℝ) * (1 / 2 : ℝ) ^ j ≤ 12 := by
  have hclosed : ∀ n : ℕ, ∑ j ∈ Finset.range n, (j + 2 : ℝ) * (1 / 2 : ℝ) ^ j =
      6 - (2 * (n : ℝ) + 6) * (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | @succ n ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        rw [pow_succ']
        ring
  have h2 : ∑ j ∈ Finset.range R, (2 * (j + 2) : ℝ) * (1 / 2 : ℝ) ^ j =
      2 * ∑ j ∈ Finset.range R, (j + 2 : ℝ) * (1 / 2 : ℝ) ^ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _; ring
  rw [h2, hclosed R]
  have hnonneg : 0 ≤ (2 * (R : ℝ) + 6) * (1 / 2 : ℝ) ^ R := by positivity
  linarith

private lemma prod_union_le_mul (B D : Finset ℕ) (hBD : ∀ p ∈ B ∪ D, 1 ≤ p) :
    ∏ p ∈ B ∪ D, p ≤ (∏ p ∈ B, p) * (∏ p ∈ D, p) := by
  have hun : B ∪ D = B ∪ (D \ B) := by ext x; simp
  have hdisj : Disjoint B (D \ B) := Finset.disjoint_left.mpr (fun _ hx hxs => (Finset.mem_sdiff.mp hxs).2 hx)
  rw [hun, Finset.prod_union hdisj]
  refine Nat.mul_le_mul_left _ ?_
  exact Finset.prod_le_prod_of_subset_of_one_le Finset.sdiff_subset
    (fun p hp _ => hBD p (Finset.mem_union_right _ hp))

private lemma goodSeq_prod_le {R : ℕ} {z : ℕ} (hz : 1 ≤ z) (A0 : ℕ)
    (hcutR : cut z R ≤ A0 ^ 2)
    (T : ℕ → Finset ℕ)
    (hTsub : ∀ j, T j ⊆ split (cut z j))
    (Tbase : Finset ℕ) (hBsub : Tbase ⊆ split (cut z R))
    (cap : ℕ → ℕ) (hcap : ∀ j, cap j = 2 * (j + 2))
    {A : Finset ℕ} (hA : A ∈ goodSeq R T Tbase cap) :
    ((∏ p ∈ A, p : ℕ) : ℝ) ≤ ((splitWheel (A0 ^ 2) : ℕ) : ℝ) * (z : ℝ) ^ (12 : ℝ) := by
  suffices hgen : ∀ k, ∀ C ∈ goodSeq k T Tbase cap,
      ((∏ p ∈ C, p : ℕ) : ℝ) ≤
        ((splitWheel (A0 ^ 2) : ℕ) : ℝ) *
          (z : ℝ) ^ (∑ j ∈ Finset.range k, (2 * (j + 2) : ℝ) * (1 / 2 : ℝ) ^ j) by
    have hC := hgen R A hA
    have hz1 : 1 ≤ (z : ℝ) := by exact_mod_cast hz
    have hpow := Real.rpow_le_rpow_of_exponent_le hz1 (sum_weighted_geom_le R)
    have hsw : 0 ≤ ((splitWheel (A0 ^ 2) : ℕ) : ℝ) := Nat.cast_nonneg _
    exact hC.trans (mul_le_mul_of_nonneg_left hpow hsw)
  intro k
  induction k with
  | zero =>
      intro C hC
      simp only [goodSeq, Finset.mem_powerset, Finset.range_zero, Finset.sum_empty,
        Real.rpow_zero, mul_one] at hC ⊢
      have hsub : C ⊆ split (A0 ^ 2) := hC.trans (hBsub.trans (split_mono hcutR))
      have hdvd : (∏ p ∈ C, p) ∣ splitWheel (A0 ^ 2) := by
        unfold splitWheel
        exact Finset.prod_dvd_prod_of_subset C (split (A0 ^ 2)) _ hsub
      exact_mod_cast Nat.le_of_dvd (splitWheel_pos _) hdvd
  | @succ k ih =>
      intro C hC
      simp only [goodSeq, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
        Finset.mem_powerset] at hC
      rcases hC with ⟨B, ⟨hBT, hBcard⟩, D, hD, rfl⟩
      have hsubB : B ⊆ split (cut z k) := hBT.trans (hTsub k)
      have hge1 : ∀ p ∈ B ∪ D, 1 ≤ p := by
        intro p hp
        rcases Finset.mem_union.mp hp with hpB | hpD
        · have := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hsubB hpB)).1).1; omega
        · have hDsub := goodSeq_subset_union k T Tbase cap hD hpD
          rcases Finset.mem_union.mp hDsub with hp0 | hpi
          · have := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hBsub hp0)).1).1; omega
          · rcases Finset.mem_biUnion.mp hpi with ⟨j, _, hpj⟩
            have := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hTsub j hpj)).1).1; omega
      have hmul : ((∏ p ∈ B ∪ D, p : ℕ) : ℝ) ≤
          ((∏ p ∈ B, p : ℕ) : ℝ) * ((∏ p ∈ D, p : ℕ) : ℝ) := by
        exact_mod_cast prod_union_le_mul B D hge1
      have hB_le : ((∏ p ∈ B, p : ℕ) : ℝ) ≤ (z : ℝ) ^ ((2 * (k + 2) : ℝ) * (1 / 2 : ℝ) ^ k) := by
        by_cases hBe : B = ∅
        · subst hBe
          simp only [Finset.prod_empty, Nat.cast_one]
          exact Real.one_le_rpow (by exact_mod_cast hz) (by positivity)
        · obtain ⟨p0, hp0⟩ := Finset.nonempty_iff_ne_empty.mpr hBe
          have hp0_le : p0 ≤ cut z k := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hsubB hp0)).1).2
          have hp0_ge : 5 ≤ p0 := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hsubB hp0)).1).1
          have hcut1 : (1 : ℝ) ≤ (cut z k : ℝ) := by exact_mod_cast (by omega : 1 ≤ cut z k)
          have hBprod_nat : ∏ p ∈ B, p ≤ (cut z k) ^ B.card := by
            calc ∏ p ∈ B, p ≤ ∏ _p ∈ B, cut z k :=
                  Finset.prod_le_prod (fun p hp => (Finset.mem_Icc.mp (Finset.mem_filter.mp (hsubB hp)).1).2)
              _ = (cut z k) ^ B.card := Finset.prod_const _
          have hBprod_R : ((∏ p ∈ B, p : ℕ) : ℝ) ≤ (cut z k : ℝ) ^ (cap k) := by
            have h1 : ((∏ p ∈ B, p : ℕ) : ℝ) ≤ (cut z k : ℝ) ^ B.card := by exact_mod_cast hBprod_nat
            exact h1.trans (pow_le_pow_right₀ hcut1 hBcard)
          rw [hcap k] at hBprod_R
          have hcut_z := cut_rpow_le z k
          calc ((∏ p ∈ B, p : ℕ) : ℝ)
              ≤ (cut z k : ℝ) ^ (2 * (k + 2)) := hBprod_R
            _ ≤ ((z : ℝ) ^ ((1 / 2 : ℝ) ^ k)) ^ (2 * (k + 2)) :=
                pow_le_pow_left₀ (Nat.cast_nonneg _) hcut_z _
            _ = ((z : ℝ) ^ ((1 / 2 : ℝ) ^ k)) ^ ((2 * (k + 2) : ℕ) : ℝ) := by
                rw [Real.rpow_natCast]
            _ = (z : ℝ) ^ ((1 / 2 : ℝ) ^ k * ((2 * (k + 2) : ℕ) : ℝ)) := by
                rw [← Real.rpow_mul (Nat.cast_nonneg _)]
            _ = (z : ℝ) ^ ((2 * (k + 2) : ℝ) * (1 / 2 : ℝ) ^ k) := by
                congr 1; push_cast; ring
      have hD_le := ih D hD
      have hz0 : 0 ≤ (z : ℝ) := Nat.cast_nonneg z
      have hzpos : 0 < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
      have hD0 : 0 ≤ ((∏ p ∈ D, p : ℕ) : ℝ) := Nat.cast_nonneg _
      have hB0 : 0 ≤ (z : ℝ) ^ ((2 * (k + 2) : ℝ) * (1 / 2 : ℝ) ^ k) := by positivity
      calc ((∏ p ∈ B ∪ D, p : ℕ) : ℝ)
          ≤ ((∏ p ∈ B, p : ℕ) : ℝ) * ((∏ p ∈ D, p : ℕ) : ℝ) := hmul
        _ ≤ (z : ℝ) ^ ((2 * (k + 2) : ℝ) * (1 / 2 : ℝ) ^ k) *
              (((splitWheel (A0 ^ 2) : ℕ) : ℝ) *
                (z : ℝ) ^ (∑ j ∈ Finset.range k, (2 * (j + 2) : ℝ) * (1 / 2 : ℝ) ^ j)) :=
            mul_le_mul hB_le hD_le hD0 hB0
        _ = ((splitWheel (A0 ^ 2) : ℕ) : ℝ) *
              ((z : ℝ) ^ (∑ j ∈ Finset.range k, (2 * (j + 2) : ℝ) * (1 / 2 : ℝ) ^ j) *
                (z : ℝ) ^ ((2 * (k + 2) : ℝ) * (1 / 2 : ℝ) ^ k)) := by ring
        _ = ((splitWheel (A0 ^ 2) : ℕ) : ℝ) *
              (z : ℝ) ^ (∑ j ∈ Finset.range (k + 1), (2 * (j + 2) : ℝ) * (1 / 2 : ℝ) ^ j) := by
            rw [← Real.rpow_add hzpos, Finset.sum_range_succ]

private lemma localProd_pos (z : ℕ) : 0 < localProd z := by
  unfold localProd
  refine Finset.prod_pos ?_
  intro p hp
  have hp5 : 5 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have hpR : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
  linarith [show (2 : ℝ) / (p : ℝ) ≤ 2 / 5 from div_le_div_of_nonneg_left (by norm_num) (by linarith) hpR]

private lemma four_lt_log_hundred : (4 : ℝ) < Real.log 100 := by
  have hexp1 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hexp4 : Real.exp 4 < 100 := by
    calc Real.exp 4 = Real.exp ((4 : ℕ) * 1) := by norm_num
      _ = (Real.exp 1) ^ 4 := by rw [Real.exp_nat_mul]
      _ < (3 : ℝ) ^ 4 := pow_lt_pow_left₀ hexp1 (Real.exp_pos 1).le (by omega)
      _ < 100 := by norm_num
  exact (Real.lt_log_iff_exp_lt (by norm_num)).mpr hexp4

private lemma one_half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  have hexp1 : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hexp_half : (Real.exp (1 / 2 : ℝ)) ^ 2 < 2 ^ 2 := by
    rw [← Real.exp_nat_mul]
    norm_num
    exact hexp1
  have hlt : Real.exp (1 / 2 : ℝ) < 2 := by
    by_contra hge
    push_neg at hge
    have hsq := pow_le_pow_left₀ (by norm_num) hge 2
    linarith
  exact (Real.lt_log_iff_exp_lt (by norm_num)).mpr hlt

private lemma log_25_12_lt_three_fourths : Real.log (25 / 12 : ℝ) < 3 / 4 := by
  have hexp1 : (2718 / 1000 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have hexp3 : (19 : ℝ) < Real.exp 3 := by
    calc (19 : ℝ) < (2718 / 1000 : ℝ) ^ 3 := by norm_num
      _ < (Real.exp 1) ^ 3 := pow_lt_pow_left₀ hexp1 (by norm_num) (by omega)
      _ = Real.exp ((3 : ℕ) * 1) := (Real.exp_nat_mul 1 3).symm
      _ = Real.exp 3 := by norm_num
  have hlt4 : (25 / 12 : ℝ) ^ 4 < (Real.exp (3 / 4 : ℝ)) ^ 4 := by
    rw [← Real.exp_nat_mul]
    norm_num
    linarith
  have hlt : (25 / 12 : ℝ) < Real.exp (3 / 4 : ℝ) := by
    by_contra hge
    push_neg at hge
    have hpow := pow_le_pow_left₀ (Real.exp_pos _).le hge 4
    linarith
  exact (Real.log_lt_iff_lt_exp (by norm_num)).mpr hlt

private lemma sum_two_div_le_neg_log_prod {T : Finset ℕ} (hT : ∀ p ∈ T, 5 ≤ p) :
    ∑ p ∈ T, (2 / (p : ℝ)) ≤ -Real.log (∏ p ∈ T, (1 - 2 / (p : ℝ))) := by
  have hpos : ∀ p ∈ T, 0 < 1 - 2 / (p : ℝ) := by
    intro p hp
    have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast hT p hp
    have hdiv : 2 / (p : ℝ) ≤ 2 / 5 := div_le_div_of_nonneg_left (by norm_num) (by linarith) hp5
    linarith
  rw [Real.log_prod (fun p hp => (hpos p hp).ne'), ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum ?_
  intro p hp
  have hexp : 1 - 2 / (p : ℝ) ≤ Real.exp (-(2 / (p : ℝ))) := by
    linarith [Real.add_one_le_exp (-(2 / (p : ℝ)))]
  have hlog : Real.log (1 - 2 / (p : ℝ)) ≤ -(2 / (p : ℝ)) :=
    (Real.log_le_iff_le_exp (hpos p hp)).mpr hexp
  linarith

private lemma prod_one_add_le_exp_sum {R : ℕ} {δ : ℕ → ℝ} (hδ : ∀ j, 0 ≤ δ j) :
    ∏ j ∈ Finset.range R, (1 + δ j) ≤ Real.exp (∑ j ∈ Finset.range R, δ j) := by
  calc ∏ j ∈ Finset.range R, (1 + δ j)
      ≤ ∏ j ∈ Finset.range R, Real.exp (δ j) := by
        refine Finset.prod_le_prod₀ (fun j _ => by linarith [hδ j]) ?_
        intro j _
        linarith [Real.add_one_le_exp (δ j)]
    _ = Real.exp (∑ j ∈ Finset.range R, δ j) := (Real.exp_sum _ _).symm

private lemma geom_sum_quarter_le (R : ℕ) :
    ∑ j ∈ Finset.range R, (1 / 4 : ℝ) ^ j ≤ 4 / 3 := by
  have hclosed : ∑ j ∈ Finset.range R, (1 / 4 : ℝ) ^ j =
      4 / 3 - (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ R := by
    induction R with
    | zero => norm_num
    | @succ R ih =>
        rw [Finset.sum_range_succ, ih, pow_succ']
        ring
  rw [hclosed]
  have hpos : 0 ≤ (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ R := by positivity
  linarith

private lemma factorial_two_j_plus_four (j : ℕ) :
    24 * 4 ^ j ≤ (2 * (j + 2)).factorial := by
  induction j with
  | zero => norm_num
  | @succ j ih =>
      have heq : 2 * (j + 1 + 2) = 2 * (j + 2) + 2 := by omega
      rw [heq, Nat.factorial_succ, Nat.factorial_succ]
      have h1 : 4 ≤ (2 * (j + 2) + 2) * (2 * (j + 2) + 1) := by nlinarith
      calc 24 * 4 ^ (j + 1) = (24 * 4 ^ j) * 4 := by ring
        _ ≤ (2 * (j + 2)).factorial * ((2 * (j + 2) + 2) * (2 * (j + 2) + 1)) :=
            Nat.mul_le_mul ih h1
        _ = (2 * (j + 2) + 2) * ((2 * (j + 2) + 1) * (2 * (j + 2)).factorial) := by ring

private lemma delta_bound (j : ℕ) :
    (3 / 4 : ℝ) ^ (2 * (j + 2)) / (((2 * (j + 2)).factorial : ℝ) * (48 / 100 : ℝ)) ≤
      (1 / 30 : ℝ) * (1 / 4 : ℝ) ^ j := by
  have hfac : (24 : ℝ) * 4 ^ j ≤ ((2 * (j + 2)).factorial : ℝ) := by
    exact_mod_cast factorial_two_j_plus_four j
  have hpow : (3 / 4 : ℝ) ^ (2 * (j + 2)) = (81 / 256 : ℝ) * (9 / 16 : ℝ) ^ j := by
    have he : 2 * (j + 2) = 4 + 2 * j := by omega
    rw [he, pow_add, pow_mul]
    norm_num
  rw [hpow, div_le_iff₀ (by positivity)]
  calc (81 / 256 : ℝ) * (9 / 16 : ℝ) ^ j
      ≤ (1 / 30 : ℝ) * (1 / 4 : ℝ) ^ j * ((24 * 4 ^ j : ℝ) * (48 / 100 : ℝ)) := by
        have h916 : (9 / 16 : ℝ) ^ j ≤ (1 : ℝ) := pow_le_one₀ (by norm_num) (by norm_num)
        have h14 : (1 / 4 : ℝ) ^ j * 4 ^ j = 1 := by rw [← mul_pow]; norm_num
        calc (81 / 256 : ℝ) * (9 / 16 : ℝ) ^ j
            ≤ (81 / 256 : ℝ) * 1 := mul_le_mul_of_nonneg_left h916 (by norm_num)
          _ ≤ (1 / 30 : ℝ) * 24 * (48 / 100 : ℝ) * 1 := by norm_num
          _ = (1 / 30 : ℝ) * (1 / 4 : ℝ) ^ j * ((24 * 4 ^ j : ℝ) * (48 / 100 : ℝ)) := by
              calc (1 / 30 : ℝ) * 24 * (48 / 100 : ℝ) * 1
                  = (1 / 30 : ℝ) * 24 * (48 / 100 : ℝ) * ((1 / 4 : ℝ) ^ j * 4 ^ j) := by rw [h14]
                _ = (1 / 30 : ℝ) * (1 / 4 : ℝ) ^ j * ((24 * 4 ^ j : ℝ) * (48 / 100 : ℝ)) := by ring
    _ ≤ (1 / 30 : ℝ) * (1 / 4 : ℝ) ^ j * (((2 * (j + 2)).factorial : ℝ) * (48 / 100 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hfac (by norm_num)) (by positivity)

private lemma interval_pi_and_sum_bound (c₀ : ℝ) (hc₀_pos : 0 < c₀) (z₀ z₁ : ℕ)
    (hz1_ge100 : 100 ≤ z₁) (hle : z₁ ≤ z₀) (hlt_sq : z₀ < (z₁ + 1) ^ 2)
    (hlo : (99 / 100 : ℝ) * c₀ ≤ Real.log (z₀ : ℝ) * localProd z₀)
    (hhi : Real.log (z₁ : ℝ) * localProd z₁ ≤ (101 / 100 : ℝ) * c₀) :
    (48 / 100 : ℝ) ≤ ∏ p ∈ split z₀ \ split z₁, (1 - 2 / (p : ℝ)) ∧
      ∑ p ∈ split z₀ \ split z₁, (2 / (p : ℝ)) ≤ (3 / 4 : ℝ) := by
  let Pi_val : ℝ := ∏ p ∈ split z₀ \ split z₁, (1 - 2 / (p : ℝ))
  have hsub : split z₁ ⊆ split z₀ := split_mono hle
  have hprod_split : localProd z₀ = Pi_val * localProd z₁ := by
    unfold localProd
    dsimp only [Pi_val]
    rw [← Finset.prod_sdiff hsub]
  have hPi_eq : Pi_val = localProd z₀ / localProd z₁ := by
    rw [hprod_split, mul_div_cancel_right₀ _ (localProd_pos _).ne']
  have hz₀_ge100 : 100 ≤ z₀ := hz1_ge100.trans hle
  have hlog_z1_gt4 : (4 : ℝ) < Real.log (z₁ : ℝ) := by
    have h100 : (100 : ℝ) ≤ (z₁ : ℝ) := by exact_mod_cast hz1_ge100
    exact four_lt_log_hundred.trans_le (Real.log_le_log (by norm_num) h100)
  have hlog_z₀_pos : 0 < Real.log (z₀ : ℝ) := by
    have h100 : (100 : ℝ) ≤ (z₀ : ℝ) := by exact_mod_cast hz₀_ge100
    linarith [four_lt_log_hundred.trans_le (Real.log_le_log (by norm_num) h100)]
  have hlog_z₁_pos : 0 < Real.log (z₁ : ℝ) := by linarith
  have hlog_z₀_le : Real.log (z₀ : ℝ) ≤ (2005 / 1000 : ℝ) * Real.log (z₁ : ℝ) := by
    have h1 : Real.log (z₀ : ℝ) ≤ 2 * Real.log ((z₁ : ℝ) + 1) := by
      have hc : (z₀ : ℝ) ≤ ((z₁ : ℝ) + 1) ^ 2 := by exact_mod_cast hlt_sq.le
      calc Real.log (z₀ : ℝ) ≤ Real.log (((z₁ : ℝ) + 1) ^ 2) :=
            Real.log_le_log (by exact_mod_cast (by omega : 0 < z₀)) hc
        _ = 2 * Real.log ((z₁ : ℝ) + 1) := by rw [Real.log_pow]; norm_num
    have hz1R : (100 : ℝ) ≤ (z₁ : ℝ) := by exact_mod_cast hz1_ge100
    have hratio : Real.log ((z₁ : ℝ) + 1) - Real.log (z₁ : ℝ) ≤ 1 / 100 := by
      rw [← Real.log_div (by linarith) (by linarith)]
      have hle' := Real.log_le_sub_one_of_pos (by positivity : 0 < ((z₁ : ℝ) + 1) / (z₁ : ℝ))
      have hdiv : ((z₁ : ℝ) + 1) / (z₁ : ℝ) - 1 = 1 / (z₁ : ℝ) := by field_simp; ring
      rw [hdiv] at hle'
      exact hle'.trans (div_le_div_of_nonneg_left (by norm_num) (by linarith) hz1R)
    nlinarith
  have hlp_0 : ((99 / 100 : ℝ) * c₀) / Real.log (z₀ : ℝ) ≤ localProd z₀ :=
    (div_le_iff₀ hlog_z₀_pos).mpr (by linarith)
  have hlp_1 : localProd z₁ ≤ ((101 / 100 : ℝ) * c₀) / Real.log (z₁ : ℝ) :=
    (le_div_iff₀ hlog_z₁_pos).mpr (by linarith)
  have hratio_log : 1000 / 2005 ≤ Real.log (z₁ : ℝ) / Real.log (z₀ : ℝ) := by
    rw [div_le_div_iff₀ (by norm_num) hlog_z₀_pos]
    linarith
  have hPi_ge : (48 / 100 : ℝ) ≤ Pi_val := by
    rw [hPi_eq]
    calc (48 / 100 : ℝ) ≤ (99 / 101 : ℝ) * (1000 / 2005 : ℝ) := by norm_num
      _ ≤ (99 / 101 : ℝ) * (Real.log (z₁ : ℝ) / Real.log (z₀ : ℝ)) :=
          mul_le_mul_of_nonneg_left hratio_log (by norm_num)
      _ = (((99 / 100 : ℝ) * c₀) / Real.log (z₀ : ℝ)) /
            (((101 / 100 : ℝ) * c₀) / Real.log (z₁ : ℝ)) := by
          field_simp [hc₀_pos.ne', hlog_z₀_pos.ne', hlog_z₁_pos.ne']
      _ ≤ localProd z₀ / localProd z₁ :=
          div_le_div₀ (localProd_pos _).le hlp_0 (localProd_pos _) hlp_1
  have h5 : ∀ p ∈ split z₀ \ split z₁, 5 ≤ p := fun p hp =>
    (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).1).1
  have hlog_sum := sum_two_div_le_neg_log_prod h5
  have hneg : -Real.log Pi_val ≤ Real.log (25 / 12 : ℝ) := by
    have h1 : Real.log (48 / 100 : ℝ) ≤ Real.log Pi_val := Real.log_le_log (by norm_num) hPi_ge
    have h2 : -Real.log (48 / 100 : ℝ) = Real.log (25 / 12 : ℝ) := by
      rw [← Real.log_inv]; norm_num
    linarith
  exact ⟨hPi_ge, hlog_sum.trans (hneg.trans log_25_12_lt_three_fourths.le)⟩

/-! ### 6. Main Theorem Assembly -/

set_option maxHeartbeats 800000 in
theorem main_proof :
    let f := fun k : ℕ => 4*k^2+1; let block := fun x : ℕ => Finset.Ioc (x/2) x; let primes := fun z : ℕ => (Finset.Icc 3 z).filter (fun p => Nat.Prime p); let split := fun z : ℕ => (Finset.Icc 5 z).filter (fun p => Nat.Prime p ∧ p % 4 = 1); let wheel := fun z : ℕ => ∏ p ∈ primes z, p; let rough := fun x z : ℕ => (block x).filter (fun k => Nat.Coprime (f k) (wheel z)); let localProd := fun z : ℕ => ∏ p ∈ split z, (1 - 2/(p : ℝ)); (∃ c : ℝ, 0<c ∧ Filter.Tendsto (fun z : ℕ => Real.log (z : ℝ) * localProd z) Filter.atTop (nhds c)) →
    ∃ U : ℕ, 4≤U ∧ ∃ c : ℝ, 0<c ∧ ∃ X : ℕ, 2≤X ∧ ∀ x : ℕ, X≤x →
      let z := (Finset.range (x+1)).sup (fun t => if t^U≤x then t else 0);
      c*(x : ℝ)/Real.log x ≤ ((rough x z).card : ℝ) := by
  dsimp only
  rintro ⟨c₀, hc₀_pos, htend⟩
  change Filter.Tendsto (fun z : ℕ => Real.log (z : ℝ) * localProd z) Filter.atTop (nhds c₀) at htend
  -- Extract A₀ ≥ 100 where `log y * localProd y ∈ [0.99 c₀, 1.01 c₀]`
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N₁, hN₁⟩ := htend (c₀ / 100) (by positivity)
  let A0 : ℕ := max N₁ 100
  have hA0_ge100 : 100 ≤ A0 := le_max_right _ _
  have hA0_band : ∀ y : ℕ, A0 ≤ y →
      (99 / 100 : ℝ) * c₀ ≤ Real.log (y : ℝ) * localProd y ∧
        Real.log (y : ℝ) * localProd y ≤ (101 / 100 : ℝ) * c₀ := by
    intro y hy
    have hdist := hN₁ y ((le_max_left N₁ 100).trans hy)
    rw [Real.dist_eq, abs_lt] at hdist
    constructor <;> linarith
  -- Choose U = 24 and constant c = c₀ / 5
  refine ⟨24, by omega, c₀ / 5, by positivity, ?_⟩
  -- Define constant M₀ = splitWheel (A0^2) and explicit error coefficient
  let M0 : ℕ := splitWheel (A0 ^ 2)
  have hM0_pos : 0 < M0 := splitWheel_pos (A0 ^ 2)
  let C_rem : ℝ := 33 * (2 * (M0 : ℝ)) * (1 + Real.log (2 * (M0 : ℝ)) + 16)
  have hC_rem_nonneg : 0 ≤ C_rem := by
    have hM01 : (1 : ℝ) ≤ (M0 : ℝ) := by exact_mod_cast hM0_pos
    have hlogM : 0 ≤ Real.log (2 * (M0 : ℝ)) := Real.log_nonneg (by linarith)
    positivity
  -- Pick X large enough so `z ≥ A0^2` and `x^(1/4) ≥ 80 * C_rem / c₀`
  let K_thr : ℕ := Nat.ceil (80 * C_rem / c₀) + 1
  let X : ℕ := max (max ((A0 ^ 2) ^ 24) (K_thr ^ 4)) 1000
  refine ⟨X, by have := le_max_right (max ((A0 ^ 2) ^ 24) (K_thr ^ 4)) 1000; omega, ?_⟩
  intro x hx
  have hx1000 : 1000 ≤ x := (le_max_right _ 1000).trans hx
  have hxA : (A0 ^ 2) ^ 24 ≤ x :=
    (le_max_left _ (K_thr ^ 4)).trans ((le_max_left _ 1000).trans hx)
  have hxK : K_thr ^ 4 ≤ x :=
    (le_max_right _ (K_thr ^ 4)).trans ((le_max_left _ 1000).trans hx)
  -- Identify `z`
  set z : ℕ := (Finset.range (x + 1)).sup (fun t => if t ^ 24 ≤ x then t else 0) with hz_def
  have hz_le_x : z ≤ x := by
    rw [hz_def]
    refine Finset.sup_le ?_
    intro t ht
    split_ifs
    · exact Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    · omega
  have hz_ge_A0sq : A0 ^ 2 ≤ z := by
    have hmem : A0 ^ 2 ∈ Finset.range (x + 1) := by
      refine Finset.mem_range.mpr ?_
      have hle : A0 ^ 2 ≤ (A0 ^ 2) ^ 24 := Nat.le_self_pow (by omega) _
      omega
    have hle := Finset.le_sup (f := fun t => if t ^ 24 ≤ x then t else 0) hmem
    simp only [hxA, ↓reduceIte] at hle
    exact hle
  have hz_ge_10000 : 10000 ≤ z := by
    have : 100 ^ 2 ≤ A0 ^ 2 := Nat.pow_le_pow_left hA0_ge100 2
    omega
  have hz_pos : 1 ≤ z := by omega
  have hz_le_x_R : (z : ℝ) ≤ (x : ℝ) := by exact_mod_cast hz_le_x
  have hlogz_pos : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hlogx_pos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  -- Define `R` = max index `r ≤ z` with `A0 ≤ cut z r`
  let goodR := (Finset.range (z + 1)).filter (fun r => A0 ≤ cut z r)
  have h0_mem : 0 ∈ goodR := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    change A0 ≤ z
    have : A0 ≤ A0 ^ 2 := Nat.le_self_pow (by omega) _
    omega
  let R : ℕ := goodR.max' ⟨0, h0_mem⟩
  have hR_mem : R ∈ goodR := Finset.max'_mem goodR ⟨0, h0_mem⟩
  have hR_le_z : R ≤ z := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hR_mem).1)
  have hcutR_ge : A0 ≤ cut z R := (Finset.mem_filter.mp hR_mem).2
  have hcut_decr : ∀ r : ℕ, cut z r + r ≤ z ∨ cut z r ≤ 1 := by
    intro r
    induction r with
    | zero => left; simp [cut]
    | @succ r ih =>
        rcases ih with hle | h1
        · by_cases h2 : 2 ≤ cut z r
          · left
            have hlt : Nat.sqrt (cut z r) < cut z r := Nat.sqrt_lt'.mpr (by nlinarith)
            change Nat.sqrt (cut z r) + (r + 1) ≤ z
            omega
          · right
            have hle1 : cut z r ≤ 1 := by omega
            have hsq := cut_antitone z r
            omega
        · right
          have hsq := cut_antitone z r
          omega
  have hcut_z_lt : cut z z < A0 := by
    rcases hcut_decr z with hle | h1
    · have : cut z z = 0 := by omega
      omega
    · omega
  have hR_lt_z : R < z := by
    by_contra hge
    have heq : R = z := by omega
    rw [heq] at hcutR_ge
    omega
  have hR1_mem_range : R + 1 ∈ Finset.range (z + 1) := Finset.mem_range.mpr (by omega)
  have hcutR1_lt : cut z (R + 1) < A0 := by
    by_contra hge
    have hm : R + 1 ∈ goodR := Finset.mem_filter.mpr ⟨hR1_mem_range, by omega⟩
    have hle := Finset.le_max' goodR (R + 1) hm
    omega
  have hcutR_le_A0sq : cut z R ≤ A0 ^ 2 := by
    have hlt_sq : cut z R < (cut z (R + 1) + 1) ^ 2 := Nat.lt_succ_sqrt' (cut z R)
    have hsq_le : (cut z (R + 1) + 1) ^ 2 ≤ A0 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  -- Check R ≥ 1 (since cut z 1 = Nat.sqrt z ≥ A0)
  have hR_pos : 1 ≤ R := by
    have h1_mem : 1 ∈ goodR := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
      change A0 ≤ Nat.sqrt z
      exact Nat.le_sqrt.mpr (by simpa [sq] using hz_ge_A0sq)
    exact Finset.le_max' goodR 1 h1_mem
  -- Bound R via 2^r * cut z r ≤ z
  have hpow2R : 2 ^ R * cut z R ≤ z := by
    suffices hgen : ∀ r, r ≤ R → 2 ^ r * cut z r ≤ z from hgen R le_rfl
    intro r hr
    induction r with
    | zero => simp [cut]
    | @succ r ih =>
        have hrR : r ≤ R := by omega
        have h4 : 4 ≤ cut z r := by
          have := cut_le z hrR
          omega
        have hstep := cut_strict_half h4
        calc 2 ^ (r + 1) * cut z (r + 1) = 2 ^ r * (2 * cut z (r + 1)) := by ring
          _ ≤ 2 ^ r * cut z r := Nat.mul_le_mul_left _ hstep
          _ ≤ z := ih hrR
  have hR_le_2logx : (R : ℝ) ≤ 2 * Real.log (x : ℝ) := by
    have h2R_le_x : ((2 ^ R : ℕ) : ℝ) ≤ (x : ℝ) := by
      have hnat : 2 ^ R ≤ x := by
        have h1 : 2 ^ R ≤ 2 ^ R * cut z R := Nat.le_mul_of_pos_right _ (by omega)
        omega
      exact_mod_cast hnat
    have hlog2R : (R : ℝ) * Real.log 2 ≤ Real.log (x : ℝ) := by
      calc (R : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ R) := by rw [Real.log_pow]
        _ ≤ Real.log (x : ℝ) := Real.log_le_log (by positivity) (by simpa using h2R_le_x)
    have hhalf := one_half_lt_log_two
    have hR0 : 0 ≤ (R : ℝ) := Nat.cast_nonneg R
    nlinarith
  -- Define disjoint partition `T j` (`j < R`) and `Tbase`
  let T : ℕ → Finset ℕ := fun j => if j < R then split (cut z j) \ split (cut z (j + 1)) else ∅
  let Tbase : Finset ℕ := split (cut z R)
  have hT_prime : ∀ j, ∀ p ∈ T j, p.Prime := by
    intro j p hp
    dsimp only [T] at hp
    split_ifs at hp
    · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2.1
    · simp at hp
  have hT_split : ∀ j, ∀ p ∈ T j, p.Prime ∧ p % 4 = 1 := by
    intro j p hp
    dsimp only [T] at hp
    split_ifs at hp
    · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2
    · simp at hp
  have hT_sub : ∀ j, T j ⊆ split (cut z j) := by
    intro j
    dsimp only [T]
    split_ifs
    · exact Finset.sdiff_subset
    · exact Finset.empty_subset _
  have hTbase_prime : ∀ p ∈ Tbase, p.Prime := fun p hp =>
    (Finset.mem_filter.mp hp).2.1
  have hTbase_split : ∀ p ∈ Tbase, p.Prime ∧ p % 4 = 1 := fun p hp =>
    (Finset.mem_filter.mp hp).2
  have hTbase_sub : Tbase ⊆ split (cut z R) := le_rfl
  have hdisj_base : ∀ j, Disjoint (T j) Tbase := by
    intro j
    dsimp only [T]
    split_ifs with hj
    · refine Finset.disjoint_left.mpr ?_
      intro p hp1 hp2
      have hnot : p ∉ split (cut z (j + 1)) := (Finset.mem_sdiff.mp hp1).2
      have hsub : split (cut z R) ⊆ split (cut z (j + 1)) := split_mono (cut_le z (by omega))
      exact hnot (hsub hp2)
    · exact Finset.disjoint_empty_left _
  have hdisj_T : ∀ i j, i ≠ j → Disjoint (T i) (T j) := by
    intro i j hij
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · dsimp only [T]
      split_ifs with hi hj
      · refine Finset.disjoint_left.mpr ?_
        intro p hpi hpj
        have hnot : p ∉ split (cut z (i + 1)) := (Finset.mem_sdiff.mp hpi).2
        have hsub : split (cut z j) ⊆ split (cut z (i + 1)) := split_mono (cut_le z (by omega))
        exact hnot (hsub (Finset.mem_sdiff.mp hpj).1)
      · exact Finset.disjoint_empty_right _
      · exact Finset.disjoint_empty_left _
      · exact Finset.disjoint_empty_left _
    · exact absurd rfl hij
    · dsimp only [T]
      split_ifs with hi hj
      · refine Finset.disjoint_left.mpr ?_
        intro p hpi hpj
        have hnot : p ∉ split (cut z (j + 1)) := (Finset.mem_sdiff.mp hpj).2
        have hsub : split (cut z i) ⊆ split (cut z (j + 1)) := split_mono (cut_le z (by omega))
        exact hnot (hsub (Finset.mem_sdiff.mp hpi).1)
      · exact Finset.disjoint_empty_right _
      · exact Finset.disjoint_empty_left _
      · exact Finset.disjoint_empty_left _
  -- Verify `Tbase ∪ (range R).biUnion T = split z`
  have hunion_split : Tbase ∪ (Finset.range R).biUnion T = split z := by
    suffices hgen : ∀ k ≤ R, split (cut z k) ∪ (Finset.range k).biUnion T = split z from hgen R le_rfl
    intro k hk
    induction k with
    | zero => simp [cut]
    | @succ k ih =>
        have hkR : k ≤ R := by omega
        have hklt : k < R := by omega
        rw [Finset.range_add_one, Finset.biUnion_insert]
        have hTk : T k = split (cut z k) \ split (cut z (k + 1)) := if_pos hklt
        have hsub : split (cut z (k + 1)) ⊆ split (cut z k) := split_mono (cut_antitone z k)
        have hstep : split (cut z (k + 1)) ∪ T k = split (cut z k) := by
          rw [hTk]
          exact Finset.union_sdiff_of_subset hsub
        calc split (cut z (k + 1)) ∪ (T k ∪ (Finset.range k).biUnion T)
            = (split (cut z (k + 1)) ∪ T k) ∪ (Finset.range k).biUnion T := by rw [Finset.union_assoc]
          _ = split (cut z k) ∪ (Finset.range k).biUnion T := by rw [hstep]
          _ = split z := ih hkR
  -- Pointwise lower sieve inequality for every `k`
  let cap : ℕ → ℕ := fun j => 2 * (j + 2)
  let G : Finset (Finset ℕ) := goodSeq R T Tbase cap
  let E : ℕ → Finset (Finset ℕ) := fun r => errSeq r R T Tbase cap
  have hpointwise : ∀ k : ℕ,
      (if Nat.Coprime (f k) (wheel z) then (1 : ℝ) else 0) ≥
        (∑ A ∈ G, (-1 : ℝ) ^ A.card * (if (∏ p ∈ A, p) ∣ f k then (1 : ℝ) else 0)) -
          ∑ r ∈ Finset.range R,
            ∑ A ∈ E r, (-1 : ℝ) ^ A.card * (if (∏ p ∈ A, p) ∣ f k then (1 : ℝ) else 0) := by
    intro k
    have hcop_iff : Nat.Coprime (f k) (wheel z) ↔ (split z).filter (fun p => p ∣ f k) = ∅ := by
      rw [coprime_wheel_iff_coprime_splitWheel, coprime_splitWheel_iff_forall_not_dvd,
        Finset.filter_eq_empty_iff]
    have hind_eq : (if Nat.Coprime (f k) (wheel z) then (1 : ℝ) else 0) =
        (∏ j ∈ Finset.range R, indCoprime (T j) (f k)) * indCoprime Tbase (f k) := by
      simp only [hcop_iff]
      by_cases hemp : (split z).filter (fun p => p ∣ f k) = ∅
      · rw [if_pos hemp]
        have he1 : ∀ j ∈ Finset.range R, indCoprime (T j) (f k) = 1 := by
          intro j hj
          unfold indCoprime
          rw [if_pos]
          ext p
          simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro hpT hdvd
          have hpS : p ∈ split z := by
            rw [← hunion_split]
            exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hj, hpT⟩)
          have hmem : p ∈ (split z).filter (fun q => q ∣ f k) := Finset.mem_filter.mpr ⟨hpS, hdvd⟩
          rw [hemp] at hmem
          exact Finset.notMem_empty p hmem
        have he2 : indCoprime Tbase (f k) = 1 := by
          unfold indCoprime
          rw [if_pos]
          ext p
          simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro hpB hdvd
          have hpS : p ∈ split z := by
            rw [← hunion_split]
            exact Finset.mem_union_left _ hpB
          have hmem : p ∈ (split z).filter (fun q => q ∣ f k) := Finset.mem_filter.mpr ⟨hpS, hdvd⟩
          rw [hemp] at hmem
          exact Finset.notMem_empty p hmem
        rw [Finset.prod_eq_one he1, he2, mul_one]
      · rw [if_neg hemp]
        obtain ⟨p0, hp0⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
        have hp0S := (Finset.mem_filter.mp hp0).1
        have hp0d := (Finset.mem_filter.mp hp0).2
        rw [← hunion_split] at hp0S
        rcases Finset.mem_union.mp hp0S with hpB | hpi
        · have he2 : indCoprime Tbase (f k) = 0 := by
            unfold indCoprime
            rw [if_neg]
            exact Finset.nonempty_iff_ne_empty.mp ⟨p0, Finset.mem_filter.mpr ⟨hpB, hp0d⟩⟩
          rw [he2, mul_zero]
        · rcases Finset.mem_biUnion.mp hpi with ⟨j0, hj0, hpT⟩
          have hej0 : indCoprime (T j0) (f k) = 0 := by
            unfold indCoprime
            rw [if_neg]
            exact Finset.nonempty_iff_ne_empty.mp ⟨p0, Finset.mem_filter.mpr ⟨hpT, hp0d⟩⟩
          rw [Finset.prod_eq_zero hj0 hej0, zero_mul]
    have hdiff := prod_diff_le_sum_diff R
      (fun j => indCoprime (T j) (f k))
      (fun j => truncSum (T j) (cap j) (f k))
      (fun j => truncSum (T j) (cap j - 1) (f k))
      (indCoprime Tbase (f k))
      (indCoprime_nonneg Tbase (f k))
      (fun j _ => ⟨indCoprime_nonneg (T j) (f k),
        indCoprime_le_truncSum_even (hT_prime j) (j + 2) (f k),
        truncSum_odd_le_indCoprime (hT_prime j) (by omega) (f k)⟩)
    let g_k : Finset ℕ → ℝ := fun A => (-1 : ℝ) ^ A.card * (if ∀ p ∈ A, p ∣ f k then (1 : ℝ) else 0)
    have hg_k : ∀ B C, Disjoint B C → g_k (B ∪ C) = g_k B * g_k C := by
      intro B C hBC
      dsimp only [g_k]
      rw [Finset.card_union_of_disjoint hBC, pow_add]
      have hiff : (∀ p ∈ B ∪ C, p ∣ f k) ↔ (∀ p ∈ B, p ∣ f k) ∧ (∀ p ∈ C, p ∣ f k) := by
        simp only [Finset.mem_union]
        exact ⟨fun h => ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩,
          fun ⟨hB, hC⟩ p hp => hp.elim (hB p) (hC p)⟩
      by_cases hB : ∀ p ∈ B, p ∣ f k <;> by_cases hC : ∀ p ∈ C, p ∣ f k
      · rw [if_pos hB, if_pos hC, if_pos (hiff.mpr ⟨hB, hC⟩)]; ring
      · rw [if_pos hB, if_neg hC, if_neg (fun h => hC (hiff.mp h).2)]; ring
      · rw [if_neg hB, if_pos hC, if_neg (fun h => hB (hiff.mp h).1)]; ring
      · rw [if_neg hB, if_neg hC, if_neg (fun h => hB (hiff.mp h).1)]; ring
    have hU_eq : ∀ j, truncSum (T j) (cap j) (f k) =
        ∑ B ∈ (T j).powerset.filter (fun B => B.card ≤ cap j), g_k B := by
      intro j
      unfold truncSum
      apply Finset.sum_congr rfl
      intro B hB
      have hBp : ∀ p ∈ B, p.Prime := fun p hp =>
        hT_prime j p ((Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1) hp)
      simp only [g_k, prod_primes_dvd_iff' hBp (f k)]
      split_ifs <;> ring
    have hUL_eq : ∀ j, truncSum (T j) (cap j) (f k) - truncSum (T j) (cap j - 1) (f k) =
        ∑ B ∈ (T j).powerset.filter (fun B => B.card = cap j), g_k B := by
      intro j
      have hcapj : cap j = 2 * (j + 2) := rfl
      rw [hcapj, truncSum_even_sub_odd (T j) (by omega : 1 ≤ j + 2) (f k)]
      apply Finset.sum_congr rfl
      intro B hB
      have hBp : ∀ p ∈ B, p.Prime := fun p hp =>
        hT_prime j p ((Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1) hp)
      simp only [g_k, prod_primes_dvd_iff' hBp (f k)]
      split_ifs <;> ring
    have hbase_eq : indCoprime Tbase (f k) = ∑ A ∈ Tbase.powerset, g_k A := by
      rw [← truncSum_full_eq_indCoprime hTbase_prime (f k)]
      unfold truncSum
      have hfilt : Tbase.powerset.filter (fun A => A.card ≤ Tbase.card) = Tbase.powerset := by
        ext A; simp only [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨fun h => h.1, fun h => ⟨h, Finset.card_le_card h⟩⟩
      rw [hfilt]
      apply Finset.sum_congr rfl
      intro A hA
      have hAp : ∀ p ∈ A, p.Prime := fun p hp => hTbase_prime p (Finset.mem_powerset.mp hA hp)
      simp only [g_k, prod_primes_dvd_iff' hAp (f k)]
      split_ifs <;> ring
    have hprod_good : (∏ j ∈ Finset.range R, truncSum (T j) (cap j) (f k)) * indCoprime Tbase (f k) =
        ∑ A ∈ G, (-1 : ℝ) ^ A.card * (if (∏ p ∈ A, p) ∣ f k then (1 : ℝ) else 0) := by
      rw [hbase_eq]
      simp_rw [hU_eq]
      rw [← sum_goodSeq_eq_prod R T Tbase cap hdisj_base hdisj_T g_k hg_k]
      apply Finset.sum_congr rfl
      intro A hA
      have hAsub : A ⊆ split z := by
        rw [← hunion_split]
        exact goodSeq_subset_union R T Tbase cap hA
      have hAp : ∀ p ∈ A, p.Prime := fun p hp => (Finset.mem_filter.mp (hAsub hp)).2.1
      simp only [g_k, prod_primes_dvd_iff' hAp (f k)]
    have hprod_err : ∀ r ∈ Finset.range R,
        (truncSum (T r) (cap r) (f k) - truncSum (T r) (cap r - 1) (f k)) *
          (∏ j ∈ (Finset.range R).erase r, truncSum (T j) (cap j) (f k)) *
          indCoprime Tbase (f k) =
        ∑ A ∈ E r, (-1 : ℝ) ^ A.card * (if (∏ p ∈ A, p) ∣ f k then (1 : ℝ) else 0) := by
      intro r hr
      rw [hUL_eq r, hbase_eq]
      simp_rw [hU_eq]
      rw [← sum_errSeq_eq_prod (Finset.mem_range.mp hr) T Tbase cap hdisj_base hdisj_T g_k hg_k]
      apply Finset.sum_congr rfl
      intro A hA
      have hAsub : A ⊆ split z := by
        rw [← hunion_split]
        exact goodSeq_subset_union R T Tbase cap (errSeq_subset_goodSeq r R T Tbase cap hA)
      have hAp : ∀ p ∈ A, p.Prime := fun p hp => (Finset.mem_filter.mp (hAsub hp)).2.1
      simp only [g_k, prod_primes_dvd_iff' hAp (f k)]
    have hsum_err : (∑ r ∈ Finset.range R,
        (truncSum (T r) (cap r) (f k) - truncSum (T r) (cap r - 1) (f k)) *
          (∏ j ∈ (Finset.range R).erase r, truncSum (T j) (cap j) (f k))) *
          indCoprime Tbase (f k) =
        ∑ r ∈ Finset.range R,
          ∑ A ∈ E r, (-1 : ℝ) ^ A.card * (if (∏ p ∈ A, p) ∣ f k then (1 : ℝ) else 0) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl hprod_err
    rw [hind_eq, ← hprod_good, ← hsum_err]
    linarith
  -- Sum `hpointwise` over `k ∈ block x`
  have hrough_ge : ((rough x z).card : ℝ) ≥
      (∑ A ∈ G, (-1 : ℝ) ^ A.card * (count (x / 2) x (∏ p ∈ A, p) : ℝ)) -
        ∑ r ∈ Finset.range R,
          ∑ A ∈ E r, (-1 : ℝ) ^ A.card * (count (x / 2) x (∏ p ∈ A, p) : ℝ) := by
    have hsum_rough : ((rough x z).card : ℝ) =
        ∑ k ∈ block x, (if Nat.Coprime (f k) (wheel z) then (1 : ℝ) else 0) := by
      unfold rough
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hG_sum : ∑ k ∈ block x, ∑ A ∈ G, (-1 : ℝ) ^ A.card * (if (∏ p ∈ A, p) ∣ f k then (1 : ℝ) else 0) =
        ∑ A ∈ G, (-1 : ℝ) ^ A.card * (count (x / 2) x (∏ p ∈ A, p) : ℝ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A _
      rw [← Finset.mul_sum]
      congr 1
      unfold count block f
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hE_sum : ∑ k ∈ block x, ∑ r ∈ Finset.range R,
          ∑ A ∈ E r, (-1 : ℝ) ^ A.card * (if (∏ p ∈ A, p) ∣ f k then (1 : ℝ) else 0) =
        ∑ r ∈ Finset.range R,
          ∑ A ∈ E r, (-1 : ℝ) ^ A.card * (count (x / 2) x (∏ p ∈ A, p) : ℝ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A _
      rw [← Finset.mul_sum]
      congr 1
      unfold count block f
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hsum_rough, ← hG_sum, ← hE_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun k _ => hpointwise k)
  -- Separate main term and remainder using `SieveDivisorRemainders`
  let D_max : ℕ := M0 * (Nat.sqrt x + 1)
  have hD_pos : 1 ≤ D_max := by
    have hsq : 1 ≤ Nat.sqrt x + 1 := by omega
    exact Nat.mul_pos hM0_pos hsq
  let len : ℝ := ((x - x / 2 : ℕ) : ℝ)
  let main_coeff : ℝ :=
    (∑ A ∈ G, (-1 : ℝ) ^ A.card * (rho (∏ p ∈ A, p) / ((∏ p ∈ A, p : ℕ) : ℝ))) -
      ∑ r ∈ Finset.range R,
        ∑ A ∈ E r, (-1 : ℝ) ^ A.card * (rho (∏ p ∈ A, p) / ((∏ p ∈ A, p : ℕ) : ℝ))
  let remA : Finset ℕ → ℝ := fun A =>
    |(count (x / 2) x (∏ p ∈ A, p) : ℝ) - len * rho (∏ p ∈ A, p) / ((∏ p ∈ A, p : ℕ) : ℝ)|
  have hsplit_err : len * main_coeff - ((rough x z).card : ℝ) ≤ (1 + (R : ℝ)) * ∑ A ∈ G, remA A := by
    have hdiff : len * main_coeff -
        ((∑ A ∈ G, (-1 : ℝ) ^ A.card * (count (x / 2) x (∏ p ∈ A, p) : ℝ)) -
          ∑ r ∈ Finset.range R,
            ∑ A ∈ E r, (-1 : ℝ) ^ A.card * (count (x / 2) x (∏ p ∈ A, p) : ℝ)) =
        (∑ A ∈ G, (-1 : ℝ) ^ A.card *
          (len * rho (∏ p ∈ A, p) / ((∏ p ∈ A, p : ℕ) : ℝ) - (count (x / 2) x (∏ p ∈ A, p) : ℝ))) -
        ∑ r ∈ Finset.range R,
          ∑ A ∈ E r, (-1 : ℝ) ^ A.card *
            (len * rho (∏ p ∈ A, p) / ((∏ p ∈ A, p : ℕ) : ℝ) - (count (x / 2) x (∏ p ∈ A, p) : ℝ)) := by
      have hG_diff : len * (∑ A ∈ G, (-1 : ℝ) ^ A.card * (rho (∏ p ∈ A, p) / ((∏ p ∈ A, p : ℕ) : ℝ))) -
          ∑ A ∈ G, (-1 : ℝ) ^ A.card * (count (x / 2) x (∏ p ∈ A, p) : ℝ) =
          ∑ A ∈ G, (-1 : ℝ) ^ A.card *
            (len * rho (∏ p ∈ A, p) / ((∏ p ∈ A, p : ℕ) : ℝ) - (count (x / 2) x (∏ p ∈ A, p) : ℝ)) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro A _; ring
      have hE_diff : len * (∑ r ∈ Finset.range R,
            ∑ A ∈ E r, (-1 : ℝ) ^ A.card * (rho (∏ p ∈ A, p) / ((∏ p ∈ A, p : ℕ) : ℝ))) -
          ∑ r ∈ Finset.range R,
            ∑ A ∈ E r, (-1 : ℝ) ^ A.card * (count (x / 2) x (∏ p ∈ A, p) : ℝ) =
          ∑ r ∈ Finset.range R,
            ∑ A ∈ E r, (-1 : ℝ) ^ A.card *
              (len * rho (∏ p ∈ A, p) / ((∏ p ∈ A, p : ℕ) : ℝ) - (count (x / 2) x (∏ p ∈ A, p) : ℝ)) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro r _
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro A _; ring
      dsimp only [main_coeff]
      linarith
    have hle_abs : ∀ S : Finset (Finset ℕ),
        |∑ A ∈ S, (-1 : ℝ) ^ A.card *
          (len * rho (∏ p ∈ A, p) / ((∏ p ∈ A, p : ℕ) : ℝ) - (count (x / 2) x (∏ p ∈ A, p) : ℝ))| ≤
          ∑ A ∈ S, remA A := by
      intro S
      calc |∑ A ∈ S, _| ≤ ∑ A ∈ S, |(-1 : ℝ) ^ A.card *
            (len * rho (∏ p ∈ A, p) / ((∏ p ∈ A, p : ℕ) : ℝ) - (count (x / 2) x (∏ p ∈ A, p) : ℝ))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ A ∈ S, remA A := by
            apply Finset.sum_congr rfl
            intro A _
            rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_sub_comm]
    have hE_le : ∀ r ∈ Finset.range R, ∑ A ∈ E r, remA A ≤ ∑ A ∈ G, remA A := by
      intro r _
      exact Finset.sum_le_sum_of_subset_of_nonneg (errSeq_subset_goodSeq r R T Tbase cap)
        (fun A _ _ => abs_nonneg _)
    calc len * main_coeff - ((rough x z).card : ℝ)
        ≤ len * main_coeff -
          ((∑ A ∈ G, (-1 : ℝ) ^ A.card * (count (x / 2) x (∏ p ∈ A, p) : ℝ)) -
            ∑ r ∈ Finset.range R,
              ∑ A ∈ E r, (-1 : ℝ) ^ A.card * (count (x / 2) x (∏ p ∈ A, p) : ℝ)) := by
          linarith
      _ = (∑ A ∈ G, _) - ∑ r ∈ Finset.range R, ∑ A ∈ E r, _ := hdiff
      _ ≤ |∑ A ∈ G, _| + ∑ r ∈ Finset.range R, |∑ A ∈ E r, _| := by
          have h1 := le_abs_self (∑ A ∈ G, (-1 : ℝ) ^ A.card *
            (len * rho (∏ p ∈ A, p) / ((∏ p ∈ A, p : ℕ) : ℝ) - (count (x / 2) x (∏ p ∈ A, p) : ℝ)))
          have h2 : - ∑ r ∈ Finset.range R, ∑ A ∈ E r, (-1 : ℝ) ^ A.card *
              (len * rho (∏ p ∈ A, p) / ((∏ p ∈ A, p : ℕ) : ℝ) - (count (x / 2) x (∏ p ∈ A, p) : ℝ)) ≤
              ∑ r ∈ Finset.range R, |∑ A ∈ E r, (-1 : ℝ) ^ A.card *
                (len * rho (∏ p ∈ A, p) / ((∏ p ∈ A, p : ℕ) : ℝ) - (count (x / 2) x (∏ p ∈ A, p) : ℝ))| := by
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_le_sum (fun r _ => neg_le_abs _)
          linarith
      _ ≤ (∑ A ∈ G, remA A) + ∑ _r ∈ Finset.range R, ∑ A ∈ G, remA A := add_le_add
          (hle_abs G) (Finset.sum_le_sum (fun r hr => (hle_abs (E r)).trans (hE_le r hr)))
      _ = (1 + (R : ℝ)) * ∑ A ∈ G, remA A := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  -- Bound `∑ A ∈ G, remA A` via `Conjectures.QuadraticPrimes.SieveDivisorRemainders`
  have hSieveDiv := Conjectures.QuadraticPrimes.SieveDivisorRemainders (x / 2) x D_max
    (Nat.div_le_self x 2) hD_pos
  dsimp only at hSieveDiv
  have hz_12_le_sqrt : (z : ℝ) ^ (12 : ℝ) ≤ Real.sqrt (x : ℝ) := by
    have hz24 : z ^ 24 ≤ x := by
      have hex : ∃ t ∈ Finset.range (x + 1), (if t ^ 24 ≤ x then t else 0) = z := by
        have hne : (Finset.range (x + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
        obtain ⟨t0, ht0_mem, ht0⟩ := Finset.exists_mem_eq_sup (Finset.range (x + 1)) hne
          (fun t => if t ^ 24 ≤ x then t else 0)
        rw [← hz_def] at ht0
        exact ⟨t0, ht0_mem, ht0.symm⟩
      rcases hex with ⟨t, _, ht⟩
      by_cases hc : t ^ 24 ≤ x
      · simp only [hc, ↓reduceIte] at ht; rw [← ht]; exact hc
      · simp only [hc, ↓reduceIte] at ht; omega
    have hsqR : ((z : ℝ) ^ (12 : ℝ)) ^ 2 ≤ (x : ℝ) := by
      have hcast : ((z : ℝ) ^ (12 : ℕ)) ^ 2 ≤ (x : ℝ) := by
        have hnat : (z ^ 12) ^ 2 = z ^ 24 := by ring
        exact_mod_cast (hnat ▸ hz24)
      simpa [Real.rpow_natCast] using hcast
    exact Real.le_sqrt_of_sq_le hsqR
  have hsum_rem_le : ∑ A ∈ G, remA A ≤ (D_max : ℝ) * (1 + Real.log (D_max : ℝ)) := by
    let errFn : ℕ → ℝ := fun d => |(count (x / 2) x d : ℝ) - len * rho d / (d : ℝ)|
    have hinjG : Set.InjOn (fun A => ∏ p ∈ A, p) (G : Set (Finset ℕ)) := by
      intro A₁ hA₁ A₂ hA₂ heq
      dsimp only at heq
      have hA₁sub : A₁ ⊆ split z := (goodSeq_subset_union R T Tbase cap hA₁).trans (by rw [hunion_split])
      have hA₂sub : A₂ ⊆ split z := (goodSeq_subset_union R T Tbase cap hA₂).trans (by rw [hunion_split])
      have h1 : ∀ p ∈ A₁, p.Prime := fun p hp => (Finset.mem_filter.mp (hA₁sub hp)).2.1
      have h2 : ∀ p ∈ A₂, p.Prime := fun p hp => (Finset.mem_filter.mp (hA₂sub hp)).2.1
      calc A₁ = (∏ p ∈ A₁, p).primeFactors := (prod_primes_primeFactors h1).symm
        _ = (∏ p ∈ A₂, p).primeFactors := by rw [heq]
        _ = A₂ := prod_primes_primeFactors h2
    have hsubG : G.image (fun A => ∏ p ∈ A, p) ⊆
        (Finset.Icc 1 D_max).filter (fun d => Odd d ∧ Squarefree d) := by
      intro d hd
      rcases Finset.mem_image.mp hd with ⟨A, hA, rfl⟩
      have hAsub : A ⊆ split z := (goodSeq_subset_union R T Tbase cap hA).trans (by rw [hunion_split])
      have hAp : ∀ p ∈ A, p.Prime := fun p hp => (Finset.mem_filter.mp (hAsub hp)).2.1
      have hAp3 : ∀ p ∈ A, p.Prime ∧ 3 ≤ p := fun p hp =>
        ⟨hAp p hp, by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hAsub hp)).1).1; omega⟩
      have hprod_ge1 : 1 ≤ ∏ p ∈ A, p := Finset.prod_pos (fun p hp => (hAp p hp).pos)
      have hprod_le_R : ((∏ p ∈ A, p : ℕ) : ℝ) ≤ (D_max : ℝ) := by
        have hg := goodSeq_prod_le hz_pos A0 hcutR_le_A0sq T hT_sub Tbase hTbase_sub cap (fun _ => rfl) hA
        have hsqrt_le : Real.sqrt (x : ℝ) ≤ (Nat.sqrt x + 1 : ℝ) := by
          have hlt : (x : ℝ) < ((Nat.sqrt x + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast Nat.lt_succ_sqrt' x
          exact (Real.sqrt_lt' (by positivity)).mpr (by simpa using hlt) |>.le
        calc ((∏ p ∈ A, p : ℕ) : ℝ) ≤ (M0 : ℝ) * (z : ℝ) ^ (12 : ℝ) := hg
          _ ≤ (M0 : ℝ) * Real.sqrt (x : ℝ) := mul_le_mul_of_nonneg_left hz_12_le_sqrt (Nat.cast_nonneg _)
          _ ≤ (M0 : ℝ) * (Nat.sqrt x + 1 : ℝ) := mul_le_mul_of_nonneg_left hsqrt_le (Nat.cast_nonneg _)
          _ = (D_max : ℝ) := by dsimp [D_max]; push_cast; ring
      have hprod_le : ∏ p ∈ A, p ≤ D_max := by exact_mod_cast hprod_le_R
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hprod_ge1, hprod_le⟩,
        prod_primes_odd hAp3, prod_primes_squarefree hAp⟩
    have hmap : ∑ A ∈ G, remA A ≤
        ∑ d ∈ (Finset.Icc 1 D_max).filter (fun d => Odd d ∧ Squarefree d), errFn d := by
      have hsum_img : ∑ A ∈ G, remA A = ∑ d ∈ G.image (fun A => ∏ p ∈ A, p), errFn d :=
        (Finset.sum_image (f := errFn) hinjG).symm
      rw [hsum_img]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubG (fun d _ _ => abs_nonneg _)
    exact hmap.trans hSieveDiv
  -- Lower bound `main_coeff` using Brun's geometric-interval bounds
  let w : ℕ → ℝ := fun p => 2 / (p : ℝ)
  have hw_split : ∀ p ∈ split z, 0 ≤ w p ∧ w p ≤ 1 := by
    intro p hp
    have hp5 : (5 : ℝ) ≤ p := by
      exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    dsimp only [w]
    constructor
    · positivity
    · exact div_le_one_of_le₀ (by linarith) (by positivity)
  have hmain_factor : main_coeff =
      ((∏ j ∈ Finset.range R, wTrunc (T j) w (cap j)) -
        ∑ r ∈ Finset.range R, wElem (T r) w (cap r) *
          (∏ j ∈ (Finset.range R).erase r, wTrunc (T j) w (cap j))) *
        (∏ p ∈ Tbase, (1 - w p)) := by
    let g_m : Finset ℕ → ℝ := fun A => (-1 : ℝ) ^ A.card * ∏ p ∈ A, w p
    have hg_m : ∀ B C, Disjoint B C → g_m (B ∪ C) = g_m B * g_m C := by
      intro B C hBC
      dsimp only [g_m]
      rw [Finset.card_union_of_disjoint hBC, Finset.prod_union hBC, pow_add]
      ring
    have hG_m : ∑ A ∈ G, (-1 : ℝ) ^ A.card * (rho (∏ p ∈ A, p) / ((∏ p ∈ A, p : ℕ) : ℝ)) =
        (∏ j ∈ Finset.range R, wTrunc (T j) w (cap j)) * (∏ p ∈ Tbase, (1 - w p)) := by
      calc ∑ A ∈ G, (-1 : ℝ) ^ A.card * (rho (∏ p ∈ A, p) / ((∏ p ∈ A, p : ℕ) : ℝ))
          = ∑ A ∈ G, g_m A := by
            apply Finset.sum_congr rfl
            intro A hA
            have hAsub : A ⊆ split z := (goodSeq_subset_union R T Tbase cap hA).trans (by rw [hunion_split])
            rw [rho_prod_split (fun p hp => (Finset.mem_filter.mp (hAsub hp)).2)]
        _ = (∏ j ∈ Finset.range R, wTrunc (T j) w (cap j)) * ∑ A ∈ Tbase.powerset, g_m A :=
            sum_goodSeq_eq_prod R T Tbase cap hdisj_base hdisj_T g_m hg_m
        _ = (∏ j ∈ Finset.range R, wTrunc (T j) w (cap j)) * (∏ p ∈ Tbase, (1 - w p)) := by
            rw [sum_powerset_eq_prod_one_sub]
    have hE_m : ∀ r ∈ Finset.range R,
        ∑ A ∈ E r, (-1 : ℝ) ^ A.card * (rho (∏ p ∈ A, p) / ((∏ p ∈ A, p : ℕ) : ℝ)) =
          wElem (T r) w (cap r) * (∏ j ∈ (Finset.range R).erase r, wTrunc (T j) w (cap j)) *
            (∏ p ∈ Tbase, (1 - w p)) := by
      intro r hr
      have h1 : ∑ A ∈ E r, (-1 : ℝ) ^ A.card * (rho (∏ p ∈ A, p) / ((∏ p ∈ A, p : ℕ) : ℝ)) =
          ∑ A ∈ E r, g_m A := by
        apply Finset.sum_congr rfl
        intro A hA
        have hAsub : A ⊆ split z :=
          (goodSeq_subset_union R T Tbase cap (errSeq_subset_goodSeq r R T Tbase cap hA)).trans
            (by rw [hunion_split])
        rw [rho_prod_split (fun p hp => (Finset.mem_filter.mp (hAsub hp)).2)]
      have h2 := sum_errSeq_eq_prod (Finset.mem_range.mp hr) T Tbase cap hdisj_base hdisj_T g_m hg_m
      have h3 : (∑ B ∈ (T r).powerset.filter (fun B => B.card = cap r), g_m B) = wElem (T r) w (cap r) := by
        unfold wElem
        apply Finset.sum_congr rfl
        intro B hB
        have hc : B.card = cap r := (Finset.mem_filter.mp hB).2
        have heven : (-1 : ℝ) ^ B.card = 1 := by
          rw [hc]; change (-1 : ℝ) ^ (2 * (r + 2)) = 1; simp [pow_mul]
        dsimp only [g_m]
        rw [heven, one_mul]
      have hwT : ∀ j, (∑ B ∈ (T j).powerset.filter (fun B => B.card ≤ cap j), g_m B) =
          wTrunc (T j) w (cap j) := fun _ => rfl
      have h4 : ∑ A ∈ Tbase.powerset, g_m A = ∏ p ∈ Tbase, (1 - w p) :=
        sum_powerset_eq_prod_one_sub Tbase w
      dsimp only [E]
      rw [h1, h2, h3, h4]
      simp_rw [hwT]
    dsimp only [main_coeff]
    rw [hG_m, Finset.sum_congr rfl hE_m, ← Finset.sum_mul, sub_mul]
  -- Bound each interval factor `Pi_j ≥ 48/100` and `S_j ≤ 3/4` for `j < R`
  let Pi_j : ℕ → ℝ := fun j => ∏ p ∈ T j, (1 - w p)
  have hPi_pos : ∀ j, 0 < Pi_j j := by
    intro j
    refine Finset.prod_pos ?_
    intro p hp
    have hpS : p ∈ split z := split_mono (cut_le z (Nat.zero_le j)) (hT_sub j hp)
    have hp5 : (5 : ℝ) ≤ p := by
      exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hpS).1).1
    have hw_lt : w p ≤ 2 / 5 := div_le_div_of_nonneg_left (by norm_num) (by linarith) hp5
    linarith
  have hPi_and_S : ∀ j ∈ Finset.range R, (48 / 100 : ℝ) ≤ Pi_j j ∧ ∑ p ∈ T j, w p ≤ (3 / 4 : ℝ) := by
    intro j hj
    have hjR : j < R := Finset.mem_range.mp hj
    have hTj : T j = split (cut z j) \ split (cut z (j + 1)) := if_pos hjR
    have hj1_ge_A0 : A0 ≤ cut z (j + 1) := hcutR_ge.trans (cut_le z (by omega))
    have hj_ge_A0 : A0 ≤ cut z j := hj1_ge_A0.trans (cut_antitone z j)
    have hj1_ge100 : 100 ≤ cut z (j + 1) := hA0_ge100.trans hj1_ge_A0
    have hres := interval_pi_and_sum_bound c₀ hc₀_pos (cut z j) (cut z (j + 1))
      hj1_ge100 (cut_antitone z j) (Nat.lt_succ_sqrt' (cut z j))
      (hA0_band (cut z j) hj_ge_A0).1 (hA0_band (cut z (j + 1)) hj1_ge_A0).2
    simpa only [Pi_j, w, ← hTj] using hres
  have hPi_ge : ∀ j ∈ Finset.range R, (48 / 100 : ℝ) ≤ Pi_j j := fun j hj => (hPi_and_S j hj).1
  have hS_le : ∀ j ∈ Finset.range R, ∑ p ∈ T j, w p ≤ (3 / 4 : ℝ) := fun j hj => (hPi_and_S j hj).2
  -- Relate `wTrunc` and `wElem` to `Pi_j`
  let δ : ℕ → ℝ := fun j => wElem (T j) w (cap j) / Pi_j j
  have hδ_nonneg : ∀ j, 0 ≤ δ j := fun j =>
    div_nonneg (wElem_nonneg (fun p hp => (hw_split p (split_mono (cut_le z (Nat.zero_le j)) (hT_sub j hp))).1) _)
      (hPi_pos j).le
  have hδ_bound : ∀ j ∈ Finset.range R, δ j ≤ (1 / 30 : ℝ) * (1 / 4 : ℝ) ^ j := by
    intro j hj
    have hw_nonneg : ∀ p ∈ T j, 0 ≤ w p := fun p hp =>
      (hw_split p (split_mono (cut_le z (Nat.zero_le j)) (hT_sub j hp))).1
    have hfac := factorial_mul_wElem_le_pow hw_nonneg (cap j)
    have hwe : wElem (T j) w (cap j) ≤ (3 / 4 : ℝ) ^ (2 * (j + 2)) / ((2 * (j + 2)).factorial : ℝ) := by
      have hpow : (∑ p ∈ T j, w p) ^ (cap j) ≤ (3 / 4 : ℝ) ^ (cap j) :=
        pow_le_pow_left₀ (Finset.sum_nonneg hw_nonneg) (hS_le j hj) _
      rw [le_div_iff₀ (by positivity)]
      calc wElem (T j) w (cap j) * ((2 * (j + 2)).factorial : ℝ)
          = ((cap j).factorial : ℝ) * wElem (T j) w (cap j) := by dsimp [cap]; ring
        _ ≤ (∑ p ∈ T j, w p) ^ (cap j) := hfac
        _ ≤ (3 / 4 : ℝ) ^ (2 * (j + 2)) := hpow
    have h1 : δ j ≤ ((3 / 4 : ℝ) ^ (2 * (j + 2)) / ((2 * (j + 2)).factorial : ℝ)) / (48 / 100 : ℝ) :=
      div_le_div₀ (by positivity) hwe (by norm_num) (hPi_ge j hj)
    have h2 : ((3 / 4 : ℝ) ^ (2 * (j + 2)) / ((2 * (j + 2)).factorial : ℝ)) / (48 / 100 : ℝ) =
        (3 / 4 : ℝ) ^ (2 * (j + 2)) / (((2 * (j + 2)).factorial : ℝ) * (48 / 100 : ℝ)) := by ring
    exact h1.trans (h2 ▸ delta_bound j)
  have hwTrunc_band : ∀ j, Pi_j j ≤ wTrunc (T j) w (cap j) ∧
      wTrunc (T j) w (cap j) ≤ Pi_j j * (1 + δ j) := by
    intro j
    have hwTj : ∀ p ∈ T j, 0 ≤ w p ∧ w p ≤ 1 := fun p hp =>
      hw_split p (split_mono (cut_le z (Nat.zero_le j)) (hT_sub j hp))
    obtain ⟨_, hU⟩ := wTrunc_bounds hwTj (by omega : 1 ≤ j + 2)
    have hsub := wTrunc_sub_eq_wElem (T j) w (by omega : 1 ≤ j + 2)
    change wTrunc (T j) w (2 * (j + 2)) - wTrunc (T j) w (2 * (j + 2) - 1) = wElem (T j) w (2 * (j + 2)) at hsub
    have hPipos := hPi_pos j
    have hmulδ : Pi_j j * (1 + δ j) = Pi_j j + wElem (T j) w (cap j) := by
      dsimp only [δ]
      field_simp [hPipos.ne']
    obtain ⟨hL, _⟩ := wTrunc_bounds hwTj (by omega : 1 ≤ j + 2)
    constructor
    · exact hU
    · rw [hmulδ]; linarith
  have hprod_Pi_base : (∏ j ∈ Finset.range R, Pi_j j) * (∏ p ∈ Tbase, (1 - w p)) = localProd z := by
    unfold localProd
    rw [← hunion_split, Finset.prod_union]
    · have hbi : ∏ p ∈ (Finset.range R).biUnion T, (1 - w p) = ∏ j ∈ Finset.range R, Pi_j j := by
        rw [Finset.prod_biUnion]
        intro i _ j _ hij
        exact hdisj_T i j hij
      rw [hbi, mul_comm]
    · refine Finset.disjoint_left.mpr ?_
      intro p hpB hpi
      rcases Finset.mem_biUnion.mp hpi with ⟨j, _, hpj⟩
      exact (Finset.disjoint_left.mp (hdisj_base j)) hpj hpB
  have hprod_one_add_le : ∏ j ∈ Finset.range R, (1 + δ j) ≤ 2 := by
    have hsum_le : ∑ j ∈ Finset.range R, δ j ≤ 1 / 20 := by
      calc ∑ j ∈ Finset.range R, δ j
          ≤ ∑ j ∈ Finset.range R, (1 / 30 : ℝ) * (1 / 4 : ℝ) ^ j :=
            Finset.sum_le_sum (fun j hj => hδ_bound j hj)
        _ = (1 / 30 : ℝ) * ∑ j ∈ Finset.range R, (1 / 4 : ℝ) ^ j := by rw [Finset.mul_sum]
        _ ≤ (1 / 30 : ℝ) * (4 / 3 : ℝ) := mul_le_mul_of_nonneg_left (geom_sum_quarter_le R) (by norm_num)
        _ ≤ 1 / 20 := by norm_num
    have hexp_le : Real.exp (1 / 20 : ℝ) ≤ 2 := by
      have hexp1 : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have hhalf : Real.exp (1 / 20 : ℝ) ≤ Real.exp (1 / 2 : ℝ) := Real.exp_le_exp.mpr (by norm_num)
      have hsq : (Real.exp (1 / 2 : ℝ)) ^ 2 < 2 ^ 2 := by
        rw [← Real.exp_nat_mul]; norm_num; exact hexp1
      have h2 : Real.exp (1 / 2 : ℝ) < 2 := by
        by_contra hge; push Not at hge
        linarith [pow_le_pow_left₀ (by norm_num) hge 2]
      linarith
    exact (prod_one_add_le_exp_sum hδ_nonneg).trans ((Real.exp_le_exp.mpr hsum_le).trans hexp_le)
  have hmain_coeff_ge : (9 / 10 : ℝ) * localProd z ≤ main_coeff := by
    have hbase_nonneg : 0 ≤ ∏ p ∈ Tbase, (1 - w p) :=
      Finset.prod_nonneg (fun p hp => by
        have := hw_split p (split_mono (cut_le z (Nat.zero_le R)) hp)
        linarith)
    have h1 : ∏ j ∈ Finset.range R, Pi_j j ≤ ∏ j ∈ Finset.range R, wTrunc (T j) w (cap j) :=
      Finset.prod_le_prod₀ (fun j _ => (hPi_pos j).le) (fun j _ => (hwTrunc_band j).1)
    have h2 : ∑ r ∈ Finset.range R, wElem (T r) w (cap r) *
          (∏ j ∈ (Finset.range R).erase r, wTrunc (T j) w (cap j)) ≤
        (1 / 10 : ℝ) * ∏ j ∈ Finset.range R, Pi_j j := by
      have hterm : ∀ r ∈ Finset.range R,
          wElem (T r) w (cap r) * (∏ j ∈ (Finset.range R).erase r, wTrunc (T j) w (cap j)) ≤
            2 * δ r * ∏ j ∈ Finset.range R, Pi_j j := by
        intro r hr
        have hwe_eq : wElem (T r) w (cap r) = δ r * Pi_j r := by
          dsimp only [δ]; field_simp [(hPi_pos r).ne']
        have her_le : ∏ j ∈ (Finset.range R).erase r, wTrunc (T j) w (cap j) ≤
            (∏ j ∈ (Finset.range R).erase r, Pi_j j) * (∏ j ∈ (Finset.range R).erase r, (1 + δ j)) := by
          rw [← Finset.prod_mul_distrib]
          exact Finset.prod_le_prod₀
            (fun j _ => (hPi_pos j).le.trans (hwTrunc_band j).1)
            (fun j _ => (hwTrunc_band j).2)
        have hprod_1d : ∏ j ∈ (Finset.range R).erase r, (1 + δ j) ≤ 2 := by
          have hmul : (1 + δ r) * ∏ j ∈ (Finset.range R).erase r, (1 + δ j) =
              ∏ j ∈ Finset.range R, (1 + δ j) :=
            Finset.mul_prod_erase (Finset.range R) (fun j => 1 + δ j) hr
          have hnonneg_er : 0 ≤ ∏ j ∈ (Finset.range R).erase r, (1 + δ j) :=
            Finset.prod_nonneg (fun j _ => by linarith [hδ_nonneg j])
          have hr1 : 1 ≤ 1 + δ r := by linarith [hδ_nonneg r]
          have hle_mul : ∏ j ∈ (Finset.range R).erase r, (1 + δ j) ≤
              (1 + δ r) * ∏ j ∈ (Finset.range R).erase r, (1 + δ j) :=
            le_mul_of_one_le_left hnonneg_er hr1
          exact (hle_mul.trans hmul.le).trans hprod_one_add_le
        have hPiprod_eq : Pi_j r * ∏ j ∈ (Finset.range R).erase r, Pi_j j = ∏ j ∈ Finset.range R, Pi_j j :=
          Finset.mul_prod_erase (Finset.range R) Pi_j hr
        have hPi_er_pos : 0 ≤ ∏ j ∈ (Finset.range R).erase r, Pi_j j :=
          Finset.prod_nonneg (fun j _ => (hPi_pos j).le)
        calc wElem (T r) w (cap r) * (∏ j ∈ (Finset.range R).erase r, wTrunc (T j) w (cap j))
            ≤ (δ r * Pi_j r) * ((∏ j ∈ (Finset.range R).erase r, Pi_j j) * 2) := by
              rw [hwe_eq]
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hδ_nonneg r) (hPi_pos r).le)
              exact her_le.trans (mul_le_mul_of_nonneg_left hprod_1d hPi_er_pos)
          _ = 2 * δ r * (Pi_j r * ∏ j ∈ (Finset.range R).erase r, Pi_j j) := by ring
          _ = 2 * δ r * ∏ j ∈ Finset.range R, Pi_j j := by rw [hPiprod_eq]
      calc ∑ r ∈ Finset.range R, wElem (T r) w (cap r) *
            (∏ j ∈ (Finset.range R).erase r, wTrunc (T j) w (cap j))
          ≤ ∑ r ∈ Finset.range R, 2 * δ r * ∏ j ∈ Finset.range R, Pi_j j :=
            Finset.sum_le_sum hterm
        _ = 2 * (∑ r ∈ Finset.range R, δ r) * ∏ j ∈ Finset.range R, Pi_j j := by
            rw [← Finset.sum_mul, ← Finset.mul_sum]
        _ ≤ 2 * (1 / 20 : ℝ) * ∏ j ∈ Finset.range R, Pi_j j := by
            have hsum_le : ∑ j ∈ Finset.range R, δ j ≤ 1 / 20 := by
              calc ∑ j ∈ Finset.range R, δ j
                  ≤ ∑ j ∈ Finset.range R, (1 / 30 : ℝ) * (1 / 4 : ℝ) ^ j :=
                    Finset.sum_le_sum (fun j hj => hδ_bound j hj)
                _ = (1 / 30 : ℝ) * ∑ j ∈ Finset.range R, (1 / 4 : ℝ) ^ j := by rw [Finset.mul_sum]
                _ ≤ (1 / 30 : ℝ) * (4 / 3 : ℝ) :=
                    mul_le_mul_of_nonneg_left (geom_sum_quarter_le R) (by norm_num)
                _ ≤ 1 / 20 := by norm_num
            have hPi_all_pos : 0 ≤ ∏ j ∈ Finset.range R, Pi_j j :=
              Finset.prod_nonneg (fun j _ => (hPi_pos j).le)
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum_le (by norm_num)) hPi_all_pos
        _ = (1 / 10 : ℝ) * ∏ j ∈ Finset.range R, Pi_j j := by ring
    have hbracket : (9 / 10 : ℝ) * ∏ j ∈ Finset.range R, Pi_j j ≤
        (∏ j ∈ Finset.range R, wTrunc (T j) w (cap j)) -
          ∑ r ∈ Finset.range R, wElem (T r) w (cap r) *
            (∏ j ∈ (Finset.range R).erase r, wTrunc (T j) w (cap j)) := by
      have h910 : (9 / 10 : ℝ) * ∏ j ∈ Finset.range R, Pi_j j =
          (∏ j ∈ Finset.range R, Pi_j j) - (1 / 10 : ℝ) * ∏ j ∈ Finset.range R, Pi_j j := by ring
      rw [h910]
      exact sub_le_sub h1 h2
    calc (9 / 10 : ℝ) * localProd z
        = ((9 / 10 : ℝ) * ∏ j ∈ Finset.range R, Pi_j j) * (∏ p ∈ Tbase, (1 - w p)) := by
          rw [← hprod_Pi_base]; ring
      _ ≤ ((∏ j ∈ Finset.range R, wTrunc (T j) w (cap j)) -
            ∑ r ∈ Finset.range R, wElem (T r) w (cap r) *
              (∏ j ∈ (Finset.range R).erase r, wTrunc (T j) w (cap j))) *
            (∏ p ∈ Tbase, (1 - w p)) := mul_le_mul_of_nonneg_right hbracket hbase_nonneg
      _ = main_coeff := hmain_factor.symm
  -- Final numerical combination: `len * main_coeff ≥ 2/5 * c₀ * x / log x` and `err ≤ 1/5 * c₀ * x / log x`
  have hlen_ge : (x : ℝ) / 2 ≤ len := by
    dsimp only [len]
    have hnat2 : x ≤ 2 * (x - x / 2) := by omega
    have hreal2 : (x : ℝ) ≤ 2 * ((x - x / 2 : ℕ) : ℝ) := by exact_mod_cast hnat2
    linarith
  have hz_ge_A0 : A0 ≤ z := by
    have : A0 ≤ A0 ^ 2 := Nat.le_self_pow (by omega) _
    omega
  have hlpz_ge : (99 / 100 : ℝ) * c₀ / Real.log (x : ℝ) ≤ localProd z := by
    have h1 := (hA0_band z hz_ge_A0).1
    have h2 : (99 / 100 : ℝ) * c₀ / Real.log (z : ℝ) ≤ localProd z :=
      (div_le_iff₀ hlogz_pos).mpr (by linarith)
    have hlog_zx : Real.log (z : ℝ) ≤ Real.log (x : ℝ) :=
      Real.log_le_log (by positivity) hz_le_x_R
    have h3 : (99 / 100 : ℝ) * c₀ / Real.log (x : ℝ) ≤ (99 / 100 : ℝ) * c₀ / Real.log (z : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hlogz_pos hlog_zx
    exact h3.trans h2
  have hmain_ge : (2 / 5 : ℝ) * c₀ * (x : ℝ) / Real.log (x : ℝ) ≤ len * main_coeff := by
    have h910_lp : (9 / 10 : ℝ) * ((99 / 100 : ℝ) * c₀ / Real.log (x : ℝ)) ≤ main_coeff :=
      (mul_le_mul_of_nonneg_left hlpz_ge (by norm_num)).trans hmain_coeff_ge
    have hmc_nonneg : 0 ≤ main_coeff := by
      have : 0 ≤ (9 / 10 : ℝ) * ((99 / 100 : ℝ) * c₀ / Real.log (x : ℝ)) := by positivity
      linarith
    have h1 : ((x : ℝ) / 2) * ((9 / 10 : ℝ) * ((99 / 100 : ℝ) * c₀ / Real.log (x : ℝ))) ≤ len * main_coeff :=
      mul_le_mul hlen_ge h910_lp (by positivity) (by positivity)
    have h2 : (2 / 5 : ℝ) * c₀ * (x : ℝ) / Real.log (x : ℝ) ≤
        ((x : ℝ) / 2) * ((9 / 10 : ℝ) * ((99 / 100 : ℝ) * c₀ / Real.log (x : ℝ))) := by
      have hfrac : (2 / 5 : ℝ) ≤ 1 / 2 * (9 / 10 * (99 / 100)) := by norm_num
      have hxlog : 0 ≤ c₀ * (x : ℝ) / Real.log (x : ℝ) := by positivity
      calc (2 / 5 : ℝ) * c₀ * (x : ℝ) / Real.log (x : ℝ)
          = (2 / 5 : ℝ) * (c₀ * (x : ℝ) / Real.log (x : ℝ)) := by ring
        _ ≤ (1 / 2 * (9 / 10 * (99 / 100))) * (c₀ * (x : ℝ) / Real.log (x : ℝ)) :=
            mul_le_mul_of_nonneg_right hfrac hxlog
        _ = ((x : ℝ) / 2) * ((9 / 10 : ℝ) * ((99 / 100 : ℝ) * c₀ / Real.log (x : ℝ))) := by ring
    exact h2.trans h1
  -- Bound the error term by `(1/5) * c₀ * x / Real.log x`
  have hx_ge1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hx_pos : (0 : ℝ) < (x : ℝ) := by linarith
  have hlogx_rpow : Real.log (x : ℝ) ≤ 16 * (x : ℝ) ^ (1 / 16 : ℝ) := by
    have h := Real.log_le_rpow_div hx_pos.le (by norm_num : (0 : ℝ) < 1 / 16)
    linarith [show (x : ℝ) ^ (1 / 16 : ℝ) / (1 / 16 : ℝ) = 16 * (x : ℝ) ^ (1 / 16 : ℝ) by ring]
  have hx116_ge1 : (1 : ℝ) ≤ (x : ℝ) ^ (1 / 16 : ℝ) := Real.one_le_rpow hx_ge1 (by norm_num)
  have hR1_le : 1 + (R : ℝ) ≤ 33 * (x : ℝ) ^ (1 / 16 : ℝ) := by
    calc 1 + (R : ℝ) ≤ 1 + 2 * Real.log (x : ℝ) := by linarith
      _ ≤ 1 + 2 * (16 * (x : ℝ) ^ (1 / 16 : ℝ)) := by linarith
      _ ≤ 33 * (x : ℝ) ^ (1 / 16 : ℝ) := by linarith
  have hD_le : (D_max : ℝ) ≤ 2 * (M0 : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) := by
    have hsqrt_le : (Nat.sqrt x : ℝ) + 1 ≤ 2 * (x : ℝ) ^ (1 / 2 : ℝ) := by
      have hsq : (Nat.sqrt x : ℝ) ≤ Real.sqrt (x : ℝ) :=
        Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' x)
      rw [Real.sqrt_eq_rpow] at hsq
      have hx12_ge1 : (1 : ℝ) ≤ (x : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hx_ge1 (by norm_num)
      linarith
    calc (D_max : ℝ) = (M0 : ℝ) * ((Nat.sqrt x : ℝ) + 1) := by dsimp [D_max]; push_cast; ring
      _ ≤ (M0 : ℝ) * (2 * (x : ℝ) ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hsqrt_le (Nat.cast_nonneg _)
      _ = 2 * (M0 : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) := by ring
  have hlogD_le : 1 + Real.log (D_max : ℝ) ≤ (1 + Real.log (2 * (M0 : ℝ)) + 16) * (x : ℝ) ^ (1 / 16 : ℝ) := by
    have hM01 : (1 : ℝ) ≤ (M0 : ℝ) := by exact_mod_cast hM0_pos
    have h2M0_pos : 0 < 2 * (M0 : ℝ) := by linarith
    have hD_pos_R : 0 < (D_max : ℝ) := by exact_mod_cast hD_pos
    have hx12_pos : 0 < (x : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx_pos _
    have hlog1 : Real.log (D_max : ℝ) ≤ Real.log (2 * (M0 : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ)) :=
      Real.log_le_log hD_pos_R hD_le
    have hlog2 : Real.log (2 * (M0 : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ)) =
        Real.log (2 * (M0 : ℝ)) + (1 / 2 : ℝ) * Real.log (x : ℝ) := by
      rw [Real.log_mul h2M0_pos.ne' hx12_pos.ne', Real.log_rpow hx_pos]
    have hlogM_nonneg : 0 ≤ Real.log (2 * (M0 : ℝ)) := Real.log_nonneg (by linarith)
    calc 1 + Real.log (D_max : ℝ)
        ≤ 1 + Real.log (2 * (M0 : ℝ)) + (1 / 2 : ℝ) * (16 * (x : ℝ) ^ (1 / 16 : ℝ)) := by linarith
      _ ≤ 1 + Real.log (2 * (M0 : ℝ)) + 16 * (x : ℝ) ^ (1 / 16 : ℝ) := by
          have : 0 ≤ (x : ℝ) ^ (1 / 16 : ℝ) := by positivity
          linarith
      _ ≤ (1 + Real.log (2 * (M0 : ℝ)) + 16) * (x : ℝ) ^ (1 / 16 : ℝ) := by
          have : (1 + Real.log (2 * (M0 : ℝ))) * 1 ≤ (1 + Real.log (2 * (M0 : ℝ))) * (x : ℝ) ^ (1 / 16 : ℝ) :=
            mul_le_mul_of_nonneg_left hx116_ge1 (by linarith)
          linarith
  have herr_le_rpow : (1 + (R : ℝ)) * ((D_max : ℝ) * (1 + Real.log (D_max : ℝ))) ≤
      C_rem * (x : ℝ) ^ (10 / 16 : ℝ) := by
    have hD0 : 0 ≤ (D_max : ℝ) := Nat.cast_nonneg _
    have hlogD0 : 0 ≤ 1 + Real.log (D_max : ℝ) := by
      have : (1 : ℝ) ≤ (D_max : ℝ) := by exact_mod_cast hD_pos
      linarith [Real.log_nonneg this]
    have hM01 : (1 : ℝ) ≤ (M0 : ℝ) := by exact_mod_cast hM0_pos
    have hlogM_nonneg : 0 ≤ Real.log (2 * (M0 : ℝ)) := Real.log_nonneg (by linarith)
    calc (1 + (R : ℝ)) * ((D_max : ℝ) * (1 + Real.log (D_max : ℝ)))
        ≤ (33 * (x : ℝ) ^ (1 / 16 : ℝ)) *
            ((2 * (M0 : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ)) *
              ((1 + Real.log (2 * (M0 : ℝ)) + 16) * (x : ℝ) ^ (1 / 16 : ℝ))) :=
          mul_le_mul hR1_le (mul_le_mul hD_le hlogD_le hlogD0 (by positivity))
            (mul_nonneg hD0 hlogD0) (by positivity)
      _ = C_rem * ((x : ℝ) ^ (1 / 16 : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) * (x : ℝ) ^ (1 / 16 : ℝ)) := by
          dsimp only [C_rem]; ring
      _ = C_rem * (x : ℝ) ^ (10 / 16 : ℝ) := by
          congr 1
          rw [← Real.rpow_add hx_pos, ← Real.rpow_add hx_pos]
          congr 1
          norm_num
  have hK_thr_le : 80 * C_rem / c₀ ≤ (x : ℝ) ^ (5 / 16 : ℝ) := by
    have hxK_R : (K_thr : ℝ) ^ 4 ≤ (x : ℝ) := by exact_mod_cast hxK
    have hx14 : (K_thr : ℝ) ≤ (x : ℝ) ^ (1 / 4 : ℝ) := by
      calc (K_thr : ℝ) = ((K_thr : ℝ) ^ 4) ^ (1 / 4 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
            norm_num
        _ ≤ (x : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by positivity) hxK_R (by norm_num)
    have hx45 : (x : ℝ) ^ (1 / 4 : ℝ) ≤ (x : ℝ) ^ (5 / 16 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx_ge1 (by norm_num)
    have hceil : 80 * C_rem / c₀ ≤ (K_thr : ℝ) := by
      have h1 := Nat.le_ceil (80 * C_rem / c₀)
      have h2 : (Nat.ceil (80 * C_rem / c₀) : ℝ) ≤ (K_thr : ℝ) := by
        dsimp [K_thr]; push_cast; linarith
      exact h1.trans h2
    exact hceil.trans (hx14.trans hx45)
  have herr_le_main : (1 + (R : ℝ)) * ((D_max : ℝ) * (1 + Real.log (D_max : ℝ))) ≤
      (1 / 5 : ℝ) * c₀ * (x : ℝ) / Real.log (x : ℝ) := by
    have hC_bound : C_rem ≤ (c₀ / 80) * (x : ℝ) ^ (5 / 16 : ℝ) := by
      have := mul_le_mul_of_nonneg_right hK_thr_le hc₀_pos.le
      rw [div_mul_cancel₀ _ hc₀_pos.ne'] at this
      linarith
    have h1 : C_rem * (x : ℝ) ^ (10 / 16 : ℝ) ≤ (c₀ / 80) * (x : ℝ) ^ (15 / 16 : ℝ) := by
      calc C_rem * (x : ℝ) ^ (10 / 16 : ℝ)
          ≤ ((c₀ / 80) * (x : ℝ) ^ (5 / 16 : ℝ)) * (x : ℝ) ^ (10 / 16 : ℝ) :=
            mul_le_mul_of_nonneg_right hC_bound (by positivity)
        _ = (c₀ / 80) * ((x : ℝ) ^ (5 / 16 : ℝ) * (x : ℝ) ^ (10 / 16 : ℝ)) := by ring
        _ = (c₀ / 80) * (x : ℝ) ^ (15 / 16 : ℝ) := by
            rw [← Real.rpow_add hx_pos]; norm_num
    have h2 : (c₀ / 80) * (x : ℝ) ^ (15 / 16 : ℝ) ≤ (1 / 5 : ℝ) * c₀ * (x : ℝ) / Real.log (x : ℝ) := by
      have hx_eq : (x : ℝ) = (x : ℝ) ^ (15 / 16 : ℝ) * (x : ℝ) ^ (1 / 16 : ℝ) := by
        rw [← Real.rpow_add hx_pos]; norm_num
      rw [le_div_iff₀ hlogx_pos]
      calc (c₀ / 80) * (x : ℝ) ^ (15 / 16 : ℝ) * Real.log (x : ℝ)
          ≤ (c₀ / 80) * (x : ℝ) ^ (15 / 16 : ℝ) * (16 * (x : ℝ) ^ (1 / 16 : ℝ)) :=
            mul_le_mul_of_nonneg_left hlogx_rpow (by positivity)
        _ = (1 / 5 : ℝ) * c₀ * ((x : ℝ) ^ (15 / 16 : ℝ) * (x : ℝ) ^ (1 / 16 : ℝ)) := by ring
        _ = (1 / 5 : ℝ) * c₀ * (x : ℝ) := by rw [← hx_eq]
    exact herr_le_rpow.trans (h1.trans h2)
  have hfinal_err : len * main_coeff - ((rough x z).card : ℝ) ≤
      (1 / 5 : ℝ) * c₀ * (x : ℝ) / Real.log (x : ℝ) := by
    calc len * main_coeff - ((rough x z).card : ℝ)
        ≤ (1 + (R : ℝ)) * ∑ A ∈ G, remA A := hsplit_err
      _ ≤ (1 + (R : ℝ)) * ((D_max : ℝ) * (1 + Real.log (D_max : ℝ))) :=
          mul_le_mul_of_nonneg_left hsum_rem_le (by positivity)
      _ ≤ (1 / 5 : ℝ) * c₀ * (x : ℝ) / Real.log (x : ℝ) := herr_le_main
  have hsub_le : (1 / 5 : ℝ) * c₀ * (x : ℝ) / Real.log (x : ℝ) ≤ ((rough x z).card : ℝ) := by
    have hdiff_c : (2 / 5 : ℝ) * c₀ * (x : ℝ) / Real.log (x : ℝ) -
        (1 / 5 : ℝ) * c₀ * (x : ℝ) / Real.log (x : ℝ) =
        (1 / 5 : ℝ) * c₀ * (x : ℝ) / Real.log (x : ℝ) := by ring
    linarith
  calc (c₀ / 5) * (x : ℝ) / Real.log (x : ℝ)
      = (1 / 5 : ℝ) * c₀ * (x : ℝ) / Real.log (x : ℝ) := by ring
    _ ≤ ((rough x z).card : ℝ) := hsub_le

end Conjectures.QuadraticPrimes.SieveInitialLowerBound_aux

theorem Conjectures.QuadraticPrimes.SieveInitialLowerBound :
    let f := fun k : ℕ => 4*k^2+1; let block := fun x : ℕ => Finset.Ioc (x/2) x; let primes := fun z : ℕ => (Finset.Icc 3 z).filter (fun p => Nat.Prime p); let split := fun z : ℕ => (Finset.Icc 5 z).filter (fun p => Nat.Prime p ∧ p % 4 = 1); let wheel := fun z : ℕ => ∏ p ∈ primes z, p; let rough := fun x z : ℕ => (block x).filter (fun k => Nat.Coprime (f k) (wheel z)); let localProd := fun z : ℕ => ∏ p ∈ split z, (1 - 2/(p : ℝ)); (∃ c : ℝ, 0<c ∧ Filter.Tendsto (fun z : ℕ => Real.log (z : ℝ) * localProd z) Filter.atTop (nhds c)) →
    ∃ U : ℕ, 4≤U ∧ ∃ c : ℝ, 0<c ∧ ∃ X : ℕ, 2≤X ∧ ∀ x : ℕ, X≤x →
      let z := (Finset.range (x+1)).sup (fun t => if t^U≤x then t else 0);
      c*(x : ℝ)/Real.log x ≤ ((rough x z).card : ℝ) :=
  Conjectures.QuadraticPrimes.SieveInitialLowerBound_aux.main_proof
