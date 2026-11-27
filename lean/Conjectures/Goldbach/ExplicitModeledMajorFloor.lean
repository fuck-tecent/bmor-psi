import Mathlib

/-!
# Goldbach gap `L-goldbach-explicit-modeled-major-floor`

For every even `n ≥ 1,000,000`, the real part of the Ramanujan-weighted
major-arc model `modeledMajor n` is at least `n / 72`.
We combine the multiplicative factorization of Ramanujan sums (`ram`),
the signed-powerset lower bound on the arithmetic Euler factors (giving at least `1/3`
of the `q = 1` mass for decreasing nonnegative denominator weights), and the
truncated Fejer-kernel lower bound at `q = 1`.
-/

open scoped BigOperators ComplexConjugate
open Finset MeasureTheory intervalIntegral

namespace Conjectures.Goldbach.ExplicitModeledMajorFloor_aux

private noncomputable def phase (m h a : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((h : ℝ) * a / m) : ℝ) : ℂ) * Complex.I)

private def unitsBelow (m : ℕ) : Finset ℕ :=
  (Finset.range m).filter (fun a => Nat.Coprime a m)

private theorem unitsBelow_card (m : ℕ) : (unitsBelow m).card = m.totient := by
  unfold unitsBelow
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  exact and_congr_right (fun _ => Nat.coprime_comm)

private theorem phase_character (m h a : ℕ) [NeZero m] :
    phase m h a = ZMod.stdAddChar ((h : ZMod m) * (a : ZMod m)) := by
  have ch := ZMod.stdAddChar_coe (N := m) ((h * a : ℕ) : ℤ)
  push_cast at ch
  rw [ch]
  unfold phase
  push_cast
  congr 1
  ring

private theorem phase_modulus (m h a : ℕ) [NeZero m] :
    phase m h (a % m) = phase m h a := by
  simp only [phase_character, ZMod.natCast_mod]

private theorem phase_pair (q r h a b : ℕ) (hq : 0 < q) (hr : 0 < r) :
    phase (q * r) h ((r * a + q * b) % (q * r)) = phase q h a * phase r h b := by
  have : NeZero (q * r) := ⟨Nat.ne_of_gt (Nat.mul_pos hq hr)⟩
  rw [phase_modulus]
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  have qnz : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have rnz : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

private noncomputable def Efn (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

private noncomputable def ram (q h : ℕ) : ℂ :=
  ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), Efn ((h : ℝ) * a / q)

private theorem ram_eq_phase (q h : ℕ) :
    ram q h = ∑ a ∈ unitsBelow q, phase q h a := by
  unfold ram unitsBelow phase Efn
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 2

private theorem ram_mul {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : q.Coprime r) (h : ℕ) :
    ram (q * r) h = ram q h * ram r h := by
  rw [ram_eq_phase, ram_eq_phase, ram_eq_phase]
  let combine (x : ℕ × ℕ) := (r * x.1 + q * x.2) % (q * r)
  let pairs := unitsBelow q ×ˢ unitsBelow r
  have member {m a : ℕ} : a ∈ unitsBelow m ↔ a < m ∧ Nat.Coprime a m := by
    simp only [unitsBelow, Finset.mem_filter, Finset.mem_range]
  have maps : pairs.image combine ⊆ unitsBelow (q * r) := by
    intro z hz
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    apply member.mpr
    refine ⟨Nat.mod_lt _ (Nat.mul_pos hq hr), ?_⟩
    change Nat.gcd ((r * a + q * b) % (q * r)) (q * r) = 1
    rw [← Nat.gcd_rec]
    change Nat.Coprime (q * r) (r * a + q * b)
    apply Nat.coprime_mul_iff_left.mpr
    constructor
    · rw [Nat.coprime_add_mul_left_right]
      exact hc.mul_right (member.mp ha).2.symm
    · rw [add_comm, Nat.coprime_add_mul_left_right]
      exact hc.symm.mul_right (member.mp hb).2.symm
  have injective : Set.InjOn combine (↑pairs) := by
    rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd he
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hc1, hd⟩ := Finset.mem_product.mp hcd
    have congruence : r * a + q * b ≡ r * c + q * d [MOD q * r] := he
    apply Prod.ext
    · have hmod := congruence.of_dvd (dvd_mul_right q r)
      have reduced : r * a ≡ r * c [MOD q] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, add_zero, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime hc reduced).eq_of_lt_of_lt
        (member.mp ha).1 (member.mp hc1).1
    · have hmod := congruence.of_dvd (dvd_mul_left r q)
      have reduced : q * b ≡ q * d [MOD r] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime hc.symm reduced).eq_of_lt_of_lt
        (member.mp hb).1 (member.mp hd).1
  have covers : pairs.image combine = unitsBelow (q * r) := by
    apply Finset.eq_of_subset_of_card_le maps
    rw [Finset.card_image_of_injOn injective, unitsBelow_card, Nat.totient_mul hc]
    simp only [pairs, Finset.card_product, unitsBelow_card]
    exact le_rfl
  rw [← covers, Finset.sum_image injective, Finset.sum_mul_sum, ← Finset.sum_product']
  exact Finset.sum_congr rfl fun x _ => phase_pair q r h x.1 x.2 hq hr

private theorem ram_primePower (p j h : ℕ) (hp : p.Prime) :
    ram (p ^ (j + 1)) h = (if p ^ (j + 1) ∣ h then ((p ^ (j + 1) : ℕ) : ℂ) else 0) -
      (if p ^ j ∣ h then ((p ^ j : ℕ) : ℂ) else 0) := by
  have full (q : ℕ) (hq : 0 < q) :
      ∑ a ∈ Finset.range q, Efn ((h : ℝ) * a / q) = if q ∣ h then (q : ℂ) else 0 := by
    let : NeZero q := ⟨hq.ne'⟩
    calc
      _ = ∑ x : ZMod q, ZMod.stdAddChar ((h : ZMod q) * x) := by
        apply Finset.sum_bij (fun (a : ℕ) _ => (a : ZMod q))
        · intro a _
          exact Finset.mem_univ _
        · intro a ha b hb hab
          simpa only [ZMod.val_natCast_of_lt (Finset.mem_range.mp ha),
            ZMod.val_natCast_of_lt (Finset.mem_range.mp hb)] using congrArg ZMod.val hab
        · intro x _
          exact ⟨x.val, Finset.mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
        · intro a _
          have cast_eq : (h : ZMod q) * a = ((h * a : ℕ) : ℤ) := by push_cast; rfl
          rw [cast_eq, ZMod.stdAddChar_coe]
          dsimp [Efn]
          congr 1
          push_cast
          ring
      _ = _ := by
        by_cases hd : q ∣ h
        · have hz : (h : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff h q).mpr hd
          simp [hd, hz, ZMod.card]
        · have hz : (h : ZMod q) ≠ 0 := fun hz => hd ((ZMod.natCast_eq_zero_iff h q).mp hz)
          rw [ite_eq_right hd]
          exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hz)
  let m := p ^ j
  have hm : 0 < m := pow_pos hp.pos _
  let mult := (Finset.range m).image (fun b => p * b)
  have hsub : mult ⊆ Finset.range (p ^ (j + 1)) := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    rw [Finset.mem_range, pow_succ']
    exact Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp hb) hp.pos
  have hfilter : (Finset.range (p ^ (j + 1))).filter (fun a => Nat.Coprime a (p ^ (j + 1))) =
      Finset.range (p ^ (j + 1)) \ mult := by
    rw [Finset.sdiff_eq_filter]
    apply Finset.filter_congr
    intro a ha
    rw [Nat.coprime_pow_right_iff (Nat.succ_pos j), Nat.coprime_comm, hp.coprime_iff_not_dvd]
    apply not_congr
    constructor
    · rintro ⟨b, rfl⟩
      apply Finset.mem_image.mpr
      refine ⟨b, Finset.mem_range.mpr ?_, rfl⟩
      rw [Finset.mem_range, pow_succ'] at ha
      exact (Nat.mul_lt_mul_left hp.pos).mp ha
    · intro ha'
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha'
      exact dvd_mul_right _ _
  have removed : ∑ a ∈ mult, Efn ((h : ℝ) * a / (p ^ (j + 1) : ℕ)) =
      ∑ b ∈ Finset.range m, Efn ((h : ℝ) * b / m) := by
    rw [show mult = (Finset.range m).image (fun b => p * b) from rfl,
      Finset.sum_image (mul_right_injective₀ hp.ne_zero).injOn]
    apply Finset.sum_congr rfl
    intro b _
    congr 1
    rw [pow_succ']
    push_cast
    dsimp [m]
    push_cast
    field_simp [show (p : ℝ) ≠ 0 by exact_mod_cast hp.ne_zero]
  unfold ram
  rw [hfilter, ← full _ (pow_pos hp.pos (j + 1)), ← full _ hm, ← removed]
  exact eq_sub_of_add_eq (Finset.sum_sdiff hsub)

private theorem ram_one (h : ℕ) : ram 1 h = 1 := by simp [ram, Efn]

private theorem ram_prime {p : ℕ} (hp : p.Prime) (h : ℕ) :
    ram p h = (if p ∣ h then (p : ℂ) else 0) - 1 := by
  simpa using ram_primePower p 0 h hp

private theorem ram_unit_power {p : ℕ} (hp : p.Prime) (j h : ℕ) (hc : h.Coprime p) :
    ram (p ^ (j + 1)) h = if j = 0 then -1 else 0 := by
  have hd := hp.coprime_iff_not_dvd.mp hc.symm
  have hpow (k : ℕ) : ¬ p ^ (k + 1) ∣ h :=
    fun hh => hd ((dvd_pow_self p (Nat.succ_ne_zero k)).trans hh)
  rw [ram_primePower p j h hp, ite_eq_right (hpow j)]
  cases j with
  | zero => simp
  | succ k => simp [hpow k]

private noncomputable def localCoefficient (p n : ℕ) : ℝ :=
  if p ∣ n then 1 / ((p : ℝ) - 1) else -(1 / ((p : ℝ) - 1) ^ 2)

private noncomputable def coefficient (q n : ℕ) : ℂ :=
  (ram q 1 / (q.totient : ℂ)) ^ 2 * (starRingEnd ℂ) (ram q n)

private theorem coefficient_one (n : ℕ) : coefficient 1 n = 1 := by
  simp [coefficient, ram_one]

private theorem coefficient_mul {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : q.Coprime r) (n : ℕ) :
    coefficient (q * r) n = coefficient q n * coefficient r n := by
  unfold coefficient
  rw [ram_mul hq hr hc, ram_mul hq hr hc, Nat.totient_mul hc, Nat.cast_mul, map_mul]
  ring

private theorem coefficient_prime {p : ℕ} (hp : p.Prime) (n : ℕ) :
    coefficient p n = (localCoefficient p n : ℂ) := by
  have hone : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.mp h)
  have hne : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  rw [coefficient, ram_prime hp, ram_prime hp, ite_eq_right hone,
    Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
  by_cases hd : p ∣ n <;> simp [localCoefficient, hd] <;> field_simp

private theorem coefficient_higher_power {p : ℕ} (hp : p.Prime) (k n : ℕ) :
    coefficient (p ^ (k + 2)) n = 0 := by
  have h := ram_unit_power hp (k + 1) 1 (by simp)
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false] at h
  simp [coefficient, h]

private theorem coefficient_not_squarefree {q : ℕ} (n : ℕ) (hq : 0 < q)
    (hs : ¬ Squarefree q) : coefficient q n = 0 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => exact (hs squarefree_one).elim
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => exact (hs (by simpa using hp.squarefree)).elim
      | succ j => exact coefficient_higher_power hp j n
  | coprime a b ha hb hab ia ib =>
    rw [coefficient_mul (by omega) (by omega) hab]
    by_cases h : Squarefree a
    · rw [ib (by omega) (fun h' => hs ((Nat.squarefree_mul hab).mpr ⟨h, h'⟩)), mul_zero]
    · rw [ia (by omega) h, zero_mul]

private theorem coefficient_prime_product (n : ℕ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    coefficient (∏ p ∈ s, p) n = ((∏ p ∈ s, localCoefficient p n : ℝ) : ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp [coefficient_one]
  | @insert p s hp ih =>
    have hprime := hs p (Finset.mem_insert_self _ _)
    have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (Finset.mem_insert_of_mem hr)
    have hcop : p.Coprime (∏ r ∈ s, r) := Nat.coprime_prod_right_iff.mpr fun r hr =>
      (Nat.coprime_primes hprime (hs' r hr)).mpr fun he => hp (he ▸ hr)
    rw [Finset.prod_insert hp, Finset.prod_insert hp,
      coefficient_mul hprime.pos (Finset.prod_pos fun r hr => (hs' r hr).pos) hcop,
      coefficient_prime hprime, ih hs', Complex.ofReal_mul]

private noncomputable def badFactor (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1) ^ 2

private theorem badFactor_nonneg (p : ℕ) : 0 ≤ badFactor p := by unfold badFactor; positivity

private theorem tail_telescope (m : ℕ) :
    ∏ p ∈ Finset.range (m + 5), (if 5 ≤ p then 1 + badFactor p else 1) ≤
      4 * ((m : ℝ) + 3) / (3 * ((m : ℝ) + 4)) := by
  induction m with
  | zero =>
    have h : ∏ p ∈ Finset.range (0 + 5), (if 5 ≤ p then 1 + badFactor p else 1) = 1 :=
      Finset.prod_eq_one fun p hp =>
        ite_eq_right (Nat.not_le.mpr (Finset.mem_range.mp hp))
    norm_num [h]
  | succ m ih =>
    rw [show m.succ + 5 = (m + 5) + 1 by omega, Finset.prod_range_succ,
      ite_eq_left (show 5 ≤ m + 5 by omega)]
    apply (mul_le_mul_of_nonneg_right ih (by linarith [badFactor_nonneg (m + 5)])).trans
    unfold badFactor
    push_cast
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have h₁ : 0 < (m : ℝ) + 4 := by linarith
    have h₂ : 0 < (m : ℝ) + 1 + 4 := by linarith
    rw [show (m : ℝ) + 5 - 1 = m + 4 by ring]
    field_simp
    nlinarith only [hm]

private theorem product_tail_le {s : Finset ℕ} (hs : ∀ p ∈ s, 5 ≤ p) :
    ∏ p ∈ s, (1 + badFactor p) ≤ 4 / 3 := by
  let m := s.sup id
  have hsub : s ⊆ Finset.range (m + 5) := by
    intro p hp
    have h : p ≤ m := Finset.le_sup (f := id) hp
    exact Finset.mem_range.mpr (by omega)
  calc
    _ = ∏ p ∈ s, (if 5 ≤ p then 1 + badFactor p else 1) :=
      Finset.prod_congr rfl fun p hp =>
        (ite_eq_left (hs p hp)).symm
    _ ≤ ∏ p ∈ Finset.range (m + 5), (if 5 ≤ p then 1 + badFactor p else 1) := by
      refine Finset.prod_le_prod_of_subset_of_one_le₀ hsub ?_ ?_
      · intro i _
        split_ifs <;> linarith [badFactor_nonneg i]
      · intro i _ _
        split_ifs <;> linarith [badFactor_nonneg i]
    _ ≤ _ := tail_telescope m
    _ ≤ 4 / 3 := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
      linarith

private theorem product_bad_factors {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) :
    ∏ p ∈ s, (1 + badFactor p) ≤ 5 / 3 := by
  have hrest : ∀ p ∈ s.erase 3, 5 ≤ p := by
    intro p hp
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hp
    obtain ⟨hprime, hpos⟩ := hs p hmem
    have hfour : p ≠ 4 := by rintro rfl; exact (by decide : ¬ Nat.Prime 4) hprime
    omega
  have hsub : s ⊆ insert 3 (s.erase 3) := by intro p hp; by_cases p = 3 <;> simp_all
  calc
    _ ≤ ∏ p ∈ insert 3 (s.erase 3), (1 + badFactor p) :=
      Finset.prod_le_prod_of_subset_of_one_le₀ hsub (fun p _ => by linarith [badFactor_nonneg p])
        (fun p _ _ => by linarith [badFactor_nonneg p])
    _ = (5 / 4) * ∏ p ∈ s.erase 3, (1 + badFactor p) := by
      rw [Finset.prod_insert (Finset.notMem_erase _ _)]
      congr 1
      norm_num [badFactor]
    _ ≤ (5 / 4) * (4 / 3) := mul_le_mul_of_nonneg_left (product_tail_le hrest) (by norm_num)
    _ = _ := by norm_num

private theorem negative_factors_lower {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime ∧ 2 < p)
    (W : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ W k) (hmono : ∀ i j, 0 < i → i ≤ j → W j ≤ W i)
    {d : ℕ} (hd : 0 < d) :
    W d / 3 ≤ ∑ t ∈ s.powerset, (∏ p ∈ t, -badFactor p) * W (d * ∏ p ∈ t, p) := by
  let P := s.powerset.erase ∅
  have hempty : ∅ ∈ s.powerset := Finset.mem_powerset.mpr (Finset.empty_subset _)
  have hrest : (∑ t ∈ P, ∏ p ∈ t, badFactor p) + 1 ≤ 5 / 3 := by
    have h := Finset.prod_one_add (f := badFactor) s
    rw [← Finset.sum_erase_add _ _ hempty] at h
    simp only [Finset.prod_empty] at h
    rw [← h]
    exact product_bad_factors hs
  have hterm (t : Finset ℕ) (ht : t ∈ P) :
      -(W d * ∏ p ∈ t, badFactor p) ≤ (∏ p ∈ t, -badFactor p) * W (d * ∏ p ∈ t, p) := by
    have ht' : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_erase.mp ht).2
    have hprod : 0 < ∏ p ∈ t, p := Finset.prod_pos fun p hp => (hs p (ht' hp)).1.pos
    have hle := hmono d (d * ∏ p ∈ t, p) hd (Nat.le_mul_of_pos_right d hprod)
    apply (abs_le.mp ?_).1
    rw [abs_mul, abs_of_nonneg (hnonneg _), Finset.abs_prod]
    simp_rw [abs_neg, abs_of_nonneg (badFactor_nonneg _)]
    rw [mul_comm (W d)]
    exact mul_le_mul_of_nonneg_left hle (Finset.prod_nonneg fun _ _ => badFactor_nonneg _)
  have low := Finset.sum_le_sum hterm
  simp only [Finset.sum_neg_distrib, ← Finset.mul_sum] at low
  have cap := mul_le_mul_of_nonneg_left
    (show (∑ t ∈ P, ∏ p ∈ t, badFactor p) ≤ 2 / 3 by linarith) (hnonneg d)
  rw [← Finset.sum_erase_add _ _ hempty]
  simp only [Finset.prod_empty, mul_one, one_mul]
  dsimp only [P] at low cap
  linarith

private theorem reindex_denominators (Q n : ℕ) (W : ℕ → ℝ) (hcut : ∀ q, Q < q → W q = 0) :
    (∑ q ∈ Finset.Icc 1 Q, (coefficient q n).re * W q) =
    ∑ t ∈ ((Finset.range (Q + 1)).filter Nat.Prime).powerset,
      (∏ p ∈ t, localCoefficient p n) * W (∏ p ∈ t, p) := by
  classical
  let P := (Finset.range (Q + 1)).filter Nat.Prime
  have hprime {t : Finset ℕ} (ht : t ∈ P.powerset) : ∀ p ∈ t, p.Prime :=
    fun p hp => (Finset.mem_filter.mp (Finset.mem_powerset.mp ht hp)).2
  symm
  apply Finset.sum_bij_ne_zero (fun t _ _ => ∏ p ∈ t, p)
  · intro t ht hnz
    exact Finset.mem_Icc.mpr ⟨Finset.prod_pos fun p hp => (hprime ht p hp).pos,
      le_of_not_gt fun h => hnz (by rw [hcut _ h, mul_zero])⟩
  · intro s hs _ t ht _ he
    exact (Nat.primeFactors_prod (hprime hs)).symm.trans
      ((congrArg Nat.primeFactors he).trans (Nat.primeFactors_prod (hprime ht)))
  · intro q hq hnz
    have hq' := Finset.mem_Icc.mp hq
    have hsq : Squarefree q := by
      by_contra hh
      exact hnz (by rw [coefficient_not_squarefree n hq'.1 hh]; simp)
    have hprod := Nat.prod_primeFactors_of_squarefree hsq
    have hsub : q.primeFactors ∈ P.powerset := by
      apply Finset.mem_powerset.mpr
      intro p hp
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_of_mem_primeFactors hp).trans hq'.2)),
          Nat.prime_of_mem_primeFactors hp⟩
    have hc := coefficient_prime_product n q.primeFactors (hprime hsub)
    rw [hprod] at hc
    exact ⟨q.primeFactors, hsub,
      fun hh => hnz (by rw [hprod] at hh; simpa only [hc, Complex.ofReal_re] using hh), hprod⟩
  · intro t ht _
    rw [coefficient_prime_product n t (hprime ht), Complex.ofReal_re]

private theorem signed_powerset_floor (n : ℕ) (W : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ W k)
    (hmono : ∀ i j, 0 < i → i ≤ j → W j ≤ W i)
    (B G : Finset ℕ) (hB : ∀ p ∈ B, (p.Prime ∧ 2 < p) ∧ ¬ p ∣ n)
    (hG : ∀ p ∈ G, p.Prime ∧ p ∣ n) (d : ℕ) (hd : 0 < d) :
    W d / 3 ≤ ∑ t ∈ (G ∪ B).powerset,
      (∏ p ∈ t, localCoefficient p n) * W (d * ∏ p ∈ t, p) := by
  classical
  induction G using Finset.induction_on generalizing d with
  | empty =>
    rw [Finset.empty_union]
    apply (negative_factors_lower (fun p hp => (hB p hp).1) W hnonneg hmono hd).trans
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro t ht
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    simp [localCoefficient, badFactor, (hB p (Finset.mem_powerset.mp ht hp)).2]
  | @insert p G hp ih =>
    have hp' := hG p (Finset.mem_insert_self _ _)
    have hG' : ∀ r ∈ G, r.Prime ∧ r ∣ n := fun r hr => hG _ (Finset.mem_insert_of_mem hr)
    have hpB : p ∉ B := fun h => (hB p h).2 hp'.2
    have hpGB : p ∉ G ∪ B := by simp [hp, hpB]
    have hsign : 0 ≤ localCoefficient p n := by
      have h : (1 : ℝ) < p := by exact_mod_cast hp'.1.one_lt
      simp [localCoefficient, hp'.2, le_of_lt h]
    rw [Finset.insert_union, Finset.sum_powerset_insert hpGB]
    have hsecond : 0 ≤ ∑ t ∈ (G ∪ B).powerset, (∏ r ∈ insert p t, localCoefficient r n) *
        W (d * ∏ r ∈ insert p t, r) := by
      calc
        0 ≤ localCoefficient p n * (∑ t ∈ (G ∪ B).powerset, (∏ r ∈ t, localCoefficient r n) *
            W (d * p * ∏ r ∈ t, r)) :=
          mul_nonneg hsign ((div_nonneg (hnonneg _) (by norm_num)).trans (ih hG' _ (Nat.mul_pos hd hp'.1.pos)))
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          have hpt : p ∉ t := fun h => hpGB (Finset.mem_powerset.mp ht h)
          rw [Finset.prod_insert hpt, Finset.prod_insert hpt, ← mul_assoc d,
            mul_assoc (localCoefficient p n)]
    linarith [ih hG' d hd]

private theorem arithmetic_floor {Q n : ℕ} (hn : Even n) (W : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ W k)
    (hmono : ∀ i j, 0 < i → i ≤ j → W j ≤ W i) (hcut : ∀ q, Q < q → W q = 0) :
    W 1 / 3 ≤ ∑ q ∈ Finset.Icc 1 Q, (coefficient q n).re * W q := by
  classical
  let P := (Finset.range (Q + 1)).filter Nat.Prime
  let G := P.filter (fun p => p ∣ n)
  let B := P.filter (fun p => ¬ p ∣ n)
  have hGB : G ∪ B = P := by ext p; simp [G, B]; tauto
  have hB (p : ℕ) (hp : p ∈ B) : (p.Prime ∧ 2 < p) ∧ ¬ p ∣ n := by
    have hp' := (Finset.mem_filter.mp hp)
    have hpr := (Finset.mem_filter.mp hp'.1).2
    have hne : p ≠ 2 := fun e => hp'.2 (e ▸ even_iff_two_dvd.mp hn)
    exact ⟨⟨hpr, lt_of_le_of_ne hpr.two_le (Ne.symm hne)⟩, hp'.2⟩
  have hG (p : ℕ) (hp : p ∈ G) : p.Prime ∧ p ∣ n :=
    ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2, (Finset.mem_filter.mp hp).2⟩
  have h := signed_powerset_floor n W hnonneg hmono B G hB hG 1 zero_lt_one
  rw [hGB] at h
  rw [reindex_denominators Q n W hcut]
  simpa only [one_mul] using h

private theorem kernelMass_floor (N : ℕ) (W : ℝ) (hW_pos : 0 < W) (hW_le : W ≤ 1 / 2) :
    ((N + 1 : ℕ) : ℝ) - 1 / (2 * W) ≤
      intervalIntegral (fun b => ‖∑ k ∈ Finset.range (N + 1), Efn ((k : ℝ) * b)‖ ^ 2)
        (-W) W volume := by
  let K : ℕ → ℝ → ℂ := fun N b => ∑ k ∈ Finset.range (N + 1), Efn ((k : ℝ) * b)
  change ((N + 1 : ℕ) : ℝ) - 1 / (2 * W) ≤ intervalIntegral (fun b => ‖K N b‖ ^ 2) (-W) W volume
  have hEmul : ∀ a b : ℝ, Efn a * Efn b = Efn (a + b) := by
    intro a b
    simp only [Efn, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hEconj : ∀ x : ℝ, star (Efn x) = Efn (-x) := by
    intro x
    simp only [Efn, Complex.star_def, Complex.exp_ofReal_mul_I, map_add, map_mul,
      Complex.conj_ofReal, Complex.conj_I]
    have h1 : (2 : ℝ) * Real.pi * (-x) = -(2 * Real.pi * x) := by ring
    rw [h1, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have hEpow : ∀ (k : ℕ) (b : ℝ), Efn ((k : ℝ) * b) = (Efn b) ^ k := by
    intro k b
    simp only [Efn, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hKneg : ∀ b : ℝ, ‖K N (-b)‖ ^ 2 = ‖K N b‖ ^ 2 := by
    intro b
    have h1 : K N (-b) = star (K N b) := by
      simp only [K, star_sum, hEconj]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      ring
    rw [h1, norm_star]
  have hE_cont : ∀ c : ℝ, Continuous (fun b : ℝ => Efn (c * b)) := fun c => by
    unfold Efn
    fun_prop
  have hsum_cont : ∀ (s : Finset ℕ) (f : ℕ → ℝ → ℂ),
      (∀ k ∈ s, Continuous (f k)) → Continuous (fun b => ∑ k ∈ s, f k b) := by
    intro s f hf
    induction s using Finset.induction with
    | empty => simpa using continuous_const
    | @insert a s ha ih =>
        simp_rw [Finset.sum_insert ha]
        exact (hf a (Finset.mem_insert_self _ _)).add
          (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))
  have hK_cont : Continuous (fun b : ℝ => K N b) :=
    hsum_cont (Finset.range (N + 1)) (fun k b => Efn ((k : ℝ) * b)) fun k _ => hE_cont (k : ℝ)
  have hnormSq_cont : Continuous (fun b : ℝ => ‖K N b‖ ^ 2) := (hK_cont.norm).pow 2
  have hnormSq_int : ∀ a c : ℝ, IntervalIntegrable (fun b : ℝ => ‖K N b‖ ^ 2) volume a c :=
    fun a c => hnormSq_cont.intervalIntegrable a c
  have hint_E_int : ∀ m : ℤ,
      intervalIntegral (fun b : ℝ => Efn ((m : ℝ) * b)) (-1 / 2) (1 / 2) volume =
        if m = 0 then (1 : ℂ) else 0 := by
    intro m
    by_cases hm : m = 0
    · subst hm
      simp [Efn]
      norm_num
    · set c : ℂ := ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I
      have hc : c ≠ 0 := by
        have hmR : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
        have hpi : (2 * Real.pi * (m : ℝ) : ℝ) ≠ 0 :=
          mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hmR
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hpi) Complex.I_ne_zero
      let F : ℝ → ℂ := fun b => Complex.exp ((b : ℂ) * c) / c
      have hderiv : ∀ b ∈ Set.uIcc (-1 / 2 : ℝ) (1 / 2 : ℝ),
          HasDerivAt F (Efn ((m : ℝ) * b)) b := by
        intro b _
        have hid : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 b := Complex.ofRealCLM.hasDerivAt
        have hmul : HasDerivAt (fun x : ℝ => (x : ℂ) * c) (1 * c) b := hid.mul_const c
        have hexp : HasDerivAt (fun x : ℝ => Complex.exp ((x : ℂ) * c))
            (Complex.exp ((b : ℂ) * c) * (1 * c)) b := hmul.cexp
        have hdiv : HasDerivAt F (Complex.exp ((b : ℂ) * c) * (1 * c) / c) b := hexp.div_const c
        have hval : Complex.exp ((b : ℂ) * c) * (1 * c) / c = Efn ((m : ℝ) * b) := by
          rw [one_mul, mul_div_cancel_right₀ _ hc]
          simp only [Efn, c]
          congr 1
          push_cast
          ring
        rwa [hval] at hdiv
      have hint : IntervalIntegrable (fun b : ℝ => Efn ((m : ℝ) * b)) volume (-1 / 2) (1 / 2) :=
        (hE_cont (m : ℝ)).intervalIntegrable _ _
      simp only [hm, ↓reduceIte]
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
      have hhalf : Complex.exp (((1 / 2 : ℝ) : ℂ) * c) =
          Complex.exp ((((-1 / 2 : ℝ) : ℂ) * c)) := by
        have hpos : ((1 / 2 : ℝ) : ℂ) * c = (((m : ℝ) * Real.pi : ℝ) : ℂ) * Complex.I := by
          simp only [c]; push_cast; ring
        have hneg : ((-1 / 2 : ℝ) : ℂ) * c = ((((-m : ℤ) : ℝ) * Real.pi : ℝ) : ℂ) * Complex.I := by
          simp only [c]; push_cast; ring
        rw [hpos, hneg, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I,
          Real.sin_int_mul_pi m, Real.sin_int_mul_pi (-m)]
        have hcos : Real.cos (((-m : ℤ) : ℝ) * Real.pi) = Real.cos ((m : ℝ) * Real.pi) := by
          push_cast
          rw [neg_mul, Real.cos_neg]
        rw [hcos]
      simp only [F, hhalf, sub_self]
  have hfull_mass :
      intervalIntegral (fun b => ‖K N b‖ ^ 2) (-1 / 2) (1 / 2) volume = ((N + 1 : ℕ) : ℝ) := by
    have hK_expand : ∀ b : ℝ, ((‖K N b‖ ^ 2 : ℝ) : ℂ) =
        ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
          Efn ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * b) := by
      intro b
      calc
        ((‖K N b‖ ^ 2 : ℝ) : ℂ) = K N b * star (K N b) := by
            rw [Complex.star_def, Complex.mul_conj']
            push_cast
            ring
        _ = (∑ j ∈ Finset.range (N + 1), Efn ((j : ℝ) * b)) *
              (∑ k ∈ Finset.range (N + 1), Efn (-((k : ℝ) * b))) := by
            simp only [K, star_sum, hEconj]
        _ = ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
              Efn ((j : ℝ) * b) * Efn (-((k : ℝ) * b)) := Finset.sum_mul_sum ..
        _ = ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
              Efn ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * b) := by
            refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
            rw [hEmul]
            congr 1
            push_cast
            ring
    have hint_sum : ∀ (s : Finset ℕ) (f : ℕ → ℝ → ℂ),
        (∀ k ∈ s, Continuous (f k)) →
        intervalIntegral (fun b => ∑ k ∈ s, f k b) (-1 / 2) (1 / 2) volume =
          ∑ k ∈ s, intervalIntegral (f k) (-1 / 2) (1 / 2) volume := by
      intro s f hf
      induction s using Finset.induction with
      | empty => simp
      | @insert a s ha ih =>
          simp_rw [Finset.sum_insert ha]
          have ha_int : IntervalIntegrable (f a) volume (-1 / 2) (1 / 2) :=
            (hf a (Finset.mem_insert_self _ _)).intervalIntegrable (-1 / 2) (1 / 2)
          have hs_int : IntervalIntegrable (fun b => ∑ k ∈ s, f k b) volume (-1 / 2) (1 / 2) :=
            (hsum_cont s f fun k hk => hf k (Finset.mem_insert_of_mem hk)).intervalIntegrable _ _
          rw [intervalIntegral.integral_add ha_int hs_int,
            ih fun k hk => hf k (Finset.mem_insert_of_mem hk)]
    have hC : ((intervalIntegral (fun b => ‖K N b‖ ^ 2) (-1 / 2) (1 / 2) volume : ℝ) : ℂ) =
        ((N + 1 : ℕ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      simp_rw [hK_expand]
      rw [hint_sum _ _ fun j _ =>
        hsum_cont (Finset.range (N + 1)) (fun k b => Efn ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * b))
          fun k _ => hE_cont (((j : ℤ) - (k : ℤ) : ℤ) : ℝ)]
      have hinner : ∀ j ∈ Finset.range (N + 1),
          intervalIntegral (fun b => ∑ k ∈ Finset.range (N + 1),
            Efn ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * b)) (-1 / 2) (1 / 2) volume = 1 := by
        intro j hj
        rw [hint_sum _ _ fun k _ => hE_cont (((j : ℤ) - (k : ℤ) : ℤ) : ℝ)]
        have hterm : ∀ k ∈ Finset.range (N + 1),
            intervalIntegral (fun b => Efn ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * b))
              (-1 / 2) (1 / 2) volume = if k = j then (1 : ℂ) else 0 := by
          intro k _
          rw [hint_E_int]
          split_ifs with h1 h2 h2
          · rfl
          · exfalso; apply h2; omega
          · exfalso; apply h1; omega
          · rfl
        rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' _ j (fun _ => (1 : ℂ))]
        simp only [hj, ↓reduceIte]
      rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact Complex.ofReal_inj.mp hC
  have hK_tail_pointwise : ∀ b ∈ Set.Icc W (1 / 2 : ℝ), ‖K N b‖ ^ 2 ≤ 1 / (4 * b ^ 2) := by
    intro b hb
    have hbW : W ≤ b := hb.1
    have hb12 : b ≤ 1 / 2 := hb.2
    have hb_pos : 0 < b := lt_of_lt_of_le hW_pos hbW
    have hgeom : (1 - Efn b) * K N b = 1 - Efn (((N + 1 : ℕ) : ℝ) * b) := by
      simp_rw [K, hEpow]
      rw [mul_comm, geom_sum_mul_neg]
    have hnum : ‖1 - Efn (((N + 1 : ℕ) : ℝ) * b)‖ ≤ 2 := by
      have hnorm1 : ‖Efn (((N + 1 : ℕ) : ℝ) * b)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
      have htri := norm_sub_le (1 : ℂ) (Efn (((N + 1 : ℕ) : ℝ) * b))
      rw [norm_one, hnorm1] at htri
      linarith
    have hsin_lb : 2 * b ≤ Real.sin (Real.pi * b) := by
      have h1 : 0 ≤ Real.pi * b := by positivity
      have h2 : Real.pi * b ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
      have hsin := Real.mul_le_sin h1 h2
      have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
      calc
        2 * b = 2 / Real.pi * (Real.pi * b) := by field_simp [hpi_ne]
        _ ≤ Real.sin (Real.pi * b) := hsin
    have hden_sq : 16 * b ^ 2 ≤ ‖1 - Efn b‖ ^ 2 := by
      have hnormSq : ‖1 - Efn b‖ ^ 2 = (1 - Real.cos (2 * Real.pi * b)) ^ 2 +
          (-Real.sin (2 * Real.pi * b)) ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp only [Efn, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
          Complex.exp_ofReal_mul_I, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, sub_zero, add_zero,
          Complex.add_im, Complex.mul_im, mul_one, zero_add, zero_sub]
        ring
      have hcos2 : Real.cos (2 * Real.pi * b) = 1 - 2 * (Real.sin (Real.pi * b)) ^ 2 := by
        have h := Real.cos_two_mul (Real.pi * b)
        rw [show 2 * (Real.pi * b) = 2 * Real.pi * b by ring] at h
        have hcs := Real.cos_sq_add_sin_sq (Real.pi * b)
        linarith
      have hcs2 := Real.cos_sq_add_sin_sq (2 * Real.pi * b)
      have htrig : (1 - Real.cos (2 * Real.pi * b)) ^ 2 + (-Real.sin (2 * Real.pi * b)) ^ 2 =
          4 * (Real.sin (Real.pi * b)) ^ 2 := by
        nlinarith
      rw [hnormSq, htrig]
      nlinarith [sq_nonneg (Real.sin (Real.pi * b) - 2 * b)]
    have hden : 4 * b ≤ ‖1 - Efn b‖ := by
      nlinarith [norm_nonneg (1 - Efn b)]
    have hK_le : ‖K N b‖ ≤ 1 / (2 * b) := by
      have hmul_le : 4 * b * ‖K N b‖ ≤ 2 := by
        calc
          4 * b * ‖K N b‖ ≤ ‖1 - Efn b‖ * ‖K N b‖ :=
              mul_le_mul_of_nonneg_right hden (norm_nonneg _)
          _ = ‖(1 - Efn b) * K N b‖ := (norm_mul _ _).symm
          _ = ‖1 - Efn (((N + 1 : ℕ) : ℝ) * b)‖ := by rw [hgeom]
          _ ≤ 2 := hnum
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hK_sq : ‖K N b‖ ^ 2 ≤ (1 / (2 * b)) ^ 2 := by
      nlinarith [norm_nonneg (K N b)]
    calc
      ‖K N b‖ ^ 2 ≤ (1 / (2 * b)) ^ 2 := hK_sq
      _ = 1 / (4 * b ^ 2) := by ring
  have h_inv_sq_int :
      intervalIntegral (fun b : ℝ => 1 / (4 * b ^ 2)) W (1 / 2) volume =
        1 / (4 * W) - 1 / 2 := by
    let G : ℝ → ℝ := fun b => -(1 / (4 * b))
    have hGderiv : ∀ b ∈ Set.uIcc W (1 / 2 : ℝ), HasDerivAt G (1 / (4 * b ^ 2)) b := by
      intro b hb
      rw [Set.uIcc_of_le hW_le] at hb
      have hb_ne : b ≠ 0 := ne_of_gt (lt_of_lt_of_le hW_pos hb.1)
      have h1 : HasDerivAt (fun x : ℝ => -(4 * x)⁻¹) (-(-4 / (4 * b) ^ 2)) b := by
        have hm : HasDerivAt (fun x : ℝ => 4 * x) 4 b := by
          simpa using (hasDerivAt_id b).const_mul (4 : ℝ)
        exact (hm.inv (mul_ne_zero four_ne_zero hb_ne)).neg
      have hGeq : G = fun x : ℝ => -(4 * x)⁻¹ := by
        ext x; simp [G, one_div]
      have hval : -(-4 / (4 * b) ^ 2) = 1 / (4 * b ^ 2) := by
        field_simp [hb_ne]
      rw [hGeq, ← hval]
      exact h1
    have hGint : IntervalIntegrable (fun b : ℝ => 1 / (4 * b ^ 2)) volume W (1 / 2) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hW_le]
      refine continuousOn_const.div (continuousOn_const.mul (continuousOn_id.pow 2)) ?_
      intro b hb
      have hb_ne : b ≠ 0 := ne_of_gt (lt_of_lt_of_le hW_pos hb.1)
      exact mul_ne_zero four_ne_zero (pow_ne_zero 2 hb_ne)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hGderiv hGint]
    have hW_ne : W ≠ 0 := ne_of_gt hW_pos
    simp only [G]
    field_simp [hW_ne]
    ring
  have hright_tail :
      intervalIntegral (fun b => ‖K N b‖ ^ 2) W (1 / 2) volume ≤ 1 / (4 * W) := by
    have hinv_int : IntervalIntegrable (fun b : ℝ => 1 / (4 * b ^ 2)) volume W (1 / 2) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hW_le]
      refine continuousOn_const.div (continuousOn_const.mul (continuousOn_id.pow 2)) ?_
      intro b hb
      have hb_ne : b ≠ 0 := ne_of_gt (lt_of_lt_of_le hW_pos hb.1)
      exact mul_ne_zero four_ne_zero (pow_ne_zero 2 hb_ne)
    have hmono := intervalIntegral.integral_mono_on hW_le (hnormSq_int W (1 / 2)) hinv_int
      hK_tail_pointwise
    linarith [hmono, h_inv_sq_int]
  have hleft_tail :
      intervalIntegral (fun b => ‖K N b‖ ^ 2) (-1 / 2) (-W) volume ≤ 1 / (4 * W) := by
    have hsymm :
        intervalIntegral (fun b => ‖K N b‖ ^ 2) (-1 / 2) (-W) volume =
          intervalIntegral (fun b => ‖K N b‖ ^ 2) W (1 / 2) volume := by
      calc
        intervalIntegral (fun b => ‖K N b‖ ^ 2) (-1 / 2) (-W) volume
            = intervalIntegral (fun b => ‖K N (-b)‖ ^ 2) (-1 / 2) (-W) volume := by
                simp_rw [hKneg]
        _ = intervalIntegral (fun b => ‖K N b‖ ^ 2) (-(-W)) (-(-1 / 2)) volume :=
                intervalIntegral.integral_comp_neg (fun b => ‖K N b‖ ^ 2)
        _ = intervalIntegral (fun b => ‖K N b‖ ^ 2) W (1 / 2) volume := by
                norm_num
    rw [hsymm]
    exact hright_tail
  have hsplit1 :
      intervalIntegral (fun b => ‖K N b‖ ^ 2) (-1 / 2) (-W) volume +
        intervalIntegral (fun b => ‖K N b‖ ^ 2) (-W) (1 / 2) volume =
          intervalIntegral (fun b => ‖K N b‖ ^ 2) (-1 / 2) (1 / 2) volume :=
    intervalIntegral.integral_add_adjacent_intervals (hnormSq_int _ _) (hnormSq_int _ _)
  have hsplit2 :
      intervalIntegral (fun b => ‖K N b‖ ^ 2) (-W) W volume +
        intervalIntegral (fun b => ‖K N b‖ ^ 2) W (1 / 2) volume =
          intervalIntegral (fun b => ‖K N b‖ ^ 2) (-W) (1 / 2) volume :=
    intervalIntegral.integral_add_adjacent_intervals (hnormSq_int _ _) (hnormSq_int _ _)
  have hsum :
      intervalIntegral (fun b => ‖K N b‖ ^ 2) (-1 / 2) (-W) volume +
        intervalIntegral (fun b => ‖K N b‖ ^ 2) (-W) W volume +
        intervalIntegral (fun b => ‖K N b‖ ^ 2) W (1 / 2) volume =
          ((N + 1 : ℕ) : ℝ) := by
    linarith [hsplit1, hsplit2, hfull_mass]
  have hhalf : 1 / (2 * W) = 1 / (4 * W) + 1 / (4 * W) := by ring
  linarith

end Conjectures.Goldbach.ExplicitModeledMajorFloor_aux

theorem Conjectures.Goldbach.ExplicitModeledMajorFloor :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let Q (n : ℕ) := (Nat.log 2 (n + 2)) ^ 2; let width (n q : ℕ) := (Q n : ℝ) / ((q : ℝ) * n); let K (n : ℕ) (β : ℝ) := ∑ k ∈ Finset.range (n + 1), E ((k : ℝ) * β); let ram (q h : ℕ) := ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), E ((h : ℝ) * a / q); let kernelMass (n : ℕ) (b : ℝ) := intervalIntegral (fun β => ‖K n β‖ ^ 2) (-b) b MeasureTheory.volume; let modeledMajor (n : ℕ) := ∑ q ∈ Finset.Icc 1 (Q n), ((ram q 1 / (q.totient : ℂ)) ^ 2 * (starRingEnd ℂ) (ram q n)) * (kernelMass n (width n q) : ℂ); ∀ n : ℕ, 1000000 ≤ n → Even n → (n : ℝ) / 72 ≤ (modeledMajor n).re := by
  intro E Q width K ram kernelMass modeledMajor n hn heven
  have hlog_ge : 19 ≤ Nat.log 2 (n + 2) := by
    refine Nat.le_log_of_pow_le (by decide) ?_
    omega
  have hQ_ge : 361 ≤ Q n := by
    dsimp only [Q]
    nlinarith
  have hQ_pos : 1 ≤ Q n := by omega
  have hpow_bound : ∀ k : ℕ, 19 ≤ k → 2 * k ^ 2 + 2 ≤ 2 ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => decide
    | @succ k hk ih =>
        have hstep : 4 * k + 2 ≤ 2 * k ^ 2 + 2 := by nlinarith
        have hsq : 2 * (k + 1) ^ 2 + 2 = 2 * k ^ 2 + 2 + (4 * k + 2) := by ring
        have hpow2 : 2 ^ (k + 1) = 2 * 2 ^ k := pow_succ' 2 k
        linarith
  have h2Q_le_n : 2 * Q n ≤ n := by
    have h1 : 2 * Q n + 2 ≤ 2 ^ (Nat.log 2 (n + 2)) := hpow_bound _ hlog_ge
    have h2 : 2 ^ (Nat.log 2 (n + 2)) ≤ n + 2 := Nat.pow_log_le_self 2 (by omega)
    omega
  let W : ℕ → ℝ := fun q => if q ≤ Q n then kernelMass n (width n q) else 0
  have hW_nonneg : ∀ q : ℕ, 0 ≤ W q := by
    intro q
    dsimp only [W]
    split_ifs
    · have hw0 : 0 ≤ width n q := by dsimp only [width]; positivity
      exact intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
    · exact le_rfl
  have hK_cont : Continuous (fun β : ℝ => ‖K n β‖ ^ 2) := by
    have hsum_cont : ∀ (s : Finset ℕ) (f : ℕ → ℝ → ℂ),
        (∀ k ∈ s, Continuous (f k)) → Continuous (fun b => ∑ k ∈ s, f k b) := by
      intro s f hf
      induction s using Finset.induction with
      | empty => simpa using continuous_const
      | @insert a s ha ih =>
          simp_rw [Finset.sum_insert ha]
          exact (hf a (Finset.mem_insert_self _ _)).add
            (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))
    have hE_cont : ∀ k : ℕ, Continuous (fun b : ℝ => E ((k : ℝ) * b)) := fun k => by
      unfold E
      fun_prop
    exact ((hsum_cont (Finset.range (n + 1)) (fun k b => E ((k : ℝ) * b)) (fun k _ => hE_cont k)).norm).pow 2
  have hW_mono : ∀ i j : ℕ, 0 < i → i ≤ j → W j ≤ W i := by
    intro i j hi hij
    dsimp only [W]
    by_cases hj : j ≤ Q n
    · have hiQ : i ≤ Q n := hij.trans hj
      rw [ite_eq_left hj, ite_eq_left hiQ]
      have hwij : width n j ≤ width n i := by
        dsimp only [width]
        have hiR : (0 : ℝ) < i := by exact_mod_cast hi
        have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos hiR hnR)
          (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hnR.le)
      have hwj0 : 0 ≤ width n j := by dsimp only [width]; positivity
      exact intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
        (Filter.Eventually.of_forall fun _ => sq_nonneg _) (hK_cont.intervalIntegrable _ _)
    · rw [ite_eq_right hj]
      split_ifs
      · have hw0 : 0 ≤ width n i := by dsimp only [width]; positivity
        exact intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
      · exact le_rfl
  have hW_cut : ∀ q : ℕ, Q n < q → W q = 0 := fun q hq => by
    dsimp only [W]
    exact ite_eq_right (not_le.mpr hq)
  have har := Conjectures.Goldbach.ExplicitModeledMajorFloor_aux.arithmetic_floor
    heven W hW_nonneg hW_mono hW_cut
  have hre : (modeledMajor n).re =
      ∑ q ∈ Finset.Icc 1 (Q n),
        (Conjectures.Goldbach.ExplicitModeledMajorFloor_aux.coefficient q n).re * W q := by
    dsimp only [modeledMajor]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hqQ : q ≤ Q n := (Finset.mem_Icc.mp hq).2
    have hcoeff :
        ((ram q 1 / (q.totient : ℂ)) ^ 2 * (starRingEnd ℂ) (ram q n)) =
          Conjectures.Goldbach.ExplicitModeledMajorFloor_aux.coefficient q n := by
      rfl
    have hWq : W q = kernelMass n (width n q) := ite_eq_left hqQ
    rw [hcoeff, hWq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hw1_pos : 0 < width n 1 := by
    dsimp only [width]
    have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hQR : (0 : ℝ) < Q n := by exact_mod_cast hQ_pos
    positivity
  have hw1_le : width n 1 ≤ 1 / 2 := by
    dsimp only [width]
    have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    rw [Nat.cast_one, one_mul, div_le_div_iff₀ hnR (by norm_num)]
    have h2Q_R : 2 * (Q n : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2Q_le_n
    linarith
  have hkm1 : (n : ℝ) / 2 ≤ kernelMass n (width n 1) := by
    have hfloor := Conjectures.Goldbach.ExplicitModeledMajorFloor_aux.kernelMass_floor
      n (width n 1) hw1_pos hw1_le
    have hkm_eq : kernelMass n (width n 1) =
        intervalIntegral (fun b => ‖∑ k ∈ Finset.range (n + 1),
          Conjectures.Goldbach.ExplicitModeledMajorFloor_aux.Efn ((k : ℝ) * b)‖ ^ 2)
          (-width n 1) (width n 1) volume := rfl
    rw [← hkm_eq] at hfloor
    have htail_le : 1 / (2 * width n 1) ≤ (n : ℝ) / 2 := by
      have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hQR : (1 : ℝ) ≤ Q n := by exact_mod_cast hQ_pos
      have h2w : 2 * width n 1 = 2 * (Q n : ℝ) / (n : ℝ) := by
        dsimp only [width]
        ring
      rw [h2w, one_div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hnp1 : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
    linarith
  have hW1 : W 1 = kernelMass n (width n 1) := ite_eq_left hQ_pos
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith
