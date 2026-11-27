import Mathlib

/-!
# Lower bound for the initial Farey sieve (HD-8011)

We partition the odd sieving primes into blocks with adjacent square-root
cutoffs. An even Bonferroni expansion and the first omitted term in one block
at a time give a lower sieve. A fixed exponential tilt controls the sum of
the first omitted factorial tails for ranks growing with U and the block index.
Squarefree intersection counts and an explicit support bound pay for rounding.
The proof compares both losses with the terminal product at sqrt(n).

The finite upper expansions and the elementary Legendre identities adapt
material by Sushaan Kandukoori (copyright 2026, Apache-2.0):
  https://github.com/sushaan-k/erdos-straus-lean/tree/f6c99eaaca6ec7a7226a7a16bef1cd2b09e36660/ErdosStraus/Estimates
The full-window intersection count, the terminal floor, and real-product
comparison helpers are reused from this project's Apache-2.0 sources
FareyFullSieveRemainder, FareySieveTerminalFloor and FareySieveCutoffRatio.
The final statement is the frozen task statement.
-/

/- Adapted from ErdosStraus/Estimates/BrunHooley.lean (Apache-2.0),
   sushaan-k/erdos-straus-lean, revision f6c99eaaca6ec7a7226a7a16bef1cd2b09e36660.
   This excerpt retains the finite combinatorial identities and omits the progression application. -/

lemma fareyProdLe {ι : Type*} {s : Finset ι} {f g : ι → ℝ}
    (hf0 : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h1 : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
      ih (fun i hi => hf0 i (by simp [hi])) (fun i hi => hfg i (by simp [hi]))
    have h2 : (0:ℝ) ≤ ∏ i ∈ s, f i := Finset.prod_nonneg (fun i hi => hf0 i (by simp [hi]))
    have h3 : f a ≤ g a := hfg a (by simp)
    have h4 : (0:ℝ) ≤ f a := hf0 a (by simp)
    have h5 : (0:ℝ) ≤ g a := le_trans h4 h3
    exact mul_le_mul h3 h1 h2 h5

lemma fareyProdOne {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hprod : ∏ i ∈ s, f i ≤ 1 :=
      ih (fun i hi => h0 i (by simp [hi])) (fun i hi => h1 i (by simp [hi]))
    have hnonneg : (0:ℝ) ≤ ∏ i ∈ s, f i := Finset.prod_nonneg (fun i hi => h0 i (by simp [hi]))
    have ha1 : f a ≤ 1 := h1 a (by simp)
    calc f a * (∏ i ∈ s, f i) ≤ 1 * 1 := mul_le_mul ha1 hprod hnonneg (by norm_num)
      _ = 1 := by norm_num

namespace ErdosStraus.RoughEstimates

open scoped BigOperators

section

open scoped Classical

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

/-- The number of `n ∈ A` with `hit i n` for every `i ∈ u`. -/
noncomputable def intersectionCount (A : Finset α) (hit : ι → α → Prop)
    (u : Finset ι) : ℝ := by
  classical
  exact ((A.filter (fun n => ∀ i ∈ u, hit i n)).card : ℝ)

end

/-! ## Bonferroni inequalities -/

variable {ι : Type*} [DecidableEq ι]

/-- The elementary symmetric sum `e_m(w) = ∑_{u ⊆ s, |u| = m} ∏_{i ∈ u} w i`. -/
noncomputable def elementary (s : Finset ι) (w : ι → ℝ) (m : ℕ) : ℝ :=
  ∑ u ∈ s.powersetCard m, ∏ i ∈ u, w i

/-- The truncation `∑_{j ≤ m} (-1)^j e_j(w)` of the expansion of `∏_{i ∈ s} (1 - w i)`. -/
noncomputable def truncation (s : Finset ι) (w : ι → ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), (-1 : ℝ) ^ j * elementary s w j

omit [DecidableEq ι] in
@[simp] theorem elementary_zero (s : Finset ι) (w : ι → ℝ) :
    elementary s w 0 = 1 := by
  simp [elementary]

omit [DecidableEq ι] in
@[simp] theorem elementary_empty_succ (w : ι → ℝ) (m : ℕ) :
    elementary ∅ w (m + 1) = 0 := by
  have h : (∅ : Finset ι).powersetCard (m + 1) = ∅ := by
    rw [Finset.powersetCard_eq_empty]
    simp
  simp [elementary, h]

theorem elementary_insert {s : Finset ι} {a : ι} (ha : a ∉ s)
    (w : ι → ℝ) (m : ℕ) :
    elementary (insert a s) w (m + 1) =
      elementary s w (m + 1) + w a * elementary s w m := by
  unfold elementary
  rw [Finset.powersetCard_succ_insert ha]
  have hdis : Disjoint (s.powersetCard (m + 1))
      ((s.powersetCard m).image (insert a)) := by
    apply Finset.disjoint_left.mpr
    intro u hu hv
    rcases Finset.mem_image.mp hv with ⟨v, hv, rfl⟩
    exact ha ((Finset.mem_powersetCard.mp hu).1 (Finset.mem_insert_self a v))
  rw [Finset.sum_union hdis, Finset.sum_image]
  · congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    have hau : a ∉ u := fun h => ha ((Finset.mem_powersetCard.mp hu).1 h)
    rw [Finset.prod_insert hau]
  · intro u hu v hv huv
    have hau : a ∉ u := fun h => ha ((Finset.mem_powersetCard.mp hu).1 h)
    have hav : a ∉ v := fun h => ha ((Finset.mem_powersetCard.mp hv).1 h)
    have he := congrArg (fun t : Finset ι => t.erase a) huv
    simpa [Finset.erase_insert hau, Finset.erase_insert hav] using he

omit [DecidableEq ι] in
@[simp] theorem truncation_zero (s : Finset ι) (w : ι → ℝ) :
    truncation s w 0 = 1 := by
  simp [truncation]

omit [DecidableEq ι] in
@[simp] theorem truncation_empty (w : ι → ℝ) (m : ℕ) :
    truncation ∅ w m = 1 := by
  induction m with
  | zero => simp
  | succ m ih => simpa [truncation, Finset.sum_range_succ] using ih

theorem truncation_insert {s : Finset ι} {a : ι} (ha : a ∉ s)
    (w : ι → ℝ) (m : ℕ) :
    truncation (insert a s) w (m + 1) =
      truncation s w (m + 1) - w a * truncation s w m := by
  have hsucc (t : Finset ι) (j : ℕ) :
      truncation t w (j + 1) = truncation t w j +
        (-1 : ℝ) ^ (j + 1) * elementary t w (j + 1) := by
    simp [truncation, Finset.sum_range_succ]
  induction m with
  | zero =>
    rw [hsucc, hsucc, elementary_insert ha]
    simp only [truncation_zero, elementary_zero, zero_add, pow_one, neg_one_mul,
      mul_one]
    ring
  | succ m ih =>
    rw [hsucc (insert a s), ih, elementary_insert ha w (m + 1),
      hsucc s (m + 1), hsucc s m]
    rw [pow_succ, pow_succ]
    ring

omit [DecidableEq ι] in
theorem elementary_nonneg (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (m : ℕ) : 0 ≤ elementary s w m := by
  apply Finset.sum_nonneg
  intro u hu
  apply Finset.prod_nonneg
  intro i hi
  exact hw i ((Finset.mem_powersetCard.mp hu).1 hi)

omit [DecidableEq ι] in
theorem prod_one_sub_mem_unit (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ 1) :
    0 ≤ (∏ i ∈ s, (1 - w i)) ∧ (∏ i ∈ s, (1 - w i)) ≤ 1 := by
  constructor
  · exact Finset.prod_nonneg (fun i hi => sub_nonneg.mpr (hw i hi).2)
  · exact fareyProdOne (fun i hi => sub_nonneg.mpr (hw i hi).2)
      (fun i hi => by linarith [(hw i hi).1])

theorem one_sub_prod_le_elementary_one (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ 1) :
    1 - (∏ i ∈ s, (1 - w i)) ≤ elementary s w 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hwa := hw a (Finset.mem_insert_self a s)
    have hws : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ 1 :=
      fun i hi => hw i (Finset.mem_insert_of_mem hi)
    have hp := prod_one_sub_mem_unit s w hws
    have hh := ih hws
    rw [Finset.prod_insert ha, elementary_insert ha]
    simp only [elementary_zero, mul_one]
    nlinarith

/-- Bonferroni's inequalities: for weights `0 ≤ w i ≤ 1` and the truncation `T_m` at rank `m`,
`0 ≤ (-1)^m (T_m - ∏_{i ∈ s} (1 - w i)) ≤ e_{m+1}(w)`. -/
theorem bonferroni (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ 1) (m : ℕ) :
    0 ≤ (-1 : ℝ) ^ m * (truncation s w m - ∏ i ∈ s, (1 - w i)) ∧
      (-1 : ℝ) ^ m * (truncation s w m - ∏ i ∈ s, (1 - w i)) ≤
        elementary s w (m + 1) := by
  induction s using Finset.induction_on generalizing m with
  | empty => simp
  | @insert a s ha ih =>
    have hwa := hw a (Finset.mem_insert_self a s)
    have hws : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ 1 :=
      fun i hi => hw i (Finset.mem_insert_of_mem hi)
    cases m with
    | zero =>
      simp only [pow_zero, truncation_zero, one_mul, zero_add]
      exact ⟨by linarith [(prod_one_sub_mem_unit (insert a s) w hw).2],
        one_sub_prod_le_elementary_one (insert a s) w hw⟩
    | succ m =>
      have h₁ := ih hws (m + 1)
      have h₀ := ih hws m
      rw [truncation_insert ha, Finset.prod_insert ha,
        elementary_insert ha w (m + 1)]
      have hidentity : (-1 : ℝ) ^ (m + 1) *
          (truncation s w (m + 1) - w a * truncation s w m -
            (1 - w a) * ∏ i ∈ s, (1 - w i)) =
          (-1 : ℝ) ^ (m + 1) *
            (truncation s w (m + 1) - ∏ i ∈ s, (1 - w i)) +
          w a * ((-1 : ℝ) ^ m *
            (truncation s w m - ∏ i ∈ s, (1 - w i))) := by
        rw [pow_succ]
        ring
      rw [hidentity]
      constructor
      · exact add_nonneg h₁.1 (mul_nonneg hwa.1 h₀.1)
      · exact add_le_add h₁.2 (mul_le_mul_of_nonneg_left h₀.2 hwa.1)

/-! ## Bounds for elementary symmetric sums -/

theorem elementary_one (P : Finset ι) (w : ι → ℝ) :
    elementary P w 1 = ∑ i ∈ P, w i := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert a P ha ih =>
    rw [elementary_insert ha, elementary_zero, ih, Finset.sum_insert ha]
    ring

theorem elementary_succ_mul_le (P : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ P, 0 ≤ w i) (m : ℕ) :
    ((m + 1 : ℕ) : ℝ) * elementary P w (m + 1) ≤
      (∑ i ∈ P, w i) * elementary P w m := by
  induction P using Finset.induction_on generalizing m with
  | empty => simp
  | @insert a P ha ih =>
    have hwa : 0 ≤ w a := hw a (Finset.mem_insert_self _ _)
    have hwp : ∀ i ∈ P, 0 ≤ w i := fun i hi => hw i (Finset.mem_insert_of_mem hi)
    cases m with
    | zero => simp [elementary_one]
    | succ m =>
      have h1 := ih hwp (m + 1)
      have h0 := ih hwp m
      have he := elementary_nonneg P w hwp m
      rw [elementary_insert ha w (m + 1), elementary_insert ha w m,
        Finset.sum_insert ha]
      have hd :
          (w a + ∑ i ∈ P, w i) *
              (elementary P w (m + 1) + w a * elementary P w m) -
              ((m + 1 + 1 : ℕ) : ℝ) *
                (elementary P w (m + 1 + 1) + w a * elementary P w (m + 1)) =
            ((∑ i ∈ P, w i) * elementary P w (m + 1) -
              ((m + 1 + 1 : ℕ) : ℝ) * elementary P w (m + 1 + 1)) +
            w a * ((∑ i ∈ P, w i) * elementary P w m -
              ((m + 1 : ℕ) : ℝ) * elementary P w (m + 1)) +
            w a * w a * elementary P w m := by
        push_cast
        ring
      apply sub_nonneg.mp
      rw [hd]
      exact add_nonneg
        (add_nonneg (sub_nonneg.mpr h1) (mul_nonneg hwa (sub_nonneg.mpr h0)))
        (mul_nonneg (mul_nonneg hwa hwa) he)

theorem elementary_le_sum_pow_div_factorial (P : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ P, 0 ≤ w i) (m : ℕ) :
    elementary P w m ≤ (∑ i ∈ P, w i) ^ m / (Nat.factorial m : ℝ) := by
  have hsum : 0 ≤ ∑ i ∈ P, w i := Finset.sum_nonneg hw
  have hmul : ∀ m : ℕ,
      (Nat.factorial m : ℝ) * elementary P w m ≤ (∑ i ∈ P, w i) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hrec := elementary_succ_mul_le P w hw m
      calc
        (Nat.factorial (m + 1) : ℝ) * elementary P w (m + 1) =
            (Nat.factorial m : ℝ) *
              (((m + 1 : ℕ) : ℝ) * elementary P w (m + 1)) := by
          rw [Nat.factorial_succ, Nat.cast_mul]
          ring
        _ ≤ (Nat.factorial m : ℝ) * ((∑ i ∈ P, w i) * elementary P w m) :=
          mul_le_mul_of_nonneg_left hrec (Nat.cast_nonneg _)
        _ = (∑ i ∈ P, w i) * ((Nat.factorial m : ℝ) * elementary P w m) := by ring
        _ ≤ (∑ i ∈ P, w i) * (∑ i ∈ P, w i) ^ m :=
          mul_le_mul_of_nonneg_left ih hsum
        _ = (∑ i ∈ P, w i) ^ (m + 1) := by rw [pow_succ]; ring
  apply (le_div_iff₀ (show (0 : ℝ) < Nat.factorial m by positivity)).mpr
  simpa [mul_comm] using hmul m

end ErdosStraus.RoughEstimates

namespace ErdosStraus.BrunHooley

open Classical RoughEstimates
open scoped BigOperators
open scoped Classical

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]

/-! ## The block sieve -/

/-- The subsets of `P` with at most `r` elements. -/
noncomputable def smallSubsets (P : Finset α) (r : ℕ) : Finset (Finset α) :=
  P.powerset.filter (fun s => s.card ≤ r)

/-- The families `f` with `f j ⊆ P j` and `|f j| ≤ r j` for every block `j`. -/
noncomputable def choices (P : ι → Finset α) (r : ι → ℕ) :
    Finset (ι → Finset α) := Fintype.piFinset (fun j => smallSubsets (P j) (r j))

/-- The union `⋃_j f j` of a family of subsets. -/
noncomputable def selected (f : ι → Finset α) : Finset α := Finset.univ.biUnion f

/-- The sign `∏_j (-1)^{|f j|}` of a family of subsets. -/
noncomputable def sign (f : ι → Finset α) : ℝ := ∏ j, (-1 : ℝ) ^ (f j).card

omit [DecidableEq α] in
theorem mem_choices {P : ι → Finset α} {r : ι → ℕ} {f : ι → Finset α} :
    f ∈ choices P r ↔ ∀ j, f j ⊆ P j ∧ (f j).card ≤ r j := by
  simp [choices, smallSubsets]

omit [DecidableEq α] in
theorem truncation_eq_smallSubsets (P : Finset α) (w : α → ℝ) (r : ℕ) :
    truncation P w r = ∑ s ∈ smallSubsets P r,
      (-1 : ℝ) ^ s.card * ∏ p ∈ s, w p := by
  have hm : ∀ s ∈ smallSubsets P r, s.card ∈ Finset.range (r + 1) := by
    intro s hs
    exact Finset.mem_range.mpr (by
      have := (Finset.mem_filter.mp hs).2
      omega)
  have hf := Finset.sum_fiberwise_of_maps_to hm
    (fun s : Finset α => (-1 : ℝ) ^ s.card * ∏ p ∈ s, w p)
  rw [← hf]
  unfold truncation elementary
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  have hset : (smallSubsets P r).filter (fun s => s.card = j) = P.powersetCard j := by
    ext s
    simp only [smallSubsets, Finset.mem_filter, Finset.mem_powerset,
      Finset.mem_powersetCard]
    have hjr : j ≤ r := by have := Finset.mem_range.mp hj; omega
    constructor
    · rintro ⟨⟨hs, _⟩, he⟩
      exact ⟨hs, he⟩
    · rintro ⟨hs, he⟩
      exact ⟨⟨hs, he.le.trans hjr⟩, he⟩
  rw [hset]
  apply Finset.sum_congr rfl
  intro s hs
  rw [(Finset.mem_powersetCard.mp hs).2]

omit [DecidableEq α] in
theorem prod_truncation_eq_sum_choices (P : ι → Finset α) (w : α → ℝ) (r : ι → ℕ) :
    (∏ j, truncation (P j) w (r j)) =
      ∑ f ∈ choices P r, sign f * ∏ j, ∏ p ∈ f j, w p := by
  simp_rw [truncation_eq_smallSubsets]
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro f hf
  exact Finset.prod_mul_distrib

theorem even_truncation_nonneg (P : Finset α) (w : α → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p ∧ w p ≤ 1) (r : ℕ) :
    0 ≤ truncation P w (2 * r) := by
  have hb := (bonferroni P w hw (2 * r)).1
  have hv : 0 ≤ ∏ p ∈ P, (1 - w p) :=
    Finset.prod_nonneg (fun p hp => sub_nonneg.mpr (hw p hp).2)
  simp only [pow_mul, neg_one_sq, one_pow, one_mul] at hb
  linarith

omit [DecidableEq ι] in
theorem product_even_truncations_ge_product (P : ι → Finset α) (w : α → ℝ)
    (hw : ∀ j p, p ∈ P j → 0 ≤ w p ∧ w p ≤ 1) (r : ι → ℕ) :
    (∏ j, ∏ p ∈ P j, (1 - w p)) ≤
      ∏ j, truncation (P j) w (2 * r j) := by
  apply fareyProdLe
  · intro j hj
    exact Finset.prod_nonneg (fun p hp => sub_nonneg.mpr (hw j p hp).2)
  · intro j hj
    have hb := (bonferroni (P j) w (hw j) (2 * r j)).1
    simp only [pow_mul, neg_one_sq, one_pow, one_mul] at hb
    linarith

omit [DecidableEq ι] [DecidableEq α] in
theorem product_indicator (P : ι → Finset α) (hit : α → Prop) :
    (∏ j, ∏ p ∈ P j, (1 - if hit p then (1 : ℝ) else 0)) =
      if ∀ j p, p ∈ P j → ¬ hit p then 1 else 0 := by
  classical
  by_cases h : ∀ j p, p ∈ P j → ¬ hit p
  · have he : (∏ j, ∏ p ∈ P j, (1 - if hit p then (1 : ℝ) else 0)) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      exact Finset.prod_eq_one (fun p hp => by simp [h j p hp])
    exact he.trans (if_pos h).symm
  · have hn := h
    push Not at h
    obtain ⟨j, p, hp, hhit⟩ := h
    have he : (∏ j, ∏ p ∈ P j, (1 - if hit p then (1 : ℝ) else 0)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      exact Finset.prod_eq_zero hp (by simp [hhit])
    exact he.trans (if_neg hn).symm

omit [DecidableEq ι] in
theorem sift_indicator_le_weight (P : ι → Finset α) (hit : α → Prop) (r : ι → ℕ) :
    (if ∀ j p, p ∈ P j → ¬ hit p then (1 : ℝ) else 0) ≤
      ∏ j, truncation (P j) (fun p => if hit p then 1 else 0) (2 * r j) := by
  rw [← product_indicator]
  apply product_even_truncations_ge_product
  intro j p hp
  split_ifs <;> norm_num

omit [DecidableEq ι] [DecidableEq α] in
theorem abs_sign (f : ι → Finset α) : |sign f| = 1 := by
  simp [sign, Finset.abs_prod]

theorem block_truncation_upper (P : Finset α) (w : α → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p ∧ w p ≤ 1) (r : ℕ) :
    truncation P w (2 * r) ≤ (∏ p ∈ P, (1 - w p)) +
      (∑ p ∈ P, w p) ^ (2 * r + 1) / ((2 * r + 1).factorial : ℝ) := by
  have hb := (bonferroni P w hw (2 * r)).2
  simp only [pow_mul, neg_one_sq, one_pow, one_mul] at hb
  have he := elementary_le_sum_pow_div_factorial P w
    (fun p hp => (hw p hp).1) (2 * r + 1)
  linarith

theorem selected_inter_block (P : ι → Finset α)
    (hP : Pairwise (fun j k => Disjoint (P j) (P k))) (r : ι → ℕ)
    {f : ι → Finset α} (hf : f ∈ choices P r) (j : ι) :
    selected f ∩ P j = f j := by
  have hmem := mem_choices.mp hf
  ext p
  simp only [Finset.mem_inter, selected, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨k, hpk⟩, hpj⟩
    by_cases hkj : k = j
    · simpa [hkj] using hpk
    · exact False.elim (Finset.disjoint_left.mp (hP hkj) ((hmem k).1 hpk) hpj)
  · intro hp
    exact ⟨⟨j, hp⟩, (hmem j).1 hp⟩

theorem choices_selected_injOn (P : ι → Finset α)
    (hP : Pairwise (fun j k => Disjoint (P j) (P k))) (r : ι → ℕ) :
    Set.InjOn selected (choices P r : Set (ι → Finset α)) := by
  intro f hf g hg he
  funext j
  rw [← selected_inter_block P hP r hf j, ← selected_inter_block P hP r hg j, he]

/-- The product of the selected primes, the divisor `d = ∏_j d_j` of the expansion. -/
noncomputable def selectedProduct (f : ι → Finset ℕ) : ℕ := ∏ p ∈ selected f, p

theorem selected_primes {P : ι → Finset ℕ} {r : ι → ℕ}
    (hP : ∀ j p, p ∈ P j → Nat.Prime p) {f : ι → Finset ℕ}
    (hf : f ∈ choices P r) : ∀ p ∈ selected f, Nat.Prime p := by
  intro p hp
  obtain ⟨j, _, hp⟩ := Finset.mem_biUnion.mp hp
  exact hP j p ((mem_choices.mp hf j).1 hp)

theorem selectedProduct_pos {P : ι → Finset ℕ} {r : ι → ℕ}
    (hP : ∀ j p, p ∈ P j → Nat.Prime p) {f : ι → Finset ℕ}
    (hf : f ∈ choices P r) : 0 < selectedProduct f :=
  Finset.prod_pos (fun p hp => (selected_primes hP hf p hp).pos)

theorem choices_product_injOn (P : ι → Finset ℕ)
    (hP : ∀ j p, p ∈ P j → Nat.Prime p)
    (hdisj : Pairwise (fun j k => Disjoint (P j) (P k))) (r : ι → ℕ) :
    Set.InjOn selectedProduct (choices P r : Set (ι → Finset ℕ)) := by
  intro f hf g hg he
  apply choices_selected_injOn P hdisj r hf hg
  have hpf := Nat.primeFactors_prod (selected_primes hP hf)
  have hpg := Nat.primeFactors_prod (selected_primes hP hg)
  exact hpf.symm.trans ((congrArg Nat.primeFactors he).trans hpg)

theorem choices_card_le_of_product_le (P : ι → Finset ℕ)
    (hP : ∀ j p, p ∈ P j → Nat.Prime p)
    (hdisj : Pairwise (fun j k => Disjoint (P j) (P k))) (r : ι → ℕ) (W : ℕ)
    (hW : ∀ f ∈ choices P r, selectedProduct f ≤ W) :
    (choices P r).card ≤ W := by
  have hsub : (choices P r).image selectedProduct ⊆ Finset.Icc 1 W := by
    intro d hd
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hd
    exact Finset.mem_Icc.mpr ⟨selectedProduct_pos hP hf, hW f hf⟩
  calc
    _ = ((choices P r).image selectedProduct).card :=
      (Finset.card_image_of_injOn (choices_product_injOn P hP hdisj r)).symm
    _ ≤ (Finset.Icc 1 W).card := Finset.card_le_card hsub
    _ = W := by simp

theorem selectedProduct_eq_block_products (P : ι → Finset ℕ)
    (hdisj : Pairwise (fun j k => Disjoint (P j) (P k))) (r : ι → ℕ)
    {f : ι → Finset ℕ} (hf : f ∈ choices P r) :
    selectedProduct f = ∏ j, ∏ p ∈ f j, p := by
  apply Finset.prod_biUnion
  intro j hj k hk hjk
  exact Finset.disjoint_left.mpr (fun p hpj hpk =>
    Finset.disjoint_left.mp (hdisj hjk) ((mem_choices.mp hf j).1 hpj)
      ((mem_choices.mp hf k).1 hpk))

theorem selectedProduct_le_block_budget (P : ι → Finset ℕ)
    (hdisj : Pairwise (fun j k => Disjoint (P j) (P k))) (r : ι → ℕ)
    (B : ι → ℝ) (hB : ∀ j, 1 ≤ B j)
    (hbound : ∀ j p, p ∈ P j → (p : ℝ) ≤ B j)
    {f : ι → Finset ℕ} (hf : f ∈ choices P r) :
    (selectedProduct f : ℝ) ≤ ∏ j, (B j) ^ (r j) := by
  rw [selectedProduct_eq_block_products P hdisj r hf]
  push_cast
  apply fareyProdLe
  · intro j hj
    exact Finset.prod_nonneg (fun p hp => Nat.cast_nonneg p)
  · intro j hj
    calc
      _ ≤ ∏ _p ∈ f j, B j := fareyProdLe
        (fun p hp => Nat.cast_nonneg p)
        (fun p hp => hbound j p ((mem_choices.mp hf j).1 hp))
      _ = (B j) ^ (f j).card := by simp
      _ ≤ (B j) ^ r j := pow_le_pow_right₀ (hB j) (mem_choices.mp hf j).2

omit [DecidableEq ι] [DecidableEq α] in
theorem product_hit_indicator (P : ι → Finset α) (hit : α → Prop) :
    (∏ j, ∏ p ∈ P j, if hit p then (1 : ℝ) else 0) =
      if ∀ j p, p ∈ P j → hit p then 1 else 0 := by
  by_cases h : ∀ j p, p ∈ P j → hit p
  · have he : (∏ j, ∏ p ∈ P j, if hit p then (1 : ℝ) else 0) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      exact Finset.prod_eq_one (fun p hp => by simp [h j p hp])
    exact he.trans (if_pos h).symm
  · have hn := h
    push Not at h
    obtain ⟨j, p, hp, hhit⟩ := h
    have he : (∏ j, ∏ p ∈ P j, if hit p then (1 : ℝ) else 0) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      exact Finset.prod_eq_zero hp (by simp [hhit])
    exact he.trans (if_neg hn).symm

theorem sum_block_weights {β : Type*} [DecidableEq β] (A : Finset β)
    (P : ι → Finset α) (hit : α → β → Prop) (r : ι → ℕ) :
    (∑ n ∈ A, ∏ j, truncation (P j) (fun p => if hit p n then 1 else 0) (r j)) =
      ∑ f ∈ choices P r, sign f * intersectionCount A hit (selected f) := by
  simp_rw [prod_truncation_eq_sum_choices]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f hf
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [product_hit_indicator]
  have he (n : β) : (∀ j p, p ∈ f j → hit p n) ↔
      (∀ p ∈ selected f, hit p n) := by
    simp only [selected, Finset.mem_biUnion, Finset.mem_univ, true_and]
    aesop
  simp_rw [he]
  simp [intersectionCount]

theorem weighted_geometric_budget (n : ℕ) :
    ∑ j ∈ Finset.range n, (2 * (j + 1 : ℝ)) / 2 ^ j ≤ 8 := by
  have he : (∑ j ∈ Finset.range n, (2 * (j + 1 : ℝ)) / 2 ^ j) =
      8 - (4 * (n : ℝ) + 8) / 2 ^ n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      push_cast
      field_simp
      ring
  rw [he]
  exact sub_le_self 8 (by positivity)

/-- For blocks with `p ≤ w^{2^{-j}}` and ranks `2(j+1)`, every expanded divisor is at most
`∏_j w^{2(j+1)/2^j} ≤ w^8`. -/
theorem geometric_block_support (n : ℕ) (P : Fin n → Finset ℕ)
    (hdisj : Pairwise (fun j k => Disjoint (P j) (P k))) (w : ℝ) (hw : 1 ≤ w)
    (hbound : ∀ j p, p ∈ P j → (p : ℝ) ≤ w ^ ((2 : ℝ) ^ (j : ℕ))⁻¹)
    {f : Fin n → Finset ℕ}
    (hf : f ∈ choices P (fun j => 2 * ((j : ℕ) + 1))) :
    (selectedProduct f : ℝ) ≤ w ^ 8 := by
  have hwpos : 0 < w := zero_lt_one.trans_le hw
  have hb (j : Fin n) : 1 ≤ w ^ ((2 : ℝ) ^ (j : ℕ))⁻¹ :=
    Real.one_le_rpow hw (by positivity)
  have hh := selectedProduct_le_block_budget P hdisj (fun j => 2 * ((j : ℕ) + 1))
    (fun j => w ^ ((2 : ℝ) ^ (j : ℕ))⁻¹) hb hbound hf
  have he : (∏ j : Fin n, (w ^ ((2 : ℝ) ^ (j : ℕ))⁻¹) ^ (2 * ((j : ℕ) + 1))) =
      w ^ (∑ j ∈ Finset.range n, (2 * (j + 1 : ℝ)) / 2 ^ j) := by
    have hexp (j : Fin n) : (w ^ ((2 : ℝ) ^ (j : ℕ))⁻¹) ^ (2 * ((j : ℕ) + 1)) =
        w ^ (((2 : ℝ) ^ (j : ℕ))⁻¹ * (2 * ((j : ℕ) + 1) : ℕ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hwpos.le]
    simp_rw [hexp]
    rw [← Real.rpow_sum_of_pos hwpos]
    congr 1
    calc
      _ = ∑ j : Fin n, (2 * ((j : ℕ) + 1 : ℝ)) / 2 ^ (j : ℕ) := by
        apply Finset.sum_congr rfl
        intro j hj
        push_cast
        ring
      _ = _ := Fin.sum_univ_eq_sum_range
        (fun j : ℕ => 2 * ((j : ℝ) + 1) / (2 : ℝ) ^ j) n
  rw [he] at hh
  apply hh.trans
  rw [← Real.rpow_natCast w 8]
  exact Real.rpow_le_rpow_of_exponent_le hw (weighted_geometric_budget n)

/-! ## Comparison with the Euler product -/

omit [DecidableEq ι] in
theorem product_truncation_upper (P : ι → Finset α) (w : α → ℝ)
    (hw : ∀ j p, p ∈ P j → 0 ≤ w p ∧ w p < 1) (r : ι → ℕ) :
    (∏ j, truncation (P j) w (2 * r j)) ≤
      (∏ j, ∏ p ∈ P j, (1 - w p)) * Real.exp
        (∑ j, ((∑ p ∈ P j, w p) ^ (2 * r j + 1) /
          ((2 * r j + 1).factorial : ℝ)) / (∏ p ∈ P j, (1 - w p))) := by
  let V : ι → ℝ := fun j => ∏ p ∈ P j, (1 - w p)
  let F : ι → ℝ := fun j => (∑ p ∈ P j, w p) ^ (2 * r j + 1) /
    ((2 * r j + 1).factorial : ℝ)
  have hV (j : ι) : 0 < V j :=
    Finset.prod_pos (fun p hp => sub_pos.mpr (hw j p hp).2)
  have hprod : (∏ j, truncation (P j) w (2 * r j)) ≤
      ∏ j, V j * Real.exp (F j / V j) := by
    apply fareyProdLe
    · intro j hj
      exact even_truncation_nonneg _ _ (fun p hp => ⟨(hw j p hp).1,
        (hw j p hp).2.le⟩) _
    · intro j hj
      have hb := block_truncation_upper (P j) w
        (fun p hp => ⟨(hw j p hp).1, (hw j p hp).2.le⟩) (r j)
      apply hb.trans
      have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (F j / V j)) (hV j).le
      have hcancel : V j * (F j / V j + 1) = V j + F j := by
        field_simp [(hV j).ne']
        ring
      rwa [hcancel] at he
  rw [Finset.prod_mul_distrib, ← Real.exp_sum] at hprod
  exact hprod

theorem factorial_odd_tail_sum_le_exp (n : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    (∑ j : Fin n, H ^ (2 * (j : ℕ) + 3) /
      ((2 * (j : ℕ) + 3).factorial : ℝ)) ≤ Real.exp H := by
  let S := (Finset.range n).image (fun j => 2 * j + 3)
  have hinj : Function.Injective (fun j : ℕ => 2 * j + 3) := by
    intro j k h
    change 2 * j + 3 = 2 * k + 3 at h
    omega
  have hsub : S ⊆ Finset.range (2 * n + 3) := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega)
  calc
    _ = ∑ j ∈ Finset.range n, H ^ (2 * j + 3) / ((2 * j + 3).factorial : ℝ) :=
      Fin.sum_univ_eq_sum_range _ _
    _ = ∑ k ∈ S, H ^ k / (k.factorial : ℝ) := by
      rw [Finset.sum_image (fun a _ b _ hab => hinj hab)]
    _ ≤ ∑ k ∈ Finset.range (2 * n + 3), H ^ k / (k.factorial : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
    _ ≤ Real.exp H := Real.sum_le_exp_of_nonneg hH _

/-- With truncation ranks `t_j = 2(j+1)`, `∏_j T_j ≤ ∏_j W_j · exp(e^H/v)` when every
block has `∑ w(p) ≤ H` and Euler factor `W_j = ∏ (1 - w(p)) ≥ v`. -/
theorem product_truncation_le_uniform_factor (n : ℕ) (P : Fin n → Finset α)
    (w : α → ℝ) (hw : ∀ j p, p ∈ P j → 0 ≤ w p ∧ w p < 1)
    (H v : ℝ) (hH : 0 ≤ H) (hv : 0 < v)
    (hSum : ∀ j, (∑ p ∈ P j, w p) ≤ H)
    (hEuler : ∀ j, v ≤ ∏ p ∈ P j, (1 - w p)) :
    (∏ j, truncation (P j) w (2 * ((j : ℕ) + 1))) ≤
      (∏ j, ∏ p ∈ P j, (1 - w p)) * Real.exp (Real.exp H / v) := by
  apply (product_truncation_upper P w hw (fun j => (j : ℕ) + 1)).trans
  apply mul_le_mul_of_nonneg_left _
    (Finset.prod_nonneg (fun j hj => Finset.prod_nonneg
      (fun p hp => (sub_pos.mpr (hw j p hp).2).le)))
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ∑ j : Fin n, (H ^ (2 * (j : ℕ) + 3) /
        ((2 * (j : ℕ) + 3).factorial : ℝ)) / v := by
      apply Finset.sum_le_sum
      intro j hj
      have hdeg : 2 * ((j : ℕ) + 1) + 1 = 2 * (j : ℕ) + 3 := by omega
      rw [hdeg]
      apply div_le_div₀
      · positivity
      · exact div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (Finset.sum_nonneg (fun p hp => (hw j p hp).1)) (hSum j) _)
          (by positivity)
      · exact hv
      · exact hEuler j
    _ = (∑ j : Fin n, H ^ (2 * (j : ℕ) + 3) /
        ((2 * (j : ℕ) + 3).factorial : ℝ)) / v := (Finset.sum_div _ _ _).symm
    _ ≤ Real.exp H / v := div_le_div_of_nonneg_right
      (factorial_odd_tail_sum_le_exp n H hH) hv.le

omit [DecidableEq α] in
theorem euler_product_lower_of_sum_bound (P : Finset α) (w : α → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p ∧ w p ≤ 1 / 2) (H : ℝ)
    (hSum : (∑ p ∈ P, w p) ≤ H) :
    Real.exp (-2 * H) ≤ ∏ p ∈ P, (1 - w p) := by
  have hpoint (p : α) (hp : p ∈ P) : Real.exp (-2 * w p) ≤ 1 - w p := by
    have hpos : 0 < 1 - w p := by linarith [(hw p hp).2]
    have hinv : (1 - w p)⁻¹ ≤ 2 := by
      have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2)
        (by linarith [(hw p hp).2] : (1 / 2 : ℝ) ≤ 1 - w p)
      norm_num only [one_div, inv_div, inv_one, mul_one] at hh
      exact hh
    have hmul := inv_mul_cancel₀ hpos.ne'
    have hh := mul_le_mul_of_nonneg_left hinv (hw p hp).1
    have hlog := Real.one_sub_inv_le_log_of_pos hpos
    apply (Real.le_log_iff_exp_le hpos).mp
    nlinarith
  calc
    _ ≤ Real.exp (∑ p ∈ P, -2 * w p) := by
      apply Real.exp_le_exp.mpr
      rw [← Finset.mul_sum]
      linarith
    _ = ∏ p ∈ P, Real.exp (-2 * w p) := Real.exp_sum _ _
    _ ≤ _ := fareyProdLe (fun p hp => (Real.exp_pos _).le) hpoint

end ErdosStraus.BrunHooley

namespace FareyBrun
open Finset ErdosStraus.RoughEstimates ErdosStraus.BrunHooley
open scoped BigOperators
noncomputable section
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]

def box (P : ι → Finset α) (w : α → ℝ) (r : ι → ℕ) : ℝ :=
  ∏ j, truncation (P j) w (r j)

def lower (P : ι → Finset α) (w : α → ℝ) (r : ι → ℕ) : ℝ :=
  let k := fun j => 2 * r j
  box P w k - ∑ j, (box P w k - box P w (Function.update k j (k j + 1)))

theorem box_difference (P : ι → Finset α) (w : α → ℝ) (r : ι → ℕ) (j : ι) :
    let k := fun j => 2 * r j
    box P w k - box P w (Function.update k j (k j + 1)) =
      elementary (P j) w (k j + 1) *
      ∏ i ∈ univ.erase j, truncation (P i) w (k i) := by
  dsimp only
  let k := fun j => 2 * r j
  change box P w k - box P w (Function.update k j (k j + 1)) = _
  unfold box
  rw [← mul_prod_erase univ _ (mem_univ j), ← mul_prod_erase univ
    (fun i => truncation (P i) w (Function.update k j (k j + 1) i)) (mem_univ j)]
  simp only [Function.update_self]
  have he : (∏ i ∈ univ.erase j, truncation (P i) w (Function.update k j (k j + 1) i)) =
      ∏ i ∈ univ.erase j, truncation (P i) w (k i) := by
    apply prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (ne_of_mem_erase hi)]
  rw [he]
  have ht : truncation (P j) w (k j + 1) =
      truncation (P j) w (k j) - elementary (P j) w (k j + 1) := by
    unfold truncation
    rw [sum_range_succ]
    simp [k, pow_succ, pow_mul, sub_eq_add_neg]
  rw [ht]
  ring

theorem lower_as_error (P : ι → Finset α) (w : α → ℝ) (r : ι → ℕ) :
    lower P w r = box P w (fun j => 2*r j) -
      ∑ j, elementary (P j) w (2*r j+1) *
        ∏ i ∈ univ.erase j, truncation (P i) w (2*r i) := by
  unfold lower
  dsimp only
  congr 1
  exact sum_congr rfl (fun j _ => box_difference P w r j)

theorem lower_indicator (P : ι → Finset α) (hit : α → Prop) [DecidablePred hit]
    (r : ι → ℕ) :
    lower P (fun p => if hit p then 1 else 0) r ≤
      if ∀ j p, p ∈ P j → ¬ hit p then (1:ℝ) else 0 := by
  classical
  let w := fun p => if hit p then (1:ℝ) else 0
  have hw (p : α) : 0 ≤ w p ∧ w p ≤ 1 := by simp only [w]; split <;> norm_num
  let T := fun j => truncation (P j) w (2*r j)
  let E := fun j => elementary (P j) w (2*r j+1)
  have ht (j : ι) : 0 ≤ T j := even_truncation_nonneg _ _ (fun p _ => hw p) _
  have he (j : ι) : 0 ≤ E j := elementary_nonneg _ _ (fun p _ => (hw p).1) _
  rw [lower_as_error]
  change (∏ j, T j) - ∑ j, E j * (∏ i ∈ univ.erase j, T i) ≤ _
  split_ifs with hall
  · have htone (j : ι) : T j ≤ 1 := by
      have hzero : E j = 0 := by
        apply le_antisymm _ (he j)
        apply (elementary_le_sum_pow_div_factorial _ _ (fun p _ => (hw p).1) _).trans
        have hz : ∑ p ∈ P j, w p = 0 := sum_eq_zero (fun p hp => if_neg (hall j p hp))
        rw [hz, zero_pow (by omega : 2*r j+1 ≠ 0), zero_div]
      have hb := (bonferroni (P j) w (fun p _ => hw p) (2*r j)).2
      change _ ≤ E j at hb
      rw [hzero] at hb
      simp only [pow_mul, neg_one_sq, one_pow, one_mul] at hb
      exact (sub_nonpos.mp hb).trans (prod_one_sub_mem_unit _ _ (fun p _ => hw p)).2
    exact (sub_le_self _ (sum_nonneg (fun j _ => mul_nonneg (he j) (prod_nonneg (fun i _ => ht i))))).trans
      (fareyProdOne (fun j _ => ht j) (fun j _ => htone j))
  · push Not at hall
    obtain ⟨j,p,hp,hh⟩ := hall
    have hz : ∏ i ∈ P j, (1-w i) = 0 := prod_eq_zero hp (by simp [w,hh])
    have hb := (bonferroni (P j) w (fun p _ => hw p) (2*r j)).2
    simp only [pow_mul, neg_one_sq, one_pow, one_mul, hz, sub_zero] at hb
    have hsingle := single_le_sum (f := fun j => E j * ∏ i ∈ univ.erase j, T i)
      (fun j _ => mul_nonneg (he j) (prod_nonneg (fun i _ => ht i))) (mem_univ j)
    have hcross := mul_le_mul_of_nonneg_right hb (prod_nonneg (fun i (_ : i ∈ univ.erase j) => ht i))
    apply sub_nonpos.mpr
    rw [← mul_prod_erase univ T (mem_univ j)]
    exact hcross.trans hsingle
end
end FareyBrun

namespace FareyBrun
open Finset ErdosStraus.RoughEstimates ErdosStraus.BrunHooley
open scoped BigOperators
noncomputable section
variable {ι α β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α] [DecidableEq β]
open scoped Classical

theorem box_mean (A : Finset β) (P : ι → Finset α) (hit : α → β → Prop)
    (r : ι → ℕ) (w : α → ℝ) (X E : ℝ)
    (hround : ∀ f ∈ choices P r, |intersectionCount A hit (selected f) -
      X * ∏ j, ∏ p ∈ f j, w p| ≤ E) :
    |(∑ u ∈ A, box P (fun p => if hit p u then 1 else 0) r) - X * box P w r| ≤
      (choices P r).card * E := by
  unfold box
  rw [sum_block_weights, prod_truncation_eq_sum_choices, Finset.mul_sum, ← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _f ∈ choices P r, E := by
      apply sum_le_sum
      intro f hf
      rw [show sign f * intersectionCount A hit (selected f) -
        X * (sign f * ∏ j, ∏ p ∈ f j, w p) =
        sign f * (intersectionCount A hit (selected f) - X * ∏ j, ∏ p ∈ f j, w p) by ring,
        abs_mul, abs_sign, one_mul]
      exact hround f hf
    _ = _ := by simp

theorem lower_count (A : Finset β) (P : ι → Finset α) (hit : α → β → Prop)
    (r : ι → ℕ) (w : α → ℝ) (X D : ℝ)
    (hbox : ∀ k : ι → ℕ, (∀ j, k j ≤ 2*r j+1) →
      |(∑ u ∈ A, box P (fun p => if hit p u then 1 else 0) k) - X * box P w k| ≤ D) :
    X * lower P w r - (1+2*(Fintype.card ι:ℝ))*D ≤
      ((A.filter (fun u => ∀ j p, p ∈ P j → ¬ hit p u)).card:ℝ) := by
  let k := fun j => 2*r j
  let v := fun j => Function.update k j (k j+1)
  let emp := fun l : ι → ℕ => ∑ u ∈ A, box P (fun p => if hit p u then 1 else 0) l
  let modl := fun l => X * box P w l
  have he0 := abs_le.mp (hbox k (fun j => Nat.le_succ _))
  have he1 (j : ι) : -(D:ℝ) ≤ emp (v j) - modl (v j) := by
    apply (abs_le.mp (hbox _ ?_)).1
    intro i
    by_cases hi : i = j
    · subst i; simp [v,k]
    · simp [v,k,Function.update_of_ne hi]
  have hh (j : ι) : emp k - emp (v j) ≤ (modl k - modl (v j)) + 2*D := by
    change -D ≤ emp k - modl k ∧ emp k - modl k ≤ D at he0
    linarith [he1 j]
  have hs := sum_le_sum (s := univ) (fun j _ => hh j)
  rw [sum_add_distrib] at hs
  simp only [sum_const,card_univ,nsmul_eq_mul] at hs
  have hpoint : ∑ u ∈ A, lower P (fun p => if hit p u then 1 else 0) r ≤
      ((A.filter (fun u => ∀ j p, p ∈ P j → ¬ hit p u)).card:ℝ) := by
    simpa using (sum_le_sum (s:=A) (fun u _ => lower_indicator P (fun p => hit p u) r))
  apply le_trans _ hpoint
  unfold lower
  dsimp only
  conv_rhs =>
    rw [sum_sub_distrib, sum_comm]
  simp_rw [Finset.sum_sub_distrib (s := A)]
  rw [mul_sub,Finset.mul_sum]
  simp_rw [mul_sub]
  change modl k - (∑ j, (modl k - modl (v j))) - _ ≤
    emp k - (∑ j, (emp k - emp (v j)))
  change -D ≤ emp k - modl k ∧ emp k - modl k ≤ D at he0
  linarith

theorem lower_model (P : ι → Finset α) (r : ι → ℕ) (w : α → ℝ)
    (hw : ∀ j p, p ∈ P j → 0 ≤ w p ∧ w p < 1) (e : ℝ)
    (he : (∑ j, ((∑ p ∈ P j, w p) ^ (2*r j+1) / ((2*r j+1).factorial : ℝ)) /
       (∏ p ∈ P j, (1-w p))) ≤ e) :
    (∏ j, ∏ p ∈ P j, (1-w p)) * (1-e*Real.exp e) ≤ lower P w r := by
  let T := fun j => truncation (P j) w (2*r j)
  let V := fun j => ∏ p ∈ P j, (1-w p)
  let F := fun j => (∑ p ∈ P j, w p) ^ (2*r j+1) / ((2*r j+1).factorial : ℝ)
  have hV (j : ι) : 0 < V j := prod_pos (fun p hp => sub_pos.mpr (hw j p hp).2)
  have hF (j : ι) : 0 ≤ F j := div_nonneg (pow_nonneg (sum_nonneg (fun p hp => (hw j p hp).1)) _) (by positivity)
  have hVT (j : ι) : V j ≤ T j := by
    have hb := (bonferroni (P j) w (fun p hp => ⟨(hw j p hp).1,(hw j p hp).2.le⟩) (2*r j)).1
    simpa [pow_mul,sub_nonneg] using hb
  have hT (j : ι) := (hV j).le.trans (hVT j)
  have hErr (j : ι) : elementary (P j) w (2*r j+1) * (∏ i ∈ univ.erase j, T i) ≤
      (F j / V j) * ∏ i, T i := by
    have hE := elementary_le_sum_pow_div_factorial (P j) w (fun p hp => (hw j p hp).1) (2*r j+1)
    rw [← mul_prod_erase univ T (mem_univ j), ← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (prod_nonneg (fun i _ => hT i))
    apply hE.trans
    calc F j = F j / V j * V j := (div_mul_cancel₀ _ (hV j).ne').symm
         _ ≤ _ := mul_le_mul_of_nonneg_left (hVT j) (div_nonneg (hF j) (hV j).le)
  have hs := sum_le_sum (s:=univ) (fun j _ => hErr j)
  rw [←sum_mul] at hs
  have hprod := product_truncation_upper P w hw r
  have hp0 : 0 ≤ ∏ j, V j := prod_nonneg (fun j _ => (hV j).le)
  have htotal : ∏ j, T j ≤ (∏ j, V j) * Real.exp e := hprod.trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hp0)
  have he0 : 0 ≤ e := (sum_nonneg (fun j _ => div_nonneg (hF j) (hV j).le)).trans he
  have htot := mul_le_mul he htotal (prod_nonneg (fun j _ => hT j)) he0
  have hgood := fareyProdLe (s:=univ) (fun j _ => (hV j).le) (fun j _ => hVT j)
  rw [lower_as_error]
  change (∏ j, V j) * _ ≤ (∏ j, T j) - _
  linarith only [hs,htot,hgood]
end
end FareyBrun

namespace FareyBrun
open Finset ErdosStraus.RoughEstimates ErdosStraus.BrunHooley
open scoped BigOperators
noncomputable section
open scoped Classical

/-- Finite lower sieve for blocks. The remainder is paid on squarefree selections;
the deterministic loss is controlled by the first omitted symmetric sum in each block. -/
theorem finite_block_lower {ι α β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    [DecidableEq β] (A : Finset β) (P : ι → Finset α) (hit : α → β → Prop)
    (r : ι → ℕ) (w : α → ℝ) (X D e : ℝ) (hX : 0 ≤ X)
    (hw : ∀ j p, p ∈ P j → 0 ≤ w p ∧ w p < 1)
    (htail : (∑ j, ((∑ p ∈ P j, w p) ^ (2*r j+1) / ((2*r j+1).factorial : ℝ)) /
       (∏ p ∈ P j, (1-w p))) ≤ e)
    (hround : ∀ k : ι → ℕ, (∀ j, k j ≤ 2*r j+1) →
      ∃ E : ℝ, (choices P k).card * E ≤ D ∧ ∀ f ∈ choices P k,
        |intersectionCount A hit (selected f) - X * ∏ j, ∏ p ∈ f j, w p| ≤ E) :
    X * ((∏ j, ∏ p ∈ P j, (1-w p)) * (1-e*Real.exp e)) -
      (1+2*(Fintype.card ι:ℝ))*D ≤
      ((A.filter (fun u => ∀ j p, p ∈ P j → ¬ hit p u)).card:ℝ) := by
  apply le_trans (sub_le_sub_right
    (mul_le_mul_of_nonneg_left (lower_model P r w hw e htail) hX) _)
  apply lower_count
  intro k hk
  obtain ⟨E,hE,hf⟩ := hround k hk
  exact (box_mean A P hit k w X E hf).trans hE

end
end FareyBrun

/- Legendre identities adapted from ErdosStraus/Estimates/Mertens.lean, Apache-2.0,
   revision f6c99eaaca6ec7a7226a7a16bef1cd2b09e36660. -/
namespace FareyBrun
open Finset Real
open scoped BigOperators ArithmeticFunction Nat
/-- `log n! = ∑_{m ≤ n} log m`. -/
theorem log_factorial_eq_sum_log (n : ℕ) :
    log (n ! : ℝ) = ∑ m ∈ Icc 1 n, log (m : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity), ih,
      Finset.sum_Icc_succ_top (by omega)]
    ring

/-- Legendre's identity `log n! = ∑_{d ≤ n} Λ(d) ⌊n/d⌋`. -/
theorem log_factorial_eq (n : ℕ) :
    log (n ! : ℝ) = ∑ d ∈ Icc 1 n, Λ d * ((n / d : ℕ) : ℝ) := by
  rw [log_factorial_eq_sum_log]
  have hdiv : ∀ m ∈ Icc 1 n, log (m : ℝ) = ∑ d ∈ m.divisors, Λ d := fun m _ =>
    ArithmeticFunction.vonMangoldt_sum.symm
  rw [Finset.sum_congr rfl hdiv,
    Finset.sum_comm' (t' := Icc 1 n) (s' := fun d => (Icc 1 n).filter (fun m => d ∣ m))]
  · apply Finset.sum_congr rfl
    intro d _
    have hIcc : Icc 1 n = Ioc 0 n := Finset.Icc_add_one_left_eq_Ioc 0 n
    rw [sum_const, nsmul_eq_mul, hIcc, Nat.Ioc_filter_dvd_card_eq_div, mul_comm]
  · intro m d
    simp only [mem_Icc, Nat.mem_divisors, mem_filter]
    constructor
    · rintro ⟨⟨h1, hm⟩, hdm, -⟩
      exact ⟨⟨⟨h1, hm⟩, hdm⟩, Nat.pos_of_dvd_of_pos hdm h1, (Nat.le_of_dvd h1 hdm).trans hm⟩
    · rintro ⟨⟨⟨h1, hm⟩, hdm⟩, -, -⟩
      exact ⟨⟨h1, hm⟩, hdm, by omega⟩

/-- `⌊n/d⌋ ≤ n/d ≤ ⌊n/d⌋ + 1`. -/
theorem natDiv_le_div_le (n d : ℕ) (hd : 0 < d) :
    ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d ∧ (n : ℝ) / d ≤ ((n / d : ℕ) : ℝ) + 1 := by
  refine ⟨Nat.cast_div_le, ?_⟩
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_le_iff₀ hdr]
  have h3 : (n : ℝ) = d * (n / d : ℕ) + (n % d : ℕ) := by exact_mod_cast (Nat.div_add_mod n d).symm
  have h4 : ((n % d : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt n hd).le
  nlinarith

end FareyBrun

namespace FareyBrun
open Finset Real
open scoped BigOperators ArithmeticFunction Nat
noncomputable section

/-- A uniform logarithmic budget, without any prime-number asymptotic. -/
theorem log_prime_budget (n : ℕ) (hn : 0 < n) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ p ≤ n) :
    (∑ p ∈ s, Real.log p / p) ≤ 2 * Real.log n := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hterm (p : ℕ) (hp : p ∈ s) :
      (n:ℝ) * (Real.log p / p) ≤ 2 * (Λ p * (n / p : ℕ)) := by
    obtain ⟨hprime,hpn⟩ := hs p hp
    rw [ArithmeticFunction.vonMangoldt_apply_prime hprime]
    have hdiv : 1 ≤ n / p := (Nat.one_le_div_iff hprime.pos).mpr hpn
    have hx := (natDiv_le_div_le n p hprime.pos).2
    have hcast : (1:ℝ) ≤ (n / p : ℕ) := by exact_mod_cast hdiv
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hprime.one_le)
    calc _ = Real.log p * ((n:ℝ)/p) := by ring
         _ ≤ Real.log p * (2*(n/p:ℕ)) :=
           mul_le_mul_of_nonneg_left (by linarith) hlog
         _ = _ := by ring
  have hsub : s ⊆ Icc 1 n := fun p hp => mem_Icc.mpr ⟨(hs p hp).1.one_le,(hs p hp).2⟩
  have hfac : Real.log (n ! : ℝ) ≤ (n:ℝ) * Real.log n := by
    rw [←Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.factorial_le_pow n)
  apply le_of_mul_le_mul_left ?_ hn'
  calc
    (n:ℝ) * (∑ p ∈ s, Real.log p / p) ≤ 2 * ∑ p ∈ s, Λ p * (n / p : ℕ) := by
      rw [mul_sum,mul_sum]
      exact sum_le_sum hterm
    _ ≤ 2 * ∑ p ∈ Icc 1 n, Λ p * (n / p : ℕ) := by
      exact mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ =>
          mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))) (by norm_num)
    _ = 2 * Real.log (n ! : ℝ) := by rw [log_factorial_eq]
    _ ≤ (n:ℝ) * (2*Real.log n) := by linarith

theorem log_prime_budget_real (x : ℝ) (hx : 1 ≤ x) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ (p:ℝ) ≤ x) :
    (∑ p ∈ s, Real.log p / p) ≤ 2 * Real.log x := by
  have hn : 1 ≤ ⌊x⌋₊ := (Nat.le_floor (by simpa using hx))
  apply (log_prime_budget ⌊x⌋₊ hn s (fun p hp => ⟨(hs p hp).1,Nat.le_floor (hs p hp).2⟩)).trans
  exact mul_le_mul_of_nonneg_left (Real.log_le_log (by exact_mod_cast hn : (0:ℝ) < ⌊x⌋₊)
    (Nat.floor_le (zero_le_one.trans hx))) (by norm_num)

/-- Reciprocal mass of any prime block between sqrt(x) and x. -/
theorem half_log_block (x : ℝ) (hx : 1 < x) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ (p:ℝ) ≤ x ∧ Real.log x ≤ 2 * Real.log p) :
    (∑ p ∈ s, 2/(p:ℝ)) ≤ 8 := by
  apply le_of_mul_le_mul_left _ (Real.log_pos hx)
  calc
    Real.log x * (∑ p ∈ s, 2/(p:ℝ)) ≤ 4 * ∑ p ∈ s, Real.log p / p := by
      rw [mul_sum,mul_sum]
      apply sum_le_sum
      intro p hp
      have hh := (hs p hp).2.2
      have hz : (0:ℝ) < p := by exact_mod_cast (hs p hp).1.pos
      rw [show Real.log x*(2/(p:ℝ)) = (2*Real.log x)/p by ring,
          show 4*(Real.log p/p) = (4*Real.log p)/p by ring]
      exact div_le_div_of_nonneg_right (by linarith) hz.le
    _ ≤ Real.log x * 8 := by
      have h := log_prime_budget_real x hx.le s (fun p hp => ⟨(hs p hp).1,(hs p hp).2.1⟩)
      linarith

/-- Local density for the two forbidden residues of an odd prime. -/
theorem euler_density_lower (s : Finset ℕ) (hs : ∀ p ∈ s, 3 ≤ p) :
    Real.exp (-3 * ∑ p ∈ s, 2/(p:ℝ)) ≤ ∏ p ∈ s, (1-2/(p:ℝ)) := by
  rw [mul_sum, Real.exp_sum]
  apply fareyProdLe (fun p _ => (Real.exp_pos _).le)
  intro p hp
  have h3 : (3:ℝ) ≤ p := by exact_mod_cast hs p hp
  have hpos : (0:ℝ) < p := by linarith
  let w := 2/(p:ℝ)
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hu : w ≤ 2/3 := by dsimp [w]; rw [div_le_div_iff₀ hpos (by norm_num : (0:ℝ)<3)]; linarith
  have hv : 0 < 1-w := by linarith
  have hi : (1-w)⁻¹ ≤ 3 := by rw [inv_eq_one_div,div_le_iff₀ hv]; linarith
  have hh := Real.one_sub_inv_le_log_of_pos hv
  have hcan := inv_mul_cancel₀ hv.ne'
  have hm := mul_le_mul_of_nonneg_right hi hw
  apply (Real.le_log_iff_exp_le hv).mp
  change -3*w ≤ _
  nlinarith
end
end FareyBrun

namespace FareyBrun
open Finset Real ErdosStraus.BrunHooley
open scoped BigOperators
noncomputable section

def rank (K j : ℕ) := K+j+1
def edge (z : ℝ) (j : ℕ) := Real.exp (Real.log z / 2^j)

/-- Every selected squarefree divisor is bounded by z^(8(K+2)), even when
one of the even ranks is increased by one for the lower correction. -/
theorem rank_support {m : ℕ} (K : ℕ) (P : Fin m → Finset ℕ)
    (hdisj : Pairwise (fun j k => Disjoint (P j) (P k))) {z : ℝ} (hz : 1 ≤ z)
    (hbound : ∀ j p, p ∈ P j → (p:ℝ) ≤ edge z j.val)
    (k : Fin m → ℕ) (hk : ∀ j, k j ≤ 2*rank K j.val+1)
    {f : Fin m → Finset ℕ} (hf : f ∈ choices P k) :
    (selectedProduct f:ℝ) ≤ z ^ (8*(K+2)) := by
  have hlog := Real.log_nonneg hz
  have hone (j : Fin m) : 1 ≤ edge z j.val := Real.one_le_exp (by positivity)
  apply (selectedProduct_le_block_budget P hdisj k (fun j => edge z j.val) hone hbound hf).trans
  have hdegree (j : Fin m) : (k j:ℝ) ≤ (K+2:ℝ)*(2*(j.val+1:ℝ)) := by
    have hh := hk j
    unfold rank at hh
    have hnat : k j ≤ (K+2)*(2*(j.val+1)) := by nlinarith [Nat.zero_le (K*j.val)]
    exact_mod_cast hnat
  have hsum : ∑ j : Fin m, (k j:ℝ) / 2^j.val ≤ (K+2:ℝ)*8 := by
    calc _ ≤ ∑ j : Fin m, (K+2:ℝ)*(2*(j.val+1:ℝ)/2^j.val) := by
              apply sum_le_sum
              intro j _
              rw [mul_div_assoc']
              exact div_le_div_of_nonneg_right (hdegree j) (by positivity)
         _ = (K+2:ℝ) * ∑ j ∈ range m, 2*(j+1:ℝ)/2^j := by
              rw [←mul_sum,Fin.sum_univ_eq_sum_range (fun j : ℕ => 2*(j+1:ℝ)/2^j) m]
         _ ≤ _ := mul_le_mul_of_nonneg_left (weighted_geometric_budget m) (by positivity)
  have hp (j : Fin m) : edge z j.val ^ k j =
      Real.exp (Real.log z * ((k j:ℝ)/2^j.val)) := by
    rw [edge,← Real.exp_nat_mul]
    congr 1
    ring
  simp_rw [hp]
  rw [← Real.exp_sum, ← mul_sum]
  have hz' : 0 < z := zero_lt_one.trans_le hz
  rw [← Real.exp_log hz', ← Real.exp_nat_mul]
  rw [Real.log_exp]
  apply Real.exp_le_exp.mpr
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hsum hlog]

def tiltError (K : ℕ) : ℝ :=
  Real.exp (24 + 8 * Real.exp 65536 - 65536 * (2*K:ℕ))

/-- Exponential tilting bounds all the omitted ranks at once, uniformly in
the number of blocks. The large fixed tilt will absorb the terminal sieve loss. -/
theorem rank_tail {m : ℕ} (K : ℕ) (P : Fin m → Finset ℕ) (w : ℕ → ℝ)
    (hS : ∀ j, (∑ p ∈ P j, w p) ≤ 8) (hw : ∀ j p, p ∈ P j → 0 ≤ w p)
    (hV : ∀ j, Real.exp (-24) ≤ ∏ p ∈ P j, (1-w p)) :
    (∑ j : Fin m, ((∑ p ∈ P j, w p) ^ (2*rank K j.val+1) /
      ((2*rank K j.val+1).factorial:ℝ)) / (∏ p ∈ P j, (1-w p))) ≤ tiltError K := by
  let a : ℝ := Real.exp 65536
  let d := fun j : ℕ => 2*rank K j+1
  let t := fun j : ℕ => (8*a)^j/(j.factorial:ℝ)
  have ha : 1 ≤ a := Real.one_le_exp (by norm_num)
  have ha' : 0 < a := zero_lt_one.trans_le ha
  have htilt (j : Fin m) : ((∑ p ∈ P j, w p) ^ (d j.val) /
      ((d j.val).factorial:ℝ)) / (∏ p ∈ P j, (1-w p)) ≤
        (Real.exp 24 / a^(2*K)) * t (d j.val) := by
    have hu := div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (sum_nonneg (fun p hp => hw j p hp)) (hS j) (d j.val))
      (by positivity : (0:ℝ) ≤ (d j.val).factorial)
    have hv := div_le_div₀ (by positivity : 0 ≤ (8:ℝ) ^ (d j.val) / ((d j.val).factorial:ℝ))
      hu (Real.exp_pos (-24)) (hV j)
    apply hv.trans
    have hd : 2*K ≤ d j.val := by dsimp [d,rank]; omega
    have hh := pow_le_pow_right₀ ha hd
    dsimp [t]
    rw [mul_pow,Real.exp_neg,div_inv_eq_mul]
    have hfac : (0:ℝ) < (d j.val).factorial := by positivity
    field_simp [ha'.ne',hfac.ne']
    nlinarith [mul_le_mul_of_nonneg_left hh (show 0 ≤ Real.exp 24 * 8^(d j.val) by positivity)]
  have hi : Function.Injective d := by intro j k hh; dsimp [d,rank] at hh; omega
  have hle : ∑ j : Fin m, t (d j.val) ≤ Real.exp (8*a) := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => t (d j)) m]
    rw [←sum_image (f:=t) (g:=d) (fun i _ j _ h => hi h)]
    have hsub : (range m).image d ⊆ range (d m+1) := by
      intro b hb
      obtain ⟨i,hi',rfl⟩ := mem_image.mp hb
      have := mem_range.mp hi'
      apply mem_range.mpr
      dsimp [d,rank]
      omega
    exact (sum_le_sum_of_subset_of_nonneg (f:=t) hsub (fun _ _ _ => by dsimp [t]; positivity)).trans
      (Real.sum_le_exp_of_nonneg (by positivity) _)
  apply (sum_le_sum (s:=univ) (fun j _ => htilt j)).trans
  rw [←mul_sum]
  apply (mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ Real.exp 24 / a^(2*K))).trans
  apply le_of_eq
  dsimp [a,tiltError]
  rw [← Real.exp_nat_mul, ← Real.exp_sub, ← Real.exp_add]
  congr 1
  ring
end
end FareyBrun

open Finset

namespace Conjectures.Goldbach.FareyFullSieveRemainder_aux

/-! ### Counting one residue class in an interval -/

lemma ceil_diff_bound (x y q : ℚ) :
    |((⌈x / q⌉ - ⌈y / q⌉ : ℤ) : ℚ) - (x - y) / q| ≤ 1 := by
  have hxlo : x / q ≤ (⌈x / q⌉ : ℚ) := Int.le_ceil _
  have hxhi : (⌈x / q⌉ : ℚ) < x / q + 1 := Int.ceil_lt_add_one _
  have hylo : y / q ≤ (⌈y / q⌉ : ℚ) := Int.le_ceil _
  have hyhi : (⌈y / q⌉ : ℚ) < y / q + 1 := Int.ceil_lt_add_one _
  have hdiv : (x - y) / q = x / q - y / q := by ring
  rw [abs_le]
  rw [hdiv]
  simp only [Int.cast_sub]
  constructor <;> linarith

lemma ceil_diff_nonneg (x y q : ℚ) (hq : 0 < q) (hxy : y ≤ x) :
    0 ≤ ⌈x / q⌉ - ⌈y / q⌉ := by
  have hqxy : y / q ≤ x / q := by gcongr
  exact sub_nonneg.mpr (Int.ceil_le_ceil hqxy)

theorem card_modEq_Icc (m c l h : ℕ) (hm : 0 < m) (hlh : l ≤ h) :
    |(((Finset.Icc l h).filter (fun u => u ≡ c [MOD m])).card : ℝ)
        - ((h - l + 1 : ℕ) : ℝ) / (m : ℝ)| ≤ 1 := by
  have hset : (Icc l h).filter (fun u => u ≡ c [MOD m]) =
      (Ico l (h + 1)).filter (fun u => u ≡ c [MOD m]) := by
    ext u
    simp [mem_filter, mem_Icc, mem_Ico]
  have hcard := Nat.Ico_filter_modEq_card l (h + 1) hm c
  have hlh' : l ≤ h + 1 := by omega
  have hxy : ((l : ℕ) : ℚ) - (c : ℚ) ≤ ((h + 1 : ℕ) : ℚ) - (c : ℚ) := by
    have hxy' : ((l : ℕ) : ℚ) ≤ ((h + 1 : ℕ) : ℚ) := by exact_mod_cast hlh'
    linarith
  have hceil_nonneg :
      0 ≤ ⌈(((h + 1 : ℕ) : ℚ) - (c : ℚ)) / (m : ℚ)⌉ -
        ⌈(((l : ℕ) : ℚ) - (c : ℚ)) / (m : ℚ)⌉ := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (ceil_diff_nonneg _ _ _ (by exact_mod_cast hm) hxy)
  have hlenQ : ((h - l + 1 : ℕ) : ℚ) =
      ((h + 1 : ℕ) : ℚ) - (l : ℕ) := by
    rw [Nat.cast_add, Nat.cast_sub hlh]
    norm_num [Nat.cast_add, Nat.cast_one]
    ring
  have hcard' : (((Icc l h).filter (fun u => u ≡ c [MOD m])).card : ℤ) =
      ⌈(((h + 1 : ℕ) : ℚ) - (c : ℚ)) / (m : ℚ)⌉ -
        ⌈(((l : ℕ) : ℚ) - (c : ℚ)) / (m : ℚ)⌉ := by
    rw [hset]
    rw [hcard]
    exact max_eq_left hceil_nonneg
  have hbound := ceil_diff_bound
    (((h + 1 : ℕ) : ℚ) - (c : ℚ)) (((l : ℕ) : ℚ) - (c : ℚ)) (m : ℚ)
  have hdiffQ :
      (((h + 1 : ℕ) : ℚ) - (c : ℚ)) -
          (((l : ℕ) : ℚ) - (c : ℚ)) = ((h - l + 1 : ℕ) : ℚ) := by
    rw [hlenQ]
    ring
  rw [hdiffQ] at hbound
  have hcardQ : (((Icc l h).filter (fun u => u ≡ c [MOD m])).card : ℚ) =
      ((⌈(((h + 1 : ℕ) : ℚ) - (c : ℚ)) / (m : ℚ)⌉ -
        ⌈(((l : ℕ) : ℚ) - (c : ℚ)) / (m : ℚ)⌉ : ℤ) : ℚ) := by
    exact_mod_cast hcard'
  have hmainQ :
      |(((Icc l h).filter (fun u => u ≡ c [MOD m])).card : ℚ) -
        ((h - l + 1 : ℕ) : ℚ) / (m : ℚ)| ≤ 1 := by
    rw [hcardQ]
    exact hbound
  have hmainR :
      ((|(((Icc l h).filter (fun u => u ≡ c [MOD m])).card : ℚ) -
        ((h - l + 1 : ℕ) : ℚ) / (m : ℚ)| : ℚ) : ℝ) ≤ (1 : ℝ) := by
    exact_mod_cast hmainQ
  simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast] using hmainR

/-! ### Moebius inversion of the coprimality mask -/

theorem ind_coprime (n u : ℕ) (hn : 0 < n) :
    (∑ k ∈ n.divisors, if k ∣ u then (ArithmeticFunction.moebius k : ℤ) else 0)
      = if Nat.Coprime n u then 1 else 0 := by
  classical
  let m := n.gcd u
  have hm : m ≠ 0 := by
    intro hm
    have hmn : m ∣ n := Nat.gcd_dvd_left n u
    rw [hm] at hmn
    exact hn.ne' (zero_dvd_iff.mp hmn)
  have hfilter : n.divisors.filter (fun k => k ∣ u) = m.divisors := by
    ext k
    constructor
    · intro hk
      rw [mem_filter] at hk
      rw [Nat.mem_divisors]
      exact ⟨Nat.dvd_gcd (Nat.dvd_of_mem_divisors hk.1) hk.2, hm⟩
    · intro hk
      rw [mem_filter]
      have hkm : k ∣ m := (Nat.mem_divisors.mp hk).1
      exact ⟨Nat.mem_divisors.mpr ⟨(dvd_gcd_iff k n u).mp hkm |>.1, hn.ne'⟩,
        (dvd_gcd_iff k n u).mp hkm |>.2⟩
  calc
    (∑ k ∈ n.divisors, if k ∣ u then (ArithmeticFunction.moebius k : ℤ) else 0) =
        ∑ k ∈ n.divisors.filter (fun k => k ∣ u), ArithmeticFunction.moebius k := by
          rw [sum_filter]
    _ = ∑ k ∈ m.divisors, ArithmeticFunction.moebius k := by rw [hfilter]
    _ = if m = 1 then 1 else 0 := by
      have h := congrArg (fun f : ArithmeticFunction ℤ => f m)
        ArithmeticFunction.moebius_mul_coe_zeta
      rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
      exact h
    _ = if Nat.Coprime n u then 1 else 0 := by
      simp [m, Nat.coprime_iff_gcd_eq_one]

theorem sum_moebius_div (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ n.divisors, ((ArithmeticFunction.moebius k : ℤ) : ℝ) / (k : ℝ)
      = (n.totient : ℝ) / (n : ℝ) := by
  classical
  let f : ArithmeticFunction ℝ :=
    ⟨fun k => if k = 0 then 0 else ((k : ℝ))⁻¹, by simp⟩
  have hf : f.IsMultiplicative := by
    rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
    constructor
    · simp [f]
    · intro a b ha hb hab
      simp [f, ha, hb, Nat.mul_ne_zero ha hb, Nat.cast_mul, mul_inv_rev, mul_comm]
  have hprod := hf.prodPrimeFactors_one_sub f hn.ne'
  have htot : (n.totient : ℝ) =
      (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - ((p : ℝ))⁻¹) := by
    simpa only [map_mul, map_natCast, map_prod, map_sub, map_one, map_inv₀] using
      congrArg (Rat.castHom ℝ) (Nat.totient_eq_mul_prod_factors n)
  calc
    (∑ k ∈ n.divisors, ((ArithmeticFunction.moebius k : ℤ) : ℝ) / (k : ℝ)) =
        ∑ k ∈ n.divisors, ((ArithmeticFunction.moebius k : ℤ) : ℝ) * f k := by
          apply sum_congr rfl
          intro k hk
          have hk0 : k ≠ 0 := (Nat.pos_of_mem_divisors hk).ne'
          simp [f, hk0, div_eq_mul_inv]
    _ = ∏ p ∈ n.primeFactors, (1 - f p) := hprod.symm
    _ = ∏ p ∈ n.primeFactors, (1 - ((p : ℝ))⁻¹) := by
      apply prod_congr rfl
      intro p hp
      have hp0 : p ≠ 0 := (Nat.pos_of_mem_primeFactors hp).ne'
      simp [f, hp0]
    _ = (n.totient : ℝ) / (n : ℝ) := by
      rw [htot]
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      exact (mul_div_cancel_left₀ _ hnR).symm

/-! ### The two roots modulo each prime factor -/

/-- Residues `x : ZMod d` with `x * (n - x) = 0`. -/
def Root (d n : ℕ) : Finset (ZMod d) :=
  match d with
  | 0 => {0, (n : ZMod 0)}
  | d + 1 => Finset.univ.filter (fun x => x * ((n : ZMod (d + 1)) - x) = 0)

theorem mem_Root (d n : ℕ) [NeZero d] (x : ZMod d) :
    x ∈ Root d n ↔ x * ((n : ZMod d) - x) = 0 := by
  cases d with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ d => simp [Root]

/-- For `u ≤ n`, the natural-number divisibility `d ∣ u * (n - u)` is the same condition. -/
theorem mem_Root_iff (d n u : ℕ) (hu : u ≤ n) :
    (u : ZMod d) ∈ Root d n ↔ d ∣ u * (n - u) := by
  cases d with
  | zero =>
      simp only [Root, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · have hu0 : u = 0 := by exact_mod_cast h
          simp [hu0]
        · have hun : u = n := by exact_mod_cast h
          simp [hun]
      · intro h
        have hprod : u * (n - u) = 0 := zero_dvd_iff.mp h
        rcases Nat.mul_eq_zero.mp hprod with hu0 | hsub
        · exact Or.inl (by exact_mod_cast hu0)
        · have hun : u = n := by omega
          exact Or.inr (by exact_mod_cast hun)
  | succ d =>
      rw [mem_Root]
      rw [← Nat.cast_sub hu, ← Nat.cast_mul]
      exact ZMod.natCast_eq_zero_iff _ _

theorem mem_Root_crt (q r n : ℕ) [NeZero q] [NeZero r] [NeZero (q * r)]
    (h : Nat.Coprime q r) (x : ZMod (q * r)) :
    ZMod.chineseRemainder h x ∈ Root q n ×ˢ Root r n ↔ x ∈ Root (q * r) n := by
  set e := ZMod.chineseRemainder h
  have hnat : e ((n : ℕ) : ZMod (q * r)) =
      (((n : ℕ) : ZMod q), ((n : ℕ) : ZMod r)) := by
    rw [map_natCast]
    rfl
  have hmul : e (x * (((n : ℕ) : ZMod (q * r)) - x)) =
      ((e x).1 * (((n : ℕ) : ZMod q) - (e x).1),
        (e x).2 * (((n : ℕ) : ZMod r) - (e x).2)) := by
    rw [map_mul, map_sub, hnat]
    rfl
  simp only [Finset.mem_product, mem_Root]
  constructor
  · rintro ⟨h1, h2⟩
    apply e.injective
    rw [hmul, map_zero]
    exact Prod.ext h1 h2
  · intro hx
    have he : e (x * (((n : ℕ) : ZMod (q * r)) - x)) = 0 := by
      rw [hx, map_zero]
    rw [hmul] at he
    exact ⟨by simpa using congrArg Prod.fst he, by simpa using congrArg Prod.snd he⟩

/-- Multiplicativity of the root count via CRT. -/
theorem card_Root_mul (q r n : ℕ) [NeZero q] [NeZero r] [NeZero (q * r)]
    (h : Nat.Coprime q r) :
    (Root (q * r) n).card = (Root q n).card * (Root r n).card := by
  have hbij : (Root (q * r) n).card = (Root q n ×ˢ Root r n).card := by
    refine Finset.card_bij' (fun x (_ : x ∈ Root (q * r) n) => ZMod.chineseRemainder h x)
      (fun y (_ : y ∈ Root q n ×ˢ Root r n) => (ZMod.chineseRemainder h).symm y) ?_ ?_ ?_ ?_
    · intro x hx
      exact (mem_Root_crt q r n h x).2 hx
    · intro y hy
      refine (mem_Root_crt q r n h ((ZMod.chineseRemainder h).symm y)).1 ?_
      rwa [RingEquiv.apply_symm_apply]
    · intro x _
      exact RingEquiv.symm_apply_apply _ _
    · intro y _
      exact RingEquiv.apply_symm_apply _ _
  rw [hbij, Finset.card_product]

/-- Prime case: exactly two roots, namely `0` and `n`. -/
theorem card_Root_prime (p n : ℕ) (hp : Nat.Prime p) (hn : ¬p ∣ n) :
    (Root p n).card = 2 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hn0 : (n : ZMod p) ≠ 0 := by
    intro h
    exact hn ((ZMod.natCast_eq_zero_iff n p).1 h)
  have hroots : Root p n = {0, (n : ZMod p)} := by
    ext x
    simp only [mem_Root, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with hx | hsub
      · exact Or.inl hx
      · exact Or.inr (sub_eq_zero.mp hsub).symm
    · rintro (rfl | rfl)
      · simp
      · simp
  rw [hroots, Finset.card_pair (Ne.symm hn0)]

theorem card_Root_prod (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p)
    (hn : ∀ p ∈ s, ¬p ∣ n) :
    (Root (∏ p ∈ s, p) n).card = 2 ^ s.card := by
  revert hs hn
  induction s using Finset.induction_on with
  | empty =>
      intro _ _
      have hroot : Root 1 n = (univ : Finset (ZMod 1)) := by
        ext x
        simp only [Finset.mem_univ, iff_true]
        rw [mem_Root]
        have hx : x = 0 := Subsingleton.elim x 0
        subst x
        simp
      simp only [prod_empty, pow_zero]
      rw [hroot, Finset.card_univ, ZMod.card, Finset.card_empty, pow_zero]
  | @insert a s ha ih =>
      intro hs hn
      have hpa : Nat.Prime a := hs a (Finset.mem_insert_self a s)
      have hs' : ∀ p ∈ s, Nat.Prime p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
      have hn' : ∀ p ∈ s, ¬p ∣ n := fun p hp => hn p (Finset.mem_insert_of_mem hp)
      have hprodpos : 0 < ∏ p ∈ s, p := Finset.prod_pos fun p hp => (hs' p hp).pos
      have hcop : Nat.Coprime a (∏ p ∈ s, p) := by
        apply Nat.Coprime.prod_right
        intro p hp
        apply (Nat.coprime_primes hpa (hs' p hp)).2
        intro h
        subst p
        exact ha hp
      letI : NeZero a := ⟨hpa.ne_zero⟩
      letI : NeZero (∏ p ∈ s, p) := ⟨hprodpos.ne'⟩
      letI : NeZero (a * ∏ p ∈ s, p) := ⟨(Nat.mul_pos hpa.pos hprodpos).ne'⟩
      calc
        (Root (∏ p ∈ insert a s, p) n).card =
            (Root (a * ∏ p ∈ s, p) n).card := by
              rw [Finset.prod_insert ha]
        _ = (Root a n).card * (Root (∏ p ∈ s, p) n).card :=
          card_Root_mul a (∏ p ∈ s, p) n hcop
        _ = 2 * 2 ^ s.card := by
          rw [card_Root_prime a n hpa (hn a (Finset.mem_insert_self a s)), ih hs' hn']
        _ = 2 ^ (insert a s).card := by
          rw [Finset.card_insert_of_notMem ha, pow_succ]
          omega

/-- The main count. -/
theorem card_Root (d n : ℕ) (hd : 0 < d) (hsq : Squarefree d)
    (hcop : Nat.Coprime d n) :
    (Root d n).card = 2 ^ d.primeFactors.card := by
  have hs : ∀ p ∈ d.primeFactors, Nat.Prime p := fun _ hp =>
    Nat.prime_of_mem_primeFactors hp
  have hn : ∀ p ∈ d.primeFactors, ¬p ∣ n := by
    intro p hp
    have hpn : Nat.Coprime p n :=
      Nat.Coprime.of_dvd_left (Nat.dvd_of_mem_primeFactors hp) hcop
    exact (hs p hp).coprime_iff_not_dvd.mp hpn
  have h := card_Root_prod d.primeFactors hs hn
  rw [Nat.prod_primeFactors_of_squarefree hsq] at h
  exact h

/-! ### The full-window sieve remainder -/

theorem main
    (n d l h : ℕ) (hn : 1 < n) (hd : 0 < d) (hsq : Squarefree d) (hcop : Nat.Coprime d n)
    (hlh : l ≤ h) (hh : h < n) :
    let r : ℝ := (2 : ℝ)^d.primeFactors.card
    let A := ((Finset.Icc l h).filter (fun u => u.Coprime n ∧ d ∣ u*(n-u))).card
    |(A:ℝ) - ((h-l+1 : ℕ):ℝ)*(n.totient:ℝ)*r/((d:ℝ)*n)| ≤ r*(n.divisors.card:ℝ) := by
  classical
  dsimp only
  have hd0 : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  set L : ℝ := ((h - l + 1 : ℕ) : ℝ) with hLdef
  set M : ℝ := L * (n.totient : ℝ) / ((d:ℝ) * (n:ℝ)) with hMdef
  set τ : ℝ := (n.divisors.card : ℝ) with hτdef
  -- membership characterisation
  have hmem : ∀ u ∈ Finset.Icc l h, (u : ZMod d) ∈ Root d n ↔ d ∣ u * (n - u) := by
    intro u hu
    refine mem_Root_iff d n u ?_
    have := Finset.mem_Icc.1 hu
    omega
  -- fibres over the root set
  have hfib : ∀ x ∈ Root d n,
      (((Finset.Icc l h).filter (fun u : ℕ => Nat.Coprime u n ∧ d ∣ u * (n - u))).filter
        (fun u : ℕ => ((u : ℕ) : ZMod d) = x)).card
      = ((Finset.Icc l h).filter
        (fun u : ℕ => Nat.Coprime u n ∧ ((u : ℕ) : ZMod d) = x)).card := by
    intro x hx
    have hset : ((Finset.Icc l h).filter (fun u : ℕ => Nat.Coprime u n ∧ d ∣ u * (n - u))).filter
        (fun u : ℕ => ((u : ℕ) : ZMod d) = x)
        = (Finset.Icc l h).filter
          (fun u : ℕ => Nat.Coprime u n ∧ ((u : ℕ) : ZMod d) = x) := by
      ext u
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hu1, hu2, hu3⟩, hu4⟩; exact ⟨hu1, hu2, hu4⟩
      · rintro ⟨hu1, hu2, hu3⟩
        exact ⟨⟨hu1, hu2, (hmem u hu1).1 (by rw [hu3]; exact hx)⟩, hu3⟩
    rw [hset]
  -- total count as a sum over roots
  have hA : (((Finset.Icc l h).filter
        (fun u : ℕ => Nat.Coprime u n ∧ d ∣ u * (n - u))).card : ℝ)
      = ∑ x ∈ Root d n, (((Finset.Icc l h).filter
        (fun u : ℕ => Nat.Coprime u n ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ) := by
    have h1 : ((Finset.Icc l h).filter (fun u : ℕ => Nat.Coprime u n ∧ d ∣ u * (n - u))).card
        = ∑ x ∈ Root d n, (((Finset.Icc l h).filter
            (fun u : ℕ => Nat.Coprime u n ∧ d ∣ u * (n - u))).filter
            (fun u : ℕ => ((u : ℕ) : ZMod d) = x)).card :=
      Finset.card_eq_sum_card_fiberwise (f := fun u : ℕ => ((u : ℕ) : ZMod d))
        (s := (Finset.Icc l h).filter (fun u : ℕ => Nat.Coprime u n ∧ d ∣ u * (n - u)))
        (t := Root d n) (by
          intro u hu
          have hu' : u ∈ (Finset.Icc l h).filter
              (fun u : ℕ => Nat.Coprime u n ∧ d ∣ u * (n - u)) := hu
          have hu'' := Finset.mem_filter.1 hu'
          exact (hmem u hu''.1).2 hu''.2.2)
    rw [h1, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun x hx => by rw [hfib x hx])
  -- per-root bound
  have hN : ∀ x ∈ Root d n,
      |(((Finset.Icc l h).filter
          (fun u : ℕ => Nat.Coprime u n ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ) - M| ≤ τ := by
    intro x hx
    have hmu : ∀ u : ℕ, (if Nat.Coprime u n then (1:ℝ) else 0)
        = ∑ k ∈ n.divisors,
          (if k ∣ u then ((ArithmeticFunction.moebius k : ℤ) : ℝ) else 0) := by
      intro u
      have hR : ((∑ k ∈ n.divisors,
            if k ∣ u then (ArithmeticFunction.moebius k : ℤ) else (0:ℤ) : ℤ) : ℝ)
          = ∑ k ∈ n.divisors,
            (if k ∣ u then ((ArithmeticFunction.moebius k : ℤ) : ℝ) else 0) := by
        rw [Int.cast_sum]
        exact Finset.sum_congr rfl (fun k _ => by split_ifs <;> simp)
      have h := ind_coprime n u (by omega)
      by_cases hcu : Nat.Coprime u n
      · have hcu' : Nat.Coprime n u := Nat.coprime_comm.mpr hcu
        have h1 : ((∑ k ∈ n.divisors,
            if k ∣ u then (ArithmeticFunction.moebius k : ℤ) else (0:ℤ) : ℤ) : ℝ) = 1 := by
          calc _ = ((if Nat.Coprime n u then (1:ℤ) else (0:ℤ) : ℤ) : ℝ) := by rw [h]
            _ = 1 := by rw [if_pos hcu']; norm_num
        rw [hR] at h1
        rw [if_pos hcu]
        exact h1.symm
      · have hcu' : ¬ Nat.Coprime n u := fun h' => hcu (Nat.coprime_comm.mp h')
        have h1 : ((∑ k ∈ n.divisors,
            if k ∣ u then (ArithmeticFunction.moebius k : ℤ) else (0:ℤ) : ℤ) : ℝ) = 0 := by
          calc _ = ((if Nat.Coprime n u then (1:ℤ) else (0:ℤ) : ℤ) : ℝ) := by rw [h]
            _ = 0 := by rw [if_neg hcu']; norm_num
        rw [hR] at h1
        rw [if_neg hcu]
        exact h1.symm
    -- Moebius expansion of the fibre count
    have hNeq : (((Finset.Icc l h).filter
          (fun u : ℕ => Nat.Coprime u n ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ)
        = ∑ k ∈ n.divisors, ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
            (((Finset.Icc l h).filter
              (fun u : ℕ => k ∣ u ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ) := by
      have hset1 : (Finset.Icc l h).filter
            (fun u : ℕ => Nat.Coprime u n ∧ ((u : ℕ) : ZMod d) = x)
          = ((Finset.Icc l h).filter (fun u : ℕ => ((u : ℕ) : ZMod d) = x)).filter
            (fun u : ℕ => Nat.Coprime u n) := by
        ext u
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hu1, hu2, hu3⟩; exact ⟨⟨hu1, hu3⟩, hu2⟩
        · rintro ⟨⟨hu1, hu3⟩, hu2⟩; exact ⟨hu1, hu2, hu3⟩
      have hset2 : ∀ k : ℕ, ((Finset.Icc l h).filter
              (fun u : ℕ => ((u : ℕ) : ZMod d) = x)).filter (fun u : ℕ => k ∣ u)
          = (Finset.Icc l h).filter
            (fun u : ℕ => k ∣ u ∧ ((u : ℕ) : ZMod d) = x) := by
        intro k
        ext u
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨hu1, hu2⟩, hu3⟩; exact ⟨hu1, hu3, hu2⟩
        · rintro ⟨hu1, hu2, hu3⟩; exact ⟨⟨hu1, hu3⟩, hu2⟩
      calc _ = ((((Finset.Icc l h).filter (fun u : ℕ => ((u : ℕ) : ZMod d) = x)).filter
              (fun u : ℕ => Nat.Coprime u n)).card : ℝ) := by rw [hset1]
        _ = ∑ u ∈ (Finset.Icc l h).filter (fun u : ℕ => ((u : ℕ) : ZMod d) = x),
              (if Nat.Coprime u n then (1:ℝ) else 0) :=
            Finset.natCast_card_filter _ _
        _ = ∑ u ∈ (Finset.Icc l h).filter (fun u : ℕ => ((u : ℕ) : ZMod d) = x),
              ∑ k ∈ n.divisors,
                (if k ∣ u then ((ArithmeticFunction.moebius k : ℤ) : ℝ) else 0) :=
            Finset.sum_congr rfl (fun u _ => hmu u)
        _ = ∑ k ∈ n.divisors,
              ∑ u ∈ (Finset.Icc l h).filter (fun u : ℕ => ((u : ℕ) : ZMod d) = x),
                (if k ∣ u then ((ArithmeticFunction.moebius k : ℤ) : ℝ) else 0) :=
            Finset.sum_comm
        _ = _ := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            have hstep : ∀ u, (if k ∣ u then ((ArithmeticFunction.moebius k : ℤ) : ℝ) else 0)
                = ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
                  (if k ∣ u then (1:ℝ) else 0) := by
              intro u; split_ifs <;> ring
            rw [Finset.sum_congr rfl (fun u _ => hstep u), ← Finset.mul_sum, Finset.sum_boole,
              hset2 k]
    -- each divisor class is a single residue class mod k*d
    have hcr : ∀ k ∈ n.divisors, ∃ c : ℕ, ∀ u : ℕ,
        (k ∣ u ∧ ((u : ℕ) : ZMod d) = x) ↔ u ≡ c [MOD (k * d)] := by
      intro k hk
      have hk0 : 0 < k := Nat.pos_of_mem_divisors hk
      have hkd' : Nat.Coprime k d :=
        (Nat.Coprime.of_dvd_right (Nat.dvd_of_mem_divisors hk) hcop).symm
      letI : NeZero k := ⟨hk0.ne'⟩
      letI : NeZero (k * d) := ⟨(Nat.mul_pos hk0 hd).ne'⟩
      set e := ZMod.chineseRemainder hkd' with he
      set y : ZMod (k * d) := e.symm (0, x) with hy
      refine ⟨y.val, fun u => ?_⟩
      have hE : e ((u : ℕ) : ZMod (k * d)) = ((u : ZMod k), ((u : ℕ) : ZMod d)) := by
        rw [map_natCast]; rfl
      have hyval : ((y.val : ℕ) : ZMod (k * d)) = y := ZMod.natCast_zmod_val y
      constructor
      · rintro ⟨h1, h2⟩
        have h3 : ((u : ℕ) : ZMod (k * d)) = y := by
          apply e.injective
          rw [hE, RingEquiv.apply_symm_apply]
          exact Prod.ext_iff.2 ⟨(ZMod.natCast_eq_zero_iff u k).2 h1, h2⟩
        exact (ZMod.natCast_eq_natCast_iff u y.val (k * d)).1 (by rw [hyval]; exact h3)
      · intro hu
        have h3 : ((u : ℕ) : ZMod (k * d)) = y := by
          have h5 := (ZMod.natCast_eq_natCast_iff u y.val (k * d)).2 hu
          rw [hyval] at h5
          exact h5
        have h4 := congrArg e h3
        rw [hE, RingEquiv.apply_symm_apply] at h4
        exact ⟨(ZMod.natCast_eq_zero_iff u k).1 (congrArg Prod.fst h4), congrArg Prod.snd h4⟩
    -- hence each term is within 1 of L/(k*d)
    have hδ : ∀ k ∈ n.divisors,
        |(((Finset.Icc l h).filter
            (fun u : ℕ => k ∣ u ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ)
          - L / ((k:ℝ) * (d:ℝ))| ≤ 1 := by
      intro k hk
      obtain ⟨c, hc⟩ := hcr k hk
      have hset : (Finset.Icc l h).filter
            (fun u : ℕ => k ∣ u ∧ ((u : ℕ) : ZMod d) = x)
          = (Finset.Icc l h).filter (fun u : ℕ => u ≡ c [MOD (k * d)]) := by
        ext u
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hu1, hu2⟩; exact ⟨hu1, (hc u).1 hu2⟩
        · rintro ⟨hu1, hu2⟩; exact ⟨hu1, (hc u).2 hu2⟩
      rw [hset]
      have hthis := card_modEq_Icc (k * d) c l h (Nat.mul_pos (Nat.pos_of_mem_divisors hk) hd) hlh
      rw [Nat.cast_mul] at hthis
      simpa [hLdef] using hthis
    -- the main term identity
    have hmain : (((Finset.Icc l h).filter
          (fun u : ℕ => Nat.Coprime u n ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ) - M
        = ∑ k ∈ n.divisors, ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
            ((((Finset.Icc l h).filter
              (fun u : ℕ => k ∣ u ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ)
              - L / ((k:ℝ) * (d:ℝ))) := by
      rw [hNeq]
      have hsplit : ∀ k ∈ n.divisors,
          ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
              (((Finset.Icc l h).filter
                (fun u : ℕ => k ∣ u ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ)
            = ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
                ((((Finset.Icc l h).filter
                  (fun u : ℕ => k ∣ u ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ)
                  - L / ((k:ℝ) * (d:ℝ)))
              + ((ArithmeticFunction.moebius k : ℤ) : ℝ) * (L / ((k:ℝ) * (d:ℝ))) := by
        intro k _; ring
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
      have hsum2 : ∑ k ∈ n.divisors,
          ((ArithmeticFunction.moebius k : ℤ) : ℝ) * (L / ((k:ℝ) * (d:ℝ))) = M := by
        have hk0 : ∀ k ∈ n.divisors, (k:ℝ) ≠ 0 := by
          intro k hk; exact_mod_cast (Nat.pos_of_mem_divisors hk).ne'
        have hstep : ∀ k ∈ n.divisors,
            ((ArithmeticFunction.moebius k : ℤ) : ℝ) * (L / ((k:ℝ) * (d:ℝ)))
              = (L / (d:ℝ)) * (((ArithmeticFunction.moebius k : ℤ) : ℝ) / (k:ℝ)) := by
          intro k hk
          field_simp
        rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, sum_moebius_div n (by omega)]
        rw [hMdef]
        field_simp
      rw [hsum2]
      ring
    -- bound the error sum
    have hμ : ∀ k : ℕ, |((ArithmeticFunction.moebius k : ℤ) : ℝ)| ≤ 1 := by
      intro k
      calc |((ArithmeticFunction.moebius k : ℤ) : ℝ)|
          = ((|(ArithmeticFunction.moebius k : ℤ)| : ℤ) : ℝ) := by rw [Int.cast_abs]
        _ ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k)
    have hbd : |∑ k ∈ n.divisors, ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
            ((((Finset.Icc l h).filter
              (fun u : ℕ => k ∣ u ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ)
              - L / ((k:ℝ) * (d:ℝ)))| ≤ τ := by
      calc |∑ k ∈ n.divisors, ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
            ((((Finset.Icc l h).filter
              (fun u : ℕ => k ∣ u ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ)
              - L / ((k:ℝ) * (d:ℝ)))|
          ≤ ∑ k ∈ n.divisors, |((ArithmeticFunction.moebius k : ℤ) : ℝ) *
              ((((Finset.Icc l h).filter
                (fun u : ℕ => k ∣ u ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ)
                - L / ((k:ℝ) * (d:ℝ)))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k ∈ n.divisors, |((ArithmeticFunction.moebius k : ℤ) : ℝ)| *
              |(((Finset.Icc l h).filter
                (fun u : ℕ => k ∣ u ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ)
                - L / ((k:ℝ) * (d:ℝ))| :=
            Finset.sum_congr rfl (fun k _ => abs_mul _ _)
        _ ≤ ∑ k ∈ n.divisors, (1:ℝ) * 1 :=
            Finset.sum_le_sum (fun k hk =>
              mul_le_mul (hμ k) (hδ k hk) (abs_nonneg _) (by norm_num))
        _ = τ := by simp [hτdef]
    rw [hmain]
    exact hbd
  -- assemble
  have hfinal : |(((Finset.Icc l h).filter
        (fun u : ℕ => Nat.Coprime u n ∧ d ∣ u * (n - u))).card : ℝ)
      - ((Root d n).card : ℝ) * M| ≤ ((Root d n).card : ℝ) * τ := by
    rw [hA]
    have hsplit : (∑ x ∈ Root d n, (((Finset.Icc l h).filter
          (fun u : ℕ => Nat.Coprime u n ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ))
        - ((Root d n).card : ℝ) * M
        = ∑ x ∈ Root d n, ((((Finset.Icc l h).filter
            (fun u : ℕ => Nat.Coprime u n ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ) - M) := by
      have hsumM : ∑ x ∈ Root d n, M = ((Root d n).card : ℝ) * M := by
        simp [Finset.sum_const, nsmul_eq_mul]
      rw [Finset.sum_sub_distrib, hsumM]
    rw [hsplit]
    calc |∑ x ∈ Root d n, ((((Finset.Icc l h).filter
            (fun u : ℕ => Nat.Coprime u n ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ) - M)|
        ≤ ∑ x ∈ Root d n, |(((Finset.Icc l h).filter
            (fun u : ℕ => Nat.Coprime u n ∧ ((u : ℕ) : ZMod d) = x)).card : ℝ) - M| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ Root d n, τ := Finset.sum_le_sum (fun x hx => hN x hx)
      _ = ((Root d n).card : ℝ) * τ := by simp [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Root d n).card : ℝ) = (2 : ℝ) ^ d.primeFactors.card := by
    rw [card_Root d n hd hsq hcop]; push_cast; ring
  rw [hcard] at hfinal
  have hMval : (2 : ℝ) ^ d.primeFactors.card * M
      = L * (n.totient : ℝ) * (2 : ℝ) ^ d.primeFactors.card
        / ((d : ℝ) * (n : ℝ)) := by
    rw [hMdef]
    field_simp
  rw [← hMval]
  exact hfinal

end Conjectures.Goldbach.FareyFullSieveRemainder_aux

theorem Conjectures.Goldbach.FareyFullSieveRemainder :
    ∀ n d l h : ℕ, 1 < n → 0 < d → Squarefree d → d.Coprime n → l ≤ h → h < n → let r : ℝ := (2 : ℝ)^d.primeFactors.card; let A := ((Finset.Icc l h).filter (fun u => u.Coprime n ∧ d ∣ u*(n-u))).card; |(A:ℝ) - ((h-l+1 : ℕ):ℝ)*(n.totient:ℝ)*r/((d:ℝ)*n)| ≤ r*(n.divisors.card:ℝ) := by
  intro n d l h hn hd hsq hcop hlh hh
  exact Conjectures.Goldbach.FareyFullSieveRemainder_aux.main n d l h hn hd hsq hcop hlh hh

namespace FareyBrun
open Finset ErdosStraus.RoughEstimates ErdosStraus.BrunHooley
open scoped BigOperators
noncomputable section
open scoped Classical

def window (n : ℕ) := Icc ((n+2)/3) ((2*n)/3)
def mask (n : ℕ) := (window n).filter (fun u => u.Coprime n)
def primes (z : ℕ) := (Icc 2 z).filter Nat.Prime
def good (n z : ℕ) := (primes z).filter (fun p => ¬ p ∣ n)
def scale (n : ℕ) : ℝ := ((window n).card:ℝ) * n.totient / n
def mainTerm (n z : ℕ) : ℝ := scale n * ∏ p ∈ good n z, (1 - 2/(p:ℝ))
def sift (n z : ℕ) := ((window n).filter (fun u => u.Coprime n ∧ z < (u*(n-u)).minFac)).card

theorem prime_intersection {n : ℕ} (hn : 64 ≤ n) (s : Finset ℕ)
    (hpr : ∀ p ∈ s, Nat.Prime p) (hc : ∀ p ∈ s, ¬ p ∣ n) :
    let d := ∏ p ∈ s, p
    |intersectionCount (mask n) (fun p u => p ∣ u*(n-u)) s -
       scale n * ∏ p ∈ s, (2/(p:ℝ))| ≤ (d:ℝ) * n.divisors.card := by
  let d := ∏ p ∈ s, p
  have hd : 0 < d := prod_pos (fun p hp => (hpr p hp).pos)
  have hf : d.primeFactors = s := Nat.primeFactors_prod hpr
  have hsq : Squarefree d := by
    have h := Nat.squarefree_prod_primeFactors d
    rwa [hf] at h
  have hcop : d.Coprime n := Nat.coprime_prod_left_iff.mpr (fun p hp => (hpr p hp).coprime_iff_not_dvd.mpr (hc p hp))
  have hi : (n+2)/3 ≤ 2*n/3 := by omega
  have hu : 2*n/3 < n := by omega
  have count := Conjectures.Goldbach.FareyFullSieveRemainder n d _ _ (by omega) hd hsq hcop hi hu
  dsimp only at count
  have hset : ((mask n).filter (fun u => ∀ p ∈ s, p ∣ u*(n-u))) =
      ((window n).filter (fun u => u.Coprime n ∧ d ∣ u*(n-u))) := by
    ext u
    simp only [mask,mem_filter]
    constructor
    · rintro ⟨⟨hu,hcop⟩,hall⟩
      exact ⟨hu,hcop,Finset.prod_primes_dvd _ (fun p hp => (hpr p hp).prime) hall⟩
    · rintro ⟨hu,hcop,hdiv⟩
      exact ⟨⟨hu,hcop⟩,fun p hp => dvd_trans (dvd_prod_of_mem (fun x : ℕ => x) hp) hdiv⟩
  have hw : (∏ p ∈ s, 2/(p:ℝ)) = 2^s.card / (d:ℝ) := by
    dsimp [d]
    simp [prod_div_distrib]
  have hlen : (window n).card = 2*n/3-(n+2)/3+1 := by simp only [window,Nat.card_Icc]; omega
  have hnorm : scale n * ∏ p ∈ s, 2/(p:ℝ) =
       ((2*n/3-(n+2)/3+1:ℕ):ℝ)*n.totient * 2^d.primeFactors.card / ((d:ℝ)*n) := by
    rw [hw,hf,scale,hlen]; ring
  have hr : (2:ℝ)^s.card ≤ d := by
    change _ ≤ ((∏ p ∈ s, p : ℕ):ℝ)
    push_cast
    rw [← show (∏ _p ∈ s, (2:ℝ)) = 2^s.card by simp]
    exact fareyProdLe (fun _ _ => by norm_num) (fun p hp => by exact_mod_cast (hpr p hp).two_le)
  dsimp only
  unfold intersectionCount
  simp only
  change |(((mask n).filter (fun u => ∀ p ∈ s, p ∣ u*(n-u))).card:ℝ) -
    scale n * ∏ p ∈ s, 2/(p:ℝ)| ≤ (d:ℝ)*n.divisors.card
  rw [hset,hnorm]
  apply count.trans
  rw [hf]
  exact mul_le_mul_of_nonneg_right hr (by positivity)

theorem window_round {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n z : ℕ} (hn : 64≤n) (P : ι → Finset ℕ) (hP : ∀ j, P j ⊆ good n z)
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) (k : ι → ℕ)
    (W : ℕ) (hW : ∀ f ∈ choices P k, selectedProduct f ≤ W) :
    ∃ E : ℝ, (choices P k).card * E ≤ (W:ℝ)^2*n.divisors.card ∧
      ∀ f ∈ choices P k, |intersectionCount (mask n) (fun p u => p ∣ u*(n-u)) (selected f) -
          scale n * ∏ j, ∏ p ∈ f j, 2/(p:ℝ)| ≤ E := by
  have hpr (j : ι) (p : ℕ) (hp : p ∈ P j) : p.Prime :=
    (mem_filter.mp (mem_filter.mp (hP j hp)).1).2
  refine ⟨(W:ℝ)*n.divisors.card, ?_, ?_⟩
  · have hcount : ((choices P k).card:ℝ) ≤ W := by exact_mod_cast choices_card_le_of_product_le P hpr hd k W hW
    calc _ ≤ (W:ℝ)*(W*n.divisors.card) := mul_le_mul_of_nonneg_right hcount (by positivity)
         _ = _ := by ring
  · intro f hf
    have hpr' := selected_primes hpr hf
    have hn' (p : ℕ) (hp : p ∈ selected f) : ¬ p ∣ n := by
      obtain ⟨j,_,hj⟩ := mem_biUnion.mp hp
      exact (mem_filter.mp (hP j ((mem_choices.mp hf j).1 hj))).2
    have hprod : (∏ p ∈ selected f, 2/(p:ℝ)) = ∏ j, ∏ p ∈ f j, 2/(p:ℝ) := by
      apply prod_biUnion
      intro j _ l _ hjl
      exact (hd hjl).mono (mem_choices.mp hf j).1 (mem_choices.mp hf l).1
    rw [←hprod]
    apply (prime_intersection hn (selected f) hpr' hn').trans
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hW f hf) (by positivity)
end
end FareyBrun

namespace FareyBrun
open Finset
noncomputable section
open scoped Classical

theorem sift_mask (n z : ℕ) (hn : 64≤n) :
    ((mask n).filter (fun u => ∀ p ∈ good n z, ¬p ∣ u*(n-u))).card = sift n z := by
  apply congrArg Finset.card
  ext u
  simp only [mask,mem_filter]
  constructor
  · rintro ⟨⟨hu,hc⟩,hs⟩
    refine ⟨hu,hc,?_⟩
    obtain ⟨hl,hh⟩ := mem_Icc.mp hu
    have hu2 : 2≤u := by omega
    have hv2 : 2≤n-u := by omega
    have hprod : u*(n-u) ≠ 1 := by nlinarith
    let p := (u*(n-u)).minFac
    have hpr : p.Prime := Nat.minFac_prime hprod
    have hd : p ∣ u*(n-u) := Nat.minFac_dvd _
    have hpn : ¬p ∣ n := by
      intro h
      have hnpu : ¬p ∣ u := by
        intro h'
        exact hpr.not_dvd_one (hc ▸ Nat.dvd_gcd h' h)
      rcases hpr.dvd_mul.mp hd with h'|h'
      · exact hnpu h'
      · have hu' : n-(n-u)=u := by omega
        exact hnpu (hu' ▸ Nat.dvd_sub h h')
    by_contra! h
    exact hs p (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hpr.two_le,h⟩,hpr⟩,hpn⟩) hd
  · rintro ⟨hu,hc,hmin⟩
    refine ⟨⟨hu,hc⟩,?_⟩
    intro p hp hd
    obtain ⟨hI,hpr⟩ := mem_filter.mp (mem_filter.mp hp).1
    have hh := Nat.minFac_le_of_dvd hpr.two_le hd
    exact (not_lt_of_ge ((mem_Icc.mp hI).2)) (hmin.trans_le hh)

theorem sift_blocks {ι : Type*} [Fintype ι] (n z : ℕ) (hn : 64≤n)
    (P : ι → Finset ℕ) (hcover : univ.biUnion P = good n z) :
    ((mask n).filter (fun u => ∀ j p, p ∈ P j → ¬ p ∣ u*(n-u))).card = sift n z := by
  rw [← sift_mask n z hn, ← hcover]
  congr 1
  apply filter_congr
  intro u _
  simp only [mem_biUnion,mem_univ,true_and,forall_exists_index]
  aesop
end
end FareyBrun

namespace FareyBrun
open Finset Real ErdosStraus.BrunHooley
open scoped BigOperators
noncomputable section
open scoped Classical

def blocks (n z : ℕ) (j : ℕ) : Finset ℕ := (good n z).filter
  (fun p : ℕ => edge z (j+1) < (p:ℝ) ∧ (p:ℝ) ≤ edge z j)
def blockCount (z : ℕ) := ⌈Real.log z / Real.log 2⌉₊ + 1

theorem edge_antitone {z : ℕ} (hz : 1 ≤ z) : Antitone (edge (z:ℝ)) := by
  intro i j hij
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_left (Real.log_nonneg (by exact_mod_cast hz)) (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hij)

theorem block_disjoint (n z : ℕ) (hz : 2≤z) {m : ℕ} :
    Pairwise (fun i j : Fin m => Disjoint (blocks n z i.val) (blocks n z j.val)) := by
  intro i j hne
  apply disjoint_left.mpr
  intro p hi hj
  have h := (mem_filter.mp hi).2
  have g := (mem_filter.mp hj).2
  rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun h => hne (Fin.ext h)) with hl|hl
  · exact (not_lt_of_ge (g.2.trans (edge_antitone (by omega : 1≤z) (by omega : i.val+1 ≤ j.val)))) h.1
  · exact (not_lt_of_ge (h.2.trans (edge_antitone (by omega : 1≤z) (by omega : j.val+1 ≤ i.val)))) g.1

theorem last_edge {z : ℕ} (hz : 2≤z) : edge (z:ℝ) (blockCount z) < 2 := by
  have hlog := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hceil := Nat.le_ceil (Real.log z / Real.log 2)
  have hcount : Real.log z / Real.log 2 < (blockCount z:ℝ) := by dsimp [blockCount]; push_cast; linarith
  have hn : ((blockCount z):ℝ) ≤ 2^(blockCount z) := by
    exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self (n:=blockCount z)))
  have hh := (div_lt_iff₀ hlog).mp (hcount.trans_le hn)
  unfold edge
  rw [←Real.exp_log (by norm_num : (0:ℝ)<2)]
  apply Real.exp_lt_exp.mpr
  rw [div_lt_iff₀ (by positivity)]
  rw [Real.exp_log (by norm_num : (0:ℝ)<2)]
  linarith

theorem block_cover (n z : ℕ) (hz : 2≤z) :
    (univ.biUnion (fun j : Fin (blockCount z) => blocks n z j.val)) = good n z := by
  ext p
  constructor
  · intro hp
    obtain ⟨j,_,hj⟩ := mem_biUnion.mp hp
    exact (mem_filter.mp hj).1
  · intro hp
    have hI := (mem_Icc.mp (mem_filter.mp (mem_filter.mp hp).1).1)
    have h2 : (2:ℝ) ≤ p := by exact_mod_cast hI.1
    let Q := fun j : ℕ => edge (z:ℝ) (j+1)<(p:ℝ)
    have hmpos : 0 < blockCount z := by simp [blockCount]
    have hx : Q (blockCount z-1) := by
      dsimp [Q]
      rw [Nat.sub_add_cancel hmpos]
      exact (last_edge hz).trans_le h2
    have hex := Exists.intro (blockCount z-1) hx
    let j := Nat.find hex
    have hlow : Q j := Nat.find_spec hex
    have hj : j ≤ blockCount z-1 := Nat.find_min' hex hx
    have hu : (p:ℝ) ≤ edge z j := by
      by_cases h0 : j=0
      · rw [h0,edge]; simp only [pow_zero,div_one,Real.exp_log (show (0:ℝ)<z by exact_mod_cast (by omega : 0<z))]
        exact_mod_cast hI.2
      · have h := Nat.find_min hex (show j-1 < j by omega)
        change ¬edge (z:ℝ) (j-1+1)<(p:ℝ) at h
        rw [Nat.sub_add_cancel (by omega)] at h
        exact le_of_not_gt h
    exact mem_biUnion.mpr ⟨⟨j,by omega⟩,mem_univ _,mem_filter.mpr ⟨hp,hlow,hu⟩⟩

theorem blocks_prime (n z j p : ℕ) (hp : p ∈ blocks n z j) : p.Prime :=
  (mem_filter.mp (mem_filter.mp (mem_filter.mp hp).1).1).2

theorem block_mass (n z j : ℕ) (hz : 2≤z) : ∑ p ∈ blocks n z j, 2/(p:ℝ) ≤ 8 := by
  have hx : 1 < edge z j := Real.one_lt_exp_iff.mpr (by
    have := Real.log_pos (by exact_mod_cast (by omega : 1<z) : (1:ℝ)<z)
    positivity)
  apply half_log_block (edge z j) hx
  intro p hp
  obtain ⟨hl,hu⟩ := (mem_filter.mp hp).2
  refine ⟨blocks_prime n z j p hp,hu,?_⟩
  have hh := Real.log_le_log (Real.exp_pos _) hl.le
  unfold edge at hh ⊢
  rw [Real.log_exp] at hh ⊢
  rw [pow_succ,←div_div] at hh
  linarith

theorem block_euler (n z j : ℕ) (hn : Even n) (hz : 2≤z) :
    Real.exp (-24) ≤ ∏ p ∈ blocks n z j, (1-2/(p:ℝ)) := by
  have h3 (p : ℕ) (hp : p ∈ blocks n z j) : 3≤p := by
    have hpr := blocks_prime n z j p hp
    have hc := (mem_filter.mp (mem_filter.mp hp).1).2
    have h2 := hpr.two_le
    have hd : 2 ∣ n := even_iff_two_dvd.mp hn
    by_contra! h
    obtain rfl : p=2 := by omega
    exact hc hd
  apply le_trans _ (euler_density_lower _ h3)
  apply Real.exp_le_exp.mpr
  linarith [block_mass n z j hz]
end
end FareyBrun

/-!
# PREPUB goldbach gap: `L-goldbach-farey-sieve-terminal-floor`

On the Farey middle third the normalized sieve mass `V n z` dominates `(2/3)·|I|·M(z)²`.
The proof splits the prime factors `p ≤ √n` into those dividing `n` (local factor
`1 - 1/p`) and those not dividing `n` (local factor `(1 - 1/p)²/(1 - 2/p)`), then bounds

* `∏_{p ∣ n, p ≤ √n} (1 - 1/p) ≤ 1/2` (the prime `2` divides the even number `n`),
* `∏_{p ≤ √n, p ∤ n} (1 - 1/p)²/(1 - 2/p) ≤ 2` (a Wallis-type telescoping product),
* `∏_{p ∣ n, p > √n} (1 - 1/p) ≥ 4/5` (at most one such prime, and it is at least `5`).
-/


open scoped BigOperators
open Finset

namespace PEqualNP.Outside

/-- The Wallis-type factor `m²/((m-1)(m+1)) = 1 + 1/(m²-1)`. -/
noncomputable def wallisFac (m : ℕ) : ℝ := (m:ℝ)^2 / (((m:ℝ)-1)*((m:ℝ)+1))

/-- Wallis-type telescoping product: `∏_{m=2}^{M} wallisFac m = 2M/(M+1)`. -/
theorem wallis_telescope : ∀ M : ℕ, 1 ≤ M →
    ∏ m ∈ Finset.Icc 2 M, wallisFac m = 2*(M:ℝ)/((M:ℝ)+1) := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => norm_num [wallisFac]
  | succ M hM ih =>
      rw [Finset.prod_Icc_succ_top (f := wallisFac) (by omega : 2 ≤ M + 1)]
      rw [ih]
      have hM0 : (M:ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
      have h1 : (M:ℝ) + 1 ≠ 0 := by positivity
      have h2 : (M:ℝ) + 2 ≠ 0 := by positivity
      simp only [wallisFac]
      push_cast
      field_simp [hM0, h1, h2]
      ring

/- PREPUB frozen statement `L-goldbach-farey-sieve-terminal-floor`. -/
set_option maxHeartbeats 1000000 in
theorem L_goldbach_farey_sieve_terminal_floor :
    let I := fun n : ℕ => Finset.Icc ((n+2)/3) ((2*n)/3);
    let P := fun z : ℕ => (Finset.Icc 2 z).filter Nat.Prime;
    let M := fun z : ℕ => ∏ p ∈ P z, (1-(p:ℝ)⁻¹);
    let V := fun n z : ℕ => ((I n).card:ℝ)*(n.totient:ℝ)/n * ∏ p ∈ (P z).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ));
    ∀ n : ℕ, 12 ≤ n → Even n → (2/3:ℝ)*((I n).card:ℝ)*(M (Nat.sqrt n))^2 ≤ V n (Nat.sqrt n) := by
  dsimp only
  classical
  intro n hn hEven
  set z : ℕ := Nat.sqrt n with hz
  set Pz : Finset ℕ := (Finset.Icc 2 z).filter Nat.Prime with hPz
  set Sz : Finset ℕ := Pz.filter (fun p => p ∣ n) with hSz
  set Tz : Finset ℕ := Pz.filter (fun p => ¬ p ∣ n) with hTz
  set Iz : Finset ℕ := Finset.Icc ((n+2)/3) ((2*n)/3) with hIz
  set Es : Finset ℕ := n.primeFactors.filter (fun p => z < p) with hEs
  set A : ℝ := ∏ p ∈ Sz, (1 - (p:ℝ)⁻¹) with hA
  set B : ℝ := ∏ p ∈ Tz, (1 - (p:ℝ)⁻¹) with hB
  set Tp : ℝ := ∏ p ∈ Tz, (1 - 2/(p:ℝ)) with hTp
  set E : ℝ := ∏ p ∈ Es, (1 - (p:ℝ)⁻¹) with hE
  have hn0 : n ≠ 0 := by omega
  have hz3 : 3 ≤ z := by
    rw [hz, Nat.le_sqrt']
    omega
  have hz_sq : z ^ 2 ≤ n := by rw [hz]; exact Nat.sqrt_le' n
  have hz_succ_sq : n < (z + 1) ^ 2 := by rw [hz]; exact Nat.lt_succ_sqrt' n
  have h2dvd : 2 ∣ n := even_iff_two_dvd.mp hEven
  -- |I| > 0
  have hIfact : Iz.card = (2*n)/3 + 1 - ((n+2)/3) := by rw [hIz]; exact Nat.card_Icc _ _
  have hIpos : (0:ℝ) < (Iz.card:ℝ) := by
    have hle : ((n+2)/3) ≤ ((2*n)/3) := by
      apply Nat.div_le_div_right; omega
    have hpos : 0 < Iz.card := by rw [hIfact]; omega
    exact_mod_cast hpos
  -- membership characterisations
  have hmemP : ∀ p : ℕ, p ∈ Pz ↔ p.Prime ∧ p ≤ z := by
    intro p
    rw [hPz, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨-, hpz⟩, hpp⟩; exact ⟨hpp, hpz⟩
    · rintro ⟨hpp, hpz⟩; exact ⟨⟨hpp.two_le, hpz⟩, hpp⟩
  have hmemS : ∀ p : ℕ, p ∈ Sz ↔ p.Prime ∧ p ∣ n ∧ p ≤ z := by
    intro p
    rw [hSz, Finset.mem_filter, hmemP]
    constructor
    · rintro ⟨⟨hpp, hpz⟩, hdvd⟩; exact ⟨hpp, hdvd, hpz⟩
    · rintro ⟨hpp, hdvd, hpz⟩; exact ⟨⟨hpp, hpz⟩, hdvd⟩
  have hmemT : ∀ p : ℕ, p ∈ Tz ↔ p.Prime ∧ ¬ p ∣ n ∧ p ≤ z := by
    intro p
    rw [hTz, Finset.mem_filter, hmemP]
    constructor
    · rintro ⟨⟨hpp, hpz⟩, hnd⟩; exact ⟨hpp, hnd, hpz⟩
    · rintro ⟨hpp, hnd, hpz⟩; exact ⟨⟨hpp, hpz⟩, hnd⟩
  have hmemE : ∀ p : ℕ, p ∈ Es ↔ p.Prime ∧ p ∣ n ∧ z < p := by
    intro p
    rw [hEs, Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hpp, hdvd, -⟩, hzp⟩; exact ⟨hpp, hdvd, hzp⟩
    · rintro ⟨hpp, hdvd, hzp⟩; exact ⟨⟨hpp, hdvd, hn0⟩, hzp⟩
  have hdisj : Disjoint Sz Tz := by
    rw [hSz, hTz]
    exact Finset.disjoint_filter_filter_not _ _ _
  have hPsplit : Pz = Sz ∪ Tz := by
    rw [hSz, hTz]
    exact (Finset.filter_union_filter_not_eq (p := fun p => p ∣ n) Pz).symm
  -- `p ∈ Tz` is odd and at least 3
  have hT_three : ∀ p ∈ Tz, 3 ≤ p := by
    intro p hp
    have hpp : p.Prime := ((hmemT p).mp hp).1
    have hnd : ¬ p ∣ n := ((hmemT p).mp hp).2.1
    have hp2 : 2 ≤ p := hpp.two_le
    have hne2 : p ≠ 2 := by intro h; exact hnd (h ▸ h2dvd)
    have hodd : p % 2 = 1 := hpp.eq_two_or_odd.resolve_left hne2
    omega
  -- `Tp ≥ 0`
  have hTp_nonneg : 0 ≤ Tp := by
    rw [hTp]
    apply Finset.prod_nonneg
    intro p hp
    have hp3 : 3 ≤ p := hT_three p hp
    have hp3r : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp3
    have hpos : (0:ℝ) < (p:ℝ) := by linarith
    rw [sub_nonneg, div_le_one hpos]
    linarith
  -- the Wallis-type bound: `∏ (1-1/p)²/(1-2/p) ≤ 2`
  have hQ : (∏ p ∈ Tz, ((1 - (p:ℝ)⁻¹)^2 / (1 - 2/(p:ℝ)))) ≤ 2 := by
    have hfac : ∀ p ∈ Tz, ((1 - (p:ℝ)⁻¹)^2 / (1 - 2/(p:ℝ))) = wallisFac (p - 1) := by
      intro p hp
      have hp3 : 3 ≤ p := hT_three p hp
      have hp3r : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp3
      have hp0 : (0:ℝ) < (p:ℝ) := by linarith
      have hp0' : (p:ℝ) ≠ 0 := ne_of_gt hp0
      have hp2a : (p:ℝ) - 2 ≠ 0 := by intro h; linarith
      have hp2b : (-2 + (p:ℝ)) ≠ 0 := by intro h; linarith
      have hA1 : (p:ℝ) - 1 - 1 ≠ 0 := by intro h; linarith
      have hA2 : (p:ℝ) - 1 + 1 ≠ 0 := by intro h; linarith
      have hden : (1:ℝ) - 2/(p:ℝ) ≠ 0 := by
        have hlt : (2:ℝ)/(p:ℝ) < 1 := by
          rw [div_lt_one hp0]; linarith
        linarith
      have h1 : (((p - 1 : ℕ)) : ℝ) = (p:ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ p)]
        norm_num
      simp only [wallisFac]
      rw [h1]
      field_simp
      ring
    have hstep : (∏ p ∈ Tz, ((1 - (p:ℝ)⁻¹)^2 / (1 - 2/(p:ℝ))))
        = ∏ p ∈ Tz, wallisFac (p - 1) := Finset.prod_congr rfl hfac
    rw [hstep]
    have hinj : Set.InjOn (fun p : ℕ => p - 1) (↑Tz : Set ℕ) := by
      intro a ha b hb hab
      have ha3 : 3 ≤ a := hT_three a ha
      have hb3 : 3 ≤ b := hT_three b hb
      have hab' : a - 1 = b - 1 := hab
      omega
    have hsubimg : (Tz.image (fun p => p - 1)) ⊆ Finset.Icc 2 (z - 1) := by
      intro m hm
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
      have hp3 : 3 ≤ p := hT_three p hp
      have hpz : p ≤ z := ((hmemT p).mp hp).2.2
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hfac1 : ∀ m ∈ Finset.Icc 2 (z - 1), (1:ℝ) ≤ wallisFac m := by
      intro m hm
      obtain ⟨hm2, -⟩ := Finset.mem_Icc.mp hm
      have hm2r : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm2
      have hpos : (0:ℝ) < ((m:ℝ)-1)*((m:ℝ)+1) := by nlinarith
      simp only [wallisFac]
      rw [le_div_iff₀ hpos]
      nlinarith
    have hfac0 : ∀ m ∈ Finset.Icc 2 (z - 1), (0:ℝ) ≤ wallisFac m := by
      intro m hm
      obtain ⟨hm2, -⟩ := Finset.mem_Icc.mp hm
      have hm2r : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm2
      have hpos : (0:ℝ) < ((m:ℝ)-1)*((m:ℝ)+1) := by nlinarith
      simp only [wallisFac]
      exact div_nonneg (sq_nonneg _) hpos.le
    calc ∏ p ∈ Tz, wallisFac (p - 1)
        = ∏ m ∈ Tz.image (fun p => p - 1), wallisFac m :=
          (Finset.prod_image (f := wallisFac) (g := fun p : ℕ => p - 1) hinj).symm
      _ ≤ ∏ m ∈ Finset.Icc 2 (z - 1), wallisFac m := by
          apply Finset.prod_le_prod_of_subset_of_one_le₀ hsubimg
          · intro m hm
            exact hfac0 m (hsubimg hm)
          · intro m hm _
            exact hfac1 m hm
      _ = 2*(((z - 1 : ℕ)):ℝ)/((((z - 1 : ℕ)):ℝ)+1) := wallis_telescope (z - 1) (by omega)
      _ ≤ 2 := by
          have hz1 : (1:ℝ) ≤ (((z - 1 : ℕ)):ℝ) := by exact_mod_cast (by omega : 1 ≤ z - 1)
          have hden : (0:ℝ) < (((z - 1 : ℕ)):ℝ) + 1 := by linarith
          rw [div_le_iff₀ hden]
          nlinarith
  have hB2 : B ^ 2 ≤ 2 * Tp := by
    have heq : B ^ 2 = (∏ p ∈ Tz, ((1 - (p:ℝ)⁻¹)^2 / (1 - 2/(p:ℝ)))) * Tp := by
      rw [hB, hTp, sq, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      have hp3 : 3 ≤ p := hT_three p hp
      have hp3r : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp3
      have hp0 : (0:ℝ) < (p:ℝ) := by linarith
      have hden : (1:ℝ) - 2/(p:ℝ) ≠ 0 := by
        have hlt : (2:ℝ)/(p:ℝ) < 1 := by
          rw [div_lt_one hp0]; linarith
        linarith
      have hp0' : (p:ℝ) ≠ 0 := ne_of_gt hp0
      have hp2a : (p:ℝ) - 2 ≠ 0 := by intro h; linarith
      have hp2b : (-2 + (p:ℝ)) ≠ 0 := by intro h; linarith
      have hA1 : (p:ℝ) - 1 - 1 ≠ 0 := by intro h; linarith
      have hA2 : (p:ℝ) - 1 + 1 ≠ 0 := by intro h; linarith
      field_simp
    rw [heq]
    nlinarith [hQ, hTp_nonneg]
  -- `A ≤ 1/2`: the prime `2` divides the even number `n`
  have h2S : (2:ℕ) ∈ Sz := (hmemS 2).mpr ⟨by norm_num, h2dvd, by omega⟩
  have hA2 : A ≤ 1/2 := by
    rw [hA]
    have heq : (∏ p ∈ Sz, (1 - (p:ℝ)⁻¹))
        = (∏ p ∈ Sz \ {2}, (1 - (p:ℝ)⁻¹)) * (1 - (2:ℝ)⁻¹) :=
      Finset.prod_eq_prod_sdiff_singleton_mul h2S _
    rw [heq]
    have hrest_nonneg : 0 ≤ ∏ p ∈ Sz \ {2}, (1 - (p:ℝ)⁻¹) := by
      apply Finset.prod_nonneg
      intro p hp
      have hpp : p.Prime := ((hmemS p).mp (Finset.mem_sdiff.mp hp).1).1
      have hp1 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
      have hinv : (p:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hpp.one_le)
      linarith
    have hrest_le : (∏ p ∈ Sz \ {2}, (1 - (p:ℝ)⁻¹)) ≤ 1 := by
      apply Finset.prod_le_one₀
      · intro p hp
        have hpp : p.Prime := ((hmemS p).mp (Finset.mem_sdiff.mp hp).1).1
        have hp1 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
        have hinv : (p:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hpp.one_le)
        linarith
      · intro p hp
        have hpp : p.Prime := ((hmemS p).mp (Finset.mem_sdiff.mp hp).1).1
        have hp1 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
        have hinv : 0 ≤ (p:ℝ)⁻¹ := inv_nonneg.mpr hp1.le
        linarith
    have hconst : (1 - (2:ℝ)⁻¹) = 1/2 := by norm_num
    rw [hconst]
    nlinarith [hrest_nonneg, hrest_le]
  -- `E ≥ 4/5`: at most one prime factor of `n` exceeds `√n`, and it is at least 5
  have hEs_card : Es.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro p hp q hq
    by_contra hne
    have hpp : p.Prime := ((hmemE p).mp hp).1
    have hqp : q.Prime := ((hmemE q).mp hq).1
    have hpd : p ∣ n := ((hmemE p).mp hp).2.1
    have hqd : q ∣ n := ((hmemE q).mp hq).2.1
    have hzp : z < p := ((hmemE p).mp hp).2.2
    have hzq : z < q := ((hmemE q).mp hq).2.2
    have hcop : p.Coprime q := (Nat.coprime_primes hpp hqp).mpr hne
    have hpqdvd : p * q ∣ n := hcop.mul_dvd_of_dvd_of_dvd hpd hqd
    have hpqle : p * q ≤ n := Nat.le_of_dvd (by omega) hpqdvd
    have hpq_ge : (z + 1) ^ 2 ≤ p * q := by
      rw [pow_two]
      apply Nat.mul_le_mul <;> omega
    omega
  have hE_ge : (4/5:ℝ) ≤ E := by
    rw [hE]
    have hfac : ∀ p ∈ Es, (4/5:ℝ) ≤ (1 - (p:ℝ)⁻¹) := by
      intro p hp
      have hpp : p.Prime := ((hmemE p).mp hp).1
      have hzp : z < p := ((hmemE p).mp hp).2.2
      have hne2 : p ≠ 2 := by omega
      have hodd : p % 2 = 1 := hpp.eq_two_or_odd.resolve_left hne2
      have hp5 : 5 ≤ p := by omega
      have hp5r : (5:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp5
      have hinv : (p:ℝ)⁻¹ ≤ 1/5 := by
        have h5 : ((5:ℝ))⁻¹ = 1/5 := by norm_num
        rw [← h5]
        exact (inv_le_inv₀ (by linarith : (0:ℝ) < (p:ℝ)) (by norm_num : (0:ℝ) < 5)).mpr hp5r
      linarith
    have hc : Es.card = 0 ∨ Es.card = 1 := by omega
    rcases hc with h0 | h1
    · rw [Finset.card_eq_zero.mp h0, Finset.prod_empty]
      norm_num
    · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
      rw [hp, Finset.prod_singleton]
      exact hfac p (by rw [hp]; exact Finset.mem_singleton_self p)
  -- the totient factorisation `φ(n)/n = A · E`
  have hphi : ((n.totient:ℝ)/(n:ℝ)) = A * E := by
    have htot : ((n.totient:ℝ)/(n:ℝ)) = ∏ p ∈ n.primeFactors, (1 - (p:ℝ)⁻¹) := by
      have hcast : (n.totient:ℝ) * (∏ p ∈ n.primeFactors, (p:ℝ))
          = (n:ℝ) * (∏ p ∈ n.primeFactors, ((p:ℝ) - 1)) := by
        have hnat := Nat.totient_mul_prod_primeFactors n
        have h1 := congrArg (fun m : ℕ => (m:ℝ)) hnat
        push_cast at h1
        have hprod : (∏ p ∈ n.primeFactors, (((p - 1 : ℕ)) : ℝ))
            = ∏ p ∈ n.primeFactors, ((p:ℝ) - 1) := by
          apply Finset.prod_congr rfl
          intro p hp
          rw [Nat.cast_sub (Nat.Prime.one_le (Nat.prime_of_mem_primeFactors hp)), Nat.cast_one]
        rw [hprod] at h1
        exact h1
      have hn0' : (n:ℝ) ≠ 0 := by positivity
      have hPne : (∏ p ∈ n.primeFactors, (p:ℝ)) ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro p hp
        have hpos : (0:ℝ) < (p:ℝ) := by
          have := (Nat.prime_of_mem_primeFactors hp).pos
          exact_mod_cast this
        linarith
      have hQP : ∏ p ∈ n.primeFactors, (1 - (p:ℝ)⁻¹)
          = (∏ p ∈ n.primeFactors, ((p:ℝ) - 1)) / (∏ p ∈ n.primeFactors, (p:ℝ)) := by
        have hfac : ∀ p ∈ n.primeFactors, (1 - (p:ℝ)⁻¹) = ((p:ℝ) - 1) / (p:ℝ) := by
          intro p hp
          have hpos : (0:ℝ) < (p:ℝ) := by
            have := (Nat.prime_of_mem_primeFactors hp).pos
            exact_mod_cast this
          have hp0' : (p:ℝ) ≠ 0 := ne_of_gt hpos
          field_simp
        rw [Finset.prod_congr rfl hfac, Finset.prod_div_distrib]
      rw [hQP, div_eq_div_iff hn0' hPne]
      simpa [mul_comm] using hcast
    rw [htot, hA, hE, hEs]
    have hprod := Finset.prod_filter_mul_prod_filter_not (s := n.primeFactors)
      (p := fun p => p ≤ z) (f := fun p => (1 - (p:ℝ)⁻¹))
    have hnotle : n.primeFactors.filter (fun p => ¬ p ≤ z)
        = n.primeFactors.filter (fun p => z < p) := by
      apply Finset.filter_congr
      intro p _
      exact Nat.not_le
    rw [← hprod, hnotle]
    have hSz_eq : n.primeFactors.filter (fun p => p ≤ z) = Sz := by
      ext p
      rw [Finset.mem_filter, hmemS]
      constructor
      · rintro ⟨hp, hpz⟩
        obtain ⟨hpp, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
        exact ⟨hpp, hdvd, hpz⟩
      · rintro ⟨hpp, hdvd, hpz⟩
        exact ⟨Nat.mem_primeFactors.mpr ⟨hpp, hdvd, hn0⟩, hpz⟩
    rw [hSz_eq]
  -- `A ≥ 0`
  have hA0 : 0 ≤ A := by
    rw [hA]
    apply Finset.prod_nonneg
    intro p hp
    have hpp : p.Prime := ((hmemS p).mp hp).1
    have hp1 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
    have hinv : (p:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hpp.one_le)
    linarith
  -- assembly
  have hMz : (∏ p ∈ Pz, (1 - (p:ℝ)⁻¹)) = A * B := by
    rw [hPsplit, Finset.prod_union hdisj, hA, hB]
  have hcore : (2/3:ℝ) * A^2 * B^2 ≤ A * E * Tp := by
    have h1 : (2/3:ℝ) * A^2 * B^2 ≤ (4/3) * A^2 * Tp := by
      have h := mul_le_mul_of_nonneg_left hB2 (by positivity : (0:ℝ) ≤ (2/3) * A^2)
      nlinarith [h]
    have h2 : (4/3:ℝ) * A^2 * Tp ≤ (2/3) * A * Tp := by
      have hAA : A^2 ≤ A * (1/2) := by nlinarith [hA0, hA2]
      have h := mul_le_mul_of_nonneg_right hAA hTp_nonneg
      nlinarith [h]
    have h3 : (2/3:ℝ) * A * Tp ≤ A * E * Tp := by
      have hAT : 0 ≤ A * Tp := mul_nonneg hA0 hTp_nonneg
      have h := mul_le_mul_of_nonneg_right hE_ge hAT
      nlinarith [h]
    linarith
  have hmain : (2/3:ℝ) * (∏ p ∈ Pz, (1 - (p:ℝ)⁻¹))^2
      ≤ ((n.totient:ℝ)/(n:ℝ)) * (∏ p ∈ Tz, (1 - 2/(p:ℝ))) := by
    rw [hMz, hphi]
    calc (2/3:ℝ) * (A * B)^2 = (2/3:ℝ) * A^2 * B^2 := by ring
      _ ≤ A * E * Tp := hcore
      _ = (A * E) * Tp := by ring
  calc (2/3:ℝ) * (Iz.card:ℝ) * (∏ p ∈ Pz, (1 - (p:ℝ)⁻¹))^2
      = (Iz.card:ℝ) * ((2/3:ℝ) * (∏ p ∈ Pz, (1 - (p:ℝ)⁻¹))^2) := by ring
    _ ≤ (Iz.card:ℝ) * (((n.totient:ℝ)/(n:ℝ)) * (∏ p ∈ Tz, (1 - 2/(p:ℝ)))) :=
        mul_le_mul_of_nonneg_left hmain hIpos.le
    _ = (Iz.card:ℝ) * (n.totient:ℝ) / (n:ℝ) * (∏ p ∈ Tz, (1 - 2/(p:ℝ))) := by ring

end PEqualNP.Outside


/-! ## Platform module-name alias (the live guard requires the theorem named `<module>`) -/

/- PREPUB frozen statement `L-goldbach-farey-sieve-terminal-floor`, under its platform
module name. -/
set_option maxHeartbeats 1000000 in
theorem Conjectures.Goldbach.FareySieveTerminalFloor :
    let I := fun n : ℕ => Finset.Icc ((n+2)/3) ((2*n)/3);
    let P := fun z : ℕ => (Finset.Icc 2 z).filter Nat.Prime;
    let M := fun z : ℕ => ∏ p ∈ P z, (1-(p:ℝ)⁻¹);
    let V := fun n z : ℕ => ((I n).card:ℝ)*(n.totient:ℝ)/n * ∏ p ∈ (P z).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ));
    ∀ n : ℕ, 12 ≤ n → Even n → (2/3:ℝ)*((I n).card:ℝ)*(M (Nat.sqrt n))^2 ≤ V n (Nat.sqrt n) :=
  PEqualNP.Outside.L_goldbach_farey_sieve_terminal_floor

namespace FareyBrun
open Finset Real Filter
open scoped BigOperators Topology
noncomputable section

theorem divisor_card (n : ℕ) (hn : 0<n) : n.divisors.card ≤ 2*n.sqrt := by
  let s := Icc 1 n.sqrt
  have hsub : n.divisors ⊆ s ∪ s.image (fun i => n/i) := by
    intro d hd
    have hpos := Nat.pos_of_mem_divisors hd
    have hdiv := (Nat.mem_divisors.mp hd).1
    have he := Nat.div_mul_cancel hdiv
    by_cases hs : d ≤ n.sqrt
    · exact mem_union_left _ (mem_Icc.mpr ⟨hpos,hs⟩)
    · apply mem_union_right
      apply mem_image.mpr
      refine ⟨n/d, mem_Icc.mpr ⟨?_,?_⟩, ?_⟩
      · exact (Nat.one_le_div_iff hpos).mpr (Nat.le_of_dvd hn hdiv)
      · apply Nat.le_sqrt.mpr
        have hle : n/d ≤ d := by
          by_contra! h
          have hbig := Nat.sqrt_lt.mp (lt_of_not_ge hs)
          nlinarith
        nlinarith [Nat.mul_le_mul_left (n/d) hle]
      · exact Nat.div_div_self hdiv hn.ne'
  have h := (card_le_card hsub).trans (card_union_le _ _)
  exact h.trans (by have hh := card_image_le (s:=s) (f:=fun i => n/i)
                    have hcard : s.card=n.sqrt := by simp [s]
                    omega)

theorem log_tail_budget {n : ℕ} (hn : 0<n) (s : Finset ℕ) (L : ℝ)
    (hs : ∀ p ∈ s, p.Prime ∧ p≤n ∧ L ≤ Real.log p) :
    L * (∑ p ∈ s, 2/(p:ℝ)) ≤ 4*Real.log n := by
  calc _ ≤ 2 * ∑ p ∈ s, Real.log p / p := by
          rw [mul_sum,mul_sum]
          apply sum_le_sum
          intro p hp
          have h := (hs p hp).2.2
          rw [show L*(2/(p:ℝ))=(2*L)/p by ring,
            show 2*(Real.log p/p)=(2*Real.log p)/p by ring]
          exact div_le_div_of_nonneg_right (by linarith) (by positivity)
       _ ≤ _ := by linarith [log_prime_budget n hn s (fun p hp => ⟨(hs p hp).1,(hs p hp).2.1⟩)]

theorem prime_mono {z y : ℕ} (h : z≤y) : primes z ⊆ primes y := by
  intro p hp
  obtain ⟨hI,hp'⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hI).1,(mem_Icc.mp hI).2.trans h⟩,hp'⟩

theorem good_mono (n : ℕ) {z y : ℕ} (h : z≤y) : good n z ⊆ good n y :=
  fun _ hp => mem_filter.mpr ⟨prime_mono h (mem_filter.mp hp).1,(mem_filter.mp hp).2⟩

def cut (n U : ℕ) := ⌊(n:ℝ)^((1:ℝ)/U)⌋₊

theorem cut_le_sqrt (n U : ℕ) (hn : 1≤n) (hU : 2≤U) : cut n U ≤ n.sqrt := by
  rw [←Real.nat_floor_real_sqrt_eq_nat_sqrt,Real.sqrt_eq_rpow]
  apply Nat.floor_mono
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
    (one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hU))

theorem good_odd {n z p : ℕ} (hn : Even n) (hp : p ∈ good n z) : 3≤p := by
  have h2 := (mem_filter.mp (mem_filter.mp hp).1).2.two_le
  have hc := (mem_filter.mp hp).2
  have hd := even_iff_two_dvd.mp hn
  by_contra! h
  obtain rfl : p=2 := by omega
  exact hc hd

theorem mainTerm_nonneg (n z : ℕ) : 0 ≤ mainTerm n z := by
  unfold mainTerm scale
  apply mul_nonneg (by positivity)
  apply prod_nonneg
  intro p hp
  have h2 : 2≤p := (mem_filter.mp (mem_filter.mp hp).1).2.two_le
  have hpos : (0:ℝ)<p := by exact_mod_cast (by omega : 0<p)
  exact sub_nonneg.mpr ((div_le_one hpos).mpr (by exact_mod_cast h2))

theorem terminal_ratio (n U : ℕ) (hn : 2≤n) (heven : Even n) (hU : 2≤U) :
    Real.exp (-12*(U:ℝ)) * mainTerm n (cut n U) ≤ mainTerm n n.sqrt := by
  let S := good n n.sqrt \ good n (cut n U)
  have hlog := Real.log_pos (by exact_mod_cast (by omega : 1<n) : (1:ℝ)<n)
  have hUp : (0:ℝ)<U := by exact_mod_cast (by omega : 0<U)
  have htail := log_tail_budget (by omega : 0<n) S (Real.log n/U) (by
    intro p hp
    obtain ⟨hy,hz⟩ := mem_sdiff.mp hp
    obtain ⟨hpr,hcop⟩ := mem_filter.mp hy
    obtain ⟨hI,hprime⟩ := mem_filter.mp hpr
    have hl : cut n U < p := by
      by_contra! hf
      exact hz (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hprime.two_le,hf⟩,hprime⟩,hcop⟩)
    have hp' : (n:ℝ)^(1/(U:ℝ)) < p := (Nat.floor_lt (by positivity)).mp hl
    have hlog' := Real.log_le_log (Real.rpow_pos_of_pos (by positivity : (0:ℝ)<n) _) hp'.le
    rw [Real.log_rpow (by positivity)] at hlog'
    exact ⟨hprime,(mem_Icc.mp hI).2.trans (Nat.sqrt_le_self _),by
      simpa [div_eq_mul_inv,mul_comm] using hlog'⟩)
  have hsum : (∑ p ∈ S, 2/(p:ℝ)) ≤ 4*U := by
    field_simp [hUp.ne'] at htail
    nlinarith [htail]
  have hprod := euler_density_lower S (fun p hp => good_odd heven (mem_sdiff.mp hp).1)
  have hh : Real.exp (-12*(U:ℝ)) ≤ ∏ p ∈ S, (1-2/(p:ℝ)) :=
    (Real.exp_le_exp.mpr (by linarith)).trans hprod
  apply (mul_le_mul_of_nonneg_right hh (mainTerm_nonneg _ _)).trans
  apply le_of_eq
  unfold mainTerm
  dsimp only [S]
  rw [mul_left_comm, prod_sdiff (good_mono n (cut_le_sqrt n U (by omega) hU))]
end
end FareyBrun

namespace FareyBrun
open Finset Real Filter
open scoped BigOperators Topology
noncomputable section

/-- A fixed, very weak polynomial floor suffices to absorb the integer rounding errors. -/
theorem mertens_weak_floor : ∃ c : ℝ, 0<c ∧ ∀ n y : ℕ, 2≤n → y≤n →
    c * (n:ℝ)^(-(1/16):ℝ) ≤ ∏ p ∈ primes y, (1-(p:ℝ)⁻¹) := by
  obtain ⟨A,hA⟩ := exists_nat_gt (Real.exp 256)
  refine ⟨(1/2:ℝ)^A,by positivity,?_⟩
  intro n y hn hy
  let S := (primes y).filter (fun p => p≤A)
  let T := primes y \ S
  have hsub : S ⊆ primes y := filter_subset _ _
  have hcard : S.card ≤ A := by
    have hs : S ⊆ Icc 1 A := by
      intro p hp
      obtain ⟨h,hpA⟩ := mem_filter.mp hp
      exact mem_Icc.mpr ⟨(mem_filter.mp h).2.one_le,hpA⟩
    simpa using card_le_card hs
  have hsmall : (1/2:ℝ)^A ≤ ∏ p ∈ S, (1-(p:ℝ)⁻¹) := by
    calc _ ≤ (1/2:ℝ)^S.card := pow_le_pow_of_le_one (by norm_num) (by norm_num) hcard
         _ = ∏ _p ∈ S, (1/2:ℝ) := by simp
         _ ≤ _ := by
           apply fareyProdLe (fun _ _ => by norm_num)
           intro p hp
           have h2 : (2:ℝ) ≤ p := by exact_mod_cast (mem_filter.mp (hsub hp)).2.two_le
           have h := one_div_le_one_div_of_le (by norm_num : 0<(2:ℝ)) h2
           rw [one_div] at h
           linarith
  have hlarge (p : ℕ) (hp : p ∈ T) : p.Prime ∧ p≤n ∧ (256:ℝ) ≤ Real.log p := by
    obtain ⟨hy',hS⟩ := mem_sdiff.mp hp
    have hAp : A<p := by by_contra! h; exact hS (mem_filter.mpr ⟨hy',h⟩)
    have hexp : Real.exp 256 ≤ (p:ℝ) := hA.le.trans (by exact_mod_cast hAp.le)
    have hlog := Real.log_le_log (Real.exp_pos _) hexp
    exact ⟨(mem_filter.mp hy').2,(mem_Icc.mp (mem_filter.mp hy').1).2.trans hy,by simpa using hlog⟩
  have hmass := log_tail_budget (by omega : 0<n) T 256 hlarge
  have hnlog : 0 ≤ log (n:ℝ) := log_nonneg (by exact_mod_cast (by omega : 1≤n))
  have h3 (p : ℕ) (hp : p ∈ T) : 3≤p := by
    have hpr := (hlarge p hp).1
    have hlog := (hlarge p hp).2.2
    have h2 := hpr.two_le
    by_contra! h
    obtain rfl : p=2 := by omega
    push_cast at hlog
    linarith [Real.log_two_lt_d9]
  have hbig : (n:ℝ)^(-(1/16):ℝ) ≤ ∏ p ∈ T, (1-(p:ℝ)⁻¹) := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast (by omega : 0<n))]
    apply le_trans _ ((euler_density_lower T h3).trans ?_)
    · apply Real.exp_le_exp.mpr
      linarith
    · apply fareyProdLe
      · intro p hp
        have h2 : (2:ℝ) ≤ p := by exact_mod_cast (hlarge p hp).1.two_le
        exact sub_nonneg.mpr ((div_le_one (by linarith : (0:ℝ)<p)).mpr h2)
      · intro p hp
        have h0 : 0 ≤ (p:ℝ)⁻¹ := by positivity
        rw [div_eq_mul_inv]
        linarith
  have hh := mul_le_mul hbig hsmall (by positivity : 0≤(1/2:ℝ)^A)
    (by exact (Real.rpow_nonneg (by positivity) _).trans hbig)
  rw [mul_comm ((n:ℝ)^(-(1/16):ℝ))] at hh
  change _ ≤ (∏ p ∈ primes y \ S, (1-(p:ℝ)⁻¹)) * ∏ p ∈ S, (1-(p:ℝ)⁻¹) at hh
  rwa [prod_sdiff hsub] at hh

theorem terminal_floor_power : ∃ c : ℝ, 0<c ∧ ∀ n : ℕ, 64≤n → Even n →
    c * (n:ℝ)^(7/8:ℝ) ≤ mainTerm n n.sqrt := by
  obtain ⟨c,hc,h⟩ := mertens_weak_floor
  refine ⟨c^2/6,by positivity,?_⟩
  intro n hn heven
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hg := h n n.sqrt (by omega) (Nat.sqrt_le_self _)
  have hs := pow_le_pow_left₀ (by positivity : 0≤c*(n:ℝ)^(-(1/16):ℝ)) hg 2
  have hcard : n ≤ 4*(window n).card := by
    simp only [window,Nat.card_Icc]
    omega
  have hcard' : (n:ℝ) ≤ 4*((window n).card:ℝ) := by exact_mod_cast hcard
  have hfloor := Conjectures.Goldbach.FareySieveTerminalFloor n (by omega) heven
  change (2/3:ℝ)*(window n).card*(∏ p ∈ primes n.sqrt, (1-(p:ℝ)⁻¹))^2 ≤ mainTerm n n.sqrt at hfloor
  apply le_trans _ hfloor
  have hh := mul_le_mul (show (n:ℝ)/6 ≤ 2/3*((window n).card:ℝ) by linarith)
    hs (sq_nonneg _) (by positivity)
  apply le_trans _ hh
  apply le_of_eq
  rw [mul_pow,←Real.rpow_mul_natCast hn0.le]
  have hhpow : (n:ℝ) * (n:ℝ)^((-(1/16):ℝ) * (2:ℕ)) = (n:ℝ)^(7/8:ℝ) := by
    rw [mul_comm,← Real.rpow_add_one hn0.ne']
    norm_num
  linear_combination -(c^2/6)*hhpow
end
end FareyBrun

namespace FareyBrun
open Finset Real ErdosStraus.BrunHooley
noncomputable section
open scoped Classical

/-- All hypotheses about intersections and truncations in the finite block sieve
are discharged here for the actual full numerator window. -/
theorem farey_window_lower (n z K : ℕ) (hn : 64≤n) (heven : Even n) (hz : 2≤z) :
    mainTerm n z * (1 - tiltError K * Real.exp (tiltError K)) -
      (1+2*(blockCount z:ℝ)) * (((z^(8*(K+2)):ℕ):ℝ)^2 * n.divisors.card) ≤ (sift n z:ℝ) := by
  let m := blockCount z
  let P := fun j : Fin m => blocks n z j.val
  let r := fun j : Fin m => rank K j.val
  let w := fun p : ℕ => 2/(p:ℝ)
  let W := z^(8*(K+2))
  have hdisj : Pairwise (fun j k => Disjoint (P j) (P k)) := block_disjoint n z hz
  have hcover : univ.biUnion P = good n z := block_cover n z hz
  have hP (j : Fin m) : P j ⊆ good n z := fun _ hp => (mem_filter.mp hp).1
  have hw (j : Fin m) (p : ℕ) (hp : p ∈ P j) : 0 ≤ w p ∧ w p < 1 := by
    have h3 : 3≤p := by
      have hpr := blocks_prime n z j.val p hp
      have h2 := hpr.two_le
      have hcop := (mem_filter.mp (hP j hp)).2
      have htwo := even_iff_two_dvd.mp heven
      by_contra! h
      obtain rfl : p=2 := by omega
      exact hcop htwo
    dsimp [w]
    have h2 : (2:ℝ)<p := by exact_mod_cast h3
    exact ⟨by positivity,(div_lt_one (by positivity)).mpr h2⟩
  have ht := rank_tail K P w (fun j => block_mass n z j.val hz)
    (fun j p hp => (hw j p hp).1) (fun j => block_euler n z j.val heven hz)
  have hround (k : Fin m → ℕ) (hk : ∀ j, k j≤2*r j+1) :=
    window_round hn P hP hdisj k W (fun f hf => by
      have hreal := rank_support K P hdisj (by exact_mod_cast (by omega : 1≤z) : (1:ℝ)≤z)
        (fun j p hp => (mem_filter.mp hp).2.2) k hk hf
      exact_mod_cast hreal)
  have hmain := finite_block_lower (mask n) P (fun p u => p ∣ u*(n-u)) r w
    (scale n) ((W:ℝ)^2*n.divisors.card) (tiltError K)
    (by unfold scale; positivity) hw ht hround
  have hV : (∏ j, ∏ p ∈ P j, (1-w p)) = ∏ p ∈ good n z, (1-w p) := by
    rw [←hcover,prod_biUnion]
    exact hdisj.set_pairwise _
  rw [hV,Fintype.card_fin] at hmain
  rw [←sift_blocks n z hn P hcover]
  simpa only [mainTerm,←mul_assoc,m,r,w,W] using hmain
end
end FareyBrun

namespace FareyBrun
open Finset Real Filter
open scoped Topology BigOperators
noncomputable section

theorem tilt_eventually : ∀ᶠ U : ℕ in atTop,
    tiltError (U/1024) * Real.exp (tiltError (U/1024)) ≤ Real.exp (-12*(U:ℝ))/16 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (24 + 8 * Real.exp 65536 + 131072 + Real.log 16 + 1)
  filter_upwards [eventually_ge_atTop N] with U hU
  have hlarge : 24 + 8 * Real.exp 65536 + 131072 + Real.log 16 + 1 ≤ (U:ℝ) :=
    hN.le.trans (by exact_mod_cast hU)
  have hfloor : (U:ℝ) < 1024*((U/1024:ℕ)+1:ℝ) := by
    exact_mod_cast (by omega : U<1024*(U/1024+1))
  let b : ℝ := 24 + 8 * Real.exp 65536 - 65536 * (2*(U/1024):ℕ)
  have hb : b+1 ≤ -12*(U:ℝ) - Real.log 16 := by dsimp [b]; push_cast; linarith
  have hb0 : b ≤ 0 := by linarith [Real.log_nonneg (by norm_num : (1:ℝ)≤16),Nat.cast_nonneg (α:=ℝ) U]
  have ht : tiltError (U/1024) ≤ 1 := Real.exp_le_one_iff.mpr hb0
  change Real.exp b * Real.exp (tiltError (U/1024)) ≤ _
  rw [←Real.exp_add,←Real.exp_log (by norm_num : (0:ℝ)<16),←Real.exp_sub]
  apply Real.exp_le_exp.mpr
  linarith

theorem count_eventually :
    ∀ᶠ n : ℕ in atTop, ∀ z : ℕ, 2≤z → z≤n → 1+2*(blockCount z:ℝ) ≤ (n:ℝ)^(1/8:ℝ) := by
  have h2 := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hl := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/8)).bound
    (show 0 < Real.log 2 / 4 by positivity)
  have hp := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/8)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 10
  filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually hl,hp,eventually_ge_atTop (2:ℕ)]
    with n hlog hpow hn
  intro z hz hzn
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1≤n)
  have hz' : (1:ℝ) ≤ z := by exact_mod_cast (by omega : 1≤z)
  have hlogz := Real.log_le_log (zero_lt_one.trans_le hz') (by exact_mod_cast hzn : (z:ℝ)≤n)
  change ‖Real.log (n:ℝ)‖ ≤ _ * ‖(n:ℝ)^(1/8:ℝ)‖ at hlog
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hn'),Real.norm_eq_abs,abs_of_nonneg (by positivity)] at hlog
  change 10 ≤ (n:ℝ)^(1/8:ℝ) at hpow
  have hc := Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg hz') h2.le)
  have hd : Real.log z / Real.log 2 ≤ (n:ℝ)^(1/8:ℝ)/4 := (div_le_iff₀ h2).mpr (by linarith)
  unfold blockCount
  push_cast
  linarith

theorem support_cut {n U : ℕ} (hn : 1≤n) (hU : 4096≤U) :
    ((cut n U ^ (8*(U/1024+2)):ℕ):ℝ) ≤ (n:ℝ)^(1/16:ℝ) := by
  have hu' : (0:ℝ)<U := by exact_mod_cast (by omega : 0<U)
  have hdeg : 16*(8*(U/1024+2))≤U := by omega
  have hpow : (1/(U:ℝ)) * ((8*(U/1024+2):ℕ):ℝ) ≤ 1/16 := by
    have hh : (16:ℝ)*(8*((U/1024:ℕ)+2:ℝ))≤U := by exact_mod_cast hdeg
    push_cast
    field_simp [hu'.ne']
    linarith
  push_cast only [Nat.cast_pow]
  calc _ ≤ ((n:ℝ)^(1/(U:ℝ)))^(8*(U/1024+2)) := by
             apply pow_le_pow_left₀ (by positivity)
             exact Nat.floor_le (by positivity)
       _ = (n:ℝ)^((1/(U:ℝ))*((8*(U/1024+2):ℕ):ℝ)) := (Real.rpow_mul_natCast (by positivity) _ _).symm
       _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hpow

theorem rounding_eventually (U : ℕ) (hU : 4096≤U) :
    ∀ᶠ n : ℕ in atTop, 2≤cut n U ∧
    (1+2*(blockCount (cut n U):ℝ)) *
      (((cut n U ^ (8*(U/1024+2)):ℕ):ℝ)^2 * n.divisors.card) ≤ 2*(n:ℝ)^(3/4:ℝ) := by
  have hu : (0:ℝ)<U := by exact_mod_cast (by omega : 0<U)
  have hc := ((tendsto_rpow_atTop (by positivity : (0:ℝ)<1/U)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 2
  filter_upwards [count_eventually,hc,eventually_ge_atTop (2:ℕ)] with n hblocks hcut hn
  have hcut' : 2≤cut n U := Nat.le_floor (by exact hcut)
  refine ⟨hcut',?_⟩
  have hn' : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hW := support_cut (by omega : 1≤n) hU
  have hτ : (n.divisors.card:ℝ) ≤ 2*(n:ℝ)^(1/2:ℝ) := by
    have hh : (n.divisors.card:ℝ) ≤ 2*(n.sqrt:ℝ) := by exact_mod_cast divisor_card n (by omega)
    rw [←Real.sqrt_eq_rpow]
    exact hh.trans (mul_le_mul_of_nonneg_left Real.nat_sqrt_le_real_sqrt (by norm_num))
  have hM := hblocks _ hcut' ((cut_le_sqrt n U (by omega) (by omega)).trans (Nat.sqrt_le_self _))
  apply (mul_le_mul hM (mul_le_mul (pow_le_pow_left₀ (by positivity) hW 2) hτ
    (by positivity) (by positivity)) (by positivity) (by positivity)).trans
  apply le_of_eq
  rw [←Real.rpow_mul_natCast hn'.le]
  have hpow : (n:ℝ)^(1/8:ℝ)*((n:ℝ)^((1/16:ℝ)*(2:ℕ))*(n:ℝ)^(1/2:ℝ)) = (n:ℝ)^(3/4:ℝ) := by
    rw [←Real.rpow_add hn',←Real.rpow_add hn']
    norm_num
  linear_combination 2*hpow
end
end FareyBrun

namespace FareyBrun
open Filter Real Finset
open scoped Topology BigOperators
noncomputable section

theorem initial_sieve :
    ∃ U₀ : ℕ, 8≤U₀ ∧ ∀ U : ℕ, U₀≤U → ∃ N₀ : ℕ, 64≤N₀ ∧ ∀ n : ℕ, N₀≤n → Even n →
      mainTerm n (cut n U) - mainTerm n n.sqrt/8 ≤ (sift n (cut n U):ℝ) := by
  obtain ⟨C,hC,hterm⟩ := terminal_floor_power
  obtain ⟨U₁,hU₁⟩ := eventually_atTop.1 tilt_eventually
  refine ⟨max 4096 U₁,by omega,?_⟩
  intro U hU
  have hU4 : 4096≤U := le_trans (le_max_left ..) hU
  have htilt := hU₁ U (le_trans (le_max_right ..) hU)
  have hg := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/8)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (32/C)
  obtain ⟨N,hN⟩ := eventually_atTop.1 ((rounding_eventually U hU4).and hg)
  refine ⟨max 64 N,le_max_left ..,?_⟩
  intro n hn heven
  have hn64 : 64≤n := le_trans (le_max_left ..) hn
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  obtain ⟨⟨hcut,hround⟩,hpow⟩ := hN n ((le_max_right ..).trans hn)
  change 32/C ≤ (n:ℝ)^(1/8:ℝ) at hpow
  have hfloor := hterm n hn64 heven
  have hfac := (div_le_iff₀ hC).mp hpow
  have hrem : 2*(n:ℝ)^(3/4:ℝ) ≤ mainTerm n n.sqrt/16 := by
    have hp : (n:ℝ)^(3/4:ℝ)*(n:ℝ)^(1/8:ℝ) = (n:ℝ)^(7/8:ℝ) := by
      rw [←Real.rpow_add hn0]; norm_num
    have hh := mul_le_mul_of_nonneg_left hfac (show 0 ≤ (n:ℝ)^(3/4:ℝ) by positivity)
    rw [show (n:ℝ)^(3/4:ℝ)*((n:ℝ)^(1/8:ℝ)*C) = (n:ℝ)^(7/8:ℝ)*C by rw [←mul_assoc,hp]] at hh
    linarith
  have hcompare := terminal_ratio n U (by omega) heven (by omega)
  have htail := mul_le_mul_of_nonneg_right htilt (mainTerm_nonneg n (cut n U))
  have hl := farey_window_lower n (cut n U) (U/1024) hn64 heven hcut
  linarith only [hl,hround,hrem,hcompare,htail]
end
end FareyBrun

theorem Conjectures.Goldbach.FareyInitialSieveLower :
    let I := fun n : ℕ => Finset.Icc ((n+2)/3) ((2*n)/3); let P := fun z : ℕ => (Finset.Icc 2 z).filter Nat.Prime; let V := fun n z : ℕ => ((I n).card:ℝ)*(n.totient:ℝ)/n * ∏ p ∈ (P z).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ)); let S := fun n z : ℕ => ((I n).filter (fun u => u.Coprime n ∧ z < (u*(n-u)).minFac)).card; let Z₀ := fun n U : ℕ => ⌊(n:ℝ)^((1:ℝ)/(U:ℝ))⌋₊; let Z₂ := Nat.sqrt; ∃ U₀ : ℕ, 8 ≤ U₀ ∧ ∀ U : ℕ, U₀ ≤ U → ∃ N₀ : ℕ, 64 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n → Even n → V n (Z₀ n U) - V n (Z₂ n)/8 ≤ (S n (Z₀ n U):ℝ) := by
  exact FareyBrun.initial_sieve
