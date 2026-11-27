import Mathlib

namespace Conjectures.Goldbach.NormalizedShiftOptimalWindow_aux

noncomputable section

def ea (c : ℕ → ℝ) (α : ℝ) (j : ℕ) : ℝ := max (α - c j) 0

def Za (I : Finset ℕ) (c : ℕ → ℝ) (α : ℝ) : ℝ := ∑ j ∈ I, ea c α j

def wa (I : Finset ℕ) (c : ℕ → ℝ) (α : ℝ) (j : ℕ) : ℝ := ea c α j / Za I c α

def Pa (I : Finset ℕ) (c : ℕ → ℝ) (α : ℝ) : Finset ℕ := I.filter (fun j => 0 < wa I c α j)

def vv (c : ℕ → ℝ) (m : ℝ) (t : ℝ) (j : ℕ) : ℝ := max (1 - t * (c j - m)) 0

def zz (I : Finset ℕ) (c : ℕ → ℝ) (m : ℝ) (t : ℝ) : ℝ := ∑ k ∈ I, vv c m t k

def ww (I : Finset ℕ) (c : ℕ → ℝ) (m : ℝ) (t : ℝ) (j : ℕ) : ℝ := vv c m t j / zz I c m t

lemma pos_max_iff {x : ℝ} : 0 < max x 0 ↔ 0 < x := by
  constructor
  · intro h
    by_contra hx
    rw [max_eq_right (not_lt.mp hx)] at h
    exact lt_irrefl 0 h
  · intro h
    exact lt_of_lt_of_le h (le_max_left _ _)

variable {I P : Finset ℕ} {c : ℕ → ℝ} {α B m t : ℝ}

lemma ea_nonneg (j : ℕ) : 0 ≤ ea c α j := le_max_right _ _

lemma ea_pos_iff (j : ℕ) : 0 < ea c α j ↔ c j < α := by
  rw [ea, pos_max_iff, sub_pos]

lemma ea_eq_sub {j : ℕ} (hc : c j < α) : ea c α j = α - c j := by
  rw [ea, max_eq_left (le_of_lt (sub_pos.mpr hc))]

lemma ea_eq_zero {j : ℕ} (hc : ¬ (c j < α)) : ea c α j = 0 := by
  rw [ea, max_eq_right (sub_nonpos.mpr (le_of_not_gt hc))]

lemma Za_pos_of {j : ℕ} (hj : j ∈ I) (hc : c j < α) : 0 < Za I c α := by
  have h1 : 0 < ea c α j := (ea_pos_iff j).mpr hc
  exact lt_of_lt_of_le h1 (Finset.single_le_sum (fun i _ => ea_nonneg i) hj)

lemma wa_nonneg (hZ : 0 < Za I c α) (j : ℕ) : 0 ≤ wa I c α j :=
  div_nonneg (ea_nonneg j) (le_of_lt hZ)

lemma sum_wa (hZ : 0 < Za I c α) : ∑ j ∈ I, wa I c α j = 1 := by
  simp only [wa]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hZ)

lemma wa_pos_iff (hZ : 0 < Za I c α) (j : ℕ) : 0 < wa I c α j ↔ c j < α := by
  rw [wa, div_pos_iff_of_pos_right hZ, ea_pos_iff]

lemma mem_Pa (hZ : 0 < Za I c α) (j : ℕ) : j ∈ Pa I c α ↔ (j ∈ I ∧ c j < α) := by
  simp only [Pa, Finset.mem_filter, wa_pos_iff hZ]

lemma Pa_subset : Pa I c α ⊆ I := Finset.filter_subset _ _

lemma exists_pos_of_sum_pos {s : Finset ℕ} {f : ℕ → ℝ} (h : 0 < ∑ i ∈ s, f i) :
    ∃ i ∈ s, 0 < f i := by
  by_contra hc
  have h2 : ∀ i ∈ s, f i ≤ 0 := by
    intro i hi
    rcases lt_or_ge 0 (f i) with h3 | h3
    · exact absurd ⟨i, hi, h3⟩ hc
    · exact h3
  have h4 := Finset.sum_nonpos h2
  linarith

lemma Pa_nonempty (hZ : 0 < Za I c α) : (Pa I c α).Nonempty := by
  obtain ⟨j, hj, hpos⟩ := exists_pos_of_sum_pos hZ
  exact ⟨j, (mem_Pa hZ j).mpr ⟨hj, (ea_pos_iff j).mp hpos⟩⟩

lemma sum_eq_sum_sub {f g : ℕ → ℝ} (hP : P ⊆ I)
    (hf : ∀ j ∈ I, j ∉ P → f j = 0) (hg : ∀ j ∈ P, f j = g j) :
    ∑ j ∈ I, f j = ∑ j ∈ P, g j := by
  rw [← Finset.sum_subset hP hf]
  exact Finset.sum_congr rfl hg

lemma alpha_value (hZ : 0 < Za I c α) (hB : (∑ j ∈ I, (wa I c α j)^2) = B) :
    (∑ j ∈ I, wa I c α j * c j) =
      (∑ j ∈ Pa I c α, c j)/((Pa I c α).card:ℝ) -
        Real.sqrt ((B - 1/((Pa I c α).card:ℝ)) *
          (∑ j ∈ Pa I c α, (c j - (∑ j ∈ Pa I c α, c j)/((Pa I c α).card:ℝ))^2)) := by
  have hZ0 : Za I c α ≠ 0 := ne_of_gt hZ
  set P := Pa I c α with hP
  set n := (P.card : ℝ) with hn
  set μ := (∑ j ∈ P, c j) / n with hμ
  set S := ∑ j ∈ P, (c j - μ)^2 with hS
  set Q := ∑ j ∈ P, (α - c j)^2 with hQ
  have hPne : P.Nonempty := by rw [hP]; exact Pa_nonempty hZ
  have hPsub : P ⊆ I := by rw [hP]; exact Pa_subset
  have hmem : ∀ j, j ∈ P ↔ (j ∈ I ∧ c j < α) := by intro j; rw [hP]; exact mem_Pa hZ j
  have hnpos : 0 < n := by rw [hn]; exact Nat.cast_pos.mpr (Finset.card_pos.mpr hPne)
  have hn0 : n ≠ 0 := ne_of_gt hnpos
  have hμsum : n * μ = ∑ j ∈ P, c j := by rw [hμ]; exact mul_div_cancel₀ _ hn0
  have hconst : ∀ b : ℝ, ∑ j ∈ P, b = n * b := by
    intro b; rw [Finset.sum_const, nsmul_eq_mul, hn]
  have hzero : ∑ j ∈ P, (c j - μ) = 0 := by
    rw [Finset.sum_sub_distrib, hconst, ← hμsum, sub_self]
  have hZa : Za I c α = ∑ j ∈ P, (α - c j) :=
    sum_eq_sum_sub hPsub (fun j hj hnj => ea_eq_zero (fun h => hnj ((hmem j).mpr ⟨hj, h⟩)))
      (fun j hj => ea_eq_sub ((hmem j).mp hj).2)
  have hZa2 : Za I c α = n * (α - μ) := by
    rw [hZa, Finset.sum_sub_distrib, hconst, ← hμsum]
    ring
  have hQeq : Q = n * (α - μ)^2 + S := by
    have hpt : ∀ j, (α - c j)^2 = (α - μ)^2 - (2*(α - μ))*(c j - μ) + (c j - μ)^2 := by
      intro j; ring
    rw [hQ, Finset.sum_congr rfl (fun j (_ : j ∈ P) => hpt j), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, hconst, ← Finset.mul_sum, hzero, ← hS]
    ring
  have hsq : (Za I c α)^2 * (∑ j ∈ I, (wa I c α j)^2) = Q := by
    have h1 : ∀ j : ℕ, (Za I c α)^2 * (wa I c α j)^2 = (ea c α j)^2 := by
      intro j; simp only [wa, sq]; field_simp [hZ0]
    have h2 : ∑ j ∈ I, (ea c α j)^2 = Q := by
      rw [hQ]
      exact sum_eq_sum_sub hPsub
        (fun j hj hnj => by
          rw [ea_eq_zero (fun h => hnj ((hmem j).mpr ⟨hj, h⟩)), zero_pow (by norm_num)])
        (fun j hj => by rw [ea_eq_sub ((hmem j).mp hj).2])
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun j (_ : j ∈ I) => h1 j), h2]
  have hB' : (Za I c α)^2 * B = Q := by rw [← hB]; exact hsq
  have hSeq : S = (Za I c α)^2 * (B - 1/n) := by
    have h1 : (Za I c α)^2 * B = n * (α - μ)^2 + S := by rw [hB', hQeq]
    have h2 : (Za I c α)^2 = n^2 * (α - μ)^2 := by rw [hZa2]; ring
    have hA : n * S = (Za I c α)^2 * B * n - (Za I c α)^2 := by
      linear_combination (-n) * h1 + h2
    calc S = (n * S) / n := by field_simp [hn0] <;> ring
      _ = ((Za I c α)^2 * B * n - (Za I c α)^2) / n := by rw [hA]
      _ = (Za I c α)^2 * (B - 1/n) := by field_simp [hn0] <;> ring
  have hBge : 1/n ≤ B := by
    have hwaI : ∑ j ∈ I, wa I c α j = ∑ j ∈ P, wa I c α j :=
      sum_eq_sum_sub hPsub
        (fun j hj hnj => by
          rw [wa, ea_eq_zero (fun h => hnj ((hmem j).mpr ⟨hj, h⟩)), zero_div])
        (fun j _ => rfl)
    have hwa2 : ∑ j ∈ I, (wa I c α j)^2 = ∑ j ∈ P, (wa I c α j)^2 :=
      sum_eq_sum_sub hPsub
        (fun j hj hnj => by
          rw [wa, ea_eq_zero (fun h => hnj ((hmem j).mpr ⟨hj, h⟩)), zero_div,
            zero_pow (by norm_num)])
        (fun j _ => rfl)
    have hpt : ∀ j, (wa I c α j - 1/n)^2 = (wa I c α j)^2 - (2*(1/n))*(wa I c α j) + (1/n)^2 := by
      intro j; ring
    have hpos : 0 ≤ ∑ j ∈ P, (wa I c α j - 1/n)^2 :=
      Finset.sum_nonneg (fun j _ => sq_nonneg _)
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ P) => hpt j), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, hconst] at hpos
    rw [← hwaI, ← hwa2, hB, sum_wa hZ] at hpos
    have h1 : n * (1/n)^2 = 1/n := by field_simp [hn0] <;> ring
    rw [h1] at hpos
    linarith
  have hsqrt : Real.sqrt ((B - 1/n) * S) = S / Za I c α := by
    have h1 : (B - 1/n) * S = ((B - 1/n) * Za I c α)^2 := by rw [hSeq]; ring
    have h2 : 0 ≤ (B - 1/n) * Za I c α := mul_nonneg (by linarith) (le_of_lt hZ)
    rw [h1, Real.sqrt_sq h2, hSeq]
    field_simp [hZ0] <;> ring
  have hval : Za I c α * (∑ j ∈ I, wa I c α j * c j) = Za I c α * μ - S := by
    have hstep : Za I c α * (∑ j ∈ I, wa I c α j * c j) = ∑ j ∈ I, ea c α j * c j := by
      simp only [wa]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by field_simp [hZ0])
    have hstep2 : ∑ j ∈ I, ea c α j * c j = ∑ j ∈ P, (α - c j) * c j :=
      sum_eq_sum_sub hPsub
        (fun j hj hnj => by
          rw [ea_eq_zero (fun h => hnj ((hmem j).mpr ⟨hj, h⟩)), zero_mul])
        (fun j hj => by rw [ea_eq_sub ((hmem j).mp hj).2])
    have hstep3 : ∑ j ∈ P, (α - c j) * c j = α * (Za I c α) - Q := by
      have hpt : ∀ j, (α - c j) * c j = α * (α - c j) - (α - c j)^2 := by intro j; ring
      rw [hQ, Finset.sum_congr rfl (fun j (_ : j ∈ P) => hpt j), Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← hZa]
    rw [hstep, hstep2, hstep3, hQeq, hZa2]
    ring
  rw [hsqrt]
  calc (∑ j ∈ I, wa I c α j * c j) = (Za I c α * μ - S) / Za I c α := by
        rw [← hval]; field_simp [hZ0] <;> ring
    _ = μ - S / Za I c α := by field_simp [hZ0] <;> ring

lemma alpha_optimal (hZ : 0 < Za I c α) (u : ℕ → ℝ) (hu : ∀ j ∈ I, 0 ≤ u j)
    (hsum : ∑ j ∈ I, u j = 1) (hsq : ∑ j ∈ I, (u j)^2 ≤ B)
    (hB : (∑ j ∈ I, (wa I c α j)^2) = B) :
    ∑ j ∈ I, wa I c α j * c j ≤ ∑ j ∈ I, u j * c j := by
  have hZ0 : Za I c α ≠ 0 := ne_of_gt hZ
  have hpt1 : ∀ j ∈ I, u j * (α - c j) ≤ u j * ea c α j := fun j hj =>
    mul_le_mul_of_nonneg_left (le_max_left _ _) (hu j hj)
  have hpt2 : ∀ j : ℕ, Za I c α * (u j * wa I c α j) = u j * ea c α j := by
    intro j; simp only [wa]; field_simp [hZ0]
  have hpt3 : ∀ j : ℕ, Za I c α * (wa I c α j)^2 = wa I c α j * ea c α j := by
    intro j; simp only [wa, sq]; field_simp [hZ0]
  have hpt4 : ∀ j ∈ I, wa I c α j * ea c α j = wa I c α j * (α - c j) := by
    intro j _
    by_cases hc : c j < α
    · rw [ea_eq_sub hc]
    · rw [ea_eq_zero hc, wa, ea_eq_zero hc, zero_div, mul_zero, zero_mul]
  have hkey : ∑ j ∈ I, u j * wa I c α j ≤ ∑ j ∈ I, (wa I c α j)^2 := by
    have h1 : 0 ≤ ∑ j ∈ I, (u j - wa I c α j)^2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hpt : ∀ j, (u j - wa I c α j)^2
        = (u j)^2 - 2*(u j * wa I c α j) + (wa I c α j)^2 := by intro j; ring
    have h2 : ∑ j ∈ I, (u j - wa I c α j)^2
        = (∑ j ∈ I, (u j)^2) - 2*(∑ j ∈ I, u j * wa I c α j) + ∑ j ∈ I, (wa I c α j)^2 := by
      rw [Finset.sum_congr rfl (fun j (_ : j ∈ I) => hpt j), Finset.sum_add_distrib,
        Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [h2] at h1
    nlinarith [hsq, hB]
  have hS1 : ∑ j ∈ I, u j * (α - c j) ≤ ∑ j ∈ I, wa I c α j * (α - c j) := by
    calc ∑ j ∈ I, u j * (α - c j) ≤ ∑ j ∈ I, u j * ea c α j := Finset.sum_le_sum hpt1
      _ = Za I c α * ∑ j ∈ I, u j * wa I c α j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => (hpt2 j).symm)
      _ ≤ Za I c α * ∑ j ∈ I, (wa I c α j)^2 :=
          mul_le_mul_of_nonneg_left hkey (le_of_lt hZ)
      _ = ∑ j ∈ I, wa I c α j * ea c α j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => hpt3 j)
      _ = ∑ j ∈ I, wa I c α j * (α - c j) := Finset.sum_congr rfl hpt4
  have hcu : ∑ j ∈ I, u j * c j = α - ∑ j ∈ I, u j * (α - c j) := by
    have hpt : ∀ j, u j * c j = α * u j - u j * (α - c j) := by intro j; ring
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ I) => hpt j), Finset.sum_sub_distrib,
      ← Finset.mul_sum, hsum]
    ring
  have hcw : ∑ j ∈ I, wa I c α j * c j = α - ∑ j ∈ I, wa I c α j * (α - c j) := by
    have hpt : ∀ j, wa I c α j * c j = α * wa I c α j - wa I c α j * (α - c j) := by
      intro j; ring
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ I) => hpt j), Finset.sum_sub_distrib,
      ← Finset.mul_sum, sum_wa hZ]
    ring
  rw [hcw, hcu]
  linarith

lemma vv_nonneg (j : ℕ) : 0 ≤ vv c m t j := le_max_right _ _

lemma vv_at_min {j : ℕ} (h : c j = m) : vv c m t j = 1 := by
  rw [vv, h, sub_self, mul_zero, sub_zero, max_eq_left (by norm_num)]

lemma vv_zero (j : ℕ) : vv c m 0 j = 1 := by
  rw [vv, max_eq_left (by norm_num)]
  norm_num

lemma zz_pos {j : ℕ} (hj : j ∈ I) (h : c j = m) : 0 < zz I c m t := by
  have h1 : vv c m t j = 1 := vv_at_min h
  have h2 : vv c m t j ≤ zz I c m t :=
    Finset.single_le_sum (fun i _ => vv_nonneg i) hj
  rw [h1] at h2
  linarith

lemma ww_nonneg (hZ : 0 < zz I c m t) (j : ℕ) : 0 ≤ ww I c m t j :=
  div_nonneg (vv_nonneg j) (le_of_lt hZ)

lemma sum_ww (hZ : 0 < zz I c m t) : ∑ j ∈ I, ww I c m t j = 1 := by
  simp only [ww]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hZ)

lemma ww_eq_wa (ht : 0 < t) (hα : α = m + 1/t) (hZ : Za I c α ≠ 0) (j : ℕ) :
    ww I c m t j = wa I c α j := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hkey : ∀ x : ℝ, max (t * x) 0 = t * max x 0 := by
    intro x
    rcases lt_or_ge x 0 with h | h
    · rw [max_eq_right (le_of_lt h), mul_zero,
        max_eq_right (mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht) (le_of_lt h))]
    · rw [max_eq_left h, max_eq_left (mul_nonneg (le_of_lt ht) h)]
  have hrel : ∀ k : ℕ, 1 - t * (c k - m) = t * (α - c k) := by
    intro k; rw [hα]; field_simp [ht0] <;> ring
  have hvv : ∀ k : ℕ, vv c m t k = t * ea c α k := by
    intro k; rw [vv, ea, hrel k, hkey]
  have hzz : zz I c m t = t * Za I c α := by
    rw [zz, Za, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => hvv k)
  rw [ww, wa, hvv j, hzz]
  field_simp [ht0, hZ] <;> ring

lemma continuous_sum {f : ℝ → ℕ → ℝ} :
    ∀ (s : Finset ℕ), (∀ i ∈ s, Continuous (f · i)) → Continuous (fun x => ∑ i ∈ s, f x i) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simpa using (continuous_const : Continuous (fun _ : ℝ => (0:ℝ)))
  | @insert a s ha ih =>
      intro h
      simp only [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

lemma continuous_ww (hZ : ∀ s : ℝ, 0 < zz I c m s) (j : ℕ) :
    Continuous (fun s => ww I c m s j) := by
  have h1 : Continuous (fun s => vv c m s j) := by
    simp only [vv]; fun_prop
  have h2 : Continuous (fun s => zz I c m s) := by
    have h3 : ∀ k ∈ I, Continuous (fun s => vv c m s k) := by
      intro k _; simp only [vv]; fun_prop
    simp only [zz]; exact continuous_sum I h3
  exact h1.div h2 (fun s => ne_of_gt (hZ s))

lemma uniform_of_sq_le (I : Finset ℕ) (hcard : 0 < I.card) (u : ℕ → ℝ)
    (hsum : ∑ j ∈ I, u j = 1) (hsq : ∑ j ∈ I, (u j)^2 ≤ 1/(I.card:ℝ)) :
    ∀ j ∈ I, u j = 1/(I.card:ℝ) := by
  have hn0 : (I.card:ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hcard)
  have hconst : ∀ b : ℝ, ∑ j ∈ I, b = (I.card:ℝ) * b := by
    intro b; rw [Finset.sum_const, nsmul_eq_mul]
  have key : ∑ j ∈ I, (u j - 1/(I.card:ℝ))^2 = (∑ j ∈ I, (u j)^2) - 1/(I.card:ℝ) := by
    have hpt : ∀ j, (u j - 1/(I.card:ℝ))^2
        = (u j)^2 - (2*(1/(I.card:ℝ)))*(u j) + (1/(I.card:ℝ))^2 := by intro j; ring
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ I) => hpt j), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, hconst, hsum]
    have h1 : (I.card:ℝ) * (1/(I.card:ℝ))^2 = 1/(I.card:ℝ) := by
      field_simp [hn0] <;> ring
    rw [h1]; ring
  have hzero : ∑ j ∈ I, (u j - 1/(I.card:ℝ))^2 = 0 := by
    have h1 : 0 ≤ ∑ j ∈ I, (u j - 1/(I.card:ℝ))^2 :=
      Finset.sum_nonneg (fun j _ => sq_nonneg _)
    rw [key] at h1
    linarith
  intro j hj
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ I) => sq_nonneg (u i - 1/(I.card:ℝ)))).mp hzero j hj
  have h2 : u j - 1/(I.card:ℝ) ≤ 0 := by
    nlinarith [h1, sq_nonneg (u j - 1/(I.card:ℝ))]
  have h3 : 0 ≤ u j - 1/(I.card:ℝ) := by
    nlinarith [h1, sq_nonneg (u j - 1/(I.card:ℝ))]
  linarith

lemma main_aux (I : Finset ℕ) (c : ℕ → ℝ) (m B : ℝ)
    (hmin : ∃ j ∈ I, c j = m) (hge : ∀ j ∈ I, m ≤ c j) (hB : 1 ≤ B * (I.card:ℝ)) :
    ∃ t : ℝ, 0 ≤ t ∧ (∀ j ∈ I, 0 ≤ ww I c m t j) ∧ (∑ j ∈ I, ww I c m t j) = 1 ∧
      (∑ j ∈ I, (ww I c m t j)^2) ≤ B ∧
      ((∑ j ∈ I, (ww I c m t j)^2) = B ∨ ∀ j ∈ I, c j ≠ m → ww I c m t j = 0) ∧
      (let P := I.filter (fun j => 0 < ww I c m t j)
       let μ := (∑ j ∈ P, c j)/(P.card:ℝ)
       P.Nonempty ∧ (∀ i ∈ P, ∀ j ∈ I, c j ≤ c i → j ∈ P) ∧
         (∑ j ∈ I, ww I c m t j * c j) =
           μ - Real.sqrt ((B - 1/(P.card:ℝ)) * (∑ j ∈ P, (c j-μ)^2))) ∧
      ∀ u : ℕ → ℝ, (∀ j ∈ I, 0 ≤ u j) → (∑ j ∈ I, u j) = 1 →
        (∑ j ∈ I, (u j)^2) ≤ B → (∑ j ∈ I, ww I c m t j * c j) ≤ ∑ j ∈ I, u j * c j := by
  obtain ⟨j₀, hj₀I, hj₀m⟩ := hmin
  have hIne : I.Nonempty := ⟨j₀, hj₀I⟩
  have hcard : 0 < I.card := Finset.card_pos.mpr hIne
  have hcardR : 0 < (I.card:ℝ) := Nat.cast_pos.mpr hcard
  have hBge : 1/(I.card:ℝ) ≤ B := by
    rw [div_le_iff₀ hcardR]
    exact hB
  have hZall : ∀ s : ℝ, 0 < zz I c m s := fun s => zz_pos hj₀I hj₀m
  have hzz0 : zz I c m 0 = (I.card:ℝ) := by
    have h1 : ∑ k ∈ I, vv c m 0 k = ∑ k ∈ I, (1:ℝ) :=
      Finset.sum_congr rfl (fun k _ => vv_zero k)
    rw [zz, h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hww0 : ∀ j ∈ I, ww I c m 0 j = 1/(I.card:ℝ) := by
    intro j _
    rw [ww, vv_zero, hzz0]
  have hsq0 : ∑ j ∈ I, (ww I c m 0 j)^2 = 1/(I.card:ℝ) := by
    have h1 : ∑ j ∈ I, (ww I c m 0 j)^2 = ∑ j ∈ I, (1/(I.card:ℝ))^2 :=
      Finset.sum_congr rfl (fun j (hj : j ∈ I) => by rw [hww0 j hj])
    rw [h1, Finset.sum_const, nsmul_eq_mul]
    field_simp [ne_of_gt hcardR] <;> ring
  by_cases hBcard : B = 1/(I.card:ℝ)
  · refine ⟨0, le_refl 0, fun j _ => ww_nonneg (hZall 0) j, sum_ww (hZall 0), ?_, ?_, ?_, ?_⟩
    · rw [hsq0, hBcard]
    · left; rw [hsq0, hBcard]
    · have hPe : I.filter (fun j => 0 < ww I c m 0 j) = I :=
        Finset.filter_eq_self.mpr (fun j hj => by
          rw [hww0 j hj]; exact div_pos one_pos hcardR)
      dsimp only
      rw [hPe]
      refine ⟨hIne, fun i _ j hj _ => hj, ?_⟩
      rw [hBcard, sub_self, zero_mul, Real.sqrt_zero, sub_zero]
      have h1 : ∑ j ∈ I, ww I c m 0 j * c j = ∑ j ∈ I, (1/(I.card:ℝ)) * c j :=
        Finset.sum_congr rfl (fun j (hj : j ∈ I) => by rw [hww0 j hj])
      rw [h1, ← Finset.mul_sum]
      ring
    · intro u hu hsum hsq
      have hu1 : ∀ j ∈ I, u j = 1/(I.card:ℝ) := by
        refine uniform_of_sq_le I hcard u hsum ?_
        rw [← hBcard]
        exact hsq
      have h1 : ∑ j ∈ I, u j * c j = ∑ j ∈ I, ww I c m 0 j * c j :=
        Finset.sum_congr rfl (fun j (hj : j ∈ I) => by rw [hu1 j hj, hww0 j hj])
      exact le_of_eq h1.symm
  · have hlt : 1/(I.card:ℝ) < B := lt_of_le_of_ne hBge (Ne.symm hBcard)
    by_cases hex : ∃ t₀ : ℝ, 0 ≤ t₀ ∧ B < ∑ j ∈ I, (ww I c m t₀ j)^2
    · obtain ⟨t₀, ht₀, hFt₀⟩ := hex
      have hFcont : Continuous (fun s => ∑ j ∈ I, (ww I c m s j)^2) := by
        have h1 : ∀ j ∈ I, Continuous (fun s => (ww I c m s j)^2) := by
          intro j _
          have hj := continuous_ww hZall j
          have heq : (fun s => ww I c m s j * ww I c m s j) = fun s => (ww I c m s j)^2 := by
            funext s; ring
          rw [← heq]
          exact hj.mul hj
        exact continuous_sum I h1
      have hFa : (∑ j ∈ I, (ww I c m 0 j)^2) ≤ B := by rw [hsq0]; exact le_of_lt hlt
      have hFb : B ≤ ∑ j ∈ I, (ww I c m t₀ j)^2 := le_of_lt hFt₀
      obtain ⟨t, ht, hFt⟩ :=
        intermediate_value_Icc ht₀ hFcont.continuousOn ⟨hFa, hFb⟩
      dsimp only at hFt
      have htt : 0 < t := by
        rcases eq_or_lt_of_le ht.1 with h | h
        · exfalso
          rw [← h] at hFt
          rw [hsq0] at hFt
          linarith
        · exact h
      have hαj₀ : c j₀ < m + 1/t := by
        rw [hj₀m]
        have h1 : 0 < 1/t := by positivity
        linarith
      have hZ : 0 < Za I c (m + 1/t) := Za_pos_of hj₀I hαj₀
      have hww : ∀ j, ww I c m t j = wa I c (m + 1/t) j :=
        fun j => ww_eq_wa htt rfl (ne_of_gt hZ) j
      have hFt' : (∑ j ∈ I, (wa I c (m + 1/t) j)^2) = B := by
        rw [← hFt]
        exact Finset.sum_congr rfl (fun j _ => by rw [hww j])
      refine ⟨t, ht.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro j _
        rw [hww j]
        exact wa_nonneg hZ j
      · simp only [hww]
        exact sum_wa hZ
      · simp only [hww]
        exact le_of_eq hFt'
      · left
        simp only [hww]
        exact hFt'
      · dsimp only
        simp only [hww]
        refine ⟨Pa_nonempty hZ, ?_, alpha_value hZ hFt'⟩
        intro i hi j hj hcj
        exact (mem_Pa hZ j).mpr ⟨hj, lt_of_le_of_lt hcj ((mem_Pa hZ i).mp hi).2⟩
      · intro u hu hsum hsq
        simp only [hww]
        exact alpha_optimal hZ u hu hsum hsq hFt'
    · have hfall : ∀ t₀ : ℝ, 0 ≤ t₀ → (∑ j ∈ I, (ww I c m t₀ j)^2) ≤ B := by
        intro t₀ ht₀
        by_contra hc
        exact hex ⟨t₀, ht₀, lt_of_not_ge hc⟩
      set M := I.filter (fun j => c j = m) with hM
      have hMsub : M ⊆ I := Finset.filter_subset _ _
      have hMmem : ∀ j, j ∈ M ↔ (j ∈ I ∧ c j = m) := by
        intro j; rw [hM, Finset.mem_filter]
      have hMne : M.Nonempty := ⟨j₀, (hMmem j₀).mpr ⟨hj₀I, hj₀m⟩⟩
      have hMc : 0 < M.card := Finset.card_pos.mpr hMne
      have hMcR : 0 < (M.card:ℝ) := Nat.cast_pos.mpr hMc
      have hMc0 : (M.card:ℝ) ≠ 0 := ne_of_gt hMcR
      set T := 1 + ∑ j ∈ I, (1/(c j - m)) with hT
      have hT0 : 0 ≤ T := by
        have h1 : 0 ≤ ∑ j ∈ I, (1/(c j - m)) :=
          Finset.sum_nonneg (fun j hj => div_nonneg zero_le_one (sub_nonneg.mpr (hge j hj)))
        rw [hT]
        linarith
      have hTkey : ∀ j ∈ I, c j ≠ m → 1 ≤ T * (c j - m) := by
        intro j hj hne
        have hd : 0 < c j - m := sub_pos.mpr (lt_of_le_of_ne (hge j hj) (Ne.symm hne))
        have h1 : 1/(c j - m) ≤ ∑ k ∈ I, (1/(c k - m)) :=
          Finset.single_le_sum
            (fun k hk => div_nonneg zero_le_one (sub_nonneg.mpr (hge k hk))) hj
        have h2 : 1/(c j - m) ≤ T := by rw [hT]; linarith
        exact (div_le_iff₀ hd).mp h2
      have hvvT : ∀ j ∈ I, vv c m T j = if c j = m then 1 else 0 := by
        intro j hj
        by_cases hc : c j = m
        · rw [if_pos hc, vv_at_min hc]
        · rw [if_neg hc, vv, max_eq_right]
          have h1 := hTkey j hj hc
          linarith
      have hzzT : zz I c m T = (M.card:ℝ) := by
        have h1 : ∑ j ∈ I, vv c m T j = ∑ j ∈ M, (1:ℝ) :=
          sum_eq_sum_sub hMsub
            (fun j hj hnj => by
              rw [hvvT j hj, if_neg (fun h => hnj ((hMmem j).mpr ⟨hj, h⟩))])
            (fun j hj => by
              rw [hvvT j (hMsub hj), if_pos ((hMmem j).mp hj).2])
        rw [zz, h1, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hwwT : ∀ j ∈ I, ww I c m T j = if c j = m then 1/(M.card:ℝ) else 0 := by
        intro j hj
        rw [ww, hvvT j hj, hzzT]
        by_cases hc : c j = m
        · rw [if_pos hc, if_pos hc]
        · rw [if_neg hc, if_neg hc, zero_div]
      have hsqT : ∑ j ∈ I, (ww I c m T j)^2 = 1/(M.card:ℝ) := by
        have h1 : ∑ j ∈ I, (ww I c m T j)^2 = ∑ j ∈ M, (1/(M.card:ℝ))^2 :=
          sum_eq_sum_sub hMsub
            (fun j hj hnj => by
              rw [hwwT j hj, if_neg (fun h => hnj ((hMmem j).mpr ⟨hj, h⟩)),
                zero_pow (by norm_num)])
            (fun j hj => by
              rw [hwwT j (hMsub hj), if_pos ((hMmem j).mp hj).2])
        rw [h1, Finset.sum_const, nsmul_eq_mul]
        field_simp [hMc0] <;> ring
      have hsumM : ∑ j ∈ M, c j = (M.card:ℝ) * m := by
        have h2 : ∀ j ∈ M, c j = m := fun j hj => ((hMmem j).mp hj).2
        have h3 : ∑ j ∈ M, c j = ∑ j ∈ M, m := Finset.sum_congr rfl h2
        rw [h3, Finset.sum_const, nsmul_eq_mul]
      have hvalT : ∑ j ∈ I, ww I c m T j * c j = m := by
        have h1 : ∑ j ∈ I, ww I c m T j * c j = ∑ j ∈ M, (1/(M.card:ℝ)) * c j :=
          sum_eq_sum_sub hMsub
            (fun j hj hnj => by
              rw [hwwT j hj, if_neg (fun h => hnj ((hMmem j).mpr ⟨hj, h⟩)), zero_mul])
            (fun j hj => by
              rw [hwwT j (hMsub hj), if_pos ((hMmem j).mp hj).2])
        rw [h1, ← Finset.mul_sum, hsumM]
        field_simp [hMc0] <;> ring
      have hμM : (∑ j ∈ M, c j)/(M.card:ℝ) = m := by
        rw [hsumM]
        field_simp [hMc0] <;> ring
      have hPe : I.filter (fun j => 0 < ww I c m T j) = M := by
        ext j
        rw [Finset.mem_filter, hMmem j]
        constructor
        · intro h
          refine ⟨h.1, ?_⟩
          by_contra hc
          rw [hwwT j h.1, if_neg hc] at h
          exact lt_irrefl 0 h.2
        · intro h
          refine ⟨h.1, ?_⟩
          rw [hwwT j h.1, if_pos h.2]
          exact div_pos one_pos hMcR
      refine ⟨T, hT0, fun j _ => ww_nonneg (hZall T) j, sum_ww (hZall T), ?_, ?_, ?_, ?_⟩
      · exact hfall T hT0
      · right
        intro j hj hc
        rw [hwwT j hj, if_neg hc]
      · dsimp only
        rw [hPe]
        refine ⟨hMne, ?_, ?_⟩
        · intro i hi j hj hcj
          refine (hMmem j).mpr ⟨hj, ?_⟩
          have h1 : c i = m := ((hMmem i).mp hi).2
          have h2 := hge j hj
          linarith
        · rw [hvalT, hμM]
          have hSM : ∑ j ∈ M, (c j - m)^2 = 0 := by
            have h2 : ∀ j ∈ M, (c j - m)^2 = 0 := by
              intro j hj
              have h3 := ((hMmem j).mp hj).2
              rw [h3, sub_self, zero_pow (by norm_num)]
            have h4 : ∑ j ∈ M, (c j - m)^2 = ∑ j ∈ M, (0:ℝ) := Finset.sum_congr rfl h2
            rw [h4]
            simp
          rw [hSM, mul_zero, Real.sqrt_zero, sub_zero]
      · intro u hu hsum hsq
        rw [hvalT]
        have h1 : ∀ j ∈ I, u j * m ≤ u j * c j := fun j hj =>
          mul_le_mul_of_nonneg_left (hge j hj) (hu j hj)
        have h2 := Finset.sum_le_sum h1
        rw [← Finset.sum_mul, hsum, one_mul] at h2
        exact h2

end

end Conjectures.Goldbach.NormalizedShiftOptimalWindow_aux

theorem Conjectures.Goldbach.NormalizedShiftOptimalWindow :
∀ (I : Finset ℕ) (c : ℕ → ℝ) (m B : ℝ),
      (∃ j ∈ I, c j = m) → (∀ j ∈ I, m ≤ c j) → 1 ≤ B * (I.card:ℝ) →
      let v := fun (t : ℝ) (j : ℕ) => max (1 - t*(c j-m)) 0
      let w := fun (t : ℝ) (j : ℕ) => v t j / (∑ k ∈ I, v t k)
      ∃ t : ℝ, 0 ≤ t ∧ (∀ j ∈ I, 0 ≤ w t j) ∧ (∑ j ∈ I, w t j) = 1 ∧
        (∑ j ∈ I, (w t j)^2) ≤ B ∧
        ((∑ j ∈ I, (w t j)^2) = B ∨ ∀ j ∈ I, c j ≠ m → w t j = 0) ∧
        (let P := I.filter (fun j => 0 < w t j)
         let μ := (∑ j ∈ P, c j)/(P.card:ℝ)
         P.Nonempty ∧ (∀ i ∈ P, ∀ j ∈ I, c j ≤ c i → j ∈ P) ∧
           (∑ j ∈ I, w t j * c j) =
             μ - Real.sqrt ((B - 1/(P.card:ℝ)) * (∑ j ∈ P, (c j-μ)^2))) ∧
        ∀ u : ℕ → ℝ, (∀ j ∈ I, 0 ≤ u j) → (∑ j ∈ I, u j) = 1 →
          (∑ j ∈ I, (u j)^2) ≤ B → (∑ j ∈ I, w t j * c j) ≤ ∑ j ∈ I, u j * c j :=
  Conjectures.Goldbach.NormalizedShiftOptimalWindow_aux.main_aux
