import Mathlib

open scoped Classical
namespace Conjectures.Goldbach.DyadicTruncationFormBudget_aux

noncomputable def Hm (m : ℕ) [NeZero m] (Nz : ZMod m) (χ ψ : DirichletCharacter ℂ m) : ℂ :=
  (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (Nz - (x : ZMod m))) / (m.totient : ℂ)

noncomputable def Bf (m : ℕ) [NeZero m] (Nz : ZMod m) (s : Finset (DirichletCharacter ℂ m))
    (u w : DirichletCharacter ℂ m → ℂ) : ℂ :=
  ∑ χ ∈ s, ∑ ψ ∈ s, star (u χ) * Hm m Nz χ ψ * w ψ

noncomputable def Qf (m : ℕ) [NeZero m] (Nz : ZMod m) (s : Finset (DirichletCharacter ℂ m))
    (a : DirichletCharacter ℂ m → ℂ) : ℝ :=
  (Bf m Nz s a a).re

lemma bf_sub_right (m : ℕ) [NeZero m] (Nz : ZMod m) (s : Finset (DirichletCharacter ℂ m))
    (u w₁ w₂ : DirichletCharacter ℂ m → ℂ) :
    Bf m Nz s u (w₁ - w₂) = Bf m Nz s u w₁ - Bf m Nz s u w₂ := by
  simp only [Bf, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma bf_sub_left (m : ℕ) [NeZero m] (Nz : ZMod m) (s : Finset (DirichletCharacter ℂ m))
    (u₁ u₂ w : DirichletCharacter ℂ m → ℂ) :
    Bf m Nz s (u₁ - u₂) w = Bf m Nz s u₁ w - Bf m Nz s u₂ w := by
  simp only [Bf, Pi.sub_apply, star_sub, sub_mul, Finset.sum_sub_distrib]

lemma cs_bound {ι : Type*} (s : Finset ι) (u g : ι → ℂ) :
    ‖∑ χ ∈ s, star (u χ) * g χ‖ ≤
      Real.sqrt (∑ χ ∈ s, ‖u χ‖ ^ 2) * Real.sqrt (∑ χ ∈ s, ‖g χ‖ ^ 2) := by
  have h1 : ‖∑ χ ∈ s, star (u χ) * g χ‖ ≤ ∑ χ ∈ s, ‖u χ‖ * ‖g χ‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun χ _ => ?_)
    rw [norm_mul, Complex.star_def, Complex.norm_conj]
  refine h1.trans ?_
  exact Real.sum_mul_le_sqrt_mul_sqrt s (fun χ => ‖u χ‖) (fun χ => ‖g χ‖)

lemma sqrt_pow_real (x : ℝ) (hx : 0 ≤ x) (j : ℕ) :
    Real.sqrt (x ^ j) = (Real.sqrt x) ^ j := by
  induction j with
  | zero => simp
  | succ n ih =>
    have he : x ^ (Nat.succ n) = x ^ n * x := pow_succ x n
    rw [he, Real.sqrt_mul (pow_nonneg hx n) x, ih, pow_succ]

lemma geom_mul_one_sub (r : ℝ) (n : ℕ) :
    (1 - r) * (∑ j ∈ Finset.range n, r ^ j) = 1 - r ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : (∑ j ∈ Finset.range (n + 1), r ^ j) = (∑ j ∈ Finset.range n, r ^ j) + r ^ n :=
      Finset.sum_range_succ _ n
    rw [he, mul_add, ih, pow_succ]
    ring

lemma geom_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    (∑ j ∈ Finset.range n, r ^ j) ≤ 1 / (1 - r) := by
  have hpos : (0 : ℝ) < 1 - r := by linarith
  rw [le_div_iff₀ hpos]
  have h := geom_mul_one_sub r n
  have h2 := pow_nonneg hr0 n
  linarith

lemma sqrt_half_le : Real.sqrt (1 / 2 : ℝ) ≤ 5 / 7 := by
  rw [Real.sqrt_le_iff]
  constructor
  · norm_num
  · norm_num

lemma sqrt_two_le : Real.sqrt (2 : ℝ) ≤ 10 / 7 := by
  rw [Real.sqrt_le_iff]
  constructor
  · norm_num
  · norm_num

lemma sqrt_two_div_le : Real.sqrt (2 : ℝ) * (1 / (1 - Real.sqrt (1 / 2 : ℝ))) ≤ 5 := by
  have h1 : Real.sqrt (1 / 2 : ℝ) ≤ 5 / 7 := sqrt_half_le
  have h2 : Real.sqrt (2 : ℝ) ≤ 10 / 7 := sqrt_two_le
  have h3 : (0 : ℝ) < 1 - Real.sqrt (1 / 2 : ℝ) := by linarith
  have h4 : 1 / (1 - Real.sqrt (1 / 2 : ℝ)) ≤ 7 / 2 := by
    rw [div_le_iff₀ h3]
    linarith
  calc Real.sqrt (2 : ℝ) * (1 / (1 - Real.sqrt (1 / 2 : ℝ))) ≤ (10 / 7) * (7 / 2) := by
        apply mul_le_mul h2 h4
        · exact div_nonneg zero_le_one (le_of_lt h3)
        · norm_num
    _ = 5 := by norm_num

lemma pow_div_pow (k K : ℕ) (hk : k < K) :
    ((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ) = (1 / 2 : ℝ) ^ (K - 1 - k) := by
  have hK : K = (k + 1) + (K - 1 - k) := by omega
  have e1 : ((2 ^ (k + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (k + 1) := by rw [Nat.cast_pow]; norm_num
  have e2 : ((2 ^ K : ℕ) : ℝ) = (2 : ℝ) ^ K := by rw [Nat.cast_pow]; norm_num
  have e3 : (2 : ℝ) ^ K = (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (K - 1 - k) := by
    conv_lhs => rw [hK]
    rw [pow_add]
  have e4 : ((1 / 2 : ℝ) ^ (K - 1 - k) * (2 : ℝ) ^ (K - 1 - k)) = 1 := by
    rw [← mul_pow]; norm_num
  rw [e1, e2, e3, div_eq_iff (by positivity)]
  calc (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ (k + 1) * 1 := (mul_one _).symm
    _ = (2 : ℝ) ^ (k + 1) * ((1 / 2 : ℝ) ^ (K - 1 - k) * (2 : ℝ) ^ (K - 1 - k)) := by rw [e4]
    _ = (1 / 2 : ℝ) ^ (K - 1 - k) * ((2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (K - 1 - k)) := by ring

lemma weight_core (m M Nn : ℝ) (hm : 0 < m) (hM : 0 < M) (hmM : m ≤ M) (hNM : Nn ≤ M) :
    (m / M) ^ 2 * (1 + Nn / m) ≤ 2 * (m / M) := by
  have ht : (0 : ℝ) ≤ m / M := div_nonneg (le_of_lt hm) (le_of_lt hM)
  have hmm : m / M ≤ 1 := (div_le_one hM).mpr hmM
  have hNM1 : Nn / M ≤ 1 := (div_le_one hM).mpr hNM
  have h1 : (m / M) ^ 2 ≤ m / M := by
    have := mul_le_mul_of_nonneg_left hmm ht
    calc (m / M) ^ 2 = (m / M) * (m / M) := by ring
      _ ≤ (m / M) * 1 := this
      _ = m / M := by ring
  have h2 : (m / M) * (Nn / M) ≤ m / M := by
    have := mul_le_mul_of_nonneg_left hNM1 ht
    calc (m / M) * (Nn / M) ≤ (m / M) * 1 := this
      _ = m / M := by ring
  have h3 : (m / M) * (Nn / m) = Nn / M := by
    field_simp [ne_of_gt hm, ne_of_gt hM] <;> ring
  have he : (m / M) ^ 2 * (1 + Nn / m) = (m / M) ^ 2 + (m / M) * (Nn / M) := by
    calc (m / M) ^ 2 * (1 + Nn / m)
        = (m / M) ^ 2 + (m / M) ^ 2 * (Nn / m) := by ring
      _ = (m / M) ^ 2 + (m / M) * ((m / M) * (Nn / m)) := by ring
      _ = (m / M) ^ 2 + (m / M) * (Nn / M) := by rw [h3]
  rw [he]
  linarith


def fibSet (m : ℕ) (N : ℕ) (r : ZMod m) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun n => (n : ZMod m) = r)

def wsum (m : ℕ) (N : ℕ) (w : ℕ → ℂ) (r : ZMod m) : ℂ :=
  ∑ n ∈ fibSet m N r, w n

theorem mem_fiber (m : ℕ) [NeZero m] {N : ℕ} {r : ZMod m} {n : ℕ} (hn : n ∈ fibSet m N r) :
    n < N + 1 ∧ (n : ZMod m) = r := by
  simp only [fibSet, Finset.mem_filter, Finset.mem_range] at hn
  exact hn

theorem fiber_card (m : ℕ) [NeZero m] (N : ℕ) (r : ZMod m) : (fibSet m N r).card ≤ 1 + N / m := by
  have hinj : Set.InjOn (fun n : ℕ => n / m) (fibSet m N r : Set ℕ) := by
    intro a ha b hb hab
    replace hab : a / m = b / m := hab
    have ha' := mem_fiber m ha
    have hb' := mem_fiber m hb
    have hmod : a % m = b % m :=
      (ZMod.natCast_eq_natCast_iff' a b m).mp (by rw [ha'.2, hb'.2])
    calc a = m * (a / m) + a % m := (Nat.div_add_mod a m).symm
      _ = m * (b / m) + b % m := by rw [hab, hmod]
      _ = b := Nat.div_add_mod b m
  have himg : (fibSet m N r).image (fun n : ℕ => n / m) ⊆ Finset.range (1 + N / m) := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    have h1 := (mem_fiber m hn).1
    have h2 : n / m ≤ N / m := Nat.div_le_div_right (Nat.le_of_lt_succ h1)
    exact Finset.mem_range.mpr (by omega)
  calc (fibSet m N r).card = ((fibSet m N r).image (fun n : ℕ => n / m)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (1 + N / m)).card := Finset.card_le_card himg
    _ = 1 + N / m := Finset.card_range _

theorem fiber_sum (m : ℕ) [NeZero m] (N : ℕ) {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    (∑ n ∈ Finset.range (N + 1), f n) = ∑ r : ZMod m, ∑ n ∈ fibSet m N r, f n := by
  have h1 : ∀ n ∈ Finset.range (N + 1), f n = ∑ r : ZMod m, if (n : ZMod m) = r then f n else 0 := by
    intro n _
    simp
  calc (∑ n ∈ Finset.range (N + 1), f n)
      = ∑ n ∈ Finset.range (N + 1), ∑ r : ZMod m, if (n : ZMod m) = r then f n else 0 :=
        Finset.sum_congr rfl h1
    _ = ∑ r : ZMod m, ∑ n ∈ Finset.range (N + 1), if (n : ZMod m) = r then f n else 0 :=
        Finset.sum_comm
    _ = ∑ r : ZMod m, ∑ n ∈ fibSet m N r, f n := by
        apply Finset.sum_congr rfl
        intro r _
        rw [fibSet, Finset.sum_filter]

theorem cs_sum (t : Finset ℕ) (z : ℕ → ℂ) :
    ‖∑ i ∈ t, z i‖ ^ 2 ≤ (t.card : ℝ) * ∑ i ∈ t, ‖z i‖ ^ 2 := by
  have hnorm : ∀ x : ℂ, ‖x‖ ^ 2 = x.re ^ 2 + x.im ^ 2 := by
    intro x
    have := Complex.sq_norm_sub_sq_re x
    linarith
  have h1 : ‖∑ i ∈ t, z i‖ ^ 2 = (∑ i ∈ t, (z i).re) ^ 2 + (∑ i ∈ t, (z i).im) ^ 2 := by
    rw [hnorm]
    simp only [Complex.re_sum, Complex.im_sum]
  have h2 : (∑ i ∈ t, (z i).re) ^ 2 ≤ (t.card : ℝ) * ∑ i ∈ t, (z i).re ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h3 : (∑ i ∈ t, (z i).im) ^ 2 ≤ (t.card : ℝ) * ∑ i ∈ t, (z i).im ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h4 : (∑ i ∈ t, ‖z i‖ ^ 2) = (∑ i ∈ t, (z i).re ^ 2) + ∑ i ∈ t, (z i).im ^ 2 := by
    simp_rw [hnorm]
    rw [Finset.sum_add_distrib]
  have h5 : (t.card : ℝ) * ((∑ i ∈ t, (z i).re ^ 2) + ∑ i ∈ t, (z i).im ^ 2)
      = (t.card : ℝ) * ∑ i ∈ t, (z i).re ^ 2 + (t.card : ℝ) * ∑ i ∈ t, (z i).im ^ 2 := by ring
  rw [h1, h4, h5]
  linarith [h2, h3]

theorem units_sum (m : ℕ) [NeZero m] {M : Type*} [AddCommMonoid M] (g : ZMod m → M) :
    (∑ a : (ZMod m)ˣ, g (a : ZMod m))
      = ∑ r ∈ (Finset.univ : Finset (ZMod m)).filter IsUnit, g r := by
  refine Finset.sum_bij (fun (a : (ZMod m)ˣ) _ => (a : ZMod m)) ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.isUnit⟩
  · intro a₁ _ a₂ _ h
    exact Units.val_injective h
  · intro r hr
    have hu : IsUnit r := (Finset.mem_filter.mp hr).2
    exact ⟨hu.unit, Finset.mem_univ _, hu.unit_spec⟩
  · intro a _
    rfl

theorem sum_units_eq (m : ℕ) [NeZero m] (g : ZMod m → ℂ) (h0 : ∀ r, ¬ IsUnit r → g r = 0) :
    (∑ a : (ZMod m)ˣ, g (a : ZMod m)) = ∑ r : ZMod m, g r := by
  rw [units_sum m g, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : IsUnit r
  · simp [h]
  · simp [h, h0 r h]

theorem sum_units_le (m : ℕ) [NeZero m] (g : ZMod m → ℝ) (h0 : ∀ r, 0 ≤ g r) :
    (∑ a : (ZMod m)ˣ, g (a : ZMod m)) ≤ ∑ r : ZMod m, g r := by
  rw [units_sum m g]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => h0 i)

theorem orth2u (m : ℕ) [NeZero m] (a b : (ZMod m)ˣ) :
    (∑ χ : DirichletCharacter ℂ m, χ (a : ZMod m) * star (χ (b : ZMod m))) =
      if a = b then (m.totient : ℂ) else 0 := by
  have hcb (χ : DirichletCharacter ℂ m) : star (χ (b : ZMod m)) = χ ((b : ZMod m)⁻¹) := by
    rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]
  have h1 : (∑ χ : DirichletCharacter ℂ m, χ (a : ZMod m) * star (χ (b : ZMod m))) =
      ∑ χ : DirichletCharacter ℂ m, χ ((b : ZMod m)⁻¹) * χ (a : ZMod m) := by
    apply Finset.sum_congr rfl
    intro χ _
    rw [hcb χ, mul_comm]
  rw [h1, DirichletCharacter.sum_char_inv_mul_char_eq ℂ b.isUnit (a : ZMod m)]
  by_cases h : (b : ZMod m) = (a : ZMod m)
  · rw [if_pos h, if_pos (Units.val_inj.mp h).symm]
  · rw [if_neg h, if_neg (fun hab => h (by rw [hab]))]

theorem parseval_starU (m : ℕ) [NeZero m] (G : (ZMod m)ˣ → ℂ) :
    (∑ χ : DirichletCharacter ℂ m, ‖∑ a : (ZMod m)ˣ, G a * star (χ (a : ZMod m))‖ ^ 2) =
      (m.totient : ℝ) * ∑ a : (ZMod m)ˣ, ‖G a‖ ^ 2 := by
  have hv (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
  have hex (χ : DirichletCharacter ℂ m) :
      star (∑ a : (ZMod m)ˣ, G a * star (χ (a : ZMod m))) *
          (∑ a : (ZMod m)ˣ, G a * star (χ (a : ZMod m))) =
        ∑ a : (ZMod m)ˣ, ∑ b : (ZMod m)ˣ,
          (star (G a) * G b) * (χ (a : ZMod m) * star (χ (b : ZMod m))) := by
    rw [star_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [star_mul, star_star]
    ring
  have hswap : ∀ (F : (ZMod m)ˣ → (ZMod m)ˣ → DirichletCharacter ℂ m → ℂ),
      (∑ χ : DirichletCharacter ℂ m, ∑ a : (ZMod m)ˣ, ∑ b : (ZMod m)ˣ, F a b χ) =
        ∑ a : (ZMod m)ˣ, ∑ b : (ZMod m)ˣ, ∑ χ : DirichletCharacter ℂ m, F a b χ := by
    intro F
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
  have hmain : (∑ χ : DirichletCharacter ℂ m,
        star (∑ a : (ZMod m)ˣ, G a * star (χ (a : ZMod m))) *
          (∑ a : (ZMod m)ˣ, G a * star (χ (a : ZMod m)))) =
      (m.totient : ℂ) * ∑ a : (ZMod m)ˣ, ((‖G a‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [hex]
    rw [hswap]
    simp_rw [← Finset.mul_sum, orth2u m]
    have hcol : ∀ a b : (ZMod m)ˣ,
        (star (G a) * G b) * (if a = b then (m.totient : ℂ) else 0) =
          if a = b then ((‖G a‖ ^ 2 : ℝ) : ℂ) * (m.totient : ℂ) else 0 := by
      intro a b
      by_cases h : a = b
      · subst h
        rw [if_pos rfl, if_pos rfl, hv]
      · rw [if_neg h, if_neg h, mul_zero]
    simp_rw [hcol]
    simp
    rw [← Finset.sum_mul, mul_comm]
  have hfinal : (∑ χ : DirichletCharacter ℂ m,
        ((‖∑ a : (ZMod m)ˣ, G a * star (χ (a : ZMod m))‖ ^ 2 : ℝ) : ℂ)) =
      (m.totient : ℂ) * ∑ a : (ZMod m)ˣ, ((‖G a‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hmain]
    apply Finset.sum_congr rfl
    intro χ _
    exact (hv _).symm
  simp only [← Complex.ofReal_sum] at hfinal
  exact_mod_cast hfinal


variable {m : ℕ} [NeZero m]

lemma totient_pos_real : (0 : ℝ) < (m.totient : ℝ) := by
  exact_mod_cast Nat.totient_pos.mpr (NeZero.pos m)

lemma totient_cast : ((m.totient : ℕ) : ℂ) = ((m.totient : ℝ) : ℂ) := by
  simp

lemma star_mul_self (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]

lemma sum_interchange {α β : Type*} [Fintype α] [Fintype β] {M : Type*} [AddCommMonoid M]
    (f : α → β → M) : (∑ a : α, ∑ b : β, f a b) = ∑ b : β, ∑ a : α, f a b := by
  conv_lhs => rw [Finset.sum_comm]

lemma sum_units_eq_sum {M : Type*} [AddCommMonoid M] (f : ZMod m → M)
    (hf : ∀ a, ¬IsUnit a → f a = 0) :
    ∑ x : (ZMod m)ˣ, f (x : ZMod m) = ∑ a : ZMod m, f a := by
  classical
  have key : ∀ a : ZMod m,
      a ∈ (Finset.univ : Finset (ZMod m)ˣ).map ⟨((↑) : (ZMod m)ˣ → ZMod m), Units.val_injective⟩
        ↔ IsUnit a := by
    intro a
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, rfl⟩
      exact x.isUnit
    · intro h
      exact ⟨h.unit, by simpa using h.unit_spec⟩
  have hmap : ∑ a ∈ (Finset.univ : Finset (ZMod m)ˣ).map
        ⟨((↑) : (ZMod m)ˣ → ZMod m), Units.val_injective⟩, f a = ∑ x : (ZMod m)ˣ, f (x : ZMod m) := by
    rw [Finset.sum_map]
    rfl
  rw [← hmap]
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro a _ hna
  exact hf a (fun hu => hna ((key a).mpr hu))

lemma sum_char_units (θ : DirichletCharacter ℂ m) :
    ∑ x : (ZMod m)ˣ, θ (x : ZMod m) = if θ = 1 then ((m.totient : ℝ) : ℂ) else 0 := by
  have hz : ∀ a : ZMod m, ¬IsUnit a → θ a = 0 := fun a ha => MulChar.map_nonunit θ ha
  rw [sum_units_eq_sum (fun a => θ a) hz]
  by_cases h : θ = 1
  · rw [if_pos h, h, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient, totient_cast]
  · rw [if_neg h, MulChar.sum_eq_zero_of_ne_one h]

lemma star_char (χ : DirichletCharacter ℂ m) (x : (ZMod m)ˣ) :
    star (χ (x : ZMod m)) = χ ((x : ZMod m)⁻¹) := by
  rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]

lemma orth1 (x y : (ZMod m)ˣ) :
    ∑ χ : DirichletCharacter ℂ m, star (χ (x : ZMod m)) * χ (y : ZMod m)
      = if x = y then ((m.totient : ℝ) : ℂ) else 0 := by
  simp_rw [star_char]
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ x.isUnit (y : ZMod m)]
  by_cases hxy : (x : ZMod m) = (y : ZMod m)
  · rw [if_pos hxy, if_pos (Units.val_inj.mp hxy), totient_cast]
  · rw [if_neg hxy, if_neg (fun h => hxy (Units.val_inj.mpr h))]

lemma orth2 (χ ψ : DirichletCharacter ℂ m) :
    ∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (x : ZMod m)
      = if χ = ψ then ((m.totient : ℝ) : ℂ) else 0 := by
  have h1 (x : (ZMod m)ˣ) :
      star (χ (x : ZMod m)) * ψ (x : ZMod m) = (χ⁻¹ * ψ) (x : ZMod m) := by
    rw [MulChar.mul_apply, MulChar.star_apply']
  have h2 : ∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (x : ZMod m)
      = ∑ x : (ZMod m)ˣ, (χ⁻¹ * ψ) (x : ZMod m) := Finset.sum_congr rfl (fun x _ => h1 x)
  rw [h2, sum_char_units]
  by_cases h : χ = ψ
  · subst h
    simp
  · rw [if_neg h, if_neg (fun h2 => h (inv_mul_eq_one.mp h2))]

lemma parseval_complex (g : (ZMod m)ˣ → ℂ) :
    ∑ χ : DirichletCharacter ℂ m, star (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * g x)
        * (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * g x)
      = ((m.totient : ℝ) : ℂ) * ∑ x : (ZMod m)ˣ, star (g x) * g x := by
  have hex (χ : DirichletCharacter ℂ m) :
      star (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * g x)
          * (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * g x)
        = ∑ x : (ZMod m)ˣ, ∑ y : (ZMod m)ˣ,
            (star (g x) * g y) * (star (χ (y : ZMod m)) * χ (x : ZMod m)) := by
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [star_mul, star_star]
    ring
  simp_rw [hex]
  have hstep (x : (ZMod m)ˣ) :
      ∑ χ : DirichletCharacter ℂ m, ∑ y : (ZMod m)ˣ,
          (star (g x) * g y) * (star (χ (y : ZMod m)) * χ (x : ZMod m))
        = star (g x) * g x * ((m.totient : ℝ) : ℂ) := by
    have h1 : ∑ χ : DirichletCharacter ℂ m, ∑ y : (ZMod m)ˣ,
        (star (g x) * g y) * (star (χ (y : ZMod m)) * χ (x : ZMod m))
        = ∑ y : (ZMod m)ˣ, (star (g x) * g y)
            * ∑ χ : DirichletCharacter ℂ m, (star (χ (y : ZMod m)) * χ (x : ZMod m)) := by
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Finset.mul_sum]
    rw [h1]
    simp_rw [orth1]
    have h2 : ∀ y : (ZMod m)ˣ,
        (star (g x) * g y) * (if y = x then ((m.totient : ℝ) : ℂ) else 0)
          = if y = x then star (g x) * g x * ((m.totient : ℝ) : ℂ) else 0 := by
      intro y
      by_cases hy : y = x
      · rw [if_pos hy, if_pos hy, hy]
      · rw [if_neg hy, if_neg hy, mul_zero]
    simp_rw [h2]
    simp
  conv_lhs => rw [Finset.sum_comm]
  have h3 : ∑ x : (ZMod m)ˣ, ∑ χ : DirichletCharacter ℂ m, ∑ y : (ZMod m)ˣ,
      (star (g x) * g y) * (star (χ (y : ZMod m)) * χ (x : ZMod m))
      = ∑ x : (ZMod m)ˣ, star (g x) * g x * ((m.totient : ℝ) : ℂ) :=
    Finset.sum_congr rfl (fun x _ => hstep x)
  rw [h3, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun x _ => by ring)

lemma parseval (g : (ZMod m)ˣ → ℂ) :
    ∑ χ : DirichletCharacter ℂ m, ‖∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * g x‖ ^ 2
      = (m.totient : ℝ) * ∑ x : (ZMod m)ˣ, ‖g x‖ ^ 2 := by
  have h := parseval_complex g
  simp_rw [star_mul_self] at h
  have h2 : ((∑ χ : DirichletCharacter ℂ m,
        ‖∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * g x‖ ^ 2 : ℝ) : ℂ)
      = (((m.totient : ℝ) * ∑ x : (ZMod m)ˣ, ‖g x‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_sum]
    exact h
  exact Complex.ofReal_injective h2

lemma sum_swap (N : ZMod m) (A B : ZMod m → ℂ)
    (hA : ∀ a, ¬IsUnit a → A a = 0) (hB : ∀ a, ¬IsUnit a → B a = 0) :
    ∑ x : (ZMod m)ˣ, A (x : ZMod m) * B (N - (x : ZMod m))
      = ∑ x : (ZMod m)ˣ, B (x : ZMod m) * A (N - (x : ZMod m)) := by
  have h1 : ∀ a : ZMod m, ¬IsUnit a → A a * B (N - a) = 0 := by
    intro a ha
    rw [hA a ha, zero_mul]
  have h2 : ∀ a : ZMod m, ¬IsUnit a → B a * A (N - a) = 0 := by
    intro a ha
    rw [hB a ha, zero_mul]
  rw [sum_units_eq_sum (fun a => A a * B (N - a)) h1,
    sum_units_eq_sum (fun a => B a * A (N - a)) h2]
  have hinv : ∀ z : ZMod m, N - (N - z) = z := fun z => by ring
  have hbij : Function.Bijective (fun z : ZMod m => N - z) := by
    constructor
    · intro a b hab
      have h3 := congrArg (fun t : ZMod m => N - t) hab
      rw [hinv, hinv] at h3
      exact h3
    · intro b
      exact ⟨N - b, hinv b⟩
  have hkey : ∑ a : ZMod m, A a * B (N - a) = ∑ b : ZMod m, A (N - b) * B b :=
    Fintype.sum_bijective (fun z : ZMod m => N - z) hbij
      (fun a : ZMod m => A a * B (N - a)) (fun b : ZMod m => A (N - b) * B b) (fun b => by simp)
  rw [hkey]
  exact Finset.sum_congr rfl (fun b _ => by ring)

lemma sum_reflect_le (N : ZMod m) (F : ZMod m → ℂ) (hF : ∀ a, ¬IsUnit a → F a = 0) :
    ∑ x : (ZMod m)ˣ, ‖F (N - (x : ZMod m))‖ ^ 2 ≤ ∑ x : (ZMod m)ˣ, ‖F (x : ZMod m)‖ ^ 2 := by
  classical
  have hinv : ∀ z : ZMod m, N - (N - z) = z := fun z => by ring
  have hinj : Function.Injective (fun x : (ZMod m)ˣ => N - (x : ZMod m)) := by
    intro a b hab
    have h3 := congrArg (fun t : ZMod m => N - t) hab
    rw [hinv, hinv] at h3
    exact Units.val_injective h3
  have hf0 : ∀ a : ZMod m, ¬IsUnit a → ‖F a‖ ^ 2 = (0 : ℝ) := by
    intro a ha
    simp [hF a ha]
  have hmap : ∑ a ∈ (Finset.univ : Finset (ZMod m)ˣ).map
        ⟨fun x : (ZMod m)ˣ => N - (x : ZMod m), hinj⟩, ‖F a‖ ^ 2
      = ∑ x : (ZMod m)ˣ, ‖F (N - (x : ZMod m))‖ ^ 2 := by
    rw [Finset.sum_map]
    rfl
  calc ∑ x : (ZMod m)ˣ, ‖F (N - (x : ZMod m))‖ ^ 2
      = ∑ a ∈ (Finset.univ : Finset (ZMod m)ˣ).map
          ⟨fun x : (ZMod m)ˣ => N - (x : ZMod m), hinj⟩, ‖F a‖ ^ 2 := hmap.symm
    _ ≤ ∑ a : ZMod m, ‖F a‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
        intro a _ _
        exact sq_nonneg _
    _ = ∑ x : (ZMod m)ˣ, ‖F (x : ZMod m)‖ ^ 2 :=
        (sum_units_eq_sum (fun a : ZMod m => ‖F a‖ ^ 2) hf0).symm

lemma synth_norm (w : DirichletCharacter ℂ m → ℂ) :
    ∑ x : (ZMod m)ˣ, ‖∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (x : ZMod m)‖ ^ 2
      = (m.totient : ℝ) * ∑ ψ : DirichletCharacter ℂ m, ‖w ψ‖ ^ 2 := by
  have hB (χ : DirichletCharacter ℂ m) :
      ∑ x : (ZMod m)ˣ, star (χ (x : ZMod m))
          * ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (x : ZMod m)
        = ((m.totient : ℝ) : ℂ) * w χ := by
    calc ∑ x : (ZMod m)ˣ, star (χ (x : ZMod m))
            * ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (x : ZMod m)
        = ∑ x : (ZMod m)ˣ, ∑ ψ : DirichletCharacter ℂ m,
            star (χ (x : ZMod m)) * (w ψ * ψ (x : ZMod m)) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ ψ : DirichletCharacter ℂ m, ∑ x : (ZMod m)ˣ,
            star (χ (x : ZMod m)) * (w ψ * ψ (x : ZMod m)) := sum_interchange _
      _ = ∑ ψ : DirichletCharacter ℂ m, w ψ
            * ∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (x : ZMod m) := by
          refine Finset.sum_congr rfl (fun ψ _ => ?_)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun x _ => by ring)
      _ = ∑ ψ : DirichletCharacter ℂ m,
            w ψ * (if χ = ψ then ((m.totient : ℝ) : ℂ) else 0) := by
          simp_rw [orth2]
      _ = ((m.totient : ℝ) : ℂ) * w χ := by
          have h2 : ∀ ψ : DirichletCharacter ℂ m,
              w ψ * (if χ = ψ then ((m.totient : ℝ) : ℂ) else 0)
                = if ψ = χ then ((m.totient : ℝ) : ℂ) * w χ else 0 := by
            intro ψ
            by_cases hψ : ψ = χ
            · rw [if_pos hψ, if_pos hψ.symm, hψ]
              ring
            · rw [if_neg hψ, if_neg (fun h => hψ h.symm), mul_zero]
          simp_rw [h2]
          simp
  have hp := parseval (fun x : (ZMod m)ˣ => ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (x : ZMod m))
  have hkey1 : ∀ χ : DirichletCharacter ℂ m,
      ‖∑ x : (ZMod m)ˣ, star (χ (x : ZMod m))
        * ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (x : ZMod m)‖ ^ 2
      = (m.totient : ℝ) ^ 2 * ‖w χ‖ ^ 2 := by
    intro χ
    rw [hB χ, norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt totient_pos_real), mul_pow]
  have hkey : ∑ χ : DirichletCharacter ℂ m,
      ‖∑ x : (ZMod m)ˣ, star (χ (x : ZMod m))
        * ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (x : ZMod m)‖ ^ 2
      = (m.totient : ℝ) ^ 2 * ∑ ψ : DirichletCharacter ℂ m, ‖w ψ‖ ^ 2 := by
    rw [Finset.sum_congr rfl (fun χ _ => hkey1 χ), Finset.mul_sum]
  rw [hkey] at hp
  have h3 : (m.totient : ℝ) * ((m.totient : ℝ) * ∑ ψ : DirichletCharacter ℂ m, ‖w ψ‖ ^ 2)
      = (m.totient : ℝ)
        * ∑ x : (ZMod m)ˣ, ‖∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (x : ZMod m)‖ ^ 2 := by
    rw [← hp]
    ring
  exact (mul_left_cancel₀ (ne_of_gt totient_pos_real) h3).symm

lemma main_bound (N : ZMod m) (w : DirichletCharacter ℂ m → ℂ) :
    ∑ χ : DirichletCharacter ℂ m,
        ‖∑ ψ : DirichletCharacter ℂ m,
            ((∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (N - (x : ZMod m)))
              / (m.totient : ℂ)) * w ψ‖ ^ 2
      ≤ ∑ ψ : DirichletCharacter ℂ m, ‖w ψ‖ ^ 2 := by
  have hφ : (m.totient : ℝ) ≠ 0 := ne_of_gt totient_pos_real
  have hFz (a : ZMod m) (ha : ¬IsUnit a) :
      ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ a = 0 := by
    refine Finset.sum_eq_zero (fun ψ _ => ?_)
    rw [MulChar.map_nonunit ψ ha, mul_zero]
  have step1 (χ : DirichletCharacter ℂ m) :
      ∑ ψ : DirichletCharacter ℂ m,
          ((∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (N - (x : ZMod m)))
            / (m.totient : ℂ)) * w ψ
        = (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m))
            * ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (N - (x : ZMod m))) / (m.totient : ℂ) := by
    have hinner : ∑ ψ : DirichletCharacter ℂ m,
        (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (N - (x : ZMod m))) * w ψ
        = ∑ x : (ZMod m)ˣ, star (χ (x : ZMod m))
            * ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (N - (x : ZMod m)) := by
      calc ∑ ψ : DirichletCharacter ℂ m,
            (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (N - (x : ZMod m))) * w ψ
          = ∑ ψ : DirichletCharacter ℂ m, ∑ x : (ZMod m)ˣ,
              (star (χ (x : ZMod m)) * ψ (N - (x : ZMod m))) * w ψ := by
            refine Finset.sum_congr rfl (fun ψ _ => ?_)
            rw [Finset.sum_mul]
        _ = ∑ x : (ZMod m)ˣ, ∑ ψ : DirichletCharacter ℂ m,
              (star (χ (x : ZMod m)) * ψ (N - (x : ZMod m))) * w ψ := sum_interchange _
        _ = ∑ x : (ZMod m)ˣ, star (χ (x : ZMod m))
              * ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (N - (x : ZMod m)) := by
            refine Finset.sum_congr rfl (fun x _ => ?_)
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun ψ _ => by ring)
    calc ∑ ψ : DirichletCharacter ℂ m,
          ((∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (N - (x : ZMod m)))
            / (m.totient : ℂ)) * w ψ
        = (∑ ψ : DirichletCharacter ℂ m,
            (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (N - (x : ZMod m))) * w ψ)
            / (m.totient : ℂ) := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl (fun ψ _ => by ring)
      _ = (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m))
            * ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (N - (x : ZMod m))) / (m.totient : ℂ) := by
          rw [hinner]
  have step2 (z : ℂ) : ‖z / (m.totient : ℂ)‖ ^ 2 = ‖z‖ ^ 2 / (m.totient : ℝ) ^ 2 := by
    rw [norm_div, div_pow, Complex.norm_natCast]
  calc ∑ χ : DirichletCharacter ℂ m,
        ‖∑ ψ : DirichletCharacter ℂ m,
          ((∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (N - (x : ZMod m)))
            / (m.totient : ℂ)) * w ψ‖ ^ 2
      = ∑ χ : DirichletCharacter ℂ m, ‖∑ x : (ZMod m)ˣ, star (χ (x : ZMod m))
          * ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (N - (x : ZMod m))‖ ^ 2
          / (m.totient : ℝ) ^ 2 := by
        refine Finset.sum_congr rfl (fun χ _ => ?_)
        rw [step1 χ, step2]
    _ = ((m.totient : ℝ) * ∑ x : (ZMod m)ˣ,
          ‖∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (N - (x : ZMod m))‖ ^ 2) / (m.totient : ℝ) ^ 2 := by
        rw [← Finset.sum_div,
          parseval (fun x : (ZMod m)ˣ => ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (N - (x : ZMod m)))]
    _ ≤ ((m.totient : ℝ) * ∑ x : (ZMod m)ˣ,
          ‖∑ ψ : DirichletCharacter ℂ m, w ψ * ψ (x : ZMod m)‖ ^ 2) / (m.totient : ℝ) ^ 2 := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt totient_pos_real)
        exact sum_reflect_le N (fun a : ZMod m => ∑ ψ : DirichletCharacter ℂ m, w ψ * ψ a) hFz
    _ = ∑ ψ : DirichletCharacter ℂ m, ‖w ψ‖ ^ 2 := by
        rw [synth_norm w]
        field_simp


set_option maxHeartbeats 800000 in
lemma contraction_ok (Nz : ZMod m) (s : Finset (DirichletCharacter ℂ m))
    (v : DirichletCharacter ℂ m → ℂ) :
    (∑ χ ∈ s, ‖∑ ψ ∈ s, Hm m Nz χ ψ * v ψ‖ ^ 2) ≤ ∑ χ ∈ s, ‖v χ‖ ^ 2 := by
  classical
  have hfilt : (Finset.univ : Finset (DirichletCharacter ℂ m)).filter (· ∈ s) = s := by
    ext ψ
    simp
  have hsub (f : DirichletCharacter ℂ m → ℂ) :
      ∑ ψ : DirichletCharacter ℂ m, f ψ * (if ψ ∈ s then v ψ else 0) = ∑ ψ ∈ s, f ψ * v ψ := by
    have h1 : ∀ ψ : DirichletCharacter ℂ m, f ψ * (if ψ ∈ s then v ψ else 0)
        = if ψ ∈ s then f ψ * v ψ else 0 := by
      intro ψ
      by_cases h : ψ ∈ s <;> simp [h]
    simp_rw [h1]
    rw [← Finset.sum_filter, hfilt]
  have hnorm : ∑ ψ : DirichletCharacter ℂ m, ‖(if ψ ∈ s then v ψ else 0)‖ ^ 2
      = ∑ ψ ∈ s, ‖v ψ‖ ^ 2 := by
    have h1 : ∀ ψ : DirichletCharacter ℂ m, ‖(if ψ ∈ s then v ψ else 0)‖ ^ 2
        = if ψ ∈ s then ‖v ψ‖ ^ 2 else 0 := by
      intro ψ
      by_cases h : ψ ∈ s <;> simp [h]
    simp_rw [h1]
    rw [← Finset.sum_filter, hfilt]
  have hmain : ∑ χ : DirichletCharacter ℂ m,
      ‖∑ ψ : DirichletCharacter ℂ m, Hm m Nz χ ψ * (if ψ ∈ s then v ψ else 0)‖ ^ 2
      ≤ ∑ ψ : DirichletCharacter ℂ m, ‖(if ψ ∈ s then v ψ else 0)‖ ^ 2 := by
    simpa only [Hm] using (main_bound Nz (fun ψ => if ψ ∈ s then v ψ else 0))
  calc (∑ χ ∈ s, ‖∑ ψ ∈ s, Hm m Nz χ ψ * v ψ‖ ^ 2)
      ≤ ∑ χ : DirichletCharacter ℂ m, ‖∑ ψ ∈ s, Hm m Nz χ ψ * v ψ‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
        intro i _ _
        exact sq_nonneg _
    _ = ∑ χ : DirichletCharacter ℂ m,
        ‖∑ ψ : DirichletCharacter ℂ m, Hm m Nz χ ψ * (if ψ ∈ s then v ψ else 0)‖ ^ 2 := by
      refine Finset.sum_congr rfl (fun χ _ => ?_)
      rw [hsub]
    _ ≤ ∑ ψ : DirichletCharacter ℂ m, ‖(if ψ ∈ s then v ψ else 0)‖ ^ 2 := hmain
    _ = ∑ χ ∈ s, ‖v χ‖ ^ 2 := hnorm

set_option maxHeartbeats 800000 in
lemma fiber_energy_ok (N : ℕ) (w : ℕ → ℂ) (s : Finset (DirichletCharacter ℂ m)) :
    (∑ χ ∈ s, ‖(∑ n ∈ Finset.range (N+1), w n * star (χ (n : ZMod m))) /
        (Real.sqrt (m.totient : ℝ) : ℂ)‖^2) ≤
      (1 + (N/m : ℕ) : ℝ) * ∑ n ∈ Finset.range (N+1), ‖w n‖^2 := by
  classical
  have hm : 0 < m := NeZero.pos m
  have hφ : (0 : ℝ) < (m.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm
  have hsqrt : ‖((Real.sqrt (m.totient : ℝ) : ℂ))‖ ^ 2 = (m.totient : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sq_sqrt (Nat.cast_nonneg m.totient)
  have hA : ∀ χ : DirichletCharacter ℂ m,
      (∑ n ∈ Finset.range (N+1), w n * star (χ (n : ZMod m))) =
        ∑ a : (ZMod m)ˣ, wsum m N w (a : ZMod m) * star (χ (a : ZMod m)) := by
    intro χ
    rw [fiber_sum m N (fun n => w n * star (χ (n : ZMod m)))]
    have h2 : ∀ r : ZMod m, (∑ n ∈ fibSet m N r, w n * star (χ (n : ZMod m))) =
        wsum m N w r * star (χ r) := by
      intro r
      have h3 : ∀ n ∈ fibSet m N r, w n * star (χ (n : ZMod m)) = w n * star (χ r) := by
        intro n hn
        rw [(mem_fiber m hn).2]
      calc (∑ n ∈ fibSet m N r, w n * star (χ (n : ZMod m)))
          = ∑ n ∈ fibSet m N r, w n * star (χ r) := Finset.sum_congr rfl h3
        _ = wsum m N w r * star (χ r) := by
            show ∑ n ∈ fibSet m N r, w n * star (χ r) = (∑ n ∈ fibSet m N r, w n) * star (χ r)
            rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun r _ => h2 r)]
    have h4 : ∀ r : ZMod m, ¬ IsUnit r → wsum m N w r * star (χ r) = 0 := by
      intro r hr
      rw [MulChar.map_nonunit χ hr, star_zero, mul_zero]
    exact (sum_units_eq m _ h4).symm
  have hP : (∑ χ : DirichletCharacter ℂ m,
      ‖∑ a : (ZMod m)ˣ, wsum m N w (a : ZMod m) * star (χ (a : ZMod m))‖ ^ 2) =
      (m.totient : ℝ) * ∑ a : (ZMod m)ˣ, ‖wsum m N w (a : ZMod m)‖ ^ 2 := parseval_starU m _
  have hbound : (∑ χ ∈ s, ‖(∑ n ∈ Finset.range (N+1), w n * star (χ (n : ZMod m))) /
      (Real.sqrt (m.totient : ℝ) : ℂ)‖ ^ 2) ≤
      ∑ a : (ZMod m)ˣ, ‖wsum m N w (a : ZMod m)‖ ^ 2 := by
    have hdiv : ∀ χ : DirichletCharacter ℂ m,
        ‖(∑ n ∈ Finset.range (N+1), w n * star (χ (n : ZMod m))) /
            (Real.sqrt (m.totient : ℝ) : ℂ)‖ ^ 2 =
          ‖∑ n ∈ Finset.range (N+1), w n * star (χ (n : ZMod m))‖ ^ 2 / (m.totient : ℝ) := by
      intro χ
      rw [norm_div, div_pow, hsqrt]
    have hsd : (∑ χ ∈ s, ‖∑ a : (ZMod m)ˣ, wsum m N w (a : ZMod m) *
        star (χ (a : ZMod m))‖ ^ 2 / (m.totient : ℝ)) =
        (∑ χ ∈ s, ‖∑ a : (ZMod m)ˣ, wsum m N w (a : ZMod m) *
          star (χ (a : ZMod m))‖ ^ 2) / (m.totient : ℝ) := by
      simp_rw [div_eq_mul_inv, Finset.sum_mul]
    have hsub : (∑ χ ∈ s, ‖∑ a : (ZMod m)ˣ, wsum m N w (a : ZMod m) *
        star (χ (a : ZMod m))‖ ^ 2) ≤
        ∑ χ : DirichletCharacter ℂ m, ‖∑ a : (ZMod m)ˣ, wsum m N w (a : ZMod m) *
          star (χ (a : ZMod m))‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun i _ _ => sq_nonneg _)
    simp_rw [hdiv, hA]
    rw [hsd, div_le_iff₀ hφ]
    calc (∑ χ ∈ s, ‖∑ a : (ZMod m)ˣ, wsum m N w (a : ZMod m) * star (χ (a : ZMod m))‖ ^ 2)
        ≤ ∑ χ : DirichletCharacter ℂ m, ‖∑ a : (ZMod m)ˣ, wsum m N w (a : ZMod m) *
            star (χ (a : ZMod m))‖ ^ 2 := hsub
      _ = (m.totient : ℝ) * ∑ a : (ZMod m)ˣ, ‖wsum m N w (a : ZMod m)‖ ^ 2 := hP
      _ = (∑ a : (ZMod m)ˣ, ‖wsum m N w (a : ZMod m)‖ ^ 2) * (m.totient : ℝ) := by ring
  have hfin : (∑ r : ZMod m, ‖wsum m N w r‖ ^ 2) ≤
      (1 + (N / m : ℕ) : ℝ) * ∑ n ∈ Finset.range (N+1), ‖w n‖ ^ 2 := by
    have hcs : ∀ r : ZMod m, ‖wsum m N w r‖ ^ 2 ≤
        ((fibSet m N r).card : ℝ) * ∑ n ∈ fibSet m N r, ‖w n‖ ^ 2 := by
      intro r
      exact cs_sum (fibSet m N r) w
    calc (∑ r : ZMod m, ‖wsum m N w r‖ ^ 2)
        ≤ ∑ r : ZMod m, ((fibSet m N r).card : ℝ) * ∑ n ∈ fibSet m N r, ‖w n‖ ^ 2 :=
          Finset.sum_le_sum (fun r _ => hcs r)
      _ ≤ ∑ r : ZMod m, (1 + (N / m : ℕ) : ℝ) * ∑ n ∈ fibSet m N r, ‖w n‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro r _
          apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun n _ => sq_nonneg _))
          calc ((fibSet m N r).card : ℝ) ≤ ((1 + N / m : ℕ) : ℝ) := by exact_mod_cast fiber_card m N r
            _ = (1 + (N / m : ℕ) : ℝ) := by simp
      _ = (1 + (N / m : ℕ) : ℝ) * ∑ r : ZMod m, ∑ n ∈ fibSet m N r, ‖w n‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ = (1 + (N / m : ℕ) : ℝ) * ∑ n ∈ Finset.range (N+1), ‖w n‖ ^ 2 := by
          rw [fiber_sum m N]
  calc (∑ χ ∈ s, ‖(∑ n ∈ Finset.range (N+1), w n * star (χ (n : ZMod m))) /
      (Real.sqrt (m.totient : ℝ) : ℂ)‖ ^ 2)
      ≤ ∑ a : (ZMod m)ˣ, ‖wsum m N w (a : ZMod m)‖ ^ 2 := hbound
    _ ≤ ∑ r : ZMod m, ‖wsum m N w r‖ ^ 2 := sum_units_le m _ (fun r => sq_nonneg _)
    _ ≤ (1 + (N / m : ℕ) : ℝ) * ∑ n ∈ Finset.range (N+1), ‖w n‖ ^ 2 := hfin

set_option maxHeartbeats 800000 in
lemma bf_bound (Nz : ZMod m) (s : Finset (DirichletCharacter ℂ m))
    (u w : DirichletCharacter ℂ m → ℂ) :
    ‖Bf m Nz s u w‖ ≤
      Real.sqrt (∑ χ ∈ s, ‖u χ‖ ^ 2) * Real.sqrt (∑ χ ∈ s, ‖w χ‖ ^ 2) := by
  have hb : Bf m Nz s u w = ∑ χ ∈ s, star (u χ) * (∑ ψ ∈ s, Hm m Nz χ ψ * w ψ) := by
    simp only [Bf]
    apply Finset.sum_congr rfl
    intro χ _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ψ _
    ring
  rw [hb]
  refine (cs_bound s u (fun χ => ∑ ψ ∈ s, Hm m Nz χ ψ * w ψ)).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (contraction_ok Nz s w)) (Real.sqrt_nonneg _)

set_option maxHeartbeats 800000 in
lemma layer_bound (Nz : ZMod m) (s : Finset (DirichletCharacter ℂ m))
    (v z : DirichletCharacter ℂ m → ℂ) (Ev : ℝ) (hEv : 0 ≤ Ev)
    (hd : (∑ χ ∈ s, ‖v χ - z χ‖ ^ 2) ≤ Ev ^ 2) :
    |Qf m Nz s v - Qf m Nz s z| ≤
      2 * Ev * Real.sqrt (∑ χ ∈ s, ‖v χ‖ ^ 2) + Ev ^ 2 := by
  have hdv : (∑ χ ∈ s, ‖(v - z) χ‖ ^ 2) ≤ Ev ^ 2 := by
    simpa only [Pi.sub_apply] using hd
  have h1 : Bf m Nz s v (v - z) = Bf m Nz s v v - Bf m Nz s v z := bf_sub_right m Nz s v v z
  have h2 : Bf m Nz s (v - z) v = Bf m Nz s v v - Bf m Nz s z v := bf_sub_left m Nz s v z v
  have h3 : Bf m Nz s (v - z) (v - z) = Bf m Nz s v (v - z) - Bf m Nz s z (v - z) :=
    bf_sub_left m Nz s v z (v - z)
  have h4 : Bf m Nz s z (v - z) = Bf m Nz s z v - Bf m Nz s z z := bf_sub_right m Nz s z v z
  have hdec : Bf m Nz s v v - Bf m Nz s z z =
      Bf m Nz s v (v - z) + Bf m Nz s (v - z) v - Bf m Nz s (v - z) (v - z) := by
    rw [h3, h4, h1, h2]
    ring
  have hQ : Qf m Nz s v - Qf m Nz s z = (Bf m Nz s v v - Bf m Nz s z z).re := by
    simp [Qf, Complex.sub_re]
  have e1 := bf_bound Nz s v (v - z)
  have e2 := bf_bound Nz s (v - z) v
  have e3 := bf_bound Nz s (v - z) (v - z)
  have hB : Real.sqrt (∑ χ ∈ s, ‖(v - z) χ‖ ^ 2) ≤ Ev := by
    rw [← Real.sqrt_sq hEv]
    exact Real.sqrt_le_sqrt hdv
  have hA : (0 : ℝ) ≤ Real.sqrt (∑ χ ∈ s, ‖v χ‖ ^ 2) := Real.sqrt_nonneg _
  have hB0 : (0 : ℝ) ≤ Real.sqrt (∑ χ ∈ s, ‖(v - z) χ‖ ^ 2) := Real.sqrt_nonneg _
  have habs : |(Bf m Nz s v (v - z) + Bf m Nz s (v - z) v - Bf m Nz s (v - z) (v - z)).re|
      ≤ ‖Bf m Nz s v (v - z)‖ + ‖Bf m Nz s (v - z) v‖ + ‖Bf m Nz s (v - z) (v - z)‖ := by
    have t1 := Complex.abs_re_le_norm (Bf m Nz s v (v - z) + Bf m Nz s (v - z) v -
      Bf m Nz s (v - z) (v - z))
    have t2 := norm_sub_le (Bf m Nz s v (v - z) + Bf m Nz s (v - z) v)
      (Bf m Nz s (v - z) (v - z))
    have t3 := norm_add_le (Bf m Nz s v (v - z)) (Bf m Nz s (v - z) v)
    linarith
  rw [hQ, hdec]
  have hstep : Real.sqrt (∑ χ ∈ s, ‖v χ‖ ^ 2) * Real.sqrt (∑ χ ∈ s, ‖(v - z) χ‖ ^ 2) +
      Real.sqrt (∑ χ ∈ s, ‖(v - z) χ‖ ^ 2) * Real.sqrt (∑ χ ∈ s, ‖v χ‖ ^ 2) +
      Real.sqrt (∑ χ ∈ s, ‖(v - z) χ‖ ^ 2) * Real.sqrt (∑ χ ∈ s, ‖(v - z) χ‖ ^ 2)
      ≤ Real.sqrt (∑ χ ∈ s, ‖v χ‖ ^ 2) * Ev + Ev * Real.sqrt (∑ χ ∈ s, ‖v χ‖ ^ 2) + Ev * Ev := by
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hB hA)
      (mul_le_mul_of_nonneg_right hB hA)) (mul_le_mul hB hB hB0 hEv)
  calc |(Bf m Nz s v (v - z) + Bf m Nz s (v - z) v - Bf m Nz s (v - z) (v - z)).re|
      ≤ ‖Bf m Nz s v (v - z)‖ + ‖Bf m Nz s (v - z) v‖ + ‖Bf m Nz s (v - z) (v - z)‖ := habs
    _ ≤ Real.sqrt (∑ χ ∈ s, ‖v χ‖ ^ 2) * Real.sqrt (∑ χ ∈ s, ‖(v - z) χ‖ ^ 2) +
        Real.sqrt (∑ χ ∈ s, ‖(v - z) χ‖ ^ 2) * Real.sqrt (∑ χ ∈ s, ‖v χ‖ ^ 2) +
        Real.sqrt (∑ χ ∈ s, ‖(v - z) χ‖ ^ 2) * Real.sqrt (∑ χ ∈ s, ‖(v - z) χ‖ ^ 2) := by
      exact add_le_add (add_le_add e1 e2) e3
    _ ≤ Real.sqrt (∑ χ ∈ s, ‖v χ‖ ^ 2) * Ev + Ev * Real.sqrt (∑ χ ∈ s, ‖v χ‖ ^ 2) + Ev * Ev :=
      hstep
    _ = 2 * Ev * Real.sqrt (∑ χ ∈ s, ‖v χ‖ ^ 2) + Ev ^ 2 := by ring

set_option maxHeartbeats 800000 in
lemma v_energy (N : ℕ) (w : ℕ → ℝ) (s : Finset (DirichletCharacter ℂ m)) :
    (∑ χ ∈ s, ‖(∑ n ∈ Finset.range (N + 1), (w n : ℂ) * star (χ (n : ZMod m))) /
        (Real.sqrt (m.totient : ℝ) : ℂ)‖ ^ 2) ≤
      (1 + (N / m : ℕ) : ℝ) * ∑ n ∈ Finset.range (N + 1), (w n) ^ 2 := by
  have h := fiber_energy_ok N (fun n => (w n : ℂ)) s
  have hc : (∑ n ∈ Finset.range (N + 1), ‖((w n : ℂ))‖ ^ 2)
      = ∑ n ∈ Finset.range (N + 1), (w n) ^ 2 := by
    apply Finset.sum_congr rfl
    intro n _
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h2 : (∑ χ ∈ s, ‖(∑ n ∈ Finset.range (N + 1), (w n : ℂ) * star (χ (n : ZMod m))) /
      (Real.sqrt (m.totient : ℝ) : ℂ)‖ ^ 2) ≤
      (1 + (N / m : ℕ) : ℝ) * ∑ n ∈ Finset.range (N + 1), ‖((w n : ℂ))‖ ^ 2 := h
  rw [hc] at h2
  exact h2

lemma weight_sqrt (N K k : ℕ) (hNK : N < 2 ^ K) (hk : k < K) :
    ((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ) *
        Real.sqrt (1 + (N : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ)) ≤
      Real.sqrt (2 : ℝ) * (Real.sqrt (1 / 2 : ℝ)) ^ (K - 1 - k) := by
  have hmM : ((2 ^ (k + 1) : ℕ) : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) := by
    have hh : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ K :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have e1 : ((2 ^ (k + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (k + 1) := by rw [Nat.cast_pow]; norm_num
    have e2 : ((2 ^ K : ℕ) : ℝ) = (2 : ℝ) ^ K := by rw [Nat.cast_pow]; norm_num
    rw [e1, e2]
    exact hh
  have hMpos : (0 : ℝ) < ((2 ^ K : ℕ) : ℝ) := by positivity
  have hmpos : (0 : ℝ) < ((2 ^ (k + 1) : ℕ) : ℝ) := by positivity
  have hNM : (N : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) := by
    have hx : (N : ℝ) < ((2 ^ K : ℕ) : ℝ) := by exact_mod_cast hNK
    linarith
  have hcore := weight_core ((2 ^ (k + 1) : ℕ) : ℝ) ((2 ^ K : ℕ) : ℝ) (N : ℝ)
    hmpos hMpos hmM hNM
  have ht : (0 : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ) := by positivity
  have hsqrt : ((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ) *
      Real.sqrt (1 + (N : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ)) =
      Real.sqrt ((((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)) ^ 2 *
        (1 + (N : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ))) := by
    rw [Real.sqrt_mul (sq_nonneg (((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)))
      (1 + (N : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ)), Real.sqrt_sq ht]
  rw [hsqrt]
  refine le_trans (Real.sqrt_le_sqrt hcore) ?_
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg 2)
  rw [pow_div_pow k K hk]
  exact le_of_eq (sqrt_pow_real (1 / 2) (by norm_num) (K - 1 - k))

lemma sum_weight_le (N K : ℕ) (S : Finset ℕ) (hNK : N < 2 ^ K) (hS : ∀ k ∈ S, k < K) :
    (∑ k ∈ S, ((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ) *
        Real.sqrt (1 + (N : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ))) ≤ 5 := by
  have h1 : (∑ k ∈ S, ((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ) *
        Real.sqrt (1 + (N : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ))) ≤
      ∑ k ∈ S, Real.sqrt (2 : ℝ) * (Real.sqrt (1 / 2 : ℝ)) ^ (K - 1 - k) := by
    apply Finset.sum_le_sum
    intro k hk
    exact weight_sqrt N K k hNK (hS k hk)
  have hr0 : (0 : ℝ) ≤ Real.sqrt (1 / 2 : ℝ) := Real.sqrt_nonneg _
  have hr1 : Real.sqrt (1 / 2 : ℝ) < 1 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
    norm_num
  have h3 : (∑ k ∈ S, (Real.sqrt (1 / 2 : ℝ)) ^ (K - 1 - k)) ≤
      ∑ k ∈ Finset.range K, (Real.sqrt (1 / 2 : ℝ)) ^ (K - 1 - k) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      exact Finset.mem_range.mpr (hS k hk)
    · intro i _ _
      exact pow_nonneg hr0 _
  have h4 : (∑ k ∈ Finset.range K, (Real.sqrt (1 / 2 : ℝ)) ^ (K - 1 - k)) =
      ∑ j ∈ Finset.range K, (Real.sqrt (1 / 2 : ℝ)) ^ j :=
    Finset.sum_range_reflect _ K
  have h5 : (∑ j ∈ Finset.range K, (Real.sqrt (1 / 2 : ℝ)) ^ j) ≤
      1 / (1 - Real.sqrt (1 / 2 : ℝ)) := geom_le _ hr0 hr1 K
  calc (∑ k ∈ S, ((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ) *
        Real.sqrt (1 + (N : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ)))
      ≤ ∑ k ∈ S, Real.sqrt (2 : ℝ) * (Real.sqrt (1 / 2 : ℝ)) ^ (K - 1 - k) := h1
    _ = Real.sqrt (2 : ℝ) * (∑ k ∈ S, (Real.sqrt (1 / 2 : ℝ)) ^ (K - 1 - k)) :=
      (Finset.mul_sum S (fun k => (Real.sqrt (1 / 2 : ℝ)) ^ (K - 1 - k)) (Real.sqrt 2)).symm
    _ ≤ Real.sqrt (2 : ℝ) * (1 / (1 - Real.sqrt (1 / 2 : ℝ))) := by
      have hx : (∑ k ∈ S, (Real.sqrt (1 / 2 : ℝ)) ^ (K - 1 - k)) ≤
          1 / (1 - Real.sqrt (1 / 2 : ℝ)) := le_trans (le_trans h3 (le_of_eq h4)) h5
      exact mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg 2)
    _ ≤ 5 := sqrt_two_div_le

lemma sum_weight_sq_le (K : ℕ) (S : Finset ℕ) (hS : ∀ k ∈ S, k < K) :
    (∑ k ∈ S, ((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)) ≤ 2 := by
  have h1 : (∑ k ∈ S, ((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ K : ℕ) : ℝ)) =
      ∑ k ∈ S, (1 / 2 : ℝ) ^ (K - 1 - k) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact pow_div_pow k K (hS k hk)
  have h3 : (∑ k ∈ S, (1 / 2 : ℝ) ^ (K - 1 - k)) ≤
      ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ (K - 1 - k) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      exact Finset.mem_range.mpr (hS k hk)
    · intro i _ _
      exact pow_nonneg (by norm_num) _
  have h4 : (∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ (K - 1 - k)) =
      ∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ j :=
    Finset.sum_range_reflect _ K
  have h5 : (∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ j) ≤ 1 / (1 - (1 / 2 : ℝ)) :=
    geom_le (1 / 2) (by norm_num) (by norm_num) K
  rw [h1]
  calc (∑ k ∈ S, (1 / 2 : ℝ) ^ (K - 1 - k)) ≤ ∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ j :=
        le_trans h3 (le_of_eq h4)
    _ ≤ 1 / (1 - (1 / 2 : ℝ)) := h5
    _ = 2 := by norm_num

set_option maxHeartbeats 800000 in
lemma main_abstract
    (N K : ℕ) (S : Finset ℕ) (w : ℕ → ℝ) (E : ℝ)
    (s : (k : ℕ) → Finset (DirichletCharacter ℂ (2^(k+1))))
    (v : (k : ℕ) → DirichletCharacter ℂ (2^(k+1)) → ℂ)
    (z : (k : ℕ) → DirichletCharacter ℂ (2^(k+1)) → ℂ)
    (hv : ∀ (k : ℕ) (χ : DirichletCharacter ℂ (2^(k+1))),
      v k χ = (∑ n ∈ Finset.range (N+1), (w n : ℂ) * star (χ (n : ZMod (2^(k+1))))) /
        (Real.sqrt (((2^(k+1) : ℕ).totient) : ℝ) : ℂ))
    (hNK : N < 2^K) (hE : 0 ≤ E) (hS : ∀ k ∈ S, 1 ≤ k ∧ k < K)
    (hbound : ∀ k ∈ S, (∑ χ ∈ s k, ‖v k χ-z k χ‖^2) ≤ E^2) :
    |∑ k ∈ S, ((2^(k+1) : ℕ) : ℝ) / ((2^K : ℕ) : ℝ) *
        (Qf (2^(k+1)) ((N : ZMod (2^(k+1)))) (s k) (v k) -
         Qf (2^(k+1)) ((N : ZMod (2^(k+1)))) (s k) (z k))| ≤
      10 * E * Real.sqrt (∑ n ∈ Finset.range (N+1), (w n)^2) + 2*E^2 := by
  have hNe : ∀ k : ℕ, NeZero (2^(k+1)) := fun k => ⟨ne_of_gt (by positivity)⟩
  have hwn : ∀ k : ℕ, (0 : ℝ) ≤ ((2^(k+1) : ℕ) : ℝ) / ((2^K : ℕ) : ℝ) :=
    fun k => by positivity
  have hlayer : ∀ k ∈ S, |Qf (2^(k+1)) ((N : ZMod (2^(k+1)))) (s k) (v k) -
      Qf (2^(k+1)) ((N : ZMod (2^(k+1)))) (s k) (z k)| ≤
      2 * E * Real.sqrt (∑ χ ∈ s k, ‖v k χ‖ ^ 2) + E ^ 2 := by
    intro k hk
    haveI : NeZero (2^(k+1)) := hNe k
    exact layer_bound ((N : ZMod (2^(k+1)))) (s k) (v k) (z k) E hE (hbound k hk)
  have hW2 : (0 : ℝ) ≤ ∑ n ∈ Finset.range (N + 1), (w n) ^ 2 :=
    Finset.sum_nonneg (fun n _ => sq_nonneg _)
  have hW : (0 : ℝ) ≤ Real.sqrt (∑ n ∈ Finset.range (N + 1), (w n) ^ 2) := Real.sqrt_nonneg _
  have hvE : ∀ k ∈ S, Real.sqrt (∑ χ ∈ s k, ‖v k χ‖ ^ 2) ≤
      Real.sqrt (1 + (N : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ)) *
        Real.sqrt (∑ n ∈ Finset.range (N + 1), (w n) ^ 2) := by
    intro k hk
    haveI : NeZero (2^(k+1)) := hNe k
    have hfe := v_energy (m := 2^(k+1)) N w (s k)
    have hfe' : (∑ χ ∈ s k, ‖v k χ‖ ^ 2) ≤
        (1 + (N / 2^(k+1) : ℕ) : ℝ) * ∑ n ∈ Finset.range (N + 1), (w n) ^ 2 := by
      have hcong : ∀ χ : DirichletCharacter ℂ (2^(k+1)),
          ‖v k χ‖ ^ 2 = ‖(∑ n ∈ Finset.range (N + 1), (w n : ℂ) *
              star (χ (n : ZMod (2^(k+1))))) /
            (Real.sqrt (((2^(k+1) : ℕ).totient) : ℝ) : ℂ)‖ ^ 2 := by
        intro χ
        rw [hv k χ]
      calc (∑ χ ∈ s k, ‖v k χ‖ ^ 2)
          = ∑ χ ∈ s k, ‖(∑ n ∈ Finset.range (N + 1), (w n : ℂ) *
              star (χ (n : ZMod (2^(k+1))))) /
            (Real.sqrt (((2^(k+1) : ℕ).totient) : ℝ) : ℂ)‖ ^ 2 :=
            Finset.sum_congr rfl (fun χ _ => hcong χ)
        _ ≤ (1 + (N / 2^(k+1) : ℕ) : ℝ) * ∑ n ∈ Finset.range (N + 1), (w n) ^ 2 := hfe
    have h1n : (1 + (N / 2^(k+1) : ℕ) : ℝ) ≤ 1 + (N : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ) := by
      have hcd : ((N / 2^(k+1) : ℕ) : ℝ) ≤ (N : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ) :=
        Nat.cast_div_le (α := ℝ)
      linarith
    calc Real.sqrt (∑ χ ∈ s k, ‖v k χ‖ ^ 2)
        ≤ Real.sqrt ((1 + (N / 2^(k+1) : ℕ) : ℝ) * ∑ n ∈ Finset.range (N + 1), (w n) ^ 2) :=
          Real.sqrt_le_sqrt hfe'
      _ ≤ Real.sqrt ((1 + (N : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ)) *
            ∑ n ∈ Finset.range (N + 1), (w n) ^ 2) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right h1n hW2)
      _ = Real.sqrt (1 + (N : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ)) *
            Real.sqrt (∑ n ∈ Finset.range (N + 1), (w n) ^ 2) :=
          Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 1 + (N : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ)) _
  calc |∑ k ∈ S, ((2^(k+1) : ℕ) : ℝ) / ((2^K : ℕ) : ℝ) *
        (Qf (2^(k+1)) ((N : ZMod (2^(k+1)))) (s k) (v k) -
         Qf (2^(k+1)) ((N : ZMod (2^(k+1)))) (s k) (z k))|
      ≤ ∑ k ∈ S, |((2^(k+1) : ℕ) : ℝ) / ((2^K : ℕ) : ℝ) *
        (Qf (2^(k+1)) ((N : ZMod (2^(k+1)))) (s k) (v k) -
         Qf (2^(k+1)) ((N : ZMod (2^(k+1)))) (s k) (z k))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ S, ((2^(k+1) : ℕ) : ℝ) / ((2^K : ℕ) : ℝ) *
        |Qf (2^(k+1)) ((N : ZMod (2^(k+1)))) (s k) (v k) -
         Qf (2^(k+1)) ((N : ZMod (2^(k+1)))) (s k) (z k)| := by
        apply Finset.sum_congr rfl
        intro k _
        rw [abs_mul, abs_of_nonneg (hwn k)]
    _ ≤ ∑ k ∈ S, ((2^(k+1) : ℕ) : ℝ) / ((2^K : ℕ) : ℝ) *
        (2 * E * Real.sqrt (∑ χ ∈ s k, ‖v k χ‖ ^ 2) + E ^ 2) := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_left (hlayer k hk) (hwn k)
    _ ≤ ∑ k ∈ S, ((2^(k+1) : ℕ) : ℝ) / ((2^K : ℕ) : ℝ) *
        (2 * E * (Real.sqrt (1 + (N : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ)) *
          Real.sqrt (∑ n ∈ Finset.range (N + 1), (w n) ^ 2)) + E ^ 2) := by
        apply Finset.sum_le_sum
        intro k hk
        have h2E : (0 : ℝ) ≤ 2 * E := by linarith
        have hstep : 2 * E * Real.sqrt (∑ χ ∈ s k, ‖v k χ‖ ^ 2) + E ^ 2 ≤
            2 * E * (Real.sqrt (1 + (N : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ)) *
              Real.sqrt (∑ n ∈ Finset.range (N + 1), (w n) ^ 2)) + E ^ 2 := by
          exact add_le_add (mul_le_mul_of_nonneg_left (hvE k hk) h2E) (le_refl _)
        exact mul_le_mul_of_nonneg_left hstep (hwn k)
    _ = 2 * E * Real.sqrt (∑ n ∈ Finset.range (N + 1), (w n) ^ 2) *
          (∑ k ∈ S, ((2^(k+1) : ℕ) : ℝ) / ((2^K : ℕ) : ℝ) *
            Real.sqrt (1 + (N : ℝ) / ((2 ^ (k + 1) : ℕ) : ℝ))) +
        E ^ 2 * (∑ k ∈ S, ((2^(k+1) : ℕ) : ℝ) / ((2^K : ℕ) : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ 2 * E * Real.sqrt (∑ n ∈ Finset.range (N + 1), (w n) ^ 2) * 5 + E ^ 2 * 2 := by
      have hA := sum_weight_le N K S hNK (fun k hk => (hS k hk).2)
      have hB := sum_weight_sq_le K S (fun k hk => (hS k hk).2)
      have h2EW : (0 : ℝ) ≤ 2 * E * Real.sqrt (∑ n ∈ Finset.range (N + 1), (w n) ^ 2) :=
        mul_nonneg (mul_nonneg (by linarith) hE) hW
      have t1 := mul_le_mul_of_nonneg_left hA h2EW
      have t2 := mul_le_mul_of_nonneg_left hB (sq_nonneg E)
      linarith
    _ = 10 * E * Real.sqrt (∑ n ∈ Finset.range (N + 1), (w n) ^ 2) + 2 * E ^ 2 := by ring

end Conjectures.Goldbach.DyadicTruncationFormBudget_aux

open Conjectures.Goldbach.DyadicTruncationFormBudget_aux

set_option maxHeartbeats 800000 in
theorem Conjectures.Goldbach.DyadicTruncationFormBudget :
  ∀ (N K : ℕ) (S : Finset ℕ) (w : ℕ → ℝ)
    (z : (k : ℕ) → DirichletCharacter ℂ (2^(k+1)) → ℂ) (E : ℝ),
  N < 2^K → 0 ≤ E → (∀ k ∈ S, 1 ≤ k ∧ k < K) →
  let s := fun k : ℕ => (Finset.univ : Finset (DirichletCharacter ℂ (2^(k+1)))).filter (fun χ => χ.conductor = 2^(k+1))
  let v := fun (k : ℕ) (χ : DirichletCharacter ℂ (2^(k+1))) =>
    (∑ n ∈ Finset.range (N+1), (w n : ℂ) * star (χ (n : ZMod (2^(k+1))))) /
      (Real.sqrt (((2^(k+1) : ℕ).totient) : ℝ) : ℂ)
  let R := fun (k : ℕ) (a : DirichletCharacter ℂ (2^(k+1)) → ℂ) =>
    (∑ χ ∈ s k, ∑ ψ ∈ s k, star (a χ) *
      ((∑ x : (ZMod (2^(k+1)))ˣ, star (χ (x : ZMod (2^(k+1)))) * ψ ((N : ZMod (2^(k+1))) - (x : ZMod (2^(k+1))))) /
        (((2^(k+1) : ℕ).totient) : ℂ)) * a ψ).re
  (∀ k ∈ S, (∑ χ ∈ s k, ‖v k χ-z k χ‖^2) ≤ E^2) →
    |∑ k ∈ S, ((2^(k+1) : ℕ) : ℝ) / ((2^K : ℕ) : ℝ) * (R k (v k) - R k (z k))| ≤
      10 * E * Real.sqrt (∑ n ∈ Finset.range (N+1), (w n)^2) + 2*E^2 := by
  intro N K S w z E hNK hE hS
  simp only []
  intro hbound
  exact main_abstract N K S w E
    (fun k : ℕ => (Finset.univ : Finset (DirichletCharacter ℂ (2^(k+1)))).filter
      (fun χ => χ.conductor = 2^(k+1)))
    (fun (k : ℕ) (χ : DirichletCharacter ℂ (2^(k+1))) =>
      (∑ n ∈ Finset.range (N+1), (w n : ℂ) * star (χ (n : ZMod (2^(k+1))))) /
        (Real.sqrt (((2^(k+1) : ℕ).totient) : ℝ) : ℂ))
    z (fun k χ => rfl) hNK hE hS hbound
