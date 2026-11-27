import Mathlib

open scoped Classical

namespace Conjectures.Goldbach.CharacterWindowFiberEnergy_aux

def fiber (m : ℕ) (N : ℕ) (r : ZMod m) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun n => (n : ZMod m) = r)

def wsum (m : ℕ) (N : ℕ) (w : ℕ → ℂ) (r : ZMod m) : ℂ :=
  ∑ n ∈ fiber m N r, w n

theorem mem_fiber (m : ℕ) [NeZero m] {N : ℕ} {r : ZMod m} {n : ℕ} (hn : n ∈ fiber m N r) :
    n < N + 1 ∧ (n : ZMod m) = r := by
  simp only [fiber, Finset.mem_filter, Finset.mem_range] at hn
  exact hn

theorem fiber_card (m : ℕ) [NeZero m] (N : ℕ) (r : ZMod m) : (fiber m N r).card ≤ 1 + N / m := by
  have hinj : Set.InjOn (fun n : ℕ => n / m) (fiber m N r : Set ℕ) := by
    intro a ha b hb hab
    replace hab : a / m = b / m := hab
    have ha' := mem_fiber m ha
    have hb' := mem_fiber m hb
    have hmod : a % m = b % m :=
      (ZMod.natCast_eq_natCast_iff' a b m).mp (by rw [ha'.2, hb'.2])
    calc a = m * (a / m) + a % m := (Nat.div_add_mod a m).symm
      _ = m * (b / m) + b % m := by rw [hab, hmod]
      _ = b := Nat.div_add_mod b m
  have himg : (fiber m N r).image (fun n : ℕ => n / m) ⊆ Finset.range (1 + N / m) := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    have h1 := (mem_fiber m hn).1
    have h2 : n / m ≤ N / m := Nat.div_le_div_right (Nat.le_of_lt_succ h1)
    exact Finset.mem_range.mpr (by omega)
  calc (fiber m N r).card = ((fiber m N r).image (fun n : ℕ => n / m)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (1 + N / m)).card := Finset.card_le_card himg
    _ = 1 + N / m := Finset.card_range _

theorem fiber_sum (m : ℕ) [NeZero m] (N : ℕ) {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    (∑ n ∈ Finset.range (N + 1), f n) = ∑ r : ZMod m, ∑ n ∈ fiber m N r, f n := by
  have h1 : ∀ n ∈ Finset.range (N + 1), f n = ∑ r : ZMod m, if (n : ZMod m) = r then f n else 0 := by
    intro n _
    simp
  calc (∑ n ∈ Finset.range (N + 1), f n)
      = ∑ n ∈ Finset.range (N + 1), ∑ r : ZMod m, if (n : ZMod m) = r then f n else 0 :=
        Finset.sum_congr rfl h1
    _ = ∑ r : ZMod m, ∑ n ∈ Finset.range (N + 1), if (n : ZMod m) = r then f n else 0 :=
        Finset.sum_comm
    _ = ∑ r : ZMod m, ∑ n ∈ fiber m N r, f n := by
        apply Finset.sum_congr rfl
        intro r _
        rw [fiber, Finset.sum_filter]

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

theorem orth2 (m : ℕ) [NeZero m] (a b : (ZMod m)ˣ) :
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

theorem parseval_star (m : ℕ) [NeZero m] (G : (ZMod m)ˣ → ℂ) :
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
    simp_rw [← Finset.mul_sum, orth2 m]
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

end Conjectures.Goldbach.CharacterWindowFiberEnergy_aux

open Conjectures.Goldbach.CharacterWindowFiberEnergy_aux

theorem Conjectures.Goldbach.CharacterWindowFiberEnergy :
    ∀ (m : ℕ) [NeZero m] (N : ℕ) (w : ℕ → ℂ) (s : Finset (DirichletCharacter ℂ m)),
      (∑ χ ∈ s, ‖(∑ n ∈ Finset.range (N+1), w n * star (χ (n : ZMod m))) /
          (Real.sqrt (m.totient : ℝ) : ℂ)‖^2) ≤
        (1 + (N/m : ℕ) : ℝ) * ∑ n ∈ Finset.range (N+1), ‖w n‖^2 := by
  intro m _ N w s
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
    have h2 : ∀ r : ZMod m, (∑ n ∈ fiber m N r, w n * star (χ (n : ZMod m))) =
        wsum m N w r * star (χ r) := by
      intro r
      have h3 : ∀ n ∈ fiber m N r, w n * star (χ (n : ZMod m)) = w n * star (χ r) := by
        intro n hn
        rw [(mem_fiber m hn).2]
      calc (∑ n ∈ fiber m N r, w n * star (χ (n : ZMod m)))
          = ∑ n ∈ fiber m N r, w n * star (χ r) := Finset.sum_congr rfl h3
        _ = wsum m N w r * star (χ r) := by
            show ∑ n ∈ fiber m N r, w n * star (χ r) = (∑ n ∈ fiber m N r, w n) * star (χ r)
            rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun r _ => h2 r)]
    have h4 : ∀ r : ZMod m, ¬ IsUnit r → wsum m N w r * star (χ r) = 0 := by
      intro r hr
      rw [MulChar.map_nonunit χ hr, star_zero, mul_zero]
    exact (sum_units_eq m _ h4).symm
  have hP : (∑ χ : DirichletCharacter ℂ m,
      ‖∑ a : (ZMod m)ˣ, wsum m N w (a : ZMod m) * star (χ (a : ZMod m))‖ ^ 2) =
      (m.totient : ℝ) * ∑ a : (ZMod m)ˣ, ‖wsum m N w (a : ZMod m)‖ ^ 2 := parseval_star m _
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
        ((fiber m N r).card : ℝ) * ∑ n ∈ fiber m N r, ‖w n‖ ^ 2 := by
      intro r
      exact cs_sum (fiber m N r) w
    calc (∑ r : ZMod m, ‖wsum m N w r‖ ^ 2)
        ≤ ∑ r : ZMod m, ((fiber m N r).card : ℝ) * ∑ n ∈ fiber m N r, ‖w n‖ ^ 2 :=
          Finset.sum_le_sum (fun r _ => hcs r)
      _ ≤ ∑ r : ZMod m, (1 + (N / m : ℕ) : ℝ) * ∑ n ∈ fiber m N r, ‖w n‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro r _
          apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun n _ => sq_nonneg _))
          calc ((fiber m N r).card : ℝ) ≤ ((1 + N / m : ℕ) : ℝ) := by exact_mod_cast fiber_card m N r
            _ = (1 + (N / m : ℕ) : ℝ) := by simp
      _ = (1 + (N / m : ℕ) : ℝ) * ∑ r : ZMod m, ∑ n ∈ fiber m N r, ‖w n‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ = (1 + (N / m : ℕ) : ℝ) * ∑ n ∈ Finset.range (N+1), ‖w n‖ ^ 2 := by
          rw [fiber_sum m N]
  calc (∑ χ ∈ s, ‖(∑ n ∈ Finset.range (N+1), w n * star (χ (n : ZMod m))) /
      (Real.sqrt (m.totient : ℝ) : ℂ)‖ ^ 2)
      ≤ ∑ a : (ZMod m)ˣ, ‖wsum m N w (a : ZMod m)‖ ^ 2 := hbound
    _ ≤ ∑ r : ZMod m, ‖wsum m N w r‖ ^ 2 := sum_units_le m _ (fun r => sq_nonneg _)
    _ ≤ (1 + (N / m : ℕ) : ℝ) * ∑ n ∈ Finset.range (N+1), ‖w n‖ ^ 2 := hfin
