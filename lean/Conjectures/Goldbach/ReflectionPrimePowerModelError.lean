import Mathlib

/- Apache-2.0, goldbach-proofs. Private adaptations of SaladDay's reflection
   contraction (50fd7ec88aaaf867ea08c0532f3ddf5d160804a6) and yidaoxiangan's
   power-index count (3efb5e66b3e688e15321c9c87767432fce3bcdd8). The fiber
   estimate is from 26day's own local draft, SHA-256
   d203ccdf9a3e66f49f8f9d77afb7704e0594e38f875b29010be6e12ceac521cf.
   The bilinear perturbation estimate and its application to prime powers are new. -/


open scoped Classical

namespace ReflectionModelAux

variable {m : ℕ} [NeZero m]

private lemma totient_pos_real : (0 : ℝ) < (m.totient : ℝ) := by
  exact_mod_cast Nat.totient_pos.mpr (NeZero.pos m)

private lemma totient_cast : ((m.totient : ℕ) : ℂ) = ((m.totient : ℝ) : ℂ) := by
  simp

private lemma star_mul_self (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]

private lemma sum_interchange {α β : Type*} [Fintype α] [Fintype β] {M : Type*} [AddCommMonoid M]
    (f : α → β → M) : (∑ a : α, ∑ b : β, f a b) = ∑ b : β, ∑ a : α, f a b := by
  conv_lhs => rw [Finset.sum_comm]

private lemma sum_units_eq_sum {M : Type*} [AddCommMonoid M] (f : ZMod m → M)
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

private lemma sum_char_units (θ : DirichletCharacter ℂ m) :
    ∑ x : (ZMod m)ˣ, θ (x : ZMod m) = if θ = 1 then ((m.totient : ℝ) : ℂ) else 0 := by
  have hz : ∀ a : ZMod m, ¬IsUnit a → θ a = 0 := fun a ha => MulChar.map_nonunit θ ha
  rw [sum_units_eq_sum (fun a => θ a) hz]
  by_cases h : θ = 1
  · rw [if_pos h, h, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient, totient_cast]
  · rw [if_neg h, MulChar.sum_eq_zero_of_ne_one h]

private lemma star_char (χ : DirichletCharacter ℂ m) (x : (ZMod m)ˣ) :
    star (χ (x : ZMod m)) = χ ((x : ZMod m)⁻¹) := by
  rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]

private lemma orth1 (x y : (ZMod m)ˣ) :
    ∑ χ : DirichletCharacter ℂ m, star (χ (x : ZMod m)) * χ (y : ZMod m)
      = if x = y then ((m.totient : ℝ) : ℂ) else 0 := by
  simp_rw [star_char]
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ x.isUnit (y : ZMod m)]
  by_cases hxy : (x : ZMod m) = (y : ZMod m)
  · rw [if_pos hxy, if_pos (Units.val_inj.mp hxy), totient_cast]
  · rw [if_neg hxy, if_neg (fun h => hxy (Units.val_inj.mpr h))]

private lemma orth2 (χ ψ : DirichletCharacter ℂ m) :
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

private lemma parseval_complex (g : (ZMod m)ˣ → ℂ) :
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

private lemma parseval (g : (ZMod m)ˣ → ℂ) :
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

private lemma sum_swap (N : ZMod m) (A B : ZMod m → ℂ)
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

private lemma sum_reflect_le (N : ZMod m) (F : ZMod m → ℂ) (hF : ∀ a, ¬IsUnit a → F a = 0) :
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

private lemma synth_norm (w : DirichletCharacter ℂ m → ℂ) :
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

private lemma main_bound (N : ZMod m) (w : DirichletCharacter ℂ m → ℂ) :
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

end ReflectionModelAux

private theorem reflectBound :
    ∀ (m : ℕ) [NeZero m] (N : ZMod m),
      let H : Matrix (DirichletCharacter ℂ m) (DirichletCharacter ℂ m) ℂ := fun χ ψ =>
        (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (N - (x : ZMod m))) / (m.totient : ℂ)
      H.IsHermitian ∧ ∀ (s : Finset (DirichletCharacter ℂ m)) (v : DirichletCharacter ℂ m → ℂ),
        (∑ χ ∈ s, ‖∑ ψ ∈ s, H χ ψ * v ψ‖^2) ≤ ∑ χ ∈ s, ‖v χ‖^2 := by
  intro m _ N
  dsimp only
  refine ⟨?_, ?_⟩
  · refine Matrix.IsHermitian.ext (fun χ ψ => ?_)
    show star ((∑ x : (ZMod m)ˣ, star (ψ (x : ZMod m)) * χ (N - (x : ZMod m))) / (m.totient : ℂ))
        = (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (N - (x : ZMod m))) / (m.totient : ℂ)
    have hstar : star ((m.totient : ℕ) : ℂ) = ((m.totient : ℕ) : ℂ) := star_natCast _
    rw [star_div₀, hstar, star_sum]
    have h1 : ∑ x : (ZMod m)ˣ, star (star (ψ (x : ZMod m)) * χ (N - (x : ZMod m)))
        = ∑ x : (ZMod m)ˣ, ψ (x : ZMod m) * star (χ (N - (x : ZMod m))) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [star_mul, star_star]
      ring
    rw [h1]
    have hsw : ∑ x : (ZMod m)ˣ, ψ (x : ZMod m) * star (χ (N - (x : ZMod m)))
        = ∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (N - (x : ZMod m)) :=
      ReflectionModelAux.sum_swap N
        (fun a : ZMod m => ψ a) (fun a : ZMod m => star (χ a))
        (fun a ha => MulChar.map_nonunit ψ ha)
        (fun a ha => by rw [MulChar.map_nonunit χ ha, star_zero])
    rw [hsw]
  · intro s v
    classical
    show (∑ χ ∈ s, ‖∑ ψ ∈ s, ((∑ x : (ZMod m)ˣ, star (χ (x : ZMod m))
        * ψ (N - (x : ZMod m))) / (m.totient : ℂ)) * v ψ‖ ^ 2) ≤ ∑ χ ∈ s, ‖v χ‖ ^ 2
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
    have hmain := ReflectionModelAux.main_bound N
      (fun ψ => if ψ ∈ s then v ψ else 0)
    calc ∑ χ ∈ s, ‖∑ ψ ∈ s, ((∑ x : (ZMod m)ˣ, star (χ (x : ZMod m))
          * ψ (N - (x : ZMod m))) / (m.totient : ℂ)) * v ψ‖ ^ 2
        ≤ ∑ χ : DirichletCharacter ℂ m, ‖∑ ψ ∈ s, ((∑ x : (ZMod m)ˣ, star (χ (x : ZMod m))
            * ψ (N - (x : ZMod m))) / (m.totient : ℂ)) * v ψ‖ ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
          intro i _ _
          exact sq_nonneg _
      _ = ∑ χ : DirichletCharacter ℂ m, ‖∑ ψ : DirichletCharacter ℂ m,
            ((∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ (N - (x : ZMod m)))
              / (m.totient : ℂ)) * (if ψ ∈ s then v ψ else 0)‖ ^ 2 := by
          refine Finset.sum_congr rfl (fun χ _ => ?_)
          rw [hsub]
      _ ≤ ∑ ψ : DirichletCharacter ℂ m, ‖(if ψ ∈ s then v ψ else 0)‖ ^ 2 := hmain
      _ = ∑ χ ∈ s, ‖v χ‖ ^ 2 := hnorm



private theorem kernelSum (m : ℕ) [NeZero m] (a b : ZMod m) :
    (∑ χ : DirichletCharacter ℂ m, star (χ a) * χ b) =
      if IsUnit a ∧ a=b then (m.totient : ℂ) else 0 := by
  classical
  by_cases ha : IsUnit a
  · have h (χ : DirichletCharacter ℂ m) : star (χ a) = χ a⁻¹ := by
      obtain ⟨u,rfl⟩ := ha
      rw [MulChar.star_apply',MulChar.inv_apply,ZMod.inv_coe_unit,Ring.inverse_unit]
    simp_rw [h]
    simpa [ha] using DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha b
  · simp [MulChar.map_nonunit _ ha,ha]

private theorem boundFiber (N m i : ℕ) [NeZero m] :
    ((Finset.range (N+1)).filter (fun j : ℕ => IsUnit (i:ZMod m) ∧ (i:ZMod m)=(j:ZMod m))).card ≤ 1+N/m := by
  classical
  calc
    _ ≤ (Finset.range (N/m+1)).card := by
      apply Finset.card_le_card_of_injOn (fun j => j/m)
      · intro j hj
        have hle := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hle))
      · intro j hj k hk he
        have eqz := (Finset.mem_filter.mp hj).2.2.symm.trans (Finset.mem_filter.mp hk).2.2
        have hrem : j % m = k % m := (ZMod.natCast_eq_natCast_iff j k m).mp eqz
        have hj' := Nat.div_add_mod j m
        have hk' := Nat.div_add_mod k m
        dsimp at he
        rw [he,hrem] at hj'
        omega
    _ = _ := by simp [Nat.add_comm]

private theorem rowBound (N m : ℕ) [NeZero m] (w : ℕ → ℂ) :
    let I := Finset.range (N+1)
    let R := fun i j : ℕ => IsUnit (i:ZMod m) ∧ (i:ZMod m)=j
    (∑ i ∈ I, ∑ j ∈ I.filter (R i), (w i*star (w j)).re) ≤
        (1+(N/m:ℕ):ℝ) * ∑ i ∈ I, ‖w i‖^2 := by
  classical
  intro I R
  have sym i j : R i j ↔ R j i := by
    constructor <;> rintro ⟨h,e⟩ <;> exact ⟨e ▸ h,e.symm⟩
  have sw : (∑ i ∈ I, ∑ j ∈ I.filter (R i), ‖w j‖^2) =
      ∑ i ∈ I, ∑ _j ∈ I.filter (R i), ‖w i‖^2 := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    by_cases h : R i j
    · simp [h,(sym i j).mp h]
    · simp [h,(sym j i).not.mpr h]
  have mass : (∑ i ∈ I, ∑ _j ∈ I.filter (R i), ‖w i‖^2) ≤
      (1+(N/m:ℕ):ℝ) * ∑ i ∈ I, ‖w i‖^2 := by
    rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro i _
    simp only [Finset.sum_const,nsmul_eq_mul]
    gcongr
    exact_mod_cast boundFiber N m i
  calc
    _ ≤ ∑ i ∈ I, ∑ j ∈ I.filter (R i), (‖w i‖^2 + ‖w j‖^2)/2 := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      apply (Complex.re_le_norm _).trans
      rw [norm_mul,norm_star]; nlinarith [sq_nonneg (‖w i‖-‖w j‖)]
    _ ≤ _ := by simp only [← Finset.sum_div,Finset.sum_add_distrib]; rw [sw]; linarith

private theorem fibers :
    ∀ (m : ℕ) [NeZero m] (N : ℕ) (w : ℕ → ℂ) (s : Finset (DirichletCharacter ℂ m)),
  (∑ χ ∈ s, ‖(∑ n ∈ Finset.range (N+1), w n * star (χ (n : ZMod m))) /
      (Real.sqrt (m.totient : ℝ) : ℂ)‖^2) ≤
    (1 + (N/m : ℕ) : ℝ) * ∑ n ∈ Finset.range (N+1), ‖w n‖^2 := by
  classical
  intro m _ N w s
  let I := Finset.range (N+1)
  let v := fun (χ : DirichletCharacter ℂ m) => ∑ i ∈ I, w i * star (χ (i:ZMod m))
  let R := fun i j : ℕ => IsUnit (i:ZMod m) ∧ (i:ZMod m)=j
  let φ : ℝ := m.totient
  have hφ : 0 < φ := by dsimp [φ]; exact_mod_cast Nat.totient_pos.mpr (NeZero.pos m)
  have expan (χ : DirichletCharacter ℂ m) :
      ((‖v χ‖^2:ℝ):ℂ) =
      ∑ i ∈ I, ∑ j ∈ I, (w i * star (w j))*(star (χ (i:ZMod m))*χ (j:ZMod m)) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    change v χ * star (v χ) = _
    simp only [v,star_sum,star_mul,star_star,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  have pair : (∑ χ : DirichletCharacter ℂ m, ((‖v χ‖^2:ℝ):ℂ)) =
      ∑ i ∈ I, ∑ j ∈ I.filter (R i), (w i*star (w j))*(φ:ℂ) := by
    simp_rw [expan]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm, Finset.sum_filter]
    apply Finset.sum_congr rfl; intro j _
    rw [← Finset.mul_sum,kernelSum]
    by_cases h : R i j <;> simp [R] at h ⊢ <;> simp_all [φ]
  have re := congrArg Complex.re pair
  simp only [Complex.re_sum,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,mul_zero,sub_zero] at re
  have un : (∑ χ : DirichletCharacter ℂ m, ‖v χ‖^2)/φ ≤
      (1+(N/m:ℕ):ℝ) * ∑ i ∈ I, ‖w i‖^2 := by
    rw [re]
    simp only [← Finset.sum_mul, mul_div_cancel_right₀ _ hφ.ne']
    exact rowBound N m w
  change (∑ χ ∈ s, ‖v χ / (Real.sqrt φ : ℂ)‖^2) ≤ _
  simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    div_pow,Real.sq_sqrt hφ.le, ← Finset.sum_div]
  exact (div_le_div_of_nonneg_right (Finset.sum_le_univ_sum_of_nonneg (fun χ => sq_nonneg ‖v χ‖)) hφ.le).trans un



private theorem supportCount :
    ∀ X : ℕ, let T := (Finset.range (X+1)).filter (fun k => ArithmeticFunction.vonMangoldt k ≠ 0 ∧ ¬ Nat.Prime k); T.card ≤ (Nat.sqrt X+1)*(Nat.log 2 X+1) := by
  intro X
  dsimp only
  let T : Finset ℕ := (Finset.range (X + 1)).filter
      (fun k => ArithmeticFunction.vonMangoldt k ≠ 0 ∧ ¬ Nat.Prime k)
  let B : Finset (ℕ × ℕ) :=
      (Finset.range (Nat.sqrt X + 1)).product (Finset.range (Nat.log 2 X + 1))
  have hsub : T ⊆ B.image (fun z : ℕ × ℕ => z.1 ^ z.2) := by
    intro k hk
    have hkX : k ≤ X := by
      have := (Finset.mem_filter.mp hk).1
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp this)
    have hΛ : ArithmeticFunction.vonMangoldt k ≠ 0 := (Finset.mem_filter.mp hk).2.1
    have hknot : ¬ Nat.Prime k := (Finset.mem_filter.mp hk).2.2
    have hpp : IsPrimePow k := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
    rcases hpp with ⟨p, j, hp, hj, hpj⟩
    have hpN : Nat.Prime p := Nat.prime_iff.mpr hp
    have hj2 : 2 ≤ j := by
      by_contra h
      have hj1 : j = 1 := by omega
      subst j
      simp at hpj
      exact hknot (hpj ▸ hpN)
    have hp2 : p ^ 2 ≤ X := by
      calc
        p ^ 2 ≤ p ^ j := by
          exact pow_le_pow_right₀ (by exact_mod_cast (Nat.Prime.one_le hpN)) hj2
        _ = k := hpj
        _ ≤ X := hkX
    have hpsqrt : p ≤ Nat.sqrt X := (Nat.le_sqrt).mpr (by simpa [pow_two] using hp2)
    have h2j : 2 ^ j ≤ X := by
      calc
        2 ^ j ≤ p ^ j := Nat.pow_le_pow_left (Nat.Prime.two_le hpN) j
        _ = k := hpj
        _ ≤ X := hkX
    have hjlog : j ≤ Nat.log 2 X := Nat.le_log_of_pow_le (by omega) h2j
    apply Finset.mem_image.mpr
    refine ⟨(p, j), ?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hpsqrt),
         Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hjlog)⟩
    · exact hpj
  calc
    T.card ≤ (B.image (fun z : ℕ × ℕ => z.1 ^ z.2)).card := Finset.card_le_card hsub
    _ ≤ B.card := Finset.card_image_le
    _ = (Nat.sqrt X + 1) * (Nat.log 2 X + 1) := by
      simp [B]

theorem Conjectures.Goldbach.ReflectionPrimePowerModelError : ∀ (m : ℕ) [NeZero m] (N : ℕ) (s : Finset (DirichletCharacter ℂ m)), 2 ≤ N →
  let w := fun n : ℕ => if n.Prime then Real.log (n : ℝ) else 0
  let v := fun (a : ℕ → ℝ) (χ : DirichletCharacter ℂ m) =>
    (∑ n ∈ Finset.range (N+1), (a n : ℂ) * star (χ (n : ZMod m))) / (Real.sqrt (m.totient : ℝ) : ℂ)
  let H := fun χ ψ : DirichletCharacter ℂ m =>
    (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ ((N : ZMod m) - (x : ZMod m))) / (m.totient : ℂ)
  let R := fun z : DirichletCharacter ℂ m → ℂ => (∑ χ ∈ s, ∑ ψ ∈ s, star (z χ) * H χ ψ * z ψ).re
  |R (v ArithmeticFunction.vonMangoldt) - R (v w)| ≤
    2 * (1 + (N/m : ℕ) : ℝ) * Real.sqrt (((N+1) * (Nat.sqrt N+1) * (Nat.log 2 N+1) : ℕ) : ℝ) *
      (Real.log (N : ℝ))^2 := by
  classical
  intro m _ N s hN w v H R
  let V := v ArithmeticFunction.vonMangoldt
  let W := v w
  let d := fun k => ArithmeticFunction.vonMangoldt k - w k
  let D := v d
  let I := Finset.range (N+1)
  let Q := fun x : DirichletCharacter ℂ m → ℂ => ∑ i ∈ s, ‖x i‖^2
  let B := fun x y : DirichletCharacter ℂ m → ℂ =>
    ∑ i ∈ s, ∑ j ∈ s, star (x i)*H i j*y j
  let A : ℝ := 1 + (N/m:ℕ)
  let L := Real.log (N:ℝ)
  let T := I.filter (fun k => ArithmeticFunction.vonMangoldt k ≠ 0 ∧ ¬ k.Prime)
  let t : ℝ := (((Nat.sqrt N+1)*(Nat.log 2 N+1):ℕ):ℝ)
  let b : ℝ := (N+1:ℕ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have subV i : D i = V i-W i := by
    change (∑ k ∈ I, ((ArithmeticFunction.vonMangoldt k-w k:ℝ):ℂ)*_) / _ = _ - _
    simp only [V,W,v,Complex.ofReal_sub,sub_mul,Finset.sum_sub_distrib,sub_div,I]
  have hbnd (x y : DirichletCharacter ℂ m → ℂ) :
      ‖B x y‖ ≤ Real.sqrt (Q x)*Real.sqrt (Q y) := by
    let hy := fun i => ∑ j ∈ s, H i j*y j
    have hcon : (∑ i ∈ s, ‖hy i‖^2) ≤ Q y := (reflectBound m (N:ZMod m)).2 s y
    have eq : B x y = ∑ i ∈ s, star (x i)*hy i := by
      dsimp [B,hy]; simp_rw [Finset.mul_sum,mul_assoc]
    rw [eq]
    calc _ ≤ ∑ i ∈ s, ‖x i‖ * ‖hy i‖ := by simpa only [norm_mul,norm_star] using norm_sum_le s (fun i => star (x i)*hy i)
         _ ≤ _ := (Real.sum_mul_le_sqrt_mul_sqrt s (fun i => ‖x i‖) (fun i => ‖hy i‖)).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcon) (Real.sqrt_nonneg _))
  have fiber (u : ℕ → ℝ) : Q (v u) ≤ A * ∑ k ∈ I, (u k)^2 := by
    simpa only [Q,v,A,I, Complex.norm_real,Real.norm_eq_abs,sq_abs] using fibers m N (fun k => (u k:ℂ)) s
  have lam (k : ℕ) (hk : k∈I) : 0 ≤ ArithmeticFunction.vonMangoldt k ∧ ArithmeticFunction.vonMangoldt k ≤ L := by
    refine ⟨ArithmeticFunction.vonMangoldt_nonneg,?_⟩
    by_cases h : k=0
    · simpa [h] using hL
    · exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero h)) (by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
  have wt (k : ℕ) (hk : k∈I) : 0 ≤ w k ∧ w k ≤ ArithmeticFunction.vonMangoldt k := by
    by_cases hp : k.Prime
    · simp [w,hp,ArithmeticFunction.vonMangoldt_apply_prime hp,Real.log_natCast_nonneg]
    · simp [w,hp,ArithmeticFunction.vonMangoldt_nonneg]
  have point {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : x^2 ≤ y^2 := by gcongr
  have uniform (u : ℕ → ℝ) (h : ∀ k ∈ I, 0≤u k ∧ u k≤L) : Q (v u) ≤ A*b*L^2 := by
    apply (fiber _).trans
    have hh := Finset.sum_le_sum (s:=I) (g:=fun _ => L^2) (fun k hk => point (h k hk).1 (h k hk).2)
    calc _ ≤ A * (∑ _ ∈ I, L^2) := mul_le_mul_of_nonneg_left hh hA
         _ = _ := by simp [I,b,mul_assoc]
  have qv : Q V ≤ A*b*L^2 := uniform _ lam
  have qw : Q W ≤ A*b*L^2 := uniform _ (fun k hk => ⟨(wt k hk).1,(wt k hk).2.trans (lam k hk).2⟩)
  have qd : Q D ≤ A*t*L^2 := by
    apply (fiber _).trans
    have sumEq : (∑ k ∈ I, (d k)^2) = ∑ k ∈ T, (d k)^2 := by
      symm; apply Finset.sum_subset (Finset.filter_subset _ _)
      intro k hk hnot
      by_cases hp : k.Prime
      · simp [d,w,hp,ArithmeticFunction.vonMangoldt_apply_prime hp]
      · have hz : ArithmeticFunction.vonMangoldt k=0 := by
          by_contra h; exact hnot (Finset.mem_filter.mpr ⟨hk,h,hp⟩)
        simp [d,w,hp,hz]
    have Tsize : (T.card:ℝ) ≤ t := Nat.cast_le.mpr (supportCount N)
    rw [sumEq]
    have hs : (∑ k ∈ T, (d k)^2) ≤ (T.card:ℝ)*L^2 := by
      apply (Finset.sum_le_sum (g:=fun _ => L^2) ?_).trans_eq
      · simp
      intro k hk
      have h := (Finset.mem_filter.mp hk).1
      apply point
      · exact sub_nonneg.mpr (wt k h).2
      · exact (sub_le_self _ (wt k h).1).trans (lam k h).2
    calc _ ≤ A*(t*L^2) := mul_le_mul_of_nonneg_left (hs.trans (mul_le_mul_of_nonneg_right Tsize (sq_nonneg L))) hA
         _ = _ := by ring
  have eq : B V V - B W W = B D V + B W D := by
    dsimp [B]
    rw [←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    simp only [subV,Complex.star_def,map_sub]; ring
  have sroot (x a : ℝ) (ha : 0≤a) (hx : x ≤ A*a*L^2) :
      Real.sqrt x ≤ Real.sqrt A*Real.sqrt a*L := by
    apply (Real.sqrt_le_sqrt hx).trans_eq
    rw [Real.sqrt_mul (mul_nonneg hA ha),Real.sqrt_mul hA,Real.sqrt_sq hL]
  have bounds : ‖B D V‖ + ‖B W D‖ ≤ 2*A*Real.sqrt (b*t)*L^2 := by
    calc _ ≤ Real.sqrt (Q D)*Real.sqrt (Q V) + Real.sqrt (Q W)*Real.sqrt (Q D) := add_le_add (hbnd _ _) (hbnd _ _)
         _ ≤ (Real.sqrt A*Real.sqrt t*L)*(Real.sqrt A*Real.sqrt b*L) + (Real.sqrt A*Real.sqrt b*L)*(Real.sqrt A*Real.sqrt t*L) := by
           gcongr
           · exact sroot _ _ ht qd
           · exact sroot _ _ hb qv
           · exact sroot _ _ hb qw
           · exact sroot _ _ ht qd
         _ = _ := by rw [Real.sqrt_mul hb]; linear_combination (2*Real.sqrt b*Real.sqrt t*L^2)*(Real.sq_sqrt hA)
  change |(B V V).re-(B W W).re| ≤ _
  rw [←Complex.sub_re]
  apply (Complex.abs_re_le_norm _).trans
  rw [eq]
  apply (norm_add_le _ _).trans
  convert bounds using 1 <;> dsimp [b,t,A,L] <;> push_cast <;> ring
