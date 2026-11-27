import Mathlib

private noncomputable def auxS (b : ℕ) [NeZero b] (k : ZMod b) : ZMod b → ℂ :=
  fun j : ZMod b =>
    ∑ a : (ZMod b)ˣ, ZMod.stdAddChar (j * (a : ZMod b) + k * ((a⁻¹ : (ZMod b)ˣ) : ZMod b))

private lemma aux_ortho (b : ℕ) [NeZero b] (t : ZMod b) :
    ∑ j : ZMod b, ZMod.stdAddChar (t * j) = if t = 0 then (b : ℂ) else 0 := by
  have h := AddChar.sum_mulShift (R := ZMod b) (R' := ℂ) t (ZMod.isPrimitive_stdAddChar b)
  simpa [mul_comm, ZMod.card] using h

private lemma aux_sum_char (b : ℕ) [NeZero b] (c d : ZMod b) :
    ∑ j : ZMod b, ZMod.stdAddChar (j * c + d)
      = (if c = 0 then (b : ℂ) else 0) * ZMod.stdAddChar d := by
  have h1 : ∀ j : ZMod b, ZMod.stdAddChar (j * c + d)
      = ZMod.stdAddChar (c * j) * ZMod.stdAddChar d := by
    intro j
    rw [mul_comm j c]
    exact ZMod.stdAddChar.map_add_eq_mul _ _
  simp_rw [h1, ← Finset.sum_mul, aux_ortho b c]

private lemma aux_inner (b : ℕ) [NeZero b] (i k : ZMod b) (a : (ZMod b)ˣ) :
    ∑ j : ZMod b, ZMod.stdAddChar (-(i * j)) *
        ZMod.stdAddChar (j * (a : ZMod b) + k * ((a⁻¹ : (ZMod b)ˣ) : ZMod b))
      = (if ((a : ZMod b) - i) = 0 then (b : ℂ) else 0) *
          ZMod.stdAddChar (k * ((a⁻¹ : (ZMod b)ˣ) : ZMod b)) := by
  have h1 : ∀ j : ZMod b, ZMod.stdAddChar (-(i * j)) *
      ZMod.stdAddChar (j * (a : ZMod b) + k * ((a⁻¹ : (ZMod b)ˣ) : ZMod b))
      = ZMod.stdAddChar (-(i * j) +
          (j * (a : ZMod b) + k * ((a⁻¹ : (ZMod b)ˣ) : ZMod b))) :=
    fun j => (ZMod.stdAddChar.map_add_eq_mul _ _).symm
  have h2 : ∀ j : ZMod b, -(i * j) +
      (j * (a : ZMod b) + k * ((a⁻¹ : (ZMod b)ˣ) : ZMod b))
      = j * ((a : ZMod b) - i) + k * ((a⁻¹ : (ZMod b)ˣ) : ZMod b) := by
    intro j
    ring
  simp_rw [h1, h2]
  exact aux_sum_char b _ _

private lemma aux_sum_swap {α β : Type*} [Fintype α] [Fintype β] {M : Type*} [AddCommMonoid M]
    (f : α → β → M) : (∑ x : α, ∑ y : β, f x y) = ∑ y : β, ∑ x : α, f x y := by
  rw [Finset.sum_comm]

private lemma aux_sum_ite {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommMonoid M]
    (a : α) (f : α → M) : ∑ x : α, (if x = a then f x else 0) = f a := by
  rw [Finset.sum_ite_eq']
  simp

private lemma aux_dft_sum (b : ℕ) [NeZero b] (w g : ZMod b → ℂ) :
    (∑ j : ZMod b, ZMod.dft w j * g j)
      = ∑ i : ZMod b, w i * ∑ j : ZMod b, ZMod.stdAddChar (-(i * j)) * g j := by
  have h : ∀ i j : ZMod b, (ZMod.stdAddChar (-(i * j)) * w i) * g j
      = w i * (ZMod.stdAddChar (-(i * j)) * g j) := by
    intro i j
    ring
  simp only [ZMod.dft_apply, Finset.sum_mul, smul_eq_mul]
  rw [aux_sum_swap]
  simp_rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]

private lemma aux_collapse (b : ℕ) [NeZero b] (w : ZMod b → ℂ) (a : ZMod b) (c : ℂ) :
    ∑ i : ZMod b, w i * ((if a - i = 0 then (b : ℂ) else 0) * c) = (w a * c) * (b : ℂ) := by
  have hmain : ∀ i : ZMod b, w i * ((if a - i = 0 then (b : ℂ) else 0) * c)
      = if i = a then w i * c * (b : ℂ) else 0 := by
    intro i
    by_cases hx : a - i = 0
    · have h1 : i = a := (sub_eq_zero.mp hx).symm
      simp only [if_pos hx, if_pos h1]
      ring
    · have h1 : ¬ (i = a) := fun hz => hx (by rw [hz, sub_self])
      simp only [if_neg hx, if_neg h1]
      ring
  calc ∑ i : ZMod b, w i * ((if a - i = 0 then (b : ℂ) else 0) * c)
      = ∑ i : ZMod b, (if i = a then w i * c * (b : ℂ) else 0) :=
        Finset.sum_congr rfl (fun i _ => hmain i)
    _ = w a * c * (b : ℂ) := aux_sum_ite a (fun i => w i * c * (b : ℂ))

private lemma aux_pair (b : ℕ) [NeZero b] (x y : ZMod b) :
    ZMod.stdAddChar x * starRingEnd ℂ (ZMod.stdAddChar y)
      = ZMod.stdAddChar (x - y) := by
  have hR : 0 < ringChar (ZMod b) := by
    rw [ZMod.ringChar_zmod_n]
    exact Nat.pos_of_ne_zero (NeZero.ne b)
  rw [AddChar.starComp_apply hR, AddChar.inv_apply, sub_eq_add_neg]
  exact (ZMod.stdAddChar.map_add_eq_mul _ _).symm

private lemma aux_mul_star (z : ℂ) : z * starRingEnd ℂ z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj', ← Complex.ofReal_pow]

private lemma aux_inner2 (b : ℕ) [NeZero b] (k : ZMod b) (a a2 : (ZMod b)ˣ) :
    ∑ j : ZMod b, ZMod.stdAddChar (j * (a : ZMod b) + k * ((a⁻¹ : (ZMod b)ˣ) : ZMod b)) *
        starRingEnd ℂ (ZMod.stdAddChar
          (j * (a2 : ZMod b) + k * ((a2⁻¹ : (ZMod b)ˣ) : ZMod b)))
      = if a = a2 then (b : ℂ) else 0 := by
  have h1 : ∀ j : ZMod b, ZMod.stdAddChar
      (j * (a : ZMod b) + k * ((a⁻¹ : (ZMod b)ˣ) : ZMod b)) *
      starRingEnd ℂ (ZMod.stdAddChar
        (j * (a2 : ZMod b) + k * ((a2⁻¹ : (ZMod b)ˣ) : ZMod b)))
      = ZMod.stdAddChar ((j * (a : ZMod b) + k * ((a⁻¹ : (ZMod b)ˣ) : ZMod b)) -
          (j * (a2 : ZMod b) + k * ((a2⁻¹ : (ZMod b)ˣ) : ZMod b))) :=
    fun j => aux_pair b _ _
  have h2 : ∀ j : ZMod b, (j * (a : ZMod b) + k * ((a⁻¹ : (ZMod b)ˣ) : ZMod b)) -
      (j * (a2 : ZMod b) + k * ((a2⁻¹ : (ZMod b)ˣ) : ZMod b))
      = j * ((a : ZMod b) - (a2 : ZMod b)) +
          k * (((a⁻¹ : (ZMod b)ˣ) : ZMod b) - ((a2⁻¹ : (ZMod b)ˣ) : ZMod b)) := by
    intro j
    ring
  simp_rw [h1, h2, aux_sum_char b]
  by_cases h : a = a2
  · subst h
    simp
  · have hne : ((a : ZMod b) - (a2 : ZMod b)) ≠ 0 := by
      intro hz
      exact h (Units.val_injective (sub_eq_zero.mp hz))
    simp [h, hne]

private lemma aux_part1 (b : ℕ) [NeZero b] (k : ZMod b) (w : ZMod b → ℂ) :
    (∑ a : (ZMod b)ˣ, w (a : ZMod b) *
        ZMod.stdAddChar (k * ((a⁻¹ : (ZMod b)ˣ) : ZMod b)))
      = (∑ j : ZMod b, ZMod.dft w j * auxS b k j) / (b : ℂ) := by
  have hmain : (∑ j : ZMod b, ZMod.dft w j * auxS b k j)
      = (b : ℂ) * ∑ a : (ZMod b)ˣ, w (a : ZMod b) *
          ZMod.stdAddChar (k * ((a⁻¹ : (ZMod b)ˣ) : ZMod b)) := by
    simp only [auxS, Finset.mul_sum]
    rw [aux_sum_swap]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [aux_dft_sum b w]
    simp_rw [aux_inner b, aux_collapse b w]
    ring
  have hb : (b : ℂ) ≠ 0 := by
    exact_mod_cast NeZero.ne b
  rw [hmain, mul_div_cancel_left₀ _ hb]

private lemma aux_part2 (b : ℕ) [NeZero b] (k : ZMod b) :
    (∑ j : ZMod b, ‖auxS b k j‖ ^ 2) = (b : ℝ) * (Nat.totient b : ℝ) := by
  have hconj : ∀ j : ZMod b, starRingEnd ℂ (auxS b k j)
      = ∑ a : (ZMod b)ˣ, starRingEnd ℂ
          (ZMod.stdAddChar (j * (a : ZMod b) + k * ((a⁻¹ : (ZMod b)ˣ) : ZMod b))) := by
    intro j
    simp only [auxS]
    exact map_sum (starRingEnd ℂ) _ Finset.univ
  have hQ : ∀ a : (ZMod b)ˣ, (∑ j : ZMod b, auxS b k j * starRingEnd ℂ
        (ZMod.stdAddChar (j * (a : ZMod b) + k * ((a⁻¹ : (ZMod b)ˣ) : ZMod b))))
      = (b : ℂ) := by
    intro a
    have hsplit : ∀ j : ZMod b, (∑ a2 : (ZMod b)ˣ, ZMod.stdAddChar
          (j * (a2 : ZMod b) + k * ((a2⁻¹ : (ZMod b)ˣ) : ZMod b))) *
        starRingEnd ℂ (ZMod.stdAddChar
          (j * (a : ZMod b) + k * ((a⁻¹ : (ZMod b)ˣ) : ZMod b)))
        = ∑ a2 : (ZMod b)ˣ, ZMod.stdAddChar
            (j * (a2 : ZMod b) + k * ((a2⁻¹ : (ZMod b)ˣ) : ZMod b)) *
          starRingEnd ℂ (ZMod.stdAddChar
            (j * (a : ZMod b) + k * ((a⁻¹ : (ZMod b)ˣ) : ZMod b))) := by
      intro j
      rw [Finset.sum_mul]
    simp only [auxS]
    simp_rw [hsplit]
    rw [aux_sum_swap]
    simp_rw [aux_inner2 b k]
    exact aux_sum_ite a (fun _ => (b : ℂ))
  have hC : (∑ j : ZMod b, auxS b k j * starRingEnd ℂ (auxS b k j))
      = ((b : ℝ) : ℂ) * ((Nat.totient b : ℝ) : ℂ) := by
    simp_rw [hconj, Finset.mul_sum]
    rw [aux_sum_swap]
    simp_rw [hQ]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ZMod.card_units_eq_totient]
    push_cast
    ring
  have hreal : ((∑ j : ZMod b, ‖auxS b k j‖ ^ 2 : ℝ) : ℂ)
      = (((b : ℝ) * (Nat.totient b : ℝ) : ℝ) : ℂ) := by
    calc ((∑ j : ZMod b, ‖auxS b k j‖ ^ 2 : ℝ) : ℂ)
        = ∑ j : ZMod b, ((‖auxS b k j‖ ^ 2 : ℝ) : ℂ) := by
          exact map_sum (algebraMap ℝ ℂ) _ Finset.univ
      _ = ∑ j : ZMod b, auxS b k j * starRingEnd ℂ (auxS b k j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [aux_mul_star]
      _ = ((b : ℝ) : ℂ) * ((Nat.totient b : ℝ) : ℂ) := hC
      _ = (((b : ℝ) * (Nat.totient b : ℝ) : ℝ) : ℂ) := by
          rw [Complex.ofReal_mul]
  exact Complex.ofReal_injective hreal

theorem Conjectures.QuadraticPrimes.GaussInverseCompletion :
    ∀ (b : ℕ) [NeZero b] (k : ZMod b) (w : ZMod b → ℂ),
      let S := fun j : ZMod b =>
        ∑ a : (ZMod b)ˣ, ZMod.stdAddChar (j*(a : ZMod b)+k*(↑(a⁻¹) : ZMod b));
      (∑ a : (ZMod b)ˣ, w (a : ZMod b) * ZMod.stdAddChar (k*(↑(a⁻¹) : ZMod b))) =
        (∑ j : ZMod b, ZMod.dft w j * S j)/(b : ℂ) ∧
      (∑ j : ZMod b, ‖S j‖^2) = (b : ℝ)*(Nat.totient b : ℝ) := by
  intro b inst k w
  exact ⟨aux_part1 b k w, aux_part2 b k⟩
