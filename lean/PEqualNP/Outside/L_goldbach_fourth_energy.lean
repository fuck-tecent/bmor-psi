import Mathlib

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace GoldbachFourthEnergy

/-- Regroup a finite double sum by the sum of its two indices. -/
lemma convolution_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → ℕ → M) :
    (∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1), f a b) =
      ∑ s ∈ Finset.range (2*n+1),
        ∑ a ∈ (Finset.range (n+1)).filter (fun a => a ≤ s ∧ s-a ≤ n), f a (s-a) := by
  classical
  let P := (Finset.range (n+1)) ×ˢ (Finset.range (n+1))
  have hmaps : ∀ p ∈ P, p.1 + p.2 ∈ Finset.range (2*n+1) := by
    intro p hp
    simp only [P, Finset.mem_product, Finset.mem_range] at hp ⊢
    omega
  rw [← Finset.sum_product (Finset.range (n+1)) (Finset.range (n+1))
    (fun p : ℕ × ℕ => f p.1 p.2)]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun p => f p.1 p.2)]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_bij (fun p _ => p.1)
  · intro p hp
    simp only [Finset.mem_filter, P, Finset.mem_product, Finset.mem_range] at hp ⊢
    omega
  · intro p hp q hq heq
    simp only [Finset.mem_filter, P, Finset.mem_product, Finset.mem_range] at hp hq
    apply Prod.ext heq
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    refine ⟨(a, s-a), ?_, rfl⟩
    simp only [Finset.mem_filter, P, Finset.mem_product, Finset.mem_range]
    omega
  · intro p hp
    simp only [Finset.mem_filter] at hp
    congr 1
    omega

noncomputable def poly (n : ℕ) (w : ℕ → ℝ) : C(AddCircle (1:ℝ), ℂ) :=
  ∑ k ∈ Finset.range (n+1), (w k : ℂ) • fourier (k:ℤ)

lemma poly_apply (n : ℕ) (w : ℕ → ℝ) (x : AddCircle (1:ℝ)) :
    poly n w x = ∑ k ∈ Finset.range (n+1), (w k : ℂ) * fourier (k:ℤ) x := by
  simp [poly, ContinuousMap.sum_apply, smul_eq_mul]

lemma poly_square (n : ℕ) (w : ℕ → ℝ) (x : AddCircle (1:ℝ)) :
    (poly n w x)^2 = poly (2*n)
      (fun s => ∑ a ∈ (Finset.range (n+1)).filter (fun a => a ≤ s ∧ s-a ≤ n),
        w a*w (s-a)) x := by
  classical
  rw [poly_apply, pow_two, Finset.sum_mul_sum, convolution_sum]
  rw [poly_apply]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Complex.ofReal_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  have has : a ≤ s := (Finset.mem_filter.mp ha).2.1
  rw [Complex.ofReal_mul]
  have hf : fourier (a:ℤ) x * fourier ((s-a:ℕ):ℤ) x = fourier (s:ℤ) x := by
    rw [← fourier_add, ← Nat.cast_add, Nat.add_sub_of_le has]
  calc
    _ = ((w a:ℂ)*(w (s-a):ℂ)) *
        (fourier (a:ℤ) x * fourier ((s-a:ℕ):ℤ) x) := by ring
    _ = _ := by rw [hf]

/-- Finite Parseval for real coefficients, using the orthonormal Fourier family. -/
lemma poly_parseval (n : ℕ) (w : ℕ → ℝ) :
    (∫ x : AddCircle (1:ℝ), ‖poly n w x‖^2 ∂AddCircle.haarAddCircle) =
      ∑ k ∈ Finset.range (n+1), (w k)^2 := by
  have ho := (orthonormal_fourier (T := (1:ℝ))).comp
    (fun k : ℕ => (k:ℤ)) Nat.cast_injective
  have h := ho.inner_sum (fun k => (w k:ℂ)) (fun k => (w k:ℂ))
    (Finset.range (n+1))
  have hp : (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ) (poly n w) =
      ∑ k ∈ Finset.range (n+1), (w k:ℂ) • fourierLp (T := (1:ℝ)) 2 (k:ℤ) := by
    simp [poly, fourierLp]
  simp only [Function.comp_apply] at h
  rw [← hp, ContinuousMap.inner_toLp] at h
  have hi : Integrable (fun x : AddCircle (1:ℝ) =>
      poly n w x * conj (poly n w x)) AddCircle.haarAddCircle := by
    exact ((poly n w).continuous.mul (poly n w).continuous.star).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hr := congrArg (RCLike.re : ℂ → ℝ) h
  rw [← integral_re hi] at hr
  simpa [Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_two] using hr

lemma poly_coe (n : ℕ) (w : ℕ → ℝ) (t : ℝ) :
    poly n w (t : AddCircle (1:ℝ)) =
      ∑ k ∈ Finset.range (n+1), (w k:ℂ) *
        Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I) := by
  rw [poly_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [fourier_coe_apply]
  congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast,
    Complex.ofReal_one, Int.cast_natCast, div_one]
  congr 1
  ring

lemma fourth_moment (n : ℕ) (w : ℕ → ℝ) :
    (∫ x : AddCircle (1:ℝ), ‖poly n w x‖^4) =
      ∑ s ∈ Finset.range (2*n+1),
        (∑ a ∈ (Finset.range (n+1)).filter (fun a => a ≤ s ∧ s-a ≤ n),
          w a*w (s-a))^2 := by
  have hvol : (volume : Measure (AddCircle (1:ℝ))) = AddCircle.haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    norm_num
  rw [hvol, ← poly_parseval]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← poly_square, norm_pow]
  ring

end GoldbachFourthEnergy

/-- The fourth moment of a finite exponential sum is the squared energy of its additive convolution. -/
theorem PEqualNP.Outside.L_goldbach_fourth_energy :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
    let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) =>
      Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t))
    ∀ n w, let T := Finset.range (n+1)
      intervalIntegral (fun t => ‖S n w t‖^4) (0:ℝ) 1 MeasureTheory.volume =
        Finset.sum (Finset.range (2*n+1)) (fun s =>
          (Finset.sum (T.filter (fun a => a ≤ s ∧ s-a ≤ n)) (fun a => w a*w (s-a)))^2) := by
  dsimp only
  intro n w
  calc
    _ = ∫ t in (0:ℝ)..1, ‖GoldbachFourthEnergy.poly n w (t : AddCircle (1:ℝ))‖^4 := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [GoldbachFourthEnergy.poly_coe]
    _ = ∫ x : AddCircle (1:ℝ), ‖GoldbachFourthEnergy.poly n w x‖^4 := by
      simpa using AddCircle.intervalIntegral_preimage (1:ℝ) 0
        (fun x => ‖GoldbachFourthEnergy.poly n w x‖^4)
    _ = _ := GoldbachFourthEnergy.fourth_moment n w
