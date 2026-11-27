import Mathlib
open scoped BigOperators

noncomputable section
namespace B1B1

def E (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)

def S (n : ℕ) (u : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n+1), (u k : ℂ) * E ((k:ℝ)*t)

lemma E_add (x y : ℝ) : E x * E y = E (x + y) := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma S_sq_mul_exp (n : ℕ) (u : ℕ → ℝ) (x : ℝ) :
    S n u x * S n u x * E (-(n:ℝ)*x)
      = ∑ m1 ∈ Finset.range (n+1), ∑ m2 ∈ Finset.range (n+1),
          ((u m1 : ℂ) * (u m2 : ℂ)) * E (((m1:ℝ)+(m2:ℝ)-(n:ℝ))*x) := by
  unfold S
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m1 _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m2 _
  have h : E ((m1:ℝ)*x) * E ((m2:ℝ)*x) * E (-(n:ℝ)*x) = E (((m1:ℝ)+(m2:ℝ)-(n:ℝ))*x) := by
    rw [E_add, E_add]
    congr 1
    ring
  calc ((u m1 : ℂ) * E ((m1:ℝ)*x)) * ((u m2 : ℂ) * E ((m2:ℝ)*x)) * E (-(n:ℝ)*x)
      = ((u m1 : ℂ) * (u m2 : ℂ)) *
          (E ((m1:ℝ)*x) * E ((m2:ℝ)*x) * E (-(n:ℝ)*x)) := by ring
    _ = ((u m1 : ℂ) * (u m2 : ℂ)) * E (((m1:ℝ)+(m2:ℝ)-(n:ℝ))*x) := by rw [h]

/-- The deep-minor integral in dispersion form: the kernel is the Fourier
transform of the deep-minor indicator at the frequency `m1 + m2 - n`. -/
theorem Jdeep_dispersion (n : ℕ) (u : ℕ → ℝ) (wideArcs : Set ℝ)
    (hW : MeasurableSet wideArcs) :
    (∫ t in (0:ℝ)..1, wideArcsᶜ.indicator
        (fun x => S n u x * S n u x * E (-(n:ℝ)*x)) t)
      = ∑ m1 ∈ Finset.range (n+1), ∑ m2 ∈ Finset.range (n+1),
          ((u m1 : ℂ) * (u m2 : ℂ)) *
            ∫ t in (0:ℝ)..1, wideArcsᶜ.indicator
              (fun x => E (((m1:ℝ)+(m2:ℝ)-(n:ℝ))*x)) t := by
  have hint : ∀ m1 m2 : ℕ, IntervalIntegrable
      (fun t => wideArcsᶜ.indicator
        (fun x => E (((m1:ℝ)+(m2:ℝ)-(n:ℝ))*x)) t) MeasureTheory.volume 0 1 := by
    intro m1 m2
    have hc : Continuous (fun x : ℝ => E (((m1:ℝ)+(m2:ℝ)-(n:ℝ))*x)) := by
      unfold E; fun_prop
    have := hc.intervalIntegrable (μ := MeasureTheory.volume) 0 1
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this ⊢
    exact this.indicator hW.compl
  have hfun : (fun t => wideArcsᶜ.indicator
        (fun x => S n u x * S n u x * E (-(n:ℝ)*x)) t)
      = fun t => ∑ m1 ∈ Finset.range (n+1), ∑ m2 ∈ Finset.range (n+1),
          ((u m1 : ℂ) * (u m2 : ℂ)) * wideArcsᶜ.indicator
            (fun x => E (((m1:ℝ)+(m2:ℝ)-(n:ℝ))*x)) t := by
    funext t
    by_cases ht : t ∈ wideArcsᶜ
    · rw [Set.indicator_of_mem ht, S_sq_mul_exp]
      apply Finset.sum_congr rfl
      intro m1 _
      apply Finset.sum_congr rfl
      intro m2 _
      rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht]
      simp only [Set.indicator_of_notMem ht, mul_zero, Finset.sum_const_zero]
  rw [hfun]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro m1 _
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro m2 _
      rw [intervalIntegral.integral_const_mul]
    · intro m2 _
      exact (hint m1 m2).const_mul ((u m1 : ℂ) * (u m2 : ℂ))
  · intro m1 _
    have hsum := IntervalIntegrable.sum (Finset.range (n+1))
      (fun m2 _ => (hint m1 m2).const_mul ((u m1 : ℂ) * (u m2 : ℂ)))
    have hcongr : (∑ i ∈ Finset.range (n+1), (fun x =>
        (u m1 : ℂ) * (u i : ℂ) * wideArcsᶜ.indicator
          (fun x => E (((m1:ℝ)+(i:ℝ)-(n:ℝ))*x)) x))
        = fun t => ∑ m2 ∈ Finset.range (n+1),
            (u m1 : ℂ) * (u m2 : ℂ) * wideArcsᶜ.indicator
              (fun x => E (((m1:ℝ)+(m2:ℝ)-(n:ℝ))*x)) t := by
      funext t
      rw [Finset.sum_apply]
    rw [hcongr] at hsum
    exact hsum

end B1B1
