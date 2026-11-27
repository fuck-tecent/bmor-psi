import Mathlib
open scoped BigOperators

noncomputable section
namespace B1B1

def E (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)

/-- The deep-minor kernel is the full circle integral minus the wide-arc part
(explicit integrability form). -/
lemma kernel_eq (s : Set ℝ) (h : ℤ)
    (h2 : IntervalIntegrable (fun x : ℝ => s.indicator (fun y => E ((h:ℝ)*y)) x) MeasureTheory.volume 0 1)
    (h3 : IntervalIntegrable (fun x : ℝ => sᶜ.indicator (fun y => E ((h:ℝ)*y)) x) MeasureTheory.volume 0 1) :
    (∫ t in (0:ℝ)..1, sᶜ.indicator (fun x => E ((h:ℝ)*x)) t)
      = (∫ t in (0:ℝ)..1, E ((h:ℝ)*t)) -
        (∫ t in (0:ℝ)..1, s.indicator (fun x => E ((h:ℝ)*x)) t) := by
  have hpt : ∀ t : ℝ, E ((h:ℝ)*t)
      = s.indicator (fun x => E ((h:ℝ)*x)) t + sᶜ.indicator (fun x => E ((h:ℝ)*x)) t := by
    intro t
    by_cases ht : t ∈ s
    · rw [Set.indicator_of_mem ht, Set.indicator_of_notMem (by simpa using ht)]
      simp
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_mem (by simpa using ht)]
      simp
  have hAdd : (∫ t in (0:ℝ)..1, E ((h:ℝ)*t))
      = (∫ t in (0:ℝ)..1, s.indicator (fun x => E ((h:ℝ)*x)) t)
        + (∫ t in (0:ℝ)..1, sᶜ.indicator (fun x => E ((h:ℝ)*x)) t) := by
    rw [← intervalIntegral.integral_add h2 h3]
    apply intervalIntegral.integral_congr
    intro t _
    exact hpt t
  rw [hAdd]
  ring

end B1B1
