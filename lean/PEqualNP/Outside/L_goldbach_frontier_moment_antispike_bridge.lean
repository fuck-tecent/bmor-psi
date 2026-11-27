import Mathlib

namespace PEqualNP.Outside

theorem L_goldbach_frontier_moment_antispike_bridge :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0
    let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
    let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) =>
      Finset.sum (Finset.range (n + 1)) (fun k => (u k : ℂ) * E ((k : ℝ) * t))
    let Q := fun n : ℕ => (Nat.log 2 (n + 2)) ^ 2
    let f := fun (n : ℕ) (t : ℝ) => (S n w t) ^ 2 * E (-(n : ℝ) * t)
    let Q₁ := fun n : ℕ => ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
    let H := fun n : ℕ => 256 * Q₁ n * Q n
    let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ,
      1 ≤ q ∧ q ≤ Q₁ n ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ (H n : ℝ) / ((q : ℝ) * (n : ℝ))}
    let deepMinor := fun n : ℕ =>
      intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (f n) t) (0 : ℝ) 1 MeasureTheory.volume
    let deepCoeff := fun (n m : ℕ) => intervalIntegral
      (fun t => (wideArcs n)ᶜ.indicator (fun u => (S n w u) ^ 2 * E (-(m : ℝ) * u)) t)
      (0 : ℝ) 1 MeasureTheory.volume
    (∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∑ m ∈ Finset.Icc n (2 * n), ‖deepCoeff n m‖ ^ 2) ≤ (n : ℝ) ^ (8 / 3 + η)) →
    (∀ e : ℝ, 0 < e → ∃ (η : ℝ) (N : ℕ), 0 < η ∧
      ∀ n : ℕ, N ≤ n → Even n → ∃ ω : ℕ → ℝ, (∀ m : ℕ, 0 ≤ ω m) ∧
        ((∑ m ∈ Finset.Icc n (2 * n), (ω m) ^ 2) * (n : ℝ) ^ (8 / 3 + η) ≤
          ((e / 2) * (n : ℝ)) ^ 2) ∧
        (∑ m ∈ Finset.Icc n (2 * n), ω m * (deepCoeff n m).re) - (e / 2) * (n : ℝ) ≤
          (deepMinor n).re) →
    ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      -(e * (n : ℝ)) ≤ (deepMinor n).re := by
  intro w E S Q f Q₁ H wideArcs deepMinor deepCoeff hMoment hSmooth e he
  obtain ⟨η, NSmooth, hη, hSmoothAt⟩ := hSmooth e he
  obtain ⟨NMoment, hMomentAt⟩ := hMoment η hη
  refine ⟨max NSmooth NMoment, ?_⟩
  intro n hn hEven
  obtain ⟨ω, _, hWeight, hTransfer⟩ := hSmoothAt n ((le_max_left _ _).trans hn) hEven
  let I := Finset.Icc n (2 * n)
  have hRealMoment : (∑ m ∈ I, (deepCoeff n m).re ^ 2) ≤ (n : ℝ) ^ (8 / 3 + η) := by
    calc
      _ ≤ ∑ m ∈ I, ‖deepCoeff n m‖ ^ 2 := by
        refine Finset.sum_le_sum fun m _ => ?_
        rw [← sq_abs (deepCoeff n m).re]
        exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 (Complex.abs_re_le_norm _)
      _ ≤ _ := hMomentAt n ((le_max_right _ _).trans hn)
  have hSquare : (∑ m ∈ I, ω m * (deepCoeff n m).re) ^ 2 ≤ ((e / 2) * (n : ℝ)) ^ 2 := by
    calc
      _ ≤ (∑ m ∈ I, (ω m) ^ 2) * (∑ m ∈ I, (deepCoeff n m).re ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq I ω (fun m => (deepCoeff n m).re)
      _ ≤ (∑ m ∈ I, (ω m) ^ 2) * (n : ℝ) ^ (8 / 3 + η) :=
        mul_le_mul_of_nonneg_left hRealMoment (Finset.sum_nonneg fun m _ => sq_nonneg (ω m))
      _ ≤ _ := hWeight
  have hAverage := (abs_le_of_sq_le_sq' hSquare (by positivity)).1
  change (∑ m ∈ I, ω m * (deepCoeff n m).re) - (e / 2) * (n : ℝ) ≤ (deepMinor n).re at hTransfer
  linarith only [hAverage, hTransfer]

end PEqualNP.Outside
