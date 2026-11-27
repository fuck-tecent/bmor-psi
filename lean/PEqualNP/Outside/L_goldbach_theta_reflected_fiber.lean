import Mathlib

theorem PEqualNP.Outside.L_goldbach_theta_reflected_fiber :
    ∀ (m r : ℕ) (c : Fin m → Fin r) (R : Fin m ≃ Fin m) (S : Fin r ≃ Fin r) (a : Fin m → ℝ),
      (∀ i, c (R i)=S (c i)) →
      let F := fun j => Finset.univ.filter (fun i => c i=j)
      ∀ j, (∑ i ∈ F j, a (R i))/((F j).card:ℝ) = (∑ i ∈ F (S j), a i)/((F (S j)).card:ℝ) := by
  intro m r c R S a h
  let F : Fin r → Finset (Fin m) := fun j => Finset.univ.filter (fun i => c i = j)
  change ∀ j : Fin r,
    (∑ i ∈ F j, a (R i)) / ((F j).card : ℝ) = (∑ i ∈ F (S j), a i) / ((F (S j)).card : ℝ)
  intro j
  have himage : (F j).image R = F (S j) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have hci : c i = j := by
        simpa only [F, Finset.mem_filter, Finset.mem_univ, true_and] using hi
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [h i, hci]
    · intro hx
      have hcx : c x = S j := by
        simpa only [F, Finset.mem_filter, Finset.mem_univ, true_and] using hx
      refine Finset.mem_image.mpr ⟨R.symm x, ?_, ?_⟩
      · simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
        have h1 : c (R (R.symm x)) = S (c (R.symm x)) := h (R.symm x)
        rw [Equiv.apply_symm_apply] at h1
        exact S.injective (h1.symm.trans hcx)
      · exact Equiv.apply_symm_apply R x
  have hsum : (∑ i ∈ F j, a (R i)) = ∑ i ∈ F (S j), a i := by
    rw [← Finset.sum_image (f := a) (g := R) (s := F j)
      (fun x _ y _ hxy => R.injective hxy), himage]
  have hcard : (F j).card = (F (S j)).card := by
    rw [← Finset.card_image_of_injective (s := F j) (f := R) R.injective, himage]
  rw [hsum, hcard]
