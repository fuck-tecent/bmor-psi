import Mathlib

theorem PEqualNP.Outside.L_goldbach_ap_refinement :
    let ap := fun (q a N : ℕ) (f : ℕ → ℝ) => Finset.sum ((Finset.range (N+1)).filter (fun k => k % q = a)) f; ∀ q d a N f, 0<q → 0<d → a<q → ap q a N f = Finset.sum (Finset.range d) (fun j => ap (q*d) (a+j*q) N f) := by
  intro ap q d a N f hq hd ha
  dsimp only [ap]
  let S : ℕ → Finset ℕ := fun j =>
    (Finset.range (N + 1)).filter (fun k => k % (q * d) = a + j * q)
  have hmod_mul : ∀ (x y r : ℕ), x < y → (x + r * y) % y = x := by
    intro x y r hxy
    induction r with
    | zero => simpa using Nat.mod_eq_of_lt hxy
    | succ r ih =>
      have hstep : x + (r + 1) * y = (x + r * y) + y := by ring
      rw [hstep, Nat.add_mod_right, ih]
  have hdisj : Set.PairwiseDisjoint (Finset.range d : Set ℕ) S := by
    intro j₁ _ j₂ _ hne
    change Disjoint (S j₁) (S j₂)
    refine Finset.disjoint_left.mpr ?_
    intro k hk1 hk2
    simp only [S, Finset.mem_filter, Finset.mem_range] at hk1 hk2
    have heq : a + j₁ * q = a + j₂ * q := hk1.2.symm.trans hk2.2
    have hmul : j₁ * q = j₂ * q := Nat.add_left_cancel heq
    exact hne (Nat.eq_of_mul_eq_mul_right hq hmul)
  have hunion :
      (Finset.range (N + 1)).filter (fun k => k % q = a) = (Finset.range d).biUnion S := by
    ext k
    simp only [S, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hkN, hka⟩
      set m := k / q
      set j := m % d
      set r := m / d
      refine ⟨j, Nat.mod_lt m hd, hkN, ?_⟩
      have h1 : k = q * m + a := by
        have hdiv := (Nat.div_add_mod k q).symm
        rwa [hka] at hdiv
      have h2 : m = d * r + j := (Nat.div_add_mod m d).symm
      have hk : k = (a + j * q) + r * (q * d) := by
        calc
          k = q * m + a := h1
          _ = q * (d * r + j) + a := by rw [h2]
          _ = (a + j * q) + r * (q * d) := by ring
      have hlt : a + j * q < q * d := by
        have hj : j + 1 ≤ d := Nat.succ_le_of_lt (Nat.mod_lt m hd)
        have hmul : (j + 1) * q ≤ d * q := Nat.mul_le_mul_right q hj
        have hmul' : q + j * q ≤ q * d := by
          calc
            q + j * q = (j + 1) * q := by ring
            _ ≤ d * q := hmul
            _ = q * d := by ring
        omega
      rw [hk]
      exact hmod_mul (a + j * q) (q * d) r hlt
    · rintro ⟨j, _, hkN, hmod⟩
      refine ⟨hkN, ?_⟩
      have hk : k = a + (d * (k / (q * d)) + j) * q := by
        have hdiv := (Nat.div_add_mod k (q * d)).symm
        rw [hmod] at hdiv
        calc
          k = q * d * (k / (q * d)) + (a + j * q) := hdiv
          _ = a + (d * (k / (q * d)) + j) * q := by ring
      rw [hk]
      exact hmod_mul a q (d * (k / (q * d)) + j) ha
  rw [hunion, Finset.sum_biUnion hdisj]
