import Mathlib

namespace Conjectures.TwinPrimes.MiddleRepeatedFirstFactorLoss_aux

/-- The multiples of a positive `d` inside `Icc a b` number at most `(b - a) / d + 1`. -/
lemma card_multiples_Icc_le {d a b : ℕ} (hd : 0 < d) :
    ((Finset.Icc a b).filter (fun x => d ∣ x)).card ≤ (b - a) / d + 1 := by
  classical
  by_cases h : ((Finset.Icc a b).filter (fun x => d ∣ x)).Nonempty
  · set T := (Finset.Icc a b).filter (fun x => d ∣ x) with hTdef
    have hmin : T.min' h ∈ T := T.min'_mem h
    have hmax : T.max' h ∈ T := T.max'_mem h
    have hminle : T.min' h ≤ T.max' h := T.min'_le _ hmax
    have hdmin : d ∣ T.min' h := (Finset.mem_filter.mp hmin).2
    have hdmax : d ∣ T.max' h := (Finset.mem_filter.mp hmax).2
    have hminI := (Finset.mem_filter.mp hmin).1
    have hmaxI := (Finset.mem_filter.mp hmax).1
    rw [Finset.mem_Icc] at hminI hmaxI
    have hdivmin : d * (T.min' h / d) = T.min' h := by
      rw [Nat.mul_comm]; exact Nat.div_mul_cancel hdmin
    have hdivmax : d * (T.max' h / d) = T.max' h := by
      rw [Nat.mul_comm]; exact Nat.div_mul_cancel hdmax
    have hdivle : T.min' h / d ≤ T.max' h / d := Nat.div_le_div_right (c := d) hminle
    have hinj : Set.InjOn (fun x : ℕ => x / d) T := by
      intro x hx y hy hxy
      dsimp only at hxy
      have hdx : d ∣ x := (Finset.mem_filter.mp hx).2
      have hdy : d ∣ y := (Finset.mem_filter.mp hy).2
      have hx' : d * (x / d) = x := by rw [Nat.mul_comm]; exact Nat.div_mul_cancel hdx
      have hy' : d * (y / d) = y := by rw [Nat.mul_comm]; exact Nat.div_mul_cancel hdy
      calc x = d * (x / d) := hx'.symm
        _ = d * (y / d) := by rw [hxy]
        _ = y := hy'
    have hsub : T.image (fun x : ℕ => x / d) ⊆ Finset.Icc (T.min' h / d) (T.max' h / d) := by
      intro q hq
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
      rw [Finset.mem_Icc]
      exact ⟨Nat.div_le_div_right (c := d) (T.min'_le x hx),
        Nat.div_le_div_right (c := d) (T.le_max' x hx)⟩
    have hstep : T.card ≤ (Finset.Icc (T.min' h / d) (T.max' h / d)).card := by
      calc T.card = (T.image (fun x : ℕ => x / d)).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.Icc (T.min' h / d) (T.max' h / d)).card := Finset.card_le_card hsub
    have hdiff : T.max' h - T.min' h = d * (T.max' h / d) - d * (T.min' h / d) := by
      rw [hdivmax, hdivmin]
    have hsub' : T.max' h / d - T.min' h / d = (T.max' h - T.min' h) / d := by
      rw [hdiff, ← Nat.mul_sub, Nat.mul_div_cancel_left _ hd]
    have hlen : T.max' h - T.min' h ≤ b - a := by omega
    calc T.card ≤ (Finset.Icc (T.min' h / d) (T.max' h / d)).card := hstep
      _ = T.max' h / d + 1 - T.min' h / d := Nat.card_Icc _ _
      _ = T.max' h / d - T.min' h / d + 1 := by omega
      _ = (T.max' h - T.min' h) / d + 1 := by rw [hsub']
      _ ≤ (b - a) / d + 1 := Nat.add_le_add_right (Nat.div_le_div_right (c := d) hlen) 1
  · have hemp : ((Finset.Icc a b).filter (fun x => d ∣ x)) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp h
    rw [hemp, Finset.card_empty]
    exact Nat.zero_le _

end Conjectures.TwinPrimes.MiddleRepeatedFirstFactorLoss_aux

theorem Conjectures.TwinPrimes.MiddleRepeatedFirstFactorLoss :
    ∀ X r : ℕ, 1<r → ((Finset.Icc X (2*X)).filter fun p => p.Prime ∧ r^2 ∣ p+2).card ≤ X/r^2+1 := by
  intro X r hr
  have hd : 0 < r ^ 2 := by positivity
  have hshift : ((Finset.Icc X (2*X)).filter fun p => p.Prime ∧ r^2 ∣ p+2).card ≤
      ((Finset.Icc (X + 2) (2 * X + 2)).filter (fun q => r ^ 2 ∣ q)).card := by
    set S := (Finset.Icc X (2 * X)).filter fun p => p.Prime ∧ r ^ 2 ∣ p + 2
    set T := (Finset.Icc (X + 2) (2 * X + 2)).filter (fun q => r ^ 2 ∣ q)
    have hinj : Set.InjOn (fun p : ℕ => p + 2) S := by
      intro p _ q _ h
      dsimp only at h
      omega
    have hsub : S.image (fun p : ℕ => p + 2) ⊆ T := by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      have hpI := (Finset.mem_filter.mp hp).1
      have hpd := (Finset.mem_filter.mp hp).2.2
      rw [Finset.mem_Icc] at hpI
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hpd⟩
    calc S.card = (S.image (fun p : ℕ => p + 2)).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ T.card := Finset.card_le_card hsub
  have hcount := Conjectures.TwinPrimes.MiddleRepeatedFirstFactorLoss_aux.card_multiples_Icc_le
    (d := r ^ 2) (a := X + 2) (b := 2 * X + 2) hd
  have hlen : 2 * X + 2 - (X + 2) = X := by omega
  rw [hlen] at hcount
  exact le_trans hshift hcount
