import Mathlib

theorem PEqualNP.Outside.L_goldbach_factor_line_reduced_progression :
    let Λ := ArithmeticFunction.vonMangoldt; ∀ (n a b U : ℕ), 0 < a → 0 < b → let g := Nat.gcd a b; (∑ r ∈ Finset.Ioc U (n/a), ∑ s ∈ (Finset.Ioc U (n/b)).filter (fun s => a*r+b*s=n), Λ r * Λ s) = if g ∣ n then ∑ r ∈ (Finset.Ioc U (n/a)).filter (fun r => (a/g)*r % (b/g) = (n/g) % (b/g) ∧ U < (n-a*r)/b), Λ r * Λ ((n-a*r)/b) else 0 := by
  dsimp only
  intro n a b U ha hb
  set L := ArithmeticFunction.vonMangoldt with hL
  set g := Nat.gcd a b with hg
  have hpos : 0 < g := by rw [hg]; exact Nat.gcd_pos_of_pos_left b ha
  have hga : g ∣ a := by rw [hg]; exact Nat.gcd_dvd_left a b
  have hgb : g ∣ b := by rw [hg]; exact Nat.gcd_dvd_right a b
  have hgae : g * (a / g) = a := Nat.mul_div_cancel' hga
  have hgbe : g * (b / g) = b := Nat.mul_div_cancel' hgb
  have hinf : ∀ r ∈ Finset.Ioc U (n/a), a * r ≤ n := by
    intro r hr
    have h1 : r ≤ n / a := (Finset.mem_Ioc.mp hr).2
    have h2 : r * a ≤ n := (Nat.le_div_iff_mul_le ha).mp h1
    calc a * r = r * a := Nat.mul_comm a r
      _ ≤ n := h2
  have hdivmod : ∀ r ∈ Finset.Ioc U (n/a),
      (b ∣ n - a*r) ↔ (g ∣ n ∧ (a/g)*r % (b/g) = (n/g) % (b/g)) := by
    intro r hr
    have har : a * r ≤ n := hinf r hr
    have har' : g * ((a/g) * r) = a * r := by
      rw [← mul_assoc, hgae]
    constructor
    · intro hdvd
      obtain ⟨k, hk⟩ := hdvd
      have hn : n = a * r + b * k := by omega
      have hgn : g ∣ n := by
        rw [hn]
        exact Nat.dvd_add (hga.mul_right r) (hgb.mul_right k)
      have hneq : g * (n / g) = n := Nat.mul_div_cancel' hgn
      have hle' : (a/g) * r ≤ n / g := by
        apply Nat.le_of_mul_le_mul_left _ hpos
        rw [har', hneq]
        exact har
      have hbd : b/g ∣ (n/g) - (a/g)*r := by
        refine ⟨k, ?_⟩
        apply Nat.eq_of_mul_eq_mul_left hpos
        rw [Nat.mul_sub, hneq, har']
        rw [hk, ← mul_assoc, hgbe]
      exact ⟨hgn, (Nat.modEq_iff_dvd' hle').mpr hbd⟩
    · rintro ⟨hgn, hmod⟩
      have hneq : g * (n / g) = n := Nat.mul_div_cancel' hgn
      have hle' : (a/g) * r ≤ n / g := by
        apply Nat.le_of_mul_le_mul_left _ hpos
        rw [har', hneq]
        exact har
      have hbd : b/g ∣ (n/g) - (a/g)*r := (Nat.modEq_iff_dvd' hle').mp hmod
      obtain ⟨k, hk⟩ := hbd
      refine ⟨k, ?_⟩
      calc n - a*r = g * ((n/g) - (a/g)*r) := by rw [Nat.mul_sub, hneq, har']
        _ = g * ((b/g)*k) := by rw [hk]
        _ = b * k := by rw [← mul_assoc, hgbe]
  have key : ∀ r ∈ Finset.Ioc U (n/a),
      (∑ s ∈ (Finset.Ioc U (n/b)).filter (fun s => a*r+b*s=n), L r * L s) =
      (if (g ∣ n ∧ (a/g)*r % (b/g) = (n/g) % (b/g) ∧ U < (n-a*r)/b) then L r * L ((n-a*r)/b) else 0) := by
    intro r hr
    have har : a * r ≤ n := hinf r hr
    by_cases hc : b ∣ n - a*r ∧ U < (n-a*r)/b
    · have hc' : g ∣ n ∧ (a/g)*r % (b/g) = (n/g) % (b/g) ∧ U < (n-a*r)/b := by
        obtain ⟨h1, h2⟩ := (hdivmod r hr).mp hc.1
        exact ⟨h1, h2, hc.2⟩
      rw [ite_eq_left hc']
      have hset : (Finset.Ioc U (n/b)).filter (fun s => a*r+b*s=n) = {(n-a*r)/b} := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hUs, hsle⟩, hs⟩
          have hbs : b * s = n - a*r := by omega
          rw [← hbs, Nat.mul_div_cancel_left s hb]
        · rintro rfl
          refine ⟨⟨hc.2, Nat.div_le_div_right (Nat.sub_le n (a*r))⟩, ?_⟩
          rw [Nat.mul_div_cancel' hc.1]
          omega
      rw [hset, Finset.sum_singleton]
    · have hc' : ¬ (g ∣ n ∧ (a/g)*r % (b/g) = (n/g) % (b/g) ∧ U < (n-a*r)/b) := by
        intro h
        exact hc ⟨(hdivmod r hr).mpr ⟨h.1, h.2.1⟩, h.2.2⟩
      rw [ite_eq_right hc']
      have hset : (Finset.Ioc U (n/b)).filter (fun s => a*r+b*s=n) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro s hs hpred
        rw [Finset.mem_Ioc] at hs
        apply hc
        obtain ⟨hUs, hsle⟩ := hs
        have hbs : b * s = n - a*r := by omega
        refine ⟨⟨s, hbs.symm⟩, ?_⟩
        rw [← hbs, Nat.mul_div_cancel_left s hb]
        exact hUs
      rw [hset, Finset.sum_empty]
  calc (∑ r ∈ Finset.Ioc U (n/a), ∑ s ∈ (Finset.Ioc U (n/b)).filter (fun s => a*r+b*s=n), L r * L s)
      = ∑ r ∈ Finset.Ioc U (n/a), (if (g ∣ n ∧ (a/g)*r % (b/g) = (n/g) % (b/g) ∧ U < (n-a*r)/b) then L r * L ((n-a*r)/b) else 0) := Finset.sum_congr rfl key
    _ = ∑ r ∈ (Finset.Ioc U (n/a)).filter (fun r => g ∣ n ∧ (a/g)*r % (b/g) = (n/g) % (b/g) ∧ U < (n-a*r)/b), L r * L ((n-a*r)/b) := (Finset.sum_filter _ _).symm
    _ = if g ∣ n then ∑ r ∈ (Finset.Ioc U (n/a)).filter (fun r => (a/g)*r % (b/g) = (n/g) % (b/g) ∧ U < (n-a*r)/b), L r * L ((n-a*r)/b) else 0 := by
        by_cases hgn : g ∣ n
        · rw [ite_eq_left hgn]
          refine Finset.sum_congr ?_ ?_
          · apply Finset.filter_congr
            intro r hr
            simp [hgn]
          · intro r hr
            rfl
        · rw [ite_eq_right hgn]
          have hE : (Finset.Ioc U (n/a)).filter (fun r => g ∣ n ∧ (a/g)*r % (b/g) = (n/g) % (b/g) ∧ U < (n-a*r)/b) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro r hr hp
            exact hgn hp.1
          rw [hE]
          simp
