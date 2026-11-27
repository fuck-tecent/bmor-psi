import Mathlib

open Finset

theorem PEqualNP.Outside.L_goldbach_residual_quadratic_signal :
    let F := fun x q r : ℕ => (Finset.range (x+1)).filter (fun k => k % q=r); let e := fun (x q : ℕ) (a : ℕ → ℝ) k => let f := F x q (k % q); a k-(∑ i ∈ f, a i)/(f.card:ℝ); let C := fun (x : ℕ) (a b : ℕ → ℝ) s => ∑ k ∈ (Finset.range (x+1)).filter (fun k => k ≤ s ∧ s-k ≤ x), a k*b (s-k); ∀ (x q c : ℕ) (a b : ℕ → ℝ), c<q → (∑ s ∈ (Finset.range (2*x+1)).filter (fun s => s % q=c), (s:ℝ)^2*C x (e x q a) (e x q b) s) = 2*∑ r ∈ Finset.range q, ((∑ i ∈ F x q r, (i:ℝ)*e x q a i)*(∑ j ∈ F x q ((c % q+q-r) % q), (j:ℝ)*e x q b j)) := by
  intro F e C x q c a b hc
  let u := e x q
  let I := range (x + 1)
  let P := I ×ˢ I
  let totals := (range (2*x+1)).filter (fun s => s % q = c)
  let term := fun z : ℕ × ℕ => ((z.1 + z.2 : ℕ) : ℝ)^2 * (u a z.1 * u b z.2)
  let partner := fun r => (c % q + q - r) % q
  let pairs := P.filter (fun z => z.1 + z.2 ∈ totals)
  have hq : 0 < q := by omega
  have byTotal (s : ℕ) : (s:ℝ)^2 * C x (u a) (u b) s =
      ∑ z ∈ P.filter (fun z => z.1 + z.2 = s), term z := by
    dsimp only [C]
    rw [mul_sum]
    apply sum_bij' (fun k _ => (k, s-k)) (fun z _ => z.1)
    · intro k hk
      simp only [mem_filter, mem_range] at hk
      simp only [P, I, mem_filter, mem_product, mem_range]
      omega
    · rintro ⟨i,j⟩ hij
      simp only [P, I, mem_filter, mem_product, mem_range] at hij
      simp only [mem_filter, mem_range]
      omega
    · intros; rfl
    · rintro ⟨i,j⟩ hij
      have hs := (mem_filter.mp hij).2
      change i+j = s at hs
      exact Prod.ext rfl (by dsimp; omega)
    · intro k hk
      have hks := (mem_filter.mp hk).2.1
      dsimp only [term]
      rw [Nat.add_sub_of_le hks]
  have centered (v : ℕ → ℝ) (r : ℕ) : (∑ i ∈ F x q r, u v i) = 0 := by
    calc
      _ = ∑ i ∈ F x q r, (v i - (∑ k ∈ F x q r, v k) / (F x q r).card) := by
        apply sum_congr rfl
        intro i hi
        change v i - _ / _ = _
        rw [(mem_filter.mp hi).2]
      _ = 0 := by
        by_cases h : F x q r = ∅
        · simp [h]
        · have hcard : ((F x q r).card : ℝ) ≠ 0 := by exact_mod_cast card_ne_zero.mpr (nonempty_iff_ne_empty.mpr h)
          rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
          field_simp
          ring
  have byResidue (r : ℕ) (hr : r < q) :
      pairs.filter (fun z => z.1 % q = r) = F x q r ×ˢ F x q (partner r) := by
    have hcanonical := Nat.mod_eq_of_lt hc
    have hpart : r + (c % q + q - r) ≡ c [MOD q] := by
      rw [hcanonical, Nat.add_sub_of_le (by omega : r ≤ c+q)]
      exact Nat.add_modulus_modEq_iff.mpr Nat.ModEq.rfl
    ext ⟨i,j⟩
    simp only [pairs, P, I, F, totals, mem_filter, mem_product, mem_range]
    constructor
    · rintro ⟨⟨⟨hi,hj⟩, _, hsum⟩, hir⟩
      have hri : i ≡ r [MOD q] := hir.trans (Nat.mod_eq_of_lt hr).symm
      have hs : i+j ≡ c [MOD q] := hsum.trans hcanonical.symm
      exact ⟨⟨hi, hir⟩, hj, hri.add_left_cancel (hs.trans hpart.symm)⟩
    · rintro ⟨⟨hi,hir⟩, hj, hjt⟩
      have hri : i ≡ r [MOD q] := hir.trans (Nat.mod_eq_of_lt hr).symm
      have hjp : j ≡ c % q + q - r [MOD q] := hjt
      have hs : i+j ≡ c [MOD q] := (hri.add hjp).trans hpart
      exact ⟨⟨⟨hi,hj⟩, by omega, Eq.trans hs hcanonical⟩, hir⟩
  have rectangle (r t : ℕ) :
      (∑ z ∈ F x q r ×ˢ F x q t, term z) =
      2 * ((∑ i ∈ F x q r, (i:ℝ) * u a i) * ∑ j ∈ F x q t, (j:ℝ) * u b j) := by
    let U := F x q r
    let V := F x q t
    have factor (f g : ℕ → ℝ) :
        (∑ z ∈ U ×ˢ V, f z.1 * g z.2) = (∑ i ∈ U, f i) * ∑ j ∈ V, g j := by
      rw [sum_product, sum_mul]
      simp only [mul_sum]
    calc
      _ = ∑ z ∈ U ×ˢ V, (((z.1:ℝ)^2 * u a z.1) * u b z.2 +
          2 * (((z.1:ℝ)*u a z.1) * ((z.2:ℝ)*u b z.2)) +
          u a z.1 * ((z.2:ℝ)^2 * u b z.2)) := by
        apply sum_congr rfl
        intro z _
        simp only [term, Nat.cast_add]
        ring
      _ = _ := by
        simp only [sum_add_distrib, ← mul_sum]
        rw [factor (fun i => (i:ℝ)^2 * u a i) (u b),
          factor (fun i => (i:ℝ) * u a i) (fun j => (j:ℝ) * u b j),
          factor (u a) (fun j => (j:ℝ)^2 * u b j)]
        simp only [U, V, centered, mul_zero, zero_mul, add_zero, zero_add]
  calc
    _ = ∑ s ∈ totals, ∑ z ∈ P.filter (fun z => z.1+z.2=s), term z :=
      sum_congr rfl (fun s _ => byTotal s)
    _ = ∑ z ∈ pairs, term z := sum_fiberwise_eq_sum_filter P totals _ term
    _ = ∑ r ∈ range q, ∑ z ∈ pairs.filter (fun z => z.1 % q = r), term z :=
      (sum_fiberwise_of_maps_to (fun z _ => mem_range.mpr (Nat.mod_lt z.1 hq)) term).symm
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro r hr
      rw [byResidue r (mem_range.mp hr)]
      exact rectangle r (partner r)
