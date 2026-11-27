import Mathlib

open Finset

theorem PEqualNP.Outside.L_goldbach_residual_polynomial_order :
    let F := fun x q r : ℕ => (Finset.range (x+1)).filter (fun k => k % q=r); let C := fun (x : ℕ) (a b : ℕ → ℝ) s => ∑ k ∈ (Finset.range (x+1)).filter (fun k => k ≤ s ∧ s-k ≤ x), a k*b (s-k); ∀ (x q c m l d : ℕ) (a b : ℕ → ℝ), 0<q → d < m + l → (∀ r<q, ∀ j < m, (∑ i ∈ F x q r, (i:ℝ)^j*a i)=0) → (∀ r<q, ∀ j < l, (∑ i ∈ F x q r, (i:ℝ)^j*b i)=0) → (∑ s ∈ (Finset.range (2*x+1)).filter (fun s => s % q=c), (s:ℝ)^d*C x a b s)=0 := by
  intro F C x q c m l d a b hq hd ha hb
  let I := range (x + 1)
  let P := I ×ˢ I
  let totals := (range (2*x+1)).filter (fun s => s % q = c)
  let coord := fun z : ℕ × ℕ => (z.1 % q, z.2 % q)
  let classes := (range q ×ˢ range q).filter (fun z => (z.1 + z.2) % q = c)
  let term := fun z : ℕ × ℕ => ((z.1 + z.2 : ℕ) : ℝ)^d * (a z.1 * b z.2)
  have byTotal (s : ℕ) : (s:ℝ)^d * C x a b s =
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
  have samePairs : P.filter (fun z => z.1 + z.2 ∈ totals) =
      P.filter (fun z => coord z ∈ classes) := by
    ext ⟨i,j⟩
    simp only [P, I, totals, classes, coord, mem_filter, mem_product, mem_range]
    rw [← Nat.add_mod]
    have := Nat.mod_lt i hq
    have := Nat.mod_lt j hq
    omega
  have rectangle (r t : ℕ) (hr : r < q) (ht : t < q) :
      (∑ z ∈ F x q r ×ˢ F x q t, term z) = 0 := by
    let M := fun (k : ℕ) (z : ℕ × ℕ) =>
      ((z.1:ℝ)^k*a z.1)*((z.2:ℝ)^(d-k)*b z.2)*(d.choose k : ℝ)
    have expand (z : ℕ × ℕ) : term z = ∑ k ∈ range (d+1), M k z := by
      simp only [term, Nat.cast_add, add_pow, sum_mul]
      apply sum_congr rfl
      intro k _
      dsimp only [M]
      ring
    simp_rw [expand]
    rw [sum_comm]
    apply sum_eq_zero
    intro k hk
    have hfactor : (∑ z ∈ F x q r ×ˢ F x q t, M k z) =
        ((∑ i ∈ F x q r, (i:ℝ)^k*a i) *
         (∑ j ∈ F x q t, (j:ℝ)^(d-k)*b j))*(d.choose k:ℝ) := by
      rw [sum_product]
      simp only [M, sum_mul, mul_sum]
      exact sum_comm
    rw [hfactor]
    by_cases hkm : k < m
    · rw [ha r hr k hkm, zero_mul, zero_mul]
    · have hk' := mem_range.mp hk
      rw [hb t ht (d-k) (by omega), mul_zero, zero_mul]
  calc
    _ = ∑ s ∈ totals, ∑ z ∈ P.filter (fun z => z.1+z.2=s), term z :=
      sum_congr rfl (fun s _ => byTotal s)
    _ = ∑ z ∈ P.filter (fun z => z.1+z.2 ∈ totals), term z :=
      sum_fiberwise_eq_sum_filter P totals _ term
    _ = ∑ z ∈ P.filter (fun z => coord z ∈ classes), term z := by rw [samePairs]
    _ = ∑ v ∈ classes, ∑ z ∈ P.filter (fun z => coord z = v), term z :=
      (sum_fiberwise_eq_sum_filter P classes coord term).symm
    _ = 0 := by
      apply sum_eq_zero
      rintro ⟨r,t⟩ hv
      obtain ⟨hr, ht⟩ := mem_product.mp (mem_filter.mp hv).1
      have hrect : P.filter (fun z => coord z = (r,t)) = F x q r ×ˢ F x q t := by
        ext ⟨i,j⟩
        simp [P, I, F, coord, and_assoc, and_left_comm, and_comm]
      rw [hrect]
      exact rectangle r t (mem_range.mp hr) (mem_range.mp ht)
