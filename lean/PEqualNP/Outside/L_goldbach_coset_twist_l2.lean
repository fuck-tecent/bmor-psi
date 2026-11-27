import Mathlib

open scoped ComplexConjugate

theorem PEqualNP.Outside.L_goldbach_coset_twist_l2 :
    let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let B := fun n s : ℕ => ∑ k ∈ (Finset.range (n+1)).filter (fun k => k ≤ s ∧ s-k ≤ n), w k*w (s-k); let Y := fun (n q : ℕ) (z : ℂ) => (B n n:ℂ) + ∑ h ∈ Finset.Icc 1 (n/q), ((B n (n+h*q):ℂ)*z^h + (B n (n-h*q):ℂ)*(z⁻¹)^h); ∀ (n q L : ℕ) (z : ℂ), 0<q → 2*(n/q)<L → IsPrimitiveRoot z L → (∑ j ∈ Finset.range L, ‖Y n q (z^j)-(B n n:ℂ)‖^2)/(L:ℝ) = ∑ h ∈ Finset.Icc 1 (n/q), ((B n (n+h*q))^2+(B n (n-h*q))^2) := by
  classical
  intro w B Y n q L z _ hL hz
  have hL0 : L ≠ 0 := by omega
  have hz0 := hz.ne_zero hL0
  let I := Finset.Icc 1 (n / q)
  let S := I.disjSum I
  let freq : ℕ ⊕ ℕ → ℕ := Sum.elim id (fun h => L - h)
  let p := fun i => z ^ freq i
  let c : ℕ ⊕ ℕ → ℝ := Sum.elim (fun h => B n (n+h*q)) (fun h => B n (n-h*q))
  have bounds (i) (hi : i ∈ S) : freq i < L := by
    cases i <;> simp_all [S, I, freq] <;> omega
  have hinj (i k) (hi : i ∈ S) (hk : k ∈ S) (he : p i = p k) : i = k := by
    have heq := hz.pow_inj (bounds i hi) (bounds k hk) he
    cases i <;> cases k <;> simp_all [S, I, freq] <;> omega
  have root (i) : (p i)^L = 1 := by
    dsimp [p]
    rw [← pow_mul, Nat.mul_comm, pow_mul, hz.pow_eq_one, one_pow]
  have pnz (i) : p i ≠ 0 := pow_ne_zero _ hz0
  have kernel (i k) (hi : i ∈ S) (hk : k ∈ S) :
      (∑ j ∈ Finset.range L, (p i / p k)^j) = if i = k then (L : ℂ) else 0 := by
    by_cases he : i = k
    · subst k
      simp [div_self (pnz i)]
    · have hratio : p i / p k ≠ 1 := fun h => he (hinj i k hi hk ((div_eq_one_iff_eq (pnz k)).mp h))
      rw [geom_sum_eq hratio L, div_pow, root, root]
      simp [he]
  have expand (j : ℕ) : ((‖∑ i ∈ S, (c i : ℂ) * p i ^ j‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ k ∈ S, ((c i : ℂ) * c k) * (p i / p k)^j := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_mul, map_pow, Complex.conj_ofReal, ← Complex.inv_eq_conj
      (Complex.norm_eq_one_of_pow_eq_one (root k) hL0), div_pow, div_eq_mul_inv, inv_pow]
    ring
  have energy : (∑ j ∈ Finset.range L, ‖∑ i ∈ S, (c i : ℂ) * p i ^ j‖^2) =
      (∑ i ∈ S, c i ^ 2) * (L : ℝ) := by
    apply Complex.ofReal_injective
    push_cast only [Complex.ofReal_sum, Complex.ofReal_mul]
    simp_rw [expand]
    rw [Finset.sum_comm, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    calc
      _ = ∑ k ∈ S, ((c i : ℂ) * c k) * (if i = k then (L : ℂ) else 0) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [← Finset.mul_sum, kernel i k hi hk]
      _ = _ := by simp [mul_ite, hi, pow_two]
  have center (j : ℕ) : Y n q (z^j) - (B n n : ℂ) =
      ∑ i ∈ S, (c i : ℂ) * p i ^ j := by
    simp only [Y, add_sub_cancel_left, S, Finset.sum_disjSum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h hh
    have hle : h ≤ L := by have := (Finset.mem_Icc.mp hh).2; omega
    have hcomp : z ^ (L-h) = (z^h)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_add, Nat.sub_add_cancel hle, hz.pow_eq_one]
    simp only [p, c, freq, Sum.elim_inl, Sum.elim_inr, id_eq, hcomp, inv_pow]
    rw [← pow_mul, Nat.mul_comm j h, pow_mul]
  simp_rw [center]
  rw [div_eq_iff (by exact_mod_cast hL0 : (L:ℝ) ≠ 0), energy]
  simp [S, I, c, Finset.sum_disjSum, Finset.sum_add_distrib]
