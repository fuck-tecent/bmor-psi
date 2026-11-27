import Mathlib

private lemma dft_ortho_sum (N : ℕ) [NeZero N] (t : ZMod N) :
    ∑ k : ZMod N, ZMod.stdAddChar (t * k) = if t = 0 then (N : ℂ) else 0 := by
  split_ifs with h
  · subst h
    simp [ZMod.card]
  · have hh := AddChar.sum_eq_zero_of_ne_one
      (ψ := AddChar.mulShift (ZMod.stdAddChar (N := N)) t) (ZMod.isPrimitive_stdAddChar N h)
    simpa [AddChar.mulShift_apply] using hh

private lemma dft_apply_mul (N : ℕ) [NeZero N] (Φ : ZMod N → ℂ) (k : ZMod N) :
    ZMod.dft Φ k = ∑ j : ZMod N, ZMod.stdAddChar (-(j*k)) * Φ j := by
  rw [ZMod.dft_apply]
  simp only [Algebra.smul_def]
  simp

private lemma star_stdAddChar_neg (N : ℕ) [NeZero N] (x : ZMod N) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  simpa [RCLike.star_def] using (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := N)) x).symm

theorem PEqualNP.Outside.L_quadratic_primes_levent_finite_dft_parseval :
    ∀ (N : ℕ) [NeZero N] (f g : ZMod N → ℂ), (∑ k : ZMod N, ZMod.dft f k * star (ZMod.dft g k)) = (N : ℂ) * ∑ n : ZMod N, f n * star (g n) := by
  intro N _ f g
  calc
    (∑ k : ZMod N, ZMod.dft f k * star (ZMod.dft g k))
        = ∑ k : ZMod N, ∑ j : ZMod N, ∑ m : ZMod N,
            (ZMod.stdAddChar (-(j*k)) * f j) * (star (ZMod.stdAddChar (-(m*k))) * star (g m)) := by
          apply Finset.sum_congr rfl; intro k _
          rw [dft_apply_mul, dft_apply_mul]
          rw [star_sum]
          rw [Finset.sum_mul_sum]
          apply Finset.sum_congr rfl; intro j _
          apply Finset.sum_congr rfl; intro m _
          rw [star_mul']
    _ = ∑ k : ZMod N, ∑ j : ZMod N, ∑ m : ZMod N,
            (ZMod.stdAddChar ((m-j)*k) * (f j * star (g m))) := by
          apply Finset.sum_congr rfl; intro k _
          apply Finset.sum_congr rfl; intro j _
          apply Finset.sum_congr rfl; intro m _
          rw [star_stdAddChar_neg]
          simp only [neg_neg]
          have hc : ZMod.stdAddChar (-(j*k)) * ZMod.stdAddChar (m*k) = ZMod.stdAddChar ((m-j)*k) := by
            rw [← AddChar.map_add_eq_mul]; congr 1; ring
          rw [← hc]; ring
    _ = ∑ j : ZMod N, ∑ m : ZMod N, ∑ k : ZMod N,
            (ZMod.stdAddChar ((m-j)*k) * (f j * star (g m))) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.sum_comm]
    _ = ∑ j : ZMod N, ∑ m : ZMod N,
            (∑ k : ZMod N, ZMod.stdAddChar ((m-j)*k)) * (f j * star (g m)) := by
          apply Finset.sum_congr rfl; intro j _
          apply Finset.sum_congr rfl; intro m _
          rw [← Finset.sum_mul]
    _ = ∑ j : ZMod N, ∑ m : ZMod N,
            (if m - j = 0 then (N:ℂ) else 0) * (f j * star (g m)) := by
          simp only [dft_ortho_sum]
    _ = ∑ j : ZMod N, (N:ℂ) * (f j * star (g j)) := by
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.sum_eq_single j]
          · simp
          · intro m _ hm
            simp [sub_eq_zero, hm]
          · intro hj; exact absurd (Finset.mem_univ j) hj
    _ = (N:ℂ) * ∑ n : ZMod N, f n * star (g n) := by
          rw [Finset.mul_sum]
