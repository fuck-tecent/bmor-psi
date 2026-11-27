import Mathlib

/- Parseval helpers and proof adapted from PR #2571 (https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/2571), under the project Apache-2.0 license. -/

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

private theorem dft_parseval_aux :
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

theorem PEqualNP.Outside.L_quadratic_primes_levent_root_mask_energy :
    ∀ (p : ℕ) [NeZero p] (a : ZMod p), let f := fun n : ZMod p => if n^2+a=0 then (1 : ℂ) else 0; (∑ k : ZMod p, ‖ZMod.dft f k‖^2) = (p : ℝ) * (((Finset.univ : Finset (ZMod p)).filter (fun n => n^2+a=0)).card : ℝ) := by
  intro p _ a
  dsimp only
  let f : ZMod p → ℂ := fun n => if n^2+a=0 then 1 else 0
  change (∑ k : ZMod p, ‖ZMod.dft f k‖^2) = (p : ℝ) *
    (((Finset.univ : Finset (ZMod p)).filter (fun n => n^2+a=0)).card : ℝ)
  have hz (z : ℂ) : (z * star z).re = ‖z‖^2 := by
    change (z * (starRingEnd ℂ) z).re = ‖z‖^2
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have h := congrArg Complex.re (dft_parseval_aux p f f)
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero] at h
  simp only [Complex.re_sum, hz] at h
  have hf : (∑ n : ZMod p, (f n * star (f n)).re) =
      (((Finset.univ : Finset (ZMod p)).filter (fun n => n^2+a=0)).card : ℝ) := by
    calc
      _ = ∑ n : ZMod p, if n^2+a=0 then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro n _
        by_cases hn : n^2+a=0 <;> simp [f, hn]
      _ = _ := Finset.sum_boole _ _
  simp only [hz] at hf
  rw [hf] at h
  exact h
