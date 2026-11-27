import Mathlib

/-
QP-0046 · Factor a pure tensor pairing over two finite positions.

The pairing over the product of the two finite positions is a product of two independent
pairings: rewrite each finite Fourier transform with `ZMod.dft_apply` (over `ℂ` the scalar
action is multiplication), turn the sum over the product type into an iterated sum, and
recognise the right hand side as `Finset.sum_mul_sum`.
-/

theorem PEqualNP.Outside.L_quadratic_primes_levent_tensor_fourier_test :
    ∀ (p q : ℕ) [NeZero p] [NeZero q] (u : ZMod p → ℂ) (v : ZMod q → ℂ) (k : ZMod p)
      (j : ZMod q),
      (∑ z : ZMod p × ZMod q,
          (ZMod.stdAddChar (-(z.1 * k)) * u z.1) * (ZMod.stdAddChar (-(z.2 * j)) * v z.2))
        = ZMod.dft u k * ZMod.dft v j := by
  intro p q _ _ u v k j
  simp only [ZMod.dft_apply, smul_eq_mul]
  conv_lhs => rw [← Finset.univ_product_univ, Finset.sum_product]
  rw [Finset.sum_mul_sum]
