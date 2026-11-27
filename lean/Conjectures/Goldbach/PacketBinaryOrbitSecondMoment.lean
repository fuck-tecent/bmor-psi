import Mathlib

open scoped BigOperators

namespace Conjectures.Goldbach.PacketBinaryOrbitSecondMoment_aux

noncomputable def ph (q a k : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((k : ℝ) * (a : ℝ) / (q : ℝ)) : ℝ) : ℂ) * Complex.I)

private lemma ph_unit (q a k : ℕ) : ‖ph q a k‖ = 1 := by
  unfold ph
  exact Complex.norm_exp_ofReal_mul_I _

private theorem orth (q u v : ℕ) (hq : 0 < q) :
    (∑ a ∈ Finset.range q, ph q a u * (starRingEnd ℂ) (ph q a v)) =
      if u % q = v % q then (q : ℂ) else 0 := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)
  have hζ : IsPrimitiveRoot ζ q := Complex.isPrimitiveRoot_exp q hq.ne'
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have phase (a k : ℕ) : ph q a k = (ζ ^ k) ^ a := by
    unfold ph
    dsimp only [ζ]
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have term (a : ℕ) : ph q a u * (starRingEnd ℂ) (ph q a v) =
      (ζ ^ u / ζ ^ v) ^ a := by
    rw [← Complex.inv_eq_conj (ph_unit q a v), phase, phase, div_pow, div_eq_mul_inv]
  simp_rw [term]
  have hpowiff (x y : ℕ) : ζ ^ x = ζ ^ y ↔ x % q = y % q := by
    have hfin := hζ.isOfFinOrder hq.ne'
    rw [hfin.pow_inj_mod, hζ.eq_orderOf]
  by_cases huv : u % q = v % q
  · have hbase : ζ ^ u / ζ ^ v = 1 :=
      (div_eq_one_iff_eq (pow_ne_zero v hζ0)).2 ((hpowiff u v).2 huv)
    rw [if_pos huv, hbase]
    simp
  · rw [if_neg huv, geom_sum_eq]
    · have hpow (x : ℕ) : (ζ ^ x) ^ q = 1 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
      simp [div_pow, hpow]
    · intro hbase
      apply huv
      apply (hpowiff u v).1
      exact (div_eq_one_iff_eq (pow_ne_zero v hζ0)).1 hbase

theorem second_moment (q m : ℕ) (k : ℕ → ℕ) (hq : 0 < q) :
    (∑ a ∈ Finset.range q, ‖∑ j ∈ Finset.range m, ph q a (k j)‖ ^ 2) =
      (q : ℝ) * ((((Finset.range m ×ˢ Finset.range m).filter
        (fun ij => k ij.1 % q = k ij.2 % q)).card : ℝ)) := by
  have expand (a : ℕ) :
      (∑ j ∈ Finset.range m, ph q a (k j)) *
          (starRingEnd ℂ) (∑ j ∈ Finset.range m, ph q a (k j)) =
        ∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m,
          ph q a (k j) * (starRingEnd ℂ) (ph q a (k l)) := by
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj', expand]
  have hswap :
      (∑ a ∈ Finset.range q, ∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m,
        ph q a (k j) * (starRingEnd ℂ) (ph q a (k l))) =
      ∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m, ∑ a ∈ Finset.range q,
        ph q a (k j) * (starRingEnd ℂ) (ph q a (k l)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
  rw [hswap]
  rw [Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun l _ => orth q (k j) (k l) hq))]
  rw [← Finset.sum_product']
  calc
    (∑ ij ∈ Finset.range m ×ˢ Finset.range m,
        if k ij.1 % q = k ij.2 % q then (q : ℂ) else 0) =
        (q : ℂ) * ∑ ij ∈ Finset.range m ×ˢ Finset.range m,
          if k ij.1 % q = k ij.2 % q then (1 : ℂ) else 0 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ij _
            split_ifs <;> ring
    _ = (q : ℂ) * ((((Finset.range m ×ˢ Finset.range m).filter
        (fun ij => k ij.1 % q = k ij.2 % q)).card : ℂ)) := by
      rw [Finset.sum_boole]

end Conjectures.Goldbach.PacketBinaryOrbitSecondMoment_aux

open Conjectures.Goldbach.PacketBinaryOrbitSecondMoment_aux

theorem Conjectures.Goldbach.PacketBinaryOrbitSecondMoment :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); ∀ q m : ℕ, 0<q → (∑ a ∈ Finset.range q, ‖∑ j ∈ Finset.range m, E ((((2:ℕ)^(j+1):ℕ):ℝ)*(a:ℝ)/(q:ℝ))‖^2) = (q:ℝ)*(((Finset.range m ×ˢ Finset.range m).filter (fun ij => (2:ℕ)^(ij.1+1)%q = (2:ℕ)^(ij.2+1)%q)).card:ℝ) := by
  intro E q m hq
  simpa only [E, ph] using
    (second_moment q m (fun j => (2 : ℕ) ^ (j + 1)) hq)
