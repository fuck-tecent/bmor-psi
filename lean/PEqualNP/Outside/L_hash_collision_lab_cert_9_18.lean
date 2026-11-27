import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside

private theorem chooseSupport (k m x : ℕ) :
    Nat.choose m (k + 1) + Nat.choose m k * x ≤
      Nat.choose x (k + 1) + Nat.choose m k * m := by
  let P (y : ℕ) := Nat.choose m (k + 1) + Nat.choose m k * y ≤
    Nat.choose y (k + 1) + Nat.choose m k * m
  change P x
  rcases le_total m x with hx | hx
  · refine Nat.le_induction (motive := fun y _ => P y) (le_refl _) ?_ x hx
    intro y hy ih
    have hs := Nat.choose_le_choose k hy
    dsimp only [P] at ih ⊢
    rw [Nat.mul_add, Nat.mul_one, Nat.choose_succ_succ']
    omega
  · refine Nat.decreasingInduction (motive := fun y _ => P y) ?_ (le_refl _) hx
    intro y hy ih
    have hs := Nat.choose_le_choose k (Nat.le_of_lt hy)
    dsimp only [P] at ih ⊢
    rw [Nat.mul_add, Nat.mul_one, Nat.choose_succ_succ'] at ih
    omega

private theorem chooseBucketSupport (k m q : ℕ) (b : Fin q → ℕ) :
    q * Nat.choose m (k + 1) + Nat.choose m k * (∑ i, b i) ≤
      (∑ i, Nat.choose (b i) (k + 1)) + q * (Nat.choose m k * m) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin q)))
    (fun i _ => chooseSupport k m (b i))
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Nat.nsmul_eq_mul, ← Finset.mul_sum] using h

theorem L_hash_collision_lab_cert_9_18 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*48620)+43758*(∑ i,b i)≤(∑ i,Nat.choose (b i) 9)+q*787644 := by
  intro q b
  have hc : Nat.choose 18 (8 + 1) = 48620 := by
    norm_num [Nat.choose_eq_factorial_div_factorial]
  have hs : Nat.choose 18 8 = 43758 := by
    norm_num [Nat.choose_eq_factorial_div_factorial]
  simpa only [hc, hs, show 43758 * 18 = (787644 : ℕ) by decide] using
    chooseBucketSupport 8 18 q b

end PEqualNP.Outside
