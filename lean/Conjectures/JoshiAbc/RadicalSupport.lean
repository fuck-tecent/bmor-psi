import Mathlib

namespace Conjectures.JoshiAbc.RadicalSupport_aux

/-- For coprime naturals the prime-factor set of the product is the disjoint union of the two
prime-factor sets, so the product of its members splits. -/
lemma prod_primeFactors_mul_of_coprime {x y : ℕ} (h : Nat.Coprime x y) :
    (x * y).primeFactors.prod id = x.primeFactors.prod id * y.primeFactors.prod id := by
  rw [h.primeFactors_mul, Finset.prod_union h.disjoint_primeFactors]

end Conjectures.JoshiAbc.RadicalSupport_aux

/-- Split the radical over the three members of a coprime triple: for coprime positive `a`, `b`
the numbers `a`, `b`, `a + b` are pairwise coprime, so the prime-factor set of `a * b * (a + b)`
is the disjoint union of the three prime-factor sets. -/
theorem Conjectures.JoshiAbc.RadicalSupport :
    let rad := fun (n : ℕ) => n.primeFactors.prod id; ∀ a b : ℕ, 0<a → 0<b → Nat.Coprime a b → rad (a*b*(a+b)) = rad a * rad b * rad (a+b) := by
  simp only []
  intro a b ha hb hab
  have hab' : Nat.Coprime a (a + b) := Nat.coprime_self_add_right.2 hab
  have hba : Nat.Coprime b (a + b) := by
    rw [add_comm]
    exact Nat.coprime_self_add_right.2 hab.symm
  have hprod : Nat.Coprime (a * b) (a + b) := Nat.coprime_mul_iff_left.2 ⟨hab', hba⟩
  have h1 := Conjectures.JoshiAbc.RadicalSupport_aux.prod_primeFactors_mul_of_coprime hprod
  have h2 := Conjectures.JoshiAbc.RadicalSupport_aux.prod_primeFactors_mul_of_coprime hab
  rw [h1, h2]
