import Mathlib

namespace Conjectures.JoshiAbc

theorem TowerWeights :
  ∀ (m n : ℕ) (v : Fin n → Fin m) (w : Fin n → ℝ) (d f : Fin m → ℝ),
    (∀ i, ((Finset.univ : Finset (Fin n)).filter (fun j => v j=i)).sum w = d i) →
    (∑ j, w j*f (v j)) = ∑ i, d i*f i := by
  intro m n v w d f h
  have h1 : (∑ j, w j * f (v j))
      = ∑ i : Fin m, ∑ j ∈ (Finset.univ : Finset (Fin n)) with v j = i, w j * f (v j) :=
    (Finset.sum_fiberwise (Finset.univ : Finset (Fin n)) v _).symm
  have h2 : (∑ i : Fin m, ∑ j ∈ (Finset.univ : Finset (Fin n)) with v j = i, w j * f (v j))
      = ∑ i : Fin m, ∑ j ∈ (Finset.univ : Finset (Fin n)) with v j = i, w j * f i := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j hj
    rw [(Finset.mem_filter.1 hj).2]
  have h3 : (∑ i : Fin m, ∑ j ∈ (Finset.univ : Finset (Fin n)) with v j = i, w j * f i)
      = ∑ i : Fin m, d i * f i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul, h i]
  exact h1.trans (h2.trans h3)

end Conjectures.JoshiAbc
