import Mathlib

theorem PEqualNP.Outside.L_goldbach_pair_errors_self :
    let C := fun (a b : ℕ → ℝ) (n : ℕ) => ∑ k ∈ Finset.range (n+1), a k*b (n-k); ∀ a e n,C (fun k => a k+e k) (fun k => a k+e k) n-C a a n=2*C a e n+C e e n := by
  dsimp only
  intro a e n
  have reflect_mem (k : ℕ) (_ : k ∈ Finset.range (n + 1)) :
      n - k ∈ Finset.range (n + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le n k))
  have reflect_twice (k : ℕ) (hk : k ∈ Finset.range (n + 1)) : n - (n - k) = k := by
    have := Finset.mem_range.mp hk
    omega
  have cross :
      (∑ k ∈ Finset.range (n + 1), e k * a (n - k)) =
        ∑ k ∈ Finset.range (n + 1), a k * e (n - k) := by
    refine Finset.sum_bij' (fun k _ => n - k) (fun k _ => n - k)
      reflect_mem reflect_mem reflect_twice reflect_twice ?_
    intro k hk
    simpa only [reflect_twice k hk] using mul_comm (e k) (a (n - k))
  simp only [add_mul, mul_add, Finset.sum_add_distrib, cross]
  ring
