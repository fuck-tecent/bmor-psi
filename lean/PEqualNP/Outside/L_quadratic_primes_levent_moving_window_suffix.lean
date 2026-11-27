import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_moving_window_suffix :
    let block := fun x : ℕ => Finset.Ioc x (2*x); let window := fun x p : ℕ => (block x).filter (fun n => p^100000 ≤ n^132301); ∀ x p : ℕ, (window x p).Nonempty → ∃ m ∈ window x p, window x p = Finset.Icc m (2*x) := by
  intro block window x p hnonempty
  let m := (window x p).min' hnonempty
  have hm : m ∈ window x p := Finset.min'_mem _ _
  refine ⟨m, hm, ?_⟩
  ext n
  constructor
  · intro hn
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hn,
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2⟩
  · intro hn
    obtain ⟨hmn, hnmax⟩ := Finset.mem_Icc.mp hn
    have hmblock := Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1
    have hmpow := (Finset.mem_filter.mp hm).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Ioc.mpr ⟨lt_of_lt_of_le hmblock.1 hmn, hnmax⟩,
      hmpow.trans (Nat.pow_le_pow_left hmn _)⟩
