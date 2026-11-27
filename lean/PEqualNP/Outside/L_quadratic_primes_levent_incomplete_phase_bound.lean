import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_incomplete_phase_bound :
    let block := fun x : ℕ => Finset.Ioc x (2*x); let window := fun x p : ℕ => (block x).filter (fun n => p^100000 ≤ n^132301); let angle := fun p k : ℕ => fun t : ℝ => 2 * Real.pi * k * t / p; let phase := fun (p k n : ℕ) => Complex.exp (((angle p k n : ℝ) : ℂ) * Complex.I); ∀ x p k : ℕ, 0<k → k<p → ‖∑ n ∈ window x p, phase p k n‖ * ‖1-phase p k 1‖ ≤ 2 := by
  intro block window angle phase x p k hk hkp
  have hwinmem : ∀ (y q n : ℕ), n ∈ window y q ↔ y < n ∧ n ≤ 2*y ∧ q^100000 ≤ n^132301 := by
    intro y q n
    simp only [block, window]
    constructor
    · intro h
      have h1 := Finset.mem_filter.mp h
      have h2 := Finset.mem_Ioc.mp h1.1
      exact ⟨h2.1, h2.2, h1.2⟩
    · intro h
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨h.1, h.2.1⟩, h.2.2⟩
  have hwineq : ∀ (y q : ℕ), (window y q).Nonempty →
      ∃ m, m ∈ window y q ∧ window y q = Finset.Icc m (2*y) := by
    intro y q hne
    refine ⟨(window y q).min' hne, Finset.min'_mem _ hne, ?_⟩
    have hminmem : (window y q).min' hne ∈ window y q := Finset.min'_mem _ hne
    obtain ⟨hym, hm2y, hmpred⟩ := (hwinmem y q _).mp hminmem
    ext n
    rw [hwinmem y q n, Finset.mem_Icc]
    constructor
    · rintro ⟨hyn, hn2y, hpred⟩
      exact ⟨Finset.min'_le _ n ((hwinmem y q n).mpr ⟨hyn, hn2y, hpred⟩), hn2y⟩
    · rintro ⟨hmn, hn2y⟩
      exact ⟨Nat.lt_of_lt_of_le hym hmn, hn2y, le_trans hmpred (Nat.pow_le_pow_left hmn 132301)⟩
  set z : ℂ := phase p k 1 with hzdef
  have hz : ‖z‖ = 1 := by
    simp only [z, phase]
    exact Complex.norm_exp_ofReal_mul_I _
  have hphase_pow : ∀ n : ℕ, phase p k n = z^n := by
    intro n
    have h1 : angle p k (n:ℝ) = (n:ℝ) * angle p k 1 := by
      simp only [angle]
      ring
    have harg : ((angle p k (n:ℝ) : ℝ) : ℂ) * Complex.I
        = (n:ℂ) * (((angle p k 1 : ℝ) : ℂ) * Complex.I) := by
      rw [h1]
      push_cast
      ring
    simp only [phase, z]
    rw [harg, Complex.exp_nat_mul]
    norm_num
  have hswap : (∑ n ∈ window x p, phase p k n) = ∑ n ∈ window x p, z^n := by
    apply Finset.sum_congr rfl
    intro n hn
    exact hphase_pow n
  have hgeo : ∀ m N : ℕ, m ≤ N → (1 - z) * (∑ n ∈ Finset.Icc m N, z^n) = z^m - z^(N+1) := by
    intro m N hle
    rw [mul_comm, Finset.sum_mul]
    have h2 : (∑ n ∈ Finset.Icc m N, (z^n * (1 - z))) = ∑ n ∈ Finset.Icc m N, (z^n - z^(n+1)) := by
      apply Finset.sum_congr rfl
      intro n hn
      ring
    rw [h2]
    have h3 := Finset.sum_Icc_sub (f := fun i => -(z^i)) hle
    have h4 : (∑ i ∈ Finset.Icc m N, (-(z^(i+1)) - (-(z^i))))
        = ∑ n ∈ Finset.Icc m N, (z^n - z^(n+1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [h4] at h3
    rw [h3]
    ring
  rw [hswap]
  by_cases hne : (window x p).Nonempty
  · obtain ⟨m, hm, hIcc⟩ := hwineq x p hne
    have hmle : m ≤ 2*x := ((hwinmem x p m).mp hm).2.1
    rw [hIcc]
    have hg := hgeo m (2*x) hmle
    have hnorm1 : ‖z^m‖ = 1 := by rw [norm_pow, hz, one_pow]
    have hnorm2 : ‖z^(2*x+1)‖ = 1 := by rw [norm_pow, hz, one_pow]
    have hkey : ‖(1 - z) * (∑ n ∈ Finset.Icc m (2*x), z^n)‖ ≤ 2 := by
      rw [hg]
      calc ‖z^m - z^(2*x+1)‖ ≤ ‖z^m‖ + ‖z^(2*x+1)‖ := norm_sub_le _ _
        _ = 2 := by rw [hnorm1, hnorm2]; norm_num
    rw [norm_mul] at hkey
    calc ‖∑ n ∈ Finset.Icc m (2*x), z^n‖ * ‖1 - z‖ = ‖1 - z‖ * ‖∑ n ∈ Finset.Icc m (2*x), z^n‖ := by ring
      _ ≤ 2 := hkey
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp
