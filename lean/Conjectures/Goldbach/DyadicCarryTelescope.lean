import Mathlib

/-!
# PREPUB goldbach: `L-goldbach-dyadic-carry-telescope`

The reflection correlation telescopes over the dyadic layers: with `M = 2^K` and
`R d = (d/M) · ∑_r A d r · A d ((N+d-r) % d)`, the level increments
`C k = R (2^(k+1)) - R (2^k)` sum to `R M - R 1`, and for `N < M` one has
`R M = ∑_n w n · w (N-n)` and `R 1 = (∑ w)^2 / M`.
The increment identity is the (inlined) dyadic carry increment lemma.
Self-contained, Mathlib only.
-/

open scoped BigOperators

namespace PEqualNP.Outside

/-- The dyadic carry increment (inlined; needed as a step of the telescope). -/
lemma carry_increment_lemma :
    ∀ (N q M : ℕ) (w : ℕ → ℝ), 0 < q → 0 < M →
      let A := fun (d r : ℕ) => ∑ n ∈ (Finset.range (N+1)).filter (fun n => n % d = r), w n
      let R := fun d : ℕ => (d : ℝ) / M * ∑ r ∈ Finset.range d, A d r * A d ((N+d-r)%d)
      let D := fun r : ℕ => A (2*q) r - A (2*q) (r+q)
      R (2*q) - R q = (q : ℝ) / M * ∑ r ∈ Finset.range q,
        (if (N+2*q-r)%(2*q) < q then (1 : ℝ) else -1) * D r * D ((N+q-r)%q) := by
  intro N q M w hq hM
  dsimp only
  set A : ℕ → ℕ → ℝ := fun d r => ∑ n ∈ (Finset.range (N+1)).filter (fun n => n % d = r), w n with hA
  set R : ℕ → ℝ := fun d => (d : ℝ) / M * ∑ r ∈ Finset.range d, A d r * A d ((N+d-r)%d) with hR
  set D : ℕ → ℝ := fun r => A (2*q) r - A (2*q) (r+q) with hD
  have hq0 : 0 < 2*q := by omega
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hdiv : q ∣ 2*q := ⟨2, by ring⟩
  -- Step 1: `A q s = A (2q) s + A (2q) (s+q)` for `s < q`
  have hsplit : ∀ s : ℕ, s < q → A q s = A (2*q) s + A (2*q) (s+q) := by
    intro s hs
    simp only [hA]
    have hset : (Finset.range (N+1)).filter (fun n => n % q = s)
        = (Finset.range (N+1)).filter (fun n => n % (2*q) = s) ∪
          (Finset.range (N+1)).filter (fun n => n % (2*q) = s+q) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union]
      constructor
      · rintro ⟨hn, hmod⟩
        have hxlt : n % (2*q) < 2*q := Nat.mod_lt _ hq0
        have hqq : n % (2*q) % q = s := by
          rw [← hmod]
          exact Nat.mod_mod_of_dvd n hdiv
        rcases Nat.lt_or_ge (n % (2*q)) q with hlt | hge
        · exact Or.inl ⟨hn, by simpa [Nat.mod_eq_of_lt hlt] using hqq⟩
        · refine Or.inr ⟨hn, ?_⟩
          have h1 : n % (2*q) % q = n % (2*q) - q := by
            rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
          rw [h1] at hqq
          omega
      · rintro (⟨hn, hmod⟩ | ⟨hn, hmod⟩)
        · refine ⟨hn, ?_⟩
          rw [← Nat.mod_mod_of_dvd n hdiv, hmod, Nat.mod_eq_of_lt hs]
        · refine ⟨hn, ?_⟩
          rw [← Nat.mod_mod_of_dvd n hdiv, hmod, Nat.add_mod, Nat.mod_eq_of_lt hs,
            Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt hs]
    have hdisj : Disjoint ((Finset.range (N+1)).filter (fun n => n % (2*q) = s))
        ((Finset.range (N+1)).filter (fun n => n % (2*q) = s+q)) := by
      rw [Finset.disjoint_filter]
      intro n _ h1 h2
      omega
    rw [hset, Finset.sum_union hdisj]
  -- Abbreviations for the three summands
  set T : ℕ → ℝ := fun r => A (2*q) r * A (2*q) ((N+2*q-r)%(2*q)) with hT
  set T' : ℕ → ℝ := fun r => A (2*q) (r+q) * A (2*q) ((N+2*q-(r+q))%(2*q)) with hT'
  set U : ℕ → ℝ := fun r => A q r * A q ((N+q-r)%q) with hU
  -- Step 2: unfold the two sides
  have hR2' : R (2*q) = ((2*q : ℕ) : ℝ) / M * ∑ r ∈ Finset.range (2*q), T r := by
    rw [hR]
  have hR2 : R (2*q) = ((2*q : ℕ) : ℝ) / M *
      ((∑ r ∈ Finset.range q, T r) + (∑ r ∈ Finset.range q, T' r)) := by
    rw [hR2']
    have hTq : (∑ x ∈ Finset.range q, T (q+x)) = ∑ r ∈ Finset.range q, T' r := by
      refine Finset.sum_congr rfl (fun r hr => ?_)
      simp only [hT, hT']
      rw [Nat.add_comm q r]
    rw [show 2*q = q+q by ring, Finset.sum_range_add, hTq]
  have hRq : R q = (q : ℝ) / M * ∑ r ∈ Finset.range q, U r := by
    rw [hR]
  -- Step 3: combine both sides
  have hcomb : R (2*q) - R q =
      (q : ℝ) / M * ∑ r ∈ Finset.range q, (2*T r + 2*T' r - U r) := by
    rw [hR2, hRq]
    have e : (∑ r ∈ Finset.range q, (2*T r + 2*T' r - U r))
        = 2 * (∑ r ∈ Finset.range q, T r) + 2 * (∑ r ∈ Finset.range q, T' r)
            - (∑ r ∈ Finset.range q, U r) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [e]
    have h2q : ((2*q : ℕ) : ℝ) = 2*(q : ℝ) := by push_cast; ring
    rw [h2q]
    field_simp
  -- Step 4: pointwise identity on `r < q`
  have hpoint : ∀ r : ℕ, r < q →
      2*T r + 2*T' r - U r
        = (if (N+2*q-r)%(2*q) < q then (1 : ℝ) else -1) * D r * D ((N+q-r)%q) := by
    intro r hr
    set u : ℕ := (N+q-r) % (2*q) with hu
    set t : ℕ := (N+q-r) % q with ht
    have hu_lt : u < 2*q := Nat.mod_lt _ hq0
    have ht_lt : t < q := Nat.mod_lt _ hq
    have ht_eq : t = u % q := by
      rw [ht, hu, Nat.mod_mod_of_dvd _ hdiv]
    have ht_mod : (N+q-r) % q = t := by rw [ht]
    have hs_eq : (N+2*q-r) % (2*q) = (u + q) % (2*q) := by
      have harg : N+2*q-r = (N+q-r) + q := by omega
      rw [harg, Nat.add_mod, hu, Nat.mod_eq_of_lt (by omega : q < 2*q)]
    have hsub : (N+2*q-(r+q)) % (2*q) = u := by
      have harg : N+2*q-(r+q) = N+q-r := by omega
      rw [harg, hu]
    have hAr : A q r = A (2*q) r + A (2*q) (r+q) := hsplit r hr
    have hAt : A q t = A (2*q) t + A (2*q) (t+q) := hsplit t ht_lt
    simp only [hT, hT', hU, hD, hAr, hAt, hs_eq, hsub, ht_mod]
    rcases Nat.lt_or_ge u q with huq | huq
    · -- Case 1: `u < q`; then `s = u+q`, `t = u`, sign `-1`
      have ht_eq_u : t = u := by rw [ht_eq, Nat.mod_eq_of_lt huq]
      have hs : (u + q) % (2*q) = u+q := Nat.mod_eq_of_lt (by omega)
      have hsign : (if (u + q) % (2*q) < q then (1 : ℝ) else -1) = -1 := by
        rw [hs]
        simp only [if_neg (by omega : ¬ u + q < q)]
      rw [hsign, hs, ht_eq_u]
      ring
    · -- Case 2: `q ≤ u < 2q`; then `s = u-q = t`, sign `+1`
      have ht_eq_u : t = u - q := by
        rw [ht_eq]
        rw [Nat.mod_eq_sub_mod huq, Nat.mod_eq_of_lt (by omega)]
      have hs : (u + q) % (2*q) = u - q := by
        have harg : u + q = (u-q) + 2*q := by omega
        rw [harg, Nat.add_mod, Nat.mod_eq_of_lt (by omega : u - q < 2*q),
          Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt (by omega : u - q < 2*q)]
      have hsign : (if (u + q) % (2*q) < q then (1 : ℝ) else -1) = 1 := by
        rw [hs]
        simp only [if_pos (by omega : u - q < q)]
      have htq : t + q = u := by omega
      rw [hsign, hs, ht_eq_u, show u - q + q = u by omega]
      ring
  rw [hcomb]
  congr 1
  exact Finset.sum_congr rfl (fun r hr => hpoint r (Finset.mem_range.mp hr))


/-- **Dyadic carry telescope**: the reflected correlation is the flat term plus the
telescoping sum of the dyadic carry increments. -/
theorem L_goldbach_dyadic_carry_telescope :
    ∀ (N K : ℕ) (w : ℕ → ℝ), N < 2^K →
    let M : ℕ := 2^K
    let A := fun (d r : ℕ) => ∑ n ∈ (Finset.range (N+1)).filter (fun n => n % d = r), w n
    let C := fun k : ℕ =>
      let q : ℕ := 2^k
      let D := fun r : ℕ => A (2*q) r - A (2*q) (r+q)
      (q : ℝ) / M * ∑ r ∈ Finset.range q,
        (if (N+2*q-r) % (2*q) < q then (1 : ℝ) else -1) * D r * D ((N+q-r) % q)
    (∑ n ∈ Finset.range (N+1), w n * w (N-n)) =
      (∑ n ∈ Finset.range (N+1), w n)^2 / M + ∑ k ∈ Finset.range K, C k := by
  intro N K w hNK
  let M : ℕ := 2^K
  let A : ℕ → ℕ → ℝ := fun d r =>
    ∑ n ∈ (Finset.range (N+1)).filter (fun n => n % d = r), w n
  let C : ℕ → ℝ := fun k =>
    let q : ℕ := 2^k
    let D : ℕ → ℝ := fun r => A (2*q) r - A (2*q) (r+q)
    (q : ℝ) / M * ∑ r ∈ Finset.range q,
      (if (N+2*q-r) % (2*q) < q then (1 : ℝ) else -1) * D r * D ((N+q-r) % q)
  show (∑ n ∈ Finset.range (N+1), w n * w (N-n)) =
    (∑ n ∈ Finset.range (N+1), w n)^2 / M + ∑ k ∈ Finset.range K, C k
  let R : ℕ → ℝ := fun d => (d : ℝ) / M * ∑ r ∈ Finset.range d, A d r * A d ((N+d-r)%d)
  have hMpos : 0 < M := by
    have : 0 < 2^K := by positivity
    simpa [M] using this
  have hNMs : N < M := by simpa [M] using hNK
  have hMne : (M : ℝ) ≠ 0 := by
    have h : (0:ℝ) < (M:ℝ) := by exact_mod_cast hMpos
    exact ne_of_gt h
  -- value of `A M`
  have hAM : ∀ r, A M r = if r ≤ N then w r else 0 := by
    intro r
    simp only [A]
    by_cases hrN : r ≤ N
    · have hfilter : (Finset.range (N+1)).filter (fun n => n % M = r) = {r} := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        constructor
        · rintro ⟨hn, hmod⟩
          have hmod' : n % M = n := Nat.mod_eq_of_lt (by omega)
          have hnr : n = r := by rw [← hmod', hmod]
          exact hnr
        · rintro rfl
          exact ⟨by omega, Nat.mod_eq_of_lt (by omega)⟩
      rw [hfilter]
      simp [hrN]
    · have hempty : (Finset.range (N+1)).filter (fun n => n % M = r) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro n hn
        obtain ⟨hnr, hmod⟩ := Finset.mem_filter.mp hn
        have hnlt : n < N + 1 := Finset.mem_range.mp hnr
        have hmod' : n % M = n := Nat.mod_eq_of_lt (by omega)
        have hnr' : n = r := by rw [← hmod', hmod]
        omega
      rw [hempty]
      simp [hrN]
  -- value of `R M`: the correlation
  have hRM : R M = ∑ n ∈ Finset.range (N+1), w n * w (N-n) := by
    show (M : ℝ) / M * ∑ r ∈ Finset.range M, A M r * A M ((N+M-r)%M) = _
    rw [div_self hMne, one_mul]
    have hterm : ∀ r ∈ Finset.range M,
        A M r * A M ((N+M-r)%M) = (if r ≤ N then w r * w (N-r) else 0) := by
      intro r hr
      rw [hAM r]
      by_cases hrN : r ≤ N
      · have harg : (N + M - r) % M = N - r := by
          have h : N + M - r = (N-r) + M*1 := by omega
          rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
        rw [if_pos hrN, harg, hAM (N-r), if_pos (by omega : N-r ≤ N)]
        simp [hrN]
      · simp [hrN]
    have hsum : (∑ r ∈ Finset.range M, A M r * A M ((N+M-r)%M))
        = ∑ r ∈ Finset.range M, (if r ≤ N then w r * w (N-r) else 0) :=
      Finset.sum_congr rfl hterm
    rw [hsum, ← Finset.sum_filter]
    congr 1
    ext r
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  -- value of `R 1`: the flat term
  have hR1 : R 1 = (∑ n ∈ Finset.range (N+1), w n)^2 / M := by
    show (1:ℝ) / M * ∑ r ∈ Finset.range 1, A 1 r * A 1 ((N+1-r)%1) = _
    have hA1 : A 1 0 = ∑ n ∈ Finset.range (N+1), w n := by
      show (∑ n ∈ (Finset.range (N+1)).filter (fun n => n % 1 = 0), w n) = _
      rw [show (Finset.range (N+1)).filter (fun n => n % 1 = 0) = Finset.range (N+1) by
        ext n
        simp [Nat.mod_one]]
    rw [Finset.sum_range_one, Nat.mod_one, hA1]
    ring
  -- each `C k` is the level increment `R (2^(k+1)) - R (2^k)`
  have hCeq : ∀ k, k < K → C k = R (2^(k+1)) - R (2^k) := by
    intro k hk
    have hq : 0 < 2^k := by positivity
    have h2 : 2 * 2^k = 2^(k+1) := by rw [pow_succ]; ring
    have hinc := carry_increment_lemma N (2^k) M w hq hMpos
    dsimp only [C, R, A]
    simp only [h2] at hinc ⊢
    exact hinc.symm
  -- telescoping
  have htel : (∑ k ∈ Finset.range K, C k) = R (2^K) - R 1 := by
    have hstep : (∑ k ∈ Finset.range K, (R (2^(k+1)) - R (2^k))) = R (2^K) - R 1 := by
      have := Finset.sum_range_sub (fun k => R (2^k)) K
      simpa using this
    rw [← hstep]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hCeq k (Finset.mem_range.mp hk)]
  have hR2K : R (2^K) = R M := rfl
  rw [htel, hR2K, hRM, hR1]
  ring

end PEqualNP.Outside


/-! Canonical module-named statement (platform checker requires a declaration
named exactly after the gap module: `Conjectures.Goldbach.DyadicCarryTelescope`). -/

theorem Conjectures.Goldbach.DyadicCarryTelescope :
    ∀ (N K : ℕ) (w : ℕ → ℝ), N < 2^K →
  let M : ℕ := 2^K
  let A := fun (d r : ℕ) => ∑ n ∈ (Finset.range (N+1)).filter (fun n => n % d = r), w n
  let C := fun k : ℕ =>
    let q : ℕ := 2^k
    let D := fun r : ℕ => A (2*q) r - A (2*q) (r+q)
    (q : ℝ) / M * ∑ r ∈ Finset.range q,
      (if (N+2*q-r) % (2*q) < q then (1 : ℝ) else -1) * D r * D ((N+q-r) % q)
  (∑ n ∈ Finset.range (N+1), w n * w (N-n)) =
    (∑ n ∈ Finset.range (N+1), w n)^2 / M + ∑ k ∈ Finset.range K, C k :=
  PEqualNP.Outside.L_goldbach_dyadic_carry_telescope
