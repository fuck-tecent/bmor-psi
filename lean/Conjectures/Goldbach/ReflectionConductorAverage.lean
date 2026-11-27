import Mathlib

open scoped BigOperators

noncomputable section

/-- Unit criterion for prime powers: `x` is a unit modulo `p^k` iff `p ∤ x.val`. -/
private lemma isUnit_zmod_prime_pow_iff (p k : ℕ) (hp : p.Prime) (hk : 0 < k)
    (x : ZMod (p^k)) : IsUnit x ↔ ¬ p ∣ x.val := by
  haveI : NeZero (p^k) := ⟨pow_ne_zero k hp.ne_zero⟩
  have hx : IsUnit x ↔ IsUnit (x.val : ZMod (p^k)) := by
    rw [ZMod.natCast_zmod_val x]
  rw [hx, ZMod.isUnit_iff_coprime x.val (p^k), Nat.coprime_pow_right_iff hk x.val p,
    Nat.coprime_comm, hp.coprime_iff_not_dvd]

/-- The canonical reduction `ZMod (p^k) → ZMod (p^j)` preserves and reflects units. -/
private lemma isUnit_castHom_iff (p j k : ℕ) (hp : p.Prime) (hj : 1 ≤ j) (hjk : j ≤ k)
    (h : p^j ∣ p^k) (x : ZMod (p^k)) :
    IsUnit ((ZMod.castHom h (ZMod (p^j))) x) ↔ IsUnit x := by
  haveI : NeZero (p^k) := ⟨pow_ne_zero k hp.ne_zero⟩
  haveI : NeZero (p^j) := ⟨pow_ne_zero j hp.ne_zero⟩
  rw [ZMod.castHom_apply]
  have h1 : (ZMod.cast x : ZMod (p^j)) = (x.val : ZMod (p^j)) :=
    (ZMod.natCast_val (R := ZMod (p^j)) x).symm
  rw [h1, isUnit_zmod_prime_pow_iff p j hp (by omega),
    isUnit_zmod_prime_pow_iff p k hp (by omega), ZMod.val_natCast,
    Nat.dvd_mod_iff (show p ∣ p^j from dvd_pow_self p (by omega))]

/-- Pointwise commutativity of the fibre average with the reflection, for the canonical
reduction `ZMod (p^k) → ZMod (p^j)`. -/
private lemma key_apply (p j k : ℕ) [Fact p.Prime] (hj : 1 ≤ j) (hjk : j ≤ k)
    (h : p^j ∣ p^k) (N : ZMod (p^k)) (f : ZMod (p^k) → ℂ) (x : ZMod (p^k)) :
    (∑ y ∈ (Finset.univ : Finset (ZMod (p^k))).filter
        (fun y => IsUnit y ∧ (ZMod.castHom h (ZMod (p^j))) y
          = (ZMod.castHom h (ZMod (p^j))) x),
        (if IsUnit y ∧ IsUnit (N - y) then f (N - y) else 0)) / ((p : ℂ) ^ (k - j))
      = (if IsUnit x ∧ IsUnit (N - x) then
          (∑ z ∈ (Finset.univ : Finset (ZMod (p^k))).filter
            (fun z => IsUnit z ∧ (ZMod.castHom h (ZMod (p^j))) z
              = (ZMod.castHom h (ZMod (p^j))) (N - x)), f z) / ((p : ℂ) ^ (k - j))
        else 0) := by
  have hp : p.Prime := Fact.out
  classical
  set π : ZMod (p^k) →+* ZMod (p^j) := ZMod.castHom h (ZMod (p^j)) with hπ
  have hunit : ∀ a : ZMod (p^k), IsUnit (π a) ↔ IsUnit a := by
    intro a
    rw [hπ]
    exact isUnit_castHom_iff p j k hp hj hjk h a
  by_cases hc : IsUnit x ∧ IsUnit (N - x)
  · rw [if_pos hc]
    have hNy_of : ∀ y : ZMod (p^k), IsUnit y → π y = π x → IsUnit (N - y) := by
      intro y _ hπy
      have h1 : π (N - y) = π (N - x) := by
        rw [map_sub π N y, hπy, map_sub π N x]
      have h2 : IsUnit (π (N - x)) := hc.2.map π
      exact (hunit (N - y)).mp (by rw [h1]; exact h2)
    have hSval : ∀ y ∈ (Finset.univ : Finset (ZMod (p^k))).filter
        (fun y => IsUnit y ∧ π y = π x),
        (if IsUnit y ∧ IsUnit (N - y) then f (N - y) else 0) = f (N - y) := by
      intro y hy
      obtain ⟨hyu, hyunit, hπy⟩ := Finset.mem_filter.mp hy
      exact if_pos ⟨hyunit, hNy_of y hyunit hπy⟩
    have hstep : (∑ y ∈ (Finset.univ : Finset (ZMod (p^k))).filter
          (fun y => IsUnit y ∧ π y = π x),
          (if IsUnit y ∧ IsUnit (N - y) then f (N - y) else 0))
        = ∑ y ∈ (Finset.univ : Finset (ZMod (p^k))).filter
          (fun y => IsUnit y ∧ π y = π x), f (N - y) :=
      Finset.sum_congr rfl hSval
    rw [hstep]
    have hbij : (∑ y ∈ (Finset.univ : Finset (ZMod (p^k))).filter
          (fun y => IsUnit y ∧ π y = π x), f (N - y))
        = ∑ z ∈ (Finset.univ : Finset (ZMod (p^k))).filter
          (fun z => IsUnit z ∧ π z = π (N - x)), f z := by
      refine Finset.sum_nbij (fun y => N - y) ?_ ?_ ?_ ?_
      · intro y hy
        obtain ⟨hyu, hyunit, hπy⟩ := Finset.mem_filter.mp hy
        simp only [Finset.mem_coe, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hNy_of y hyunit hπy, by
          rw [map_sub π N y, hπy, map_sub π N x]⟩
      · intro y1 hy1 y2 hy2 he
        have h2 : -y1 = -y2 := by
          have := congrArg (fun t => t - N) he
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
        have h3 := congrArg (fun t => -t) h2
        simpa using h3
      · intro z hz
        obtain ⟨hzu, hzunit, hπz⟩ := Finset.mem_filter.mp hz
        have hNz : π (N - z) = π x := by
          rw [map_sub π N z, hπz, map_sub π N x]
          abel
        have hpx : IsUnit (π x) := hc.1.map π
        refine ⟨N - z, ?_, ?_⟩
        · simp only [Finset.mem_coe, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, (hunit (N - z)).mp (by rw [hNz]; exact hpx), hNz⟩
        · show N - (N - z) = z
          abel
      · intro y _
        rfl
    rw [hbij]
  · rw [if_neg hc]
    have hzero : (∑ y ∈ (Finset.univ : Finset (ZMod (p^k))).filter
        (fun y => IsUnit y ∧ π y = π x),
        (if IsUnit y ∧ IsUnit (N - y) then f (N - y) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      obtain ⟨hyu, hyunit, hπy⟩ := Finset.mem_filter.mp hy
      rw [if_neg]
      rintro ⟨-, hNyu⟩
      rcases not_and_or.mp hc with hxbad | hNbad
      · exact hxbad ((hunit x).mp (hπy ▸ hyunit.map π))
      · have h1 : π (N - y) = π (N - x) := by
          rw [map_sub π N y, hπy, map_sub π N x]
        exact hNbad ((hunit (N - x)).mp (h1 ▸ hNyu.map π))
    rw [hzero]
    simp

/-- **PREPUB gap `L-goldbach-reflection-conductor-average`.**
The prime-power averaging operator `P` (average over the units in a fibre of the canonical
reduction `π : ZMod (p^k) → ZMod (p^j)`) commutes with the reflection `K : g ↦ g(N - ·)`. -/
theorem PEqualNP.Outside.L_goldbach_reflection_conductor_average :
    ∀ (p j k : ℕ) [Fact p.Prime], 1 ≤ j → j ≤ k →
      ∀ (h : p^j ∣ p^k) (N : ZMod (p^k)) (f : ZMod (p^k) → ℂ),
        let π := ZMod.castHom h (ZMod (p^j))
        let P := fun (g : ZMod (p^k) → ℂ) (x : ZMod (p^k)) =>
          (∑ y ∈ (Finset.univ : Finset (ZMod (p^k))).filter (fun y => IsUnit y ∧ π y = π x), g y) /
            ((p : ℂ)^(k-j))
        let K := fun (g : ZMod (p^k) → ℂ) (x : ZMod (p^k)) =>
          if IsUnit x ∧ IsUnit (N-x) then g (N-x) else 0
        P (K f) = K (P f) := by
  intro p j k hpinst hj hjk h N f
  intro π P K
  funext x
  exact key_apply p j k hj hjk h N f x

/-- Alias under the upstream module name. -/
theorem Conjectures.Goldbach.ReflectionConductorAverage :
    ∀ (p j k : ℕ) [Fact p.Prime], 1 ≤ j → j ≤ k →
      ∀ (h : p^j ∣ p^k) (N : ZMod (p^k)) (f : ZMod (p^k) → ℂ),
        let π := ZMod.castHom h (ZMod (p^j))
        let P := fun (g : ZMod (p^k) → ℂ) (x : ZMod (p^k)) =>
          (∑ y ∈ (Finset.univ : Finset (ZMod (p^k))).filter (fun y => IsUnit y ∧ π y = π x), g y) /
            ((p : ℂ)^(k-j))
        let K := fun (g : ZMod (p^k) → ℂ) (x : ZMod (p^k)) =>
          if IsUnit x ∧ IsUnit (N-x) then g (N-x) else 0
        P (K f) = K (P f) :=
  PEqualNP.Outside.L_goldbach_reflection_conductor_average
