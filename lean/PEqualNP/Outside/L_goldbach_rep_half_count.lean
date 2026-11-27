import Mathlib

/-- Swapping the two primes pairs the strict lower and upper halves.
The central representation contributes once when the half is prime. -/
theorem PEqualNP.Outside.L_goldbach_rep_half_count :
    ∀ n : ℕ,
    let reps := fun n : ℕ => (Finset.range (n + 1)).filter
      (fun p => Nat.Prime p ∧ Nat.Prime (n - p))
    (reps n).card = 2 * ((reps n).filter (fun p => 2 * p < n)).card +
      (if Even n ∧ Nat.Prime (n / 2) then 1 else 0) := by
  intro n reps
  let R := reps n
  let lower := R.filter (fun p => 2*p < n)
  let upper := R.filter (fun p => n < 2*p)
  let center := R.filter (fun p => 2*p = n)
  have memR (p : ℕ) : p ∈ R ↔ p ≤ n ∧ p.Prime ∧ (n-p).Prime := by
    simp [R, reps]
  have reflect (p : ℕ) (hp : p ∈ R) : n-p ∈ R := by
    obtain ⟨h, h₁, h₂⟩ := (memR p).mp hp
    exact (memR _).mpr ⟨Nat.sub_le .., h₂, by rwa [Nat.sub_sub_self h]⟩
  have pairs : lower.card = upper.card := by
    apply Finset.card_nbij' (fun p => n-p) (fun p => n-p)
    · intro p hp
      obtain ⟨hr, hlo⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨reflect p hr, by change n < 2*(n-p); omega⟩
    · intro p hp
      obtain ⟨hr, hup⟩ := Finset.mem_filter.mp hp
      have hp_le := ((memR p).mp hr).1
      exact Finset.mem_filter.mpr ⟨reflect p hr, by change 2*(n-p) < n; omega⟩
    · intro p hp
      exact Nat.sub_sub_self ((memR p).mp (Finset.mem_filter.mp hp).1).1
    · intro p hp
      exact Nat.sub_sub_self ((memR p).mp (Finset.mem_filter.mp hp).1).1
  have diagonal : center.card = (if Even n ∧ (n/2).Prime then 1 else 0) := by
    by_cases h : Even n ∧ (n/2).Prime
    · obtain ⟨k, hk⟩ := h.1
      have hc : center = {n/2} := by
        ext p
        simp only [center, Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨_, heq⟩
          omega
        · rintro rfl
          exact ⟨(memR _).mpr ⟨by omega, h.2, by rw [show n-n/2 = n/2 by omega]; exact h.2⟩,
            by omega⟩
      simp [hc, h]
    · have hc : center = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        obtain ⟨hr, heq⟩ := Finset.mem_filter.mp hp
        exact h ⟨⟨p, by omega⟩, by rw [show n/2 = p by omega]; exact ((memR p).mp hr).2.1⟩
      simp [hc, h]
  have partition : (lower ∪ upper) ∪ center = R := by
    ext p
    simp only [lower, upper, center, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ((h | h) | h) <;> exact h.1
    · intro hp
      rcases lt_trichotomy (2*p) n with h | h | h
      · exact Or.inl (Or.inl ⟨hp,h⟩)
      · exact Or.inr ⟨hp,h⟩
      · exact Or.inl (Or.inr ⟨hp,h⟩)
  have disjointHalves : Disjoint lower upper := by
    apply Finset.disjoint_left.mpr
    intro p hl hu
    exact (Finset.mem_filter.mp hl).2.asymm (Finset.mem_filter.mp hu).2
  have disjointCenter : Disjoint (lower ∪ upper) center := by
    apply Finset.disjoint_left.mpr
    intro p hp hc
    simp only [lower, upper, center, Finset.mem_union, Finset.mem_filter] at hp hc
    omega
  have size := congrArg Finset.card partition
  rw [Finset.card_union_of_disjoint disjointCenter,
    Finset.card_union_of_disjoint disjointHalves, ← pairs, diagonal] at size
  change R.card = 2*lower.card + _
  omega
