import Mathlib

/-- The number of square roots of `-1` among the residues below a prime: one for the prime two,
two for the primes congruent to one mod four, and none for the primes congruent to three mod four.
The counting happens in the field of residues: a root `x` comes with `-x`, and the two standard
representatives below the prime are the value of `x` and the prime minus that value. -/
theorem PEqualNP.Outside.L_quadratic_primes_levent_root_card_splitting :
    let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a);
    ∀ p : ℕ, Nat.Prime p → (roots 1 p).card = if p=2 then 1 else if p % 4 = 1 then 2 else 0 := by
  intro roots p hp
  letI : Fact p.Prime := ⟨hp⟩
  have h1p : 1 < p := Nat.Prime.one_lt hp
  -- Unfold the local definition once, so that every later goal is a plain finset statement.
  have hroots : ∀ a q : ℕ, roots a q = Finset.filter (fun r => q ∣ r^2 + a) (Finset.range q) :=
    fun _ _ => rfl
  have key : ∀ r : ℕ, ((r^2 + 1 : ℕ) : ZMod p) = (r : ZMod p)^2 + 1 := by
    intro r
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one]
  -- Membership in the filtered range says that the cast is a square root of minus one.
  have hmem : ∀ r : ℕ, r ∈ roots 1 p ↔ r < p ∧ (r : ZMod p)^2 = -1 := by
    intro r
    rw [hroots]
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hlt, hdvd⟩
      refine ⟨hlt, neg_eq_iff_eq_neg.mp (neg_eq_iff_add_eq_zero.mpr ?_ )⟩
      rw [← key]
      exact (ZMod.natCast_eq_zero_iff (r^2 + 1) p).mpr hdvd
    · rintro ⟨hlt, hroot⟩
      refine ⟨hlt, (ZMod.natCast_eq_zero_iff (r^2 + 1) p).mp (key r ▸ ?_)⟩
      exact neg_eq_iff_add_eq_zero.mp (neg_eq_iff_eq_neg.mpr hroot)
  -- Going back from a root in the field to divisibility of the standard representative.
  have hdvd : ∀ r : ℕ, r < p → (r : ZMod p)^2 = -1 → p ∣ r^2 + 1 := by
    intro r hr hroot
    have h0 : ((r^2 + 1 : ℕ) : ZMod p) = 0 := by
      rw [key]
      exact neg_eq_iff_add_eq_zero.mp (neg_eq_iff_eq_neg.mpr hroot)
    exact (ZMod.natCast_eq_zero_iff (r^2 + 1) p).mp h0
  rcases hp.eq_two_or_odd with rfl | hodd
  · -- The even prime: the only root below two is one.
    have hset : (Finset.filter (fun r => 2 ∣ r^2 + 1) (Finset.range 2) : Finset ℕ) = {1} := by
      decide
    rw [hroots, hset, Finset.card_singleton]
    exact by decide
  · haveI hnz : NeZero p := ⟨Nat.Prime.ne_zero hp⟩
    have hpos : p ≠ 2 := by omega
    have hfour : p % 4 = 1 ∨ p % 4 = 3 := by omega
    by_cases h1 : p % 4 = 1
    · -- Minus one is a square: pick a root and list its two representatives.
      obtain ⟨x, hx⟩ : ∃ y : ZMod p, y^2 = -1 := by
        obtain ⟨y, hy⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr (by omega : p % 4 ≠ 3)
        exact ⟨y, by rw [pow_two]; exact hy.symm⟩
      have hval : x.val < p := ZMod.val_lt x
      have hcoe : (x.val : ZMod p) = x := @ZMod.natCast_zmod_val p hnz x
      have hsqv : (x.val : ZMod p)^2 = -1 := by rw [hcoe]; exact hx
      have had : p ∣ x.val^2 + 1 := hdvd x.val hval hsqv
      have hxv : 0 < x.val := by
        by_contra hz
        have hz2 : x.val = 0 := Nat.eq_zero_of_not_pos hz
        have hd : p ∣ 1 := by simpa [hz2] using had
        have : p ≤ 1 := Nat.le_of_dvd (by omega : (0 : ℕ) < 1) hd
        omega
      have hsub : p - x.val < p := by omega
      -- The negation of a root is the representative obtained by subtracting from the prime.
      have hpx : ((p - x.val : ℕ) : ZMod p) = -x := by
        rw [Nat.cast_sub (Nat.le_of_lt hval), ZMod.natCast_self, zero_sub, hcoe]
      have hmain : roots 1 p = {x.val, p - x.val} := by
        apply Finset.ext
        intro r
        have hiff : r ∈ ({x.val, p - x.val} : Finset ℕ) ↔ r = x.val ∨ r = p - x.val := by simp
        rw [hmem, hiff]
        constructor
        · rintro ⟨hr, hroot⟩
          have h2 : (r : ZMod p)^2 = x^2 := by rw [hx]; exact hroot
          have h3 : (r : ZMod p) = x ∨ (r : ZMod p) = -x := sq_eq_sq_iff_eq_or_eq_neg.mp h2
          rcases h3 with h | h
          · exact Or.inl (by
              have hc : ZMod.val (r : ZMod p) = ZMod.val x := congrArg ZMod.val h
              rwa [ZMod.val_natCast_of_lt hr] at hc)
          · exact Or.inr (by
              have hn : (r : ZMod p) = ((p - x.val : ℕ) : ZMod p) := by rw [hpx, h]
              have hc : ZMod.val (r : ZMod p) = ZMod.val ((p - x.val : ℕ) : ZMod p) :=
                congrArg ZMod.val hn
              rwa [ZMod.val_natCast_of_lt hr, ZMod.val_natCast_of_lt hsub] at hc)
        · rintro (h | h)
          · subst h
            exact ⟨hval, hsqv⟩
          · subst h
            refine ⟨hsub, ?_⟩
            rw [hpx, neg_sq, ← hcoe]
            exact hsqv
      have hne : x.val ≠ p - x.val := by omega
      rw [if_neg hpos, if_pos h1]
      exact Finset.card_eq_two.mpr ⟨x.val, p - x.val, hne, hmain⟩
    · -- Minus one is not a square: the filtered range is empty.
      have h3 : p % 4 = 3 := by
        rcases hfour with h | h
        · exact absurd h h1
        · exact h
      have hempty : roots 1 p = ∅ := by
        apply Finset.ext
        intro r
        rw [hmem]
        constructor
        · rintro ⟨_, hroot⟩
          exact absurd h3 (ZMod.mod_four_ne_three_of_sq_eq_neg_one hroot)
        · exact fun h => absurd h (by simp)
      rw [if_neg hpos, if_neg h1, hempty, Finset.card_empty]
