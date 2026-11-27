import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_fixed_a_root_pair :
    let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a); ∀ (p a : ℕ) [Fact p.Prime], p≠2 → ((roots a p).card : ℤ) = 1 + legendreSym p (-(a : ℤ)) := by
  dsimp only
  intro p a _ hp
  have hcard : ((Finset.range p).filter (fun r => p ∣ r^2+a)).card
      = (Finset.univ.filter (fun x : ZMod p => x^2 = -(a : ZMod p))).card := by
    apply Finset.card_bij (fun (r : ℕ) (_ : r ∈ (Finset.range p).filter (fun r => p ∣ r^2+a)) => (r : ZMod p))
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_range] at hr
      obtain ⟨hrlt, hrdiv⟩ := hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h2 : ((r^2 + a : ℕ) : ZMod p) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]; exact hrdiv
      push_cast at h2
      linear_combination h2
    · intro r1 hr1 r2 hr2 heq
      simp only [Finset.mem_filter, Finset.mem_range] at hr1 hr2
      have h := ZMod.natCast_eq_natCast_iff' r1 r2 p
      rw [h] at heq
      rw [Nat.mod_eq_of_lt hr1.1, Nat.mod_eq_of_lt hr2.1] at heq
      exact heq
    · intro x hx
      refine ⟨x.val, ?_, by rw [ZMod.natCast_zmod_val]⟩
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hx ⊢
      refine ⟨ZMod.val_lt x, ?_⟩
      have h2 : ((x.val^2 + a : ℕ) : ZMod p) = 0 := by
        push_cast
        rw [ZMod.natCast_zmod_val, hx]
        ring
      exact (ZMod.natCast_eq_zero_iff _ _).mp h2
  have h2 : (Finset.univ.filter (fun x : ZMod p => x^2 = -(a : ZMod p))).card
      = ({x : ZMod p | x^2 = (-(a:ℤ) : ZMod p)}).toFinset.card := by
    rw [show ({x : ZMod p | x^2 = (-(a:ℤ) : ZMod p)}).toFinset
          = Finset.univ.filter (fun x : ZMod p => x^2 = (-(a:ℤ) : ZMod p)) from by ext x; simp]
    rw [show ((-(a:ℤ) : ZMod p)) = -(a : ZMod p) from by push_cast; ring]
  rw [hcard, h2]
  have hcs := legendreSym.card_sqrts p hp (-(a:ℤ))
  simp only [Int.cast_neg, Int.cast_natCast] at hcs ⊢
  rw [hcs]; ring
