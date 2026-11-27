import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside

theorem L_goldbach_unit_sieve_density :
    let U := fun q n : ℕ => (Finset.range q).filter (fun a => Nat.Coprime a q ∧ Nat.Coprime (n+q-a) q); ∀ q n T, 0<q → ((Finset.range (q*T)).filter (fun a => HMod.hMod a q ∈ U q n)).card=T*(U q n).card := by
  dsimp only
  intro q n T hq
  classical
  let U : ℕ → ℕ → Finset ℕ := fun q n =>
    (Finset.range q).filter (fun a => Nat.Coprime a q ∧ Nat.Coprime (n + q - a) q)
  let p : ℕ → Prop := fun a => HMod.hMod a q ∈ U q n
  change ((Finset.range (q * T)).filter p).card = T * (U q n).card
  have hfilter : (Finset.range q).filter p = U q n := by
    ext a
    by_cases ha : a < q
    · simp only [p, Finset.mem_filter, Finset.mem_range]
      rw [Nat.mod_eq_of_lt ha]
      simp [U, ha]
    · simp [p, U, ha]
  have hp : Function.Periodic p q := by
    intro a
    apply eq_iff_iff.mpr
    change HMod.hMod (a + q) q ∈ U q n ↔ HMod.hMod a q ∈ U q n
    rw [Nat.add_mod_right]
  have hmain : ∀ T : ℕ, ((Finset.range (q * T)).filter p).card =
      T * (U q n).card := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
        have hnext : q * (T + 1) = q * T + q := by ring
        have hsplit : Finset.range (q * (T + 1)) =
            Finset.range (q * T) ∪ Finset.Ico (q * T) (q * (T + 1)) := by
          rw [hnext]
          ext a
          simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
          omega
        have hdisj : Disjoint (Finset.range (q * T))
            (Finset.Ico (q * T) (q * (T + 1))) := by
          rw [hnext, Finset.disjoint_left]
          intro a ha hb
          simp only [Finset.mem_range, Finset.mem_Ico] at ha hb
          omega
        have hdisj' : Disjoint ((Finset.range (q * T)).filter p)
            ((Finset.Ico (q * T) (q * (T + 1))).filter p) :=
          hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
        rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint hdisj', ih]
        have hblock : ((Finset.Ico (q * T) (q * (T + 1))).filter p).card =
            (U q n).card := by
          have hlen : q * (T + 1) = q * T + q := by ring
          rw [hlen]
          rw [Nat.filter_Ico_card_eq_of_periodic (q * T) q p hp]
          simpa only [hfilter] using Nat.count_eq_card_filter_range (p := p) q
        rw [hblock]
        ring
  exact hmain T

end PEqualNP.Outside
