import Mathlib
open scoped BigOperators

noncomputable section
namespace B1B1

/-- The divisors of `q` that divide `a` are exactly the divisors of `gcd a q`. -/
lemma divisors_filter_dvd_eq_gcd (a q : ℕ) (hq : 0 < q) :
    q.divisors.filter (fun d => d ∣ a) = (Nat.gcd a q).divisors := by
  ext d
  rw [Finset.mem_filter, Nat.mem_divisors, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdq, _hqne⟩, hda⟩
    exact ⟨Nat.dvd_gcd hda hdq, (Nat.gcd_pos_of_pos_right a hq).ne'⟩
  · rintro ⟨hdg, _⟩
    exact ⟨⟨hdg.trans (Nat.gcd_dvd_right a q), by omega⟩,
      hdg.trans (Nat.gcd_dvd_left a q)⟩

end B1B1
