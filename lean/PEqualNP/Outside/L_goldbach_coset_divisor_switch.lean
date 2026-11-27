import Mathlib

theorem PEqualNP.Outside.L_goldbach_coset_divisor_switch :
    ∀ d Q : ℕ, 0<d → (∑ q ∈ (Finset.Ioc Q (2*Q)).filter (fun q => q∣d), (q:ℝ)) = (d:ℝ)* ∑ h ∈ d.divisors.filter (fun h => Q*h<d ∧ d≤2*Q*h), 1/(h:ℝ) := by
  intro d Q hd
  let weight (q : ℕ) : ℝ := if Q < q ∧ q ≤ 2*Q then q else 0
  have hblock : (Finset.Ioc Q (2*Q)).filter (fun q => q ∣ d) =
      d.divisors.filter (fun q => Q < q ∧ q ≤ 2*Q) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors]
    exact ⟨fun ⟨hI, hq⟩ => ⟨⟨hq, Nat.ne_of_gt hd⟩, hI⟩,
      fun ⟨⟨hq, _⟩, hI⟩ => ⟨hI, hq⟩⟩
  rw [hblock]
  calc
    _ = ∑ q ∈ d.divisors, weight q := by rw [Finset.sum_filter]
    _ = ∑ h ∈ d.divisors, weight (d/h) := (Nat.sum_div_divisors d weight).symm
    _ = _ := by
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      have hpos := Nat.pos_of_mem_divisors hh
      have hprod := Nat.div_mul_cancel (Nat.mem_divisors.mp hh).1
      have hswitch : (Q < d / h ∧ d / h ≤ 2*Q) ↔ (Q*h < d ∧ d ≤ 2*Q*h) := by
        rw [← hprod, Nat.mul_div_cancel _ hpos, mul_lt_mul_iff_of_pos_right hpos,
          mul_le_mul_iff_of_pos_right hpos]
      dsimp only [weight]
      by_cases hI : Q*h < d ∧ d ≤ 2*Q*h
      · rw [ite_eq_left (hswitch.mpr hI), ite_eq_left hI, mul_one_div,
          eq_div_iff (by exact_mod_cast hpos.ne')]
        exact_mod_cast hprod
      · simp [hI, mt hswitch.mp hI]
