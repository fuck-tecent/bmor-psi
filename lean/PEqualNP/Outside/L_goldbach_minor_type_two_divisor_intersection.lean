import Mathlib

theorem PEqualNP.Outside.L_goldbach_minor_type_two_divisor_intersection :
    ∀ (d e Y : ℕ), 0 < d → 0 < e → ((Finset.Icc 1 Y).filter (fun r => d ∣ r ∧ e ∣ r)).card = Y / (Nat.lcm d e) := by
  intro d e Y _ _
  rw [← Nat.card_multiples' Y (Nat.lcm d e)]
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range, Nat.lcm_dvd_iff]
  omega
