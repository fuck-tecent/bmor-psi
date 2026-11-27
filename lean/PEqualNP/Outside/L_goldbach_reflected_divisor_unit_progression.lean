import Mathlib

theorem PEqualNP.Outside.L_goldbach_reflected_divisor_unit_progression :
    ∀ n p d : ℕ, p < n → Nat.Coprime p n → d ∣ n-p → Nat.Coprime n d ∧ p % d = n % d := by
  intro n p d hpn hcop hd
  have hmod : p % d = n % d := by
    have heq : n = p + (n - p) := (Nat.add_sub_of_le hpn.le).symm
    rw [heq, Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, add_zero, Nat.mod_mod]
  have hcop_sub : Nat.Coprime n (n - p) :=
    (Nat.coprime_self_sub_right hpn.le).mpr hcop.symm
  exact ⟨hcop_sub.coprime_dvd_right hd, hmod⟩
