import Mathlib

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.L_goldbach_finite_rough_candidate_lift :
    ∀ n : ℕ, 22 ≤ n → Even n → ∃ p : ℕ, Nat.Prime p ∧ p < n ∧ 2 ≤ n-p ∧ Nat.Coprime (n-p) 210 := by
  intro n hn he
  have cover : ∀ a : Fin 210, a.val % 2 = 0 → ∃ p : Fin 20,
      Nat.Prime p.val ∧ Nat.Coprime ((a.val + 210 - p.val) % 210) 210 := by
    decide +kernel
  obtain ⟨k, hk⟩ := he
  obtain ⟨p, hp, hc⟩ := cover ⟨n % 210, Nat.mod_lt _ (by decide)⟩ (by
    change n % 210 % 2 = 0
    omega)
  have hp_lt := p.isLt
  refine ⟨p.val, hp, by omega, by omega, ?_⟩
  change Nat.gcd ((n % 210 + 210 - p.val) % 210) 210 = 1 at hc
  change Nat.gcd (n - p.val) 210 = 1
  rw [Nat.gcd_comm, Nat.gcd_rec 210 (n - p.val)]
  rwa [show (n - p.val) % 210 = (n % 210 + 210 - p.val) % 210 by omega]
