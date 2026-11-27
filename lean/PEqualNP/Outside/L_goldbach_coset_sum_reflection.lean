import Mathlib

theorem PEqualNP.Outside.L_goldbach_coset_sum_reflection :
    let F := fun n q r : ℕ => (Finset.range (n + 1)).filter (fun k => k % q = r);
    let j := fun n q r : ℕ => (n + q - r) % q;
    ∀ n q r : ℕ, 0 < q → r < q → (F n q r).card = (F n q (j n q r)).card := by
  dsimp only
  intro n q r _hq hr
  have base : n ≡ n + q [MOD q] := (Nat.add_mod_right n q).symm
  have reflect (k : ℕ) (hk : k ≤ n) :
      k % q = r ↔ (n - k) % q = (n + q - r) % q := by
    constructor
    · intro h
      have hc : k ≡ r [MOD q] := by
        simpa only [Nat.ModEq, Nat.mod_eq_of_lt hr] using h
      have hs : k + (n - k) ≡ r + (n + q - r) [MOD q] := by
        simpa only [show k + (n - k) = n by omega,
          show r + (n + q - r) = n + q by omega] using base
      exact Nat.ModEq.add_left_cancel hc hs
    · intro h
      have hc : n - k ≡ n + q - r [MOD q] := h
      have hs : (n - k) + k ≡ (n + q - r) + r [MOD q] := by
        simpa only [show (n - k) + k = n by omega,
          show (n + q - r) + r = n + q by omega] using base
      have hh : k ≡ r [MOD q] := Nat.ModEq.add_left_cancel hc hs
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt hr] using hh
  refine Finset.card_bij (fun k _ => n - k) ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    exact ⟨by omega, (reflect k (by omega)).mp hk.2⟩
  · intro a ha b hb he
    simp only [Finset.mem_filter, Finset.mem_range] at ha hb
    change n - a = n - b at he
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    have hrev : n - (n - k) = k := by omega
    refine ⟨n - k, ?_, hrev⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, (reflect (n - k) (by omega)).mpr ?_⟩
    simpa only [hrev] using hk.2
