import Mathlib

theorem PEqualNP.Outside.L_goldbach_unit_power_lift :
    let U := fun q n : ℕ => (Finset.range q).filter (fun a => Nat.Coprime a q ∧ Nat.Coprime (n+q-a) q); ∀ p k n, Nat.Prime p → (U (p^(k+1)) n).card=p^k*(U p n).card := by
  dsimp only
  intro p k n hp
  let F (q a : ℕ) : ℕ := if Nat.Coprime a q ∧ Nat.Coprime (n+q-a) q then 1 else 0
  simp only [Finset.card_filter]
  change (∑ a ∈ Finset.range (p^(k+1)), F (p^(k+1)) a) =
    p^k * ∑ a ∈ Finset.range p, F p a
  have block (t r : ℕ) (ht : t < p^k) (hr : r < p) :
      F (p^(k+1)) (t*p+r) = F p r := by
    have hbound : t*p+r ≤ n+p^(k+1) := by
      have h := Nat.mul_le_mul_right p (Nat.succ_le_of_lt ht)
      rw [Nat.succ_mul] at h
      rw [pow_succ]
      omega
    have ha : Nat.ModEq p (t*p+r) r := by simp [Nat.ModEq, Nat.add_mod]
    have hn : Nat.ModEq p (n+p^(k+1)) (n+p) := by
      simp [Nat.ModEq, pow_succ, Nat.add_mod]
    have hb := Nat.ModEq.sub hbound (show r ≤ n+p by omega) hn ha
    simp only [F, Nat.coprime_pow_right_iff (Nat.succ_pos k), Nat.Coprime,
      ha.gcd_eq, hb.gcd_eq]
  have blocks (m : ℕ) (hm : m ≤ p^k) :
      (∑ a ∈ Finset.range (m*p), F (p^(k+1)) a) =
        m * ∑ a ∈ Finset.range p, F p a := by
    induction m with
    | zero => simp
    | succ t ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih (by omega), Nat.succ_mul]
      apply congrArg (fun x : ℕ => (t * ∑ a ∈ Finset.range p, F p a) + x)
      apply Finset.sum_congr rfl
      intro r hr
      exact block t r (by omega) (Finset.mem_range.mp hr)
  simpa only [← pow_succ] using blocks (p^k) (le_refl _)
