import Mathlib
theorem Conjectures.Goldbach.FareyTerminalSurvivors : ∀ (n : ℕ) (J : Finset ℕ), 64 ≤ n → let I := (Finset.Icc ((n+2)/3) ((2*n)/3)).filter (fun u => u.Coprime n ∧ (J.filter (fun a => (a*u) % n = 1)).Nonempty); I.filter (fun u => Nat.sqrt n < (u*(n-u)).minFac) = I.filter (fun u => u.Prime ∧ (n-u).Prime) := by
  intro n J hn
  dsimp only
  have hgeneral : ∀ a b : ℕ, 2 ≤ a → 2 ≤ b → a ≤ n → b ≤ n → n.sqrt < a → n.sqrt < b → (n.sqrt < (a*b).minFac ↔ a.Prime ∧ b.Prime) := by
    intro a b ha hb han hbn hsa hsb
    constructor
    · intro hmin
      constructor
      · by_contra hnp
        have hsq := Nat.minFac_sq_le_self (show 0<a by omega) hnp
        have hmin_a : a.minFac ≤ n.sqrt := Nat.le_sqrt.mpr (by nlinarith)
        have hprod : (a*b).minFac ≤ a.minFac := Nat.minFac_le_of_dvd (Nat.minFac_prime (by omega : a ≠ 1)).two_le (dvd_trans (Nat.minFac_dvd a) (dvd_mul_right a b))
        omega
      · by_contra hnp
        have hsq := Nat.minFac_sq_le_self (show 0<b by omega) hnp
        have hmin_b : b.minFac ≤ n.sqrt := Nat.le_sqrt.mpr (by nlinarith)
        have hprod : (a*b).minFac ≤ b.minFac := Nat.minFac_le_of_dvd (Nat.minFac_prime (by omega : b ≠ 1)).two_le (dvd_trans (Nat.minFac_dvd b) (dvd_mul_left b a))
        omega
    · rintro ⟨hpa,hpb⟩
      have hp : (a*b).minFac.Prime := Nat.minFac_prime (by nlinarith)
      have hd := hp.dvd_mul.mp (Nat.minFac_dvd (a*b))
      rcases hd with h | h
      · have heq := (Nat.prime_dvd_prime_iff_eq hp hpa).mp h
        omega
      · have heq := (Nat.prime_dvd_prime_iff_eq hp hpb).mp h
        omega
  ext u
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor <;> intro h
  all_goals
    have hu_lo : (n+2)/3 ≤ u := h.1.1.1
    have hu_hi : u ≤ (2*n)/3 := h.1.1.2
    have hu_le : u ≤ n := by omega
    have hba : 2 ≤ u := by omega
    have hbb : 2 ≤ n-u := by omega
    have hsq := Nat.sqrt_le n
    have hsa : n.sqrt < u := by
      have hlin : n ≤ 3*u+2 := by omega
      nlinarith
    have hsb : n.sqrt < n-u := by
      have hlin : n ≤ 3*(n-u)+2 := by omega
      nlinarith
  · exact ⟨h.1, (hgeneral u (n-u) hba hbb hu_le (Nat.sub_le _ _) hsa hsb).mp h.2⟩
  · exact ⟨h.1, (hgeneral u (n-u) hba hbb hu_le (Nat.sub_le _ _) hsa hsb).mpr h.2⟩

