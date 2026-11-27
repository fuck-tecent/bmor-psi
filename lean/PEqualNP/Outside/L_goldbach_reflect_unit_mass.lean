import Mathlib

open Finset

namespace PEqualNP.Outside

theorem L_goldbach_reflect_unit_mass :
    let w := fun k : ℕ => if k.Prime then Real.log (k : ℝ) else 0; ∀ n : ℕ, 4 ≤ n → Even n → (∑ k ∈ Finset.range (n+1), w k*w (n-k)) = (∑ k ∈ (Finset.range (n+1)).filter (fun k => Nat.Coprime k n), w k*w (n-k)) + (w (n/2))^2 := by
  intro w n hn heven
  classical
  obtain ⟨m, rfl⟩ := heven
  have hsplit :=
    (Finset.sum_filter_add_sum_filter_not (s := Finset.range (m + m + 1))
      (p := fun k => Nat.Coprime k (m + m)) (f := fun k => w k * w (m + m - k))).symm
  rw [hsplit]
  congr 1
  have hmem : (m + m) / 2 ∈ (Finset.range (m + m + 1)).filter (fun k => ¬ Nat.Coprime k (m + m)) := by
    refine mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩
    intro hcop
    have hdvd : (m + m) / 2 ∣ Nat.gcd ((m + m) / 2) (m + m) :=
      Nat.dvd_gcd (dvd_refl _) ⟨2, by omega⟩
    rw [hcop.gcd_eq_one] at hdvd
    have hle : (m + m) / 2 ≤ 1 := Nat.le_of_dvd zero_lt_one hdvd
    omega
  have hsingle :
      (∑ k ∈ (Finset.range (m + m + 1)).filter (fun k => ¬ Nat.Coprime k (m + m)), w k * w (m + m - k)) =
        w ((m + m) / 2) * w (m + m - (m + m) / 2) := by
    refine Finset.sum_eq_single ((m + m) / 2) ?_ ?_
    · intro k hk hkne
      have hk_range : k < m + m + 1 := mem_range.mp (mem_filter.mp hk).1
      have hnotcop : ¬ Nat.Coprime k (m + m) := (mem_filter.mp hk).2
      by_cases hp : k.Prime
      · by_cases hq : (m + m - k).Prime
        · exfalso
          have hdvd_n : k ∣ m + m := by
            by_contra hndvd
            exact hnotcop (hp.coprime_iff_not_dvd.mpr hndvd)
          have hdvd_sub : k ∣ m + m - k := Nat.dvd_sub hdvd_n (dvd_refl k)
          rcases hq.eq_one_or_self_of_dvd k hdvd_sub with hk1 | hkeq
          · exact hp.ne_one hk1
          · omega
        · simp [w, hq]
      · simp [w, hp]
    · intro hnotmem
      exact (hnotmem hmem).elim
  rw [hsingle]
  have hsub : m + m - (m + m) / 2 = (m + m) / 2 := by omega
  rw [hsub, sq]

end PEqualNP.Outside
