import Mathlib

namespace Conjectures.Cuts.Taske501a766669a89fff4ee44e7_aux

/-- Stripping the forced factor of three from the shifted progression. -/
lemma strip_three (c x8 : ℕ) (hc : c = 1 ∨ c = 5 ∨ c = 11 ∨ c = 13 ∨ c = 17) :
    (18 * x8 + c + 2) / (if (3 : ℕ) ∣ 18 * x8 + c + 2 then (3 : ℕ) else (1 : ℕ)) =
      (if c % (3 : ℕ) = (1 : ℕ) then (6 : ℕ) else (18 : ℕ)) * x8 +
        (if c % (3 : ℕ) = (1 : ℕ) then (c + (2 : ℕ)) / (3 : ℕ) else c + (2 : ℕ)) := by
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · have hd : (3 : ℕ) ∣ 18 * x8 + 1 + 2 := ⟨6 * x8 + 1, by ring⟩
    simp only [hd, ↓reduceIte]
    norm_num
    omega
  · have hd : ¬ (3 : ℕ) ∣ 18 * x8 + 5 + 2 := by omega
    simp only [hd, ↓reduceIte]
    norm_num
  · have hd : ¬ (3 : ℕ) ∣ 18 * x8 + 11 + 2 := by omega
    simp only [hd, ↓reduceIte]
    norm_num
  · have hd : (3 : ℕ) ∣ 18 * x8 + 13 + 2 := ⟨6 * x8 + 5, by ring⟩
    simp only [hd, ↓reduceIte]
    norm_num
    omega
  · have hd : ¬ (3 : ℕ) ∣ 18 * x8 + 17 + 2 := by omega
    simp only [hd, ↓reduceIte]
    norm_num

/-- Nine never divides the shifted progression on the admissible residues. -/
lemma nine_not_dvd (c x8 : ℕ) (hc : c = 1 ∨ c = 5 ∨ c = 11 ∨ c = 13 ∨ c = 17) :
    ¬ (9 : ℕ) ∣ 18 * x8 + c + 2 := by
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> omega

end Conjectures.Cuts.Taske501a766669a89fff4ee44e7_aux

theorem Conjectures.Cuts.Taske501a766669a89fff4ee44e7 :
    have x1 : Finset ℕ := {(1 : ℕ), (5 : ℕ), (11 : ℕ), (13 : ℕ), (17 : ℕ)}; have x2 : ℕ → ℕ := fun (x2 : ℕ) => if x2 % (3 : ℕ) = (1 : ℕ) then (6 : ℕ) else (18 : ℕ); have x3 : ℕ → ℕ := fun (x3 : ℕ) => if x3 % (3 : ℕ) = (1 : ℕ) then (x3 + (2 : ℕ)) / (3 : ℕ) else x3 + (2 : ℕ); have x4 : ℕ → Prop := fun (x4 : ℕ) => (3 : ℕ) < x4 ∧ Nat.Prime x4 ∧ ¬(9 : ℕ) ∣ x4 + (2 : ℕ) ∧ ((x4 + (2 : ℕ)) / if (3 : ℕ) ∣ x4 + (2 : ℕ) then (3 : ℕ) else (1 : ℕ)).primeFactorsList.length ≤ (2 : ℕ); have x5 : ℕ → ℕ → Prop := fun (x5 x6 : ℕ) => (3 : ℕ) < (18 : ℕ) * x6 + x5 ∧ Nat.Prime ((18 : ℕ) * x6 + x5) ∧ (x2 x5 * x6 + x3 x5).primeFactorsList.length ≤ (2 : ℕ); ∀ x6 ∈ x1, ∀ (x8 : ℕ), x4 ((18 : ℕ) * x8 + x6) ↔ x5 x6 x8 := by
  intro x1 x2 x3 x4 x5 x6 hx6 x8
  have hc : x6 = 1 ∨ x6 = 5 ∨ x6 = 11 ∨ x6 = 13 ∨ x6 = 17 := by
    have hx6' : x6 ∈ ({(1 : ℕ), (5 : ℕ), (11 : ℕ), (13 : ℕ), (17 : ℕ)} : Finset ℕ) := hx6
    simpa using hx6'
  have hQ := Conjectures.Cuts.Taske501a766669a89fff4ee44e7_aux.strip_three x6 x8 hc
  have h9 := Conjectures.Cuts.Taske501a766669a89fff4ee44e7_aux.nine_not_dvd x6 x8 hc
  dsimp only [x4, x5, x2, x3]
  rw [hQ]
  constructor
  · rintro ⟨h1, h2, _, h4⟩
    exact ⟨h1, h2, h4⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, h9, h3⟩
