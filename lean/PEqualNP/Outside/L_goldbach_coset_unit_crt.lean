import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Prod

namespace GoldbachReflectedUnits

-- Reduction along a divisor commutes with the reflection when the residue
-- lies in range. The bounds ensure both natural subtractions are exact.
private theorem reflectedCoprime {d m n r : ℕ}
    (hd : 0 < d) (hdm : d ∣ m) (hr : r < m) :
    ((n + m - r) % m).Coprime d ↔ ((n + d - r % d) % d).Coprime d := by
  have hr' := Nat.mod_lt r hd
  have hsum : n + m ≡ n + d [MOD d] :=
    Nat.ModEq.rfl.add (hdm.modEq_zero_nat.trans Nat.modulus_modEq_zero.symm)
  have hdiff : n + m - r ≡ n + d - r % d [MOD d] :=
    Nat.ModEq.sub (by omega) (by omega) hsum (Nat.mod_modEq r d).symm
  have h := ((Nat.mod_modEq (n + m - r) m).of_dvd hdm).trans
    (hdiff.trans (Nat.mod_modEq _ d).symm)
  simp only [Nat.coprime_iff_gcd_eq_one, h.gcd_eq]

private theorem coprimeResidue (r d : ℕ) : r.Coprime d ↔ (r % d).Coprime d := by
  simp only [Nat.coprime_iff_gcd_eq_one, (Nat.mod_modEq r d).gcd_eq]

-- Restrict the Chinese remainder bijection to any family of residue sets
-- whose membership condition holds exactly when it holds in both factors.
private theorem crtFilterCard (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (S : ℕ → Finset ℕ) (bound : ∀ q r, r ∈ S q → r < q)
    (splitMem : ∀ r, r < a * b → (r ∈ S (a * b) ↔ r % a ∈ S a ∧ r % b ∈ S b)) :
    (S (a * b)).card = (S a).card * (S b).card := by
  rw [← Finset.card_product]
  apply Finset.card_bij (fun r _ => (r % a, r % b))
  · intro r hr
    exact Finset.mem_product.mpr ((splitMem r (bound _ _ hr)).mp hr)
  · intro x hx y hy hxy
    have hA : x ≡ y [MOD a] := congrArg Prod.fst hxy
    have hB : x ≡ y [MOD b] := congrArg Prod.snd hxy
    exact ((Nat.modEq_and_modEq_iff_modEq_mul hab).mp ⟨hA, hB⟩).eq_of_lt_of_lt
      (bound _ _ hx) (bound _ _ hy)
  · rintro ⟨i, j⟩ hij
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
    let k := Nat.chineseRemainder hab i j
    have hk : k.val < a * b := Nat.chineseRemainder_lt_mul hab i j ha.ne' hb.ne'
    have hki : k.val % a = i := Eq.trans k.property.1 (Nat.mod_eq_of_lt (bound _ _ hi))
    have hkj : k.val % b = j := Eq.trans k.property.2 (Nat.mod_eq_of_lt (bound _ _ hj))
    refine ⟨k.val, (splitMem _ hk).mpr ?_, Prod.ext hki hkj⟩
    simpa only [hki, hkj] using And.intro hi hj

end GoldbachReflectedUnits

open GoldbachReflectedUnits

theorem PEqualNP.Outside.L_goldbach_coset_unit_crt :
    let R := fun n q : ℕ => ((Finset.range q).filter (fun r => r.Coprime q ∧ ((n+q-r)%q).Coprime q)).card; ∀ n a b : ℕ, 0<a → 0<b → a.Coprime b → R n (a*b)=R n a*R n b := by
  dsimp only
  intro n a b ha hb hab
  let S (q : ℕ) := (Finset.range q).filter (fun r => r.Coprime q ∧ ((n + q - r) % q).Coprime q)
  apply crtFilterCard a b ha hb hab S
  · intro q r hr
    exact Finset.mem_range.mp (Finset.mem_filter.mp hr).1
  · intro r hr
    simp only [S, Finset.mem_filter, Finset.mem_range, hr, Nat.mod_lt _ ha, Nat.mod_lt _ hb,
      true_and, Nat.coprime_mul_iff_right]
    rw [coprimeResidue r a, coprimeResidue r b,
      reflectedCoprime ha (dvd_mul_right a b) hr, reflectedCoprime hb (dvd_mul_left b a) hr]
    exact and_and_and_comm
