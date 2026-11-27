import Mathlib

namespace Conjectures.Goldbach.ReflectionConductorBlocks_aux

lemma isUnit_iff_not_dvd_val {p k : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hk : 0 < k)
    (a : ZMod (p ^ k)) :
    IsUnit a ↔ ¬ p ∣ a.val := by
  have h : IsUnit a ↔ IsUnit ((a.val : ℕ) : ZMod (p ^ k)) := by rw [ZMod.natCast_zmod_val]
  rw [h, ZMod.isUnit_natCast_iff_not_dvd_pow hp hk]

lemma isUnit_cast_iff {p k j : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hk : 0 < k) (hj : 0 < j)
    (a : ZMod (p ^ k)) :
    IsUnit (ZMod.cast a : ZMod (p ^ j)) ↔ IsUnit a := by
  have h1 : (ZMod.cast a : ZMod (p ^ j)) = ((a.val : ℕ) : ZMod (p ^ j)) :=
    (ZMod.natCast_val a).symm
  rw [h1, ZMod.isUnit_natCast_iff_not_dvd_pow hp hj]
  exact (isUnit_iff_not_dvd_val hp hk a).symm

lemma changeLevel_apply {p k j : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hk : 0 < k) (hj : 0 < j)
    (hm : p ^ j ∣ p ^ k) (ψ₀ : DirichletCharacter ℂ (p ^ j)) (a : ZMod (p ^ k)) :
    DirichletCharacter.changeLevel hm ψ₀ a = ψ₀ (ZMod.cast a) := by
  by_cases ha : IsUnit a
  · have h := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ₀ hm ha.unit
    rwa [IsUnit.unit_spec] at h
  · rw [MulChar.map_nonunit _ ha,
      MulChar.map_nonunit _ ((isUnit_cast_iff hp hk hj a).not.mpr ha)]

lemma sum_units_eq_sum {n : ℕ} [NeZero n] (f : ZMod n → ℂ)
    (hf : ∀ a : ZMod n, ¬IsUnit a → f a = 0) :
    ∑ x : (ZMod n)ˣ, f (x : ZMod n) = ∑ a : ZMod n, f a := by
  classical
  have h1 : ∑ x : (ZMod n)ˣ, f (x : ZMod n)
      = ∑ a ∈ (Finset.univ : Finset (ZMod n)).filter IsUnit, f a := by
    refine Finset.sum_bij (fun x _ => (x : ZMod n))
      (fun x _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.isUnit⟩)
      (fun x y _ _ h => Units.ext h) ?_ (fun x _ => rfl)
    intro b hb
    exact ⟨((Finset.mem_filter.mp hb).2 : IsUnit b).unit, Finset.mem_univ _,
      ((Finset.mem_filter.mp hb).2 : IsUnit b).unit_spec⟩
  rw [h1]
  refine (Finset.sum_subset_zero_on_sdiff (Finset.filter_subset _ _) ?_ (fun x _ => rfl)).trans ?_
  · intro a ha
    refine hf a (fun hau => ?_)
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hau⟩)
  · rfl

lemma reflection_swap {n : ℕ} [NeZero n] (N : ZMod n) (χ ψ : DirichletCharacter ℂ n) :
    (∑ x : (ZMod n)ˣ, star (χ (x : ZMod n)) * ψ (N - (x : ZMod n)))
      = star (∑ x : (ZMod n)ˣ, star (ψ (x : ZMod n)) * χ (N - (x : ZMod n))) := by
  classical
  have e1 : ∀ a : ZMod n, ¬IsUnit a → star (χ a) * ψ (N - a) = 0 := by
    intro a ha
    rw [MulChar.map_nonunit χ ha, star_zero, zero_mul]
  have e2 : ∀ a : ZMod n, ¬IsUnit a → ψ a * star (χ (N - a)) = 0 := by
    intro a ha
    rw [MulChar.map_nonunit ψ ha, zero_mul]
  have hbij : Function.Bijective (fun b : ZMod n => N - b) := by
    constructor
    · intro b₁ b₂ h
      have h2 := congrArg (fun z : ZMod n => N - z) h
      simpa only [sub_sub_cancel] using h2
    · intro b
      exact ⟨N - b, sub_sub_cancel N b⟩
  have hsub : (∑ b : ZMod n, star (χ (N - b)) * ψ b)
      = ∑ a : ZMod n, star (χ a) * ψ (N - a) :=
    Fintype.sum_bijective (fun b : ZMod n => N - b) hbij
      (fun b : ZMod n => star (χ (N - b)) * ψ b) (fun a : ZMod n => star (χ a) * ψ (N - a))
      (fun b => by rw [sub_sub_cancel])
  have hL : (∑ x : (ZMod n)ˣ, star (χ (x : ZMod n)) * ψ (N - (x : ZMod n)))
      = ∑ a : ZMod n, star (χ a) * ψ (N - a) :=
    sum_units_eq_sum (fun a : ZMod n => star (χ a) * ψ (N - a)) e1
  have hR : star (∑ x : (ZMod n)ˣ, star (ψ (x : ZMod n)) * χ (N - (x : ZMod n)))
      = ∑ a : ZMod n, ψ a * star (χ (N - a)) := by
    have h1 : star (∑ x : (ZMod n)ˣ, star (ψ (x : ZMod n)) * χ (N - (x : ZMod n)))
        = ∑ x : (ZMod n)ˣ, star (star (ψ (x : ZMod n)) * χ (N - (x : ZMod n))) :=
      star_sum Finset.univ _
    rw [h1]
    have h2 : ∀ x : (ZMod n)ˣ, star (star (ψ (x : ZMod n)) * χ (N - (x : ZMod n)))
        = ψ (x : ZMod n) * star (χ (N - (x : ZMod n))) := by
      intro x
      rw [star_mul, star_star, mul_comm]
    simp_rw [h2]
    exact sum_units_eq_sum (fun a : ZMod n => ψ a * star (χ (N - a))) e2
  rw [hL, hR, ← hsub]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

lemma reflection_eq_zero_of_factorsThrough {p k j : ℕ} [NeZero (p ^ k)] (hp : p.Prime)
    (hk : 0 < k) (hj : 0 < j) (hjk : j ≤ k) (N : ZMod (p ^ k))
    (χ ψ : DirichletCharacter ℂ (p ^ k))
    (hψ : ψ.FactorsThrough (p ^ j)) (hχ : ¬ χ.FactorsThrough (p ^ j)) :
    (∑ x : (ZMod (p ^ k))ˣ, star (χ (x : ZMod (p ^ k))) * ψ (N - (x : ZMod (p ^ k)))) = 0 := by
  classical
  have hm : p ^ j ∣ p ^ k := Nat.pow_dvd_pow p hjk
  obtain ⟨hdvd, ψ₀, hψ₀⟩ := hψ
  have hex : ∃ t : (ZMod (p ^ k))ˣ,
      (ZMod.cast (t : ZMod (p ^ k)) : ZMod (p ^ j)) = 1 ∧ χ (t : ZMod (p ^ k)) ≠ 1 := by
    by_contra hc
    refine hχ ((DirichletCharacter.factorsThrough_iff_ker_unitsMap hm).mpr ?_)
    intro t ht
    rw [MonoidHom.mem_ker] at ht ⊢
    have hcast : (ZMod.cast (t : ZMod (p ^ k)) : ZMod (p ^ j)) = 1 := by
      have h := congrArg (fun u : (ZMod (p ^ j))ˣ => (u : ZMod (p ^ j))) ht
      rwa [ZMod.unitsMap_val, Units.val_one] at h
    by_contra hcon
    exact hc ⟨t, hcast, fun h1 =>
      hcon (by rw [Units.ext_iff, MulChar.coe_toUnitHom, h1, Units.val_one])⟩
  obtain ⟨t, htcast, hχt⟩ := hex
  have hkey : ∀ y : (ZMod (p ^ k))ˣ,
      (DirichletCharacter.changeLevel hdvd ψ₀) (N - (t : ZMod (p ^ k)) * (y : ZMod (p ^ k)))
        = (DirichletCharacter.changeLevel hdvd ψ₀) (N - (y : ZMod (p ^ k))) := by
    intro y
    rw [changeLevel_apply hp hk hj hdvd ψ₀, changeLevel_apply hp hk hj hdvd ψ₀]
    have htcast2 : (ZMod.castHom hdvd (ZMod (p ^ j))) (t : ZMod (p ^ k)) = 1 := htcast
    have h : (ZMod.cast (N - (t : ZMod (p ^ k)) * (y : ZMod (p ^ k))) : ZMod (p ^ j))
        = (ZMod.cast (N - (y : ZMod (p ^ k))) : ZMod (p ^ j)) := by
      show (ZMod.castHom hdvd (ZMod (p ^ j))) (N - (t : ZMod (p ^ k)) * (y : ZMod (p ^ k)))
          = (ZMod.castHom hdvd (ZMod (p ^ j))) (N - (y : ZMod (p ^ k)))
      rw [map_sub, map_mul, map_sub, htcast2, one_mul]
    rw [h]
  have hb : (∑ y : (ZMod (p ^ k))ˣ,
        star (χ ((t * y : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)))
          * ψ (N - ((t * y : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))))
      = (∑ x : (ZMod (p ^ k))ˣ, star (χ (x : ZMod (p ^ k))) * ψ (N - (x : ZMod (p ^ k)))) :=
    Fintype.sum_bijective (fun y : (ZMod (p ^ k))ˣ => t * y) (Group.mulLeft_bijective t)
      (fun y : (ZMod (p ^ k))ˣ => star (χ ((t * y : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)))
        * ψ (N - ((t * y : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))))
      (fun x : (ZMod (p ^ k))ˣ => star (χ (x : ZMod (p ^ k))) * ψ (N - (x : ZMod (p ^ k))))
      (fun y => rfl)
  have hsum : (∑ x : (ZMod (p ^ k))ˣ, star (χ (x : ZMod (p ^ k))) * ψ (N - (x : ZMod (p ^ k))))
      = star (χ (t : ZMod (p ^ k)))
        * (∑ x : (ZMod (p ^ k))ˣ, star (χ (x : ZMod (p ^ k))) * ψ (N - (x : ZMod (p ^ k)))) := by
    calc (∑ x : (ZMod (p ^ k))ˣ, star (χ (x : ZMod (p ^ k))) * ψ (N - (x : ZMod (p ^ k))))
        = ∑ y : (ZMod (p ^ k))ˣ,
            star (χ ((t * y : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)))
              * ψ (N - ((t * y : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))) := hb.symm
      _ = star (χ (t : ZMod (p ^ k)))
            * (∑ x : (ZMod (p ^ k))ˣ,
                star (χ (x : ZMod (p ^ k))) * ψ (N - (x : ZMod (p ^ k)))) := by
          have hterm : ∀ y : (ZMod (p ^ k))ˣ,
              star (χ ((t * y : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)))
                  * ψ (N - ((t * y : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)))
                = star (χ (t : ZMod (p ^ k)))
                  * (star (χ (y : ZMod (p ^ k))) * ψ (N - (y : ZMod (p ^ k)))) := by
            intro y
            rw [Units.val_mul, map_mul, star_mul, hψ₀, hkey y]
            ring
          simp_rw [hterm]
          rw [Finset.mul_sum]
  have hne : star (χ (t : ZMod (p ^ k))) ≠ 1 := by
    intro hc
    refine hχt ?_
    have h := congrArg star hc
    rw [star_star, star_one] at h
    exact h
  have hz : (star (χ (t : ZMod (p ^ k))) - 1)
      * (∑ x : (ZMod (p ^ k))ˣ, star (χ (x : ZMod (p ^ k))) * ψ (N - (x : ZMod (p ^ k)))) = 0 := by
    rw [sub_mul, ← hsum, one_mul, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

end Conjectures.Goldbach.ReflectionConductorBlocks_aux

theorem Conjectures.Goldbach.ReflectionConductorBlocks :
∀ (p k : ℕ) [Fact p.Prime], 1 ≤ k →
  ∀ (N : ZMod (p^k)) (χ ψ : DirichletCharacter ℂ (p^k)),
    max p χ.conductor ≠ max p ψ.conductor →
      (∑ x : (ZMod (p^k))ˣ, star (χ (x : ZMod (p^k))) * ψ (N - (x : ZMod (p^k)))) = 0 := by
  intro p k hp hk N χ ψ hne
  have hpq : p.Prime := hp.out
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hpq.ne_zero
  obtain ⟨a, hak, hac⟩ : ∃ a, a ≤ k ∧ χ.conductor = p ^ a :=
    (Nat.dvd_prime_pow hpq).mp (DirichletCharacter.conductor_dvd_level χ)
  obtain ⟨b, hbk, hbc⟩ : ∃ b, b ≤ k ∧ ψ.conductor = p ^ b :=
    (Nat.dvd_prime_pow hpq).mp (DirichletCharacter.conductor_dvd_level ψ)
  have hma : max p χ.conductor = p ^ (max 1 a) := by
    rw [hac]
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rw [pow_zero, max_eq_left hp1, max_eq_left (Nat.zero_le 1), pow_one]
    · have h1 : p ≤ p ^ a := by
        calc p = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ a := Nat.pow_le_pow_right hpq.pos ha
      rw [max_eq_right h1, max_eq_right ha]
  have hmb : max p ψ.conductor = p ^ (max 1 b) := by
    rw [hbc]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · rw [pow_zero, max_eq_left hp1, max_eq_left (Nat.zero_le 1), pow_one]
    · have h1 : p ≤ p ^ b := by
        calc p = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ b := Nat.pow_le_pow_right hpq.pos hb
      rw [max_eq_right h1, max_eq_right hb]
  have hne2 : max 1 a ≠ max 1 b := by
    intro hcon
    refine hne ?_
    rw [hma, hmb, hcon]
  rcases lt_or_gt_of_ne hne2 with hlt | hgt
  · have hj : 0 < max 1 a := lt_of_lt_of_le (by norm_num) (le_max_left 1 a)
    have hjk : max 1 a ≤ k := by
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · rw [max_eq_left (Nat.zero_le 1)]; exact hk
      · rw [max_eq_right ha]; exact hak
    have hchi : χ.FactorsThrough (p ^ (max 1 a)) := by
      have h1 : χ.conductor ∣ p ^ (max 1 a) := by
        rw [hac]; exact Nat.pow_dvd_pow p (le_max_right 1 a)
      exact (DirichletCharacter.mem_conductorSet_iff χ).mp
        ((DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ
          (Nat.pow_dvd_pow p hjk)).mpr h1)
    have hpsi : ¬ ψ.FactorsThrough (p ^ (max 1 a)) := by
      intro hfac
      have h1 : ψ.conductor ∣ p ^ (max 1 a) :=
        (DirichletCharacter.mem_conductorSet_iff_conductor_dvd ψ
          (Nat.pow_dvd_pow p hjk)).mp
          ((DirichletCharacter.mem_conductorSet_iff ψ).mpr hfac)
      rw [hbc] at h1
      obtain ⟨m, hm, hpm⟩ := (Nat.dvd_prime_pow hpq).mp h1
      have hab : b = m := Nat.pow_right_injective hpq.two_le hpm
      have h2 : max 1 b ≤ max 1 a := by
        refine max_le (le_max_left 1 a) ?_
        rw [hab]; exact hm
      exact absurd h2 (not_le.mpr hlt)
    have hz : (∑ x : (ZMod (p^k))ˣ, star (ψ (x : ZMod (p^k))) * χ (N - (x : ZMod (p^k)))) = 0 :=
      Conjectures.Goldbach.ReflectionConductorBlocks_aux.reflection_eq_zero_of_factorsThrough
        hpq hk hj hjk N ψ χ hchi hpsi
    rw [Conjectures.Goldbach.ReflectionConductorBlocks_aux.reflection_swap N χ ψ, hz, star_zero]
  · have hj : 0 < max 1 b := lt_of_lt_of_le (by norm_num) (le_max_left 1 b)
    have hjk : max 1 b ≤ k := by
      rcases Nat.eq_zero_or_pos b with rfl | hb
      · rw [max_eq_left (Nat.zero_le 1)]; exact hk
      · rw [max_eq_right hb]; exact hbk
    have hpsifac : ψ.FactorsThrough (p ^ (max 1 b)) := by
      have h1 : ψ.conductor ∣ p ^ (max 1 b) := by
        rw [hbc]; exact Nat.pow_dvd_pow p (le_max_right 1 b)
      exact (DirichletCharacter.mem_conductorSet_iff ψ).mp
        ((DirichletCharacter.mem_conductorSet_iff_conductor_dvd ψ
          (Nat.pow_dvd_pow p hjk)).mpr h1)
    have hchin : ¬ χ.FactorsThrough (p ^ (max 1 b)) := by
      intro hfac
      have h1 : χ.conductor ∣ p ^ (max 1 b) :=
        (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ
          (Nat.pow_dvd_pow p hjk)).mp
          ((DirichletCharacter.mem_conductorSet_iff χ).mpr hfac)
      rw [hac] at h1
      obtain ⟨m, hm, hpm⟩ := (Nat.dvd_prime_pow hpq).mp h1
      have hab : a = m := Nat.pow_right_injective hpq.two_le hpm
      have h2 : max 1 a ≤ max 1 b := by
        refine max_le (le_max_left 1 b) ?_
        rw [hab]; exact hm
      exact absurd h2 (not_le.mpr hgt)
    exact Conjectures.Goldbach.ReflectionConductorBlocks_aux.reflection_eq_zero_of_factorsThrough
      hpq hk hj hjk N χ ψ hpsifac hchin
