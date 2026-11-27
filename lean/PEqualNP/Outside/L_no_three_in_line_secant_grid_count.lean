import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_secant_grid_count :
    let d := fun (a b c : ℤ × ℤ) => (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1); let ok := fun (S : Finset (ℤ × ℤ)) => ∀ a∈S, ∀ b∈S, ∀ c∈S, a≠b → b≠c → a≠c → d a b c≠0; ∀ (S : Finset (ℤ × ℤ)) (y : ℤ) (X : Finset ℤ), ok S → (∀ a∈S,a.2≠y) → S.card*(S.card-1)/2<X.card → ∃ x∈X,ok (insert (x,y) S) := by
  intro d ok S y X hS hy hcard
  let forb : Finset (ℤ × ℤ) → Finset ℤ :=
    fun P => X.filter (fun x => ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧ d a b (x, y) = 0)
  have hforb_le : ∀ P ∈ S.powersetCard 2, (forb P).card ≤ 1 := by
    intro P hP
    obtain ⟨hPS, hP2⟩ := Finset.mem_powersetCard.mp hP
    obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hP2
    have hpS : p ∈ S := hPS (Finset.mem_insert_self p {q})
    have hpy : p.2 ≠ y := hy p hpS
    have hpair : ∀ x ∈ forb {p, q}, d p q (x, y) = 0 := by
      intro x hx
      obtain ⟨_, a, ha, b, hb, hab, hdab⟩ := Finset.mem_filter.mp hx
      have ha' : a = p ∨ a = q := by simpa using ha
      have hb' : b = p ∨ b = q := by simpa using hb
      rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
      · exact absurd rfl hab
      · exact hdab
      · dsimp only [d] at hdab ⊢
        linarith
      · exact absurd rfl hab
    refine Finset.card_le_one.mpr ?_
    intro x₁ hx₁ x₂ hx₂
    have h1 : d p q (x₁, y) = 0 := hpair x₁ hx₁
    have h2 : d p q (x₂, y) = 0 := hpair x₂ hx₂
    dsimp only [d] at h1 h2
    have hdiff : (q.2 - p.2) * (x₁ - x₂) = 0 := by linarith
    rcases mul_eq_zero.mp hdiff with hq2 | hx12
    · have hq2eq : q.2 = p.2 := sub_eq_zero.mp hq2
      have h1' : (q.1 - p.1) * (y - p.2) = 0 := by
        rw [hq2] at h1
        linarith
      rcases mul_eq_zero.mp h1' with hq1 | hyp
      · have hq1eq : q.1 = p.1 := sub_eq_zero.mp hq1
        exact absurd (Prod.ext hq1eq.symm hq2eq.symm) hpq
      · exact absurd (sub_eq_zero.mp hyp).symm hpy
    · exact sub_eq_zero.mp hx12
  let Bad : Finset ℤ := (S.powersetCard 2).biUnion forb
  have hBad_card : Bad.card < X.card := by
    have h1 : Bad.card ≤ ∑ P ∈ S.powersetCard 2, (forb P).card := Finset.card_biUnion_le
    have h2 : ∑ P ∈ S.powersetCard 2, (forb P).card ≤ ∑ _P ∈ S.powersetCard 2, 1 :=
      Finset.sum_le_sum hforb_le
    have h3 : (∑ _P ∈ S.powersetCard 2, 1) = (S.powersetCard 2).card := by simp
    have h4 : (S.powersetCard 2).card = S.card * (S.card - 1) / 2 := by
      rw [Finset.card_powersetCard, Nat.choose_two_right]
    omega
  obtain ⟨x, hxX, hxBad⟩ := Finset.exists_mem_notMem_of_card_lt_card hBad_card
  refine ⟨x, hxX, ?_⟩
  intro a ha b hb c hc hab hbc hac hd0
  have hnot_pair : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → d u v (x, y) ≠ 0 := by
    intro u hu v hv huv hduv
    have hsub : ({u, v} : Finset (ℤ × ℤ)) ⊆ S := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz'
      · exact hu
      · rw [Finset.mem_singleton.mp hz']
        exact hv
    have hPmem : ({u, v} : Finset (ℤ × ℤ)) ∈ S.powersetCard 2 :=
      Finset.mem_powersetCard.mpr ⟨hsub, Finset.card_pair huv⟩
    have hxforb : x ∈ forb {u, v} :=
      Finset.mem_filter.mpr ⟨hxX, u, Finset.mem_insert_self u {v}, v,
        Finset.mem_insert_of_mem (Finset.mem_singleton_self v), huv, hduv⟩
    exact hxBad (Finset.mem_biUnion.mpr ⟨{u, v}, hPmem, hxforb⟩)
  rcases Finset.mem_insert.mp ha with rfl | haS <;>
    rcases Finset.mem_insert.mp hb with rfl | hbS <;>
    rcases Finset.mem_insert.mp hc with rfl | hcS
  · exact absurd rfl hab
  · exact absurd rfl hab
  · exact absurd rfl hac
  · refine hnot_pair b hbS c hcS hbc ?_
    dsimp only [d] at hd0 ⊢
    linarith
  · exact absurd rfl hbc
  · refine hnot_pair a haS c hcS hac ?_
    dsimp only [d] at hd0 ⊢
    linarith
  · exact hnot_pair a haS b hbS hab hd0
  · exact hS a haS b hbS c hcS hab hbc hac hd0
