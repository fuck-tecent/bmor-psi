import Mathlib

namespace GoldbachAux

/-- 条带：与中心 `c` 的距离落在半开区间 `(r2, r1]` 的点集。 -/
def strip (c r1 r2 : ℝ) : Set ℝ := {u : ℝ | r2 < |u - c| ∧ |u - c| ≤ r1}

lemma strip_volume_le (c r1 r2 : ℝ) (hr2 : 0 ≤ r2) (hr12 : r2 ≤ r1) :
    MeasureTheory.volume (strip c r1 r2) ≤ ENNReal.ofReal (2 * (r1 - r2)) := by
  have hsub : strip c r1 r2 ⊆ Set.Ico (c - r1) (c - r2) ∪ Set.Ioc (c + r2) (c + r1) := by
    intro u hu
    obtain ⟨h1, h2⟩ := hu
    rcases lt_or_ge u c with hu' | hu'
    · have hneg : u - c ≤ 0 := by linarith
      rw [abs_of_nonpos hneg] at h1 h2
      exact Or.inl ⟨by linarith, by linarith⟩
    · have hpos : 0 ≤ u - c := by linarith
      rw [abs_of_nonneg hpos] at h1 h2
      exact Or.inr ⟨by linarith, by linarith⟩
  calc MeasureTheory.volume (strip c r1 r2)
      ≤ MeasureTheory.volume (Set.Ico (c - r1) (c - r2) ∪ Set.Ioc (c + r2) (c + r1)) :=
        MeasureTheory.measure_mono hsub
    _ ≤ MeasureTheory.volume (Set.Ico (c - r1) (c - r2))
          + MeasureTheory.volume (Set.Ioc (c + r2) (c + r1)) :=
        MeasureTheory.measure_union_le _ _
    _ = ENNReal.ofReal (r1 - r2) + ENNReal.ofReal (r1 - r2) := by
        rw [Real.volume_Ico, Real.volume_Ioc,
          show (c - r2) - (c - r1) = r1 - r2 from by ring,
          show (c + r1) - (c + r2) = r1 - r2 from by ring]
    _ = ENNReal.ofReal (2 * (r1 - r2)) := by
        rw [← ENNReal.ofReal_add (by linarith : 0 ≤ r1 - r2) (by linarith : 0 ≤ r1 - r2)]
        congr 1
        ring

lemma ofReal_sum_eq {ι : Type*} (f : ι → ℝ) :
    ∀ s : Finset ι, (∀ i ∈ s, 0 ≤ f i) →
      ENNReal.ofReal (∑ i ∈ s, f i) = ∑ i ∈ s, ENNReal.ofReal (f i) := by
  classical
  intro s
  induction s using Finset.induction with
  | empty => intro _; simp
  | insert i s hi ih =>
      intro hf
      have hrest : ∀ j ∈ s, 0 ≤ f j := fun j hj => hf j (Finset.mem_insert_of_mem hj)
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        ENNReal.ofReal_add (hf i (Finset.mem_insert_self i s)) (Finset.sum_nonneg hrest),
        ih hrest]

end GoldbachAux

theorem PEqualNP.Outside.L_goldbach_plateau_arc_shell :
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; ∀ n h : ℕ, 0<n → Q (n+h)=Q n → MeasureTheory.volume ((arcs n) \ (arcs (n+h))) ≤ ENNReal.ofReal (4*(Q n:ℝ)^2*(h:ℝ)/((n:ℝ)*((n+h:ℕ):ℝ))) := by
  intro Q arcs n h hn hQ
  have hArcs : ∀ m : ℕ, arcs m = {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q m ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q m:ℝ)/((q:ℝ)*(m:ℝ))} := fun _ => rfl
  have hlog : 0 < Nat.log 2 (n+2) := Nat.log_pos_iff.mpr ⟨by omega, by omega⟩
  have hQnpos : 0 < Q n := pow_pos hlog 2
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hnhR : (0:ℝ) < ((n+h:ℕ):ℝ) := Nat.cast_pos.mpr (show 0 < n + h by omega)
  have hQn0 : (0:ℝ) ≤ Q n := Nat.cast_nonneg (Q n)
  have hr2le : ∀ q : ℕ, 1 ≤ q → (Q n:ℝ)/((q:ℝ)*(n+h:ℕ)) ≤ (Q n:ℝ)/((q:ℝ)*n) := by
    intro q hq1
    have hqR : (0:ℝ) < q := by exact_mod_cast hq1
    exact div_le_div_of_nonneg_left hQn0 (mul_pos hqR hnR) (by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast (Nat.le_add_right n h))
  have hnonneg : ∀ q : ℕ, 1 ≤ q → 0 ≤ 2 * ((Q n:ℝ)/((q:ℝ)*n) - (Q n:ℝ)/((q:ℝ)*(n+h:ℕ))) := by
    intro q hq1
    have := hr2le q hq1
    linarith
  have hcover : (arcs n) \ (arcs (n+h)) ⊆ ⋃ q ∈ Finset.Ico 1 (Q n + 1), ⋃ a ∈ Finset.filter (fun a => Nat.Coprime a q) (Finset.range (q + 1)), GoldbachAux.strip ((a:ℝ)/(q:ℝ)) ((Q n:ℝ)/((q:ℝ)*n)) ((Q n:ℝ)/((q:ℝ)*(n+h:ℕ))) := by
    rintro t ⟨ht1, ht2⟩
    rw [hArcs n] at ht1
    obtain ⟨q, a, hq1, hq2, ha, hcop, habs⟩ := ht1
    have hnot : ¬ (|t - (a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n+h:ℕ))) := by
      intro hle
      apply ht2
      rw [hArcs (n+h)]
      exact ⟨q, a, hq1, by rw [hQ]; exact hq2, ha, hcop, by rw [hQ]; exact hle⟩
    refine Set.mem_iUnion₂.mpr ⟨q, Finset.mem_Ico.mpr ⟨hq1, Nat.lt_succ_of_le hq2⟩, ?_⟩
    refine Set.mem_iUnion₂.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le ha), hcop⟩, ?_⟩
    exact ⟨lt_of_not_ge hnot, habs⟩
  have hbound : MeasureTheory.volume ((arcs n) \ (arcs (n+h)))
      ≤ ENNReal.ofReal (∑ q ∈ Finset.Ico 1 (Q n + 1), ∑ a ∈ Finset.filter (fun a => Nat.Coprime a q) (Finset.range (q + 1)), 2 * ((Q n:ℝ)/((q:ℝ)*n) - (Q n:ℝ)/((q:ℝ)*(n+h:ℕ)))) := by
    calc MeasureTheory.volume ((arcs n) \ (arcs (n+h)))
        ≤ MeasureTheory.volume (⋃ q ∈ Finset.Ico 1 (Q n + 1), ⋃ a ∈ Finset.filter (fun a => Nat.Coprime a q) (Finset.range (q + 1)), GoldbachAux.strip ((a:ℝ)/(q:ℝ)) ((Q n:ℝ)/((q:ℝ)*n)) ((Q n:ℝ)/((q:ℝ)*(n+h:ℕ)))) :=
          MeasureTheory.measure_mono hcover
      _ ≤ ∑ q ∈ Finset.Ico 1 (Q n + 1), MeasureTheory.volume (⋃ a ∈ Finset.filter (fun a => Nat.Coprime a q) (Finset.range (q + 1)), GoldbachAux.strip ((a:ℝ)/(q:ℝ)) ((Q n:ℝ)/((q:ℝ)*n)) ((Q n:ℝ)/((q:ℝ)*(n+h:ℕ)))) :=
          MeasureTheory.measure_biUnion_finset_le _ _
      _ ≤ ∑ q ∈ Finset.Ico 1 (Q n + 1), ∑ a ∈ Finset.filter (fun a => Nat.Coprime a q) (Finset.range (q + 1)), MeasureTheory.volume (GoldbachAux.strip ((a:ℝ)/(q:ℝ)) ((Q n:ℝ)/((q:ℝ)*n)) ((Q n:ℝ)/((q:ℝ)*(n+h:ℕ)))) :=
          Finset.sum_le_sum (fun q _ => MeasureTheory.measure_biUnion_finset_le _ _)
      _ ≤ ∑ q ∈ Finset.Ico 1 (Q n + 1), ∑ a ∈ Finset.filter (fun a => Nat.Coprime a q) (Finset.range (q + 1)), ENNReal.ofReal (2 * ((Q n:ℝ)/((q:ℝ)*n) - (Q n:ℝ)/((q:ℝ)*(n+h:ℕ)))) :=
          Finset.sum_le_sum (fun q hq => Finset.sum_le_sum (fun a _ =>
            GoldbachAux.strip_volume_le ((a:ℝ)/(q:ℝ)) ((Q n:ℝ)/((q:ℝ)*n)) ((Q n:ℝ)/((q:ℝ)*(n+h:ℕ)))
              (div_nonneg hQn0 (mul_nonneg (le_of_lt (by exact_mod_cast (Finset.mem_Ico.mp hq).1 : (0:ℝ) < q)) hnhR.le)) (hr2le q (Finset.mem_Ico.mp hq).1)))
      _ = ENNReal.ofReal (∑ q ∈ Finset.Ico 1 (Q n + 1), ∑ a ∈ Finset.filter (fun a => Nat.Coprime a q) (Finset.range (q + 1)), 2 * ((Q n:ℝ)/((q:ℝ)*n) - (Q n:ℝ)/((q:ℝ)*(n+h:ℕ)))) := by
          symm
          rw [GoldbachAux.ofReal_sum_eq (fun q => ∑ a ∈ Finset.filter (fun a => Nat.Coprime a q) (Finset.range (q + 1)), 2 * ((Q n:ℝ)/((q:ℝ)*n) - (Q n:ℝ)/((q:ℝ)*(n+h:ℕ)))) (Finset.Ico 1 (Q n + 1))
            (fun q hq => Finset.sum_nonneg (fun a _ => hnonneg q (Finset.mem_Ico.mp hq).1))]
          exact Finset.sum_congr rfl (fun q hq => GoldbachAux.ofReal_sum_eq (fun a => 2 * ((Q n:ℝ)/((q:ℝ)*n) - (Q n:ℝ)/((q:ℝ)*(n+h:ℕ)))) (Finset.filter (fun a => Nat.Coprime a q) (Finset.range (q + 1))) (fun a _ => hnonneg q (Finset.mem_Ico.mp hq).1))
  have hterm : ∀ q ∈ Finset.Ico 1 (Q n + 1),
      ∑ a ∈ Finset.filter (fun a => Nat.Coprime a q) (Finset.range (q + 1)), 2 * ((Q n:ℝ)/((q:ℝ)*n) - (Q n:ℝ)/((q:ℝ)*(n+h:ℕ)))
      ≤ 4 * (Q n:ℝ) * (h:ℝ) / ((n:ℝ) * ((n+h:ℕ):ℝ)) := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Ico.mp hq).1
    have hq1R : (1:ℝ) ≤ q := by exact_mod_cast hq1
    have hqR : (0:ℝ) < q := by exact_mod_cast hq1
    have hq0 : (q:ℝ) ≠ 0 := ne_of_gt hqR
    have hn0 : (n:ℝ) ≠ 0 := ne_of_gt hnR
    have hnh0 : ((n+h:ℕ):ℝ) ≠ 0 := ne_of_gt hnhR
    have hcast : ((n+h:ℕ):ℝ) = (n:ℝ) + (h:ℝ) := Nat.cast_add n h
    have hX : 0 ≤ 2 * ((Q n:ℝ)/((q:ℝ)*n) - (Q n:ℝ)/((q:ℝ)*(n+h:ℕ))) := hnonneg q hq1
    have hsub : Finset.filter (fun a => Nat.Coprime a q) (Finset.range (q + 1)) ⊆ Finset.range (q + 1) := by
      intro a hmem
      exact (Finset.mem_filter.mp hmem).1
    have hin : ∑ a ∈ Finset.filter (fun a => Nat.Coprime a q) (Finset.range (q + 1)), 2 * ((Q n:ℝ)/((q:ℝ)*n) - (Q n:ℝ)/((q:ℝ)*(n+h:ℕ)))
        ≤ ((q+1:ℕ):ℝ) * 2 * ((Q n:ℝ)/((q:ℝ)*n) - (Q n:ℝ)/((q:ℝ)*(n+h:ℕ))) := by
      calc ∑ a ∈ Finset.filter (fun a => Nat.Coprime a q) (Finset.range (q + 1)), 2 * ((Q n:ℝ)/((q:ℝ)*n) - (Q n:ℝ)/((q:ℝ)*(n+h:ℕ)))
          ≤ ∑ a ∈ Finset.range (q+1), 2 * ((Q n:ℝ)/((q:ℝ)*n) - (Q n:ℝ)/((q:ℝ)*(n+h:ℕ))) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro a _ _; exact hX)
        _ = ((Finset.range (q+1)).card:ℕ) • (2 * ((Q n:ℝ)/((q:ℝ)*n) - (Q n:ℝ)/((q:ℝ)*(n+h:ℕ)))) := Finset.sum_const _
        _ = ((q+1:ℕ):ℝ) * 2 * ((Q n:ℝ)/((q:ℝ)*n) - (Q n:ℝ)/((q:ℝ)*(n+h:ℕ))) := by
            rw [Finset.card_range, nsmul_eq_mul]
            ring
    have hkey : ((q+1:ℕ):ℝ) * 2 * ((Q n:ℝ)/((q:ℝ)*n) - (Q n:ℝ)/((q:ℝ)*(n+h:ℕ)))
        ≤ 4 * (Q n:ℝ) * (h:ℝ) / ((n:ℝ) * ((n+h:ℕ):ℝ)) := by
      have hfrac : ((q+1:ℕ):ℝ)/q ≤ 2 := by
        rw [div_le_iff₀ hqR]
        exact_mod_cast (show q + 1 ≤ 2 * q from by omega)
      calc ((q+1:ℕ):ℝ) * 2 * ((Q n:ℝ)/((q:ℝ)*n) - (Q n:ℝ)/((q:ℝ)*(n+h:ℕ)))
          = (((q+1:ℕ):ℝ)/q) * (2 * ((Q n:ℝ)*(h:ℝ) / ((n:ℝ) * ((n+h:ℕ):ℝ)))) := by
            rw [hcast]
            field_simp [hq0, hn0]
            ring
        _ ≤ 2 * (2 * ((Q n:ℝ)*(h:ℝ) / ((n:ℝ) * ((n+h:ℕ):ℝ)))) :=
            mul_le_mul_of_nonneg_right hfrac (by positivity)
        _ = 4 * (Q n:ℝ) * (h:ℝ) / ((n:ℝ) * ((n+h:ℕ):ℝ)) := by
            ring
    linarith [hin, hkey]
  have hreal : ∑ q ∈ Finset.Ico 1 (Q n + 1), ∑ a ∈ Finset.filter (fun a => Nat.Coprime a q) (Finset.range (q + 1)), 2 * ((Q n:ℝ)/((q:ℝ)*n) - (Q n:ℝ)/((q:ℝ)*(n+h:ℕ)))
      ≤ 4*(Q n:ℝ)^2*(h:ℝ)/((n:ℝ)*((n+h:ℕ):ℝ)) := by
    have hstep : ∑ q ∈ Finset.Ico 1 (Q n + 1), ∑ a ∈ Finset.filter (fun a => Nat.Coprime a q) (Finset.range (q + 1)), 2 * ((Q n:ℝ)/((q:ℝ)*n) - (Q n:ℝ)/((q:ℝ)*(n+h:ℕ)))
        ≤ ∑ q ∈ Finset.Ico 1 (Q n + 1), 4 * (Q n:ℝ) * (h:ℝ) / ((n:ℝ) * ((n+h:ℕ):ℝ)) :=
          Finset.sum_le_sum hterm
    have hconst : ∑ q ∈ Finset.Ico 1 (Q n + 1), 4 * (Q n:ℝ) * (h:ℝ) / ((n:ℝ) * ((n+h:ℕ):ℝ))
        = 4*(Q n:ℝ)^2*(h:ℝ)/((n:ℝ)*((n+h:ℕ):ℝ)) := by
      rw [Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel, nsmul_eq_mul]
      ring
    linarith [hstep, hconst]
  exact le_trans hbound (ENNReal.ofReal_le_ofReal hreal)
