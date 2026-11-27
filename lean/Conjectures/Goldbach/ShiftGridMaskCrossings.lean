import Mathlib

private noncomputable def gridCell (K j : ℕ) : Set ℝ := Set.Icc ((j:ℝ)/K) (((j:ℝ)+1)/K)

private noncomputable def hits (K : ℕ) (x : ℝ) : Finset ℕ :=
  @Finset.filter ℕ (fun j => x ∈ gridCell K j) (fun _ => Classical.propDecidable _) (Finset.range K)

private theorem atMostTwo {K : ℕ} (hK : 0 < K) (x : ℝ) : (hits K x).card ≤ 2 := by
  classical
  by_cases h : (hits K x).Nonempty
  · let i := (hits K x).min' h
    have hi' : i ∈ hits K x := Finset.min'_mem _ _
    simp only [hits, Finset.mem_filter] at hi'
    have hi := hi'.2
    change (i:ℝ)/K ≤ x ∧ x ≤ ((i:ℝ)+1)/K at hi
    have sub : hits K x ⊆ {i,i+1} := by
      intro j hj
      have hlo : i ≤ j := Finset.min'_le _ _ hj
      simp only [hits, Finset.mem_filter] at hj
      have hjx := hj.2
      change (j:ℝ)/K ≤ x ∧ x ≤ ((j:ℝ)+1)/K at hjx
      have hk : (0:ℝ) < K := by exact_mod_cast hK
      have hreal : (j:ℝ) ≤ (i:ℝ)+1 := (div_le_div_iff_of_pos_right hk).mp (hjx.1.trans hi.2)
      have hhi : j ≤ i+1 := by exact_mod_cast hreal
      simp only [Finset.mem_insert,Finset.mem_singleton]
      omega
    exact (Finset.card_le_card sub).trans (by simp)
  · simp [Finset.not_nonempty_iff_eq_empty.mp h]

private theorem countCross {K : ℕ} (hk : 0 < K) (Q : ℕ) (c d : ℕ → ℕ → ℝ)
    (ok : ℕ → ℕ → Prop) :
    let arcs : Set ℝ := {t | ∃ q ∈ Finset.Icc 1 Q, ∃ a ∈ Finset.range (q+1),
      ok q a ∧ |t - c q a| ≤ d q a}
    let cross := @Finset.filter ℕ (fun j => ((gridCell K j) ∩ arcs).Nonempty ∧
      ((gridCell K j) ∩ arcsᶜ).Nonempty) (fun _ => Classical.propDecidable _) (Finset.range K)
    cross.card ≤ 4 * ∑ q ∈ Finset.Icc 1 Q, (q+1) := by
  classical
  intro arcs cross
  let ends := fun q a => hits K (c q a - d q a) ∪ hits K (c q a + d q a)
  let row := fun q => (Finset.range (q+1)).biUnion (ends q)
  have sub : cross ⊆ (Finset.Icc 1 Q).biUnion row := by
    intro j hj
    simp only [cross,Finset.mem_filter] at hj
    obtain ⟨hj,⟨u,hu,⟨q,hq,a,ha,hgood,huarc⟩⟩,⟨v,hv,hvout⟩⟩ := hj
    refine Finset.mem_biUnion.mpr ⟨q,hq,Finset.mem_biUnion.mpr ⟨a,ha,?_⟩⟩
    have hvbad : ¬ |v-c q a| ≤ d q a := fun hv' => hvout ⟨q,hq,a,ha,hgood,hv'⟩
    rw [abs_le] at huarc hvbad
    change (j:ℝ)/K ≤ u ∧ u ≤ ((j:ℝ)+1)/K at hu
    change (j:ℝ)/K ≤ v ∧ v ≤ ((j:ℝ)+1)/K at hv
    simp only [ends,Finset.mem_union,hits,Finset.mem_filter]
    
    by_cases hleft : v < c q a - d q a
    · left
      refine ⟨hj,?_,?_⟩ <;> linarith
    · right
      have ht : c q a + d q a < v := by by_contra! hc; exact hvbad ⟨by linarith,by linarith⟩
      refine ⟨hj,?_,?_⟩ <;> linarith
  have rowle (q : ℕ) : (row q).card ≤ (q+1)*4 := by
    calc
      _ ≤ ∑ a ∈ Finset.range (q+1), (ends q a).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ Finset.range (q+1), 4 := Finset.sum_le_sum fun a _ =>
        (Finset.card_union_le _ _).trans (Nat.add_le_add (atMostTwo hk _) (atMostTwo hk _))
      _ = _ := by simp
  calc
    _ ≤ _ := Finset.card_le_card sub
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, (row q).card := Finset.card_biUnion_le
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, (q+1)*4 := Finset.sum_le_sum fun q _ => rowle q
    _ = _ := by rw [← Finset.sum_mul, Nat.mul_comm]

theorem Conjectures.Goldbach.ShiftGridMaskCrossings :
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; ∀ n K : ℕ, 0 < n → 0 < K →
let cell := fun j : ℕ => Set.Icc ((j : ℝ) / K) (((j : ℝ)+1) / K)
let cross := @Finset.filter ℕ (fun j => ((cell j) ∩ (wideArcs n)).Nonempty ∧ ((cell j) ∩ (wideArcs n)ᶜ).Nonempty) (fun _ => Classical.propDecidable _) (Finset.range K)
cross.card ≤ 4 * (∑ q ∈ Finset.Icc 1 (Q₁ n), (q+1)) := by
  intro Q Q₁ H arcs n K hn hK cell cross
  have harcs : arcs n = {t | ∃ q ∈ Finset.Icc 1 (Q₁ n), ∃ a ∈ Finset.range (q+1),
      Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))} := by
    ext t
    constructor
    · rintro ⟨q,a,h1,h2,h3,h4,h5⟩
      exact ⟨q,Finset.mem_Icc.mpr ⟨h1,h2⟩,a,Finset.mem_range.mpr (by omega),h4,h5⟩
    · rintro ⟨q,hq,a,ha,h4,h5⟩
      exact ⟨q,a,(Finset.mem_Icc.mp hq).1,(Finset.mem_Icc.mp hq).2,
        Nat.le_of_lt_succ (Finset.mem_range.mp ha),h4,h5⟩
  dsimp only [cross,cell]
  rw [harcs]
  exact countCross hK (Q₁ n) (fun q a => (a:ℝ)/q) (fun q _ => (H n:ℝ)/((q:ℝ)*n))
    (fun q a => Nat.Coprime a q)
