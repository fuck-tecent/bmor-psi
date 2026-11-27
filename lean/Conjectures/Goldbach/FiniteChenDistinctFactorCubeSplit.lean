import Mathlib

private theorem orderedFactors {a b c d : ℕ} (ha : a.Prime) (_hb : b.Prime)
    (hc : c.Prime) (hd : d.Prime) (hab : a < b) (hcd : c < d)
    (he : a*b = c*d) : a = c ∧ b = d := by
  have hdiv : a ∣ c*d := he ▸ dvd_mul_right a b
  rcases ha.dvd_mul.mp hdiv with h | h
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq ha hc).mp h
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left ha.pos he⟩
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq ha hd).mp h
    have hbc := Nat.eq_of_mul_eq_mul_left ha.pos (he.trans (Nat.mul_comm _ _))
    omega

theorem Conjectures.Goldbach.FiniteChenDistinctFactorCubeSplit : ∀ n : ℕ, let R := (Finset.Icc 2 n).filter Nat.Prime; let D := (Finset.range (n+1)).filter (fun p => p.Prime ∧ (R.filter (fun r => ((Finset.Ioc r (n/r)).filter (fun v => v.Prime ∧ p+r*v=n)).Nonempty)).Nonempty); let B := D.filter (fun p => (R.filter (fun r => r ∣ n ∧ ((Finset.Ioc r (n/r)).filter (fun v => v.Prime ∧ p+r*v=n)).Nonempty)).Nonempty); let L := R.filter (fun r => ¬ r∣n ∧ r^3≤n); let H := R.filter (fun r => ¬ r∣n ∧ n<r^3); let F := fun r : ℕ => ((Finset.Ioc r (n/r)).filter (fun v => v.Prime ∧ (n-r*v).Prime)).card; D.card = B.card + (∑ r ∈ L, F r) + (∑ r ∈ H, F r) ∧ B.card≤n.primeFactors.card := by
  classical
  intro n
  dsimp only
  let R := (Finset.Icc 2 n).filter Nat.Prime
  let W := fun p r : ℕ => ((Finset.Ioc r (n/r)).filter (fun v => v.Prime ∧ p+r*v=n)).Nonempty
  let D := (Finset.range (n+1)).filter (fun p => p.Prime ∧ (R.filter (W p)).Nonempty)
  let B := D.filter (fun p => (R.filter (fun r => r ∣ n ∧ W p r)).Nonempty)
  let G := R.filter (fun r => ¬ r ∣ n)
  let V := fun r : ℕ => (Finset.Ioc r (n/r)).filter (fun v => v.Prime ∧ (n-r*v).Prime)
  let pairs := G.sigma V
  let f := fun z : (Σ _ : ℕ, ℕ) => n-z.1*z.2
  have memD {p : ℕ} : p ∈ D ↔ p < n+1 ∧ p.Prime ∧ ∃ r ∈ R, W p r := by
    simp only [D, Finset.mem_filter, Finset.mem_range, Finset.filter_nonempty_iff]
  have memB {p : ℕ} : p ∈ B ↔ p ∈ D ∧ ∃ r ∈ R, r ∣ n ∧ W p r := by
    simp only [B, Finset.mem_filter, Finset.filter_nonempty_iff]
  have posR {r : ℕ} (hr : r ∈ R) : r.Prime := (Finset.mem_filter.mp hr).2
  have factors {p r : ℕ} : W p r ↔ ∃ v ∈ Finset.Ioc r (n/r), v.Prime ∧ p+r*v=n :=
    Finset.filter_nonempty_iff
  have mulBound {r v : ℕ} (hr : r ∈ R) (hv : v ∈ Finset.Ioc r (n/r)) : r*v ≤ n := by
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le (posR hr).pos).mp (Finset.mem_Ioc.mp hv).2
  have decode {z : Σ _ : ℕ, ℕ} (hz : z ∈ pairs) :
      z.1 ∈ R ∧ ¬ z.1 ∣ n ∧ z.2 ∈ Finset.Ioc z.1 (n/z.1) ∧ z.2.Prime ∧ (f z).Prime := by
    obtain ⟨hr,hv⟩ := Finset.mem_sigma.mp hz
    exact ⟨(Finset.mem_filter.mp hr).1, (Finset.mem_filter.mp hr).2,
      (Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2⟩
  have eqsets : D \ B = pairs.image f := by
    ext p
    constructor
    · intro hp
      obtain ⟨hd,hb⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨_,pr,r,hr,hw⟩ := memD.mp hd
      obtain ⟨v,hv,pv,eq⟩ := factors.mp hw
      have good : ¬ r ∣ n := fun h => hb (memB.mpr ⟨hd,r,hr,h,hw⟩)
      have val : n-r*v=p := by omega
      exact Finset.mem_image.mpr ⟨⟨r,v⟩, Finset.mem_sigma.mpr
        ⟨Finset.mem_filter.mpr ⟨hr,good⟩, Finset.mem_filter.mpr ⟨hv,pv,val.symm ▸ pr⟩⟩, val⟩
    · intro hp
      obtain ⟨⟨r,v⟩,hz,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hr,good,hv,pv,pr⟩ := decode hz
      have bound := mulBound hr hv
      have eq : f ⟨r,v⟩ + r*v=n := Nat.sub_add_cancel bound
      apply Finset.mem_sdiff.mpr
      refine ⟨memD.mpr ⟨by dsimp [f]; omega,pr,r,hr,factors.mpr ⟨v,hv,pv,eq⟩⟩, ?_⟩
      intro hb
      obtain ⟨_,s,hs,hsn,hw⟩ := memB.mp hb
      obtain ⟨w,hw,pw,eq'⟩ := factors.mp hw
      obtain ⟨hh,_⟩ := orderedFactors (posR hr) pv (posR hs) pw
        (Finset.mem_Ioc.mp hv).1 (Finset.mem_Ioc.mp hw).1 (Nat.add_left_cancel (eq.trans eq'.symm))
      exact good (hh.symm ▸ hsn)
  have inj : Set.InjOn f (↑pairs) := by
    rintro ⟨a,b⟩ hx ⟨c,d⟩ hy he
    obtain ⟨ha,_,hb,pb,_⟩ := decode hx
    obtain ⟨hc,_,hd,pd,_⟩ := decode hy
    have ab : a*b≤n := mulBound ha hb
    have cd : c*d≤n := mulBound hc hd
    change n-a*b = n-c*d at he
    obtain ⟨rfl,rfl⟩ := orderedFactors (posR ha) pb (posR hc) pd
      (Finset.mem_Ioc.mp hb).1 (Finset.mem_Ioc.mp hd).1 (by omega : a*b=c*d)
    rfl
  have count : (D \ B).card = ∑ r ∈ G, (V r).card := by
    rw [eqsets, Finset.card_image_of_injOn inj]
    exact Finset.card_sigma _ _
  have bad : B ⊆ n.primeFactors := by
    intro p hp
    obtain ⟨hd,r,hr,hrn,hw⟩ := memB.mp hp
    obtain ⟨v,_,_,eq⟩ := factors.mp hw
    have hsub : p=n-r*v := by omega
    have hdvd : r ∣ p := hsub ▸ Nat.dvd_sub hrn (dvd_mul_right r v)
    have hrp := (Nat.prime_dvd_prime_iff_eq (posR hr) (memD.mp hd).2.1).mp hdvd
    obtain ⟨h2,hle⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1
    exact Nat.mem_primeFactors.mpr ⟨(memD.mp hd).2.1, hrp ▸ hrn, by omega⟩
  refine ⟨?_, Finset.card_le_card bad⟩
  have split := Finset.sum_filter_add_sum_filter_not G (fun r => r^3≤n) (fun r => (V r).card)
  have low : G.filter (fun r => r^3≤n) = R.filter (fun r => ¬ r∣n ∧ r^3≤n) := by
    ext; simp [G, and_assoc]
  have high : G.filter (fun r => ¬ r^3≤n) = R.filter (fun r => ¬ r∣n ∧ n<r^3) := by
    ext; simp [G, and_assoc, not_le]
  rw [low,high] at split
  have total := Finset.card_sdiff_add_card_eq_card (show B ⊆ D from Finset.filter_subset _ _)
  change D.card = B.card + (∑ r ∈ R.filter (fun r => ¬ r∣n ∧ r^3≤n), (V r).card) + (∑ r ∈ R.filter (fun r => ¬ r∣n ∧ n<r^3), (V r).card)
  rw [← total, count, ← split]
  ac_rfl
