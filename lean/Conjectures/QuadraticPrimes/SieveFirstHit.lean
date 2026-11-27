import Mathlib

private lemma coprime_wheel_iff_minFac_gt
    {n z : ℕ} (hn : n ≠ 1) (hodd : Odd n) :
    Nat.Coprime n (∏ p ∈ (Finset.Icc 3 z).filter (fun p => Nat.Prime p), p) ↔
      z < n.minFac := by
  rw [Nat.coprime_prod_right_iff]
  constructor
  · intro h
    by_contra hz
    have hle : n.minFac ≤ z := Nat.le_of_not_gt hz
    have hminprime : Nat.Prime n.minFac := Nat.minFac_prime hn
    have hminodd : Odd n.minFac := hodd.of_dvd_nat (Nat.minFac_dvd n)
    have hmin3 : 3 ≤ n.minFac := hminprime.odd_iff.mp hminodd
    have hmem : n.minFac ∈ (Finset.Icc 3 z).filter (fun p => Nat.Prime p) := by
      simp [Finset.mem_Icc, hmin3, hle, hminprime]
    have hcop : Nat.Coprime n.minFac n := (h n.minFac hmem).symm
    exact (hminprime.coprime_iff_not_dvd.mp hcop) (Nat.minFac_dvd n)
  · intro hz p hp
    have hp' := Finset.mem_filter.mp hp
    have hpbounds := Finset.mem_Icc.mp hp'.1
    have hpprime : Nat.Prime p := hp'.2
    have hnotdvd : ¬p ∣ n := by
      intro hdiv
      have hminle : n.minFac ≤ p := Nat.minFac_le_of_dvd hpprime.two_le hdiv
      exact (not_lt_of_ge hminle) (lt_of_le_of_lt hpbounds.2 hz)
    exact (hpprime.coprime_iff_not_dvd.mpr hnotdvd).symm

private lemma f_odd (k : ℕ) : Odd (4 * k ^ 2 + 1) := by
  exact ⟨2 * k ^ 2, by ring⟩

private lemma card_filter_minFac_partition
    (s : Finset ℕ) (g : ℕ → ℕ) (lo hi : ℕ) (hlohi : lo ≤ hi) :
    (s.filter (fun k => lo < (g k).minFac)).card =
      (s.filter (fun k => hi < (g k).minFac)).card +
        (s.filter (fun k => lo < (g k).minFac ∧ (g k).minFac ≤ hi)).card := by
  let upper := s.filter (fun k => hi < (g k).minFac)
  let band := s.filter (fun k => lo < (g k).minFac ∧ (g k).minFac ≤ hi)
  have hpartition :
      s.filter (fun k => lo < (g k).minFac) = upper ∪ band := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_union, upper, band]
    constructor
    · intro hk
      by_cases hupper : hi < (g k).minFac
      · exact Or.inl ⟨hk.1, hupper⟩
      · exact Or.inr ⟨hk.1, hk.2, Nat.le_of_not_gt hupper⟩
    · rintro (⟨hks, hupper⟩ | ⟨hks, hlo, _⟩)
      · exact ⟨hks, lt_of_le_of_lt hlohi hupper⟩
      · exact ⟨hks, hlo⟩
  have hdisjoint : Disjoint upper band := by
    refine Finset.disjoint_left.mpr ?_
    intro k hkupper hkband
    have hupper : hi < (g k).minFac := (Finset.mem_filter.mp hkupper).2
    have hband : (g k).minFac ≤ hi := (Finset.mem_filter.mp hkband).2.2
    exact (not_lt_of_ge hband) hupper
  rw [hpartition, Finset.card_union_of_disjoint hdisjoint]

private lemma rough_eq_minFac_filter (x z : ℕ) :
    let f := fun k : ℕ => 4*k^2+1;
    let block := fun x : ℕ => Finset.Ioc (x/2) x;
    let primes := fun z : ℕ => (Finset.Icc 3 z).filter (fun p => Nat.Prime p);
    let wheel := fun z : ℕ => ∏ p ∈ primes z, p;
    (block x).filter (fun k => Nat.Coprime (f k) (wheel z)) =
      (block x).filter (fun k => z < (f k).minFac) := by
  dsimp only
  apply Finset.filter_congr
  intro k hk
  apply coprime_wheel_iff_minFac_gt
  · have hkpos : 0 < k := by
      have hk' := Finset.mem_Ioc.mp hk
      omega
    nlinarith
  · exact f_odd k

theorem Conjectures.QuadraticPrimes.SieveFirstHit :
    let f := fun k : ℕ => 4*k^2+1; let block := fun x : ℕ => Finset.Ioc (x/2) x; let primes := fun z : ℕ => (Finset.Icc 3 z).filter (fun p => Nat.Prime p); let wheel := fun z : ℕ => ∏ p ∈ primes z, p; let rough := fun x z : ℕ => (block x).filter (fun k => Nat.Coprime (f k) (wheel z)); ∀ x lo hi : ℕ, 0<x → lo≤hi →
      (rough x lo).card =
        (rough x hi).card + ((block x).filter (fun k => lo < (f k).minFac ∧ (f k).minFac ≤ hi)).card := by
  dsimp only
  intro x lo hi _hx hlohi
  have hlo := rough_eq_minFac_filter x lo
  have hhi := rough_eq_minFac_filter x hi
  rw [hlo, hhi]
  exact card_filter_minFac_partition _ _ _ _ hlohi
