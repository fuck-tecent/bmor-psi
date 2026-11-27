import Mathlib

private theorem shift_sum (B : ℕ → ℝ) (n q : ℕ) :
    (∑ s ∈ (Finset.range (2*n+1)).filter (fun s => s % q = n % q), B s) - B n =
      ∑ d ∈ Finset.Icc 1 n, if q ∣ d then B (n-d)+B (n+d) else 0 := by
  classical
  let D := (Finset.Icc 1 n).filter (fun d => q ∣ d)
  let L := D.image (fun d => n-d)
  let R := D.image (fun d => n+d)
  have hD {d : ℕ} : d ∈ D ↔ (1 ≤ d ∧ d ≤ n) ∧ q ∣ d := by
    simp [D]
  have hL {s : ℕ} : s ∈ L ↔ s < n ∧ s % q = n % q := by
    constructor
    · rintro hs
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨⟨hd₁, hd₂⟩, hdq⟩ := hD.mp hd
      refine ⟨by omega, (Nat.modEq_iff_dvd' (show n-d ≤ n by omega)).mpr ?_⟩
      simpa only [show n-(n-d)=d by omega] using hdq
    · rintro ⟨hlt, hmod⟩
      apply Finset.mem_image.mpr
      exact ⟨n-s, hD.mpr ⟨⟨by omega, by omega⟩, (Nat.modEq_iff_dvd' (by omega)).mp hmod⟩,
        by omega⟩
  have hR {s : ℕ} : s ∈ R ↔ (n < s ∧ s ≤ 2*n) ∧ s % q = n % q := by
    constructor
    · intro hs
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨⟨hd₁, hd₂⟩, hdq⟩ := hD.mp hd
      refine ⟨⟨by omega, by omega⟩, Eq.symm ((Nat.modEq_iff_dvd' (show n ≤ n+d by omega)).mpr ?_)⟩
      simpa using hdq
    · rintro ⟨⟨hlt, hle⟩, hmod⟩
      apply Finset.mem_image.mpr
      exact ⟨s-n, hD.mpr ⟨⟨by omega, by omega⟩, (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm⟩,
        by omega⟩
  have hset : (Finset.range (2*n+1)).filter (fun s => s % q = n % q) = insert n (L ∪ R) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_union, hL, hR]
    by_cases h : s=n
    · subst s
      simp
      omega
    · omega
  have hcenter : n ∉ L ∪ R := by simp [hL, hR]
  have hdis : Disjoint L R := Finset.disjoint_left.mpr fun s hl hr =>
    (Nat.lt_asymm (hL.mp hl).1 (hR.mp hr).1.1)
  have sumL : (∑ s ∈ L, B s) = ∑ d ∈ D, B (n-d) := by
    apply Finset.sum_image
    intro a ha b hb hab
    have ha' := (hD.mp ha).1.2
    have hb' := (hD.mp hb).1.2
    dsimp at hab
    omega
  have sumR : (∑ s ∈ R, B s) = ∑ d ∈ D, B (n+d) := by
    apply Finset.sum_image
    intro a _ b _ hab
    exact Nat.add_left_cancel hab
  rw [hset, Finset.sum_insert hcenter, Finset.sum_union hdis, sumL, sumR, ← Finset.sum_add_distrib]
  simp only [add_sub_cancel_left]
  exact Finset.sum_filter _ _

theorem PEqualNP.Outside.L_goldbach_coset_block_shift_transform :
    let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let B := fun n s : ℕ => ∑ k ∈ (Finset.range (n+1)).filter (fun k => k ≤ s ∧ s-k ≤ n), w k*w (s-k); let Z := fun n q : ℕ => ∑ s ∈ (Finset.range (2*n+1)).filter (fun s => s % q = n % q), B n s; ∀ n Q : ℕ, 0<Q → (∑ q ∈ Finset.Ioc Q (2*Q), (q:ℝ)*(Z n q-B n n)) = ∑ d ∈ Finset.Icc 1 n, (B n (n-d)+B n (n+d))*(d:ℝ)*(∑ h ∈ d.divisors.filter (fun h => Q*h<d ∧ d≤2*Q*h), 1/(h:ℝ)) := by
  intro w B Z n Q _
  have switch (d Q : ℕ) (hd : 0 < d) :
      (∑ q ∈ (Finset.Ioc Q (2*Q)).filter (fun q => q∣d), (q:ℝ)) =
      (d:ℝ)* ∑ h ∈ d.divisors.filter (fun h => Q*h<d ∧ d≤2*Q*h), 1/(h:ℝ) := by
    let weight (q : ℕ) : ℝ := if Q < q ∧ q ≤ 2*Q then q else 0
    have hblock : (Finset.Ioc Q (2*Q)).filter (fun q => q ∣ d) =
        d.divisors.filter (fun q => Q < q ∧ q ≤ 2*Q) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors]
      exact ⟨fun ⟨hI, hq⟩ => ⟨⟨hq, Nat.ne_of_gt hd⟩, hI⟩,
        fun ⟨⟨hq, _⟩, hI⟩ => ⟨hI, hq⟩⟩
    rw [hblock]
    calc
      _ = ∑ q ∈ d.divisors, weight q := by rw [Finset.sum_filter]
      _ = ∑ h ∈ d.divisors, weight (d/h) := (Nat.sum_div_divisors d weight).symm
      _ = _ := by
        rw [Finset.sum_filter, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h hh
        have hpos := Nat.pos_of_mem_divisors hh
        have hprod := Nat.div_mul_cancel (Nat.mem_divisors.mp hh).1
        have hswitch : (Q < d / h ∧ d / h ≤ 2*Q) ↔ (Q*h < d ∧ d ≤ 2*Q*h) := by
          rw [← hprod, Nat.mul_div_cancel _ hpos, mul_lt_mul_iff_of_pos_right hpos,
            mul_le_mul_iff_of_pos_right hpos]
        dsimp only [weight]
        by_cases hI : Q*h < d ∧ d ≤ 2*Q*h
        · rw [ite_eq_left (hswitch.mpr hI), ite_eq_left hI, mul_one_div,
            eq_div_iff (by exact_mod_cast hpos.ne')]
          exact_mod_cast hprod
        · simp [hI, mt hswitch.mp hI]
  let A (d : ℕ) : ℝ := B n (n-d) + B n (n+d)
  have shares (q : ℕ) : Z n q - B n n =
      ∑ d ∈ Finset.Icc 1 n, if q ∣ d then A d else 0 := by
    exact shift_sum (B n) n q
  calc
    _ = ∑ q ∈ Finset.Ioc Q (2*Q), ∑ d ∈ Finset.Icc 1 n,
          (if q ∣ d then (q : ℝ) else 0) * A d := by
      apply Finset.sum_congr rfl
      intro q _
      rw [shares, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : q ∣ d <;> simp [hd]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      rw [← Finset.sum_mul, ← Finset.sum_filter, switch d Q hdpos]
      dsimp only [A]
      ring
