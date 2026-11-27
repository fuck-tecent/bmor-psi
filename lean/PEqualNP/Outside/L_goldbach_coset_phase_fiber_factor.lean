import Mathlib

open scoped Classical

private def bucket (x q r : ℕ) := (Finset.range (x+1)).filter (fun k => k % q=r)
private noncomputable def conv (x : ℕ) (a b : ℕ → ℂ) (s : ℕ) :=
  ∑ i ∈ (Finset.range (x+1)).filter (fun i => i ≤ s ∧ s-i ≤ x), a i*b (s-i)

private theorem expandConv (x s : ℕ) (a b : ℕ → ℂ) :
    conv x a b s = ∑ i ∈ Finset.range (x+1), ∑ j ∈ Finset.range (x+1),
      if i+j=s then a i*b j else 0 := by
  rw [conv, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases h : i ≤ s ∧ s-i ≤ x
  · rw [if_pos h,Finset.sum_eq_single (s-i)]
    · simp [Nat.add_sub_of_le h.1]
    · intro j _ hj; rw [if_neg (show i+j ≠ s by omega)]
    · intro hnot; exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  · rw [if_neg h]
    symm; apply Finset.sum_eq_zero
    intro j hj
    have := Finset.mem_range.mp hj
    rw [if_neg (show i+j ≠ s by omega)]

private theorem rearrange (x : ℕ) (S : Finset ℕ) (a b w : ℕ → ℂ) :
    (∑ s ∈ S, w s * conv x a b s) =
      ∑ i ∈ Finset.range (x+1), ∑ j ∈ Finset.range (x+1),
        if i+j ∈ S then w (i+j)*(a i*b j) else 0 := by
  simp_rw [expandConv,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq]

private theorem strideSum {M : Type} [AddCommMonoid M] (n q : ℕ) (hq : 0 < q) (f : ℕ → M) :
    (∑ s ∈ bucket (2*n) q (n % q), f s) =
      f n + ∑ h ∈ Finset.Icc 1 (n/q), (f (n+h*q) + f (n-h*q)) := by
  let I := bucket (2*n) q (n % q)
  let D := Finset.Icc 1 (n/q)
  let P := I.filter (n < ·)
  let N := I.filter (· < n)
  have hr {i : ℕ} (hi : i ∈ I) : i ≤ 2*n ∧ i ≡ n [MOD q] := by
    obtain ⟨hi,he⟩ := Finset.mem_filter.mp hi
    exact ⟨by have := Finset.mem_range.mp hi; omega, he⟩
  have he {h : ℕ} (hh : h ∈ D) : 0 < h*q ∧ h*q ≤ n := by
    obtain ⟨hp,hle⟩ := Finset.mem_Icc.mp hh
    exact ⟨Nat.mul_pos hp hq,(Nat.le_div_iff_mul_le hq).mp hle⟩
  have pairsPos : (∑ i ∈ P, f i) = ∑ h ∈ D, f (n+h*q) := by
    refine Finset.sum_bij' (fun i _ => (i-n)/q) (fun h _ => n+h*q) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      obtain ⟨hI,hgt⟩ := Finset.mem_filter.mp hi
      obtain ⟨hlt,hm⟩ := hr hI
      have hm' := (Nat.modEq_iff_dvd' hgt.le).mp hm.symm
      have hprod := Nat.div_mul_cancel hm'
      exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (Nat.sub_pos_of_lt hgt) hm') hq,
        Nat.div_le_div_right (by omega : i-n≤n)⟩
    · intro h hh
      obtain ⟨hp,hle⟩ := he hh
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by simp⟩,by omega⟩
    · intro i hi
      obtain ⟨hI,hgt⟩ := Finset.mem_filter.mp hi
      have hm := (Nat.modEq_iff_dvd' hgt.le).mp (hr hI).2.symm
      rw [Nat.div_mul_cancel hm]; omega
    · intro h _; simp [Nat.add_sub_cancel_left,Nat.mul_div_cancel _ hq]
    · intro i hi
      obtain ⟨hI,hgt⟩ := Finset.mem_filter.mp hi
      have hm := (Nat.modEq_iff_dvd' hgt.le).mp (hr hI).2.symm
      rw [Nat.div_mul_cancel hm]; congr 1; omega
  have pairsNeg : (∑ i ∈ N, f i) = ∑ h ∈ D, f (n-h*q) := by
    refine Finset.sum_bij' (fun i _ => (n-i)/q) (fun h _ => n-h*q) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      obtain ⟨hI,hlt⟩ := Finset.mem_filter.mp hi
      have hm := (Nat.modEq_iff_dvd' hlt.le).mp (hr hI).2
      have hprod := Nat.div_mul_cancel hm
      exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hm) hq,
        Nat.div_le_div_right (Nat.sub_le _ _)⟩
    · intro h hh
      obtain ⟨hp,hle⟩ := he hh
      have hm : n-h*q ≡ n [MOD q] := (Nat.modEq_iff_dvd' (Nat.sub_le _ _)).mpr (by
        rw [Nat.sub_sub_self hle]; exact dvd_mul_left _ _)
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hm⟩,by omega⟩
    · intro i hi
      obtain ⟨hI,hlt⟩ := Finset.mem_filter.mp hi
      rw [Nat.div_mul_cancel ((Nat.modEq_iff_dvd' hlt.le).mp (hr hI).2),Nat.sub_sub_self hlt.le]
    · intro h hh; rw [Nat.sub_sub_self (he hh).2,Nat.mul_div_cancel _ hq]
    · intro i hi
      obtain ⟨hI,hlt⟩ := Finset.mem_filter.mp hi
      rw [Nat.div_mul_cancel ((Nat.modEq_iff_dvd' hlt.le).mp (hr hI).2), Nat.sub_sub_self hlt.le]
  have Ieq : I = insert n (P ∪ N) := by
    ext i
    have hmem : n ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),rfl⟩
    simp only [Finset.mem_insert, Finset.mem_union,P,N,Finset.mem_filter]
    by_cases h : i=n
    · simpa [h] using hmem
    · constructor
      · intro hi; rcases lt_or_gt_of_ne h with hi'|hi' <;> tauto
      · rintro (rfl|⟨hi,_⟩|⟨hi,_⟩) <;> assumption
  change (∑ i ∈ I, _) = _
  rw [Ieq,Finset.sum_insert (by simp [P,N]),Finset.sum_union, pairsPos,pairsNeg,Finset.sum_add_distrib]
  exact Finset.disjoint_left.mpr (fun i hi hi' => lt_asymm (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hi').2)

private theorem diagonalBuckets (x q c : ℕ) (hq : 0 < q) (w a b : ℕ → ℂ) :
    (∑ s ∈ bucket (2*x) q c, w s * conv x a b s) =
    ∑ r ∈ Finset.range q, ∑ t ∈ Finset.range q,
      if (r+t) % q=c then ∑ i ∈ bucket x q r, ∑ j ∈ bucket x q t, w (i+j)*(a i*b j)
      else 0 := by
  rw [rearrange]
  let I := Finset.range (x+1)
  have regroup (f : ℕ → ℂ) :
      (∑ r ∈ Finset.range q, ∑ i ∈ bucket x q r, f i) = ∑ i ∈ I, f i :=
    Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_range.mpr (Nat.mod_lt i hq)) f
  change (∑ i ∈ I, _) = _
  rw [← regroup]
  apply Finset.sum_congr rfl
  intro r hr
  have inside (i : ℕ) (hi : i ∈ bucket x q r) :
      (∑ j ∈ I, if i+j ∈ bucket (2*x) q c then w (i+j)*(a i*b j) else 0) =
      ∑ t ∈ Finset.range q, ∑ j ∈ bucket x q t,
        (if (r+t) % q=c then w (i+j)*(a i*b j) else 0) := by
    rw [← regroup]
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hxi,hri⟩ := Finset.mem_filter.mp hi
    obtain ⟨hxj,htj⟩ := Finset.mem_filter.mp hj
    have hi' := Finset.mem_range.mp hxi
    have hj' := Finset.mem_range.mp hxj
    have hsum : i+j ∈ bucket (2*x) q c ↔ (r+t) % q=c := by
      simp only [bucket, Finset.mem_filter,Finset.mem_range]
      rw [Nat.add_mod,hri,htj]
      omega
    simp only [hsum]
  rw [Finset.sum_congr rfl inside, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> simp_all



private theorem complementIndex {q r t c : ℕ} (hr : r < q) (ht : t < q) (hc : c < q) :
    (r+t) % q=c ↔ t=(c % q+q-r) % q := by
  let u := (c % q+q-r) % q
  have hu : u < q := Nat.mod_lt _ (by omega)
  have he : (r+u) % q=c := by
    dsimp only [u]; rw [Nat.add_mod_mod, Nat.mod_eq_of_lt hc]
    rw [show r+(c+q-r) = c+q by omega,Nat.add_mod_right,Nat.mod_eq_of_lt hc]
  constructor
  · intro h
    have hm : t ≡ u [MOD q] := Nat.ModEq.add_left_cancel' r (h.trans he.symm)
    simpa only [Nat.ModEq,Nat.mod_eq_of_lt ht,Nat.mod_eq_of_lt hu] using hm
  · rintro rfl; exact he

theorem PEqualNP.Outside.L_goldbach_coset_phase_fiber_factor :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q=r); let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; let j := fun n q r : ℕ => (n+q-r) % q; let B := fun n s : ℕ => ∑ k ∈ (Finset.range (n+1)).filter (fun k => k ≤ s ∧ s-k ≤ n), w k*w (s-k); let Y := fun (n q : ℕ) (z : ℂ) => (B n n:ℂ) + ∑ h ∈ Finset.Icc 1 (n/q), ((B n (n+h*q):ℂ)*z^h + (B n (n-h*q):ℂ)*(z⁻¹)^h); ∀ (n q : ℕ) (u : ℂ), 0<q → u≠0 → u^n*Y n q (u^q) = ∑ r ∈ Finset.range q, (∑ k ∈ F n q r, (w k:ℂ)*u^k)*(∑ k ∈ F n q (j n q r), (w k:ℂ)*u^k) := by
  intro F w A jc B Y n q u hq hu
  let W := fun k : ℕ => (w k:ℂ)
  have Bcast (s : ℕ) : (B n s:ℂ) = conv n W W s := by simp [B,conv,W,Complex.ofReal_sum]
  have central : u^n*Y n q (u^q) = ∑ s ∈ bucket (2*n) q (n % q), u^s*(B n s:ℂ) := by
    rw [strideSum n q hq]
    dsimp only [Y]
    rw [mul_add,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro h hh
    have hle := (Nat.le_div_iff_mul_le hq).mp (Finset.mem_Icc.mp hh).2
    have hpos : u^n*(u^q)^h = u^(n+h*q) := by rw [← pow_mul,mul_comm q h,pow_add]
    have hneg : u^n*((u^q)⁻¹)^h = u^(n-h*q) := by
      rw [inv_pow,←pow_mul,mul_comm q h,← pow_sub₀ u hu hle]
    linear_combination (B n (n+h*q):ℂ)*hpos + (B n (n-h*q):ℂ)*hneg
  rw [central]
  simp_rw [Bcast]
  rw [diagonalBuckets n q (n % q) hq (fun k => u^k)]
  apply Finset.sum_congr rfl
  intro r hr
  let t := (n % q+q-r) % q
  have ht : t ∈ Finset.range q := Finset.mem_range.mpr (Nat.mod_lt _ hq)
  have hj : t = jc n q r := by
    dsimp only [t,jc]
    have hr' := Finset.mem_range.mp hr
    have eq : n+q-r = n+(q-r) := by omega
    have eq' : n % q+q-r=n % q+(q-r) := by omega
    rw [eq,eq',Nat.mod_add_mod]
  rw [Finset.sum_eq_single t]
  · have cond := (complementIndex (Finset.mem_range.mp hr) (Finset.mem_range.mp ht) (Nat.mod_lt n hq)).mpr (by simp [t])
    rw [if_pos cond]
    change _ = (∑ k ∈ bucket n q r, W k*u^k)*(∑ k ∈ bucket n q (jc n q r), W k*u^k)
    rw [←hj,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_add]; ring
  · intro j hj' hne; exact if_neg (mt (complementIndex (Finset.mem_range.mp hr) (Finset.mem_range.mp hj') (Nat.mod_lt n hq)).mp (by simpa [t] using hne))
  · intro h; exact (h ht).elim
