import Mathlib

theorem Conjectures.Cuts.Task3ff39db98df0e787e22fdced :
(∀ (x1 : ℕ),   Nat.Prime x1 →     ∀ (x3 x4 : ZMod x1) (x5 : Fin (4 : ℕ) → ZMod x1),       Function.Injective x5 →         ∀ (x7 : Finset (Fin x1 × Fin (4 : ℕ))),           have x8 : Fin x1 × Fin (4 : ℕ) → ZMod x1 := fun (x8 : Fin x1 × Fin (4 : ℕ)) => (↑(↑x8.1 : ℕ) : ZMod x1);           have x9 : Fin x1 × Fin (4 : ℕ) → ZMod x1 := fun (x9 : Fin x1 × Fin (4 : ℕ)) => x3 * x8 x9 ^ (2 : ℕ) + x4 * x8 x9 + x5 x9.2;           have x10 : Fin x1 × Fin (4 : ℕ) → ℕ × ℕ := fun (x10 : Fin x1 × Fin (4 : ℕ)) => ((↑x10.1 : ℕ), (x9 x10).val);           have x11 : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ → Prop := fun (x11 x12 x13 : ℕ × ℕ) => ((↑x12.1 : ℤ) - (↑x11.1 : ℤ)) * ((↑x13.2 : ℤ) - (↑x11.2 : ℤ)) = ((↑x12.2 : ℤ) - (↑x11.2 : ℤ)) * ((↑x13.1 : ℤ) - (↑x11.1 : ℤ));           have x12 : Fin x1 × Fin (4 : ℕ) → Fin x1 × Fin (4 : ℕ) → Fin x1 × Fin (4 : ℕ) → Prop := fun (x12 x13 x14 : Fin x1 × Fin (4 : ℕ)) =>             if x12.1 = x13.1 then x14.1 = x12.1             else               have x15 : ZMod x1 := (x9 x13 - x9 x12) * (x8 x13 - x8 x12)⁻¹;               have x16 : ZMod x1 := x9 x12 - x15 * x8 x12;               ((2 : ZMod x1) * x3 * x8 x14 + x4 - x15) ^ (2 : ℕ) = (x4 - x15) ^ (2 : ℕ) - (4 : ZMod x1) * x3 * (x5 x14.2 - x16);           (∀ (x13 x14 x15 : Fin x1 × Fin (4 : ℕ)), x13 ≠ x14 → x13 ≠ x15 → x14 ≠ x15 → x12 x13 x14 x15 → x11 (x10 x13) (x10 x14) (x10 x15) → x13 ∈ x7 ∨ x14 ∈ x7 ∨ x15 ∈ x7) →             have x14 : Finset (ℕ × ℕ) := Finset.image x10 (Finset.univ \ x7);             ((∀ x15 ∈ x14, x15.1 < x1 ∧ x15.2 < x1) ∧ ∀ x15 ∈ x14, ∀ x17 ∈ x14, ∀ x19 ∈ x14, x15 ≠ x17 → x15 ≠ x19 → x17 ≠ x19 → ¬x11 x15 x17 x19) ∧ x14.card + x7.card = (4 : ℕ) * x1) := by
  intro p hp A b L hL D X Y pt col shadow hHit S
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let x := X
  let y := Y
  let g := pt
  have xinj (i j : Fin p × Fin 4) (h : x i = x j) : i.1 = j.1 := by
    apply Fin.ext
    have r := congrArg ZMod.val h
    change (i.1.val : ZMod p).val = (j.1.val : ZMod p).val at r
    simpa only [ZMod.val_natCast_of_lt i.1.isLt,ZMod.val_natCast_of_lt j.1.isLt] using r
  have gx (i : Fin p × Fin 4) : ((g i).1 : ZMod p) = x i := rfl
  have gy (i : Fin p × Fin 4) : ((g i).2 : ZMod p) = y i := ZMod.natCast_zmod_val _
  have inj : Function.Injective g := by
    intro i j h
    have e : i.1 = j.1 := Fin.ext (congrArg Prod.fst h)
    have eX : x i = x j := congrArg (fun r : Fin p => (r.val : ZMod p)) e
    have eqY := congrArg (fun z : ℕ × ℕ => (z.2 : ZMod p)) h
    change ((g i).2 : ZMod p) = (g j).2 at eqY
    rw [gy,gy] at eqY
    change A * (x i)^2 + b*x i + L i.2 = A*(x j)^2 + b*x j + L j.2 at eqY
    rw [eX] at eqY
    exact Prod.ext e (hL (add_left_cancel eqY))
  have covers (i j k : Fin p × Fin 4) (hij : i ≠ j) (hc : col (g i) (g j) (g k)) :
      shadow i j k := by
    change (((g j).1 : ℤ) - (g i).1) * (((g k).2 : ℤ) - (g i).2) =
      (((g j).2 : ℤ) - (g i).2) * (((g k).1 : ℤ) - (g i).1) at hc
    have fieldEq := congrArg (fun z : ℤ => (z : ZMod p)) hc
    change (_ : ZMod p) = _ at fieldEq
    simp only [Int.cast_mul,Int.cast_sub,Int.cast_natCast,gx,gy] at fieldEq
    by_cases eq : i.1 = j.1
    · have eX : x i = x j := congrArg (fun r : Fin p => (r.val : ZMod p)) eq
      have eY : y j - y i ≠ 0 := by
        intro zero
        have eqY : y i = y j := (sub_eq_zero.mp zero).symm
        apply hij
        apply inj
        exact Prod.ext (congrArg Fin.val eq) (congrArg ZMod.val eqY)
      rw [← eX,sub_self,zero_mul] at fieldEq
      have ek := (mul_eq_zero.mp fieldEq.symm).resolve_left eY
      simpa [shadow,eq] using xinj k i (sub_eq_zero.mp ek)
    · have den : x j - x i ≠ 0 := fun h => eq (xinj j i (sub_eq_zero.mp h)).symm
      let m := (y j-y i)*(x j-x i)⁻¹
      have slope : m*(x j-x i) = y j-y i := by
        dsimp only [m]
        rw [mul_assoc,inv_mul_cancel₀ den,mul_one]
      have fac : (x j-x i)*(y k-y i-m*(x k-x i)) = 0 := by
        calc
          _ = (y j-y i-m*(x j-x i))*(x k-x i) := by linear_combination fieldEq
          _ = 0 := by rw [slope,sub_self,zero_mul]
      have line := (mul_eq_zero.mp fac).resolve_left den
      change A*(x k)^2 + b*x k + L k.2 - y i - m*(x k-x i) = 0 at line
      have discriminant :
          (2*A*x k + b-m)^2 = (b-m)^2 - 4*A*(L k.2-(y i-m*x i)) := by
        linear_combination 4*A*line
      simpa [shadow,eq] using discriminant
  constructor
  · constructor
    · intro z hz
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
      exact ⟨i.1.isLt,ZMod.val_lt _⟩
    · intro v hv w hw u hu hvw hvu hwu det
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hu
      have ij : i ≠ j := fun h => hvw (congrArg g h)
      have ik : i ≠ k := fun h => hvu (congrArg g h)
      have jk : j ≠ k := fun h => hwu (congrArg g h)
      rcases hHit i j k ij ik jk (covers i j k ij det) det with e|e|e
      · exact (Finset.mem_sdiff.mp hi).2 e
      · exact (Finset.mem_sdiff.mp hj).2 e
      · exact (Finset.mem_sdiff.mp hk).2 e
  · change ((Finset.univ \ D).image g).card + D.card = 4*p
    rw [Finset.card_image_of_injective _ inj,Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)]
    simp [Nat.mul_comm]
