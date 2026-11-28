import Mathlib

private theorem squareLiftOrdered {a b : ℕ} (ha : 0 < a) (hab : a < b) (cop : a.Coprime b) :
    ∃ u v : ℕ, 0 < u ∧ u < v ∧ u.Coprime v ∧ (a+b)^2 ≤ 4*v^2 ∧
      (u^2*(v^2-u^2)*v^2).primeFactors.prod id ≤
        4*(a+b)*(a*b*(a+b)).primeFactors.prod id := by
  let d := b-a
  let c := a+b
  let g := Nat.gcd d c
  let u := d/g
  let v := c/g
  have hd : 0 < d := Nat.sub_pos_of_lt hab
  have hc : 0 < c := by dsimp [c]; omega
  have hdc : d < c := by dsimp [c,d]; omega
  have hg : 0 < g := Nat.gcd_pos_of_pos_left c hd
  have hgd : g ∣ d := Nat.gcd_dvd_left d c
  have hgc : g ∣ c := Nat.gcd_dvd_right d c
  have hgu : g*u=d := Nat.mul_div_cancel' hgd
  have hgv : g*v=c := Nat.mul_div_cancel' hgc
  have hud : u ∣ d := ⟨g,by simpa [mul_comm] using hgu.symm⟩
  have hvc : v ∣ c := ⟨g,by simpa [mul_comm] using hgv.symm⟩
  have hu : 0 < u := by
    apply Nat.pos_of_ne_zero
    intro hu0
    apply hd.ne'
    calc
      d = g*u := hgu.symm
      _ = 0 := by rw [hu0,mul_zero]
  have huv : u < v := by
    apply Nat.lt_of_mul_lt_mul_left (a:=g)
    simpa [hgu,hgv] using hdc
  have hcop : u.Coprime v := Nat.coprime_div_gcd_div_gcd hg
  have htwoA : g ∣ 2*a := by
    have eq : c-d=2*a := by dsimp [c,d]; omega
    rw [← eq]; exact Nat.dvd_sub hgc hgd
  have htwoB : g ∣ 2*b := by
    have eq : c+d=2*b := by dsimp [c,d]; omega
    rw [← eq]; exact Nat.dvd_add hgc hgd
  have hg2 : g ∣ 2 := by
    have h := Nat.dvd_gcd htwoA htwoB
    simpa [Nat.gcd_mul_left,cop.gcd_eq_one] using h
  have hgLe : g ≤ 2 := Nat.le_of_dvd (by decide) hg2
  have hG2 : g^2 ≤ 4 := by simpa using (Nat.pow_le_pow_left hgLe 2)
  have hd2 : g^2*u^2 = d^2 := by rw [← mul_pow,hgu]
  have hc2 : g^2*v^2 = c^2 := by rw [← mul_pow,hgv]
  have hexc : g^2*(v^2-u^2) = 4*a*b := by
    have hVU : u^2 ≤ v^2 := Nat.pow_le_pow_left huv.le 2
    have hSum : g^2*(v^2-u^2)+d^2 = c^2 := by
      rw [← hd2,← Nat.mul_add,Nat.sub_add_cancel hVU,hc2]
    have hGeom : c^2 = d^2 + 4*a*b := by
      have hb : b=a+d := by dsimp [d]; omega
      have hC : c=a+b := rfl
      rw [hC,hb]; ring
    omega
  let r := (a*b*c).primeFactors.prod id
  have hr : 0 < r := Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  have hprod : 0 < a*b*c := Nat.mul_pos (Nat.mul_pos ha (ha.trans hab)) hc
  have htarget : 0 < 4*d*r := Nat.mul_pos (Nat.mul_pos (by decide) hd) hr
  have hRad : (u^2*(v^2-u^2)*v^2).primeFactors.prod id ∣ 4*d*r := by
    apply (Nat.prod_primeFactors_dvd_iff htarget.ne').2
    intro p hp
    obtain ⟨hpp,hDvd,_⟩ := Nat.mem_primeFactors.mp hp
    refine Nat.mem_primeFactors.mpr ⟨hpp,?_,htarget.ne'⟩
    have fromRad (h : p ∣ a*b*c) : p ∣ 4*d*r := by
      have hpMem : p ∈ (a*b*c).primeFactors := Nat.mem_primeFactors.mpr ⟨hpp,h,hprod.ne'⟩
      have hpR : p ∣ r := Finset.dvd_prod_of_mem id hpMem
      exact dvd_trans hpR (dvd_mul_left r (4*d))
    have fromD (h : p ∣ d) : p ∣ 4*d*r :=
      dvd_trans (dvd_trans h (dvd_mul_left d 4)) (dvd_mul_right (4*d) r)
    have from4 (h : p ∣ 4) : p ∣ 4*d*r :=
      dvd_trans (dvd_trans h (dvd_mul_right 4 d)) (dvd_mul_right (4*d) r)
    rcases hpp.dvd_mul.mp hDvd with hLeft | hLast
    · rcases hpp.dvd_mul.mp hLeft with hFirst | hMiddle
      · exact fromD (dvd_trans (hpp.dvd_of_dvd_pow hFirst) hud)
      · have hTotal : p ∣ 4*a*b := by
          rw [← hexc]; exact dvd_trans hMiddle (dvd_mul_left _ _)
        rw [mul_assoc] at hTotal
        rcases hpp.dvd_mul.mp hTotal with h4 | habD
        · exact from4 h4
        · exact fromRad (dvd_trans habD (dvd_mul_right (a*b) c))
    · have hpC : p ∣ c := dvd_trans (hpp.dvd_of_dvd_pow hLast) hvc
      exact fromRad (dvd_trans hpC (dvd_mul_left c (a*b)))
  refine ⟨u,v,hu,huv,hcop,?_,?_⟩
  · change c^2 ≤ 4*v^2
    rw [← hc2]
    exact Nat.mul_le_mul_right _ hG2
  · exact (Nat.le_of_dvd htarget hRad).trans (Nat.mul_le_mul_right r (Nat.mul_le_mul_left 4 hdc.le))

theorem Conjectures.Cuts.Task7ed0b9c0917aa6adbbd74ec1 :
    (have x1 : ℕ → ℕ := fun (x1 : ℕ) => x1.primeFactors.prod id; ∀ (x2 x3 : ℕ), (0 : ℕ) < x2 → (0 : ℕ) < x3 → x2.Coprime x3 → x2 ≠ x3 → ∃ (x8 : ℕ) (x9 : ℕ), (0 : ℕ) < x8 ∧ x8 < x9 ∧ x8.Coprime x9 ∧ (x2 + x3) ^ (2 : ℕ) ≤ (4 : ℕ) * x9 ^ (2 : ℕ) ∧ x1 (x8 ^ (2 : ℕ) * (x9 ^ (2 : ℕ) - x8 ^ (2 : ℕ)) * x9 ^ (2 : ℕ)) ≤ (4 : ℕ) * (x2 + x3) * x1 (x2 * x3 * (x2 + x3))) := by
  classical
  dsimp only
  intro a b ha hb hCop hab
  rcases lt_or_gt_of_ne hab with hl | hg
  · exact squareLiftOrdered ha hl hCop
  · have sw := squareLiftOrdered hb hg hCop.symm
    simpa only [add_comm b a, mul_comm b a] using sw
