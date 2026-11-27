import Mathlib

/-!
# PREPUB goldbach: `L-goldbach-farey-late-first-hit-factor-switch`

On the Farey middle third, a survivor with rough `minFac(u(n-u)) ∈ (n^{1/3}, √n]` has its
rough prime dividing exactly one of `u` and `n-u`; writing the surviving half as `p * q`
with `p` prime and `q` prime (the second factor is forced to be prime because three
factors `≥ p > n^{1/3}` would exceed `n`), the survivors biject with the pairs counted by
the right-hand side.  Self-contained, Mathlib only.
-/

open scoped BigOperators
open Finset

namespace PEqualNP.Outside

/-- Middle-third size bounds. -/
private lemma mid_bounds {n u : ℕ} (hn : 64 ≤ n)
    (hu : u ∈ Finset.Icc ((n+2)/3) ((2*n)/3)) :
    22 ≤ u ∧ u < n ∧ 22 ≤ n - u ∧ n - u < n := by
  obtain ⟨hu1, hu2⟩ := Finset.mem_Icc.mp hu
  have h3u : n ≤ 3*u := by
    have h := (Nat.div_le_iff_le_mul_add_pred (by norm_num : 0 < 3)).mp hu1
    omega
  have h3u' : 3*u ≤ 2*n := by
    have h := (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).mp hu2
    omega
  omega

/-- The middle third is symmetric under `u ↦ n - u`. -/
private lemma mid_symm {n u : ℕ} (hn : 64 ≤ n)
    (hu : u ∈ Finset.Icc ((n+2)/3) ((2*n)/3)) :
    n - u ∈ Finset.Icc ((n+2)/3) ((2*n)/3) := by
  obtain ⟨hu1, hu2⟩ := Finset.mem_Icc.mp hu
  have h3u : n ≤ 3*u := by
    have h := (Nat.div_le_iff_le_mul_add_pred (by norm_num : 0 < 3)).mp hu1
    omega
  have h3u' : 3*u ≤ 2*n := by
    have h := (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).mp hu2
    omega
  rw [Finset.mem_Icc]
  constructor
  · rw [Nat.div_le_iff_le_mul_add_pred (by norm_num : 0 < 3)]
    omega
  · rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 3)]
    omega

/-- `u(n-u)` is at least `22·22`. -/
private lemma prod_ge {n u : ℕ} (hn : 64 ≤ n)
    (hu : u ∈ Finset.Icc ((n+2)/3) ((2*n)/3)) : 22 ≤ u*(n-u) := by
  have hb := mid_bounds hn hu
  have h : 22*22 ≤ u*(n-u) := Nat.mul_le_mul hb.1 hb.2.2.1
  omega

/-- `minFac(u(n-u))` is prime. -/
private lemma Fprime {n u : ℕ} (hn : 64 ≤ n)
    (hu : u ∈ Finset.Icc ((n+2)/3) ((2*n)/3)) : Nat.Prime ((u*(n-u)).minFac) := by
  have h := prod_ge hn hu
  exact Nat.minFac_prime (by omega : u*(n-u) ≠ 1)

/-- `minFac(u(n-u))` divides one of the two factors. -/
private lemma Fdvd_or {n u : ℕ} (hn : 64 ≤ n)
    (hu : u ∈ Finset.Icc ((n+2)/3) ((2*n)/3)) :
    (u*(n-u)).minFac ∣ u ∨ (u*(n-u)).minFac ∣ (n-u) := by
  have hp := Fprime hn hu
  have hd : (u*(n-u)).minFac ∣ u*(n-u) := Nat.minFac_dvd _
  exact (Nat.Prime.dvd_mul hp).mp hd

/-- Any divisor `> 1` of `u` is at least `minFac(u(n-u))`. -/
private lemma F_le_left {n u d : ℕ} (hn : 64 ≤ n)
    (hu : u ∈ Finset.Icc ((n+2)/3) ((2*n)/3)) (hdvd : d ∣ u) (hd : 1 < d) :
    (u*(n-u)).minFac ≤ d := by
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
  have hpdvd : p ∣ u*(n-u) := dvd_mul_of_dvd_left (dvd_trans hpd hdvd) _
  have h1 : (u*(n-u)).minFac ≤ p := Nat.minFac_le_of_dvd hp.two_le hpdvd
  have h2 : p ≤ d := Nat.le_of_dvd (by omega) hpd
  omega

/-- Any divisor `> 1` of `n - u` is at least `minFac(u(n-u))`. -/
private lemma F_le_right {n u d : ℕ} (hn : 64 ≤ n)
    (hu : u ∈ Finset.Icc ((n+2)/3) ((2*n)/3)) (hdvd : d ∣ n-u) (hd : 1 < d) :
    (u*(n-u)).minFac ≤ d := by
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
  have hpdvd : p ∣ u*(n-u) := dvd_mul_of_dvd_right (dvd_trans hpd hdvd) _
  have h1 : (u*(n-u)).minFac ≤ p := Nat.minFac_le_of_dvd hp.two_le hpdvd
  have h2 : p ≤ d := Nat.le_of_dvd (by omega) hpd
  omega

/-- If `minFac(u(n-u))` divides `u`, then it is `minFac u`. -/
private lemma minFac_eq_left {n u : ℕ} (hn : 64 ≤ n)
    (hu : u ∈ Finset.Icc ((n+2)/3) ((2*n)/3))
    (hdvd : (u*(n-u)).minFac ∣ u) : Nat.minFac u = (u*(n-u)).minFac := by
  have hb := mid_bounds hn hu
  have hF := Fprime hn hu
  have hup : Nat.Prime (Nat.minFac u) := Nat.minFac_prime (by omega : u ≠ 1)
  have hmu_dvd : Nat.minFac u ∣ u*(n-u) := dvd_mul_of_dvd_left (Nat.minFac_dvd u) _
  have h1 : (u*(n-u)).minFac ≤ Nat.minFac u := Nat.minFac_le_of_dvd hup.two_le hmu_dvd
  have h2 : Nat.minFac u ≤ (u*(n-u)).minFac := Nat.minFac_le_of_dvd hF.two_le hdvd
  exact le_antisymm h2 h1

/-- If `minFac(u(n-u))` divides `n - u`, then it is `minFac (n-u)`. -/
private lemma minFac_eq_right {n u : ℕ} (hn : 64 ≤ n)
    (hu : u ∈ Finset.Icc ((n+2)/3) ((2*n)/3))
    (hdvd : (u*(n-u)).minFac ∣ n-u) : Nat.minFac (n-u) = (u*(n-u)).minFac := by
  have hb := mid_bounds hn hu
  have hF := Fprime hn hu
  have hvp : Nat.Prime (Nat.minFac (n-u)) := Nat.minFac_prime (by omega : n-u ≠ 1)
  have hmv_dvd : Nat.minFac (n-u) ∣ u*(n-u) := dvd_mul_of_dvd_right (Nat.minFac_dvd (n-u)) _
  have h1 : (u*(n-u)).minFac ≤ Nat.minFac (n-u) := Nat.minFac_le_of_dvd hvp.two_le hmv_dvd
  have h2 : Nat.minFac (n-u) ≤ (u*(n-u)).minFac := Nat.minFac_le_of_dvd hF.two_le hdvd
  exact le_antisymm h2 h1

/-- Under the hit conditions, `u` has essentially two prime factors: if `F = minFac(u(n-u))`
divides `u` then `u = F * q` with `q` prime and `q ≥ F`. -/
private lemma semiprime_left {n u : ℕ} (hn : 64 ≤ n)
    (hu : u ∈ Finset.Icc ((n+2)/3) ((2*n)/3))
    (hdvd : (u*(n-u)).minFac ∣ u)
    (hgt : n < ((u*(n-u)).minFac)^3) (hle : ((u*(n-u)).minFac)^2 ≤ n) :
    ∃ q : ℕ, q.Prime ∧ u = (u*(n-u)).minFac * q ∧ (u*(n-u)).minFac ≤ q := by
  set F := (u*(n-u)).minFac with hFdef
  have hb := mid_bounds hn hu
  have hFp : F.Prime := Fprime hn hu
  have hFpos : 0 < F := hFp.pos
  have hu_eq : u = F * (u / F) := (Nat.mul_div_cancel' hdvd).symm
  set q := u / F with hqdef
  have hq_dvd : q ∣ u := Nat.div_dvd_of_dvd hdvd
  have hq_pos : 0 < q := by
    have hFu : F ≤ u := Nat.le_of_dvd (by omega) hdvd
    rw [hqdef]
    exact Nat.div_pos hFu hFpos
  -- q = 1 forces u = F, impossible since F^2 ≤ n but F ≥ 22
  have hq_ne_one : q ≠ 1 := by
    intro h1
    have huF : u = F := by rw [hu_eq, h1, mul_one]
    have h22 : 22 ≤ F := by omega
    have h3u : n ≤ 3*u := by
      obtain ⟨hu1, _⟩ := Finset.mem_Icc.mp hu
      have h := (Nat.div_le_iff_le_mul_add_pred (by norm_num : 0 < 3)).mp hu1
      omega
    have hF3 : F ≤ 3 := by
      have h' : F*F ≤ 3*F := by
        have hFF : F*F = F^2 := by ring
        omega
      exact Nat.le_of_mul_le_mul_right h' hFpos
    omega
  have hq2 : 2 ≤ q := by omega
  have hq_prime : q.Prime := by
    by_contra hnp
    obtain ⟨d, hdq, hd2, hdlt⟩ := (Nat.not_prime_iff_exists_dvd_lt hq2).mp hnp
    have hdu : d ∣ u := dvd_trans hdq hq_dvd
    have hd_ge : F ≤ d := F_le_left hn hu hdu (by omega)
    have hqd2 : 2 ≤ q / d := by
      rw [Nat.le_div_iff_mul_le (by omega : 0 < d)]
      obtain ⟨k, hk⟩ := hdq
      rw [hk] at hdlt ⊢
      rcases k with _ | _ | k
      · simp at hdlt
      · simp at hdlt
      · calc 2*d ≤ (k+2)*d := Nat.mul_le_mul_right d (by omega)
          _ = d*(k+2) := Nat.mul_comm _ _
    have hqdiv_dvd : q / d ∣ u := dvd_trans (Nat.div_dvd_of_dvd hdq) hq_dvd
    have hqd_ge : F ≤ q / d := F_le_left hn hu hqdiv_dvd (by omega)
    have hq_eq : q = d * (q / d) := (Nat.mul_div_cancel' hdq).symm
    have hu_ge : F^3 ≤ u := by
      rw [hu_eq, hq_eq]
      have h1 : F * (F * F) ≤ F * (d * (q / d)) := by
        apply Nat.mul_le_mul_left
        exact Nat.mul_le_mul hd_ge hqd_ge
      have h2 : F^3 = F * (F * F) := by ring
      omega
    omega
  have hFq : F ≤ q := F_le_left hn hu hq_dvd (by omega)
  exact ⟨q, hq_prime, hu_eq, hFq⟩

/-- Same statement with `n - u` in place of `u`. -/
private lemma semiprime_right {n u : ℕ} (hn : 64 ≤ n)
    (hu : u ∈ Finset.Icc ((n+2)/3) ((2*n)/3))
    (hdvd : (u*(n-u)).minFac ∣ n-u)
    (hgt : n < ((u*(n-u)).minFac)^3) (hle : ((u*(n-u)).minFac)^2 ≤ n) :
    ∃ q : ℕ, q.Prime ∧ n-u = (u*(n-u)).minFac * q ∧ (u*(n-u)).minFac ≤ q := by
  have hvI := mid_symm hn hu
  have hb := mid_bounds hn hu
  have hF_eq : (((n-u)*(n-(n-u))).minFac) = ((u*(n-u)).minFac) := by
    have hnv : n - (n-u) = u := by omega
    rw [hnv, Nat.mul_comm]
  have hdvd' : ((n-u)*(n-(n-u))).minFac ∣ (n-u) := by rw [hF_eq]; exact hdvd
  have hgt' : n < (((n-u)*(n-(n-u))).minFac)^3 := by rw [hF_eq]; exact hgt
  have hle' : (((n-u)*(n-(n-u))).minFac)^2 ≤ n := by rw [hF_eq]; exact hle
  obtain ⟨q, hqp, hvq, hFq⟩ := semiprime_left hn hvI hdvd' hgt' hle'
  rw [hF_eq] at hvq hFq
  exact ⟨q, hqp, hvq, hFq⟩

/-- Key arithmetic: for a semiprime `p*q ∈ I` with `p ≤ q`, `p ≤ minFac(n-p*q)`, the
rough prime `minFac((p*q)(n-p*q))` is exactly `p`. -/
private lemma minFac_prod_pq {n p q : ℕ} (hn : 64 ≤ n)
    (hpp : p.Prime) (hqp : q.Prime) (hpq : p ≤ q)
    (hI : p*q ∈ Finset.Icc ((n+2)/3) ((2*n)/3))
    (hmin : p ≤ (n - p*q).minFac) :
    ((p*q)*(n - p*q)).minFac = p := by
  have hb := mid_bounds hn hI
  have hprod22 : 22*22 ≤ (p*q)*(n - p*q) := Nat.mul_le_mul hb.1 hb.2.2.1
  have hw1 : (p*q)*(n - p*q) ≠ 1 := by omega
  have hFp : ((p*q)*(n - p*q)).minFac.Prime := Nat.minFac_prime hw1
  have hFdvd : ((p*q)*(n - p*q)).minFac ∣ (p*q)*(n - p*q) := Nat.minFac_dvd _
  have hdvd_p : p ∣ (p*q)*(n - p*q) := dvd_mul_of_dvd_left (dvd_mul_right p q) _
  have hle : ((p*q)*(n - p*q)).minFac ≤ p := Nat.minFac_le_of_dvd hpp.two_le hdvd_p
  have hge : p ≤ ((p*q)*(n - p*q)).minFac := by
    by_contra hcon
    have hlt : ((p*q)*(n - p*q)).minFac < p := lt_of_not_ge hcon
    rcases (Nat.Prime.dvd_mul hFp).mp hFdvd with h | h
    · rcases (Nat.Prime.dvd_mul hFp).mp h with h' | h'
      · rcases (Nat.dvd_prime hpp).mp h' with h1 | h1
        · exact hFp.ne_one h1
        · omega
      · rcases (Nat.dvd_prime hqp).mp h' with h1 | h1
        · exact hFp.ne_one h1
        · omega
    · have h2 : (n - p*q).minFac ≤ ((p*q)*(n - p*q)).minFac :=
        Nat.minFac_le_of_dvd hFp.two_le h
      omega
  exact le_antisymm hle hge

/-- `mark` flips `1` to `n-1` on `u ↦ n-u`. -/
private lemma mark_neg {n u : ℕ} (hn : 64 ≤ n) (hu : u ≤ n) {J : Finset ℕ}
    (h : (J.filter (fun a => (a*u)%n = 1)).Nonempty) :
    (J.filter (fun a => (a*(n-u))%n = n-1)).Nonempty := by
  obtain ⟨a, ha⟩ := h
  rw [Finset.mem_filter] at ha
  obtain ⟨haJ, hamod⟩ := ha
  refine ⟨a, ?_⟩
  rw [Finset.mem_filter]
  refine ⟨haJ, ?_⟩
  have h2 : ((a*u : ℕ) : ZMod n) = ((1:ℕ) : ZMod n) := by
    rw [ZMod.natCast_eq_natCast_iff', hamod, Nat.mod_eq_of_lt (by omega : 1 < n)]
  have h2' : ((a:ℕ):ZMod n) * ((u:ℕ):ZMod n) = 1 := by
    have hh := h2
    rw [Nat.cast_mul] at hh
    have hone : ((1:ℕ):ZMod n) = 1 := by norm_num
    rw [hone] at hh
    exact hh
  have hcast : ((n-u : ℕ) : ZMod n) = -((u:ℕ) : ZMod n) := by
    rw [Nat.cast_sub hu, ZMod.natCast_self]
    simp
  have h3 : ((n-1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self]
    norm_num
  have hZ : ((a*(n-u) : ℕ) : ZMod n) = ((n-1 : ℕ) : ZMod n) := by
    rw [Nat.cast_mul, hcast, h3]
    calc ((a:ℕ):ZMod n) * -((u:ℕ):ZMod n)
        = -(((a:ℕ):ZMod n) * ((u:ℕ):ZMod n)) := by ring
      _ = -1 := by rw [h2']
  have hfin := (ZMod.natCast_eq_natCast_iff' (a*(n-u)) (n-1) n).mp hZ
  rwa [Nat.mod_eq_of_lt (by omega : n-1 < n)] at hfin

/-- The inverse flip: `mark (n-u) (n-1)` gives `mark u 1`. -/
private lemma mark_neg' {n u : ℕ} (hn : 64 ≤ n) (hu : u ≤ n) {J : Finset ℕ}
    (h : (J.filter (fun a => (a*u)%n = n-1)).Nonempty) :
    (J.filter (fun a => (a*(n-u))%n = 1)).Nonempty := by
  obtain ⟨a, ha⟩ := h
  rw [Finset.mem_filter] at ha
  obtain ⟨haJ, hamod⟩ := ha
  refine ⟨a, ?_⟩
  rw [Finset.mem_filter]
  refine ⟨haJ, ?_⟩
  have h2 : ((a*u : ℕ) : ZMod n) = ((n-1:ℕ) : ZMod n) := by
    rw [ZMod.natCast_eq_natCast_iff', hamod, Nat.mod_eq_of_lt (by omega : n-1 < n)]
  have h3 : ((n-1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self]
    norm_num
  have h2' : ((a:ℕ):ZMod n) * ((u:ℕ):ZMod n) = -1 := by
    have hh := h2
    rw [Nat.cast_mul] at hh
    rw [h3] at hh
    exact hh
  have hcast : ((n-u : ℕ) : ZMod n) = -((u:ℕ) : ZMod n) := by
    rw [Nat.cast_sub hu, ZMod.natCast_self]
    simp
  have hZ : ((a*(n-u) : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by
    rw [Nat.cast_mul, hcast]
    calc ((a:ℕ):ZMod n) * -((u:ℕ):ZMod n)
        = -(((a:ℕ):ZMod n) * ((u:ℕ):ZMod n)) := by ring
      _ = -(-1) := by rw [h2']
      _ = ((1:ℕ):ZMod n) := by norm_num
  have hfin := (ZMod.natCast_eq_natCast_iff' (a*(n-u)) 1 n).mp hZ
  rwa [Nat.mod_eq_of_lt (by omega : 1 < n)] at hfin

/-- Main identity: the survivors with a late rough prime switch to the `p*q` pairs. -/
theorem L_goldbach_farey_late_first_hit_factor_switch :
    ∀ (n : ℕ) (J : Finset ℕ), 64 ≤ n → let I := Finset.Icc ((n+2)/3) ((2*n)/3);
    let mark := fun (u b : ℕ) => (J.filter (fun a => (a*u)%n = b)).Nonempty;
    let Hit := I.filter (fun u => u.Coprime n ∧ mark u 1 ∧ n < ((u*(n-u)).minFac)^3 ∧ ((u*(n-u)).minFac)^2 ≤ n);
    let P := (Finset.range (n+1)).filter (fun p => p.Prime ∧ n < p^3 ∧ p^2 ≤ n);
    let Q := fun (p b : ℕ) => (Finset.Icc p n).filter (fun q => q.Prime ∧ p*q ∈ I ∧ (p*q).Coprime n ∧ p ≤ (n-p*q).minFac ∧ mark (p*q) b);
    Hit.card = ∑ p ∈ P, ((Q p 1).card+(Q p (n-1)).card) := by
  intro n J hn
  dsimp only
  set I : Finset ℕ := Finset.Icc ((n+2)/3) ((2*n)/3) with hI
  set mark : ℕ → ℕ → Prop := fun u b => (J.filter (fun a => (a*u)%n = b)).Nonempty with hmark
  set F : ℕ → ℕ := fun u => (u*(n-u)).minFac with hF
  set Hit : Finset ℕ := I.filter (fun u => u.Coprime n ∧ mark u 1 ∧ n < (F u)^3 ∧ (F u)^2 ≤ n) with hHit
  set P : Finset ℕ := (Finset.range (n+1)).filter (fun p => p.Prime ∧ n < p^3 ∧ p^2 ≤ n) with hP
  set Q : ℕ → ℕ → Finset ℕ := fun p b => (Finset.Icc p n).filter (fun q => q.Prime ∧ p*q ∈ I ∧ (p*q).Coprime n ∧ p ≤ (n-p*q).minFac ∧ mark (p*q) b) with hQ
  set H1 : Finset ℕ := Hit.filter (fun u => F u ∣ u) with hH1
  set H2 : Finset ℕ := Hit.filter (fun u => ¬ F u ∣ u) with hH2
  have hFn : ∀ u, F u = (u*(n-u)).minFac := by intro u; rw [hF]
  have hPmem : ∀ p, p ∈ P ↔ p.Prime ∧ n < p^3 ∧ p^2 ≤ n ∧ p < n+1 := by
    intro p; rw [hP, Finset.mem_filter, Finset.mem_range]; tauto
  have hQmem : ∀ p b q, q ∈ Q p b ↔ q ∈ Finset.Icc p n ∧ q.Prime ∧ p*q ∈ I ∧
      (p*q).Coprime n ∧ p ≤ (n-p*q).minFac ∧ mark (p*q) b := by
    intro p b q; rw [hQ, Finset.mem_filter]
  have hHitmem : ∀ u, u ∈ Hit ↔ u ∈ I ∧ u.Coprime n ∧ mark u 1 ∧ n < (F u)^3 ∧ (F u)^2 ≤ n := by
    intro u; rw [hHit, Finset.mem_filter]
  have hH1mem : ∀ u, u ∈ H1 ↔ u ∈ Hit ∧ F u ∣ u := by
    intro u; rw [hH1, Finset.mem_filter]
  have hH2mem : ∀ u, u ∈ H2 ↔ u ∈ Hit ∧ ¬ F u ∣ u := by
    intro u; rw [hH2, Finset.mem_filter]
  have hsplit : Hit.card = H1.card + H2.card := by
    rw [hH1, hH2]
    exact (Finset.card_filter_add_card_filter_not (fun u => F u ∣ u) (s := Hit)).symm
  -- ===== E1 =====
  have E1 : H1.card = ∑ p ∈ P, (Q p 1).card := by
    rw [← Finset.card_sigma]
    refine Finset.card_bij (fun u hu => ⟨F u, u / F u⟩) ?_ ?_ ?_
    · intro u hu
      obtain ⟨huHit, hdvd⟩ := (hH1mem u).mp hu
      obtain ⟨huI, hcop, hmark1, hF3, hF2⟩ := (hHitmem u).mp huHit
      have hFapp : F u = (u*(n-u)).minFac := hFn u
      have hdvd' : ((u*(n-u)).minFac) ∣ u := by rw [← hFapp]; exact hdvd
      have hF3' : n < ((u*(n-u)).minFac)^3 := by rw [← hFapp]; exact hF3
      have hF2' : ((u*(n-u)).minFac)^2 ≤ n := by rw [← hFapp]; exact hF2
      have hFp : (F u).Prime := by rw [hFapp]; exact Fprime hn huI
      have hFpos : 0 < F u := hFp.pos
      rw [Finset.mem_sigma]
      constructor
      · -- F u ∈ P
        rw [hPmem]
        have hFF : F u ≤ (F u)^2 := by
          have h2 : 1 ≤ F u := by have := hFp.two_le; omega
          calc F u = F u * 1 := (Nat.mul_one _).symm
            _ ≤ F u * F u := Nat.mul_le_mul_left (F u) h2
            _ = (F u)^2 := by ring
        have hle_n : F u ≤ n := hFF.trans hF2
        exact ⟨hFp, hF3, hF2, Nat.lt_succ_of_le hle_n⟩
      · -- u/F u ∈ Q (F u) 1
        rw [hQmem]
        obtain ⟨q', hq'p, hu_eq', hFq'⟩ := semiprime_left hn huI hdvd' hF3' hF2'
        set q := u / F u with hqdef
        have hu2 : u = F u * q' := by rw [hFapp]; exact hu_eq'
        have hq_eq' : q = q' := by
          rw [hqdef]
          refine Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; exact le_of_eq hu2.symm) ?_
          calc u = F u * q' := hu2
            _ < F u * (q'+1) := Nat.mul_lt_mul_of_pos_left (by omega) hFpos
            _ = (q'+1) * F u := Nat.mul_comm _ _
        have hu_eq : u = F u * q := by rw [hq_eq']; exact hu2
        have hFq : F u ≤ q := by rw [hq_eq']; exact hFq'
        constructor
        · rw [Finset.mem_Icc]
          refine ⟨hFq, ?_⟩
          have hq_le_u : q ≤ u := by rw [hqdef]; exact Nat.div_le_self u (F u)
          have hu_lt_n : u < n := (mid_bounds hn huI).2.1
          exact le_trans hq_le_u (le_of_lt hu_lt_n)
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hq_eq']; exact hq'p
        · rw [← hu_eq]; exact huI
        · rw [← hu_eq]; exact hcop
        · have hnu_eq : n - F u * q = n - u := by rw [← hu_eq]
          rw [hnu_eq]
          have hb := mid_bounds hn huI
          have hvp : Nat.Prime (Nat.minFac (n-u)) := Nat.minFac_prime (by omega : n-u ≠ 1)
          have hdvd_nu : Nat.minFac (n-u) ∣ u*(n-u) := dvd_mul_of_dvd_right (Nat.minFac_dvd (n-u)) _
          have h1 : ((u*(n-u)).minFac) ≤ Nat.minFac (n-u) := Nat.minFac_le_of_dvd hvp.two_le hdvd_nu
          rw [← hFapp] at h1
          exact h1
        · rw [← hu_eq]; exact hmark1
    · -- injective
      intro u1 hu1 u2 hu2 heq
      obtain ⟨huHit1, hdvd1⟩ := (hH1mem u1).mp hu1
      obtain ⟨huHit2, hdvd2⟩ := (hH1mem u2).mp hu2
      have hF12 : F u1 = F u2 := congrArg Sigma.fst heq
      have hq12 : u1 / F u1 = u2 / F u2 := congrArg Sigma.snd heq
      have h1 : u1 = F u1 * (u1 / F u1) := (Nat.mul_div_cancel' hdvd1).symm
      have h2 : u2 = F u2 * (u2 / F u2) := (Nat.mul_div_cancel' hdvd2).symm
      rw [h1, h2, hq12, hF12]
    · -- surjective
      intro b hb
      obtain ⟨p, q⟩ := b
      rw [Finset.mem_sigma] at hb
      obtain ⟨hpP, hqQ⟩ := hb
      rw [hPmem] at hpP
      rw [hQmem] at hqQ
      obtain ⟨hp1, hp2, hp3, hp4⟩ := hpP
      obtain ⟨hqIcc, hqqp, hqI, hqcop, hqmin, hqmark⟩ := hqQ
      rw [Finset.mem_Icc] at hqIcc
      obtain ⟨hqp_ge, hqp_le⟩ := hqIcc
      have hF_eq : F (p*q) = p := by
        rw [hFn, minFac_prod_pq hn hp1 hqqp hqp_ge hqI hqmin]
      have hmem : p*q ∈ H1 := by
        rw [hH1mem]
        constructor
        · rw [hHitmem]
          exact ⟨hqI, hqcop, hqmark, by rw [hF_eq]; exact hp2,
            by rw [hF_eq]; exact hp3⟩
        · rw [hF_eq]; exact dvd_mul_right p q
      refine ⟨p*q, hmem, ?_⟩
      rw [hF_eq]
      rw [Nat.mul_div_cancel_left q hp1.pos]
  -- ===== E2 =====
  have E2 : H2.card = ∑ p ∈ P, (Q p (n-1)).card := by
    rw [← Finset.card_sigma]
    refine Finset.card_bij (fun u hu => ⟨F u, (n-u) / F u⟩) ?_ ?_ ?_
    · intro u hu
      obtain ⟨huHit, hdvd_not⟩ := (hH2mem u).mp hu
      obtain ⟨huI, hcop, hmark1, hF3, hF2⟩ := (hHitmem u).mp huHit
      have hFapp : F u = (u*(n-u)).minFac := hFn u
      have hdvd_nu' : ((u*(n-u)).minFac) ∣ (n-u) := by
        rcases Fdvd_or hn huI with h | h
        · have hFu : F u ∣ u := by rw [hFapp]; exact h
          exact absurd hFu hdvd_not
        · exact h
      have hF3' : n < ((u*(n-u)).minFac)^3 := by rw [← hFapp]; exact hF3
      have hF2' : ((u*(n-u)).minFac)^2 ≤ n := by rw [← hFapp]; exact hF2
      have hFp : (F u).Prime := by rw [hFapp]; exact Fprime hn huI
      have hFpos : 0 < F u := hFp.pos
      rw [Finset.mem_sigma]
      constructor
      · -- F u ∈ P
        rw [hPmem]
        have hFF : F u ≤ (F u)^2 := by
          have h2 : 1 ≤ F u := by have := hFp.two_le; omega
          calc F u = F u * 1 := (Nat.mul_one _).symm
            _ ≤ F u * F u := Nat.mul_le_mul_left (F u) h2
            _ = (F u)^2 := by ring
        have hle_n : F u ≤ n := hFF.trans hF2
        exact ⟨hFp, hF3, hF2, Nat.lt_succ_of_le hle_n⟩
      · -- (n-u)/F u ∈ Q (F u) (n-1)
        rw [hQmem]
        obtain ⟨q', hq'p, hv_eq', hFq'⟩ := semiprime_right hn huI hdvd_nu' hF3' hF2'
        set q := (n-u) / F u with hqdef
        have hv2 : n - u = F u * q' := by rw [hFapp]; exact hv_eq'
        have hq_eq' : q = q' := by
          rw [hqdef]
          refine Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; exact le_of_eq hv2.symm) ?_
          calc n - u = F u * q' := hv2
            _ < F u * (q'+1) := Nat.mul_lt_mul_of_pos_left (by omega) hFpos
            _ = (q'+1) * F u := Nat.mul_comm _ _
        have hnu_eq : n - u = F u * q := by rw [hq_eq']; exact hv2
        have hFq : F u ≤ q := by rw [hq_eq']; exact hFq'
        have hnuI : n - u ∈ I := mid_symm hn huI
        have hnu_le : n - u ≤ n := by have := (mid_bounds hn huI).2.2.2; omega
        constructor
        · rw [Finset.mem_Icc]
          refine ⟨hFq, ?_⟩
          have hq_le : q ≤ n - u := by rw [hqdef]; exact Nat.div_le_self (n-u) (F u)
          have hnu_lt : n - u < n := (mid_bounds hn huI).2.2.2
          exact le_trans hq_le (le_of_lt hnu_lt)
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hq_eq']; exact hq'p
        · -- F u * q ∈ I
          rw [← hnu_eq]; exact hnuI
        · -- coprime
          have hu_le_n : u ≤ n := le_of_lt (mid_bounds hn huI).2.1
          have hcop_nu : (n-u).Coprime n := by
            have hgcd1 : Nat.gcd (n-u) n ∣ u := by
              have hd1 : Nat.gcd (n-u) n ∣ n := Nat.gcd_dvd_right _ _
              have hd2 : Nat.gcd (n-u) n ∣ n-u := Nat.gcd_dvd_left _ _
              have hsub := Nat.dvd_sub hd1 hd2
              rwa [Nat.sub_sub_self hu_le_n] at hsub
            have hcop' : Nat.gcd u n = 1 := hcop
            have hdvd1 : Nat.gcd (n-u) n ∣ 1 := by
              rw [← hcop']
              exact Nat.dvd_gcd hgcd1 (Nat.gcd_dvd_right _ _)
            exact Nat.dvd_antisymm hdvd1 (Nat.one_dvd _)
          rw [← hnu_eq]; exact hcop_nu
        · -- F u ≤ minFac (n - F u*q)
          have hnu2 : n - F u * q = u := by rw [← hnu_eq]; exact Nat.sub_sub_self (le_of_lt (mid_bounds hn huI).2.1)
          rw [hnu2]
          have hu22 : 22 ≤ u := (mid_bounds hn huI).1
          have hup : Nat.Prime (Nat.minFac u) := Nat.minFac_prime (by omega : u ≠ 1)
          have hdvd_u : Nat.minFac u ∣ u*(n-u) := dvd_mul_of_dvd_left (Nat.minFac_dvd u) _
          have hle : ((u*(n-u)).minFac) ≤ Nat.minFac u := Nat.minFac_le_of_dvd hup.two_le hdvd_u
          rw [← hFapp] at hle
          exact hle
        · -- mark (F u * q) (n-1)
          rw [← hnu_eq]
          have hmu : (J.filter (fun a => (a*u)%n = 1)).Nonempty := by simpa only [hmark] using hmark1
          have hu_le_n : u ≤ n := le_of_lt (mid_bounds hn huI).2.1
          have hmn : (J.filter (fun a => (a*(n-u))%n = n-1)).Nonempty :=
            mark_neg hn hu_le_n hmu
          simpa only [hmark] using hmn
    · -- injective
      intro u1 hu1 u2 hu2 heq
      obtain ⟨huHit1, hdvd1_not⟩ := (hH2mem u1).mp hu1
      obtain ⟨huHit2, hdvd2_not⟩ := (hH2mem u2).mp hu2
      obtain ⟨huI1, -, -, -, -⟩ := (hHitmem u1).mp huHit1
      obtain ⟨huI2, -, -, -, -⟩ := (hHitmem u2).mp huHit2
      have hdvd1 : F u1 ∣ n - u1 := by
        rcases Fdvd_or hn huI1 with h | h
        · exact absurd (by rw [hFn u1]; exact h) hdvd1_not
        · exact h
      have hdvd2 : F u2 ∣ n - u2 := by
        rcases Fdvd_or hn huI2 with h | h
        · exact absurd (by rw [hFn u2]; exact h) hdvd2_not
        · exact h
      have hF12 : F u1 = F u2 := congrArg Sigma.fst heq
      have hq12 : (n-u1) / F u1 = (n-u2) / F u2 := congrArg Sigma.snd heq
      have h1 : n - u1 = F u1 * ((n-u1) / F u1) := (Nat.mul_div_cancel' hdvd1).symm
      have h2 : n - u2 = F u2 * ((n-u2) / F u2) := (Nat.mul_div_cancel' hdvd2).symm
      have hb1 := mid_bounds hn huI1
      have hb2 := mid_bounds hn huI2
      have hnu : n - u1 = n - u2 := by rw [h1, h2, hq12, hF12]
      omega
    · -- surjective
      intro b hb
      obtain ⟨p, q⟩ := b
      rw [Finset.mem_sigma] at hb
      obtain ⟨hpP, hqQ⟩ := hb
      rw [hPmem] at hpP
      rw [hQmem] at hqQ
      obtain ⟨hp1, hp2, hp3, hp4⟩ := hpP
      obtain ⟨hqIcc, hqqp, hqI, hqcop, hqmin, hqmark⟩ := hqQ
      rw [Finset.mem_Icc] at hqIcc
      obtain ⟨hqp_ge, hqp_le⟩ := hqIcc
      have hpq_le_n : p*q ≤ n := by
        have hlt : p*q < n := (mid_bounds hn hqI).2.1
        omega
      have huI : n - p*q ∈ I := mid_symm hn hqI
      have hF_eq : F (n - p*q) = p := by
        have hnv : n - (n - p*q) = p*q := Nat.sub_sub_self hpq_le_n
        rw [hFn, hnv, Nat.mul_comm]
        exact minFac_prod_pq hn hp1 hqqp hqp_ge hqI hqmin
      have hcop_u : (n - p*q).Coprime n := by
        have hgcd1 : Nat.gcd (n - p*q) n ∣ p*q := by
          have hd1 : Nat.gcd (n - p*q) n ∣ n := Nat.gcd_dvd_right _ _
          have hd2 : Nat.gcd (n - p*q) n ∣ n - p*q := Nat.gcd_dvd_left _ _
          have hsub := Nat.dvd_sub hd1 hd2
          rwa [Nat.sub_sub_self hpq_le_n] at hsub
        have hdvd1 : Nat.gcd (n - p*q) n ∣ 1 := by
          rw [← hqcop]
          exact Nat.dvd_gcd hgcd1 (Nat.gcd_dvd_right _ _)
        exact Nat.dvd_antisymm hdvd1 (Nat.one_dvd _)
      have hmark_u : mark (n - p*q) 1 := by
        have hpq_le : p*q ≤ n := hpq_le_n
        have hmn : (J.filter (fun a => (a*(n - (p*q)))%n = 1)).Nonempty := by
          have hm0 : (J.filter (fun a => (a*(p*q))%n = n-1)).Nonempty := by
            simpa only [hmark] using hqmark
          exact mark_neg' hn hpq_le hm0
        simpa only [hmark]
      have hhit : n - p*q ∈ Hit := by
        rw [hHitmem]
        exact ⟨huI, hcop_u, hmark_u, by rw [hF_eq]; exact hp2, by rw [hF_eq]; exact hp3⟩
      have hnotdvd : ¬ F (n - p*q) ∣ (n - p*q) := by
        rw [hF_eq]
        intro hdvd
        have hpqd : p ∣ p*q := dvd_mul_right p q
        have hpn : p ∣ n := by
          have hadd : p ∣ (n - p*q) + p*q := Nat.dvd_add hdvd hpqd
          rwa [Nat.sub_add_cancel hpq_le_n] at hadd
        have hgcd_dvd : p ∣ Nat.gcd (p*q) n := Nat.dvd_gcd hpqd hpn
        rw [hqcop] at hgcd_dvd
        have hle1 : p ≤ 1 := Nat.le_of_dvd (by norm_num : 0 < 1) hgcd_dvd
        have hp2le : 2 ≤ p := hp1.two_le
        omega
      have hmem : n - p*q ∈ H2 := by
        rw [hH2mem]
        exact ⟨hhit, hnotdvd⟩
      refine ⟨n - p*q, hmem, ?_⟩
      have hnv : n - (n - p*q) = p*q := Nat.sub_sub_self hpq_le_n
      rw [hF_eq, hnv]
      rw [Nat.mul_div_cancel_left q hp1.pos]
  rw [hsplit, E1, E2, ← Finset.sum_add_distrib]

end PEqualNP.Outside

open PEqualNP.Outside

theorem Conjectures.Goldbach.FareyLateFirstHitFactorSwitch :
  ∀ (n : ℕ) (J : Finset ℕ), 64 ≤ n → let I := Finset.Icc ((n+2)/3) ((2*n)/3); let mark := fun (u b : ℕ) => (J.filter (fun a => (a*u)%n = b)).Nonempty; let Hit := I.filter (fun u => u.Coprime n ∧ mark u 1 ∧ n < ((u*(n-u)).minFac)^3 ∧ ((u*(n-u)).minFac)^2 ≤ n); let P := (Finset.range (n+1)).filter (fun p => p.Prime ∧ n < p^3 ∧ p^2 ≤ n); let Q := fun (p b : ℕ) => (Finset.Icc p n).filter (fun q => q.Prime ∧ p*q ∈ I ∧ (p*q).Coprime n ∧ p ≤ (n-p*q).minFac ∧ mark (p*q) b); Hit.card = ∑ p ∈ P, ((Q p 1).card+(Q p (n-1)).card)
  := PEqualNP.Outside.L_goldbach_farey_late_first_hit_factor_switch
