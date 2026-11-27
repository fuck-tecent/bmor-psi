import Mathlib

namespace Conjectures.Goldbach.BeaumontCycleFiber_aux

theorem card_filter_dvd (d n m : ℕ) (hn : 0 < n) (hm : d * n = m) :
    ((Finset.range m).filter (fun k => n ∣ k)).card = d := by
  have himg : (Finset.range m).filter (fun k => n ∣ k) = (Finset.range d).image (fun j => n * j) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hk, j, hj⟩
      refine ⟨j, ?_, hj.symm⟩
      have h2 : n * j < n * d := by
        calc n * j = k := hj.symm
          _ < m := hk
          _ = n * d := by rw [← hm, Nat.mul_comm d n]
      exact (Nat.mul_lt_mul_left hn).mp h2
    · rintro ⟨j, hj, rfl⟩
      refine ⟨?_, j, rfl⟩
      calc n * j < n * d := (Nat.mul_lt_mul_left hn).mpr hj
        _ = m := by rw [← hm, Nat.mul_comm n d]
  rw [himg, Finset.card_image_of_injective _ (fun x y hx => Nat.mul_left_cancel hn hx),
    Finset.card_range]

end Conjectures.Goldbach.BeaumontCycleFiber_aux

theorem Conjectures.Goldbach.BeaumontCycleFiber : ∀ (m a : ℕ), 0 < m → ((Finset.range m).filter (fun k => (a*k)%m=0)).card = Nat.gcd m a := by
  intro m a hm
  have hdpos : 0 < Nat.gcd m a := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left m a) hm
  have hcop : Nat.Coprime (m / Nat.gcd m a) (a / Nat.gcd m a) :=
    Nat.coprime_div_gcd_div_gcd hdpos
  have hmdeq : Nat.gcd m a * (m / Nat.gcd m a) = m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m a)
  have hnpos : 0 < m / Nat.gcd m a := by
    rcases Nat.eq_zero_or_pos (m / Nat.gcd m a) with hz | hp
    · rw [hz, mul_zero] at hmdeq
      omega
    · exact hp
  have key : ∀ k : ℕ, (a * k) % m = 0 ↔ (m / Nat.gcd m a) ∣ k := by
    intro k
    have h2 : m ∣ a * k ↔ (m / Nat.gcd m a) ∣ k := by
      constructor
      · intro h
        have hh : Nat.gcd m a * (m / Nat.gcd m a) ∣ (Nat.gcd m a * (a / Nat.gcd m a)) * k := by
          rw [hmdeq, Nat.mul_div_cancel' (Nat.gcd_dvd_right m a)]
          exact h
        have hstep : Nat.gcd m a * (m / Nat.gcd m a) ∣ Nat.gcd m a * ((a / Nat.gcd m a) * k) := by
          rwa [mul_assoc] at hh
        exact hcop.dvd_of_dvd_mul_left ((mul_dvd_mul_iff_left hdpos.ne').mp hstep)
      · intro h
        have hstep2 : (m / Nat.gcd m a) ∣ (a / Nat.gcd m a) * k := Dvd.dvd.mul_left h _
        have hstep : Nat.gcd m a * (m / Nat.gcd m a) ∣ Nat.gcd m a * ((a / Nat.gcd m a) * k) :=
          (mul_dvd_mul_iff_left hdpos.ne').mpr hstep2
        have hfinal : m ∣ Nat.gcd m a * ((a / Nat.gcd m a) * k) := by rwa [hmdeq] at hstep
        have heq : Nat.gcd m a * ((a / Nat.gcd m a) * k) = a * k := by
          rw [← mul_assoc, Nat.mul_div_cancel' (Nat.gcd_dvd_right m a)]
        exact heq ▸ hfinal
    exact Nat.dvd_iff_mod_eq_zero.symm.trans h2
  have hfeq : (Finset.range m).filter (fun k => (a * k) % m = 0)
      = (Finset.range m).filter (fun k => (m / Nat.gcd m a) ∣ k) := by
    apply Finset.filter_congr
    intro k _
    exact key k
  rw [hfeq]
  exact Conjectures.Goldbach.BeaumontCycleFiber_aux.card_filter_dvd
    (Nat.gcd m a) (m / Nat.gcd m a) m hnpos hmdeq
