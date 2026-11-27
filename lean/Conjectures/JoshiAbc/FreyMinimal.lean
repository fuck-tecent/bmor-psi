import Mathlib

namespace Conjectures.JoshiAbc

namespace FreyMinimal_aux

theorem contra_of_dvd_both {a b p : ℕ} (hp : p.Prime) (hab : Nat.Coprime a b)
    (hpa : p ∣ a) (hpb : p ∣ b) : False := by
  have hg : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa hpb
  have h1 : Nat.gcd a b = 1 := Nat.coprime_iff_gcd_eq_one.mp hab
  rw [h1] at hg
  have hp1 : p = 1 := Nat.eq_one_of_dvd_one hg
  exact absurd hp1 (ne_of_gt hp.one_lt)

theorem not_two_of_odd {p : ℕ} (hodd : Odd p) : p ≠ 2 := by
  intro h
  rcases hodd with ⟨k, hk⟩
  omega

theorem not_dvd_sixteen {p : ℕ} (hp : p.Prime) (hodd : Odd p) : ¬ p ∣ 16 := by
  intro h
  have h4 : p ∣ (2:ℕ) ^ 4 := by
    have e : (2:ℕ) ^ 4 = 16 := by norm_num
    rw [e]
    exact h
  have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h4
  have heq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
  exact not_two_of_odd hodd heq

end FreyMinimal_aux

theorem FreyMinimal :
    ∀ a b p : ℕ, 0<a → 0<b → Nat.Coprime a b → p.Prime → Odd p → p ∣ a*b*(a+b) → ¬ p ∣ 16*(a^2+a*b+b^2) := by
  intro a b p ha hb hab hp hodd hdiv hcd
  rcases (Nat.Prime.dvd_mul hp).1 hcd with h16 | hQ
  · exact (FreyMinimal_aux.not_dvd_sixteen hp hodd) h16
  rcases (Nat.Prime.dvd_mul hp).1 hdiv with hab_prod | hsum
  · rcases (Nat.Prime.dvd_mul hp).1 hab_prod with hpa | hpb
    · have hQ' : p ∣ a * (a + b) + b ^ 2 := by
        have e : a * (a + b) + b ^ 2 = a ^ 2 + a * b + b ^ 2 := by ring
        rw [e]
        exact hQ
      have hbmul : p ∣ a * (a + b) := dvd_mul_of_dvd_left hpa (a + b)
      have hb2 : p ∣ b ^ 2 := (Nat.dvd_add_right hbmul).1 hQ'
      exact FreyMinimal_aux.contra_of_dvd_both hp hab hpa (hp.dvd_of_dvd_pow hb2)
    · have hQ' : p ∣ b * (a + b) + a ^ 2 := by
        have e : b * (a + b) + a ^ 2 = a ^ 2 + a * b + b ^ 2 := by ring
        rw [e]
        exact hQ
      have hamul : p ∣ b * (a + b) := dvd_mul_of_dvd_left hpb (a + b)
      have ha2 : p ∣ a ^ 2 := (Nat.dvd_add_right hamul).1 hQ'
      exact FreyMinimal_aux.contra_of_dvd_both hp hab (hp.dvd_of_dvd_pow ha2) hpb
  · have hsq : p ∣ (a + b) ^ 2 := by
      have h := dvd_mul_of_dvd_left hsum (a + b)
      have e : (a + b) * (a + b) = (a + b) ^ 2 := by ring
      rw [e] at h
      exact h
    have e : (a + b) ^ 2 = (a ^ 2 + a * b + b ^ 2) + a * b := by ring
    have hboth : p ∣ (a ^ 2 + a * b + b ^ 2) + a * b := by
      rw [← e]
      exact hsq
    have habm : p ∣ a * b := (Nat.dvd_add_right hQ).1 hboth
    rcases (Nat.Prime.dvd_mul hp).1 habm with hpa | hpb
    · have hba : p ∣ b + a := by
        rw [Nat.add_comm]
        exact hsum
      exact FreyMinimal_aux.contra_of_dvd_both hp hab hpa ((Nat.dvd_add_left hpa).1 hba)
    · exact FreyMinimal_aux.contra_of_dvd_both hp hab ((Nat.dvd_add_left hpb).1 hsum) hpb

end Conjectures.JoshiAbc
