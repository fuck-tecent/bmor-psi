import Mathlib
open scoped BigOperators

noncomputable section
namespace B1B1

/-- Reduced fractions are equal only if numerator and denominator agree. -/
lemma fraction_inj {q q' a a' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (hcop : Nat.Coprime a q) (hcop' : Nat.Coprime a' q')
    (h : (a:ℝ)/(q:ℝ) = (a':ℝ)/(q':ℝ)) : a = a' ∧ q = q' := by
  have hcross : (a:ℤ) * (q':ℤ) = (a':ℤ) * (q:ℤ) := by
    have h' : (a:ℝ) * (q':ℝ) = (a':ℝ) * (q:ℝ) := by
      rw [div_eq_div_iff (by positivity) (by positivity)] at h
      exact h
    exact_mod_cast h'
  have hqq' : q = q' := by
    have hdvd : (q:ℤ) ∣ (q':ℤ) := by
      have hq_dvd : (q:ℤ) ∣ (a:ℤ) * (q':ℤ) :=
        ⟨(a':ℤ), by rw [mul_comm (q:ℤ) (a':ℤ)]; exact hcross⟩
      have hcopZ : IsCoprime (q:ℤ) (a:ℤ) := hcop.symm.isCoprime
      have hq_dvd' : (q:ℤ) ∣ (q':ℤ) * (a:ℤ) := by rw [mul_comm]; exact hq_dvd
      exact hcopZ.dvd_of_dvd_mul_right hq_dvd'
    have hdvd' : q ∣ q' := by exact_mod_cast hdvd
    have hdvd2 : (q':ℤ) ∣ (q:ℤ) := by
      have hq'_dvd : (q':ℤ) ∣ (a':ℤ) * (q:ℤ) :=
        ⟨(a:ℤ), by rw [mul_comm (q':ℤ) (a:ℤ)]; exact hcross.symm⟩
      have hcopZ' : IsCoprime (q':ℤ) (a':ℤ) := hcop'.symm.isCoprime
      have hq'_dvd' : (q':ℤ) ∣ (q:ℤ) * (a':ℤ) := by rw [mul_comm]; exact hq'_dvd
      exact hcopZ'.dvd_of_dvd_mul_right hq'_dvd'
    have hdvd2' : q' ∣ q := by exact_mod_cast hdvd2
    exact Nat.le_antisymm (Nat.le_of_dvd hq' hdvd') (Nat.le_of_dvd hq hdvd2')
  have haa' : a = a' := by
    have hZ : (a:ℤ) * (q:ℤ) = (a':ℤ) * (q:ℤ) := by
      rw [hqq']
      have hc := hcross
      rw [hqq'] at hc
      exact hc
    have hqZ : (q:ℤ) ≠ 0 := by exact_mod_cast hq.ne'
    have h : (a:ℤ) = (a':ℤ) := mul_right_cancel₀ hqZ hZ
    exact_mod_cast h
  exact ⟨haa', hqq'⟩

end B1B1
