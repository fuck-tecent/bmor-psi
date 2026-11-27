import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside

theorem L_quadratic_primes_total_mass_lower :
    ∀ x : ℕ, 2 ≤ x → 2*(x:ℝ)*Real.log (x:ℝ) <
      Finset.sum (Finset.Ioc x (2*x)) (fun n => Real.log ((n:ℝ)^2+1)) := by
  intro x hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hcard : (Finset.Ioc x (2*x)).card = x := by
    rw [Nat.card_Ioc]
    omega
  have hne : (Finset.Ioc x (2*x)).Nonempty :=
    ⟨x + 1, Finset.mem_Ioc.mpr ⟨by omega, by omega⟩⟩
  calc
    2*(x:ℝ)*Real.log (x:ℝ) =
        Finset.sum (Finset.Ioc x (2*x)) (fun _ => 2 * Real.log (x:ℝ)) := by
      rw [Finset.sum_const, hcard, nsmul_eq_mul]
      ring
    _ < _ := by
      apply Finset.sum_lt_sum_of_nonempty hne
      intro n hn
      have hxn : (x : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
      have hs : (x : ℝ)^2 < (n : ℝ)^2 + 1 := by nlinarith [sq_nonneg ((n : ℝ) - x)]
      have hlog := Real.log_lt_log (sq_pos_of_pos hxpos) hs
      simpa only [Real.log_pow, Nat.cast_ofNat] using hlog

end PEqualNP.Outside
