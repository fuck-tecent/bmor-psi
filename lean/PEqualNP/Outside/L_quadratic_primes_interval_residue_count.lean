import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_interval_residue_count :
    let roots := fun (q : ℕ) => ((Finset.range q).filter (fun r => q ∣ r^2+1)).card; ∀ x q : ℕ, 0 < q → ((Finset.Ioc x (2*x)).filter (fun n => q ∣ n^2+1)).card ≤ (x/q+1)*roots q := by
  dsimp only
  intro x q hq
  let roots := (Finset.range q).filter (fun r => q ∣ r ^ 2 + 1)
  let solutions := (Finset.Ioc x (2 * x)).filter (fun n => q ∣ n ^ 2 + 1)
  let blockAndRoot := fun n : Nat => ((n - x) / q, n % q)
  change solutions.card ≤ (x / q + 1) * roots.card
  rw [← Finset.card_range (x / q + 1), ← Finset.card_product]
  refine Finset.card_le_card_of_injOn blockAndRoot ?_ ?_
  · intro n hn
    have hn' : n ∈ solutions := hn
    obtain ⟨hnInterval, hnDvd⟩ := Finset.mem_filter.mp hn'
    obtain ⟨_, hnUpper⟩ := Finset.mem_Ioc.mp hnInterval
    apply Finset.mk_mem_product
    · apply Finset.mem_range.mpr
      exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega : n - x ≤ x))
    · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt n hq), ?_⟩
      exact Nat.modEq_zero_iff_dvd.mp
        ((((Nat.mod_modEq n q).pow 2).add_right 1).trans hnDvd.modEq_zero_nat)
  · intro n hn m hm heq
    have hn' : n ∈ solutions := hn
    have hm' : m ∈ solutions := hm
    have hnx := ((Finset.mem_Ioc.mp (Finset.mem_filter.mp hn').1).1).le
    have hmx := ((Finset.mem_Ioc.mp (Finset.mem_filter.mp hm').1).1).le
    have hquot : (n - x) / q = (m - x) / q := congrArg Prod.fst heq
    have hmod : Nat.ModEq q n m := congrArg Prod.snd heq
    have hrem : (n - x) % q = (m - x) % q := hmod.sub_right hnx hmx
    have hdiff : n - x = m - x := by
      rw [← Nat.mod_add_div (n - x) q, ← Nat.mod_add_div (m - x) q, hrem, hquot]
    omega
