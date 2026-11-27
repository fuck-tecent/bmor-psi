import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.List.Prime
import Mathlib.Data.ZMod.Basic

theorem Conjectures.Goldbach.FiniteSharedLucasCertificates :
    let checked := fun (nodes : List (ℕ × ℕ × List ℕ)) => ∀ entry ∈ nodes, let p := entry.1; let a := entry.2.1; let fs := entry.2.2; 2 < p ∧ fs.prod = p-1 ∧ Nat.powMod a (p-1) p = 1 % p ∧ (∀ r ∈ fs, 2 ≤ r ∧ r < p ∧ (r = 2 ∨ ∃ item ∈ nodes, item.1 = r) ∧ Nat.powMod a ((p-1)/r) p ≠ 1 % p); ∀ nodes : List (ℕ × ℕ × List ℕ), checked nodes → ∀ entry ∈ nodes, Nat.Prime entry.1 := by
  dsimp only
  intro nodes hchecked
  have sound : ∀ p : ℕ, ∀ entry ∈ nodes, entry.1 = p → p.Prime := by
    intro p
    induction p using Nat.strong_induction_on with
    | ind p ih =>
      intro entry hentry hvalue
      rcases entry with ⟨p', a, fs⟩
      dsimp only at hvalue
      subst p'
      obtain ⟨_, hprod, hpow, hfs⟩ := hchecked (p, a, fs) hentry
      have hfprime : ∀ r ∈ fs, Nat.Prime r := by
        intro r hr
        obtain ⟨_, hrlt, hsource, _⟩ := hfs r hr
        rcases hsource with rfl | ⟨item, hitem, hval⟩
        · exact Nat.prime_two
        · exact ih r hrlt item hitem hval
      refine lucas_primality p (a : ZMod p) ?_ ?_
      · have hmod : a ^ (p - 1) % p = 1 % p := by
          simpa only [Nat.powMod_def] using hpow
        have hc := (ZMod.natCast_eq_natCast_iff' (a ^ (p - 1)) 1 p).2 hmod
        simpa only [Nat.cast_pow, Nat.cast_one] using hc
      · intro q hq hqdiv
        have hqprod : q ∣ fs.prod := by rw [hprod]; exact hqdiv
        obtain ⟨r, hr, hrdiv⟩ := hq.prime.dvd_prod_iff.mp hqprod
        have hqr : q = r := (Nat.prime_dvd_prime_iff_eq hq (hfprime r hr)).mp hrdiv
        subst r
        intro heq
        apply (hfs q hr).2.2.2
        rw [Nat.powMod_def]
        apply (ZMod.natCast_eq_natCast_iff' (a ^ ((p - 1) / q)) 1 p).1
        simpa only [Nat.cast_pow, Nat.cast_one] using heq
  intro entry hentry
  exact sound entry.1 entry hentry rfl
