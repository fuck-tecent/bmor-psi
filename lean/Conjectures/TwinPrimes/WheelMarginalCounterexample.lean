import Mathlib

/-!
# PREPUB twin-primes gap: `L-twin-primes-wheel-marginal-counterexample`

A mod-`q` wheel marginal (the mass of a window in every residue class) does not determine the
difference-2 correlation inside the window.  For every admissible wheel class `a` we construct
two `{0,1}`-valued weights `f, g` supported on the coprime part of a short window `(X, 51X/50]`
which have the same residue-class sums modulo `q`, but whose difference-2 correlations differ:
`sum f(n) f(n+2) = 1` while `sum g(n) g(n+2) = 0`.

Construction: let `m` be the representative of the class `a` in `[X+1, X+q]` and `n2` the
representative of the class `(a+2) % q` near the top of the window.  Take `f` supported on
`{m, m+2}` and `g` supported on `{m, n2}`; the window is long enough (`X >= 200(q+1)`) that
`n2` is more than `2` away from both `m` and `m+2`.
-/

open scoped BigOperators
open Finset

namespace TwinWheelMarginal

/-- The window `w X` is the integer interval `[X+1, (51X-1)/50]`. -/
lemma window_eq (X : ℕ) :
    (Finset.range (2 * X + 1)).filter (fun n => X < n ∧ 50 * n < 51 * X)
      = Finset.Icc (X + 1) ((51 * X - 1) / 50) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨-, hXn, h50⟩
    refine ⟨by omega, ?_⟩
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 50)]
    omega
  · rintro ⟨h1, h2⟩
    have hle : n * 50 ≤ 51 * X - 1 := by
      have := Nat.le_div_iff_mul_le (k := 50) (x := n) (y := 51 * X - 1) (by norm_num)
      exact this.mp h2
    have h2X : (51 * X - 1) / 50 ≤ 2 * X := by
      have h : (51 * X - 1) / 50 < 2 * X + 1 := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 50)]
        omega
      omega
    refine ⟨?_, by omega, by omega⟩
    omega

/-- The canonical representative of the class `c` inside `[x, x+q-1]`. -/
lemma class_rep_spec {q x c : ℕ} (hq : 0 < q) (hc : c < q) :
    (x + ((c + q - x % q) % q)) % q = c := by
  set r := (c + q - x % q) % q with hr
  have hxq : x % q < q := Nat.mod_lt _ hq
  have hxle : x % q ≤ c + q := by omega
  have hsum : x % q + (c + q - x % q) = c + q := by omega
  have hr_mod : r ≡ (c + q - x % q) [MOD q] := by
    rw [hr]
    exact Nat.mod_modEq (c + q - x % q) q
  have hx_mod : x ≡ x % q [MOD q] := (Nat.mod_modEq x q).symm
  have hadd : x + r ≡ x % q + (c + q - x % q) [MOD q] := Nat.ModEq.add hx_mod hr_mod
  change (x + r) % q = (x % q + (c + q - x % q)) % q at hadd
  rw [hadd, hsum]
  rw [Nat.add_mod, Nat.mod_eq_of_lt hc, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt hc]

/-- The largest representative of the class `b` at most `N`. -/
lemma class_rep_max_spec {q N b : ℕ} (hq : 0 < q) (hb : b < q) (hNb : b ≤ N) :
    (N - ((N + q - b) % q)) % q = b := by
  set r := (N + q - b) % q with hr
  have hrlt : r < q := Nat.mod_lt _ hq
  have h1 : q * ((N + q - b) / q) + r = N + q - b := Nat.div_add_mod (N + q - b) q
  have hN : N % q + q * (N / q) = N := Nat.mod_add_div N q
  have hk : 1 ≤ (N + q - b) / q := by
    rw [Nat.le_div_iff_mul_le hq]
    omega
  have hqeq : q * ((N + q - b) / q) = q * ((N + q - b) / q - 1) + q := by
    obtain ⟨K', hK'⟩ : ∃ K', (N + q - b) / q = K' + 1 :=
      ⟨(N + q - b) / q - 1, by omega⟩
    rw [hK']
    simp only [Nat.add_sub_cancel]
    ring
  have hNr : N - r = q * ((N + q - b) / q - 1) + b := by omega
  have hkey : N - r = b + ((N + q - b) / q - 1) * q := by
    rw [hNr]; ring
  rw [hkey, Nat.mul_comm ((N + q - b) / q - 1) q, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hb]

lemma coprime_of_mod {n q : ℕ} (h : Nat.Coprime (n % q) q) : Nat.Coprime n q := by
  rw [Nat.coprime_iff_gcd_eq_one] at *
  rw [Nat.gcd_comm]
  rw [Nat.gcd_rec]
  exact h

lemma coprime_mod_of_coprime {n q : ℕ} (h : Nat.Coprime n q) : Nat.Coprime (n % q) q := by
  rw [Nat.coprime_iff_gcd_eq_one] at *
  have h' : q.gcd n = 1 := by rwa [Nat.gcd_comm]
  rw [Nat.gcd_rec] at h'
  exact h'

/-- Sum of a two-point indicator over a finset. -/
lemma sum_two_ite (s : Finset ℕ) (x y : ℕ) (hxy : x ≠ y) :
    (∑ n ∈ s, (if n = x ∨ n = y then (1 : ℝ) else 0))
      = (if x ∈ s then 1 else 0) + (if y ∈ s then 1 else 0) := by
  have hsplit : ∀ n : ℕ, (if n = x ∨ n = y then (1 : ℝ) else 0)
      = (if n = x then (1 : ℝ) else 0) + (if n = y then (1 : ℝ) else 0) := by
    intro n
    by_cases hx : n = x
    · subst hx
      simp [hxy]
    · by_cases hy : n = y
      · subst hy
        simp [hx, Ne.symm hxy]
      · simp [hx, hy]
  calc (∑ n ∈ s, (if n = x ∨ n = y then (1 : ℝ) else 0))
      = ∑ n ∈ s, ((if n = x then (1 : ℝ) else 0) + (if n = y then (1 : ℝ) else 0)) :=
        Finset.sum_congr rfl (fun n _ => hsplit n)
    _ = (∑ n ∈ s, (if n = x then (1 : ℝ) else 0))
          + ∑ n ∈ s, (if n = y then (1 : ℝ) else 0) := Finset.sum_add_distrib
    _ = (if x ∈ s then 1 else 0) + (if y ∈ s then 1 else 0) := by
        rw [Finset.sum_ite_eq' s x (fun _ => (1 : ℝ)),
          Finset.sum_ite_eq' s y (fun _ => (1 : ℝ))]

theorem wheel_marginal_main :
    let w := fun (X : ℕ) => (Finset.range (2 * X + 1)).filter (fun n => X < n ∧ 50 * n < 51 * X);
    ∀ (q X : ℕ), 0 < q → 200 * (q + 1) ≤ X →
      (∃ a : ℕ, a < q ∧ Nat.Coprime a q ∧ Nat.Coprime (a + 2) q) →
      (∃ f g : ℕ → ℝ,
        (∀ n, (f n = 0 ∨ f n = 1) ∧ (g n = 0 ∨ g n = 1) ∧
          (¬ (n ∈ w X ∧ Nat.Coprime n q) → f n = 0 ∧ g n = 0)) ∧
        (∀ a : ℕ, a < q → ((w X).filter (fun n => n % q = a)).sum f
          = ((w X).filter (fun n => n % q = a)).sum g) ∧
        (w X).sum (fun n => f n * f (n + 2)) = 1 ∧
        (w X).sum (fun n => g n * g (n + 2)) = 0) := by
  dsimp only
  intro q X hq hX ha
  obtain ⟨a, ha_lt, ha_cop, ha2_cop⟩ := ha
  -- abbreviations for the two representatives
  set N := (51 * X - 1) / 50 with hN
  have hN_ge : X + 4 * q + 3 ≤ N := by
    rw [hN, Nat.le_div_iff_mul_le (by norm_num : 0 < 50)]
    omega
  have hN_le : N ≤ 2 * X := by
    have h : N < 2 * X + 1 := by
      rw [hN, Nat.div_lt_iff_lt_mul (by norm_num : 0 < 50)]
      omega
    omega
  set b := (a + 2) % q with hb_def
  have hb_lt : b < q := Nat.mod_lt _ hq
  have hb_le : b ≤ N := by omega
  set m := X + 1 + ((a + q - (X + 1) % q) % q) with hm_def
  have hm_mod : m % q = a := by
    rw [hm_def]
    exact class_rep_spec hq ha_lt
  set n2 := N - ((N + q - b) % q) with hn2_def
  have hn2_mod : n2 % q = b := by
    rw [hn2_def]
    exact class_rep_max_spec hq hb_lt hb_le
  have hm_ge : X + 1 ≤ m := by omega
  have hm_le : m ≤ X + q := by
    rw [hm_def]
    have : (a + q - (X + 1) % q) % q < q := Nat.mod_lt _ hq
    omega
  have hn2_ge : N - q + 1 ≤ n2 := by
    rw [hn2_def]
    have : (N + q - b) % q < q := Nat.mod_lt _ hq
    omega
  have hn2_far : m + 2 + 1 ≤ n2 := by omega
  -- membership facts
  set W : Finset ℕ := (Finset.range (2 * X + 1)).filter (fun n => X < n ∧ 50 * n < 51 * X) with hW
  have hW_eq : W = Finset.Icc (X + 1) N := by
    rw [hW, window_eq, ← hN]
  have hm_mem : m ∈ W := by
    rw [hW_eq]; exact Finset.mem_Icc.mpr ⟨hm_ge, by omega⟩
  have hm2_mem : m + 2 ∈ W := by
    rw [hW_eq]; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hn2_mem : n2 ∈ W := by
    rw [hW_eq]; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  -- coprimality
  have hm_cop : Nat.Coprime m q := coprime_of_mod (by rw [hm_mod]; exact ha_cop)
  have hm2_mod : (m + 2) % q = b := by
    have hL : (m + 2) % q = (a % q + 2 % q) % q := by
      rw [Nat.add_mod, hm_mod, Nat.add_mod, Nat.mod_mod]
    have h1 : (m + 2) % q = (a + 2) % q := by
      rw [hL, Nat.add_mod a 2 q]
    rw [h1, hb_def]
  have hm2_cop : Nat.Coprime (m + 2) q := coprime_of_mod (by rw [hm2_mod]; exact coprime_mod_of_coprime ha2_cop)
  have hn2_cop : Nat.Coprime n2 q := coprime_of_mod (by rw [hn2_mod]; exact coprime_mod_of_coprime ha2_cop)
  -- define the weights
  set f : ℕ → ℝ := fun n => if n = m ∨ n = m + 2 then 1 else 0 with hf
  set g : ℕ → ℝ := fun n => if n = m ∨ n = n2 then 1 else 0 with hg
  refine ⟨f, g, ?_, ?_, ?_, ?_⟩
  · intro n
    refine ⟨?_, ?_, ?_⟩
    · by_cases h : n = m ∨ n = m + 2 <;> simp [hf, h]
    · by_cases h : n = m ∨ n = n2 <;> simp [hg, h]
    · intro hn
      constructor
      · by_contra hne
        have hcond : n = m ∨ n = m + 2 := by
          by_contra hc
          simp [hf, hc] at hne
        rcases hcond with rfl | rfl
        · exact hn ⟨hm_mem, hm_cop⟩
        · exact hn ⟨hm2_mem, hm2_cop⟩
      · by_contra hne
        have hcond : n = m ∨ n = n2 := by
          by_contra hc
          simp [hg, hc] at hne
        rcases hcond with rfl | rfl
        · exact hn ⟨hm_mem, hm_cop⟩
        · exact hn ⟨hn2_mem, hn2_cop⟩
  · intro a' ha'_lt
    -- the class-a' slice of the window
    set S : Finset ℕ := W.filter (fun n => n % q = a') with hS
    have hmS : m ∈ S ↔ a' = a := by
      rw [hS, Finset.mem_filter]
      constructor
      · rintro ⟨-, h⟩; omega
      · intro h; subst h; exact ⟨hm_mem, hm_mod⟩
    have hm2S : m + 2 ∈ S ↔ a' = b := by
      rw [hS, Finset.mem_filter]
      constructor
      · rintro ⟨-, h⟩
        rw [hm2_mod] at h
        omega
      · intro h; subst h; exact ⟨hm2_mem, hm2_mod⟩
    have hn2S : n2 ∈ S ↔ a' = b := by
      rw [hS, Finset.mem_filter]
      constructor
      · rintro ⟨-, h⟩
        rw [hn2_mod] at h
        omega
      · intro h; subst h; exact ⟨hn2_mem, hn2_mod⟩
    have hf_sum : (∑ n ∈ S, f n) = (if a' = a then 1 else 0) + (if a' = b then 1 else 0) := by
      have : (∑ n ∈ S, f n)
          = (if m ∈ S then 1 else 0) + (if m + 2 ∈ S then 1 else 0) := by
        rw [hf]
        exact sum_two_ite S m (m + 2) (by omega)
      rw [this]
      simp only [hmS, hm2S]
    have hg_sum : (∑ n ∈ S, g n) = (if a' = a then 1 else 0) + (if a' = b then 1 else 0) := by
      have : (∑ n ∈ S, g n)
          = (if m ∈ S then 1 else 0) + (if n2 ∈ S then 1 else 0) := by
        rw [hg]
        exact sum_two_ite S m n2 (by omega)
      rw [this]
      simp only [hmS, hn2S]
    rw [hf_sum, hg_sum]
  · -- twin correlation of f is 1 (only the pair (m, m+2) contributes)
    have hterm : ∀ n ∈ W, f n * f (n + 2) = (if n = m then (1 : ℝ) else 0) := by
      intro n _
      by_cases hnm : n = m
      · subst hnm
        have h1 : f m = 1 := by simp [hf]
        have h2 : f (m + 2) = 1 := by simp [hf, show m + 2 ≠ m by omega]
        rw [h1, h2]
        norm_num
      · by_cases hnm2 : n = m + 2
        · subst hnm2
          have h2 : f (m + 2) = 1 := by simp [hf, show m + 2 ≠ m by omega]
          have h3 : f (m + 4) = 0 := by
            simp [hf, show m + 4 ≠ m by omega, show m + 4 ≠ m + 2 by omega]
          rw [h2, h3]
          simp [show m + 2 ≠ m by omega]
        · have h0 : f n = 0 := by simp [hf, hnm, hnm2]
          rw [h0]
          simp [hnm]
    calc (∑ n ∈ W, f n * f (n + 2))
        = ∑ n ∈ W, (if n = m then (1 : ℝ) else 0) := Finset.sum_congr rfl hterm
      _ = (if m ∈ W then (1 : ℝ) else 0) := Finset.sum_ite_eq' W m (fun _ => (1 : ℝ))
      _ = 1 := by rw [if_pos hm_mem]
  · -- twin correlation of g is 0 (no two support points differ by 2)
    have hterm : ∀ n ∈ W, g n * g (n + 2) = 0 := by
      intro n _
      by_cases hnm : n = m
      · subst hnm
        have h1 : g (m + 2) = 0 := by
          simp [hg, show m + 2 ≠ m by omega, show m + 2 ≠ n2 by omega]
        rw [h1]
        ring
      · by_cases hn2 : n = n2
        · subst hn2
          have h1 : g (n2 + 2) = 0 := by
            simp [hg, show n2 + 2 ≠ m by omega, show n2 + 2 ≠ n2 by omega]
          rw [h1]
          ring
        · have h0 : g n = 0 := by simp [hg, hnm, hn2]
          rw [h0]
          ring
    exact Finset.sum_eq_zero hterm

end TwinWheelMarginal

open TwinWheelMarginal

theorem Conjectures.TwinPrimes.WheelMarginalCounterexample :
  let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); ∀ (q X : ℕ), 0 < q → 200*(q+1) ≤ X → (∃ a : ℕ, a < q ∧ Nat.Coprime a q ∧ Nat.Coprime (a+2) q) → (∃ f g : ℕ → ℝ, (∀ n, (f n=0 ∨ f n=1) ∧ (g n=0 ∨ g n=1) ∧ (¬ (n ∈ w X ∧ Nat.Coprime n q) → f n=0 ∧ g n=0)) ∧ (∀ a : ℕ, a < q → ((w X).filter (fun n => n % q=a)).sum f = ((w X).filter (fun n => n % q=a)).sum g) ∧ (w X).sum (fun n => f n * f (n+2))=1 ∧ (w X).sum (fun n => g n * g (n+2))=0)
  := TwinWheelMarginal.wheel_marginal_main
