import Mathlib

namespace PEqualNP.Outside

private lemma qp_dvd_mod_sq_add_one {q n : ℕ} : q ∣ n ^ 2 + 1 ↔ q ∣ (n % q) ^ 2 + 1 := by
  let k := n / q
  let r := n % q
  have hdiv : n = q * k + r := (Nat.div_add_mod n q).symm
  have heq : n ^ 2 + 1 = q * (q * k ^ 2 + 2 * k * r) + (r ^ 2 + 1) := by
    calc
      n ^ 2 + 1 = (q * k + r) ^ 2 + 1 := by rw [hdiv]
      _ = q * (q * k ^ 2 + 2 * k * r) + (r ^ 2 + 1) := by ring
  change q ∣ n ^ 2 + 1 ↔ q ∣ r ^ 2 + 1
  rw [heq]
  exact Nat.dvd_add_right (dvd_mul_right q _)

private lemma qp_mono_filter_Ioc (P : ℕ → Prop) [DecidablePred P]
    (hmono : ∀ m n : ℕ, m ≤ n → P m → P n) (a d : ℕ) :
    ∃ A : ℕ, A ≤ a + d + 1 ∧ (Finset.Ioc a (a + d)).filter P = Finset.Ico A (a + d + 1) := by
  induction d with
  | zero =>
    refine ⟨a + 1, le_rfl, ?_⟩
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ico]
    omega
  | succ k ih =>
    by_cases htop : P (a + k + 1)
    · obtain ⟨A, hAle, hEq⟩ := ih
      refine ⟨A, by omega, ?_⟩
      ext n
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ico]
      constructor
      · rintro ⟨⟨hn1, hn2⟩, hPn⟩
        by_cases hnk : n ≤ a + k
        · have hmem : n ∈ (Finset.Ioc a (a + k)).filter P :=
            Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hn1, hnk⟩, hPn⟩
          rw [hEq] at hmem
          have hIco := Finset.mem_Ico.mp hmem
          omega
        · omega
      · intro hn
        have hnk_or : n ≤ a + k ∨ n = a + k + 1 := by omega
        rcases hnk_or with hnk | rfl
        · have hmem : n ∈ Finset.Ico A (a + k + 1) := Finset.mem_Ico.mpr ⟨hn.1, by omega⟩
          rw [← hEq] at hmem
          have hf := Finset.mem_filter.mp hmem
          have hIoc := Finset.mem_Ioc.mp hf.1
          exact ⟨⟨hIoc.1, by omega⟩, hf.2⟩
        · exact ⟨⟨by omega, by omega⟩, htop⟩
    · refine ⟨a + k + 2, le_rfl, ?_⟩
      ext n
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ico]
      constructor
      · rintro ⟨⟨_, hn2⟩, hPn⟩
        exfalso
        exact htop (hmono n (a + k + 1) (by omega) hPn)
      · intro hn
        omega

private lemma qp_card_mod_Ico_step {q r : ℕ} (hq : 0 < q) (hr : r < q) (B : ℕ) :
    ((Finset.Ico B (B + q)).filter (fun n => n % q = r)).card = 1 := by
  let b := B % q
  have hb_lt : b < q := Nat.mod_lt B hq
  have hB_eq : q * (B / q) + b = B := Nat.div_add_mod B q
  let k0 := if b ≤ r then B / q else B / q + 1
  let n0 := q * k0 + r
  have hsingleton : (Finset.Ico B (B + q)).filter (fun n => n % q = r) = {n0} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hn1, hn2⟩, hn_mod⟩
      have hn_eq : q * (n / q) + r = n := by
        have hd := Nat.div_add_mod n q
        rw [hn_mod] at hd
        exact hd
      have hn0_bounds : B ≤ n0 ∧ n0 < B + q := by
        dsimp only [n0, k0]
        by_cases hbr : b ≤ r
        · simp only [hbr, ↓reduceIte]
          omega
        · simp only [hbr, ↓reduceIte]
          have hmul : q * (B / q + 1) = q * (B / q) + q := by ring
          omega
      have hk_eq : n / q = k0 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hle : q * (n / q + 1) ≤ q * k0 := Nat.mul_le_mul_left q hlt
          have hmul : q * (n / q + 1) = q * (n / q) + q := by ring
          have hn0_def : n0 = q * k0 + r := rfl
          omega
        · have hle : q * (k0 + 1) ≤ q * (n / q) := Nat.mul_le_mul_left q hgt
          have hmul : q * (k0 + 1) = q * k0 + q := by ring
          have hn0_def : n0 = q * k0 + r := rfl
          omega
      have hn0_def : n0 = q * k0 + r := rfl
      rw [← hn_eq, hk_eq, hn0_def]
    · rintro rfl
      refine ⟨?_, ?_⟩
      · dsimp only [n0, k0]
        by_cases hbr : b ≤ r
        · simp only [hbr, ↓reduceIte]
          omega
        · simp only [hbr, ↓reduceIte]
          have hmul : q * (B / q + 1) = q * (B / q) + q := by ring
          omega
      · dsimp only [n0]
        rw [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr]
  rw [hsingleton, Finset.card_singleton]

private lemma qp_card_mod_Ico_mul {q r : ℕ} (hq : 0 < q) (hr : r < q) (A k : ℕ) :
    ((Finset.Ico A (A + q * k)).filter (fun n => n % q = r)).card = k := by
  induction k with
  | zero => simp
  | succ m ih =>
    let M := A + q * m
    have hunion : Finset.Ico A (A + q * (m + 1)) =
        Finset.Ico A M ∪ Finset.Ico M (M + q) := by
      have hmul : A + q * (m + 1) = M + q := by
        dsimp only [M]
        ring
      rw [hmul]
      ext n
      simp only [Finset.mem_union, Finset.mem_Ico]
      have hAM : A ≤ M := by
        dsimp only [M]
        omega
      omega
    have hdisj : Disjoint ((Finset.Ico A M).filter (fun n => n % q = r))
        ((Finset.Ico M (M + q)).filter (fun n => n % q = r)) := by
      rw [Finset.disjoint_left]
      intro n hn1 hn2
      simp only [Finset.mem_filter, Finset.mem_Ico] at hn1 hn2
      omega
    rw [hunion, Finset.filter_union, Finset.card_union_of_disjoint hdisj, ih,
      qp_card_mod_Ico_step hq hr M]

private lemma qp_card_mod_Ico_abs {q r : ℕ} (hq : 0 < q) (hr : r < q) (A L : ℕ) :
    |(((Finset.Ico A (A + L)).filter (fun n => n % q = r)).card : ℝ) -
        (L : ℝ) / (q : ℝ)| ≤ 1 := by
  let k := L / q
  let rem := L % q
  have hL_div : q * k + rem = L := Nat.div_add_mod L q
  have hrem_lt : rem < q := Nat.mod_lt L hq
  let M := A + q * k
  have hunion : Finset.Ico A (A + L) = Finset.Ico A M ∪ Finset.Ico M (M + rem) := by
    have hML : A + L = M + rem := by
      dsimp only [M]
      omega
    rw [hML]
    ext n
    simp only [Finset.mem_union, Finset.mem_Ico]
    have hAM : A ≤ M := by
      dsimp only [M]
      omega
    omega
  have hdisj : Disjoint ((Finset.Ico A M).filter (fun n => n % q = r))
      ((Finset.Ico M (M + rem)).filter (fun n => n % q = r)) := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    simp only [Finset.mem_filter, Finset.mem_Ico] at hn1 hn2
    omega
  let c := ((Finset.Ico A (A + L)).filter (fun n => n % q = r)).card
  have hc_split : c = k + ((Finset.Ico M (M + rem)).filter (fun n => n % q = r)).card := by
    dsimp only [c]
    rw [hunion, Finset.filter_union, Finset.card_union_of_disjoint hdisj,
      qp_card_mod_Ico_mul hq hr A k]
  have hsub : (Finset.Ico M (M + rem)).filter (fun n => n % q = r) ⊆
      (Finset.Ico M (M + q)).filter (fun n => n % q = r) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ico] at hn ⊢
    exact ⟨⟨hn.1.1, by omega⟩, hn.2⟩
  have hrem_card : ((Finset.Ico M (M + rem)).filter (fun n => n % q = r)).card ≤ 1 := by
    calc
      ((Finset.Ico M (M + rem)).filter (fun n => n % q = r)).card
        ≤ ((Finset.Ico M (M + q)).filter (fun n => n % q = r)).card := Finset.card_le_card hsub
      _ = 1 := qp_card_mod_Ico_step hq hr M
  have hc_lo : k ≤ c := by omega
  have hc_hi : c ≤ k + 1 := by omega
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hq_ne : (q : ℝ) ≠ 0 := ne_of_gt hq_pos
  have hc_lo_r : (k : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc_lo
  have hc_hi_r : (c : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast hc_hi
  have hL_r : (q : ℝ) * (k : ℝ) + (rem : ℝ) = (L : ℝ) := by exact_mod_cast hL_div
  have hrem_nonneg : (0 : ℝ) ≤ (rem : ℝ) := Nat.cast_nonneg rem
  have hrem_le : (rem : ℝ) ≤ (q : ℝ) := by exact_mod_cast le_of_lt hrem_lt
  have hmul_lo : (q : ℝ) * (k : ℝ) ≤ (q : ℝ) * (c : ℝ) :=
    mul_le_mul_of_nonneg_left hc_lo_r (le_of_lt hq_pos)
  have hmul_hi : (q : ℝ) * (c : ℝ) ≤ (q : ℝ) * ((k : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hc_hi_r (le_of_lt hq_pos)
  have hdiff : (c : ℝ) - (L : ℝ) / (q : ℝ) = ((q : ℝ) * (c : ℝ) - (L : ℝ)) / (q : ℝ) := by
    field_simp [hq_ne]
  change |(c : ℝ) - (L : ℝ) / (q : ℝ)| ≤ 1
  rw [hdiff, abs_div, abs_of_pos hq_pos, div_le_one hq_pos, abs_le]
  constructor <;> linarith

private lemma qp_moving_window_gen (E1 E2 x q : ℕ) (hq : 0 < q) :
    let block := fun x : ℕ => Finset.Ioc x (2 * x)
    let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r ^ 2 + a)
    let window := fun x p : ℕ => (block x).filter (fun n => p ^ E1 ≤ n ^ E2)
    let countHits := fun a x p : ℕ => ((window x p).filter (fun n => p ∣ n ^ 2 + a)).card
    |(countHits 1 x q : ℝ) - ((window x q).card : ℝ) * ((roots 1 q).card : ℝ) / q| ≤
      ((roots 1 q).card : ℝ) := by
  intro block roots window countHits
  have hmono : ∀ m n : ℕ, m ≤ n → q ^ E1 ≤ m ^ E2 → q ^ E1 ≤ n ^ E2 := by
    intro m n hmn hm
    exact le_trans hm (Nat.pow_le_pow_left hmn E2)
  obtain ⟨A, hAle, hW_eq⟩ := qp_mono_filter_Ioc (fun n => q ^ E1 ≤ n ^ E2) hmono x x
  have hW : window x q = Finset.Ico A (x + x + 1) := by
    dsimp only [window, block]
    rw [Nat.two_mul x]
    exact hW_eq
  let L := (window x q).card
  have hL_eq : L = x + x + 1 - A := by
    dsimp only [L]
    rw [hW]
    simp
  have hAL : A + L = x + x + 1 := by omega
  have hW_Ico : window x q = Finset.Ico A (A + L) := by
    rw [hW, hAL]
  have hcount : countHits 1 x q =
      ∑ r ∈ roots 1 q, ((window x q).filter (fun n => n % q = r)).card := by
    dsimp only [countHits]
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases hd : q ∣ n ^ 2 + 1
    · have hd_mod : q ∣ (n % q) ^ 2 + 1 := qp_dvd_mod_sq_add_one.mp hd
      have hmem : n % q ∈ roots 1 q :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt n hq), hd_mod⟩
      simp only [hd, ↓reduceIte, Finset.sum_ite_eq, hmem]
    · simp only [hd, ↓reduceIte]
      symm
      refine Finset.sum_eq_zero (fun r hr => ?_)
      have hne : n % q ≠ r := by
        intro heq
        have hr_dvd : q ∣ r ^ 2 + 1 := (Finset.mem_filter.mp hr).2
        rw [← heq] at hr_dvd
        exact hd (qp_dvd_mod_sq_add_one.mpr hr_dvd)
      simp only [hne, ↓reduceIte]
  have hsum_diff : (countHits 1 x q : ℝ) - (L : ℝ) * ((roots 1 q).card : ℝ) / (q : ℝ) =
      ∑ r ∈ roots 1 q,
        ((((window x q).filter (fun n => n % q = r)).card : ℝ) - (L : ℝ) / (q : ℝ)) := by
    rw [Finset.sum_sub_distrib, hcount]
    push_cast
    simp only [Finset.sum_const, nsmul_eq_mul]
    congr 1
    ring
  change |(countHits 1 x q : ℝ) - (L : ℝ) * ((roots 1 q).card : ℝ) / (q : ℝ)| ≤
      ((roots 1 q).card : ℝ)
  rw [hsum_diff]
  calc
    |∑ r ∈ roots 1 q,
        ((((window x q).filter (fun n => n % q = r)).card : ℝ) - (L : ℝ) / (q : ℝ))|
      ≤ ∑ r ∈ roots 1 q,
          |(((window x q).filter (fun n => n % q = r)).card : ℝ) - (L : ℝ) / (q : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ roots 1 q, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun r hr => ?_)
        have hr_lt : r < q := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
        rw [hW_Ico]
        exact qp_card_mod_Ico_abs hq hr_lt A L
    _ = ((roots 1 q).card : ℝ) := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

theorem L_quadratic_primes_levent_moving_window_floor :
    let block := fun x : ℕ => Finset.Ioc x (2*x); let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a); let window := fun x p : ℕ => (block x).filter (fun n => p^100000 ≤ n^132301); let countHits := fun a x p : ℕ => ((window x p).filter (fun n => p ∣ n^2+a)).card; ∀ x q : ℕ, 0<q → |(countHits 1 x q : ℝ) - ((window x q).card : ℝ)*((roots 1 q).card : ℝ)/q| ≤ ((roots 1 q).card : ℝ) := by
  intro block roots window countHits x q hq
  exact qp_moving_window_gen 100000 132301 x q hq

end PEqualNP.Outside
