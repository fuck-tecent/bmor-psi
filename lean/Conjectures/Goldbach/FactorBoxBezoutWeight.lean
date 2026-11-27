import Mathlib

private theorem aux_gcd_pos {a b : ℤ} (ha : 0 < a) (_hb : 0 < b) :
    (0:ℤ) < (Int.gcd a b : ℤ) := by
  have h1 : (0:ℕ) < Int.gcd a b := by
    rw [Int.gcd_def]
    exact Nat.gcd_pos_of_pos_left b.natAbs (Int.natAbs_pos.mpr (by omega))
  exact_mod_cast h1

private theorem aux_coprime_div {a b : ℤ} (ha : 0 < a) (_hb : 0 < b) :
    IsCoprime (b / (Int.gcd a b : ℤ)) (a / (Int.gcd a b : ℤ)) := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
  exact Int.gcd_div_gcd_div_gcd (by
    have h1 : (0:ℕ) < Int.gcd a b := by
      rw [Int.gcd_def]
      exact Nat.gcd_pos_of_pos_left b.natAbs (Int.natAbs_pos.mpr (by omega))
    exact_mod_cast h1)

theorem Conjectures.Goldbach.FactorBoxBezoutWeight :
∀ (a b n l r u v : ℤ) (w : ℤ → ℤ → ℝ), 0 < a → 0 < b →
let g : ℤ := Int.gcd a b
let h := b / g
let k := a / g
let x := (n / g) * Int.gcdA a b
let y := (n / g) * Int.gcdB a b
let lo := max (-((x-l) / h)) (-((v-y) / k))
let hi := min ((r-x) / h) ((y-u) / k)
let box := ((Finset.Icc l r).product (Finset.Icc u v)).filter (fun z => a*z.1 + b*z.2 = n)
(∑ z ∈ box, w z.1 z.2) = if g ∣ n then ∑ i ∈ Finset.Icc lo hi, w (x+h*i) (y-k*i) else 0 := by
  intro a b n l r u v w ha hb
  dsimp only
  set g : ℤ := ↑(Int.gcd a b) with hg
  set h : ℤ := b / g with hh
  set k : ℤ := a / g with hk
  set x : ℤ := n / g * Int.gcdA a b with hx
  set y : ℤ := n / g * Int.gcdB a b with hy
  set lo : ℤ := max (-((x - l) / h)) (-((v - y) / k)) with hlo
  set hi : ℤ := min ((r - x) / h) ((y - u) / k) with hhi
  set box : Finset (ℤ × ℤ) :=
    ((Finset.Icc l r).product (Finset.Icc u v)).filter (fun z => a * z.1 + b * z.2 = n)
    with hbox
  have hg0 : (0:ℤ) < g := by rw [hg]; exact aux_gcd_pos ha hb
  have hgne : g ≠ 0 := ne_of_gt hg0
  have hga : g ∣ a := by rw [hg]; exact Int.gcd_dvd_left a b
  have hgb : g ∣ b := by rw [hg]; exact Int.gcd_dvd_right a b
  have hhg : h * g = b := by rw [hh]; exact Int.ediv_mul_cancel hgb
  have hkg : k * g = a := by rw [hk]; exact Int.ediv_mul_cancel hga
  have hgh : g * h = b := by rw [mul_comm]; exact hhg
  have hgk : g * k = a := by rw [mul_comm]; exact hkg
  have hh0 : (0:ℤ) < h := by nlinarith
  have hk0 : (0:ℤ) < k := by nlinarith
  have hhne : h ≠ 0 := ne_of_gt hh0
  have hcop : IsCoprime h k := by
    rw [hh, hk, hg]
    exact aux_coprime_div ha hb
  have hak : a * h = b * k := by
    calc a * h = (g * k) * h := by rw [hgk]
      _ = (g * h) * k := by ring
      _ = b * k := by rw [hgh]
  have hbez : g = a * Int.gcdA a b + b * Int.gcdB a b := by
    rw [hg]; exact Int.gcd_eq_gcd_ab a b
  -- the four interval characterisations
  have hI1 : ∀ i : ℤ, -((x - l) / h) ≤ i ↔ l ≤ x + h * i := by
    intro i
    constructor
    · intro h1
      have h2 : -i ≤ (x - l) / h := by omega
      have h3 := (Int.le_ediv_iff_mul_le hh0).mp h2
      linear_combination h3
    · intro h1
      have h2 : -i * h ≤ x - l := by linear_combination h1
      have h3 : -i ≤ (x - l) / h := (Int.le_ediv_iff_mul_le hh0).mpr h2
      omega
  have hI2 : ∀ i : ℤ, -((v - y) / k) ≤ i ↔ y - k * i ≤ v := by
    intro i
    constructor
    · intro h1
      have h2 : -i ≤ (v - y) / k := by omega
      have h3 := (Int.le_ediv_iff_mul_le hk0).mp h2
      linear_combination h3
    · intro h1
      have h2 : -i * k ≤ v - y := by linear_combination h1
      have h3 : -i ≤ (v - y) / k := (Int.le_ediv_iff_mul_le hk0).mpr h2
      omega
  have hI3 : ∀ i : ℤ, i ≤ (r - x) / h ↔ x + h * i ≤ r := by
    intro i
    constructor
    · intro h1
      have h3 := (Int.le_ediv_iff_mul_le hh0).mp h1
      linear_combination h3
    · intro h1
      have h2 : i * h ≤ r - x := by linear_combination h1
      exact (Int.le_ediv_iff_mul_le hh0).mpr h2
  have hI4 : ∀ i : ℤ, i ≤ (y - u) / k ↔ u ≤ y - k * i := by
    intro i
    constructor
    · intro h1
      have h3 := (Int.le_ediv_iff_mul_le hk0).mp h1
      linear_combination h3
    · intro h1
      have h2 : i * k ≤ y - u := by linear_combination h1
      exact (Int.le_ediv_iff_mul_le hk0).mpr h2
  split_ifs with hgn
  · -- compatible fibre
    have hxy : a * x + b * y = n := by
      have e1 : a * x + b * y = n / g * g := by
        rw [hx, hy, hbez]; ring
      rw [e1]; exact Int.ediv_mul_cancel hgn
    have hfwd : ∀ i : ℤ, lo ≤ i → i ≤ hi → (x + h * i, y - k * i) ∈ box := by
      intro i hil hih
      rw [hlo] at hil
      rw [hhi] at hih
      rw [hbox]
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_Icc.mpr
          ⟨(hI1 i).mp (le_trans (le_max_left _ _) hil),
           (hI3 i).mp (le_trans hih (min_le_left _ _))⟩
      · exact Finset.mem_Icc.mpr
          ⟨(hI4 i).mp (le_trans hih (min_le_right _ _)),
           (hI2 i).mp (le_trans (le_max_right _ _) hil)⟩
      · have e2 : a * (x + h * i) + b * (y - k * i)
            = a * x + b * y + (a * h - b * k) * i := by ring
        rw [e2, hak, hxy]; ring
    have hbwd : ∀ z ∈ box, ∃ i : ℤ, lo ≤ i ∧ i ≤ hi ∧ z = (x + h * i, y - k * i) := by
      intro z hz
      rw [hbox] at hz
      obtain ⟨hzmem, hzeq⟩ := Finset.mem_filter.mp hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_product.mp hzmem
      rw [Finset.mem_Icc] at hz1 hz2
      have hkey : k * (z.1 - x) = h * (y - z.2) := by
        have e1 : a * (z.1 - x) = b * (y - z.2) := by
          have e2 : a * (z.1 - x) + b * (z.2 - y) = a * z.1 + b * z.2 - (a * x + b * y) := by
            ring
          rw [hzeq, hxy] at e2
          linarith
        have s1 : g * (k * (z.1 - x)) = a * (z.1 - x) := by
          calc g * (k * (z.1 - x)) = (g * k) * (z.1 - x) := by ring
            _ = a * (z.1 - x) := by rw [hgk]
        have s2 : g * (h * (y - z.2)) = b * (y - z.2) := by
          calc g * (h * (y - z.2)) = (g * h) * (y - z.2) := by ring
            _ = b * (y - z.2) := by rw [hgh]
        have e3 : g * (k * (z.1 - x)) = g * (h * (y - z.2)) := by
          rw [s1, s2]; exact e1
        exact mul_left_cancel₀ hgne e3
      have hdvd : h ∣ (z.1 - x) := by
        have h2 : h ∣ (z.1 - x) * k := by
          rw [mul_comm]
          exact ⟨y - z.2, hkey⟩
        exact IsCoprime.dvd_of_dvd_mul_right hcop h2
      obtain ⟨i, histep⟩ : ∃ i : ℤ, z.1 - x = h * i := hdvd
      have hz1' : z.1 = x + h * i := by omega
      have hz2' : z.2 = y - k * i := by
        have e4 : h * (y - z.2) = h * (k * i) := by
          rw [← hkey, histep]; ring
        have e5 := mul_left_cancel₀ hhne e4
        omega
      refine ⟨i, ?_, ?_, ?_⟩
      · rw [hlo]
        exact max_le ((hI1 i).mpr (by rw [← hz1']; exact hz1.1))
          ((hI2 i).mpr (by rw [← hz2']; exact hz2.2))
      · rw [hhi]
        exact le_min ((hI3 i).mpr (by rw [← hz1']; exact hz1.2))
          ((hI4 i).mpr (by rw [← hz2']; exact hz2.1))
      · rw [Prod.ext_iff]
        exact ⟨hz1', hz2'⟩
    have hboxeq : box = (Finset.Icc lo hi).image (fun i => (x + h * i, y - k * i)) := by
      apply Finset.ext
      intro z
      constructor
      · intro hz
        obtain ⟨i, hil, hih, rfl⟩ := hbwd z hz
        exact Finset.mem_image.mpr ⟨i, Finset.mem_Icc.mpr ⟨hil, hih⟩, rfl⟩
      · intro hz
        obtain ⟨i, him, rfl⟩ := Finset.mem_image.mp hz
        exact hfwd i (Finset.mem_Icc.mp him).1 (Finset.mem_Icc.mp him).2
    rw [hboxeq, Finset.sum_image]
    intro i _ j _ hij
    have h4 : h * i = h * j := by
      have c1 : x + h * i = x + h * j := congrArg Prod.fst hij
      linarith
    exact mul_left_cancel₀ hhne h4
  · -- incompatible fibre
    have hboxe : box = ∅ := by
      apply Finset.ext
      intro z
      constructor
      · intro hz
        rw [hbox] at hz
        obtain ⟨-, hzeq⟩ := Finset.mem_filter.mp hz
        exfalso
        apply hgn
        have h5 : g ∣ a * z.1 + b * z.2 :=
          dvd_add (Dvd.dvd.mul_right hga z.1) (Dvd.dvd.mul_right hgb z.2)
        rwa [hzeq] at h5
      · intro hz
        simp at hz
    rw [hboxe]
    simp
