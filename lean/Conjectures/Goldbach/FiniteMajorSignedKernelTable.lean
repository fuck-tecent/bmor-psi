import Mathlib

private def ram (q t : ℕ) : ℤ :=
  ∑ d ∈ q.divisors.filter (fun d => d ∣ t), (d : ℤ) * ArithmeticFunction.moebius (q/d)
private def coef (q t : ℕ) : ℚ :=
  (ArithmeticFunction.moebius q : ℚ)^2 / (q.totient : ℚ)^2 * (ram q t : ℚ)
private def leftEnd (q : ℕ) : ℚ := if q ∣ 30 then 1 - 2*(q : ℚ)/(9*105) else 0
/- Entries are lower bounds in millionths. For each modulus we check both endpoints
   of the permitted weight interval, for every possible gcd of that modulus with n. -/
private def table : List ℤ := [0, 997883, 995767, 496825, 0, 247354, 493650, -27778, 0, 0, 244708, -10000, 0, -6945, -27778, 121031, 0, -3907, 0, -3087, 0, -13889, -10000, -2067, 0, 0, -6945, 0, 0, -1276, 117063, -1112, 0, -5000, -3907, -6945, 0, -772, -3087, -3473, 0, -625, -13889, -567, 0, 0, -2067, -473, 0, 0, 0, -1954, 0, -370, 0, -2500, 0, -1544, -1276, -298, 0, -278, -1112, 0, 0, -1737, -5000, -230, 0, -1034, -6945, -205, 0, -193, -772, 0, 0, -2778, -3473, -165, 0, 0, -625, -149, 0, -977, -567, -638, 0, -130, 0, -2315, 0, -556, -473, -772, 0, -109, 0, 0, 0, -100, -1954, -97, 0, -3473]
private def minorant (q : ℕ) : ℚ := (table.getD q 0 : ℚ) / 1000000
private def Certified (q : ℕ) : Prop := ∀ t ∈ q.divisors, q.gcd 30 ∣ t →
  minorant q ≤ coef q t * leftEnd q ∧ minorant q ≤ coef q t
private instance (q : ℕ) : Decidable (Certified q) := inferInstanceAs (Decidable (∀ t ∈ q.divisors, q.gcd 30 ∣ t →
  minorant q ≤ coef q t * leftEnd q ∧ minorant q ≤ coef q t))
private theorem cert1 : Certified 1 := by decide +kernel
private theorem cert2 : Certified 2 := by decide +kernel
private theorem cert3 : Certified 3 := by decide +kernel
private theorem cert4 : Certified 4 := by decide +kernel
private theorem cert5 : Certified 5 := by decide +kernel
private theorem cert6 : Certified 6 := by decide +kernel
private theorem cert7 : Certified 7 := by decide +kernel
private theorem cert8 : Certified 8 := by decide +kernel
private theorem cert9 : Certified 9 := by decide +kernel
private theorem cert10 : Certified 10 := by decide +kernel
private theorem cert11 : Certified 11 := by decide +kernel
private theorem cert12 : Certified 12 := by decide +kernel
private theorem cert13 : Certified 13 := by decide +kernel
private theorem cert14 : Certified 14 := by decide +kernel
private theorem cert15 : Certified 15 := by decide +kernel
private theorem cert16 : Certified 16 := by decide +kernel
private theorem cert17 : Certified 17 := by decide +kernel
private theorem cert18 : Certified 18 := by decide +kernel
private theorem cert19 : Certified 19 := by decide +kernel
private theorem cert20 : Certified 20 := by decide +kernel
private theorem cert21 : Certified 21 := by decide +kernel
private theorem cert22 : Certified 22 := by decide +kernel
private theorem cert23 : Certified 23 := by decide +kernel
private theorem cert24 : Certified 24 := by decide +kernel
private theorem cert25 : Certified 25 := by decide +kernel
private theorem cert26 : Certified 26 := by decide +kernel
private theorem cert27 : Certified 27 := by decide +kernel
private theorem cert28 : Certified 28 := by decide +kernel
private theorem cert29 : Certified 29 := by decide +kernel
private theorem cert30 : Certified 30 := by decide +kernel
private theorem cert31 : Certified 31 := by decide +kernel
private theorem cert32 : Certified 32 := by decide +kernel
private theorem cert33 : Certified 33 := by decide +kernel
private theorem cert34 : Certified 34 := by decide +kernel
private theorem cert35 : Certified 35 := by decide +kernel
private theorem cert36 : Certified 36 := by decide +kernel
private theorem cert37 : Certified 37 := by decide +kernel
private theorem cert38 : Certified 38 := by decide +kernel
private theorem cert39 : Certified 39 := by decide +kernel
private theorem cert40 : Certified 40 := by decide +kernel
private theorem cert41 : Certified 41 := by decide +kernel
private theorem cert42 : Certified 42 := by decide +kernel
private theorem cert43 : Certified 43 := by decide +kernel
private theorem cert44 : Certified 44 := by decide +kernel
private theorem cert45 : Certified 45 := by decide +kernel
private theorem cert46 : Certified 46 := by decide +kernel
private theorem cert47 : Certified 47 := by decide +kernel
private theorem cert48 : Certified 48 := by decide +kernel
private theorem cert49 : Certified 49 := by decide +kernel
private theorem cert50 : Certified 50 := by decide +kernel
private theorem cert51 : Certified 51 := by decide +kernel
private theorem cert52 : Certified 52 := by decide +kernel
private theorem cert53 : Certified 53 := by decide +kernel
private theorem cert54 : Certified 54 := by decide +kernel
private theorem cert55 : Certified 55 := by decide +kernel
private theorem cert56 : Certified 56 := by decide +kernel
private theorem cert57 : Certified 57 := by decide +kernel
private theorem cert58 : Certified 58 := by decide +kernel
private theorem cert59 : Certified 59 := by decide +kernel
private theorem cert60 : Certified 60 := by decide +kernel
private theorem cert61 : Certified 61 := by decide +kernel
private theorem cert62 : Certified 62 := by decide +kernel
private theorem cert63 : Certified 63 := by decide +kernel
private theorem cert64 : Certified 64 := by decide +kernel
private theorem cert65 : Certified 65 := by decide +kernel
private theorem cert66 : Certified 66 := by decide +kernel
private theorem cert67 : Certified 67 := by decide +kernel
private theorem cert68 : Certified 68 := by decide +kernel
private theorem cert69 : Certified 69 := by decide +kernel
private theorem cert70 : Certified 70 := by decide +kernel
private theorem cert71 : Certified 71 := by decide +kernel
private theorem cert72 : Certified 72 := by decide +kernel
private theorem cert73 : Certified 73 := by decide +kernel
private theorem cert74 : Certified 74 := by decide +kernel
private theorem cert75 : Certified 75 := by decide +kernel
private theorem cert76 : Certified 76 := by decide +kernel
private theorem cert77 : Certified 77 := by decide +kernel
private theorem cert78 : Certified 78 := by decide +kernel
private theorem cert79 : Certified 79 := by decide +kernel
private theorem cert80 : Certified 80 := by decide +kernel
private theorem cert81 : Certified 81 := by decide +kernel
private theorem cert82 : Certified 82 := by decide +kernel
private theorem cert83 : Certified 83 := by decide +kernel
private theorem cert84 : Certified 84 := by decide +kernel
private theorem cert85 : Certified 85 := by decide +kernel
private theorem cert86 : Certified 86 := by decide +kernel
private theorem cert87 : Certified 87 := by decide +kernel
private theorem cert88 : Certified 88 := by decide +kernel
private theorem cert89 : Certified 89 := by decide +kernel
private theorem cert90 : Certified 90 := by decide +kernel
private theorem cert91 : Certified 91 := by decide +kernel
private theorem cert92 : Certified 92 := by decide +kernel
private theorem cert93 : Certified 93 := by decide +kernel
private theorem cert94 : Certified 94 := by decide +kernel
private theorem cert95 : Certified 95 := by decide +kernel
private theorem cert96 : Certified 96 := by decide +kernel
private theorem cert97 : Certified 97 := by decide +kernel
private theorem cert98 : Certified 98 := by decide +kernel
private theorem cert99 : Certified 99 := by decide +kernel
private theorem cert100 : Certified 100 := by decide +kernel
private theorem cert101 : Certified 101 := by decide +kernel
private theorem cert102 : Certified 102 := by decide +kernel
private theorem cert103 : Certified 103 := by decide +kernel
private theorem cert104 : Certified 104 := by decide +kernel
private theorem cert105 : Certified 105 := by decide +kernel
private theorem lowerTable : (351/100 : ℚ) < ∑ q ∈ Finset.Icc 1 105, minorant q := by decide +kernel

private theorem certified {q : ℕ} (hq : q ∈ Finset.Icc 1 105) : Certified q := by
  obtain ⟨h1,h2⟩ := Finset.mem_Icc.mp hq
  interval_cases q
  · exact cert1
  · exact cert2
  · exact cert3
  · exact cert4
  · exact cert5
  · exact cert6
  · exact cert7
  · exact cert8
  · exact cert9
  · exact cert10
  · exact cert11
  · exact cert12
  · exact cert13
  · exact cert14
  · exact cert15
  · exact cert16
  · exact cert17
  · exact cert18
  · exact cert19
  · exact cert20
  · exact cert21
  · exact cert22
  · exact cert23
  · exact cert24
  · exact cert25
  · exact cert26
  · exact cert27
  · exact cert28
  · exact cert29
  · exact cert30
  · exact cert31
  · exact cert32
  · exact cert33
  · exact cert34
  · exact cert35
  · exact cert36
  · exact cert37
  · exact cert38
  · exact cert39
  · exact cert40
  · exact cert41
  · exact cert42
  · exact cert43
  · exact cert44
  · exact cert45
  · exact cert46
  · exact cert47
  · exact cert48
  · exact cert49
  · exact cert50
  · exact cert51
  · exact cert52
  · exact cert53
  · exact cert54
  · exact cert55
  · exact cert56
  · exact cert57
  · exact cert58
  · exact cert59
  · exact cert60
  · exact cert61
  · exact cert62
  · exact cert63
  · exact cert64
  · exact cert65
  · exact cert66
  · exact cert67
  · exact cert68
  · exact cert69
  · exact cert70
  · exact cert71
  · exact cert72
  · exact cert73
  · exact cert74
  · exact cert75
  · exact cert76
  · exact cert77
  · exact cert78
  · exact cert79
  · exact cert80
  · exact cert81
  · exact cert82
  · exact cert83
  · exact cert84
  · exact cert85
  · exact cert86
  · exact cert87
  · exact cert88
  · exact cert89
  · exact cert90
  · exact cert91
  · exact cert92
  · exact cert93
  · exact cert94
  · exact cert95
  · exact cert96
  · exact cert97
  · exact cert98
  · exact cert99
  · exact cert100
  · exact cert101
  · exact cert102
  · exact cert103
  · exact cert104
  · exact cert105

set_option maxRecDepth 4096 in
theorem Conjectures.Goldbach.FiniteMajorSignedKernelTable : let R := fun (q n : ℕ) => ∑ d ∈ q.divisors.filter (fun d => d ∣ n), (d:ℝ)*(ArithmeticFunction.moebius (q/d):ℝ); ∀ (n : ℕ) (K : ℕ → ℝ), 30 ∣ n → (∀ q ∈ Finset.Icc (1:ℕ) 105, 0≤K q ∧ K q≤1) → (∀ q ∈ Finset.Icc (1:ℕ) 105, q ∣ 30 → 1-2*(q:ℝ)/(9*105)≤K q) → (351/100:ℝ) < ∑ q ∈ Finset.Icc (1:ℕ) 105, (ArithmeticFunction.moebius q:ℝ)^2/(Nat.totient q:ℝ)^2*R q n*K q := by
  classical
  dsimp only
  intro n K hn hK hleft
  have total : (351/100 : ℝ) < ∑ q ∈ Finset.Icc 1 105, (minorant q : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_sum] using (Rat.cast_lt (K := ℝ)).mpr lowerTable
  apply total.trans_le
  apply Finset.sum_le_sum
  intro q hq
  let t := q.gcd n
  have qpos : 0 < q := (Finset.mem_Icc.mp hq).1
  have ht : t ∈ q.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, qpos.ne'⟩
  have hgt : q.gcd 30 ∣ t := Nat.dvd_gcd (Nat.gcd_dvd_left _ _) ((Nat.gcd_dvd_right q 30).trans hn)
  obtain ⟨hlo,hhi⟩ := certified hq t ht hgt
  have realLo : (minorant q : ℝ) ≤ (coef q t : ℝ) * (leftEnd q : ℝ) := by exact_mod_cast hlo
  have realHi : (minorant q : ℝ) ≤ (coef q t : ℝ) := by exact_mod_cast hhi
  have lowK : (leftEnd q : ℝ) ≤ K q := by
    by_cases hd : q ∣ 30
    · simpa [leftEnd,hd] using hleft q hq hd
    · simpa [leftEnd,hd] using (hK q hq).1
  have mid : (minorant q : ℝ) ≤ (coef q t : ℝ) * K q := by
    by_cases hc : 0 ≤ (coef q t : ℝ)
    · exact realLo.trans (mul_le_mul_of_nonneg_left lowK hc)
    · exact realHi.trans (by simpa using mul_le_mul_of_nonpos_left (hK q hq).2 (le_of_not_ge hc))
  have filterEq : q.divisors.filter (fun d => d ∣ t) = q.divisors.filter (fun d => d ∣ n) := by
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hd,hdt⟩; exact ⟨hd,hdt.trans (Nat.gcd_dvd_right q n)⟩
    · rintro ⟨hd,hdn⟩; exact ⟨hd,Nat.dvd_gcd (Nat.mem_divisors.mp hd).1 hdn⟩
  simpa [coef, ram, filterEq] using mid
