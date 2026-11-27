import Mathlib

namespace BLS

/-- Auxiliary loop for `powMod`: structural recursion on fuel, binary method. -/
def powModAux : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, acc, _, _, _ => acc
  | fuel + 1, acc, b, e, m =>
    if e = 0 then acc
    else powModAux fuel (if e % 2 = 1 then acc * b % m else acc) (b * b % m) (e / 2) m

/-- Kernel-friendly modular exponentiation (structural recursion on fuel, binary method). -/
def powMod (a e m : ℕ) : ℕ := powModAux (Nat.log2 e + 1) (1 % m) (a % m) e m

theorem powModAux_eq (fuel : ℕ) : ∀ acc b e m : ℕ, acc % m = acc → e < 2 ^ fuel →
    powModAux fuel acc b e m = acc * b ^ e % m := by
  induction fuel with
  | zero =>
    intro acc b e m hacc he
    have he0 : e = 0 := by simpa using he
    subst he0
    simp [powModAux, hacc]
  | succ n ih =>
    intro acc b e m hacc he
    rw [powModAux]
    have he2 : e / 2 < 2 ^ n := by
      rw [pow_succ] at he
      omega
    split_ifs with h0 h1
    · subst h0
      simp [hacc]
    · rw [ih _ _ _ _ (Nat.mod_mod _ _) he2]
      obtain ⟨k, rfl⟩ : ∃ k, e = 2 * k + 1 := ⟨e / 2, by omega⟩
      have hk : (2 * k + 1) / 2 = k := by omega
      rw [hk]
      have h : acc * b % m * (b * b % m) ^ k ≡ acc * b * (b * b) ^ k [MOD m] :=
        (Nat.mod_modEq _ _).mul ((Nat.mod_modEq _ _).pow _)
      have h2 : acc * b * (b * b) ^ k = acc * b ^ (2 * k + 1) := by ring
      rw [h2] at h
      exact h
    · rw [ih _ _ _ _ hacc he2]
      obtain ⟨k, rfl⟩ : ∃ k, e = 2 * k := ⟨e / 2, by omega⟩
      have hk : (2 * k) / 2 = k := by omega
      rw [hk]
      have h : acc * (b * b % m) ^ k ≡ acc * (b * b) ^ k [MOD m] :=
        (Nat.ModEq.refl _).mul ((Nat.mod_modEq _ _).pow _)
      have h2 : acc * (b * b) ^ k = acc * b ^ (2 * k) := by ring
      rw [h2] at h
      exact h

theorem powMod_eq (a e m : ℕ) : powMod a e m = a ^ e % m := by
  unfold powMod
  rw [powModAux_eq _ _ _ _ _ (Nat.mod_mod _ _) Nat.lt_log2_self]
  have h : 1 % m * (a % m) ^ e ≡ 1 * a ^ e [MOD m] :=
    (Nat.mod_modEq _ _).mul ((Nat.mod_modEq _ _).pow _)
  rw [one_mul] at h
  exact h

/-- Certificate check for `N` with `F = ℓ^e ∣ N - 1` and `N < F^3`.
`a` is the witness base, `s` an integer-square-root witness for the discriminant. -/
def check (N ℓ e a s : ℕ) : Bool :=
  let F := ℓ ^ e
  let x := powMod a ((N - 1) / ℓ) N
  let m := (N - 1) / F
  let c1 := m % F
  let c2 := m / F
  decide (1 < N) && decide (0 < e) && decide (N % F = 1) && decide (N < F * F * F) &&
  decide (powMod x ℓ N = 1) && decide (Nat.gcd (x + N - 1) N = 1) &&
  (decide (N ≤ F * F) || decide (c1 * c1 < 4 * c2) ||
    (decide (s * s + 4 * c2 < c1 * c1) && decide (c1 * c1 < (s + 1) * (s + 1) + 4 * c2)))

/-- If `d ∣ n` but `d ∤ n / ℓ` (`ℓ` prime), then the full `ℓ`-part of `n` divides `d`. -/
theorem pow_dvd_of_dvd_of_not_dvd_div {ℓ e d n : ℕ} (hℓ : ℓ.Prime) (hn : ℓ ^ e ∣ n)
    (hd : d ∣ n) (hnd : ¬ d ∣ n / ℓ) : ℓ ^ e ∣ d := by
  obtain ⟨k, rfl⟩ := hd
  have hk : ¬ ℓ ∣ k := by
    rintro ⟨k', rfl⟩
    apply hnd
    rw [show d * (ℓ * k') = ℓ * (d * k') by ring, Nat.mul_div_cancel_left _ hℓ.pos]
    exact dvd_mul_right _ _
  have hc : Nat.Coprime (ℓ ^ e) k :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hk)
  exact hc.dvd_of_dvd_mul_right hn

/-- Pocklington step: every prime factor of `N` is `≡ 1 (mod ℓ^e)`. -/
theorem prime_factor_dvd_sub_one {N ℓ e a r : ℕ} (hℓ : ℓ.Prime) (hN : 1 < N)
    (hF : ℓ ^ e ∣ N - 1) (he : 0 < e)
    (hx : (a ^ ((N - 1) / ℓ) % N) ^ ℓ % N = 1)
    (hg : Nat.gcd (a ^ ((N - 1) / ℓ) % N + N - 1) N = 1)
    (hr : r.Prime) (hrN : r ∣ N) : ℓ ^ e ∣ r - 1 := by
  have := Fact.mk hr
  have hℓN : ℓ ∣ N - 1 := (dvd_pow_self ℓ he.ne').trans hF
  generalize hxdef : a ^ ((N - 1) / ℓ) % N = x at hx hg
  have hxc : (x : ZMod r) = (a : ZMod r) ^ ((N - 1) / ℓ) := by
    have h1 : (x : ZMod r) = ((a ^ ((N - 1) / ℓ) : ℕ) : ZMod r) := by
      rw [ZMod.natCast_eq_natCast_iff, ← hxdef]
      exact (Nat.mod_modEq _ _).of_dvd hrN
    rw [h1, Nat.cast_pow]
  have hxl : (x : ZMod r) ^ ℓ = 1 := by
    have h1 : ((x ^ ℓ : ℕ) : ZMod r) = ((1 : ℕ) : ZMod r) := by
      rw [ZMod.natCast_eq_natCast_iff]
      have h2 : x ^ ℓ ≡ 1 [MOD N] := by
        unfold Nat.ModEq
        rw [hx, Nat.mod_eq_of_lt hN]
      exact h2.of_dvd hrN
    simpa using h1
  have hne : (x : ZMod r) ≠ 1 := by
    intro h1
    have h2 : ((x + N - 1 : ℕ) : ZMod r) = 0 := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, h1, (ZMod.natCast_eq_zero_iff N r).mpr hrN]
      simp
    rw [ZMod.natCast_eq_zero_iff] at h2
    have h3 := Nat.dvd_gcd h2 hrN
    rw [hg] at h3
    exact hr.one_lt.ne' (Nat.dvd_one.mp h3)
  have hpow : (a : ZMod r) ^ (N - 1) = 1 := by
    rw [← Nat.div_mul_cancel hℓN, pow_mul, ← hxc, hxl]
  have ha0 : (a : ZMod r) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hpow
    exact zero_ne_one hpow
  have hd1 : orderOf (a : ZMod r) ∣ N - 1 := orderOf_dvd_of_pow_eq_one hpow
  have hd2 : ¬ orderOf (a : ZMod r) ∣ (N - 1) / ℓ := by
    rw [orderOf_dvd_iff_pow_eq_one, ← hxc]
    exact hne
  have hd3 : orderOf (a : ZMod r) ∣ r - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one ha0)
  exact (pow_dvd_of_dvd_of_not_dvd_div hℓ hF hd1 hd2).trans hd3

/-- `(α+β)² - 4αβ = (α-β)²` is a perfect square, so it is neither negative nor strictly
between two consecutive squares. -/
theorem square_gap {α β s : ℕ} :
    ¬ ((α + β) * (α + β) < 4 * (α * β)) ∧
    ¬ (s * s + 4 * (α * β) < (α + β) * (α + β) ∧
      (α + β) * (α + β) < (s + 1) * (s + 1) + 4 * (α * β)) := by
  have key : ∀ a d : ℕ,
      ¬ ((a + (a + d)) * (a + (a + d)) < 4 * (a * (a + d))) ∧
      ¬ (s * s + 4 * (a * (a + d)) < (a + (a + d)) * (a + (a + d)) ∧
        (a + (a + d)) * (a + (a + d)) < (s + 1) * (s + 1) + 4 * (a * (a + d))) := by
    intro a d
    have hid : (a + (a + d)) * (a + (a + d)) = d * d + 4 * (a * (a + d)) := by ring
    rw [hid]
    refine ⟨by omega, ?_⟩
    rintro ⟨h1, h2⟩
    have h1' : s * s < d * d := by omega
    have h2' : d * d < (s + 1) * (s + 1) := by omega
    have hsd : s < d := by
      by_contra hc
      have := Nat.mul_le_mul (Nat.le_of_not_lt hc) (Nat.le_of_not_lt hc)
      omega
    have hds : d < s + 1 := by
      by_contra hc
      have := Nat.mul_le_mul (Nat.le_of_not_lt hc) (Nat.le_of_not_lt hc)
      omega
    omega
  rcases le_total α β with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    exact key α d
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have := key β d
    rwa [Nat.add_comm (β + d) β, Nat.mul_comm (β + d) β]

theorem check_sound {N ℓ e a s : ℕ} (hℓ : ℓ.Prime) (h : check N ℓ e a s = true) : N.Prime := by
  simp only [check, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, powMod_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hN, he⟩, hmod⟩, hlt⟩, hx⟩, hg⟩, hsq⟩ := h
  generalize hFdef : ℓ ^ e = F at hmod hlt hsq
  have hFpos : 0 < F := by
    rw [← hFdef]
    exact pow_pos hℓ.pos e
  have hF : F ∣ N - 1 := by
    have h1 := Nat.dvd_sub_mod (n := F) N
    rwa [hmod] at h1
  by_contra hNp
  have hr : (N.minFac).Prime := Nat.minFac_prime (by omega)
  obtain ⟨t, ht⟩ := Nat.minFac_dvd N
  generalize N.minFac = r at hr ht
  have hrF : F ∣ r - 1 := by
    rw [← hFdef]
    exact prime_factor_dvd_sub_one hℓ hN (hFdef ▸ hF) he hx hg hr (Dvd.intro t ht.symm)
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [mul_one] at ht
    exact hNp (ht ▸ hr)
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [mul_zero] at ht
    omega
  obtain ⟨α, hα⟩ := hrF
  have hr2 := hr.two_le
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hα
    omega
  have hrα : r = F * α + 1 := by omega
  have htF : F ∣ t - 1 := by
    have h1 : N - 1 = F * (α * t) + (t - 1) := by
      have h2 : N = F * (α * t) + t := by
        rw [ht, hrα]
        ring
      omega
    rw [h1] at hF
    exact (Nat.dvd_add_right (dvd_mul_right F (α * t))).mp hF
  obtain ⟨β, hβ⟩ := htF
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hβ
    omega
  have htβ : t = F * β + 1 := by omega
  have hNeq : N = α * β * (F * F) + (α + β) * F + 1 := by
    rw [ht, hrα, htβ]
    ring
  have hαβpos : 1 ≤ α * β := Nat.mul_pos (Nat.pos_of_ne_zero hα0) (Nat.pos_of_ne_zero hβ0)
  have hαβ : α * β < F := by
    by_contra hc
    have h1 : F * (F * F) ≤ α * β * (F * F) := Nat.mul_le_mul_right _ (Nat.le_of_not_lt hc)
    have h2 : F * F * F = F * (F * F) := by ring
    have h3 := Nat.zero_le ((α + β) * F)
    omega
  have hNbig : F * F < N := by
    have h1 : 1 * (F * F) ≤ α * β * (F * F) := Nat.mul_le_mul_right _ hαβpos
    have h3 := Nat.zero_le ((α + β) * F)
    omega
  have hsum1 : α + β ≤ α * β + 1 := by
    obtain ⟨a', rfl⟩ : ∃ a', α = a' + 1 := ⟨α - 1, by omega⟩
    obtain ⟨b', rfl⟩ : ∃ b', β = b' + 1 := ⟨β - 1, by omega⟩
    have h1 : (a' + 1) * (b' + 1) = a' * b' + a' + b' + 1 := by ring
    omega
  have hsum : α + β < F := by
    by_contra hc
    have h1 : α + β = F := by omega
    have h2 : α * β + 1 = F := by omega
    have h3 : N = F * F * F + 1 := by
      calc N = α * β * (F * F) + (α + β) * F + 1 := hNeq
        _ = (α * β + 1) * (F * F) + 1 := by rw [h1]; ring
        _ = F * F * F + 1 := by rw [h2]; ring
    omega
  have hm : (N - 1) / F = (α + β) + F * (α * β) := by
    apply Nat.div_eq_of_eq_mul_right hFpos
    have h1 : α * β * (F * F) + (α + β) * F = F * ((α + β) + F * (α * β)) := by ring
    omega
  have hc1 : (N - 1) / F % F = α + β := by
    rw [hm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsum]
  have hc2 : (N - 1) / F / F = α * β := by
    rw [hm, Nat.add_mul_div_left _ _ hFpos, Nat.div_eq_of_lt hsum, zero_add]
  rw [hc1, hc2] at hsq
  have hgap := square_gap (α := α) (β := β) (s := s)
  rcases hsq with (h1 | h1) | h1
  · omega
  · exact hgap.1 h1
  · exact hgap.2 h1

end BLS

namespace GW
open BLS

def lOf (i : ℕ) : ℕ :=
  match i with
  | 0 => 3 | 1 => 5 | 2 => 7 | 3 => 11 | 4 => 13 | 5 => 17 | 6 => 19 | _ => 23

theorem lOf_prime (i : ℕ) : (lOf i).Prime := by
  unfold lOf
  split <;> norm_num

def isqrtAux : ℕ → ℕ → ℕ → ℕ
  | 0, x, _ => x
  | f + 1, x, n => if (x + n / x) / 2 < x then isqrtAux f ((x + n / x) / 2) n else x

def isqrt (n : ℕ) : ℕ := if n = 0 then 0 else isqrtAux 64 (2 ^ (Nat.log2 n / 2 + 1)) n

def sWit (N l e : ℕ) : ℕ :=
  isqrt (((N - 1) / l ^ e % l ^ e) * ((N - 1) / l ^ e % l ^ e) - 4 * ((N - 1) / l ^ e / l ^ e))

def bLoop : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, b, _, _ => b
  | f + 1, b, l, n => if n < l ^ (3 * b) then b else bLoop f (b + 1) l n

def pOf (n l b e k : ℕ) : ℕ :=
  1 + 2 ^ e * ((n - 2) * powMod (2 ^ e) (l ^ (b - 1) * (l - 1) - 1) (l ^ b) % l ^ b) + k * (2 ^ e * l ^ b)

def rowAux (n l b e a1 a2 p : ℕ) : Bool :=
  decide (p ≤ n) && check p 2 e a1 (sWit p 2 e) && check (n - p) l b a2 (sWit (n - p) l b)

def rowOK (n code : ℕ) : Bool :=
  rowAux n (lOf (code % 8)) (bLoop 400 1 (lOf (code % 8)) n) (Nat.log2 n / 3 + 1)
    (code / 512 % 64) (code / 8 % 64)
    (pOf n (lOf (code % 8)) (bLoop 400 1 (lOf (code % 8)) n) (Nat.log2 n / 3 + 1) (code / 32768))

theorem rowOK_sound {n code : ℕ} (h : rowOK n code = true) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  unfold rowOK rowAux at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hp, h1⟩, h2⟩ := h
  exact ⟨_, _, check_sound Nat.prime_two h1, check_sound (lOf_prime _) h2, Nat.add_sub_of_le hp⟩

def checkList (f : ℕ → ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | i, c :: cs => rowOK (f i) c && checkList f (i + 1) cs

theorem checkList_sound (f : ℕ → ℕ) : ∀ (cs : List ℕ) (i0 : ℕ), checkList f i0 cs = true →
    ∀ i, i0 ≤ i → i < i0 + cs.length → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = f i := by
  intro cs
  induction cs with
  | nil =>
    intro i0 _ i h1 h2
    simp only [List.length_nil] at h2
    omega
  | cons c cs ih =>
    intro i0 h i h1 h2
    simp only [checkList, Bool.and_eq_true] at h
    simp only [List.length_cons] at h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact rowOK_sound h.1
    · exact ih (i0 + 1) h.2 i hlt (by omega)

def tab0 : List ℕ := [21890577, 694800, 1639954, 1083944, 15468049, 7509520, 6948370, 1083928, 24086033, 2496024, 26347035, 989712, 1771025, 593424, 230930, 1183248, 18220561, 33294864, 31720978, 43485712, 10847761, 6852112, 15959571, 17305104, 64620049, 2002448, 5309970, 955920, 18449937, 232976, 5572122, 658968, 9537041, 24514064, 30115347, 7277072, 30311953, 46009872, 93226514, 17932840, 22513169, 7178776, 22447634, 11831824, 50136593, 3845656, 63276571, 7638544, 35522065, 50367000, 8947218, 62003736, 65734161, 26545680, 42796562, 3083792, 11503121, 15472144, 29492758, 51252752, 54887953, 7703056, 15992338, 1019416]

theorem len0 : tab0.length = 64 := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok0 : checkList (fun j => 2 ^ j) 62 tab0 = true := by decide +kernel

def tab1 : List ℕ := [29558289, 46205456, 50923026, 57248280, 18679313, 20056592, 6718995, 19965464, 1312273, 50240016, 115770898, 12458512, 47023633, 29886992, 61408786, 32902680, 90441233, 5442072, 19793427, 10489360, 53872145, 3149328, 53610002, 17960488, 104728081, 9834000, 291341842, 57708048, 755217, 80742928, 47023635, 133830160, 241403417, 821784, 277808658, 29624848, 528352785, 18291216, 6915602, 44403216, 140510737, 119213656, 22349331, 62097936, 117704209, 73730584, 1508882, 19140112, 146736657, 1609232, 39028242, 27366928, 147850769, 27037200, 25462293, 43814416, 22414873, 50993680, 120555026, 100961808, 168494609, 495120, 19695122, 16976424]

theorem len1 : tab1.length = 64 := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : checkList (fun j => 2 ^ j) 126 tab1 = true := by decide +kernel

def tab2 : List ℕ := [126977553, 25988624, 34047507, 9735696, 51578385, 21171728, 106464786, 30772752, 8324625, 39259664, 6293010, 256413200, 103155225, 59938320, 37094931, 65672720, 34145809, 61410832, 249366034, 136612376, 50333201, 124423704, 922256914, 91363864, 28182033, 68033040, 25003539, 135957008, 231802393, 122689040, 272762394, 59378200, 26281497, 18591248, 139363858, 7638544, 240059921, 118099472, 638879251, 205328, 2885137, 189827600, 77432338, 73146896, 136119865, 658984, 168101394, 35658256, 204441105, 186521104, 80545302, 92608016, 280888849, 120887824, 32900626, 179310096, 62686737, 172100120, 34309650, 234622480, 1050137, 20125224, 104859155, 56135184]

theorem len2 : tab2.length = 64 := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : checkList (fun j => 2 ^ j) 190 tab2 = true := by decide +kernel

def tab3 : List ℕ := [51676713, 204344848, 58885658, 266451472, 35816977, 18549264, 443352594, 55511568, 282953233, 264604184, 66717203, 50925072, 111117841, 120785424, 112854546, 241045008, 4654609, 66161168, 213583386, 49842704, 1673561625, 8784400, 77137427, 144312856, 98960913, 114821648, 439617042, 77335056, 223118873, 47779344, 116950546, 66980368, 1207928337, 268143120, 259720723, 28741136, 28706321, 7342608, 42534418, 146442768, 519669265, 151555600, 1162872346, 584325648, 175441425, 102012432, 308348437, 115837456, 104531473, 30084632, 389842450, 247139864, 262145553, 190974480, 389940762, 38767120, 391972369, 46828048, 457180691, 77370904, 109839889, 423010840, 105514514, 92573200]

theorem len3 : tab3.length = 64 := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : checkList (fun j => 2 ^ j) 254 tab3 = true := by decide +kernel

def tab4 : List ℕ := [103220753, 295078416, 157484562, 118229520, 205391377, 16977424, 482477587, 78779920, 59508241, 192024104, 283805202, 133404184, 152929809, 99486232, 59147794, 120655376, 482510353, 313657880, 371361299, 46698024, 339871273, 96897624, 1225885210, 49711632, 894764561, 121047568, 426083858, 46336536, 103024153, 49941016, 446662163, 215392784, 223151641, 311660048, 84411922, 33790480, 201459217, 99718672, 579733010, 316476944, 49120785, 72846864, 376145431, 77629968, 767624721, 173549080, 546178578, 175835664, 153159185, 175607320, 531793426, 55905808, 50824721, 347770384, 175539731, 77927960, 318408209, 871730712, 35358226, 301209112, 423527953, 343083536, 165676562, 18228760]

theorem len4 : tab4.length = 64 := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : checkList (fun j => 2 ^ j) 318 tab4 = true := by decide +kernel

def tab5 : List ℕ := [293668369, 635603472, 52790803, 54659608, 152077849, 165874192, 466781714, 246254096, 246220305, 88149520, 125797906, 323685904, 562562577, 51055144, 454493715, 186355216, 79201809, 168431120, 603424274, 117115416, 1272907281, 367269392, 436635154, 59182608, 577668633, 422219304, 329235, 393907728, 44336657, 269388304, 1445398034, 135111184, 293013009, 142549520, 460424722, 656280088, 2314307089, 265325080, 18908693, 3279384, 226362897, 128194064, 167085586, 1519847952, 98666009, 305072656, 339609106, 83367448, 329233, 86510096, 327255571, 75041296, 348325393, 89951760, 162596370, 4427280, 314639889, 1847760400, 311789074, 102828560, 1874789905, 120133136, 93324819, 49778192]

theorem len5 : tab5.length = 64 := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : checkList (fun j => 2 ^ j) 382 tab5 = true := by decide +kernel

def tab6 : List ℕ := [108299793, 87919160, 25462290, 388732432, 410519057, 105945616, 3084420626, 25464344, 29066769, 864325136, 197166611, 965547536, 1844381209, 13181464, 59180562, 312643088, 573670929, 399280656, 962233874, 421072408, 640714257, 437259800, 514459155, 13536784, 159548945, 70258192, 288261650, 282463760, 1308263953, 117770768, 116393490, 673061392, 534447641, 443026968, 98076182, 60001808, 1444677137, 371630608, 55641618, 362912272, 1342047761, 652446232, 26936850, 163286544, 1029867025, 74359320, 1514669587, 313428520, 329188881, 95522328, 680363538, 319953432, 505349649, 246090264, 5965338, 384928280, 45352465, 139598360, 811501075, 114331152, 1366656529, 348293656, 222299666, 871599632]

theorem len6 : tab6.length = 64 := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok6 : checkList (fun j => 2 ^ j) 446 tab6 = true := by decide +kernel

def tab7 : List ℕ := [72287761, 55512592, 8521234, 17274384, 143033873, 115707408, 881886739, 136088088, 570361361, 239046160, 502302226, 64457240, 732497433, 145197584, 384894482, 619810320, 798557713, 452857360, 891258387, 975115816, 372835857, 380312080, 79922706, 127374888, 1061684753, 278367768, 87426578, 449284648, 72615441, 206211600, 594216469, 87886352, 104269353, 372870672, 158959130, 5343760, 2740487697, 1379112472, 488343058, 70584848, 1475020305, 12519952, 1512474131, 266936856, 932546065, 306645520, 1082099218, 581849640, 133498385, 62625296, 385713682, 400824872, 625083921, 782863888, 96503315, 58821176, 102598161, 694290960, 782468626, 264998416, 515474969, 581963280, 271943186, 22368784]

theorem len7 : tab7.length = 64 := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok7 : checkList (fun j => 2 ^ j) 510 tab7 = true := by decide +kernel

def tab8 : List ℕ := [316212753, 1299910160, 579765779, 693537296, 176653849, 294850088, 917210642, 33230352, 1380779537, 177776144, 1201276434, 708774416, 158631441, 74914320, 1465845267, 9997848, 1263896081, 445286968, 3886155282, 59444752, 53642769, 96376336, 2701428242, 453642768]

theorem len8 : tab8.length = 24 := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok8 : checkList (fun j => 2 ^ j) 574 tab8 = true := by decide +kernel

end GW

set_option maxHeartbeats 0 in
theorem Conjectures.Goldbach.Rfc11DyadicLeftEndpointWitnesses : (∀ j : ℕ, 62≤j → j≤597 → let n : ℕ := 2^j; ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n) := by
  intro j h1 h2
  have hall0 := GW.checkList_sound (fun j => 2 ^ j) GW.tab0 62 GW.ok0
  rw [GW.len0] at hall0
  have hall1 := GW.checkList_sound (fun j => 2 ^ j) GW.tab1 126 GW.ok1
  rw [GW.len1] at hall1
  have hall2 := GW.checkList_sound (fun j => 2 ^ j) GW.tab2 190 GW.ok2
  rw [GW.len2] at hall2
  have hall3 := GW.checkList_sound (fun j => 2 ^ j) GW.tab3 254 GW.ok3
  rw [GW.len3] at hall3
  have hall4 := GW.checkList_sound (fun j => 2 ^ j) GW.tab4 318 GW.ok4
  rw [GW.len4] at hall4
  have hall5 := GW.checkList_sound (fun j => 2 ^ j) GW.tab5 382 GW.ok5
  rw [GW.len5] at hall5
  have hall6 := GW.checkList_sound (fun j => 2 ^ j) GW.tab6 446 GW.ok6
  rw [GW.len6] at hall6
  have hall7 := GW.checkList_sound (fun j => 2 ^ j) GW.tab7 510 GW.ok7
  rw [GW.len7] at hall7
  have hall8 := GW.checkList_sound (fun j => 2 ^ j) GW.tab8 574 GW.ok8
  rw [GW.len8] at hall8
  by_cases hc0 : j < 126
  · exact hall0 j (by omega) (by omega)
  by_cases hc1 : j < 190
  · exact hall1 j (by omega) (by omega)
  by_cases hc2 : j < 254
  · exact hall2 j (by omega) (by omega)
  by_cases hc3 : j < 318
  · exact hall3 j (by omega) (by omega)
  by_cases hc4 : j < 382
  · exact hall4 j (by omega) (by omega)
  by_cases hc5 : j < 446
  · exact hall5 j (by omega) (by omega)
  by_cases hc6 : j < 510
  · exact hall6 j (by omega) (by omega)
  by_cases hc7 : j < 574
  · exact hall7 j (by omega) (by omega)
  exact hall8 j (by omega) (by omega)
