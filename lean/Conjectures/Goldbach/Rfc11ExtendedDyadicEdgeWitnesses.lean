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

def tab0 : List ℕ := [415827481, 68292120, 2677933590, 17632808, 1479083537, 5344784, 192218642, 978852376, 1034946065, 697141776, 2707523098, 19598864, 676660793, 484542992, 699336211, 252611096, 4090693137, 490932776, 1526990354, 663689744, 604145193, 29100584, 2563573266, 1004898832, 937100817, 102697488, 358450707, 153389584, 507741713, 336988696, 5885462034, 299960856, 253625873, 64588344, 1566246418, 184227344, 2755724825, 262671888, 3226666515, 191141416, 2193425937, 430607888, 2422277650, 141364752, 1632241177, 226789904, 1876395538, 606574096, 1447462425, 137011728, 488146451, 1710198312, 153781777, 341477904, 798918162, 469110288, 305759761, 363923984, 1895204378, 963841552, 1916732945, 165022312, 931137045, 228462096]

theorem len0 : tab0.length = 64 := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok0 : checkList (fun j => 2 ^ j) 598 tab0 = true := by decide +kernel

def tab1 : List ℕ := [284362257, 184525352, 361825810, 1727532568, 1790576153, 233868824, 64554514, 479038992, 1760101905, 148344336, 407995923, 425201176, 4098852369, 224628240, 1678050834, 2111016464, 68159017, 511053328, 26379794, 183634448, 647792145, 1758268944, 19039763, 108923416, 97388049, 145724944, 3224995346, 849546768, 1056179729, 830705168, 3452143122, 1153337872, 1589184017, 189402640, 1884554771, 239667736, 1193543193, 1554811408, 652019218, 558206480, 2019427865, 201166360, 761824786, 91462184, 610633233, 787299856, 685049363, 640621072, 722634265, 1010704912, 1300203026, 261492240, 429721105, 1908607504, 651888146, 326601232, 1594394129, 605163024, 451315223, 1207635472, 975144465, 284953128, 60589586, 434179624]

theorem len1 : tab1.length = 64 := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : checkList (fun j => 2 ^ j) 662 tab1 = true := by decide +kernel

def tab2 : List ℕ := [4064085521, 315756048, 2267186706, 483498520, 1868727833, 41847312, 2667283987, 3021408792, 149194257, 1132795408, 222889498, 49482256, 169707025, 101550608, 511346194, 115707408, 3079800345, 206703120, 2958263827, 932908584, 966297105, 2858355216, 594052626, 1237913104, 2030437905, 4191491600, 2607384082, 80058896, 373851665, 2269612560, 2341996051, 229871128, 852526609, 1104874008, 1238861338, 189926952, 1015186961, 4367911464, 812353066, 1247742480, 1669531153, 548313616, 5016061459, 59738640, 1136428569, 59608600, 1859520026, 1356961304, 31884817, 2829687320, 52168210, 1544784400, 200574481, 66917904, 1876493845, 1367150104, 739640849, 747081232, 4250535442, 317229584, 738821649, 365596200, 3854796306, 95881744]

theorem len2 : tab2.length = 64 := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : checkList (fun j => 2 ^ j) 726 tab2 = true := by decide +kernel

def tab3 : List ℕ := [3934750225, 1099172376, 2760181267, 931990032, 1298171417, 310348304, 2146666026, 892276240, 894961169, 160401944, 147818002, 347015696, 44238353, 298490384, 316540443, 875990544, 3388802577, 1127916048, 1977091602, 3643836968, 1927153169, 1656360472, 3648947730, 78220816, 2319615505, 891390488, 2343208475, 260573752, 1542325777, 596872720, 2431223314, 619396624, 1954874905, 442403352, 1811252754, 2009532944, 2971305497, 84314640, 700188179, 1258589720, 222463505, 97750552, 509478418, 506239512, 356320809, 823995920, 372114962, 1801883176, 1745913361, 1061919248, 636159510, 521144848, 812451345, 611323432, 687736338, 25758224, 52430361, 1469124112, 2044921362, 981339664, 982320657, 821469712, 2279638547, 178001424]

theorem len3 : tab3.length = 64 := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : checkList (fun j => 2 ^ j) 790 tab3 = true := by decide +kernel

def tab4 : List ℕ := [504727057, 1612941848, 3101165098, 16189968, 1244661265, 1405786640, 734922258, 975473168, 62391825, 1331829264, 1034356243, 1798216208, 1531643417, 1658234384, 4052420114, 844079632, 621643281, 1126763024, 102041106, 317230616, 2276525585, 728972824, 1398081043, 3195375120, 421889553, 1126272528, 4040164882, 404818448, 13444187665, 1170475536, 279021074, 914951696, 1425933841, 1244563984, 728466963, 312317464, 2018543121, 2242447888, 213124626, 1138200120, 1375176209, 229188112, 1887012370, 1441237528, 1040123417, 1136003600, 5956765205, 2162238992, 1046283793, 1831537168, 847218194, 194120216, 2333312537, 3611232784, 595723794, 3268053520, 503645713, 1021778448, 3023308307, 271095320, 287409689, 4330359312, 558990866, 589305360]

theorem len4 : tab4.length = 64 := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : checkList (fun j => 2 ^ j) 854 tab4 = true := by decide +kernel

def tab5 : List ℕ := [1705215505, 1837340176, 3085993490, 1088951824, 1273660945, 188845584, 5614142995, 873205264, 591136273, 448203288, 312083986, 2322206224, 113903121, 3812891152, 3397944850, 1579354664, 1218741777, 1712264760, 1025639955, 1698500112, 719881745, 170265104, 8569849362, 17697336, 53151257, 30050840, 1033733650, 327061016, 1458046481, 436773392, 3301180955, 264867368, 422413849, 1100417552, 7202047506, 911641104, 2452063761, 33039896, 2217313818, 3233749520, 4106356241, 1760923160, 3446081046, 424744464, 1875281425, 113085976, 1049265682, 6704401936, 522028569, 196611600, 2207450642, 6982160, 1385104913, 151260688, 2607154707, 2154597912, 10949854745, 1369378320, 2418312722, 1817775640, 2184185369, 169545232, 7158400530, 615714328]

theorem len5 : tab5.length = 64 := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : checkList (fun j => 2 ^ j) 918 tab5 = true := by decide +kernel

def tab6 : List ℕ := [35128849, 1564085776, 2919499283, 3217695248, 1815545361, 1116509712, 969999890, 2615544336, 6074598929, 504407576, 1141245458, 839092776, 5119477265, 4918021648, 1291912723, 1532496400, 1806239249, 366778904, 5213750810, 556960272, 529401385, 1758988824, 1232111122, 1196886544, 508298769, 140709392, 1582728731, 2069073424, 180520465, 1251675664, 6139545114, 6977528336, 4402120209, 1104875024, 5623514650, 1995737624, 3263202833, 1705053720, 11059529237, 1516603992, 3015476753, 107744784, 9623668242, 852861456, 6208357929, 824806928, 4779247122, 5692394040, 3929703953, 2294123024, 5655070227, 5053552152, 4974708249, 1366429200, 16136013330, 2380073488, 5446075921, 113708560, 1807582738, 1335334440, 2055800337, 101030456, 936576531, 1605339664]

theorem len6 : tab6.length = 64 := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok6 : checkList (fun j => 2 ^ j) 982 tab6 = true := by decide +kernel

def tab7 : List ℕ := [2520450577, 75283984, 78841362, 3206223376]

theorem len7 : tab7.length = 4 := by decide +kernel

set_option maxHeartbeats 0 in
theorem ok7 : checkList (fun j => 2 ^ j) 1046 tab7 = true := by decide +kernel

end GW

set_option maxHeartbeats 0 in
theorem Conjectures.Goldbach.Rfc11ExtendedDyadicEdgeWitnesses : (∀ j : ℕ, 598≤j → j≤1049 → let n : ℕ := 2^j; ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n) := by
  intro j h1 h2
  have hall0 := GW.checkList_sound (fun j => 2 ^ j) GW.tab0 598 GW.ok0
  rw [GW.len0] at hall0
  have hall1 := GW.checkList_sound (fun j => 2 ^ j) GW.tab1 662 GW.ok1
  rw [GW.len1] at hall1
  have hall2 := GW.checkList_sound (fun j => 2 ^ j) GW.tab2 726 GW.ok2
  rw [GW.len2] at hall2
  have hall3 := GW.checkList_sound (fun j => 2 ^ j) GW.tab3 790 GW.ok3
  rw [GW.len3] at hall3
  have hall4 := GW.checkList_sound (fun j => 2 ^ j) GW.tab4 854 GW.ok4
  rw [GW.len4] at hall4
  have hall5 := GW.checkList_sound (fun j => 2 ^ j) GW.tab5 918 GW.ok5
  rw [GW.len5] at hall5
  have hall6 := GW.checkList_sound (fun j => 2 ^ j) GW.tab6 982 GW.ok6
  rw [GW.len6] at hall6
  have hall7 := GW.checkList_sound (fun j => 2 ^ j) GW.tab7 1046 GW.ok7
  rw [GW.len7] at hall7
  by_cases hc0 : j < 662
  · exact hall0 j (by omega) (by omega)
  by_cases hc1 : j < 726
  · exact hall1 j (by omega) (by omega)
  by_cases hc2 : j < 790
  · exact hall2 j (by omega) (by omega)
  by_cases hc3 : j < 854
  · exact hall3 j (by omega) (by omega)
  by_cases hc4 : j < 918
  · exact hall4 j (by omega) (by omega)
  by_cases hc5 : j < 982
  · exact hall5 j (by omega) (by omega)
  by_cases hc6 : j < 1046
  · exact hall6 j (by omega) (by omega)
  exact hall7 j (by omega) (by omega)
