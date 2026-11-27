import Mathlib

/-! ### 小素数试除证书（试除到 sqrt，模板复用仓库已验收生成器） -/

/-- `256` 以内素数表。 -/
def tinyPrimes : List ℕ := [
    2,3,5,7,11,13,17,19,23,29,
    31,37,41,43,47,53,59,61,67,71,
    73,79,83,89,97,101,103,107,109,113,
    127,131,137,139,149,151,157,163,167,173,
    179,181,191,193,197,199,211,223,227,229,
    233,239,241,251
  ]

/-- 小素数快速判素：试除到 sqrt（只试 `tinyPrimes`）。 -/
def isPrimeTiny (n : ℕ) : Bool :=
  decide (2 ≤ n) && !(tinyPrimes.any (fun r => n % r == 0 && r * r ≤ n))

lemma bool_not_eq_false {b : Bool} : (!b) = false → b = true := by
  cases b <;> simp

set_option maxRecDepth 10000 in
lemma tinyPrimes_prime_decide : tinyPrimes.all (fun r => decide (Nat.Prime r)) = true := by
  decide

lemma tinyPrimes_prime : ∀ r ∈ tinyPrimes, Nat.Prime r := by
  intro r hr
  exact of_decide_eq_true (List.all_eq_true.mp tinyPrimes_prime_decide r hr)

set_option maxRecDepth 10000 in
lemma tinyPrimes_complete_decide :
    (List.range 257).all (fun r => !(decide (Nat.Prime r)) || decide (r ∈ tinyPrimes)) = true := by
  decide

lemma tinyPrimes_complete {r : ℕ} (hr : Nat.Prime r) (hr2 : r ≤ 256) : r ∈ tinyPrimes := by
  have hall := List.all_eq_true.mp tinyPrimes_complete_decide r (List.mem_range.mpr (by omega))
  have hprime : decide (Nat.Prime r) = true := decide_eq_true hr
  rw [hprime] at hall
  simp at hall
  exact hall

set_option maxRecDepth 10000 in
lemma isPrimeTiny_spec {n : ℕ} (hn : n < 66049) (h : isPrimeTiny n = true) :
    Nat.Prime n := by
  unfold isPrimeTiny at h
  rw [Bool.and_eq_true] at h
  have h2 : 2 ≤ n := of_decide_eq_true h.1
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h2, ?_⟩
  intro m hm2 hmsqrt hmdvd
  obtain ⟨r, hrprime, hrm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  have hrmle : r ≤ m := Nat.le_of_dvd (by omega) hrm
  have hsqrt : Nat.sqrt n < 257 := by
    rw [Nat.sqrt_lt']
    omega
  have hrTINY : r ≤ 256 := by omega
  have hrmem : r ∈ tinyPrimes := tinyPrimes_complete hrprime hrTINY
  have hrr : r * r ≤ n := by
    have h1 : r ≤ Nat.sqrt n := by omega
    exact (Nat.le_sqrt.mp h1)
  have hany : (tinyPrimes.any (fun x => n % x == 0 && x * x ≤ n)) = true := by
    apply List.any_eq_true.mpr
    refine ⟨r, hrmem, ?_⟩
    have hmod : n % r = 0 := Nat.mod_eq_zero_of_dvd (hrm.trans hmdvd)
    simp [hmod, hrr]
  have hnot : (!(tinyPrimes.any (fun x => n % x == 0 && x * x ≤ n))) = true := h.2
  rw [hany] at hnot
  simpa using hnot

/-! ### Lucas 证书 → `Nat.Prime` -/

lemma prime_mem_of_dvd_prod {fs : List ℕ} {q : ℕ}
    (hfs : ∀ r ∈ fs, Nat.Prime r) (hq : Nat.Prime q) (hd : q ∣ fs.prod) : q ∈ fs := by
  induction fs with
  | nil =>
      rw [List.prod_nil] at hd
      have hle : q ≤ 1 := Nat.le_of_dvd (by norm_num) hd
      have := hq.two_le
      omega
  | cons a t ih =>
      rw [List.prod_cons] at hd
      rcases (hq.dvd_mul).mp hd with h | h
      · have hqa : q = a := (Nat.prime_dvd_prime_iff_eq hq (hfs a (List.mem_cons_self))).mp h
        subst hqa; exact List.mem_cons_self
      · exact List.mem_cons_of_mem a (ih (fun r hr => hfs r (List.mem_cons_of_mem a hr)) h)

lemma cast_powMod (p a k : ℕ) : ((Nat.powMod a k p : ℕ) : ZMod p) = (a : ZMod p)^k := by
  rw [Nat.powMod_def, ZMod.natCast_mod, Nat.cast_pow]

theorem prime_of_cert {p a : ℕ} {fs : List ℕ} (hp2 : 2 < p) (hprod : fs.prod = p - 1)
    (hfs : ∀ r ∈ fs, Nat.Prime r)
    (ha : Nat.powMod a (p - 1) p = 1 % p)
    (hd : ∀ r ∈ fs, Nat.powMod a ((p - 1) / r) p ≠ 1 % p) : Nat.Prime p := by
  have hp1 : 1 < p := by omega
  refine lucas_primality p (a : ZMod p) ?_ ?_
  · have h := congrArg (fun n : ℕ => (n : ZMod p)) ha
    rw [cast_powMod] at h
    rwa [Nat.mod_eq_of_lt hp1, Nat.cast_one] at h
  · intro q hq hqd
    have hqmem : q ∈ fs := by
      have hqt : q ∣ fs.prod := by rw [hprod]; exact hqd
      exact prime_mem_of_dvd_prod hfs hq hqt
    intro hzmod
    have hnatcast : ((Nat.powMod a ((p - 1) / q) p : ℕ) : ZMod p) = ((1 % p : ℕ) : ZMod p) := by
      rw [cast_powMod, hzmod, Nat.mod_eq_of_lt hp1, Nat.cast_one]
    have hmod : Nat.ModEq p (Nat.powMod a ((p - 1) / q) p) (1 % p) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp hnatcast
    have hlt1 : Nat.powMod a ((p - 1) / q) p < p := by
      rw [Nat.powMod_def]; exact Nat.mod_lt _ (by omega)
    have hlt2 : 1 % p < p := Nat.mod_lt _ (by omega)
    exact hd q hqmem (Nat.ModEq.eq_of_lt_of_lt hmod hlt1 hlt2)



/-! ### 大素数 Lucas 证书（Pratt 树，118 个节点） -/

set_option maxRecDepth 100000 in
theorem prime_node_0 : Nat.Prime 78427 := by
  refine prime_of_cert (p := 78427) (a := 3) (fs := [2, 3, 3, 4357]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_1 : Nat.Prime 71647 := by
  refine prime_of_cert (p := 71647) (a := 3) (fs := [2, 3, 11941]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_2 : Nat.Prime 286589 := by
  refine prime_of_cert (p := 286589) (a := 2) (fs := [2, 2, 71647]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_1
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_3 : Nat.Prime 573179 := by
  refine prime_of_cert (p := 573179) (a := 2) (fs := [2, 286589]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_2
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_4 : Nat.Prime 142148393 := by
  refine prime_of_cert (p := 142148393) (a := 3) (fs := [2, 2, 2, 31, 573179]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_3
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_5 : Nat.Prime 425023695071 := by
  refine prime_of_cert (p := 425023695071) (a := 34) (fs := [2, 5, 13, 23, 142148393]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_4
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_6 : Nat.Prime 3999999999999998041 := by
  refine prime_of_cert (p := 3999999999999998041) (a := 14) (fs := [2, 2, 2, 3, 5, 78427, 425023695071]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_0
    · exact prime_node_5
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_7 : Nat.Prime 7102591 := by
  refine prime_of_cert (p := 7102591) (a := 3) (fs := [2, 3, 5, 11, 21523]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_8 : Nat.Prime 10595153 := by
  refine prime_of_cert (p := 10595153) (a := 3) (fs := [2, 2, 2, 2, 191, 3467]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_9 : Nat.Prime 3999999999999998143 := by
  refine prime_of_cert (p := 3999999999999998143) (a := 3) (fs := [2, 3, 3, 2953, 7102591, 10595153]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_7
    · exact prime_node_8
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_10 : Nat.Prime 1198403 := by
  refine prime_of_cert (p := 1198403) (a := 2) (fs := [2, 223, 2687]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_11 : Nat.Prime 481758007 := by
  refine prime_of_cert (p := 481758007) (a := 3) (fs := [2, 3, 67, 1198403]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_10
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_12 : Nat.Prime 1037865469 := by
  refine prime_of_cert (p := 1037865469) (a := 2) (fs := [2, 2, 3, 47, 61, 97, 311]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_13 : Nat.Prime 4151461877 := by
  refine prime_of_cert (p := 4151461877) (a := 2) (fs := [2, 2, 1037865469]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_12
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_14 : Nat.Prime 3999999999999998279 := by
  refine prime_of_cert (p := 3999999999999998279) (a := 17) (fs := [2, 481758007, 4151461877]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_11
    · exact prime_node_13
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_15 : Nat.Prime 5624461 := by
  refine prime_of_cert (p := 5624461) (a := 7) (fs := [2, 2, 3, 3, 5, 31247]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_16 : Nat.Prime 3999999999999998369 := by
  refine prime_of_cert (p := 3999999999999998369) (a := 3) (fs := [2, 2, 2, 2, 2, 11, 11, 37, 277, 17921, 5624461]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_15
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_17 : Nat.Prime 310559 := by
  refine prime_of_cert (p := 310559) (a := 7) (fs := [2, 31, 5009]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_18 : Nat.Prime 41666666666666651 := by
  refine prime_of_cert (p := 41666666666666651) (a := 2) (fs := [2, 5, 5, 7, 19, 23, 739, 1187, 310559]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_17
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_19 : Nat.Prime 3999999999999998497 := by
  refine prime_of_cert (p := 3999999999999998497) (a := 5) (fs := [2, 2, 2, 2, 2, 3, 41666666666666651]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_18
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_20 : Nat.Prime 274333 := by
  refine prime_of_cert (p := 274333) (a := 2) (fs := [2, 2, 3, 22861]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_21 : Nat.Prime 39503953 := by
  refine prime_of_cert (p := 39503953) (a := 5) (fs := [2, 2, 2, 2, 3, 3, 274333]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_20
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_22 : Nat.Prime 1185118591 := by
  refine prime_of_cert (p := 1185118591) (a := 3) (fs := [2, 3, 5, 39503953]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_21
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_23 : Nat.Prime 1348664956559 := by
  refine prime_of_cert (p := 1348664956559) (a := 7) (fs := [2, 569, 1185118591]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_22
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_24 : Nat.Prime 2697329913119 := by
  refine prime_of_cert (p := 2697329913119) (a := 7) (fs := [2, 1348664956559]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_23
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_25 : Nat.Prime 1073537305421363 := by
  refine prime_of_cert (p := 1073537305421363) (a := 2) (fs := [2, 199, 2697329913119]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_24
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_26 : Nat.Prime 3999999999999998539 := by
  refine prime_of_cert (p := 3999999999999998539) (a := 3) (fs := [2, 3, 3, 3, 3, 23, 1073537305421363]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_25
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_27 : Nat.Prime 654606202001 := by
  refine prime_of_cert (p := 654606202001) (a := 3) (fs := [2, 2, 2, 2, 5, 5, 5, 19, 3343, 5153]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_28 : Nat.Prime 45454545454545439 := by
  refine prime_of_cert (p := 45454545454545439) (a := 3) (fs := [2, 3, 71, 163, 654606202001]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_27
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_29 : Nat.Prime 3999999999999998633 := by
  refine prime_of_cert (p := 3999999999999998633) (a := 3) (fs := [2, 2, 2, 11, 45454545454545439]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_28
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_30 : Nat.Prime 2917403 := by
  refine prime_of_cert (p := 2917403) (a := 2) (fs := [2, 691, 2111]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_31 : Nat.Prime 38953164857 := by
  refine prime_of_cert (p := 38953164857) (a := 3) (fs := [2, 2, 2, 1669, 2917403]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_30
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_32 : Nat.Prime 3999999999999998941 := by
  refine prime_of_cert (p := 3999999999999998941) (a := 2) (fs := [2, 2, 3, 5, 11, 157, 991, 38953164857]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_31
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_33 : Nat.Prime 392827 := by
  refine prime_of_cert (p := 392827) (a := 2) (fs := [2, 3, 7, 47, 199]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_34 : Nat.Prime 5239526527 := by
  refine prime_of_cert (p := 5239526527) (a := 3) (fs := [2, 3, 3, 3, 13, 19, 392827]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_33
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_35 : Nat.Prime 125748636649 := by
  refine prime_of_cert (p := 125748636649) (a := 17) (fs := [2, 2, 2, 3, 5239526527]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_34
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_36 : Nat.Prime 3999999999999999011 := by
  refine prime_of_cert (p := 3999999999999999011) (a := 2) (fs := [2, 5, 89, 103, 347, 125748636649]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_35
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_37 : Nat.Prime 579613 := by
  refine prime_of_cert (p := 579613) (a := 2) (fs := [2, 2, 3, 11, 4391]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_38 : Nat.Prime 2926699093 := by
  refine prime_of_cert (p := 2926699093) (a := 2) (fs := [2, 2, 3, 3, 67, 193, 6287]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_39 : Nat.Prime 3999999999999999223 := by
  refine prime_of_cert (p := 3999999999999999223) (a := 3) (fs := [2, 3, 3, 131, 579613, 2926699093]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_37
    · exact prime_node_38
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_40 : Nat.Prime 5548607 := by
  refine prime_of_cert (p := 5548607) (a := 5) (fs := [2, 7, 251, 1579]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_41 : Nat.Prime 244138709 := by
  refine prime_of_cert (p := 244138709) (a := 2) (fs := [2, 2, 11, 5548607]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_40
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_42 : Nat.Prime 2929664509 := by
  refine prime_of_cert (p := 2929664509) (a := 6) (fs := [2, 2, 3, 244138709]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_41
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_43 : Nat.Prime 566251415628539 := by
  refine prime_of_cert (p := 566251415628539) (a := 2) (fs := [2, 241, 401, 2929664509]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_42
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_44 : Nat.Prime 3999999999999999497 := by
  refine prime_of_cert (p := 3999999999999999497) (a := 3) (fs := [2, 2, 2, 883, 566251415628539]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_43
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_45 : Nat.Prime 1345037 := by
  refine prime_of_cert (p := 1345037) (a := 3) (fs := [2, 2, 7, 11, 11, 397]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_46 : Nat.Prime 4008551 := by
  refine prime_of_cert (p := 4008551) (a := 14) (fs := [2, 5, 5, 7, 13, 881]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_47 : Nat.Prime 2693746273 := by
  refine prime_of_cert (p := 2693746273) (a := 15) (fs := [2, 2, 2, 2, 2, 3, 7, 4008551]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_46
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_48 : Nat.Prime 999999999999999877 := by
  refine prime_of_cert (p := 999999999999999877) (a := 5) (fs := [2, 2, 3, 23, 1345037, 2693746273]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_45
    · exact prime_node_47
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_49 : Nat.Prime 3999999999999999509 := by
  refine prime_of_cert (p := 3999999999999999509) (a := 2) (fs := [2, 2, 999999999999999877]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_48
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_50 : Nat.Prime 327689 := by
  refine prime_of_cert (p := 327689) (a := 3) (fs := [2, 2, 2, 40961]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_51 : Nat.Prime 655379 := by
  refine prime_of_cert (p := 655379) (a := 2) (fs := [2, 327689]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_50
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_52 : Nat.Prime 7703863487539 := by
  refine prime_of_cert (p := 7703863487539) (a := 3) (fs := [2, 3, 61, 32117, 655379]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_51
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_53 : Nat.Prime 3999999999999999581 := by
  refine prime_of_cert (p := 3999999999999999581) (a := 7) (fs := [2, 2, 5, 13, 1997, 7703863487539]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_52
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_54 : Nat.Prime 1077697 := by
  refine prime_of_cert (p := 1077697) (a := 5) (fs := [2, 2, 2, 2, 2, 2, 3, 3, 1871]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_55 : Nat.Prime 149855393 := by
  refine prime_of_cert (p := 149855393) (a := 3) (fs := [2, 2, 2, 2, 2, 1307, 3583]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_56 : Nat.Prime 299710787 := by
  refine prime_of_cert (p := 299710787) (a := 2) (fs := [2, 149855393]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_55
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_57 : Nat.Prime 103100510729 := by
  refine prime_of_cert (p := 103100510729) (a := 3) (fs := [2, 2, 2, 43, 299710787]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_56
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_58 : Nat.Prime 4000000000000000069 := by
  refine prime_of_cert (p := 4000000000000000069) (a := 6) (fs := [2, 2, 3, 3, 1077697, 103100510729]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_54
    · exact prime_node_57
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_59 : Nat.Prime 83617 := by
  refine prime_of_cert (p := 83617) (a := 5) (fs := [2, 2, 2, 2, 2, 3, 13, 67]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_60 : Nat.Prime 3010213 := by
  refine prime_of_cert (p := 3010213) (a := 2) (fs := [2, 2, 3, 3, 83617]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_59
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_61 : Nat.Prime 7401767 := by
  refine prime_of_cert (p := 7401767) (a := 5) (fs := [2, 17, 293, 743]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_62 : Nat.Prime 4000000000000000147 := by
  refine prime_of_cert (p := 4000000000000000147) (a := 2) (fs := [2, 3, 29921, 3010213, 7401767]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_60
    · exact prime_node_61
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_63 : Nat.Prime 3527057 := by
  refine prime_of_cert (p := 3527057) (a := 5) (fs := [2, 2, 2, 2, 13, 31, 547]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_64 : Nat.Prime 567044989633 := by
  refine prime_of_cert (p := 567044989633) (a := 5) (fs := [2, 2, 2, 2, 2, 2, 3, 3, 11, 23, 73, 151, 353]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_65 : Nat.Prime 4000000000000000163 := by
  refine prime_of_cert (p := 4000000000000000163) (a := 2) (fs := [2, 3527057, 567044989633]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_63
    · exact prime_node_64
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_66 : Nat.Prime 2145734401 := by
  refine prime_of_cert (p := 2145734401) (a := 11) (fs := [2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 5, 23, 43, 113]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_67 : Nat.Prime 124452595259 := by
  refine prime_of_cert (p := 124452595259) (a := 2) (fs := [2, 29, 2145734401]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_66
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_68 : Nat.Prime 248905190519 := by
  refine prime_of_cert (p := 248905190519) (a := 13) (fs := [2, 124452595259]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_67
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_69 : Nat.Prime 497810381039 := by
  refine prime_of_cert (p := 497810381039) (a := 11) (fs := [2, 248905190519]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_68
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_70 : Nat.Prime 4000000000000000333 := by
  refine prime_of_cert (p := 4000000000000000333) (a := 6) (fs := [2, 2, 3, 7, 23, 4159, 497810381039]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_69
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_71 : Nat.Prime 970061 := by
  refine prime_of_cert (p := 970061) (a := 2) (fs := [2, 2, 5, 7, 13, 13, 41]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_72 : Nat.Prime 21721186845649 := by
  refine prime_of_cert (p := 21721186845649) (a := 13) (fs := [2, 2, 2, 2, 3, 3, 131, 1187, 970061]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_71
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_73 : Nat.Prime 86884747382597 := by
  refine prime_of_cert (p := 86884747382597) (a := 2) (fs := [2, 2, 21721186845649]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_72
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_74 : Nat.Prime 4000000000000000687 := by
  refine prime_of_cert (p := 4000000000000000687) (a := 3) (fs := [2, 3, 7673, 86884747382597]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_73
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_75 : Nat.Prime 264283 := by
  refine prime_of_cert (p := 264283) (a := 12) (fs := [2, 3, 17, 2591]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_76 : Nat.Prime 108109218419 := by
  refine prime_of_cert (p := 108109218419) (a := 2) (fs := [2, 479, 10111, 11161]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_77 : Nat.Prime 4000000000000000781 := by
  refine prime_of_cert (p := 4000000000000000781) (a := 2) (fs := [2, 2, 5, 7, 264283, 108109218419]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_75
    · exact prime_node_76
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_78 : Nat.Prime 872471 := by
  refine prime_of_cert (p := 872471) (a := 13) (fs := [2, 5, 43, 2029]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_79 : Nat.Prime 6979769 := by
  refine prime_of_cert (p := 6979769) (a := 3) (fs := [2, 2, 2, 872471]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_78
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_80 : Nat.Prime 107399713 := by
  refine prime_of_cert (p := 107399713) (a := 5) (fs := [2, 2, 2, 2, 2, 3, 7, 71, 2251]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_81 : Nat.Prime 4000000000000000793 := by
  refine prime_of_cert (p := 4000000000000000793) (a := 3) (fs := [2, 2, 2, 23, 29, 6979769, 107399713]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_79
    · exact prime_node_80
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_82 : Nat.Prime 1283509 := by
  refine prime_of_cert (p := 1283509) (a := 6) (fs := [2, 2, 3, 3, 101, 353]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_83 : Nat.Prime 24760136180749 := by
  refine prime_of_cert (p := 24760136180749) (a := 2) (fs := [2, 2, 3, 97, 16573, 1283509]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_82
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_84 : Nat.Prime 4000000000000000951 := by
  refine prime_of_cert (p := 4000000000000000951) (a := 3) (fs := [2, 3, 3, 5, 5, 359, 24760136180749]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_83
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_85 : Nat.Prime 249463 := by
  refine prime_of_cert (p := 249463) (a := 3) (fs := [2, 3, 3, 13859]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_86 : Nat.Prime 288773 := by
  refine prime_of_cert (p := 288773) (a := 2) (fs := [2, 2, 11, 6563]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_87 : Nat.Prime 577547 := by
  refine prime_of_cert (p := 577547) (a := 2) (fs := [2, 288773]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_86
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_88 : Nat.Prime 4000000000000001089 := by
  refine prime_of_cert (p := 4000000000000001089) (a := 19) (fs := [2, 2, 2, 2, 2, 2, 3, 7, 7, 13, 227, 249463, 577547]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_85
    · exact prime_node_87
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_89 : Nat.Prime 663557 := by
  refine prime_of_cert (p := 663557) (a := 2) (fs := [2, 2, 19, 8731]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_90 : Nat.Prime 8030039 := by
  refine prime_of_cert (p := 8030039) (a := 23) (fs := [2, 131, 30649]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_91 : Nat.Prime 4000000000000001209 := by
  refine prime_of_cert (p := 4000000000000001209) (a := 17) (fs := [2, 2, 2, 3, 31, 1009, 663557, 8030039]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_89
    · exact prime_node_90
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_92 : Nat.Prime 37317457 := by
  refine prime_of_cert (p := 37317457) (a := 5) (fs := [2, 2, 2, 2, 3, 3, 3, 11, 7853]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_93 : Nat.Prime 6920415224913497 := by
  refine prime_of_cert (p := 6920415224913497) (a := 3) (fs := [2, 2, 2, 79, 139, 2111, 37317457]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_92
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_94 : Nat.Prime 4000000000000001267 := by
  refine prime_of_cert (p := 4000000000000001267) (a := 2) (fs := [2, 17, 17, 6920415224913497]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_93
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_95 : Nat.Prime 135757 := by
  refine prime_of_cert (p := 135757) (a := 2) (fs := [2, 2, 3, 3, 3, 3, 419]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_96 : Nat.Prime 4000000000000001693 := by
  refine prime_of_cert (p := 4000000000000001693) (a := 2) (fs := [2, 2, 173, 277, 2377, 64667, 135757]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_95
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_97 : Nat.Prime 34757507 := by
  refine prime_of_cert (p := 34757507) (a := 2) (fs := [2, 7, 53, 139, 337]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_98 : Nat.Prime 57541526209 := by
  refine prime_of_cert (p := 57541526209) (a := 7) (fs := [2, 2, 2, 2, 2, 2, 3, 3, 37, 769, 3511]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_99 : Nat.Prime 4000000000000001927 := by
  refine prime_of_cert (p := 4000000000000001927) (a := 5) (fs := [2, 34757507, 57541526209]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_97
    · exact prime_node_98
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_100 : Nat.Prime 103049821291 := by
  refine prime_of_cert (p := 103049821291) (a := 3) (fs := [2, 3, 5, 13, 16091, 16421]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_101 : Nat.Prime 4000000000000003217 := by
  refine prime_of_cert (p := 4000000000000003217) (a := 3) (fs := [2, 2, 2, 2, 7, 41, 79, 107, 103049821291]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_100
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_102 : Nat.Prime 438827 := by
  refine prime_of_cert (p := 438827) (a := 2) (fs := [2, 313, 701]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_103 : Nat.Prime 129839255107 := by
  refine prime_of_cert (p := 129839255107) (a := 2) (fs := [2, 3, 11, 4483, 438827]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_102
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_104 : Nat.Prime 4000000000000003669 := by
  refine prime_of_cert (p := 4000000000000003669) (a := 2) (fs := [2, 2, 3, 3, 3, 109, 2617, 129839255107]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_103
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_105 : Nat.Prime 291503 := by
  refine prime_of_cert (p := 291503) (a := 5) (fs := [2, 23, 6337]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_106 : Nat.Prime 297333061 := by
  refine prime_of_cert (p := 297333061) (a := 6) (fs := [2, 2, 3, 5, 17, 291503]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_105
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_107 : Nat.Prime 8156440529353 := by
  refine prime_of_cert (p := 8156440529353) (a := 10) (fs := [2, 2, 2, 3, 3, 3, 127, 297333061]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_106
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_108 : Nat.Prime 4000000000000004731 := by
  refine prime_of_cert (p := 4000000000000004731) (a := 3) (fs := [2, 3, 3, 5, 5449, 8156440529353]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_107
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_109 : Nat.Prime 70619 := by
  refine prime_of_cert (p := 70619) (a := 2) (fs := [2, 17, 31, 67]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_110 : Nat.Prime 96269 := by
  refine prime_of_cert (p := 96269) (a := 2) (fs := [2, 2, 41, 587]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_111 : Nat.Prime 192539 := by
  refine prime_of_cert (p := 192539) (a := 2) (fs := [2, 96269]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_110
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_112 : Nat.Prime 4000000000000005733 := by
  refine prime_of_cert (p := 4000000000000005733) (a := 2) (fs := [2, 2, 3, 73, 499, 673, 70619, 192539]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_109
    · exact prime_node_111
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_113 : Nat.Prime 128629 := by
  refine prime_of_cert (p := 128629) (a := 11) (fs := [2, 2, 3, 3, 3, 3, 397]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_114 : Nat.Prime 850237691 := by
  refine prime_of_cert (p := 850237691) (a := 6) (fs := [2, 5, 661, 128629]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_113
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_115 : Nat.Prime 10202852293 := by
  refine prime_of_cert (p := 10202852293) (a := 2) (fs := [2, 2, 3, 850237691]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_114
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_116 : Nat.Prime 163245636689 := by
  refine prime_of_cert (p := 163245636689) (a := 3) (fs := [2, 2, 2, 2, 10202852293]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_115
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

set_option maxRecDepth 100000 in
theorem prime_node_117 : Nat.Prime 4000000000000005929 := by
  refine prime_of_cert (p := 4000000000000005929) (a := 3) (fs := [2, 2, 2, 71, 179, 241, 163245636689]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact isPrimeTiny_spec (by decide) (by decide)
    · exact prime_node_116
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide


/-! ### 见证大素数表 -/

def Qlist : List ℕ := [3999999999999998041, 3999999999999998143, 3999999999999998279, 3999999999999998369, 3999999999999998497, 3999999999999998539, 3999999999999998633, 3999999999999998941, 3999999999999999011, 3999999999999999223, 3999999999999999497, 3999999999999999509, 3999999999999999581, 4000000000000000069, 4000000000000000147, 4000000000000000163, 4000000000000000333, 4000000000000000687, 4000000000000000781, 4000000000000000793, 4000000000000000951, 4000000000000001089, 4000000000000001209, 4000000000000001267, 4000000000000001693, 4000000000000001927, 4000000000000003217, 4000000000000003669, 4000000000000004731, 4000000000000005733, 4000000000000005929]

theorem Qlist_prime : ∀ q ∈ Qlist, Nat.Prime q := by
  intro q hq
  simp only [Qlist, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_node_6
  · exact prime_node_9
  · exact prime_node_14
  · exact prime_node_16
  · exact prime_node_19
  · exact prime_node_26
  · exact prime_node_29
  · exact prime_node_32
  · exact prime_node_36
  · exact prime_node_39
  · exact prime_node_44
  · exact prime_node_49
  · exact prime_node_53
  · exact prime_node_58
  · exact prime_node_62
  · exact prime_node_65
  · exact prime_node_70
  · exact prime_node_74
  · exact prime_node_77
  · exact prime_node_81
  · exact prime_node_84
  · exact prime_node_88
  · exact prime_node_91
  · exact prime_node_94
  · exact prime_node_96
  · exact prime_node_99
  · exact prime_node_101
  · exact prime_node_104
  · exact prime_node_108
  · exact prime_node_112
  · exact prime_node_117


/-! ### 见证索引位图与逐点核验 -/

def W : ℕ := 510
def BITS : ℕ := 5
def BASE : ℕ := 32

def chunkWord : ℕ → ℕ
  | 0 => 0xa30844d128a05c40200c4108c015002209cc01cce0100463844d00c0311006204c0020891044338444198001140308140109a13240209044008811804c3806100820104260090500ca410466700400c80311008200c00888d504020864120c00300280004148820184a2005410a1a0180e320064098001902300c4000c0231402080c0008011004600c6900800104220054118880114430804013ca0404c320c4000882414020a84118ce1500880004400c0414008284c00a8a111042004c509822504220804018c033240320441008201802a2906d0212018403210cd00c201008a000400bc011148c28061008014000220064108221102600041208a05004601540188a04000208c640a002404020004108ce2600a20804400c0119066084410b0041a422284c01a02011142000402a0001108808840008a13040a090c0
  | 1 => 0x3084470a8011842200c60008823140a800411a88210066000614888310423005e0008804040200044220201902608a6412001314620846100c0311c280010100c001100200547088263006370100120211a40228c40018023046a080411ac0011086089050182010063208cd0082110002200c4128a2404e3008604880142403090c0108e01002a00c41098a0180082910100d261046200580098011100b080c01080930442680c7188001908f00441088003242300940008201800a214600a001591e600841009aa53497084c000c001004628041308e330022205e110c20184020856e198004148680c4000ce340002084650180519c86000490080258028004c000ca11844308c4713001184c2000600088341c224906028c2078066080440092411c03004c0188871800200d8512824110220804418c813000220500
  | 2 => 0x3384c5228e31042300c4008801400080916101a00180260858540c0310403204d00082111c420006429800184030094008803314232004000c22100ac00d45008805800238d45008241008a005040a0201052220049028e43004b2847018ce259426009410888050063384c002c8018002004670a0a3404e20084100ce1604236804020c001108a491410082410402204c900c8030463008401bc001240600044288a15002309041418021802600c4100da211c630050008c81400030a06713ce310402000c008803314224804918c00110263884100c2012402010c00a1274046600065118e0194830804e01881440620804710801300262806108c001842201a41089a11108b09500118a01380c09060018a23000208044188001142a000442200030403289802a8211910220460098a2110c200040088825140828060
  | 3 => 0x62009040c801504020944000ce430042200611088011046000490880230063008c5120201340200440319a0b84c22096401801514234a0d000c2011046084690ac2410022284c10208410406008650a0a111003200411088178002210c00188018066000610200419c62018c00adc011c030806d0a8044040600e69089a23042208560188001007829061709a011c0229900328a03004a0084509820505230004002002300022044120801114c62846108ca534002685400c88010103008601a0251042208c4101803300020a84102800114282850500c0014002208c7228814004a002400a0031048800060088015140b88044008201b82a694640a082bc003008c7088201846200c4411820444030806908883300024806140ce011028a044420880300060090128c26100420846014da041022010470080a6046228245
  | 4 => 0x27056021823410c300c5000881304c22206002a0019026380450082510463684d004881100420850023c211940200e641080441c02681811cc801012f00c6100ca01040b0054000a0630006088440a82110506280d000c01354020844d2ac011904800101018a0310a388940088204000f00444118221040220cc0009a24000309105118001102838d6522c20301a220cc100ca410046001651980011023012600bc81400030806158ce51805308c49098021a448008c70092111083080c0098001140238c40008034144222060188203504c688452082811006b09801a0201804a0844709800404820884e08c01500234844419821300664810d20805180220050000ca0104aa0144019820110080806100c8130012218450088240028000410192018462004c525c2118162080400b003190080006108ca33046208061
  | 5 => 0x63088c40a801114230204400c024008209869008811114649164008201040638980220201000380044298a01048201440098833400a0904111921180680014408ea2100482850108c2418462009650a000410223806008801350032104500e8031c2c08c4900800180e300d8108c20190a2080d51a0a0104020805010c8130442281601082511028098442080010028704c0188a741c0200c40118a1404060084100801600230804022c211944a082f102c0319028285000c88c184060054d818001100308060108a330003284c000920180286818400820184a600cd002c29100022006013c24114c60006100882434830804720826300520046423022300e2704c54c9a4180422145409800105020a14000c83400620846000d2518026284640082219cc838941209201100302040120201a42201040008017944268064
  | 6 => 0xb880c41a02010402010611880b500432004110c801809700c610a0a01802600985220211806200444298031108320841088014140220500188003102a08061308823000300d4000c24104e22184412800584062886702dc2500224804010c011104a384412088898066004c1120891a402001ed0a0a0110230004100ca43000b09841028014382808d04008021102c204c010d2010417080402b001404eb00c600980230403a8060208203002648041008a259cca005000c8893000200c640a280134220016912ca5500884806110c0319048284610180010422005801a080110573806d19821438e209c4408801980420a86400c0719ca60010500c02185222090908c217800220d600a820184023904028a21624230844010821100aa0104d421a03000a010c1189a05810300d45120a1110062806000da14000820460
  | 7 => 0x2005440b0a34100629461021a1504680810410ce0100880804e008035100a288c002880194a2488641980141013008400088431c0209c4001a2031046088650880098422384c910e06300020a511228e1104c2689e01180530422684601bce0414260005b02022104ac004c012c81584060086419801138e20016400c8150408080c020821182060146400c241900200980088861000308c55298201840301040089a14000209049288221008aa014523c001444268d00108811006f004640980051403010401888330028704c400c8111c2a48461088821c402024c100c2011c660804d0a003405830804100da341c024810400800110660944108800c0006204c0021201448a01c400a0021842c0804900ce2514238996011800180663846d02c047b80a886411888018446000400992313423080c1109a24000209981
  | 8 => 0x62080c0248065100200d61120823042208044298e7300264844160c801000c20d0002ca73004a2090552001114820026028c8145042080410080131c280006520c003102601141089a7414062185c1b0224040b294600a801340022804112c211802a2804e20c00184a2288c920c84400e200505118001900648941408023000308047009211002a00c413a0ab18428388c500921180633814451801105e308c60129a430402680c01880519c280016d088221240800cc7228a9104020046049803424e3009e10080479c830830502c201804828069408251244200641020291108f388450980011083390c0108a2400022044d009c2180cc08c6400800500c2284d50a0201000608c4d0bce6104220086e00884314420844018c813002f805010088018002205403888031442000470a0e0510260884000c014040380067
  | 9 => 0x4f20040119a01840309060009c1400032106500a01114260044d02c201c046219151082112462000601b020104020904428da2524032806000a00580b328505099c230002688c11202410062000400c8e1105423884700c013142829cc100c807b4880016140c02101a320cc0008205840300c4e099201a40b200440a8015042371c490180811c4629061330071000800900088a019006080651a8201100b000641988231c22218653a8021942c0084d08800510622090000c285822248060130a456cc2281e1088a362462480411a8e03006f29c4170c20300220050502081184463ac4513c00504830895031801558022044e38c011002a0006100a02340080294d1a0211100300cc012024424030ac41008a440402200c110c0151c26682440a0221000f20541248a7100e2201600a00213483008443a8023240308105
  | 10 => 0x66709001a001105220904110c013040a20460108e011066480690880079028a84c12082611c0b00c403200340402008440080199c220985002d20194880832102c0430046284c11202a18446004440a8a0110032014018ac1604232850001800190260946500802180a300d89020201146a080671302310406000c4008034040268040388231104628c614982218042204c012084180430006d0b2801048301cce018a2400422850928801400262850400803110e2389e0188201106300cc0118204048b09c4902086314030804102c20100c63850963c0210003284c008ca11810200460098a01108209060320065000b0986400c271002a01444008803040200d410082019482220c032001184822804008c81300c8201e029820110460104508800300233850520821134020044513ca0594082286110a2150023218c0
  | 11 => 0x200047218e14140609040188843002a0984d128811942c0004100ce214063299e02648418402709002b0a11842b20260108847a40348040208021102809864488e21042301141088a9190030004722001104e6380c400c82350620818010c2316c260006108800110c26854108c264100b004511a1a21242329c40009c2300422810100c00790680984900c00c004820501008811354b801e4118001842639c4109802524030844020c201c45908d84008003100320cc71882858062000c509800111820804000804400122116018ce51142ae018520c2210166005070202043882204c0198011c4880804908801514232004410c2540046289490302818066288c1009a419006094401a0a0110082004700ce640023204611888098026009053880050462288c020c84184022044722824110220006700c095042868060
  | 12 => 0x8208c4709800590820204011806604030a04000c8518028000650180311026395e00a8803140308860198a11343800c40408013142208064128201c4262810930c0010402289000882419002480671b002184027006008a22600282804120ce13344a018613088030062208c5089a1104a200445160201ed222004100c0152402205606a80219026394442202011003005010088110002204440a001190060a8c10080150023081091ac811004a288410080311c0600df60082019006700600a001134082806062c8464003085071080731046281010882018022284c504820180023810d23ce3104c621d60018e2404436b06540800100b20010d0082018052204c102da15848300cc5298201110200cc90988450048210c00082940046005010181211c03005e01882c1000308864298a04248320cc1098013006321184
  | 13 => 0xe2000c4098204108201040088e13141221c4d109201542c084613ac873004800cc7221201806208445198005140638061108e1434222016002c0551426085610882257053288c000c261a4022244412801410032006100c04514a30810000c00180464945130824100c268501328291040208044198011382f088400088260403890c41aa254007838d0100802580220054008c8130002200400bca1124260087d0a08250428085e128c02100882804400dc01b8020050112880184020814519820604230004000c04304682184140823112262886100802310060094018c8110006000451a8e01b4c200c4111803400220906513c007902c2804d08c0218406204c020a243040248d040a002124228826038c8131423080440082019c4a00d850300218423008c11a020104832004e220011100308040088a130008490c0
  | 14 => 0xf00cc0149239254200c4700ce25006220045069204004c084614300d30008204c712e09104423844019922514860216700ca133422238600280119028001040082d11c620091000c2618486088400dc21144024806130804514080806119821300662884120883980a2004c00a1c0180020806451804504224896008c01500032050712c0319cc62906100a2018402005402a8a11108f0004d118e0138030106400881784a26a50118802511ea0016400c8419c033858112c211100248c670a0aa114030086108c0340068084402888111c4c685010200330002208c520c20104620804009800190882166000ce5604088210502802110266844508c225804b014c0188201840321c4e0a8a0c902300c61128e291ca84804402c20301a608841088e41000f025011a02011002480601a0065142328c6418ca33004209d00
  | 15 => 0x43080c022821110c200c69008024142208165228e03103308041718231000300d00108814000208847318201c0862816000c8151c6308060108011004c00a442180211006891e00892630043084451a02010402210600080478003090672a8e2580a80810909820104a6288c000c8498002002441b022104226956008c814344320500008203004c0144142c0018448208c100da47806300045298001100320841028813006a21115188024112800444220001102b00cc71082810403398641a00058406388c40adad60022238c000cebc00483804138a0310022009e10ac90314460006d0a020610830004158c834044c29847008011b84608165320005042268540020a01006221c47128045050b00861108a530403498603bc2940026000610182031c0200cc15a12118042009640dc0111422000c94bf623008208100
  | 16 => 0xb000401a0231a40248c4701806400020810120d211148f0994d38c2330123388c1008211004648107218a0184283a0402880136c082904010c21101b2010690a00258006011072092890462000c50c8241b4082804110886780022046720ce0410260984908ce2310a800d40008201810a4846d518011a4822004700ce2604280804019ba01904628c4e4080450022a0cc1008aa1100338444598a241543000600088135017099013ac8331428380654980411023704c90488111c82205740bca34140b2816010c0330442680641e4221004828144008273240328cc5020a031078800450dc01504e20096400c825012309847228211004628d010c82019e02385e920c201100300c44219261242308d40108a140012090c1108001802628c440182310042294c028ca110458880600a0021900800940088036144308161
  | 17 => 0x830005109801405e220c490300441c08480601088219c68080450880010023008c012c2031c0300464530a21b822201541880161c230990010c20110660806140da51000268650008291048a080451e823114032804018ce1300a22044001803590c60804100ce0b80e8009e00dc211006b3844d0a805184062086401803414237104018c003342600d057888030002224c5008a0304a2001440b0e01042c200441a002904080806750c25110260006420c2499063006401a8203445300104148a1558c200c40088a330022a804128c22100662890400c03180032890d02ca61900a2086011820104e2000445a00140032204441088011c3369c6108883984e2688c9109241010600d401982a1840c08141048a141c02700c1128001102a004410b02755043004c02892118043005800a000190066816710802500ea080c0
  | 18 => 0x2394446a0e14142621060108a1784020a107028803004a00c410080053828a18cd12c84184022004d230e11240b002e018ca243442084611980160066080612082211c22005e1131a619003080451cc01190222094002002554022110012801100c88010900802104eb88580088211141308064120a01042368c67198019801a22961108e15346601c4900c0050002204c00892810442003040b0e21900600850098024140b21040198e0158ca085050080059c2602909008201a48220500098205052628861128e4304322106000c8261026380450888b300032850702aa060002004741a001191020004191804604a30826418d2011c732890100ca418422284c0008241100309544198011109e0084010ca1304238904440802190c600061019ca101a32090025d2118003204470a823110060006e0888a7842209061
  | 19 => 0x620014719820124c320cc00ac013006328047160e319146a006138c8010408385e00a02110003804651a1201240329147088837a4622285600802610260090504800100027094100c261040a208650b0205048339c4108c8632448080601ac8119c2a0044141800300c200de10a9a01007301844098005848208860008a3324022810400c051105301d8120800790030098522c80140e200cc0098024102820041318e1500972044420c0110126280690882319c067064110ca018442381650a0014380600c41008834000221061109201802628c4d008021256a004c5220203100b08840128011950200064108024402808065188203460608505018241802320500088a61800220c4512022b842208040018e130003085600082710066482e50080013843711e71b028300ef00060118a11240c00cc0018019002321064
  | 20 => 0x4b704c0198a219088812e00988231412498c400ce11542a0044d0b08018443688c7008211b863384c42dc001c4862804128ce331c024806100a0011086009410882010003894c500824180422045112002404822146110c04524282984020c001008a38069088e4100ea004c102824594820044519801410330804118881340020904702e801902600c6101800101a22850000dc65800208060128011100620de0388893142268069188001103328c4500c80124a239140089a17841a200641bce1584c20805400ca4300024804e22c2119148487c4098205b8020094108d2141406004401a020654832172100881400032118400c201003248049218001c40b288c900c21100e64acc52a0041040c000411888a3000820064108231d0d22904108885180060114540c2660082001050a0024148220847008893002220505
  | 21 => 0x3084400a9a0190c600d41289c250062080c010c81510b248d90008031102820cc0008a01940382065698024102600c40020845540320441108813004608101609a0110a26850d0a1cf41043080ce22824114c2288c1020025140309c40198031102f0846100c20104cb28540028814004a08c6d11802104836814008c8130082a804002c035002a00d0400c201840238a400888910078020442a0201340c00c6109802780430804120b80100280254430c20190667150738c2118042484c009800138220146008c033240308040108221802a4844108a225800800d0102da0594e2480541182013486088400880150068480c400c004702a0846132007524262054118829300020bcc069800184030904408e2478422480c000c0319c860804d02c03100e821500188241140200040198a053488000410088351c2221100
  | 22 => 0x42200402a8a45040848cc109a2a434438044420a82414330004502c2018023004c1028849244300985198001042222e74020a241c8820187008231002c4816100c0b11028a89e028c87100030006413026404c32904108a21300ea0804100c0b78073280490a00210522288c90a8a8100660086e0a000410020884038c023542308565018e03003900d16399201a4220090108d2058486a0c400a0e4105c8480c002c815042a2806120882195280805523c0079012010c11b080184530146413e02410020004e088055046209de042c271806628561208051a40200cc030c2c1106a70187228205a50300cc0488e14002a484470080141c4aa004530d22180e628505123611004620c600bc0619002200c1018a331c0248441388e64102800564018223240221501308a0790e609464098041108c20c440180150488a8067
  | 23 => 0x832004012028134cb00c41128a131c2328061408e0100284804438c04105a32898702c847804a4846019805110020805008810794190804401a031588a006410a0803042200910009261846320100520205048f280c00adc19d02820465018001103700065088a01706f0190110c216004a00504198a09040268064009c560082080441ac204148608c4908c0830012005e10208f19042014441b023410c3208c0698e140042084403e9205802c38861008001902a388c012c271006648cc7130014140200cc000c84404024804418801334264810d788825004300541130a618006080450ce04138820084433ca1900030806760dc11102a00464008043246b0058018c207a4af09c60498221040222c40098a178402200650182250128288440200318062204c0230b01014200247120e01140200061098813002309161
  | 24 => 0x66000ce118a3110880954904886300028050000c8211046080714cc223444b014c0009241848b09d00198a0c948608049008057d4622196000c815006628c610882430466009001a0293104208460230a0438c32104110ce232402204c4198001806600909418041026238580020a4104a248c47230011852b281e1008823140309161188211108638d010088450442011090892118003008440980112426a01e012003600030844120c031154a0046e088e011003385892882034006080c5121a2104220104000804784420cc450082011c26a184400ce5500032050002d2411462000d6218e0514830144008881500230804d1a8201382c2846101a203102638cc502a24104a309c400980011403200600288430002880d100c00c3828380640882b124a300900209201240270d44098a2c943e0804700dc25046220104
  | 25 => 0x300540098021154802cc005c815700221100008801802608c4450920100232065002020184862146022a8f1140b2896108805314034818018c8111072001100082330022004c10a08433906888641b000114c62084e08ce26040a284600282540046283c100c001906238585208814106349445128a05848203541018823002b210412880011c660a510020221040820cc710d211046a004712a0001b82300070188015006349060188225802a00441088827c00200cc10092811c82080c00c8e2104022884712804400682810100c001104c384414180051023286404a020144820046d09a011848828c410080150423098c902c021006aa807d030055000268cc5008203140201c650a00013413000605a08251c222058442a0030048000410a125101022090930f60334020850712801194cb483c700ca23144881de1
  | 26 => 0x42208d6198045442200f0442001b806208040008e51902680ae13882011003005851a0814345a08167198214040221060309c1324436806110801100282824502ca25840628500029a7100020190412022110027106118c01314032018704c264384c0046500880304a302d4130c241010220845098011100608cc100c81300c2218c00282011c6a01844320079804b004c1128a03240320c4009800904030896408ac2500622a0c5198811804a29509048031102b209f61a82010403001601bc2051026388c4108e3504032846112a2019c68380613082510072009000a0283004a200470a824110e200c610080240402085e4288026004f0886150ce078042004c7088a01804239445118081842300c40020e133462204402e001414480050100820504c600981188211004b001006a8201380208c6704802300030a465
  | 27 => 0x73004c01a002110e3091710a8a23142308164188e31008c08584388007802c20907021c110083e24c0198a0104883816000ca45144a698c000e22314c84806408883124060050110c283044a01c510a0001b886288410a005985020984501820190462884104803300620050508ac0604620a2511a0001742601460108e36002c099ed118015902800c6100c201842c009801a1c1400a27004e128e11ecef003200988431c020804038802401660006148caa11c03215410088718403209642a0e0110260acc002dca31c424904022c0111c2a2856138803104a802d850c82731006380c01bd22104c220c64098a49000b6804900c0119037009840a080300a3384c702ec61144200cce219a0404833a0410888140003480655982011c2a08c64008a01845a2158122d261048a009640a0001100239067288859002220060
  | 28 => 0x300d001a8a018408210411080279422084c400c8019c4a0946900c2310026008c5109aa194020016421806410c32004000882324220844010a00180466806d3082279c63298c90a0241044f08447131a119146880c0008025700268641199211002f0847548c20500e2005400088e19003388640a022584260814400c033040208040029c1180d2011610080a110a23958518ca05804600040120221849300de0008037840309045228001102c3884438c82d1002204c0008a160059018c515c0412422014601a0a3340032004428ce219c2a28d4401a00b840b289811a82110082080c011805110830a047009a1614486810510c205382c00061318035000820d0000da6100e320c600e4a04040b08849099af500222016412c06180460904153027104420110518c8031002015400a1a0114c608071008823002a09060
  | 29 => 0x187044d0cc23104222146010804314230806418ce01144800041008223044300cc102080400a200045222051042220040048a1634630846904c0310052008640a00c10423005e12482912463000c44a8e01040220de001a21900226a86518e00101320010901802101a8214c0088261900a0006e09a801040200041088e17b4c809165109203008c01041088a018162211010a12013493004c4118001840b08c600a8e14040b205072880031cc6084652080099026a84d4009c14004201460098a0904060004700ce5794824a04002c87bb46a2805603c8418402204c010c2019042004401a021411883886460e825402b8986900a0134432014450092518023708cd02ca13000208c4723021c8422280c410ea250403b016140882110860024122c2511c02284c032ca43000300045119211102c021e42bc0131488098c1
  | 30 => 0x4300445128211a42300c690a881324632384100f801802f0816901800100ab205000082710002480c01a020154060a047188094244b28060109201b42a08c61019c5580a30094500e07580aa381400c82118482208610880433422280602e003110860044540ce0310cf20ccd009201000200d056a000184e2a806100a21500632044000c213144838c49088845042a00de7188891388200565098011100600c4102da140002084441988019c26000452302759c23b04d000c201900a2046d0bc014040268960008845142a4816018c2110026280440082218022a14c5020a07840b00d0519800514832004410c81400030804728885300660006108c233502300701220a11008338c4459822124020106001882984220a841118001002a3810d0180411c027111020c24180e27086e098a2524280014008c015146348061
  | 31 => 0xe2200c40c8a11040cb0c4008c01414024816400e0911466000614882a5400320cc1120201a402004441a00018403230410a282534222984038c011004609549088043000a684c00088911003019471a0005942b28041108ef3340b29d00428803102a8096101822110a3204c012c2860002080670cc04190c6701e1320034400808165218001005338d01021a2c804200de0008a01848a0b4651180150483280c001882b94572186738c061104600ae9088001a5020154018c211000300465298a2bb48208c44388a341c63210c110820500863884408c0410002285090292113442215000a022110cc4886138c01400232844418c803009200464019a21840328cc508d20180e22184d0bc01110020804100c8560442490600082311c28000412088032403208c152aa01000a7244019800d102200e670ada160022080c5
  | _ => 0

def qIdxOf (j : ℕ) : ℕ :=
  ((chunkWord ((j - 65) / W)) >>> (BITS * ((j - 65) % W))) % BASE

def nOf (j : ℕ) : ℕ := 4000000000000000000 + 2 * j

def qOf (j : ℕ) : ℕ := Qlist.getD (qIdxOf j) 0

def repOKB (j : ℕ) : Bool :=
  decide (65 ≤ j) && decide (j ≤ 16384) &&
    decide (qIdxOf j < Qlist.length) && decide (qOf j ≤ nOf j) &&
      decide (nOf j - qOf j < 66049) && isPrimeTiny (nOf j - qOf j)

lemma getD_mem_of_lt {l : List ℕ} {i : ℕ} {d : ℕ} (h : i < l.length) : l.getD i d ∈ l := by
  induction l generalizing i with
  | nil => simp at h
  | cons a t ih =>
      cases i with
      | zero => simp
      | succ i => exact List.mem_cons_of_mem a (ih (by simpa using h))

lemma repOKB_spec {j : ℕ} (h : repOKB j = true) :
    65 ≤ j ∧ j ≤ 16384 ∧ qIdxOf j < Qlist.length ∧ qOf j ≤ nOf j ∧
      nOf j - qOf j < 66049 ∧ isPrimeTiny (nOf j - qOf j) = true := by
  unfold repOKB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩


/-! ### 分块内核核验 -/

set_option maxRecDepth 10000 in
lemma chunkCheck_0 : (List.range W).all (fun i => repOKB (65 + 0 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_1 : (List.range W).all (fun i => repOKB (65 + 1 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_2 : (List.range W).all (fun i => repOKB (65 + 2 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_3 : (List.range W).all (fun i => repOKB (65 + 3 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_4 : (List.range W).all (fun i => repOKB (65 + 4 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_5 : (List.range W).all (fun i => repOKB (65 + 5 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_6 : (List.range W).all (fun i => repOKB (65 + 6 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_7 : (List.range W).all (fun i => repOKB (65 + 7 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_8 : (List.range W).all (fun i => repOKB (65 + 8 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_9 : (List.range W).all (fun i => repOKB (65 + 9 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_10 : (List.range W).all (fun i => repOKB (65 + 10 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_11 : (List.range W).all (fun i => repOKB (65 + 11 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_12 : (List.range W).all (fun i => repOKB (65 + 12 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_13 : (List.range W).all (fun i => repOKB (65 + 13 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_14 : (List.range W).all (fun i => repOKB (65 + 14 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_15 : (List.range W).all (fun i => repOKB (65 + 15 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_16 : (List.range W).all (fun i => repOKB (65 + 16 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_17 : (List.range W).all (fun i => repOKB (65 + 17 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_18 : (List.range W).all (fun i => repOKB (65 + 18 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_19 : (List.range W).all (fun i => repOKB (65 + 19 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_20 : (List.range W).all (fun i => repOKB (65 + 20 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_21 : (List.range W).all (fun i => repOKB (65 + 21 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_22 : (List.range W).all (fun i => repOKB (65 + 22 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_23 : (List.range W).all (fun i => repOKB (65 + 23 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_24 : (List.range W).all (fun i => repOKB (65 + 24 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_25 : (List.range W).all (fun i => repOKB (65 + 25 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_26 : (List.range W).all (fun i => repOKB (65 + 26 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_27 : (List.range W).all (fun i => repOKB (65 + 27 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_28 : (List.range W).all (fun i => repOKB (65 + 28 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_29 : (List.range W).all (fun i => repOKB (65 + 29 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_30 : (List.range W).all (fun i => repOKB (65 + 30 * 510 + i)) = true := by
  decide

set_option maxRecDepth 10000 in
lemma chunkCheck_31 : (List.range W).all (fun i => repOKB (65 + 31 * 510 + i)) = true := by
  decide

lemma chunkRepOK_0 : ∀ i : ℕ, i < 510 → repOKB (65 + 0 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_0 i (List.mem_range.mpr hi)

lemma chunkRepOK_1 : ∀ i : ℕ, i < 510 → repOKB (65 + 1 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_1 i (List.mem_range.mpr hi)

lemma chunkRepOK_2 : ∀ i : ℕ, i < 510 → repOKB (65 + 2 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_2 i (List.mem_range.mpr hi)

lemma chunkRepOK_3 : ∀ i : ℕ, i < 510 → repOKB (65 + 3 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_3 i (List.mem_range.mpr hi)

lemma chunkRepOK_4 : ∀ i : ℕ, i < 510 → repOKB (65 + 4 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_4 i (List.mem_range.mpr hi)

lemma chunkRepOK_5 : ∀ i : ℕ, i < 510 → repOKB (65 + 5 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_5 i (List.mem_range.mpr hi)

lemma chunkRepOK_6 : ∀ i : ℕ, i < 510 → repOKB (65 + 6 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_6 i (List.mem_range.mpr hi)

lemma chunkRepOK_7 : ∀ i : ℕ, i < 510 → repOKB (65 + 7 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_7 i (List.mem_range.mpr hi)

lemma chunkRepOK_8 : ∀ i : ℕ, i < 510 → repOKB (65 + 8 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_8 i (List.mem_range.mpr hi)

lemma chunkRepOK_9 : ∀ i : ℕ, i < 510 → repOKB (65 + 9 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_9 i (List.mem_range.mpr hi)

lemma chunkRepOK_10 : ∀ i : ℕ, i < 510 → repOKB (65 + 10 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_10 i (List.mem_range.mpr hi)

lemma chunkRepOK_11 : ∀ i : ℕ, i < 510 → repOKB (65 + 11 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_11 i (List.mem_range.mpr hi)

lemma chunkRepOK_12 : ∀ i : ℕ, i < 510 → repOKB (65 + 12 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_12 i (List.mem_range.mpr hi)

lemma chunkRepOK_13 : ∀ i : ℕ, i < 510 → repOKB (65 + 13 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_13 i (List.mem_range.mpr hi)

lemma chunkRepOK_14 : ∀ i : ℕ, i < 510 → repOKB (65 + 14 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_14 i (List.mem_range.mpr hi)

lemma chunkRepOK_15 : ∀ i : ℕ, i < 510 → repOKB (65 + 15 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_15 i (List.mem_range.mpr hi)

lemma chunkRepOK_16 : ∀ i : ℕ, i < 510 → repOKB (65 + 16 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_16 i (List.mem_range.mpr hi)

lemma chunkRepOK_17 : ∀ i : ℕ, i < 510 → repOKB (65 + 17 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_17 i (List.mem_range.mpr hi)

lemma chunkRepOK_18 : ∀ i : ℕ, i < 510 → repOKB (65 + 18 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_18 i (List.mem_range.mpr hi)

lemma chunkRepOK_19 : ∀ i : ℕ, i < 510 → repOKB (65 + 19 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_19 i (List.mem_range.mpr hi)

lemma chunkRepOK_20 : ∀ i : ℕ, i < 510 → repOKB (65 + 20 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_20 i (List.mem_range.mpr hi)

lemma chunkRepOK_21 : ∀ i : ℕ, i < 510 → repOKB (65 + 21 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_21 i (List.mem_range.mpr hi)

lemma chunkRepOK_22 : ∀ i : ℕ, i < 510 → repOKB (65 + 22 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_22 i (List.mem_range.mpr hi)

lemma chunkRepOK_23 : ∀ i : ℕ, i < 510 → repOKB (65 + 23 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_23 i (List.mem_range.mpr hi)

lemma chunkRepOK_24 : ∀ i : ℕ, i < 510 → repOKB (65 + 24 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_24 i (List.mem_range.mpr hi)

lemma chunkRepOK_25 : ∀ i : ℕ, i < 510 → repOKB (65 + 25 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_25 i (List.mem_range.mpr hi)

lemma chunkRepOK_26 : ∀ i : ℕ, i < 510 → repOKB (65 + 26 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_26 i (List.mem_range.mpr hi)

lemma chunkRepOK_27 : ∀ i : ℕ, i < 510 → repOKB (65 + 27 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_27 i (List.mem_range.mpr hi)

lemma chunkRepOK_28 : ∀ i : ℕ, i < 510 → repOKB (65 + 28 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_28 i (List.mem_range.mpr hi)

lemma chunkRepOK_29 : ∀ i : ℕ, i < 510 → repOKB (65 + 29 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_29 i (List.mem_range.mpr hi)

lemma chunkRepOK_30 : ∀ i : ℕ, i < 510 → repOKB (65 + 30 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_30 i (List.mem_range.mpr hi)

lemma chunkRepOK_31 : ∀ i : ℕ, i < 510 → repOKB (65 + 31 * 510 + i) = true := by
  intro i hi
  exact List.all_eq_true.mp chunkCheck_31 i (List.mem_range.mpr hi)

lemma chunkRange_0 : ∀ j : ℕ, 65 + 0 * 510 ≤ j → j < 65 + 1 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 0 * 510) < 510 := by omega
  have h := chunkRepOK_0 (j - (65 + 0 * 510)) hi
  have heq : 65 + 0 * 510 + (j - (65 + 0 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_1 : ∀ j : ℕ, 65 + 1 * 510 ≤ j → j < 65 + 2 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 1 * 510) < 510 := by omega
  have h := chunkRepOK_1 (j - (65 + 1 * 510)) hi
  have heq : 65 + 1 * 510 + (j - (65 + 1 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_2 : ∀ j : ℕ, 65 + 2 * 510 ≤ j → j < 65 + 3 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 2 * 510) < 510 := by omega
  have h := chunkRepOK_2 (j - (65 + 2 * 510)) hi
  have heq : 65 + 2 * 510 + (j - (65 + 2 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_3 : ∀ j : ℕ, 65 + 3 * 510 ≤ j → j < 65 + 4 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 3 * 510) < 510 := by omega
  have h := chunkRepOK_3 (j - (65 + 3 * 510)) hi
  have heq : 65 + 3 * 510 + (j - (65 + 3 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_4 : ∀ j : ℕ, 65 + 4 * 510 ≤ j → j < 65 + 5 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 4 * 510) < 510 := by omega
  have h := chunkRepOK_4 (j - (65 + 4 * 510)) hi
  have heq : 65 + 4 * 510 + (j - (65 + 4 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_5 : ∀ j : ℕ, 65 + 5 * 510 ≤ j → j < 65 + 6 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 5 * 510) < 510 := by omega
  have h := chunkRepOK_5 (j - (65 + 5 * 510)) hi
  have heq : 65 + 5 * 510 + (j - (65 + 5 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_6 : ∀ j : ℕ, 65 + 6 * 510 ≤ j → j < 65 + 7 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 6 * 510) < 510 := by omega
  have h := chunkRepOK_6 (j - (65 + 6 * 510)) hi
  have heq : 65 + 6 * 510 + (j - (65 + 6 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_7 : ∀ j : ℕ, 65 + 7 * 510 ≤ j → j < 65 + 8 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 7 * 510) < 510 := by omega
  have h := chunkRepOK_7 (j - (65 + 7 * 510)) hi
  have heq : 65 + 7 * 510 + (j - (65 + 7 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_8 : ∀ j : ℕ, 65 + 8 * 510 ≤ j → j < 65 + 9 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 8 * 510) < 510 := by omega
  have h := chunkRepOK_8 (j - (65 + 8 * 510)) hi
  have heq : 65 + 8 * 510 + (j - (65 + 8 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_9 : ∀ j : ℕ, 65 + 9 * 510 ≤ j → j < 65 + 10 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 9 * 510) < 510 := by omega
  have h := chunkRepOK_9 (j - (65 + 9 * 510)) hi
  have heq : 65 + 9 * 510 + (j - (65 + 9 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_10 : ∀ j : ℕ, 65 + 10 * 510 ≤ j → j < 65 + 11 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 10 * 510) < 510 := by omega
  have h := chunkRepOK_10 (j - (65 + 10 * 510)) hi
  have heq : 65 + 10 * 510 + (j - (65 + 10 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_11 : ∀ j : ℕ, 65 + 11 * 510 ≤ j → j < 65 + 12 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 11 * 510) < 510 := by omega
  have h := chunkRepOK_11 (j - (65 + 11 * 510)) hi
  have heq : 65 + 11 * 510 + (j - (65 + 11 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_12 : ∀ j : ℕ, 65 + 12 * 510 ≤ j → j < 65 + 13 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 12 * 510) < 510 := by omega
  have h := chunkRepOK_12 (j - (65 + 12 * 510)) hi
  have heq : 65 + 12 * 510 + (j - (65 + 12 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_13 : ∀ j : ℕ, 65 + 13 * 510 ≤ j → j < 65 + 14 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 13 * 510) < 510 := by omega
  have h := chunkRepOK_13 (j - (65 + 13 * 510)) hi
  have heq : 65 + 13 * 510 + (j - (65 + 13 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_14 : ∀ j : ℕ, 65 + 14 * 510 ≤ j → j < 65 + 15 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 14 * 510) < 510 := by omega
  have h := chunkRepOK_14 (j - (65 + 14 * 510)) hi
  have heq : 65 + 14 * 510 + (j - (65 + 14 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_15 : ∀ j : ℕ, 65 + 15 * 510 ≤ j → j < 65 + 16 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 15 * 510) < 510 := by omega
  have h := chunkRepOK_15 (j - (65 + 15 * 510)) hi
  have heq : 65 + 15 * 510 + (j - (65 + 15 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_16 : ∀ j : ℕ, 65 + 16 * 510 ≤ j → j < 65 + 17 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 16 * 510) < 510 := by omega
  have h := chunkRepOK_16 (j - (65 + 16 * 510)) hi
  have heq : 65 + 16 * 510 + (j - (65 + 16 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_17 : ∀ j : ℕ, 65 + 17 * 510 ≤ j → j < 65 + 18 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 17 * 510) < 510 := by omega
  have h := chunkRepOK_17 (j - (65 + 17 * 510)) hi
  have heq : 65 + 17 * 510 + (j - (65 + 17 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_18 : ∀ j : ℕ, 65 + 18 * 510 ≤ j → j < 65 + 19 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 18 * 510) < 510 := by omega
  have h := chunkRepOK_18 (j - (65 + 18 * 510)) hi
  have heq : 65 + 18 * 510 + (j - (65 + 18 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_19 : ∀ j : ℕ, 65 + 19 * 510 ≤ j → j < 65 + 20 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 19 * 510) < 510 := by omega
  have h := chunkRepOK_19 (j - (65 + 19 * 510)) hi
  have heq : 65 + 19 * 510 + (j - (65 + 19 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_20 : ∀ j : ℕ, 65 + 20 * 510 ≤ j → j < 65 + 21 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 20 * 510) < 510 := by omega
  have h := chunkRepOK_20 (j - (65 + 20 * 510)) hi
  have heq : 65 + 20 * 510 + (j - (65 + 20 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_21 : ∀ j : ℕ, 65 + 21 * 510 ≤ j → j < 65 + 22 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 21 * 510) < 510 := by omega
  have h := chunkRepOK_21 (j - (65 + 21 * 510)) hi
  have heq : 65 + 21 * 510 + (j - (65 + 21 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_22 : ∀ j : ℕ, 65 + 22 * 510 ≤ j → j < 65 + 23 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 22 * 510) < 510 := by omega
  have h := chunkRepOK_22 (j - (65 + 22 * 510)) hi
  have heq : 65 + 22 * 510 + (j - (65 + 22 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_23 : ∀ j : ℕ, 65 + 23 * 510 ≤ j → j < 65 + 24 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 23 * 510) < 510 := by omega
  have h := chunkRepOK_23 (j - (65 + 23 * 510)) hi
  have heq : 65 + 23 * 510 + (j - (65 + 23 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_24 : ∀ j : ℕ, 65 + 24 * 510 ≤ j → j < 65 + 25 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 24 * 510) < 510 := by omega
  have h := chunkRepOK_24 (j - (65 + 24 * 510)) hi
  have heq : 65 + 24 * 510 + (j - (65 + 24 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_25 : ∀ j : ℕ, 65 + 25 * 510 ≤ j → j < 65 + 26 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 25 * 510) < 510 := by omega
  have h := chunkRepOK_25 (j - (65 + 25 * 510)) hi
  have heq : 65 + 25 * 510 + (j - (65 + 25 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_26 : ∀ j : ℕ, 65 + 26 * 510 ≤ j → j < 65 + 27 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 26 * 510) < 510 := by omega
  have h := chunkRepOK_26 (j - (65 + 26 * 510)) hi
  have heq : 65 + 26 * 510 + (j - (65 + 26 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_27 : ∀ j : ℕ, 65 + 27 * 510 ≤ j → j < 65 + 28 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 27 * 510) < 510 := by omega
  have h := chunkRepOK_27 (j - (65 + 27 * 510)) hi
  have heq : 65 + 27 * 510 + (j - (65 + 27 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_28 : ∀ j : ℕ, 65 + 28 * 510 ≤ j → j < 65 + 29 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 28 * 510) < 510 := by omega
  have h := chunkRepOK_28 (j - (65 + 28 * 510)) hi
  have heq : 65 + 28 * 510 + (j - (65 + 28 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_29 : ∀ j : ℕ, 65 + 29 * 510 ≤ j → j < 65 + 30 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 29 * 510) < 510 := by omega
  have h := chunkRepOK_29 (j - (65 + 29 * 510)) hi
  have heq : 65 + 29 * 510 + (j - (65 + 29 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_30 : ∀ j : ℕ, 65 + 30 * 510 ≤ j → j < 65 + 31 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 30 * 510) < 510 := by omega
  have h := chunkRepOK_30 (j - (65 + 30 * 510)) hi
  have heq : 65 + 30 * 510 + (j - (65 + 30 * 510)) = j := by omega
  rwa [heq] at h

lemma chunkRange_31 : ∀ j : ℕ, 65 + 31 * 510 ≤ j → j < 65 + 32 * 510 → repOKB j = true := by
  intro j h1 h2
  have hi : j - (65 + 31 * 510) < 510 := by omega
  have h := chunkRepOK_31 (j - (65 + 31 * 510)) hi
  have heq : 65 + 31 * 510 + (j - (65 + 31 * 510)) = j := by omega
  rwa [heq] at h


/-! ### 二叉合并 -/

lemma mergeRange_0_2 : ∀ n : ℕ, 65 + 0 * 510 ≤ n → n < 65 + 2 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 1 * 510) with h | h
  · exact chunkRange_0 n hlo h
  · exact chunkRange_1 n (by omega) hhi


lemma mergeRange_2_4 : ∀ n : ℕ, 65 + 2 * 510 ≤ n → n < 65 + 4 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 3 * 510) with h | h
  · exact chunkRange_2 n hlo h
  · exact chunkRange_3 n (by omega) hhi


lemma mergeRange_0_4 : ∀ n : ℕ, 65 + 0 * 510 ≤ n → n < 65 + 4 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 2 * 510) with h | h
  · exact mergeRange_0_2 n hlo h
  · exact mergeRange_2_4 n (by omega) hhi


lemma mergeRange_4_6 : ∀ n : ℕ, 65 + 4 * 510 ≤ n → n < 65 + 6 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 5 * 510) with h | h
  · exact chunkRange_4 n hlo h
  · exact chunkRange_5 n (by omega) hhi


lemma mergeRange_6_8 : ∀ n : ℕ, 65 + 6 * 510 ≤ n → n < 65 + 8 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 7 * 510) with h | h
  · exact chunkRange_6 n hlo h
  · exact chunkRange_7 n (by omega) hhi


lemma mergeRange_4_8 : ∀ n : ℕ, 65 + 4 * 510 ≤ n → n < 65 + 8 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 6 * 510) with h | h
  · exact mergeRange_4_6 n hlo h
  · exact mergeRange_6_8 n (by omega) hhi


lemma mergeRange_0_8 : ∀ n : ℕ, 65 + 0 * 510 ≤ n → n < 65 + 8 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 4 * 510) with h | h
  · exact mergeRange_0_4 n hlo h
  · exact mergeRange_4_8 n (by omega) hhi


lemma mergeRange_8_10 : ∀ n : ℕ, 65 + 8 * 510 ≤ n → n < 65 + 10 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 9 * 510) with h | h
  · exact chunkRange_8 n hlo h
  · exact chunkRange_9 n (by omega) hhi


lemma mergeRange_10_12 : ∀ n : ℕ, 65 + 10 * 510 ≤ n → n < 65 + 12 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 11 * 510) with h | h
  · exact chunkRange_10 n hlo h
  · exact chunkRange_11 n (by omega) hhi


lemma mergeRange_8_12 : ∀ n : ℕ, 65 + 8 * 510 ≤ n → n < 65 + 12 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 10 * 510) with h | h
  · exact mergeRange_8_10 n hlo h
  · exact mergeRange_10_12 n (by omega) hhi


lemma mergeRange_12_14 : ∀ n : ℕ, 65 + 12 * 510 ≤ n → n < 65 + 14 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 13 * 510) with h | h
  · exact chunkRange_12 n hlo h
  · exact chunkRange_13 n (by omega) hhi


lemma mergeRange_14_16 : ∀ n : ℕ, 65 + 14 * 510 ≤ n → n < 65 + 16 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 15 * 510) with h | h
  · exact chunkRange_14 n hlo h
  · exact chunkRange_15 n (by omega) hhi


lemma mergeRange_12_16 : ∀ n : ℕ, 65 + 12 * 510 ≤ n → n < 65 + 16 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 14 * 510) with h | h
  · exact mergeRange_12_14 n hlo h
  · exact mergeRange_14_16 n (by omega) hhi


lemma mergeRange_8_16 : ∀ n : ℕ, 65 + 8 * 510 ≤ n → n < 65 + 16 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 12 * 510) with h | h
  · exact mergeRange_8_12 n hlo h
  · exact mergeRange_12_16 n (by omega) hhi


lemma mergeRange_0_16 : ∀ n : ℕ, 65 + 0 * 510 ≤ n → n < 65 + 16 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 8 * 510) with h | h
  · exact mergeRange_0_8 n hlo h
  · exact mergeRange_8_16 n (by omega) hhi


lemma mergeRange_16_18 : ∀ n : ℕ, 65 + 16 * 510 ≤ n → n < 65 + 18 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 17 * 510) with h | h
  · exact chunkRange_16 n hlo h
  · exact chunkRange_17 n (by omega) hhi


lemma mergeRange_18_20 : ∀ n : ℕ, 65 + 18 * 510 ≤ n → n < 65 + 20 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 19 * 510) with h | h
  · exact chunkRange_18 n hlo h
  · exact chunkRange_19 n (by omega) hhi


lemma mergeRange_16_20 : ∀ n : ℕ, 65 + 16 * 510 ≤ n → n < 65 + 20 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 18 * 510) with h | h
  · exact mergeRange_16_18 n hlo h
  · exact mergeRange_18_20 n (by omega) hhi


lemma mergeRange_20_22 : ∀ n : ℕ, 65 + 20 * 510 ≤ n → n < 65 + 22 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 21 * 510) with h | h
  · exact chunkRange_20 n hlo h
  · exact chunkRange_21 n (by omega) hhi


lemma mergeRange_22_24 : ∀ n : ℕ, 65 + 22 * 510 ≤ n → n < 65 + 24 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 23 * 510) with h | h
  · exact chunkRange_22 n hlo h
  · exact chunkRange_23 n (by omega) hhi


lemma mergeRange_20_24 : ∀ n : ℕ, 65 + 20 * 510 ≤ n → n < 65 + 24 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 22 * 510) with h | h
  · exact mergeRange_20_22 n hlo h
  · exact mergeRange_22_24 n (by omega) hhi


lemma mergeRange_16_24 : ∀ n : ℕ, 65 + 16 * 510 ≤ n → n < 65 + 24 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 20 * 510) with h | h
  · exact mergeRange_16_20 n hlo h
  · exact mergeRange_20_24 n (by omega) hhi


lemma mergeRange_24_26 : ∀ n : ℕ, 65 + 24 * 510 ≤ n → n < 65 + 26 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 25 * 510) with h | h
  · exact chunkRange_24 n hlo h
  · exact chunkRange_25 n (by omega) hhi


lemma mergeRange_26_28 : ∀ n : ℕ, 65 + 26 * 510 ≤ n → n < 65 + 28 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 27 * 510) with h | h
  · exact chunkRange_26 n hlo h
  · exact chunkRange_27 n (by omega) hhi


lemma mergeRange_24_28 : ∀ n : ℕ, 65 + 24 * 510 ≤ n → n < 65 + 28 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 26 * 510) with h | h
  · exact mergeRange_24_26 n hlo h
  · exact mergeRange_26_28 n (by omega) hhi


lemma mergeRange_28_30 : ∀ n : ℕ, 65 + 28 * 510 ≤ n → n < 65 + 30 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 29 * 510) with h | h
  · exact chunkRange_28 n hlo h
  · exact chunkRange_29 n (by omega) hhi


lemma mergeRange_30_32 : ∀ n : ℕ, 65 + 30 * 510 ≤ n → n < 65 + 32 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 31 * 510) with h | h
  · exact chunkRange_30 n hlo h
  · exact chunkRange_31 n (by omega) hhi


lemma mergeRange_28_32 : ∀ n : ℕ, 65 + 28 * 510 ≤ n → n < 65 + 32 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 30 * 510) with h | h
  · exact mergeRange_28_30 n hlo h
  · exact mergeRange_30_32 n (by omega) hhi


lemma mergeRange_24_32 : ∀ n : ℕ, 65 + 24 * 510 ≤ n → n < 65 + 32 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 28 * 510) with h | h
  · exact mergeRange_24_28 n hlo h
  · exact mergeRange_28_32 n (by omega) hhi


lemma mergeRange_16_32 : ∀ n : ℕ, 65 + 16 * 510 ≤ n → n < 65 + 32 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 24 * 510) with h | h
  · exact mergeRange_16_24 n hlo h
  · exact mergeRange_24_32 n (by omega) hhi


lemma mergeRange_0_32 : ∀ n : ℕ, 65 + 0 * 510 ≤ n → n < 65 + 32 * 510 → repOKB n = true := by
  intro n hlo hhi
  rcases lt_or_ge n (65 + 16 * 510) with h | h
  · exact mergeRange_0_16 n hlo h
  · exact mergeRange_16_32 n (by omega) hhi


lemma repOKB_all : ∀ j : ℕ, 65 ≤ j → j ≤ 16384 → repOKB j = true := by
  intro j h1 h2
  exact mergeRange_0_32 j h1 (by omega)

/-! ### 主定理 -/

theorem Conjectures.Goldbach.FinitePostBoundaryThrough32768 :
    ∀ j : ℕ, 65 ≤ j → j ≤ 16384 → let n : ℕ := 4000000000000000000 + 2*j; ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n := by
  intro j hj65 hj16
  have hrep : repOKB j = true := repOKB_all j hj65 hj16
  obtain ⟨h65, h16, hqi, hle, hbound, hpi⟩ := repOKB_spec hrep
  have hqmem : qOf j ∈ Qlist := by
    exact getD_mem_of_lt (i := qIdxOf j) hqi
  have hqprime : Nat.Prime (qOf j) := Qlist_prime (qOf j) hqmem
  have hpprime : Nat.Prime (nOf j - qOf j) := isPrimeTiny_spec hbound hpi
  refine ⟨nOf j - qOf j, qOf j, hpprime, hqprime, ?_⟩
  have hsum : (nOf j - qOf j) + qOf j = nOf j := by omega
  simpa only [nOf] using hsum
