import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

/-! Lucas certificates for the 64 even integers immediately above 4 · 10^18.
Each list factors p - 1 completely. Its modular-power checks certify that
the indicated base has order p - 1 in ZMod p. -/

namespace PostBoundaryCertificates

private def Checks (p a : ℕ) : List ℕ → Prop
  | [] => True
  | r :: rs =>
    Nat.Prime r ∧ Nat.powMod a ((p - 1) / r) p ≠ 1 % p ∧ Checks p a rs

private theorem factorCheck {p a q : ℕ} (hq : q.Prime) (fs : List ℕ)
    (checks : Checks p a fs) (dvd : q ∣ fs.prod) :
    Nat.powMod a ((p - 1) / q) p ≠ 1 % p := by
  induction fs with
  | nil =>
    have h : q ∣ 1 := dvd
    exact (hq.ne_one (Nat.dvd_one.mp h)).elim
  | cons r rs ih =>
    obtain ⟨hr, checked, rest⟩ := checks
    simp only [List.prod_cons] at dvd
    rcases hq.dvd_mul.mp dvd with h | h
    · have eq : q = r := (Nat.prime_dvd_prime_iff_eq hq hr).mp h
      subst q
      exact checked
    · exact ih rest h

private theorem powEqOne (p a e : ℕ) :
    ((a : ZMod p) ^ e = 1) ↔ Nat.powMod a e p = 1 % p := by
  rw [Nat.powMod_def, ← Nat.cast_pow]
  simpa only [Nat.cast_one] using ZMod.natCast_eq_natCast_iff' (a ^ e) 1 p

private theorem lucasCertificate (p a : ℕ) (fs : List ℕ)
    (complete : fs.prod = p - 1) (checks : Checks p a fs)
    (fermat : Nat.powMod a (p - 1) p = 1 % p) : Nat.Prime p := by
  apply lucas_primality p (a : ZMod p)
  · exact (powEqOne p a (p - 1)).mpr fermat
  · intro q hq hd
    rw [← complete] at hd
    exact fun e => factorCheck hq fs checks hd ((powEqOne p a _).mp e)

private theorem prime_2 : Nat.Prime 2 := by
  norm_num

private theorem prime_3 : Nat.Prime 3 := by
  norm_num

private theorem prime_5 : Nat.Prime 5 := by
  norm_num

private theorem prime_7 : Nat.Prime 7 := by
  norm_num

private theorem prime_11 : Nat.Prime 11 := by
  norm_num

private theorem prime_13 : Nat.Prime 13 := by
  norm_num

private theorem prime_17 : Nat.Prime 17 := by
  norm_num

private theorem prime_19 : Nat.Prime 19 := by
  norm_num

private theorem prime_23 : Nat.Prime 23 := by
  norm_num

private theorem prime_29 : Nat.Prime 29 := by
  norm_num

private theorem prime_31 : Nat.Prime 31 := by
  norm_num

private theorem prime_37 : Nat.Prime 37 := by
  norm_num

private theorem prime_41 : Nat.Prime 41 := by
  norm_num

private theorem prime_43 : Nat.Prime 43 := by
  norm_num

private theorem prime_47 : Nat.Prime 47 := by
  norm_num

private theorem prime_53 : Nat.Prime 53 := by
  norm_num

private theorem prime_59 : Nat.Prime 59 := by
  norm_num

private theorem prime_61 : Nat.Prime 61 := by
  norm_num

private theorem prime_67 : Nat.Prime 67 := by
  norm_num

private theorem prime_71 : Nat.Prime 71 := by
  norm_num

private theorem prime_73 : Nat.Prime 73 := by
  norm_num

private theorem prime_97 : Nat.Prime 97 := by
  norm_num

private theorem prime_127 : Nat.Prime 127 := by
  norm_num

private theorem prime_131 : Nat.Prime 131 := by
  norm_num

private theorem prime_137 : Nat.Prime 137 := by
  norm_num

private theorem prime_139 : Nat.Prime 139 := by
  norm_num

private theorem prime_149 : Nat.Prime 149 := by
  norm_num

private theorem prime_151 : Nat.Prime 151 := by
  norm_num

private theorem prime_157 : Nat.Prime 157 := by
  norm_num

private theorem prime_163 : Nat.Prime 163 := by
  norm_num

private theorem prime_167 : Nat.Prime 167 := by
  norm_num

private theorem prime_181 : Nat.Prime 181 := by
  norm_num

private theorem prime_211 : Nat.Prime 211 := by
  norm_num

private theorem prime_227 : Nat.Prime 227 := by
  norm_num

private theorem prime_229 : Nat.Prime 229 := by
  norm_num

private theorem prime_239 : Nat.Prime 239 := by
  norm_num

private theorem prime_241 : Nat.Prime 241 := by
  norm_num

private theorem prime_251 : Nat.Prime 251 := by
  norm_num

private theorem prime_269 : Nat.Prime 269 := by
  norm_num

private theorem prime_283 : Nat.Prime 283 := by
  norm_num

private theorem prime_313 : Nat.Prime 313 := by
  norm_num

private theorem prime_317 : Nat.Prime 317 := by
  norm_num

private theorem prime_331 : Nat.Prime 331 := by
  norm_num

private theorem prime_337 : Nat.Prime 337 := by
  norm_num

private theorem prime_367 : Nat.Prime 367 := by
  norm_num

private theorem prime_379 : Nat.Prime 379 := by
  norm_num

private theorem prime_389 : Nat.Prime 389 := by
  norm_num

private theorem prime_401 : Nat.Prime 401 := by
  norm_num

private theorem prime_439 : Nat.Prime 439 := by
  norm_num

private theorem prime_487 : Nat.Prime 487 := by
  norm_num

private theorem prime_491 : Nat.Prime 491 := by
  norm_num

private theorem prime_499 : Nat.Prime 499 := by
  norm_num

private theorem prime_509 : Nat.Prime 509 := by
  norm_num

private theorem prime_547 : Nat.Prime 547 := by
  norm_num

private theorem prime_769 : Nat.Prime 769 := by
  norm_num

private theorem prime_883 : Nat.Prime 883 := by
  norm_num

private theorem prime_1213 : Nat.Prime 1213 := by
  norm_num

private theorem prime_1283 : Nat.Prime 1283 := by
  norm_num

private theorem prime_1301 : Nat.Prime 1301 := by
  norm_num

private theorem prime_1307 : Nat.Prime 1307 := by
  norm_num

private theorem prime_1579 : Nat.Prime 1579 := by
  norm_num

private theorem prime_1871 : Nat.Prime 1871 := by
  norm_num

private theorem prime_2087 : Nat.Prime 2087 := by
  norm_num

private theorem prime_2719 : Nat.Prime 2719 := by
  norm_num

private theorem prime_3583 : Nat.Prime 3583 := by
  norm_num

private theorem prime_4093 : Nat.Prime 4093 := by
  norm_num

private theorem prime_6421 : Nat.Prime 6421 := by
  norm_num

private theorem prime_7577 : Nat.Prime 7577 := by
  norm_num

private theorem prime_8147 : Nat.Prime 8147 := by
  norm_num

private theorem prime_8429 : Nat.Prime 8429 := by
  norm_num

private theorem prime_14407 : Nat.Prime 14407 := by
  norm_num

private theorem prime_18913 : Nat.Prime 18913 := by
  norm_num

private theorem prime_20681 : Nat.Prime 20681 := by
  norm_num

private theorem prime_25657 : Nat.Prime 25657 := by
  norm_num

private theorem prime_26209 : Nat.Prime 26209 := by
  norm_num

private theorem prime_32779 : Nat.Prime 32779 := by
  norm_num

private theorem prime_40763 : Nat.Prime 40763 := by
  norm_num

private theorem prime_65701 : Nat.Prime 65701 := by
  norm_num

set_option maxRecDepth 4000 in
private theorem prime_115471 : Nat.Prime 115471 := by
  refine lucasCertificate 115471 6 [2, 3, 3, 5, 1283] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_5, by decide, ?_⟩
  refine ⟨prime_1283, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_166667 : Nat.Prime 166667 := by
  refine lucasCertificate 166667 2 [2, 167, 499] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_167, by decide, ?_⟩
  refine ⟨prime_499, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_174017 : Nat.Prime 174017 := by
  refine lucasCertificate 174017 3 [2, 2, 2, 2, 2, 2, 2719] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2719, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_192631 : Nat.Prime 192631 := by
  refine lucasCertificate 192631 3 [2, 3, 5, 6421] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_5, by decide, ?_⟩
  refine ⟨prime_6421, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_239851 : Nat.Prime 239851 := by
  refine lucasCertificate 239851 3 [2, 3, 3, 5, 5, 13, 41] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_5, by decide, ?_⟩
  refine ⟨prime_5, by decide, ?_⟩
  refine ⟨prime_13, by decide, ?_⟩
  refine ⟨prime_41, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_265157 : Nat.Prime 265157 := by
  refine lucasCertificate 265157 2 [2, 2, 151, 439] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_151, by decide, ?_⟩
  refine ⟨prime_439, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_1077697 : Nat.Prime 1077697 := by
  refine lucasCertificate 1077697 5 [2, 2, 2, 2, 2, 2, 3, 3, 1871] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_1871, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_1786469 : Nat.Prime 1786469 := by
  refine lucasCertificate 1786469 2 [2, 2, 31, 14407] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_31, by decide, ?_⟩
  refine ⟨prime_14407, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_3572939 : Nat.Prime 3572939 := by
  refine lucasCertificate 3572939 2 [2, 1786469] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_1786469, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_4318891 : Nat.Prime 4318891 := by
  refine lucasCertificate 4318891 2 [2, 3, 5, 19, 7577] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_5, by decide, ?_⟩
  refine ⟨prime_19, by decide, ?_⟩
  refine ⟨prime_7577, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_4623217 : Nat.Prime 4623217 := by
  refine lucasCertificate 4623217 23 [2, 2, 2, 2, 3, 13, 31, 239] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_13, by decide, ?_⟩
  refine ⟨prime_31, by decide, ?_⟩
  refine ⟨prime_239, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_5220511 : Nat.Prime 5220511 := by
  refine lucasCertificate 5220511 6 [2, 3, 5, 174017] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_5, by decide, ?_⟩
  refine ⟨prime_174017, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_5548607 : Nat.Prime 5548607 := by
  refine lucasCertificate 5548607 5 [2, 7, 251, 1579] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_7, by decide, ?_⟩
  refine ⟨prime_251, by decide, ?_⟩
  refine ⟨prime_1579, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_6363769 : Nat.Prime 6363769 := by
  refine lucasCertificate 6363769 7 [2, 2, 2, 3, 265157] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_265157, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_8541289 : Nat.Prime 8541289 := by
  refine lucasCertificate 8541289 43 [2, 2, 2, 3, 3, 3, 3, 7, 7, 269] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_7, by decide, ?_⟩
  refine ⟨prime_7, by decide, ?_⟩
  refine ⟨prime_269, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_15924371 : Nat.Prime 15924371 := by
  refine lucasCertificate 15924371 2 [2, 5, 7, 11, 20681] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_5, by decide, ?_⟩
  refine ⟨prime_7, by decide, ?_⟩
  refine ⟨prime_11, by decide, ?_⟩
  refine ⟨prime_20681, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_42393521 : Nat.Prime 42393521 := by
  refine lucasCertificate 42393521 3 [2, 2, 2, 2, 5, 13, 40763] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_5, by decide, ?_⟩
  refine ⟨prime_13, by decide, ?_⟩
  refine ⟨prime_40763, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_149855393 : Nat.Prime 149855393 := by
  refine lucasCertificate 149855393 3 [2, 2, 2, 2, 2, 1307, 3583] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_1307, by decide, ?_⟩
  refine ⟨prime_3583, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_244138709 : Nat.Prime 244138709 := by
  refine lucasCertificate 244138709 2 [2, 2, 11, 5548607] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_11, by decide, ?_⟩
  refine ⟨prime_5548607, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_299710787 : Nat.Prime 299710787 := by
  refine lucasCertificate 299710787 2 [2, 149855393] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_149855393, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_594085421 : Nat.Prime 594085421 := by
  refine lucasCertificate 594085421 3 [2, 2, 5, 43, 331, 2087] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_5, by decide, ?_⟩
  refine ⟨prime_43, by decide, ?_⟩
  refine ⟨prime_331, by decide, ?_⟩
  refine ⟨prime_2087, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_777448979 : Nat.Prime 777448979 := by
  refine lucasCertificate 777448979 2 [2, 73, 1301, 4093] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_73, by decide, ?_⟩
  refine ⟨prime_1301, by decide, ?_⟩
  refine ⟨prime_4093, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_2712263549 : Nat.Prime 2712263549 := by
  refine lucasCertificate 2712263549 2 [2, 2, 157, 4318891] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_157, by decide, ?_⟩
  refine ⟨prime_4318891, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_2929664509 : Nat.Prime 2929664509 := by
  refine lucasCertificate 2929664509 6 [2, 2, 3, 244138709] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_244138709, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_13994081623 : Nat.Prime 13994081623 := by
  refine lucasCertificate 13994081623 3 [2, 3, 3, 777448979] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_777448979, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_103100510729 : Nat.Prime 103100510729 := by
  refine lucasCertificate 103100510729 3 [2, 2, 2, 43, 299710787] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_43, by decide, ?_⟩
  refine ⟨prime_299710787, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_37379684141669 : Nat.Prime 37379684141669 := by
  refine lucasCertificate 37379684141669 2 [2, 2, 11, 389, 18913, 115471] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_11, by decide, ?_⟩
  refine ⟨prime_389, by decide, ?_⟩
  refine ⟨prime_18913, by decide, ?_⟩
  refine ⟨prime_115471, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_566251415628539 : Nat.Prime 566251415628539 := by
  refine lucasCertificate 566251415628539 2 [2, 241, 401, 2929664509] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_241, by decide, ?_⟩
  refine ⟨prime_401, by decide, ?_⟩
  refine ⟨prime_2929664509, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_100000000000000003 : Nat.Prime 100000000000000003 := by
  refine lucasCertificate 100000000000000003 2 [2, 3, 7, 61, 65701, 594085421] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_7, by decide, ?_⟩
  refine ⟨prime_61, by decide, ?_⟩
  refine ⟨prime_65701, by decide, ?_⟩
  refine ⟨prime_594085421, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_181818181818181813 : Nat.Prime 181818181818181813 := by
  refine lucasCertificate 181818181818181813 5 [2, 2, 3, 29, 192631, 2712263549] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_29, by decide, ?_⟩
  refine ⟨prime_192631, by decide, ?_⟩
  refine ⟨prime_2712263549, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_399999999999999979 : Nat.Prime 399999999999999979 := by
  refine lucasCertificate 399999999999999979 2 [2, 3, 3, 3, 23, 211, 239851, 6363769] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_23, by decide, ?_⟩
  refine ⟨prime_211, by decide, ?_⟩
  refine ⟨prime_239851, by decide, ?_⟩
  refine ⟨prime_6363769, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_1000000000000000009 : Nat.Prime 1000000000000000009 := by
  refine lucasCertificate 1000000000000000009 7 [2, 2, 2, 3, 3, 97, 26209, 32779, 166667] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_97, by decide, ?_⟩
  refine ⟨prime_26209, by decide, ?_⟩
  refine ⟨prime_32779, by decide, ?_⟩
  refine ⟨prime_166667, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_3999999999999998803 : Nat.Prime 3999999999999998803 := by
  refine lucasCertificate 3999999999999998803 2 [2, 3, 229, 8147, 8429, 42393521] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_229, by decide, ?_⟩
  refine ⟨prime_8147, by decide, ?_⟩
  refine ⟨prime_8429, by decide, ?_⟩
  refine ⟨prime_42393521, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_3999999999999999349 : Nat.Prime 3999999999999999349 := by
  refine lucasCertificate 3999999999999999349 6 [2, 2, 3, 3, 3, 3, 3, 3, 31, 61, 283, 491, 5220511] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_31, by decide, ?_⟩
  refine ⟨prime_61, by decide, ?_⟩
  refine ⟨prime_283, by decide, ?_⟩
  refine ⟨prime_491, by decide, ?_⟩
  refine ⟨prime_5220511, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_3999999999999999497 : Nat.Prime 3999999999999999497 := by
  refine lucasCertificate 3999999999999999497 3 [2, 2, 2, 883, 566251415628539] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_883, by decide, ?_⟩
  refine ⟨prime_566251415628539, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_3999999999999999691 : Nat.Prime 3999999999999999691 := by
  refine lucasCertificate 3999999999999999691 3 [2, 3, 3, 5, 29, 41, 37379684141669] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_5, by decide, ?_⟩
  refine ⟨prime_29, by decide, ?_⟩
  refine ⟨prime_41, by decide, ?_⟩
  refine ⟨prime_37379684141669, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_3999999999999999761 : Nat.Prime 3999999999999999761 := by
  refine lucasCertificate 3999999999999999761 7 [2, 2, 2, 2, 5, 3572939, 13994081623] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_5, by decide, ?_⟩
  refine ⟨prime_3572939, by decide, ?_⟩
  refine ⟨prime_13994081623, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_3999999999999999791 : Nat.Prime 3999999999999999791 := by
  refine lucasCertificate 3999999999999999791 11 [2, 5, 399999999999999979] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_5, by decide, ?_⟩
  refine ⟨prime_399999999999999979, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_3999999999999999883 : Nat.Prime 3999999999999999883 := by
  refine lucasCertificate 3999999999999999883 2 [2, 3, 19, 157, 547, 25657, 15924371] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_19, by decide, ?_⟩
  refine ⟨prime_157, by decide, ?_⟩
  refine ⟨prime_547, by decide, ?_⟩
  refine ⟨prime_25657, by decide, ?_⟩
  refine ⟨prime_15924371, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_3999999999999999887 : Nat.Prime 3999999999999999887 := by
  refine lucasCertificate 3999999999999999887 5 [2, 11, 181818181818181813] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_11, by decide, ?_⟩
  refine ⟨prime_181818181818181813, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_4000000000000000037 : Nat.Prime 4000000000000000037 := by
  refine lucasCertificate 4000000000000000037 2 [2, 2, 1000000000000000009] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_1000000000000000009, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_4000000000000000049 : Nat.Prime 4000000000000000049 := by
  refine lucasCertificate 4000000000000000049 3 [2, 2, 2, 2, 13, 487, 4623217, 8541289] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_13, by decide, ?_⟩
  refine ⟨prime_487, by decide, ?_⟩
  refine ⟨prime_4623217, by decide, ?_⟩
  refine ⟨prime_8541289, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_4000000000000000069 : Nat.Prime 4000000000000000069 := by
  refine lucasCertificate 4000000000000000069 6 [2, 2, 3, 3, 1077697, 103100510729] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_3, by decide, ?_⟩
  refine ⟨prime_1077697, by decide, ?_⟩
  refine ⟨prime_103100510729, by decide, ?_⟩
  trivial

set_option maxRecDepth 4000 in
private theorem prime_4000000000000000121 : Nat.Prime 4000000000000000121 := by
  refine lucasCertificate 4000000000000000121 3 [2, 2, 2, 5, 100000000000000003] (by decide) ?_ (by decide)
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_2, by decide, ?_⟩
  refine ⟨prime_5, by decide, ?_⟩
  refine ⟨prime_100000000000000003, by decide, ?_⟩
  trivial

end PostBoundaryCertificates

open PostBoundaryCertificates

theorem PEqualNP.Outside.L_goldbach_finite_post_boundary_prime_block :
    ∀ j : ℕ, 1 ≤ j → j ≤ 64 → let n : ℕ := 4000000000000000000 + 2*j; ∃ p ∈ ({3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,67,71,127,131,137,139,149,151,163,181,211,227,239,251,313,317,337,367,379,509,769,1213} : Finset ℕ), Nat.Prime p ∧ p < n ∧ Nat.Prime (n-p) := by
  intro j hlo hhi
  interval_cases j
  · exact ⟨211, by decide, prime_211, by decide, prime_3999999999999999791⟩
  · exact ⟨313, by decide, prime_313, by decide, prime_3999999999999999691⟩
  · exact ⟨509, by decide, prime_509, by decide, prime_3999999999999999497⟩
  · exact ⟨317, by decide, prime_317, by decide, prime_3999999999999999691⟩
  · exact ⟨127, by decide, prime_127, by decide, prime_3999999999999999883⟩
  · exact ⟨251, by decide, prime_251, by decide, prime_3999999999999999761⟩
  · exact ⟨131, by decide, prime_131, by decide, prime_3999999999999999883⟩
  · exact ⟨1213, by decide, prime_1213, by decide, prime_3999999999999998803⟩
  · exact ⟨131, by decide, prime_131, by decide, prime_3999999999999999887⟩
  · exact ⟨137, by decide, prime_137, by decide, prime_3999999999999999883⟩
  · exact ⟨139, by decide, prime_139, by decide, prime_3999999999999999883⟩
  · exact ⟨137, by decide, prime_137, by decide, prime_3999999999999999887⟩
  · exact ⟨139, by decide, prime_139, by decide, prime_3999999999999999887⟩
  · exact ⟨337, by decide, prime_337, by decide, prime_3999999999999999691⟩
  · exact ⟨239, by decide, prime_239, by decide, prime_3999999999999999791⟩
  · exact ⟨149, by decide, prime_149, by decide, prime_3999999999999999883⟩
  · exact ⟨151, by decide, prime_151, by decide, prime_3999999999999999883⟩
  · exact ⟨149, by decide, prime_149, by decide, prime_3999999999999999887⟩
  · exact ⟨151, by decide, prime_151, by decide, prime_3999999999999999887⟩
  · exact ⟨3, by decide, prime_3, by decide, prime_4000000000000000037⟩
  · exact ⟨5, by decide, prime_5, by decide, prime_4000000000000000037⟩
  · exact ⟨7, by decide, prime_7, by decide, prime_4000000000000000037⟩
  · exact ⟨163, by decide, prime_163, by decide, prime_3999999999999999883⟩
  · exact ⟨11, by decide, prime_11, by decide, prime_4000000000000000037⟩
  · exact ⟨13, by decide, prime_13, by decide, prime_4000000000000000037⟩
  · exact ⟨3, by decide, prime_3, by decide, prime_4000000000000000049⟩
  · exact ⟨17, by decide, prime_17, by decide, prime_4000000000000000037⟩
  · exact ⟨19, by decide, prime_19, by decide, prime_4000000000000000037⟩
  · exact ⟨367, by decide, prime_367, by decide, prime_3999999999999999691⟩
  · exact ⟨23, by decide, prime_23, by decide, prime_4000000000000000037⟩
  · exact ⟨13, by decide, prime_13, by decide, prime_4000000000000000049⟩
  · exact ⟨181, by decide, prime_181, by decide, prime_3999999999999999883⟩
  · exact ⟨29, by decide, prime_29, by decide, prime_4000000000000000037⟩
  · exact ⟨31, by decide, prime_31, by decide, prime_4000000000000000037⟩
  · exact ⟨379, by decide, prime_379, by decide, prime_3999999999999999691⟩
  · exact ⟨3, by decide, prime_3, by decide, prime_4000000000000000069⟩
  · exact ⟨37, by decide, prime_37, by decide, prime_4000000000000000037⟩
  · exact ⟨7, by decide, prime_7, by decide, prime_4000000000000000069⟩
  · exact ⟨41, by decide, prime_41, by decide, prime_4000000000000000037⟩
  · exact ⟨43, by decide, prime_43, by decide, prime_4000000000000000037⟩
  · exact ⟨13, by decide, prime_13, by decide, prime_4000000000000000069⟩
  · exact ⟨47, by decide, prime_47, by decide, prime_4000000000000000037⟩
  · exact ⟨17, by decide, prime_17, by decide, prime_4000000000000000069⟩
  · exact ⟨19, by decide, prime_19, by decide, prime_4000000000000000069⟩
  · exact ⟨53, by decide, prime_53, by decide, prime_4000000000000000037⟩
  · exact ⟨23, by decide, prime_23, by decide, prime_4000000000000000069⟩
  · exact ⟨211, by decide, prime_211, by decide, prime_3999999999999999883⟩
  · exact ⟨59, by decide, prime_59, by decide, prime_4000000000000000037⟩
  · exact ⟨29, by decide, prime_29, by decide, prime_4000000000000000069⟩
  · exact ⟨31, by decide, prime_31, by decide, prime_4000000000000000069⟩
  · exact ⟨53, by decide, prime_53, by decide, prime_4000000000000000049⟩
  · exact ⟨67, by decide, prime_67, by decide, prime_4000000000000000037⟩
  · exact ⟨37, by decide, prime_37, by decide, prime_4000000000000000069⟩
  · exact ⟨71, by decide, prime_71, by decide, prime_4000000000000000037⟩
  · exact ⟨41, by decide, prime_41, by decide, prime_4000000000000000069⟩
  · exact ⟨43, by decide, prime_43, by decide, prime_4000000000000000069⟩
  · exact ⟨227, by decide, prime_227, by decide, prime_3999999999999999887⟩
  · exact ⟨47, by decide, prime_47, by decide, prime_4000000000000000069⟩
  · exact ⟨769, by decide, prime_769, by decide, prime_3999999999999999349⟩
  · exact ⟨71, by decide, prime_71, by decide, prime_4000000000000000049⟩
  · exact ⟨53, by decide, prime_53, by decide, prime_4000000000000000069⟩
  · exact ⟨3, by decide, prime_3, by decide, prime_4000000000000000121⟩
  · exact ⟨239, by decide, prime_239, by decide, prime_3999999999999999887⟩
  · exact ⟨59, by decide, prime_59, by decide, prime_4000000000000000069⟩
