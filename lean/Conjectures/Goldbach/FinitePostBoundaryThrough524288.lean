import Mathlib

/-!
Finite interval F02 in the fourth Goldbach task proposal. The original 57 offsets
and the bit sieve proofs below are adapted from Anders Hafreager, PR 3706,
commit 25cc1158ef5f053ed8e0a0ca1a4f69820fbd6c4b, Apache License 2.0.
Source: https://github.com/andeplane/goldbach-proofs/blob/25cc1158ef5f053ed8e0a0ca1a4f69820fbd6c4b/research/reference-proofs/FinitePostBoundaryThrough262144.lean
Changes by 26day: certify all 68 anchors with Mathlib Lucas witnesses, extend
the small-factor sieve through 877, and check the new half-open target interval.
The 11 repair offsets and their order are from F02 in the official proposal.
-/
namespace PostBoundary524288.Anchors

private theorem cert1051 : Nat.Prime 1051 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7] }])

private theorem cert1063 : Nat.Prime 1063 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 59] }])

private theorem cert1117 : Nat.Prime 1117 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 31] }])

private theorem cert1129 : Nat.Prime 1129 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 47] }])

private theorem cert1163 : Nat.Prime 1163 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 83] }])

private theorem cert1201 : Nat.Prime 1201 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5] }])

private theorem cert1217 : Nat.Prime 1217 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 19] }])

private theorem cert1279 : Nat.Prime 1279 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 71] }])

private theorem cert1289 : Nat.Prime 1289 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 7, 23] }])

private theorem cert1327 : Nat.Prime 1327 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 17] }])

private theorem cert1367 : Nat.Prime 1367 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 683] }])

private theorem cert1427 : Nat.Prime 1427 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 23, 31] }])

private theorem cert1429 : Nat.Prime 1429 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 17] }])

private theorem cert1447 : Nat.Prime 1447 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 241] }])

private theorem cert1459 : Nat.Prime 1459 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3] }])

private theorem cert1559 : Nat.Prime 1559 := by
  primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 19, 41] }])

private theorem cert1567 : Nat.Prime 1567 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 29] }])

private theorem cert1579 : Nat.Prime 1579 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 263] }])

private theorem cert1583 : Nat.Prime 1583 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 113] }])

private theorem cert1601 : Nat.Prime 1601 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5] }])

private theorem cert1607 : Nat.Prime 1607 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 73] }])

private theorem cert1621 : Nat.Prime 1621 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5] }])

private theorem cert1667 : Nat.Prime 1667 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 17] }])

private theorem cert1699 : Nat.Prime 1699 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 283] }])

private theorem cert1723 : Nat.Prime 1723 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 41] }])

private theorem cert1753 : Nat.Prime 1753 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 73] }])

private theorem cert1777 : Nat.Prime 1777 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 37] }])

private theorem cert1811 : Nat.Prime 1811 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 181] }])

private theorem cert1877 : Nat.Prime 1877 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 67] }])

private theorem cert1901 : Nat.Prime 1901 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 19] }])

private theorem cert1907 : Nat.Prime 1907 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 953] }])

private theorem cert2027 : Nat.Prime 2027 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 1013] }])

private theorem cert2069 : Nat.Prime 2069 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 47] }])

private theorem cert2111 : Nat.Prime 2111 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 211] }])

private theorem cert2137 : Nat.Prime 2137 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 89] }])

private theorem cert2141 : Nat.Prime 2141 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 107] }])

private theorem cert2153 : Nat.Prime 2153 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 269] }])

private theorem cert2213 : Nat.Prime 2213 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 79] }])

private theorem cert2221 : Nat.Prime 2221 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37] }])

private theorem cert2237 : Nat.Prime 2237 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 43] }])

private theorem cert2243 : Nat.Prime 2243 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 59] }])

private theorem cert2273 : Nat.Prime 2273 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 71] }])

private theorem cert2293 : Nat.Prime 2293 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 191] }])

private theorem cert2399 : Nat.Prime 2399 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 11, 109] }])

private theorem cert2411 : Nat.Prime 2411 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 241] }])

private theorem cert2467 : Nat.Prime 2467 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 137] }])

private theorem cert2503 : Nat.Prime 2503 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 139] }])

private theorem cert2557 : Nat.Prime 2557 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 71] }])

private theorem cert2579 : Nat.Prime 2579 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 1289] }]) [cert1289]

private theorem cert2671 : Nat.Prime 2671 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 89] }])

private theorem cert2687 : Nat.Prime 2687 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 17, 79] }])

private theorem cert2693 : Nat.Prime 2693 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 673] }])

private theorem cert2707 : Nat.Prime 2707 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 41] }])

private theorem cert2711 : Nat.Prime 2711 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 271] }])

private theorem cert2749 : Nat.Prime 2749 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 229] }])

private theorem cert2953 : Nat.Prime 2953 := by
  primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 41] }])

private theorem cert3019 : Nat.Prime 3019 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 503] }])

private theorem cert3037 : Nat.Prime 3037 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 23] }])

private theorem cert3119 : Nat.Prime 3119 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 1559] }]) [cert1559]

private theorem cert3181 : Nat.Prime 3181 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 53] }])

private theorem cert3301 : Nat.Prime 3301 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11] }])

private theorem cert3389 : Nat.Prime 3389 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 11] }])

private theorem cert3407 : Nat.Prime 3407 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 131] }])

private theorem cert3449 : Nat.Prime 3449 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 431] }])

private theorem cert3697 : Nat.Prime 3697 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 11] }])

private theorem cert3761 : Nat.Prime 3761 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 47] }])

private theorem cert3803 : Nat.Prime 3803 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 1901] }]) [cert1901]

private theorem cert3943 : Nat.Prime 3943 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 73] }])

private theorem cert4021 : Nat.Prime 4021 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 67] }])

private theorem cert4049 : Nat.Prime 4049 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 23] }])

private theorem cert4091 : Nat.Prime 4091 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 409] }])

private theorem cert4139 : Nat.Prime 4139 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 2069] }]) [cert2069]

private theorem cert4159 : Nat.Prime 4159 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 11] }])

private theorem cert4241 : Nat.Prime 4241 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 53] }])

private theorem cert4283 : Nat.Prime 4283 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 2141] }]) [cert2141]

private theorem cert4357 : Nat.Prime 4357 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11] }])

private theorem cert4363 : Nat.Prime 4363 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 727] }])

private theorem cert4549 : Nat.Prime 4549 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 379] }])

private theorem cert4799 : Nat.Prime 4799 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 2399] }]) [cert2399]

private theorem cert4861 : Nat.Prime 4861 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5] }])

private theorem cert4999 : Nat.Prime 4999 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 17] }])

private theorem cert5101 : Nat.Prime 5101 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 17] }])

private theorem cert5119 : Nat.Prime 5119 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 853] }])

private theorem cert5153 : Nat.Prime 5153 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 23] }])

private theorem cert5231 : Nat.Prime 5231 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 523] }])

private theorem cert5309 : Nat.Prime 5309 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 1327] }]) [cert1327]

private theorem cert5333 : Nat.Prime 5333 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 31, 43] }])

private theorem cert5393 : Nat.Prime 5393 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 337] }])

private theorem cert5519 : Nat.Prime 5519 := by
  primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 31, 89] }])

private theorem cert5531 : Nat.Prime 5531 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 7, 79] }])

private theorem cert5801 : Nat.Prime 5801 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 29] }])

private theorem cert5849 : Nat.Prime 5849 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 17, 43] }])

private theorem cert5869 : Nat.Prime 5869 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 163] }])

private theorem cert5897 : Nat.Prime 5897 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 67] }])

private theorem cert5981 : Nat.Prime 5981 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 13, 23] }])

private theorem cert6101 : Nat.Prime 6101 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 61] }])

private theorem cert6317 : Nat.Prime 6317 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 1579] }]) [cert1579]

private theorem cert6421 : Nat.Prime 6421 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 107] }])

private theorem cert6563 : Nat.Prime 6563 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 17, 193] }])

private theorem cert6581 : Nat.Prime 6581 := by
  primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 5, 7, 47] }])

private theorem cert6779 : Nat.Prime 6779 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3389] }]) [cert3389]

private theorem cert6899 : Nat.Prime 6899 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3449] }]) [cert3449]

private theorem cert7121 : Nat.Prime 7121 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 89] }])

private theorem cert7219 : Nat.Prime 7219 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 401] }])

private theorem cert7499 : Nat.Prime 7499 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 23, 163] }])

private theorem cert7523 : Nat.Prime 7523 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3761] }]) [cert3761]

private theorem cert7793 : Nat.Prime 7793 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 487] }])

private theorem cert8111 : Nat.Prime 8111 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 811] }])

private theorem cert8377 : Nat.Prime 8377 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 349] }])

private theorem cert8447 : Nat.Prime 8447 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 41, 103] }])

private theorem cert8501 : Nat.Prime 8501 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 17] }])

private theorem cert8537 : Nat.Prime 8537 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 97] }])

private theorem cert8581 : Nat.Prime 8581 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 13] }])

private theorem cert8597 : Nat.Prime 8597 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 307] }])

private theorem cert8627 : Nat.Prime 8627 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 227] }])

private theorem cert9011 : Nat.Prime 9011 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 17, 53] }])

private theorem cert9173 : Nat.Prime 9173 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 2293] }]) [cert2293]

private theorem cert9281 : Nat.Prime 9281 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 29] }])

private theorem cert9479 : Nat.Prime 9479 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 677] }])

private theorem cert9613 : Nat.Prime 9613 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 89] }])

private theorem cert9811 : Nat.Prime 9811 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 109] }])

private theorem cert10529 : Nat.Prime 10529 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 47] }])

private theorem cert11399 : Nat.Prime 11399 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 41, 139] }])

private theorem cert11941 : Nat.Prime 11941 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 199] }])

private theorem cert11981 : Nat.Prime 11981 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 599] }])

private theorem cert12109 : Nat.Prime 12109 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 1009] }])

private theorem cert12149 : Nat.Prime 12149 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3037] }]) [cert3037]

private theorem cert12203 : Nat.Prime 12203 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 6101] }]) [cert6101]

private theorem cert12211 : Nat.Prime 12211 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 37] }])

private theorem cert12401 : Nat.Prime 12401 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 31] }])

private theorem cert12613 : Nat.Prime 12613 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1051] }]) [cert1051]

private theorem cert12757 : Nat.Prime 12757 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1063] }]) [cert1063]

private theorem cert13127 : Nat.Prime 13127 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 6563] }]) [cert6563]

private theorem cert13327 : Nat.Prime 13327 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 2221] }]) [cert2221]

private theorem cert13421 : Nat.Prime 13421 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 11, 61] }])

private theorem cert13451 : Nat.Prime 13451 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 269] }])

private theorem cert13757 : Nat.Prime 13757 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 181] }])

private theorem cert13789 : Nat.Prime 13789 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 383] }])

private theorem cert13873 : Nat.Prime 13873 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17] }])

private theorem cert13913 : Nat.Prime 13913 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 37, 47] }])

private theorem cert14243 : Nat.Prime 14243 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7121] }]) [cert7121]

private theorem cert14461 : Nat.Prime 14461 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 241] }])

private theorem cert15329 : Nat.Prime 15329 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 479] }])

private theorem cert15773 : Nat.Prime 15773 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3943] }]) [cert3943]

private theorem cert16141 : Nat.Prime 16141 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 269] }])

private theorem cert16217 : Nat.Prime 16217 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 2027] }]) [cert2027]

private theorem cert16381 : Nat.Prime 16381 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13] }])

private theorem cert17443 : Nat.Prime 17443 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 19] }])

private theorem cert17783 : Nat.Prime 17783 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 17, 523] }])

private theorem cert17921 : Nat.Prime 17921 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7] }])

private theorem cert18803 : Nat.Prime 18803 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 17, 79] }])

private theorem cert20693 : Nat.Prime 20693 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 739] }])

private theorem cert21379 : Nat.Prime 21379 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 509] }])

private theorem cert22367 : Nat.Prime 22367 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 53, 211] }])

private theorem cert22861 : Nat.Prime 22861 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 127] }])

private theorem cert23203 : Nat.Prime 23203 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1289] }]) [cert1289]

private theorem cert23209 : Nat.Prime 23209 := by
  primality (cert := .witnesses [.lucas { root := 31, primeFactors := [2, 3, 967] }])

private theorem cert23687 : Nat.Prime 23687 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 911] }])

private theorem cert23773 : Nat.Prime 23773 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 283] }])

private theorem cert24671 : Nat.Prime 24671 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 2467] }]) [cert2467]

private theorem cert25057 : Nat.Prime 25057 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 29] }])

private theorem cert25073 : Nat.Prime 25073 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 1567] }]) [cert1567]

private theorem cert26501 : Nat.Prime 26501 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 53] }])

private theorem cert28097 : Nat.Prime 28097 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 439] }])

private theorem cert29131 : Nat.Prime 29131 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 971] }])

private theorem cert31247 : Nat.Prime 31247 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 17, 919] }])

private theorem cert32191 : Nat.Prime 32191 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 29, 37] }])

private theorem cert38453 : Nat.Prime 38453 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 9613] }]) [cert9613]

private theorem cert42737 : Nat.Prime 42737 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 2671] }]) [cert2671]

private theorem cert45139 : Nat.Prime 45139 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7523] }]) [cert7523]

private theorem cert59393 : Nat.Prime 59393 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 29] }])

private theorem cert65707 : Nat.Prime 65707 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 47, 233] }])

private theorem cert68777 : Nat.Prime 68777 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 8597] }]) [cert8597]

private theorem cert69067 : Nat.Prime 69067 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1279] }]) [cert1279]

private theorem cert71483 : Nat.Prime 71483 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 103, 347] }])

private theorem cert71647 : Nat.Prime 71647 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11941] }]) [cert11941]

private theorem cert77153 : Nat.Prime 77153 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 2411] }]) [cert2411]

private theorem cert77479 : Nat.Prime 77479 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 37, 349] }])

private theorem cert78427 : Nat.Prime 78427 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 4357] }]) [cert4357]

private theorem cert79151 : Nat.Prime 79151 := by
  primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 1583] }]) [cert1583]

private theorem cert106699 : Nat.Prime 106699 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17783] }]) [cert17783]

private theorem cert110419 : Nat.Prime 110419 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 11, 239] }])

private theorem cert147253 : Nat.Prime 147253 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 1753] }]) [cert1753]

private theorem cert147881 : Nat.Prime 147881 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 3697] }]) [cert3697]

private theorem cert154339 : Nat.Prime 154339 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 29, 887] }])

private theorem cert158303 : Nat.Prime 158303 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 79151] }]) [cert79151]

private theorem cert162011 : Nat.Prime 162011 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 17, 953] }])

private theorem cert169483 : Nat.Prime 169483 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 47, 601] }])

private theorem cert170503 : Nat.Prime 170503 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 157, 181] }])

private theorem cert170843 : Nat.Prime 170843 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 12203] }]) [cert12203]

private theorem cert183461 : Nat.Prime 183461 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 9173] }]) [cert9173]

private theorem cert220447 : Nat.Prime 220447 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 37, 331] }])

private theorem cert274333 : Nat.Prime 274333 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 22861] }]) [cert22861]

private theorem cert286589 : Nat.Prime 286589 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 71647] }]) [cert71647]

private theorem cert290837 : Nat.Prime 290837 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 13, 17, 47] }])

private theorem cert300877 : Nat.Prime 300877 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 25073] }]) [cert25073]

private theorem cert323201 : Nat.Prime 323201 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 101] }])

private theorem cert341687 : Nat.Prime 341687 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 170843] }]) [cert170843]

private theorem cert402583 : Nat.Prime 402583 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 229, 293] }])

private theorem cert402767 : Nat.Prime 402767 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 13, 2213] }]) [cert2213]

private theorem cert412663 : Nat.Prime 412663 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 68777] }]) [cert68777]

private theorem cert444109 : Nat.Prime 444109 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 17, 311] }])

private theorem cert489367 : Nat.Prime 489367 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 31, 877] }])

private theorem cert560561 : Nat.Prime 560561 := by
  primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 7, 11, 13] }])

private theorem cert573179 : Nat.Prime 573179 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 286589] }]) [cert286589]

private theorem cert678971 : Nat.Prime 678971 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 43, 1579] }]) [cert1579]

private theorem cert774791 : Nat.Prime 774791 := by
  primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 5, 77479] }]) [cert77479]

private theorem cert844279 : Nat.Prime 844279 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 223, 631] }])

private theorem cert938257 : Nat.Prime 938257 := by
  primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 11, 1777] }]) [cert1777]

private theorem cert941617 : Nat.Prime 941617 := by
  primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 13, 503] }])

private theorem cert1038043 : Nat.Prime 1038043 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 47, 409] }])

private theorem cert1067687 : Nat.Prime 1067687 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 19, 28097] }]) [cert28097]

private theorem cert1080143 : Nat.Prime 1080143 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 77153] }]) [cert77153]

private theorem cert1162529 : Nat.Prime 1162529 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 17, 2137] }]) [cert2137]

private theorem cert1277011 : Nat.Prime 1277011 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 2027] }]) [cert2027]

private theorem cert1453429 : Nat.Prime 1453429 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 47, 859] }])

private theorem cert1552207 : Nat.Prime 1552207 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 61, 4241] }]) [cert4241]

private theorem cert1603319 : Nat.Prime 1603319 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 151, 5309] }]) [cert5309]

private theorem cert1627573 : Nat.Prime 1627573 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 23, 5897] }]) [cert5897]

private theorem cert1713353 : Nat.Prime 1713353 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 79, 2711] }]) [cert2711]

private theorem cert1740197 : Nat.Prime 1740197 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 439, 991] }])

private theorem cert1740301 : Nat.Prime 1740301 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 5801] }]) [cert5801]

private theorem cert1805561 : Nat.Prime 1805561 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 45139] }]) [cert45139]

private theorem cert1853497 : Nat.Prime 1853497 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 8581] }]) [cert8581]

private theorem cert1957469 : Nat.Prime 1957469 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 489367] }]) [cert489367]

private theorem cert2146093 : Nat.Prime 2146093 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 13757] }]) [cert13757]

private theorem cert2607557 : Nat.Prime 2607557 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 23, 4049] }]) [cert4049]

private theorem cert2824109 : Nat.Prime 2824109 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 17, 349] }])

private theorem cert2906161 : Nat.Prime 2906161 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 12109] }]) [cert12109]

private theorem cert3034189 : Nat.Prime 3034189 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 89, 947] }])

private theorem cert3304607 : Nat.Prime 3304607 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 131, 12613] }]) [cert12613]

private theorem cert3704137 : Nat.Prime 3704137 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 154339] }]) [cert154339]

private theorem cert3862921 : Nat.Prime 3862921 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 32191] }]) [cert32191]

private theorem cert3889261 : Nat.Prime 3889261 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 31, 41] }])

private theorem cert4696873 : Nat.Prime 4696873 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 31, 59, 107] }])

private theorem cert4750103 : Nat.Prime 4750103 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 47, 7219] }]) [cert7219]

private theorem cert4776451 : Nat.Prime 4776451 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 4549] }]) [cert4549]

private theorem cert4934387 : Nat.Prime 4934387 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 8537] }]) [cert8537]

private theorem cert5624461 : Nat.Prime 5624461 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 31247] }]) [cert31247]

private theorem cert39503953 : Nat.Prime 39503953 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 274333] }]) [cert274333]

private theorem cert103715837 : Nat.Prime 103715837 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 3704137] }]) [cert3704137]

private theorem cert142148393 : Nat.Prime 142148393 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 31, 573179] }]) [cert573179]

private theorem cert724223803 : Nat.Prime 724223803 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 43, 73, 38453] }]) [cert38453]

private theorem cert1185118591 : Nat.Prime 1185118591 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 39503953] }]) [cert39503953]

private theorem cert4722309947 : Nat.Prime 4722309947 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 29, 67, 71483] }]) [cert71483]

private theorem cert23801780297 : Nat.Prime 23801780297 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 163, 2607557] }]) [cert2607557]

private theorem cert43301425379 : Nat.Prime 43301425379 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 37, 53, 379, 29131] }]) [cert29131]

private theorem cert425023695071 : Nat.Prime 425023695071 := by
  primality (cert := .witnesses [.lucas { root := 34, primeFactors := [2, 5, 13, 23, 142148393] }]) [cert142148393]

private theorem cert1348664956559 : Nat.Prime 1348664956559 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 569, 1185118591] }]) [cert1185118591]

private theorem cert2697329913119 : Nat.Prime 2697329913119 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 1348664956559] }]) [cert1348664956559]

private theorem cert47746371275783 : Nat.Prime 47746371275783 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 17, 59, 23801780297] }]) [cert23801780297]

private theorem cert77663870767319 : Nat.Prime 77663870767319 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 11, 101, 337, 103715837] }]) [cert103715837]

private theorem cert148533234311177 : Nat.Prime 148533234311177 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 13, 17, 8111, 941617] }]) [cert8111, cert941617]

private theorem cert618429189857761 : Nat.Prime 618429189857761 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 593, 724223803] }]) [cert724223803]

private theorem cert11111111111111101 : Nat.Prime 11111111111111101 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 31, 37, 41, 271, 2906161] }]) [cert2906161]

private theorem cert17857142857142843 : Nat.Prime 17857142857142843 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 17, 47746371275783] }]) [cert47746371275783]

private theorem cert45454545454545397 : Nat.Prime 45454545454545397 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 13, 2243, 43301425379] }]) [cert2243, cert43301425379]

private theorem cert111111111111111011 : Nat.Prime 111111111111111011 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11111111111111101] }]) [cert11111111111111101]

private theorem cert117647058823529329 : Nat.Prime 117647058823529329 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 61, 5393, 15329, 162011] }]) [cert5393, cert15329, cert162011]

private theorem cert333333333333333149 : Nat.Prime 333333333333333149 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 29, 37, 77663870767319] }]) [cert77663870767319]

private theorem cert3999999999999754229 : Nat.Prime 3999999999999754229 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 193, 1129, 2237, 13873, 147881] }]) [cert1129, cert2237, cert13873, cert147881]

private theorem cert3999999999999766759 : Nat.Prime 3999999999999766759 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 163, 173, 199, 233, 293, 1740197] }]) [cert1740197]

private theorem cert3999999999999774781 : Nat.Prime 3999999999999774781 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 359, 2273, 5519, 4934387] }]) [cert2273, cert5519, cert4934387]

private theorem cert3999999999999776299 : Nat.Prime 3999999999999776299 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 43, 67, 167, 523, 6581, 402583] }]) [cert6581, cert402583]

private theorem cert3999999999999785681 : Nat.Prime 3999999999999785681 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 1289, 2707, 13421, 1067687] }]) [cert1289, cert2707, cert13421, cert1067687]

private theorem cert3999999999999787547 : Nat.Prime 3999999999999787547 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 79, 89, 1429, 3761, 1080143] }]) [cert1429, cert3761, cert1080143]

private theorem cert3999999999999795509 : Nat.Prime 3999999999999795509 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 487, 857, 1063, 4021, 560561] }]) [cert1063, cert4021, cert560561]

private theorem cert3999999999999796301 : Nat.Prime 3999999999999796301 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 1811, 4363, 11399, 444109] }]) [cert1811, cert4363, cert11399, cert444109]

private theorem cert3999999999999802837 : Nat.Prime 3999999999999802837 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 281, 617, 1163, 7499, 220447] }]) [cert1163, cert7499, cert220447]

private theorem cert3999999999999808897 : Nat.Prime 3999999999999808897 := by
  primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 7, 13, 137, 1447, 3407, 169483] }]) [cert1447, cert3407, cert169483]

private theorem cert3999999999999811921 : Nat.Prime 3999999999999811921 := by
  primality (cert := .witnesses [.lucas { root := 31, primeFactors := [2, 3, 5, 7, 17, 2687, 15773, 3304607] }]) [cert2687, cert15773, cert3304607]

private theorem cert3999999999999817217 : Nat.Prime 3999999999999817217 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 19, 37, 5981, 3862921] }]) [cert5981, cert3862921]

private theorem cert3999999999999819619 : Nat.Prime 3999999999999819619 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 11, 41, 101, 997, 12149, 402767] }]) [cert12149, cert402767]

private theorem cert3999999999999824263 : Nat.Prime 3999999999999824263 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 17, 149, 587, 20693, 42737] }]) [cert20693, cert42737]

private theorem cert3999999999999826099 : Nat.Prime 3999999999999826099 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 53, 79, 12401, 4750103] }]) [cert12401, cert4750103]

private theorem cert3999999999999845357 : Nat.Prime 3999999999999845357 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 43, 751, 2503, 3181, 3889261] }]) [cert2503, cert3181, cert3889261]

private theorem cert3999999999999854033 : Nat.Prime 3999999999999854033 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 13, 631, 2557, 9281, 183461] }]) [cert2557, cert9281, cert183461]

private theorem cert3999999999999856129 : Nat.Prime 3999999999999856129 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 19, 31, 83, 139, 14461, 26501] }]) [cert14461, cert26501]

private theorem cert3999999999999861707 : Nat.Prime 3999999999999861707 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 317, 401, 2749, 6779, 844279] }]) [cert2749, cert6779, cert844279]

private theorem cert3999999999999862267 : Nat.Prime 3999999999999862267 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 31, 859, 4799, 16141, 323201] }]) [cert4799, cert16141, cert323201]

private theorem cert3999999999999864779 : Nat.Prime 3999999999999864779 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 431, 593, 1217, 5531, 1162529] }]) [cert1217, cert5531, cert1162529]

private theorem cert3999999999999867337 : Nat.Prime 3999999999999867337 := by
  primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 11, 71, 79, 97, 11981, 774791] }]) [cert11981, cert774791]

private theorem cert3999999999999869249 : Nat.Prime 3999999999999869249 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 29, 89, 1601, 8377, 1805561] }]) [cert1601, cert8377, cert1805561]

private theorem cert3999999999999886037 : Nat.Prime 3999999999999886037 := by
  primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 7, 11, 37, 773, 21379, 3034189] }]) [cert21379, cert3034189]

private theorem cert3999999999999886871 : Nat.Prime 3999999999999886871 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 13, 19, 89, 257, 1201, 4139, 14243] }]) [cert1201, cert4139, cert14243]

private theorem cert3999999999999890101 : Nat.Prime 3999999999999890101 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 19, 73, 193, 23209, 2146093] }]) [cert23209, cert2146093]

private theorem cert3999999999999903583 : Nat.Prime 3999999999999903583 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 181, 1667, 2111, 9479, 110419] }]) [cert1667, cert2111, cert9479, cert110419]

private theorem cert3999999999999909553 : Nat.Prime 3999999999999909553 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 787, 2953, 24671, 1453429] }]) [cert2953, cert24671, cert1453429]

private theorem cert3999999999999911377 : Nat.Prime 3999999999999911377 := by
  primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 7, 41, 151, 8447, 9811, 23203] }]) [cert8447, cert9811, cert23203]

private theorem cert3999999999999916613 : Nat.Prime 3999999999999916613 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 23, 97, 1559, 12757, 65707] }]) [cert1559, cert12757, cert65707]

private theorem cert3999999999999919169 : Nat.Prime 3999999999999919169 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 11, 241, 827, 16381, 1740301] }]) [cert16381, cert1740301]

private theorem cert3999999999999921727 : Nat.Prime 3999999999999921727 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 313, 433, 5119, 13913, 69067] }]) [cert5119, cert13913, cert69067]

private theorem cert3999999999999922901 : Nat.Prime 3999999999999922901 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 149, 1201, 3119, 5869, 12211] }]) [cert1201, cert3119, cert5869, cert12211]

private theorem cert3999999999999927317 : Nat.Prime 3999999999999927317 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 67, 113, 1607, 5153, 938257] }]) [cert1607, cert5153, cert938257]

private theorem cert3999999999999930151 : Nat.Prime 3999999999999930151 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 211, 3301, 4283, 1277011] }]) [cert3301, cert4283, cert1277011]

private theorem cert3999999999999931391 : Nat.Prime 3999999999999931391 := by
  primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 5, 1907, 5849, 22367, 1603319] }]) [cert1907, cert5849, cert22367, cert1603319]

private theorem cert3999999999999932417 : Nat.Prime 3999999999999932417 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 17, 53, 773, 1723, 1627573] }]) [cert1723, cert1627573]

private theorem cert3999999999999934001 : Nat.Prime 3999999999999934001 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 23, 31, 47, 3019, 2824109] }]) [cert3019, cert2824109]

private theorem cert3999999999999940249 : Nat.Prime 3999999999999940249 := by
  primality (cert := .witnesses [.lucas { root := 21, primeFactors := [2, 3, 13, 971, 1117, 6899, 1713353] }]) [cert1117, cert6899, cert1713353]

private theorem cert3999999999999940667 : Nat.Prime 3999999999999940667 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 61, 109, 193, 1621, 9011, 106699] }]) [cert1621, cert9011, cert106699]

private theorem cert3999999999999942929 : Nat.Prime 3999999999999942929 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 11, 31, 449, 1427, 3803, 300877] }]) [cert1427, cert3803, cert300877]

private theorem cert3999999999999946703 : Nat.Prime 3999999999999946703 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 5231, 23687, 23773, 678971] }]) [cert5231, cert23687, cert23773, cert678971]

private theorem cert3999999999999957143 : Nat.Prime 3999999999999957143 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 163, 457, 691, 13451, 412663] }]) [cert13451, cert412663]

private theorem cert3999999999999960353 : Nat.Prime 3999999999999960353 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 193, 401, 1699, 3449, 25057] }]) [cert1699, cert3449, cert25057]

private theorem cert3999999999999963901 : Nat.Prime 3999999999999963901 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 23, 127, 839, 1877, 170503] }]) [cert1877, cert170503]

private theorem cert3999999999999975379 : Nat.Prime 3999999999999975379 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 727, 4159, 5333, 341687] }]) [cert4159, cert5333, cert341687]

private theorem cert3999999999999978353 : Nat.Prime 3999999999999978353 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 1367, 16217, 4696873] }]) [cert1367, cert16217, cert4696873]

private theorem cert3999999999999981883 : Nat.Prime 3999999999999981883 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 2557, 6421, 8501, 4776451] }]) [cert2557, cert6421, cert8501, cert4776451]

private theorem cert3999999999999984923 : Nat.Prime 3999999999999984923 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 23, 2579, 13127, 17443, 147253] }]) [cert2579, cert13127, cert17443, cert147253]

private theorem cert3999999999999986077 : Nat.Prime 3999999999999986077 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 47, 113, 149, 1459, 4861, 59393] }]) [cert1459, cert4861, cert59393]

private theorem cert3999999999999986453 : Nat.Prime 3999999999999986453 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 31, 47, 97, 419, 8627, 1957469] }]) [cert8627, cert1957469]

private theorem cert3999999999999988783 : Nat.Prime 3999999999999988783 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 1051, 7793, 13327, 290837] }]) [cert1051, cert7793, cert13327, cert290837]

private theorem cert3999999999999989597 : Nat.Prime 3999999999999989597 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 4091, 6317, 18803, 158303] }]) [cert4091, cert6317, cert18803, cert158303]

private theorem cert3999999999999991051 : Nat.Prime 3999999999999991051 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 79, 751, 13789, 1552207] }]) [cert13789, cert1552207]

private theorem cert3999999999999992801 : Nat.Prime 3999999999999992801 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 17, 2153, 10529, 1853497] }]) [cert2153, cert10529, cert1853497]

private theorem cert3999999999999993601 : Nat.Prime 3999999999999993601 := by
  primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 13, 29, 1667, 4999, 5101] }]) [cert1667, cert4999, cert5101]

private theorem cert3999999999999994813 : Nat.Prime 3999999999999994813 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 23, 199, 2697329913119] }]) [cert2697329913119]

private theorem cert3999999999999994937 : Nat.Prime 3999999999999994937 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 45454545454545397] }]) [cert45454545454545397]

private theorem cert3999999999999996337 : Nat.Prime 3999999999999996337 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 17, 1038043, 4722309947] }]) [cert1038043, cert4722309947]

private theorem cert3999999999999996397 : Nat.Prime 3999999999999996397 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 111111111111111011] }]) [cert111111111111111011]

private theorem cert3999999999999996611 : Nat.Prime 3999999999999996611 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 2693, 148533234311177] }]) [cert2693, cert148533234311177]

private theorem cert3999999999999996833 : Nat.Prime 3999999999999996833 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 17857142857142843] }]) [cert17857142857142843]

private theorem cert3999999999999997153 : Nat.Prime 3999999999999997153 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 17, 61, 5393, 15329, 162011] }]) [cert5393, cert15329, cert162011]

private theorem cert3999999999999997187 : Nat.Prime 3999999999999997187 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 117647058823529329] }]) [cert117647058823529329]

private theorem cert3999999999999997789 : Nat.Prime 3999999999999997789 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 333333333333333149] }]) [cert333333333333333149]

private theorem cert3999999999999998041 : Nat.Prime 3999999999999998041 := by
  primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 78427, 425023695071] }]) [cert78427, cert425023695071]

private theorem cert3999999999999998149 : Nat.Prime 3999999999999998149 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 11, 618429189857761] }]) [cert618429189857761]

private theorem cert3999999999999998369 : Nat.Prime 3999999999999998369 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 37, 277, 17921, 5624461] }]) [cert17921, cert5624461]

def offsets : List ℕ :=
  [2847, 10403, 8949, 57071, 15077, 24621, 7199, 13923, 18117, 67583, 59751, 68609, 88623, 42857, 135221, 36099, 77099, 137733, 72683, 180381, 21647, 109899, 130751, 96417, 154643, 225219, 175737, 214319, 245771, 223701, 197163, 145967, 203699, 191103, 113963, 90447, 132663, 39647, 188079, 204491, 113129, 233241, 13547, 182783, 11217, 212453, 143871, 83387, 69849, 138293, 173901, 65999, 80831, 78273, 6399, 53297, 59333, 1959, 3663, 1631, 1851, 3389, 5187, 5063, 2211, 2813, 3167, 3603]

private def certifiedOffsets : List {s : ℕ // (4000000000000000000-s).Prime} :=
  [⟨2847, cert3999999999999997153⟩,
   ⟨10403, cert3999999999999989597⟩,
   ⟨8949, cert3999999999999991051⟩,
   ⟨57071, cert3999999999999942929⟩,
   ⟨15077, cert3999999999999984923⟩,
   ⟨24621, cert3999999999999975379⟩,
   ⟨7199, cert3999999999999992801⟩,
   ⟨13923, cert3999999999999986077⟩,
   ⟨18117, cert3999999999999981883⟩,
   ⟨67583, cert3999999999999932417⟩,
   ⟨59751, cert3999999999999940249⟩,
   ⟨68609, cert3999999999999931391⟩,
   ⟨88623, cert3999999999999911377⟩,
   ⟨42857, cert3999999999999957143⟩,
   ⟨135221, cert3999999999999864779⟩,
   ⟨36099, cert3999999999999963901⟩,
   ⟨77099, cert3999999999999922901⟩,
   ⟨137733, cert3999999999999862267⟩,
   ⟨72683, cert3999999999999927317⟩,
   ⟨180381, cert3999999999999819619⟩,
   ⟨21647, cert3999999999999978353⟩,
   ⟨109899, cert3999999999999890101⟩,
   ⟨130751, cert3999999999999869249⟩,
   ⟨96417, cert3999999999999903583⟩,
   ⟨154643, cert3999999999999845357⟩,
   ⟨225219, cert3999999999999774781⟩,
   ⟨175737, cert3999999999999824263⟩,
   ⟨214319, cert3999999999999785681⟩,
   ⟨245771, cert3999999999999754229⟩,
   ⟨223701, cert3999999999999776299⟩,
   ⟨197163, cert3999999999999802837⟩,
   ⟨145967, cert3999999999999854033⟩,
   ⟨203699, cert3999999999999796301⟩,
   ⟨191103, cert3999999999999808897⟩,
   ⟨113963, cert3999999999999886037⟩,
   ⟨90447, cert3999999999999909553⟩,
   ⟨132663, cert3999999999999867337⟩,
   ⟨39647, cert3999999999999960353⟩,
   ⟨188079, cert3999999999999811921⟩,
   ⟨204491, cert3999999999999795509⟩,
   ⟨113129, cert3999999999999886871⟩,
   ⟨233241, cert3999999999999766759⟩,
   ⟨13547, cert3999999999999986453⟩,
   ⟨182783, cert3999999999999817217⟩,
   ⟨11217, cert3999999999999988783⟩,
   ⟨212453, cert3999999999999787547⟩,
   ⟨143871, cert3999999999999856129⟩,
   ⟨83387, cert3999999999999916613⟩,
   ⟨69849, cert3999999999999930151⟩,
   ⟨138293, cert3999999999999861707⟩,
   ⟨173901, cert3999999999999826099⟩,
   ⟨65999, cert3999999999999934001⟩,
   ⟨80831, cert3999999999999919169⟩,
   ⟨78273, cert3999999999999921727⟩,
   ⟨6399, cert3999999999999993601⟩,
   ⟨53297, cert3999999999999946703⟩,
   ⟨59333, cert3999999999999940667⟩,
   ⟨1959, cert3999999999999998041⟩,
   ⟨3663, cert3999999999999996337⟩,
   ⟨1631, cert3999999999999998369⟩,
   ⟨1851, cert3999999999999998149⟩,
   ⟨3389, cert3999999999999996611⟩,
   ⟨5187, cert3999999999999994813⟩,
   ⟨5063, cert3999999999999994937⟩,
   ⟨2211, cert3999999999999997789⟩,
   ⟨2813, cert3999999999999997187⟩,
   ⟨3167, cert3999999999999996833⟩,
   ⟨3603, cert3999999999999996397⟩]

/-- Lucas certificates establish primality of every large summand. -/
theorem anchors_prime (a : ℕ) (ha : a ∈ offsets) : Nat.Prime (4000000000000000000 - a) := by
  have hm : a ∈ certifiedOffsets.map Subtype.val := ha
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hm
  exact s.property


end PostBoundary524288.Anchors

/-! An exact finite Goldbach cover using a checked sieve of bit positions.
A geometric series proposes a mask of multiples. The kernel verifies its
first bit and translation closure, which suffice for the primality proof. -/

namespace PostBoundary524288.Cover

/-- Bits at indices less than `width`. -/
def lowMask (width : ℕ) : ℕ := (1 <<< width) - 1

theorem lowMask_bit (width i : ℕ) : (lowMask width).testBit i = decide (i < width) := by
  simp [lowMask, Nat.shiftLeft_eq, Nat.testBit_two_pow_sub_one]

/-- A mask passes if it contains zero and shifting a live bit by `step`
preserves it whenever the resulting position is below `width`. -/
def advances (width step bits : ℕ) : Bool :=
  let moved := (bits <<< step) &&& lowMask width
  bits.testBit 0 && ((moved &&& bits) == moved)

theorem multiples_in_mask {width step bits : ℕ} (h : advances width step bits = true)
    (k : ℕ) (hk : step * k < width) : bits.testBit (step * k) = true := by
  simp only [advances, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hz, hs'⟩ := h
  induction k with
  | zero => simpa using hz
  | succ k ih =>
    have hle : step * k ≤ step * (k + 1) := Nat.mul_le_mul_left step (Nat.le_succ k)
    have hprev := ih (lt_of_le_of_lt hle hk)
    have hge : step ≤ step * (k + 1) := by rw [Nat.mul_succ]; omega
    have hsub : step * (k + 1) - step = step * k := by rw [Nat.mul_succ]; omega
    have hm : ((bits <<< step) &&& lowMask width).testBit (step * (k+1)) = true := by
      simp [Nat.testBit_and, Nat.testBit_shiftLeft, lowMask_bit, hk, hge, hsub, hprev]
    have hi := congrArg (fun m : ℕ => m.testBit (step * (k + 1))) hs'
    change ((((bits <<< step) &&& lowMask width) &&& bits).testBit _) =
      (((bits <<< step) &&& lowMask width).testBit _) at hi
    rwa [Nat.testBit_and, hm, Bool.true_and] at hi

def unionBy {α : Type} (f : α → ℕ) : List α → ℕ
  | [] => 0
  | a :: rest => f a ||| unionBy f rest

theorem unionBy_bit {α : Type} (f : α → ℕ) (xs : List α) (i : ℕ) :
    (unionBy f xs).testBit i = true ↔ ∃ x ∈ xs, (f x).testBit i = true := by
  induction xs with
  | nil => simp [unionBy]
  | cons x xs ih => simp [unionBy, Nat.testBit_or, ih]

/-- The denominator is odd and positive when `d ≥ 2`. The proofs below
only need the checked closure property of this proposed periodic pattern. -/
def period (width d : ℕ) : ℕ :=
  lowMask ((width / d + 1) * d) / lowMask d

def divisors : List ℕ := (List.range 876).map (· + 2)
def width : ℕ := 770060

def survivors : ℕ := lowMask width ^^^ unionBy (period width) divisors

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem periods_checked : divisors.all (fun d => advances width d (period width d)) = true := by
  decide +kernel

theorem survivors_prime {q : ℕ} (hq : 2 ≤ q) (hlt : q < width)
    (hb : survivors.testBit q = true) : Nat.Prime q := by
  by_contra hcomp
  have hsq := Nat.minFac_sq_le_self (by omega : 0 < q) hcomp
  have hlo := (Nat.minFac_prime (by omega : q ≠ 1)).two_le
  have hupper : q.minFac < 878 := by
    by_contra! hlarge
    have hone := Nat.mul_le_mul hlarge hlarge
    rw [pow_two] at hsq
    change q < 770060 at hlt
    omega
  have hd : q.minFac ∈ divisors := by
    apply List.mem_map.mpr
    exact ⟨q.minFac - 2, List.mem_range.mpr (by omega), by omega⟩
  have hcheck := (List.all_eq_true.mp periods_checked) q.minFac hd
  obtain ⟨k, hdiv⟩ := Nat.minFac_dvd q
  have hp := multiples_in_mask hcheck k (by simpa only [← hdiv] using hlt)
  rw [← hdiv] at hp
  have hbad := (unionBy_bit (period width) divisors q).2 ⟨q.minFac, hd, hp⟩
  simp [survivors, Nat.testBit_xor, lowMask_bit, hlt, hbad] at hb

end PostBoundary524288.Cover

/-! A contiguous interval of binary Goldbach representations above 4 × 10¹⁸.
The large summands come from Lucas certificates. The small summands come
from the packed sieve proved sound above. -/

namespace PostBoundary524288.Cover

open PostBoundary524288.Anchors (offsets)

/-- Bit `2*k` selects a certified complement of a large anchor for
the target `4*10^18 + 262146 + 2*k`. -/
def targetBits : ℕ := unionBy (fun a => survivors >>> (a + 262146)) offsets

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem targets_checked : advances 262144 2 targetBits = true := by
  decide +kernel

theorem offset_bound {a : ℕ} (h : a ∈ offsets) : a ≤ 245771 := by
  have checked : offsets.all (fun v => decide (v ≤ 245771)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checked a h)

end PostBoundary524288.Cover

open PostBoundary524288.Anchors (offsets)
open PostBoundary524288.Cover in
theorem Conjectures.Goldbach.FinitePostBoundaryThrough524288 :
    (fun (lo hi : ℕ) => ∀ n : ℕ, lo≤n → n<hi → 2∣n →
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n) (4*10^18+262146) (4*10^18+524290) := by
  intro n hlo hhi he
  obtain ⟨half, hhalf⟩ := he
  let k := half - 2000000000000131073
  have heq : n = 4000000000000000000 + 262146 + 2*k := by dsimp [k]; omega
  have hpos : 2*k < 262144 := by omega
  have hbit := multiples_in_mask targets_checked k hpos
  obtain ⟨a, ha, hsmall⟩ := (unionBy_bit _ offsets (2*k)).1 hbit
  rw [Nat.testBit_shiftRight] at hsmall
  have bound := offset_bound ha
  have hp := PostBoundary524288.Anchors.anchors_prime a ha
  have hq := survivors_prime (q := a + 262146 + 2*k) (by omega)
    (by change _ < 770060; omega) hsmall
  exact ⟨4000000000000000000-a, a+262146+2*k, hp, hq, by omega⟩
