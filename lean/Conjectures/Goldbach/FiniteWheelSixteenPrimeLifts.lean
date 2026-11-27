import Mathlib

/- Lifts from the project's wheel.csv at commit 8fae77e19dff1beee0406459a65d691bebab1318,
   Apache-2.0. The Lucas witnesses and proofs below were generated for these entries.
   Each witness is checked using Mathlib's Lucas criterion. -/
private theorem primeInFactors {q : ℕ} (hq : q.Prime) (fs : List ℕ)
    (hf : ∀ f ∈ fs, f.Prime) (hd : q ∣ fs.prod) : q ∈ fs := by
  induction fs with
  | nil => simp at hd; exact (hq.ne_one hd).elim
  | cons f fs ih =>
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq := (Nat.prime_dvd_prime_iff_eq hq (hf f (by simp))).mp hd
      simp [heq]
    · exact List.mem_cons_of_mem f (ih (fun x hx => hf x (by simp [hx])) hd)

private theorem certPrime (p a : ℕ) (fs : List ℕ) (hf : fs.prod = p-1)
    (hpow : (a : ZMod p)^(p-1) = 1)
    (h : ∀ q ∈ fs, q.Prime ∧ (a : ZMod p)^((p-1)/q) ≠ 1) : p.Prime := by
  apply lucas_primality p a hpow
  intro q hq hd
  exact (h q (primeInFactors hq fs (fun x hx => (h x hx).1) (hf.symm ▸ hd))).2

private theorem pr2 : Nat.Prime 2 := by norm_num
private theorem pr3 : Nat.Prime 3 := by norm_num
private theorem pr5 : Nat.Prime 5 := by norm_num
private theorem pr7 : Nat.Prime 7 := by norm_num
private theorem pr11 : Nat.Prime 11 := by norm_num
private theorem pr13 : Nat.Prime 13 := by norm_num
private theorem pr17 : Nat.Prime 17 := by norm_num
private theorem pr19 : Nat.Prime 19 := by norm_num
private theorem pr23 : Nat.Prime 23 := by norm_num
private theorem pr29 : Nat.Prime 29 := by norm_num
private theorem pr31 : Nat.Prime 31 := by norm_num
private theorem pr37 : Nat.Prime 37 := by norm_num
private theorem pr41 : Nat.Prime 41 := by norm_num
private theorem pr43 : Nat.Prime 43 := by norm_num
private theorem pr47 : Nat.Prime 47 := by norm_num
private theorem pr53 : Nat.Prime 53 := by norm_num
private theorem pr59 : Nat.Prime 59 := by norm_num
private theorem pr61 : Nat.Prime 61 := by norm_num
private theorem pr67 : Nat.Prime 67 := by norm_num
private theorem pr71 : Nat.Prime 71 := by norm_num
private theorem pr73 : Nat.Prime 73 := by norm_num
private theorem pr79 : Nat.Prime 79 := by norm_num
private theorem pr83 : Nat.Prime 83 := by norm_num
private theorem pr89 : Nat.Prime 89 := by norm_num
private theorem pr97 : Nat.Prime 97 := by norm_num
private theorem pr103 : Nat.Prime 103 := by norm_num
private theorem pr107 : Nat.Prime 107 := by norm_num
private theorem pr109 : Nat.Prime 109 := by norm_num
private theorem pr113 : Nat.Prime 113 := by norm_num
private theorem pr127 : Nat.Prime 127 := by norm_num
private theorem pr131 : Nat.Prime 131 := by norm_num
private theorem pr137 : Nat.Prime 137 := by norm_num
private theorem pr139 : Nat.Prime 139 := by norm_num
private theorem pr149 : Nat.Prime 149 := by norm_num
private theorem pr151 : Nat.Prime 151 := by norm_num
private theorem pr163 : Nat.Prime 163 := by norm_num
private theorem pr167 : Nat.Prime 167 := by norm_num
private theorem pr173 : Nat.Prime 173 := by norm_num
private theorem pr179 : Nat.Prime 179 := by norm_num
private theorem pr181 : Nat.Prime 181 := by norm_num
private theorem pr191 : Nat.Prime 191 := by norm_num
private theorem pr193 : Nat.Prime 193 := by norm_num
private theorem pr197 : Nat.Prime 197 := by norm_num
private theorem pr199 : Nat.Prime 199 := by norm_num
private theorem pr223 : Nat.Prime 223 := by norm_num
private theorem pr229 : Nat.Prime 229 := by norm_num
private theorem pr233 : Nat.Prime 233 := by norm_num
private theorem pr241 : Nat.Prime 241 := by norm_num
private theorem pr251 : Nat.Prime 251 := by norm_num
private theorem pr263 : Nat.Prime 263 := by norm_num
private theorem pr271 : Nat.Prime 271 := by norm_num
private theorem pr277 : Nat.Prime 277 := by norm_num
private theorem pr281 : Nat.Prime 281 := by norm_num
private theorem pr293 : Nat.Prime 293 := by norm_num
private theorem pr311 : Nat.Prime 311 := by norm_num
private theorem pr313 : Nat.Prime 313 := by norm_num
private theorem pr317 : Nat.Prime 317 := by norm_num
private theorem pr337 : Nat.Prime 337 := by norm_num
private theorem pr347 : Nat.Prime 347 := by norm_num
private theorem pr349 : Nat.Prime 349 := by norm_num
private theorem pr353 : Nat.Prime 353 := by norm_num
private theorem pr373 : Nat.Prime 373 := by norm_num
private theorem pr379 : Nat.Prime 379 := by norm_num
private theorem pr397 : Nat.Prime 397 := by norm_num
private theorem pr409 : Nat.Prime 409 := by norm_num
private theorem pr433 : Nat.Prime 433 := by norm_num
private theorem pr443 : Nat.Prime 443 := by norm_num
private theorem pr449 : Nat.Prime 449 := by norm_num
private theorem pr461 : Nat.Prime 461 := by norm_num
private theorem pr463 : Nat.Prime 463 := by norm_num
private theorem pr467 : Nat.Prime 467 := by norm_num
private theorem pr479 : Nat.Prime 479 := by norm_num
private theorem pr487 : Nat.Prime 487 := by norm_num
private theorem pr491 : Nat.Prime 491 := by norm_num
private theorem pr509 : Nat.Prime 509 := by norm_num
private theorem pr521 : Nat.Prime 521 := by norm_num
private theorem pr523 : Nat.Prime 523 := by norm_num
private theorem pr569 : Nat.Prime 569 := by norm_num
private theorem pr571 : Nat.Prime 571 := by norm_num
private theorem pr577 : Nat.Prime 577 := by norm_num
private theorem pr593 : Nat.Prime 593 := by norm_num
private theorem pr599 : Nat.Prime 599 := by norm_num
private theorem pr601 : Nat.Prime 601 := by norm_num
private theorem pr613 : Nat.Prime 613 := by norm_num
private theorem pr617 : Nat.Prime 617 := by norm_num
private theorem pr619 : Nat.Prime 619 := by norm_num
private theorem pr641 : Nat.Prime 641 := by norm_num
private theorem pr653 : Nat.Prime 653 := by norm_num
private theorem pr659 : Nat.Prime 659 := by norm_num
private theorem pr683 : Nat.Prime 683 := by norm_num
private theorem pr691 : Nat.Prime 691 := by norm_num
private theorem pr701 : Nat.Prime 701 := by norm_num
private theorem pr709 : Nat.Prime 709 := by norm_num
private theorem pr733 : Nat.Prime 733 := by norm_num
private theorem pr743 : Nat.Prime 743 := by norm_num
private theorem pr751 : Nat.Prime 751 := by norm_num
private theorem pr769 : Nat.Prime 769 := by norm_num
private theorem pr773 : Nat.Prime 773 := by norm_num
private theorem pr809 : Nat.Prime 809 := by norm_num
private theorem pr811 : Nat.Prime 811 := by norm_num
private theorem pr821 : Nat.Prime 821 := by norm_num
private theorem pr853 : Nat.Prime 853 := by norm_num
private theorem pr863 : Nat.Prime 863 := by norm_num
private theorem pr887 : Nat.Prime 887 := by norm_num
private theorem pr907 : Nat.Prime 907 := by norm_num
private theorem pr911 : Nat.Prime 911 := by norm_num
private theorem pr937 : Nat.Prime 937 := by norm_num
private theorem pr953 : Nat.Prime 953 := by norm_num
private theorem pr997 : Nat.Prime 997 := by norm_num
private theorem pr1009 : Nat.Prime 1009 := by
  apply certPrime 1009 11 [2, 2, 2, 2, 3, 3, 7] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr7, by decide⟩
private theorem pr1033 : Nat.Prime 1033 := by
  apply certPrime 1033 5 [2, 2, 2, 3, 43] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr43, by decide⟩
private theorem pr1049 : Nat.Prime 1049 := by
  apply certPrime 1049 3 [2, 2, 2, 131] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr131, by decide⟩
private theorem pr1087 : Nat.Prime 1087 := by
  apply certPrime 1087 3 [2, 3, 181] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr181, by decide⟩
private theorem pr1109 : Nat.Prime 1109 := by
  apply certPrime 1109 2 [2, 2, 277] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr277, by decide⟩
private theorem pr1129 : Nat.Prime 1129 := by
  apply certPrime 1129 11 [2, 2, 2, 3, 47] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr47, by decide⟩
private theorem pr1187 : Nat.Prime 1187 := by
  apply certPrime 1187 2 [2, 593] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr593, by decide⟩
private theorem pr1231 : Nat.Prime 1231 := by
  apply certPrime 1231 3 [2, 3, 5, 41] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr41, by decide⟩
private theorem pr1289 : Nat.Prime 1289 := by
  apply certPrime 1289 6 [2, 2, 2, 7, 23] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr23, by decide⟩
private theorem pr1301 : Nat.Prime 1301 := by
  apply certPrime 1301 2 [2, 2, 5, 5, 13] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr13, by decide⟩
private theorem pr1319 : Nat.Prime 1319 := by
  apply certPrime 1319 13 [2, 659] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr659, by decide⟩
private theorem pr1367 : Nat.Prime 1367 := by
  apply certPrime 1367 5 [2, 683] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr683, by decide⟩
private theorem pr1399 : Nat.Prime 1399 := by
  apply certPrime 1399 13 [2, 3, 233] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr233, by decide⟩
private theorem pr1453 : Nat.Prime 1453 := by
  apply certPrime 1453 2 [2, 2, 3, 11, 11] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr11, by decide⟩
private theorem pr1481 : Nat.Prime 1481 := by
  apply certPrime 1481 3 [2, 2, 2, 5, 37] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr37, by decide⟩
private theorem pr1493 : Nat.Prime 1493 := by
  apply certPrime 1493 2 [2, 2, 373] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr373, by decide⟩
private theorem pr1511 : Nat.Prime 1511 := by
  apply certPrime 1511 11 [2, 5, 151] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr151, by decide⟩
private theorem pr1549 : Nat.Prime 1549 := by
  apply certPrime 1549 2 [2, 2, 3, 3, 43] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr43, by decide⟩
private theorem pr1579 : Nat.Prime 1579 := by
  apply certPrime 1579 3 [2, 3, 263] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr263, by decide⟩
private theorem pr1609 : Nat.Prime 1609 := by
  apply certPrime 1609 7 [2, 2, 2, 3, 67] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr67, by decide⟩
private theorem pr1657 : Nat.Prime 1657 := by
  apply certPrime 1657 11 [2, 2, 2, 3, 3, 23] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr23, by decide⟩
private theorem pr1669 : Nat.Prime 1669 := by
  apply certPrime 1669 2 [2, 2, 3, 139] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr139, by decide⟩
private theorem pr1733 : Nat.Prime 1733 := by
  apply certPrime 1733 2 [2, 2, 433] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr433, by decide⟩
private theorem pr1741 : Nat.Prime 1741 := by
  apply certPrime 1741 2 [2, 2, 3, 5, 29] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr29, by decide⟩
private theorem pr1753 : Nat.Prime 1753 := by
  apply certPrime 1753 7 [2, 2, 2, 3, 73] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr73, by decide⟩
private theorem pr1811 : Nat.Prime 1811 := by
  apply certPrime 1811 6 [2, 5, 181] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr181, by decide⟩
private theorem pr1877 : Nat.Prime 1877 := by
  apply certPrime 1877 2 [2, 2, 7, 67] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr67, by decide⟩
private theorem pr1907 : Nat.Prime 1907 := by
  apply certPrime 1907 2 [2, 953] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr953, by decide⟩
private theorem pr1931 : Nat.Prime 1931 := by
  apply certPrime 1931 2 [2, 5, 193] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr193, by decide⟩
private theorem pr2003 : Nat.Prime 2003 := by
  apply certPrime 2003 5 [2, 7, 11, 13] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr13, by decide⟩
private theorem pr2029 : Nat.Prime 2029 := by
  apply certPrime 2029 2 [2, 2, 3, 13, 13] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr13, by decide⟩
private theorem pr2237 : Nat.Prime 2237 := by
  apply certPrime 2237 2 [2, 2, 13, 43] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr43, by decide⟩
private theorem pr2377 : Nat.Prime 2377 := by
  apply certPrime 2377 5 [2, 2, 2, 3, 3, 3, 11] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr11, by decide⟩
private theorem pr2389 : Nat.Prime 2389 := by
  apply certPrime 2389 2 [2, 2, 3, 199] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr199, by decide⟩
private theorem pr2437 : Nat.Prime 2437 := by
  apply certPrime 2437 2 [2, 2, 3, 7, 29] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr29, by decide⟩
private theorem pr2473 : Nat.Prime 2473 := by
  apply certPrime 2473 5 [2, 2, 2, 3, 103] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr103, by decide⟩
private theorem pr2477 : Nat.Prime 2477 := by
  apply certPrime 2477 2 [2, 2, 619] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr619, by decide⟩
private theorem pr2659 : Nat.Prime 2659 := by
  apply certPrime 2659 2 [2, 3, 443] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr443, by decide⟩
private theorem pr2677 : Nat.Prime 2677 := by
  apply certPrime 2677 2 [2, 2, 3, 223] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr223, by decide⟩
private theorem pr2719 : Nat.Prime 2719 := by
  apply certPrime 2719 3 [2, 3, 3, 151] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr151, by decide⟩
private theorem pr2731 : Nat.Prime 2731 := by
  apply certPrime 2731 3 [2, 3, 5, 7, 13] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr13, by decide⟩
private theorem pr2797 : Nat.Prime 2797 := by
  apply certPrime 2797 2 [2, 2, 3, 233] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr233, by decide⟩
private theorem pr2861 : Nat.Prime 2861 := by
  apply certPrime 2861 2 [2, 2, 5, 11, 13] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr13, by decide⟩
private theorem pr3037 : Nat.Prime 3037 := by
  apply certPrime 3037 2 [2, 2, 3, 11, 23] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr23, by decide⟩
private theorem pr3049 : Nat.Prime 3049 := by
  apply certPrime 3049 11 [2, 2, 2, 3, 127] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr127, by decide⟩
private theorem pr3371 : Nat.Prime 3371 := by
  apply certPrime 3371 2 [2, 5, 337] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr337, by decide⟩
private theorem pr3407 : Nat.Prime 3407 := by
  apply certPrime 3407 5 [2, 13, 131] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr131, by decide⟩
private theorem pr3463 : Nat.Prime 3463 := by
  apply certPrime 3463 3 [2, 3, 577] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr577, by decide⟩
private theorem pr3623 : Nat.Prime 3623 := by
  apply certPrime 3623 5 [2, 1811] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr1811, by decide⟩
private theorem pr3691 : Nat.Prime 3691 := by
  apply certPrime 3691 2 [2, 3, 3, 5, 41] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr41, by decide⟩
private theorem pr3793 : Nat.Prime 3793 := by
  apply certPrime 3793 5 [2, 2, 2, 2, 3, 79] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr79, by decide⟩
private theorem pr3929 : Nat.Prime 3929 := by
  apply certPrime 3929 3 [2, 2, 2, 491] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr491, by decide⟩
private theorem pr4007 : Nat.Prime 4007 := by
  apply certPrime 4007 5 [2, 2003] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2003, by decide⟩
private theorem pr4219 : Nat.Prime 4219 := by
  apply certPrime 4219 2 [2, 3, 19, 37] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr19, by decide⟩
  · exact ⟨pr37, by decide⟩
private theorem pr4483 : Nat.Prime 4483 := by
  apply certPrime 4483 2 [2, 3, 3, 3, 83] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr83, by decide⟩
private theorem pr5119 : Nat.Prime 5119 := by
  apply certPrime 5119 3 [2, 3, 853] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr853, by decide⟩
private theorem pr5813 : Nat.Prime 5813 := by
  apply certPrime 5813 2 [2, 2, 1453] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr1453, by decide⟩
private theorem pr5987 : Nat.Prime 5987 := by
  apply certPrime 5987 2 [2, 41, 73] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr41, by decide⟩
  · exact ⟨pr73, by decide⟩
private theorem pr6007 : Nat.Prime 6007 := by
  apply certPrime 6007 3 [2, 3, 7, 11, 13] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr13, by decide⟩
private theorem pr6053 : Nat.Prime 6053 := by
  apply certPrime 6053 2 [2, 2, 17, 89] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr17, by decide⟩
  · exact ⟨pr89, by decide⟩
private theorem pr6113 : Nat.Prime 6113 := by
  apply certPrime 6113 3 [2, 2, 2, 2, 2, 191] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr191, by decide⟩
private theorem pr6197 : Nat.Prime 6197 := by
  apply certPrime 6197 2 [2, 2, 1549] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr1549, by decide⟩
private theorem pr6257 : Nat.Prime 6257 := by
  apply certPrime 6257 3 [2, 2, 2, 2, 17, 23] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr17, by decide⟩
  · exact ⟨pr23, by decide⟩
private theorem pr6317 : Nat.Prime 6317 := by
  apply certPrime 6317 2 [2, 2, 1579] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr1579, by decide⟩
private theorem pr6491 : Nat.Prime 6491 := by
  apply certPrime 6491 2 [2, 5, 11, 59] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr59, by decide⟩
private theorem pr6581 : Nat.Prime 6581 := by
  apply certPrime 6581 14 [2, 2, 5, 7, 47] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr47, by decide⟩
private theorem pr7013 : Nat.Prime 7013 := by
  apply certPrime 7013 2 [2, 2, 1753] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr1753, by decide⟩
private theorem pr7151 : Nat.Prime 7151 := by
  apply certPrime 7151 7 [2, 5, 5, 11, 13] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr13, by decide⟩
private theorem pr7333 : Nat.Prime 7333 := by
  apply certPrime 7333 6 [2, 2, 3, 13, 47] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr47, by decide⟩
private theorem pr8009 : Nat.Prime 8009 := by
  apply certPrime 8009 3 [2, 2, 2, 7, 11, 13] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr13, by decide⟩
private theorem pr8011 : Nat.Prime 8011 := by
  apply certPrime 8011 14 [2, 3, 3, 5, 89] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr89, by decide⟩
private theorem pr8087 : Nat.Prime 8087 := by
  apply certPrime 8087 5 [2, 13, 311] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr311, by decide⟩
private theorem pr8663 : Nat.Prime 8663 := by
  apply certPrime 8663 5 [2, 61, 71] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr61, by decide⟩
  · exact ⟨pr71, by decide⟩
private theorem pr9011 : Nat.Prime 9011 := by
  apply certPrime 9011 2 [2, 5, 17, 53] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr17, by decide⟩
  · exact ⟨pr53, by decide⟩
private theorem pr9241 : Nat.Prime 9241 := by
  apply certPrime 9241 13 [2, 2, 2, 3, 5, 7, 11] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr11, by decide⟩
private theorem pr9461 : Nat.Prime 9461 := by
  apply certPrime 9461 3 [2, 2, 5, 11, 43] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr43, by decide⟩
private theorem pr9689 : Nat.Prime 9689 := by
  apply certPrime 9689 3 [2, 2, 2, 7, 173] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr173, by decide⟩
private theorem pr9749 : Nat.Prime 9749 := by
  apply certPrime 9749 2 [2, 2, 2437] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2437, by decide⟩
private theorem pr10313 : Nat.Prime 10313 := by
  apply certPrime 10313 3 [2, 2, 2, 1289] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr1289, by decide⟩
private theorem pr10937 : Nat.Prime 10937 := by
  apply certPrime 10937 3 [2, 2, 2, 1367] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr1367, by decide⟩
private theorem pr12107 : Nat.Prime 12107 := by
  apply certPrime 12107 2 [2, 6053] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr6053, by decide⟩
private theorem pr12227 : Nat.Prime 12227 := by
  apply certPrime 12227 2 [2, 6113] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr6113, by decide⟩
private theorem pr14479 : Nat.Prime 14479 := by
  apply certPrime 14479 3 [2, 3, 19, 127] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr19, by decide⟩
  · exact ⟨pr127, by decide⟩
private theorem pr14489 : Nat.Prime 14489 := by
  apply certPrime 14489 3 [2, 2, 2, 1811] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr1811, by decide⟩
private theorem pr14551 : Nat.Prime 14551 := by
  apply certPrime 14551 3 [2, 3, 5, 5, 97] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr97, by decide⟩
private theorem pr15017 : Nat.Prime 15017 := by
  apply certPrime 15017 3 [2, 2, 2, 1877] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr1877, by decide⟩
private theorem pr17327 : Nat.Prime 17327 := by
  apply certPrime 17327 5 [2, 8663] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr8663, by decide⟩
private theorem pr17519 : Nat.Prime 17519 := by
  apply certPrime 17519 13 [2, 19, 461] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr19, by decide⟩
  · exact ⟨pr461, by decide⟩
private theorem pr19963 : Nat.Prime 19963 := by
  apply certPrime 19963 2 [2, 3, 3, 1109] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr1109, by decide⟩
private theorem pr21739 : Nat.Prime 21739 := by
  apply certPrime 21739 2 [2, 3, 3623] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3623, by decide⟩
private theorem pr21841 : Nat.Prime 21841 := by
  apply certPrime 21841 11 [2, 2, 2, 2, 3, 5, 7, 13] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr13, by decide⟩
private theorem pr25183 : Nat.Prime 25183 := by
  apply certPrime 25183 5 [2, 3, 3, 1399] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr1399, by decide⟩
private theorem pr26021 : Nat.Prime 26021 := by
  apply certPrime 26021 2 [2, 2, 5, 1301] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr1301, by decide⟩
private theorem pr26591 : Nat.Prime 26591 := by
  apply certPrime 26591 22 [2, 5, 2659] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr2659, by decide⟩
private theorem pr27031 : Nat.Prime 27031 := by
  apply certPrime 27031 6 [2, 3, 5, 17, 53] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr17, by decide⟩
  · exact ⟨pr53, by decide⟩
private theorem pr30047 : Nat.Prime 30047 := by
  apply certPrime 30047 5 [2, 83, 181] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr83, by decide⟩
  · exact ⟨pr181, by decide⟩
private theorem pr30059 : Nat.Prime 30059 := by
  apply certPrime 30059 2 [2, 7, 19, 113] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr19, by decide⟩
  · exact ⟨pr113, by decide⟩
private theorem pr30071 : Nat.Prime 30071 := by
  apply certPrime 30071 13 [2, 5, 31, 97] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr31, by decide⟩
  · exact ⟨pr97, by decide⟩
private theorem pr30097 : Nat.Prime 30097 := by
  apply certPrime 30097 10 [2, 2, 2, 2, 3, 3, 11, 19] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr19, by decide⟩
private theorem pr30211 : Nat.Prime 30211 := by
  apply certPrime 30211 2 [2, 3, 5, 19, 53] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr19, by decide⟩
  · exact ⟨pr53, by decide⟩
private theorem pr30271 : Nat.Prime 30271 := by
  apply certPrime 30271 3 [2, 3, 5, 1009] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr1009, by decide⟩
private theorem pr30389 : Nat.Prime 30389 := by
  apply certPrime 30389 2 [2, 2, 71, 107] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr71, by decide⟩
  · exact ⟨pr107, by decide⟩
private theorem pr37549 : Nat.Prime 37549 := by
  apply certPrime 37549 2 [2, 2, 3, 3, 7, 149] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr149, by decide⟩
private theorem pr39569 : Nat.Prime 39569 := by
  apply certPrime 39569 3 [2, 2, 2, 2, 2473] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2473, by decide⟩
private theorem pr41953 : Nat.Prime 41953 := by
  apply certPrime 41953 5 [2, 2, 2, 2, 2, 3, 19, 23] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr19, by decide⟩
  · exact ⟨pr23, by decide⟩
private theorem pr42433 : Nat.Prime 42433 := by
  apply certPrime 42433 10 [2, 2, 2, 2, 2, 2, 3, 13, 17] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr17, by decide⟩
private theorem pr43661 : Nat.Prime 43661 := by
  apply certPrime 43661 2 [2, 2, 5, 37, 59] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr37, by decide⟩
  · exact ⟨pr59, by decide⟩
private theorem pr45053 : Nat.Prime 45053 := by
  apply certPrime 45053 2 [2, 2, 7, 1609] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr1609, by decide⟩
private theorem pr45779 : Nat.Prime 45779 := by
  apply certPrime 45779 2 [2, 47, 487] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr47, by decide⟩
  · exact ⟨pr487, by decide⟩
private theorem pr47809 : Nat.Prime 47809 := by
  apply certPrime 47809 7 [2, 2, 2, 2, 2, 2, 3, 3, 83] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr83, by decide⟩
private theorem pr50053 : Nat.Prime 50053 := by
  apply certPrime 50053 2 [2, 2, 3, 43, 97] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr43, by decide⟩
  · exact ⟨pr97, by decide⟩
private theorem pr56911 : Nat.Prime 56911 := by
  apply certPrime 56911 3 [2, 3, 5, 7, 271] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr271, by decide⟩
private theorem pr56957 : Nat.Prime 56957 := by
  apply certPrime 56957 2 [2, 2, 29, 491] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr29, by decide⟩
  · exact ⟨pr491, by decide⟩
private theorem pr57917 : Nat.Prime 57917 := by
  apply certPrime 57917 2 [2, 2, 14479] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr14479, by decide⟩
private theorem pr59281 : Nat.Prime 59281 := by
  apply certPrime 59281 7 [2, 2, 2, 2, 3, 5, 13, 19] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr19, by decide⟩
private theorem pr60077 : Nat.Prime 60077 := by
  apply certPrime 60077 2 [2, 2, 23, 653] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr23, by decide⟩
  · exact ⟨pr653, by decide⟩
private theorem pr60083 : Nat.Prime 60083 := by
  apply certPrime 60083 2 [2, 11, 2731] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr2731, by decide⟩
private theorem pr60089 : Nat.Prime 60089 := by
  apply certPrime 60089 3 [2, 2, 2, 7, 29, 37] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr29, by decide⟩
  · exact ⟨pr37, by decide⟩
private theorem pr60091 : Nat.Prime 60091 := by
  apply certPrime 60091 2 [2, 3, 5, 2003] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr2003, by decide⟩
private theorem pr60101 : Nat.Prime 60101 := by
  apply certPrime 60101 3 [2, 2, 5, 5, 601] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr601, by decide⟩
private theorem pr60103 : Nat.Prime 60103 := by
  apply certPrime 60103 5 [2, 3, 3, 3, 3, 7, 53] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr53, by decide⟩
private theorem pr60107 : Nat.Prime 60107 := by
  apply certPrime 60107 2 [2, 41, 733] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr41, by decide⟩
  · exact ⟨pr733, by decide⟩
private theorem pr60127 : Nat.Prime 60127 := by
  apply certPrime 60127 3 [2, 3, 11, 911] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr911, by decide⟩
private theorem pr60779 : Nat.Prime 60779 := by
  apply certPrime 60779 2 [2, 30389] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr30389, by decide⟩
private theorem pr72643 : Nat.Prime 72643 := by
  apply certPrime 72643 2 [2, 3, 12107] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr12107, by decide⟩
private theorem pr75079 : Nat.Prime 75079 := by
  apply certPrime 75079 3 [2, 3, 3, 43, 97] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr43, by decide⟩
  · exact ⟨pr97, by decide⟩
private theorem pr77513 : Nat.Prime 77513 := by
  apply certPrime 77513 3 [2, 2, 2, 9689] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr9689, by decide⟩
private theorem pr83911 : Nat.Prime 83911 := by
  apply certPrime 83911 3 [2, 3, 5, 2797] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr2797, by decide⟩
private theorem pr89909 : Nat.Prime 89909 := by
  apply certPrime 89909 2 [2, 2, 7, 13, 13, 19] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr19, by decide⟩
private theorem pr90107 : Nat.Prime 90107 := by
  apply certPrime 90107 2 [2, 45053] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr45053, by decide⟩
private theorem pr90121 : Nat.Prime 90121 := by
  apply certPrime 90121 23 [2, 2, 2, 3, 5, 751] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr751, by decide⟩
private theorem pr90127 : Nat.Prime 90127 := by
  apply certPrime 90127 3 [2, 3, 3, 3, 1669] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr1669, by decide⟩
private theorem pr90271 : Nat.Prime 90271 := by
  apply certPrime 90271 3 [2, 3, 3, 5, 17, 59] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr17, by decide⟩
  · exact ⟨pr59, by decide⟩
private theorem pr97609 : Nat.Prime 97609 := by
  apply certPrime 97609 17 [2, 2, 2, 3, 7, 7, 83] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr83, by decide⟩
private theorem pr101611 : Nat.Prime 101611 := by
  apply certPrime 101611 2 [2, 3, 3, 5, 1129] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr1129, by decide⟩
private theorem pr118603 : Nat.Prime 118603 := by
  apply certPrime 118603 2 [2, 3, 3, 11, 599] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr599, by decide⟩
private theorem pr120157 : Nat.Prime 120157 := by
  apply certPrime 120157 2 [2, 2, 3, 17, 19, 31] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr17, by decide⟩
  · exact ⟨pr19, by decide⟩
  · exact ⟨pr31, by decide⟩
private theorem pr120163 : Nat.Prime 120163 := by
  apply certPrime 120163 3 [2, 3, 7, 2861] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr2861, by decide⟩
private theorem pr120167 : Nat.Prime 120167 := by
  apply certPrime 120167 5 [2, 60083] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr60083, by decide⟩
private theorem pr121559 : Nat.Prime 121559 := by
  apply certPrime 121559 7 [2, 60779] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr60779, by decide⟩
private theorem pr122653 : Nat.Prime 122653 := by
  apply certPrime 122653 5 [2, 2, 3, 3, 3407] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3407, by decide⟩
private theorem pr125131 : Nat.Prime 125131 := by
  apply certPrime 125131 2 [2, 3, 5, 43, 97] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr43, by decide⟩
  · exact ⟨pr97, by decide⟩
private theorem pr126517 : Nat.Prime 126517 := by
  apply certPrime 126517 2 [2, 2, 3, 13, 811] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr811, by decide⟩
private theorem pr149873 : Nat.Prime 149873 := by
  apply certPrime 149873 5 [2, 2, 2, 2, 17, 19, 29] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr17, by decide⟩
  · exact ⟨pr19, by decide⟩
  · exact ⟨pr29, by decide⟩
private theorem pr150169 : Nat.Prime 150169 := by
  apply certPrime 150169 7 [2, 2, 2, 3, 6257] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr6257, by decide⟩
private theorem pr150193 : Nat.Prime 150193 := by
  apply certPrime 150193 5 [2, 2, 2, 2, 3, 3, 7, 149] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr149, by decide⟩
private theorem pr150197 : Nat.Prime 150197 := by
  apply certPrime 150197 2 [2, 2, 37549] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr37549, by decide⟩
private theorem pr150203 : Nat.Prime 150203 := by
  apply certPrime 150203 2 [2, 13, 53, 109] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr53, by decide⟩
  · exact ⟨pr109, by decide⟩
private theorem pr150217 : Nat.Prime 150217 := by
  apply certPrime 150217 10 [2, 2, 2, 3, 11, 569] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr569, by decide⟩
private theorem pr158633 : Nat.Prime 158633 := by
  apply certPrime 158633 3 [2, 2, 2, 79, 251] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr79, by decide⟩
  · exact ⟨pr251, by decide⟩
private theorem pr160313 : Nat.Prime 160313 := by
  apply certPrime 160313 3 [2, 2, 2, 29, 691] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr29, by decide⟩
  · exact ⟨pr691, by decide⟩
private theorem pr165173 : Nat.Prime 165173 := by
  apply certPrime 165173 2 [2, 2, 7, 17, 347] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr17, by decide⟩
  · exact ⟨pr347, by decide⟩
private theorem pr180211 : Nat.Prime 180211 := by
  apply certPrime 180211 2 [2, 3, 5, 6007] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr6007, by decide⟩
private theorem pr180221 : Nat.Prime 180221 := by
  apply certPrime 180221 2 [2, 2, 5, 9011] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr9011, by decide⟩
private theorem pr180233 : Nat.Prime 180233 := by
  apply certPrime 180233 3 [2, 2, 2, 13, 1733] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr1733, by decide⟩
private theorem pr180247 : Nat.Prime 180247 := by
  apply certPrime 180247 3 [2, 3, 11, 2731] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr2731, by decide⟩
private theorem pr180361 : Nat.Prime 180361 := by
  apply certPrime 180361 21 [2, 2, 2, 3, 3, 3, 5, 167] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr167, by decide⟩
private theorem pr182779 : Nat.Prime 182779 := by
  apply certPrime 182779 2 [2, 3, 41, 743] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr41, by decide⟩
  · exact ⟨pr743, by decide⟩
private theorem pr195203 : Nat.Prime 195203 := by
  apply certPrime 195203 2 [2, 7, 73, 191] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr73, by decide⟩
  · exact ⟨pr191, by decide⟩
private theorem pr210229 : Nat.Prime 210229 := by
  apply certPrime 210229 2 [2, 2, 3, 17519] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr17519, by decide⟩
private theorem pr210233 : Nat.Prime 210233 := by
  apply certPrime 210233 3 [2, 2, 2, 11, 2389] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr2389, by decide⟩
private theorem pr210241 : Nat.Prime 210241 := by
  apply certPrime 210241 7 [2, 2, 2, 2, 2, 2, 3, 3, 5, 73] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr73, by decide⟩
private theorem pr210247 : Nat.Prime 210247 := by
  apply certPrime 210247 3 [2, 3, 67, 523] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr67, by decide⟩
  · exact ⟨pr523, by decide⟩
private theorem pr210257 : Nat.Prime 210257 := by
  apply certPrime 210257 3 [2, 2, 2, 2, 17, 773] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr17, by decide⟩
  · exact ⟨pr773, by decide⟩
private theorem pr210263 : Nat.Prime 210263 := by
  apply certPrime 210263 5 [2, 13, 8087] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr8087, by decide⟩
private theorem pr210277 : Nat.Prime 210277 := by
  apply certPrime 210277 2 [2, 2, 3, 3, 3, 3, 11, 59] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr59, by decide⟩
private theorem pr210391 : Nat.Prime 210391 := by
  apply certPrime 210391 3 [2, 3, 5, 7013] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr7013, by decide⟩
private theorem pr211283 : Nat.Prime 211283 := by
  apply certPrime 211283 2 [2, 149, 709] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr149, by decide⟩
  · exact ⟨pr709, by decide⟩
private theorem pr214381 : Nat.Prime 214381 := by
  apply certPrime 214381 2 [2, 2, 3, 3, 3, 5, 397] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr397, by decide⟩
private theorem pr215389 : Nat.Prime 215389 := by
  apply certPrime 215389 2 [2, 2, 3, 3, 31, 193] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr31, by decide⟩
  · exact ⟨pr193, by decide⟩
private theorem pr239557 : Nat.Prime 239557 := by
  apply certPrime 239557 2 [2, 2, 3, 19963] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr19963, by decide⟩
private theorem pr240257 : Nat.Prime 240257 := by
  apply certPrime 240257 3 [2, 2, 2, 2, 2, 2, 2, 1877] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr1877, by decide⟩
private theorem pr240259 : Nat.Prime 240259 := by
  apply certPrime 240259 2 [2, 3, 23, 1741] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr23, by decide⟩
  · exact ⟨pr1741, by decide⟩
private theorem pr240263 : Nat.Prime 240263 := by
  apply certPrime 240263 5 [2, 11, 67, 163] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr67, by decide⟩
  · exact ⟨pr163, by decide⟩
private theorem pr240271 : Nat.Prime 240271 := by
  apply certPrime 240271 6 [2, 3, 5, 8009] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr8009, by decide⟩
private theorem pr240283 : Nat.Prime 240283 := by
  apply certPrime 240283 2 [2, 3, 3, 7, 1907] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr1907, by decide⟩
private theorem pr240287 : Nat.Prime 240287 := by
  apply certPrime 240287 5 [2, 317, 379] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr317, by decide⟩
  · exact ⟨pr379, by decide⟩
private theorem pr240421 : Nat.Prime 240421 := by
  apply certPrime 240421 6 [2, 2, 3, 5, 4007] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr4007, by decide⟩
private theorem pr243119 : Nat.Prime 243119 := by
  apply certPrime 243119 7 [2, 121559] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr121559, by decide⟩
private theorem pr270287 : Nat.Prime 270287 := by
  apply certPrime 270287 5 [2, 149, 907] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr149, by decide⟩
  · exact ⟨pr907, by decide⟩
private theorem pr270299 : Nat.Prime 270299 := by
  apply certPrime 270299 2 [2, 7, 43, 449] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr43, by decide⟩
  · exact ⟨pr449, by decide⟩
private theorem pr270307 : Nat.Prime 270307 := by
  apply certPrime 270307 3 [2, 3, 3, 15017] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr15017, by decide⟩
private theorem pr270311 : Nat.Prime 270311 := by
  apply certPrime 270311 13 [2, 5, 27031] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr27031, by decide⟩
private theorem pr270323 : Nat.Prime 270323 := by
  apply certPrime 270323 2 [2, 13, 37, 281] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr37, by decide⟩
  · exact ⟨pr281, by decide⟩
private theorem pr270337 : Nat.Prime 270337 := by
  apply certPrime 270337 10 [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 11] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr11, by decide⟩
private theorem pr270451 : Nat.Prime 270451 := by
  apply certPrime 270451 2 [2, 3, 3, 5, 5, 601] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr601, by decide⟩
private theorem pr300317 : Nat.Prime 300317 := by
  apply certPrime 300317 2 [2, 2, 75079] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr75079, by decide⟩
private theorem pr300319 : Nat.Prime 300319 := by
  apply certPrime 300319 3 [2, 3, 50053] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr50053, by decide⟩
private theorem pr300323 : Nat.Prime 300323 := by
  apply certPrime 300323 2 [2, 11, 11, 17, 73] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr17, by decide⟩
  · exact ⟨pr73, by decide⟩
private theorem pr300331 : Nat.Prime 300331 := by
  apply certPrime 300331 3 [2, 3, 3, 5, 47, 71] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr47, by decide⟩
  · exact ⟨pr71, by decide⟩
private theorem pr300343 : Nat.Prime 300343 := by
  apply certPrime 300343 3 [2, 3, 7, 7151] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr7151, by decide⟩
private theorem pr300347 : Nat.Prime 300347 := by
  apply certPrime 300347 2 [2, 263, 571] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr263, by decide⟩
  · exact ⟨pr571, by decide⟩
private theorem pr300367 : Nat.Prime 300367 := by
  apply certPrime 300367 3 [2, 3, 3, 11, 37, 41] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr37, by decide⟩
  · exact ⟨pr41, by decide⟩
private theorem pr300481 : Nat.Prime 300481 := by
  apply certPrime 300481 14 [2, 2, 2, 2, 2, 2, 3, 5, 313] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr313, by decide⟩
private theorem pr302711 : Nat.Prime 302711 := by
  apply certPrime 302711 13 [2, 5, 30271] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr30271, by decide⟩
private theorem pr317267 : Nat.Prime 317267 := by
  apply certPrime 317267 2 [2, 158633] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr158633, by decide⟩
private theorem pr330347 : Nat.Prime 330347 := by
  apply certPrime 330347 2 [2, 165173] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr165173, by decide⟩
private theorem pr330359 : Nat.Prime 330359 := by
  apply certPrime 330359 7 [2, 7, 7, 3371] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr3371, by decide⟩
private theorem pr330383 : Nat.Prime 330383 := by
  apply certPrime 330383 5 [2, 13, 97, 131] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr97, by decide⟩
  · exact ⟨pr131, by decide⟩
private theorem pr349933 : Nat.Prime 349933 := by
  apply certPrime 349933 2 [2, 2, 3, 11, 11, 241] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr241, by decide⟩
private theorem pr360391 : Nat.Prime 360391 := by
  apply certPrime 360391 3 [2, 3, 5, 41, 293] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr41, by decide⟩
  · exact ⟨pr293, by decide⟩
private theorem pr360407 : Nat.Prime 360407 := by
  apply certPrime 360407 5 [2, 31, 5813] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr31, by decide⟩
  · exact ⟨pr5813, by decide⟩
private theorem pr360541 : Nat.Prime 360541 := by
  apply certPrime 360541 17 [2, 2, 3, 3, 5, 2003] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr2003, by decide⟩
private theorem pr386887 : Nat.Prime 386887 := by
  apply certPrime 386887 6 [2, 3, 17, 3793] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr17, by decide⟩
  · exact ⟨pr3793, by decide⟩
private theorem pr390407 : Nat.Prime 390407 := by
  apply certPrime 390407 5 [2, 195203] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr195203, by decide⟩
private theorem pr390413 : Nat.Prime 390413 := by
  apply certPrime 390413 2 [2, 2, 11, 19, 467] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr19, by decide⟩
  · exact ⟨pr467, by decide⟩
private theorem pr390419 : Nat.Prime 390419 := by
  apply certPrime 390419 2 [2, 7, 79, 353] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr79, by decide⟩
  · exact ⟨pr353, by decide⟩
private theorem pr390421 : Nat.Prime 390421 := by
  apply certPrime 390421 2 [2, 2, 3, 3, 3, 3, 5, 241] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr241, by decide⟩
private theorem pr390433 : Nat.Prime 390433 := by
  apply certPrime 390433 5 [2, 2, 2, 2, 2, 3, 7, 7, 83] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr83, by decide⟩
private theorem pr390437 : Nat.Prime 390437 := by
  apply certPrime 390437 2 [2, 2, 97609] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr97609, by decide⟩
private theorem pr420439 : Nat.Prime 420439 := by
  apply certPrime 420439 3 [2, 3, 79, 887] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr79, by decide⟩
  · exact ⟨pr887, by decide⟩
private theorem pr420457 : Nat.Prime 420457 := by
  apply certPrime 420457 5 [2, 2, 2, 3, 17519] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr17519, by decide⟩
private theorem pr420467 : Nat.Prime 420467 := by
  apply certPrime 420467 2 [2, 210233] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr210233, by decide⟩
private theorem pr434347 : Nat.Prime 434347 := by
  apply certPrime 434347 5 [2, 3, 11, 6581] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr6581, by decide⟩
private theorem pr450473 : Nat.Prime 450473 := by
  apply certPrime 450473 3 [2, 2, 2, 11, 5119] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr5119, by decide⟩
private theorem pr450479 : Nat.Prime 450479 := by
  apply certPrime 450479 7 [2, 7, 23, 1399] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr23, by decide⟩
  · exact ⟨pr1399, by decide⟩
private theorem pr450481 : Nat.Prime 450481 := by
  apply certPrime 450481 7 [2, 2, 2, 2, 3, 5, 1877] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr1877, by decide⟩
private theorem pr450487 : Nat.Prime 450487 := by
  apply certPrime 450487 5 [2, 3, 3, 29, 863] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr29, by decide⟩
  · exact ⟨pr863, by decide⟩
private theorem pr450493 : Nat.Prime 450493 := by
  apply certPrime 450493 14 [2, 2, 3, 7, 31, 173] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr31, by decide⟩
  · exact ⟨pr173, by decide⟩
private theorem pr450503 : Nat.Prime 450503 := by
  apply certPrime 450503 5 [2, 13, 17327] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr17327, by decide⟩
private theorem pr463157 : Nat.Prime 463157 := by
  apply certPrime 463157 2 [2, 2, 89, 1301] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr89, by decide⟩
  · exact ⟨pr1301, by decide⟩
private theorem pr480499 : Nat.Prime 480499 := by
  apply certPrime 480499 2 [2, 3, 53, 1511] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr53, by decide⟩
  · exact ⟨pr1511, by decide⟩
private theorem pr480503 : Nat.Prime 480503 := by
  apply certPrime 480503 5 [2, 11, 21841] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr21841, by decide⟩
private theorem pr480509 : Nat.Prime 480509 := by
  apply certPrime 480509 2 [2, 2, 7, 131, 131] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr131, by decide⟩
  · exact ⟨pr131, by decide⟩
private theorem pr480517 : Nat.Prime 480517 := by
  apply certPrime 480517 2 [2, 2, 3, 23, 1741] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr23, by decide⟩
  · exact ⟨pr1741, by decide⟩
private theorem pr480521 : Nat.Prime 480521 := by
  apply certPrime 480521 3 [2, 2, 2, 5, 41, 293] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr41, by decide⟩
  · exact ⟨pr293, by decide⟩
private theorem pr480527 : Nat.Prime 480527 := by
  apply certPrime 480527 5 [2, 240263] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr240263, by decide⟩
private theorem pr480533 : Nat.Prime 480533 := by
  apply certPrime 480533 2 [2, 2, 13, 9241] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr9241, by decide⟩
private theorem pr480661 : Nat.Prime 480661 := by
  apply certPrime 480661 2 [2, 2, 3, 5, 8011] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr8011, by decide⟩
private theorem pr508957 : Nat.Prime 508957 := by
  apply certPrime 508957 2 [2, 2, 3, 7, 73, 83] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr73, by decide⟩
  · exact ⟨pr83, by decide⟩
private theorem pr540559 : Nat.Prime 540559 := by
  apply certPrime 540559 3 [2, 3, 3, 59, 509] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr59, by decide⟩
  · exact ⟨pr509, by decide⟩
private theorem pr540577 : Nat.Prime 540577 := by
  apply certPrime 540577 10 [2, 2, 2, 2, 2, 3, 3, 1877] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr1877, by decide⟩
private theorem pr540587 : Nat.Prime 540587 := by
  apply certPrime 540587 2 [2, 89, 3037] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr89, by decide⟩
  · exact ⟨pr3037, by decide⟩
private theorem pr600623 : Nat.Prime 600623 := by
  apply certPrime 600623 5 [2, 11, 23, 1187] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr23, by decide⟩
  · exact ⟨pr1187, by decide⟩
private theorem pr618619 : Nat.Prime 618619 := by
  apply certPrime 618619 2 [2, 3, 7, 11, 13, 103] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr103, by decide⟩
private theorem pr660683 : Nat.Prime 660683 := by
  apply certPrime 660683 2 [2, 11, 59, 509] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr59, by decide⟩
  · exact ⟨pr509, by decide⟩
private theorem pr718901 : Nat.Prime 718901 := by
  apply certPrime 718901 2 [2, 2, 5, 5, 7, 13, 79] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr79, by decide⟩
private theorem pr750787 : Nat.Prime 750787 := by
  apply certPrime 750787 3 [2, 3, 125131] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr125131, by decide⟩
private theorem pr780823 : Nat.Prime 780823 := by
  apply certPrime 780823 5 [2, 3, 3, 7, 6197] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr6197, by decide⟩
private theorem pr810839 : Nat.Prime 810839 := by
  apply certPrime 810839 7 [2, 7, 57917] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr57917, by decide⟩
private theorem pr840863 : Nat.Prime 840863 := by
  apply certPrime 840863 7 [2, 11, 37, 1033] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr37, by decide⟩
  · exact ⟨pr1033, by decide⟩
private theorem pr1018123 : Nat.Prime 1018123 := by
  apply certPrime 1018123 2 [2, 3, 7, 7, 3463] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr3463, by decide⟩
private theorem pr1036613 : Nat.Prime 1036613 := by
  apply certPrime 1036613 2 [2, 2, 337, 769] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr337, by decide⟩
  · exact ⟨pr769, by decide⟩
private theorem pr1111793 : Nat.Prime 1111793 := by
  apply certPrime 1111793 3 [2, 2, 2, 2, 11, 6317] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr6317, by decide⟩
private theorem pr1139141 : Nat.Prime 1139141 := by
  apply certPrime 1139141 2 [2, 2, 5, 56957] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr56957, by decide⟩
private theorem pr1198247 : Nat.Prime 1198247 := by
  apply certPrime 1198247 5 [2, 7, 7, 12227] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr12227, by decide⟩
private theorem pr1531181 : Nat.Prime 1531181 := by
  apply certPrime 1531181 2 [2, 2, 5, 7, 10937] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr10937, by decide⟩
private theorem pr1671671 : Nat.Prime 1671671 := by
  apply certPrime 1671671 11 [2, 5, 7, 11, 13, 167] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr167, by decide⟩
private theorem pr1707331 : Nat.Prime 1707331 := by
  apply certPrime 1707331 10 [2, 3, 5, 56911] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr56911, by decide⟩
private theorem pr1773781 : Nat.Prime 1773781 := by
  apply certPrime 1773781 6 [2, 2, 3, 5, 17, 37, 47] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr17, by decide⟩
  · exact ⟨pr37, by decide⟩
  · exact ⟨pr47, by decide⟩
private theorem pr1814843 : Nat.Prime 1814843 := by
  apply certPrime 1814843 2 [2, 19, 163, 293] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr19, by decide⟩
  · exact ⟨pr163, by decide⟩
  · exact ⟨pr293, by decide⟩
private theorem pr2432471 : Nat.Prime 2432471 := by
  apply certPrime 2432471 13 [2, 5, 347, 701] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr347, by decide⟩
  · exact ⟨pr701, by decide⟩
private theorem pr2812811 : Nat.Prime 2812811 := by
  apply certPrime 2812811 18 [2, 5, 7, 11, 13, 281] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr281, by decide⟩
private theorem pr2838461 : Nat.Prime 2838461 := by
  apply certPrime 2838461 2 [2, 2, 5, 347, 409] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr347, by decide⟩
  · exact ⟨pr409, by decide⟩
private theorem pr3153191 : Nat.Prime 3153191 := by
  apply certPrime 3153191 13 [2, 5, 43, 7333] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr43, by decide⟩
  · exact ⟨pr7333, by decide⟩
private theorem pr3434773 : Nat.Prime 3434773 := by
  apply certPrime 3434773 2 [2, 2, 3, 11, 26021] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr26021, by decide⟩
private theorem pr3506339 : Nat.Prime 3506339 := by
  apply certPrime 3506339 2 [2, 11, 11, 14489] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr14489, by decide⟩
private theorem pr3610531 : Nat.Prime 3610531 := by
  apply certPrime 3610531 7 [2, 3, 3, 5, 7, 11, 521] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr521, by decide⟩
private theorem pr3845987 : Nat.Prime 3845987 := by
  apply certPrime 3845987 2 [2, 809, 2377] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr809, by decide⟩
  · exact ⟨pr2377, by decide⟩
private theorem pr6072817 : Nat.Prime 6072817 := by
  apply certPrime 6072817 5 [2, 2, 2, 2, 3, 126517] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr126517, by decide⟩
private theorem pr8398393 : Nat.Prime 8398393 := by
  apply certPrime 8398393 7 [2, 2, 2, 3, 349933] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr349933, by decide⟩
private theorem pr9917909 : Nat.Prime 9917909 := by
  apply certPrime 9917909 2 [2, 2, 7, 11, 13, 2477] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr2477, by decide⟩
private theorem pr10568417 : Nat.Prime 10568417 := by
  apply certPrime 10568417 3 [2, 2, 2, 2, 2, 223, 1481] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr223, by decide⟩
  · exact ⟨pr1481, by decide⟩
private theorem pr11600161 : Nat.Prime 11600161 := by
  apply certPrime 11600161 7 [2, 2, 2, 2, 2, 3, 5, 11, 13, 13, 13] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr13, by decide⟩
private theorem pr11831849 : Nat.Prime 11831849 := by
  apply certPrime 11831849 3 [2, 2, 2, 7, 211283] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr211283, by decide⟩
private theorem pr11861917 : Nat.Prime 11861917 := by
  apply certPrime 11861917 6 [2, 2, 3, 11, 73, 1231] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr73, by decide⟩
  · exact ⟨pr1231, by decide⟩
private theorem pr12042083 : Nat.Prime 12042083 := by
  apply certPrime 12042083 2 [2, 13, 463157] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr463157, by decide⟩
private theorem pr12537529 : Nat.Prime 12537529 := by
  apply certPrime 12537529 17 [2, 2, 2, 3, 313, 1669] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr313, by decide⟩
  · exact ⟨pr1669, by decide⟩
private theorem pr15037523 : Nat.Prime 15037523 := by
  apply certPrime 15037523 2 [2, 97, 77513] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr97, by decide⟩
  · exact ⟨pr77513, by decide⟩
private theorem pr15645671 : Nat.Prime 15645671 := by
  apply certPrime 15645671 13 [2, 5, 349, 4483] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr349, by decide⟩
  · exact ⟨pr4483, by decide⟩
private theorem pr16775459 : Nat.Prime 16775459 := by
  apply certPrime 16775459 2 [2, 7, 1198247] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr1198247, by decide⟩
private theorem pr18198247 : Nat.Prime 18198247 := by
  apply certPrime 18198247 3 [2, 3, 11, 103, 2677] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr103, by decide⟩
  · exact ⟨pr2677, by decide⟩
private theorem pr19036021 : Nat.Prime 19036021 := by
  apply certPrime 19036021 6 [2, 2, 3, 5, 317267] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr317267, by decide⟩
private theorem pr19219219 : Nat.Prime 19219219 := by
  apply certPrime 19219219 3 [2, 3, 67, 47809] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr67, by decide⟩
  · exact ⟨pr47809, by decide⟩
private theorem pr22354433 : Nat.Prime 22354433 := by
  apply certPrime 22354433 3 [2, 2, 2, 2, 2, 2, 2, 2, 2, 43661] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr43661, by decide⟩
private theorem pr23153149 : Nat.Prime 23153149 := by
  apply certPrime 23153149 2 [2, 2, 3, 3, 3, 214381] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr214381, by decide⟩
private theorem pr24744761 : Nat.Prime 24744761 := by
  apply certPrime 24744761 3 [2, 2, 2, 5, 618619] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr618619, by decide⟩
private theorem pr26906921 : Nat.Prime 26906921 := by
  apply certPrime 26906921 3 [2, 2, 2, 5, 17, 39569] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr17, by decide⟩
  · exact ⟨pr39569, by decide⟩
private theorem pr29519507 : Nat.Prime 29519507 := by
  apply certPrime 29519507 2 [2, 29, 508957] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr29, by decide⟩
  · exact ⟨pr508957, by decide⟩
private theorem pr29579581 : Nat.Prime 29579581 := by
  apply certPrime 29579581 2 [2, 2, 3, 3, 3, 3, 5, 19, 31, 31] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr19, by decide⟩
  · exact ⟨pr31, by decide⟩
  · exact ⟨pr31, by decide⟩
private theorem pr30075047 : Nat.Prime 30075047 := by
  apply certPrime 30075047 5 [2, 15037523] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr15037523, by decide⟩
private theorem pr31711717 : Nat.Prime 31711717 := by
  apply certPrime 31711717 2 [2, 2, 3, 3, 3, 479, 613] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr479, by decide⟩
  · exact ⟨pr613, by decide⟩
private theorem pr32953493 : Nat.Prime 32953493 := by
  apply certPrime 32953493 2 [2, 2, 11, 13, 53, 1087] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr53, by decide⟩
  · exact ⟨pr1087, by decide⟩
private theorem pr38018033 : Nat.Prime 38018033 := by
  apply certPrime 38018033 3 [2, 2, 2, 2, 13, 182779] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr182779, by decide⟩
private theorem pr39729733 : Nat.Prime 39729733 := by
  apply certPrime 39729733 2 [2, 2, 3, 7, 79, 5987] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr79, by decide⟩
  · exact ⟨pr5987, by decide⟩
private theorem pr47447467 : Nat.Prime 47447467 := by
  apply certPrime 47447467 2 [2, 3, 11, 718901] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr718901, by decide⟩
private theorem pr48918893 : Nat.Prime 48918893 := by
  apply certPrime 48918893 2 [2, 2, 11, 1111793] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr1111793, by decide⟩
private theorem pr50120137 : Nat.Prime 50120137 := by
  apply certPrime 50120137 15 [2, 2, 2, 3, 3, 11, 11, 11, 523] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr523, by decide⟩
private theorem pr50150117 : Nat.Prime 50150117 := by
  apply certPrime 50150117 2 [2, 2, 12537529] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr12537529, by decide⟩
private theorem pr50150131 : Nat.Prime 50150131 := by
  apply certPrime 50150131 2 [2, 3, 5, 1671671] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr1671671, by decide⟩
private theorem pr50390359 : Nat.Prime 50390359 := by
  apply certPrime 50390359 3 [2, 3, 8398393] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr8398393, by decide⟩
private theorem pr53783747 : Nat.Prime 53783747 := by
  apply certPrime 53783747 2 [2, 641, 41953] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr641, by decide⟩
  · exact ⟨pr41953, by decide⟩
private theorem pr53843819 : Nat.Prime 53843819 := by
  apply certPrime 53843819 2 [2, 7, 3845987] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr3845987, by decide⟩
private theorem pr58288273 : Nat.Prime 58288273 := by
  apply certPrime 58288273 10 [2, 2, 2, 2, 3, 7, 47, 3691] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr47, by decide⟩
  · exact ⟨pr3691, by decide⟩
private theorem pr63363319 : Nat.Prime 63363319 := by
  apply certPrime 63363319 6 [2, 3, 17, 29, 31, 691] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr17, by decide⟩
  · exact ⟨pr29, by decide⟩
  · exact ⟨pr31, by decide⟩
  · exact ⟨pr691, by decide⟩
private theorem pr64624597 : Nat.Prime 64624597 := by
  apply certPrime 64624597 2 [2, 2, 3, 53, 101611] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr53, by decide⟩
  · exact ⟨pr101611, by decide⟩
private theorem pr68348461 : Nat.Prime 68348461 := by
  apply certPrime 68348461 2 [2, 2, 3, 5, 1139141] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr1139141, by decide⟩
private theorem pr69459443 : Nat.Prime 69459443 := by
  apply certPrime 69459443 2 [2, 13, 71, 191, 197] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr71, by decide⟩
  · exact ⟨pr191, by decide⟩
  · exact ⟨pr197, by decide⟩
private theorem pr81951889 : Nat.Prime 81951889 := by
  apply certPrime 81951889 7 [2, 2, 2, 2, 3, 1707331] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr1707331, by decide⟩
private theorem pr107357279 : Nat.Prime 107357279 := by
  apply certPrime 107357279 7 [2, 7, 17, 31, 14551] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr17, by decide⟩
  · exact ⟨pr31, by decide⟩
  · exact ⟨pr14551, by decide⟩
private theorem pr107807753 : Nat.Prime 107807753 := by
  apply certPrime 107807753 3 [2, 2, 2, 13, 1036613] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr1036613, by decide⟩
private theorem pr112520267 : Nat.Prime 112520267 := by
  apply certPrime 112520267 2 [2, 31, 1814843] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr31, by decide⟩
  · exact ⟨pr1814843, by decide⟩
private theorem pr118138063 : Nat.Prime 118138063 := by
  apply certPrime 118138063 6 [2, 3, 7, 2812811] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr2812811, by decide⟩
private theorem pr120510413 : Nat.Prime 120510413 := by
  apply certPrime 120510413 2 [2, 2, 11, 103, 26591] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr103, by decide⟩
  · exact ⟨pr26591, by decide⟩
private theorem pr131681567 : Nat.Prime 131681567 := by
  apply certPrime 131681567 5 [2, 43, 1531181] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr43, by decide⟩
  · exact ⟨pr1531181, by decide⟩
private theorem pr136246129 : Nat.Prime 136246129 := by
  apply certPrime 136246129 14 [2, 2, 2, 2, 3, 2838461] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr2838461, by decide⟩
private theorem pr139279321 : Nat.Prime 139279321 := by
  apply certPrime 139279321 7 [2, 2, 2, 3, 3, 5, 386887] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr386887, by decide⟩
private theorem pr147957839 : Nat.Prime 147957839 := by
  apply certPrime 147957839 7 [2, 7, 10568417] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr10568417, by decide⟩
private theorem pr151711607 : Nat.Prime 151711607 := by
  apply certPrime 151711607 5 [2, 1657, 45779] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr1657, by decide⟩
  · exact ⟨pr45779, by decide⟩
private theorem pr187747613 : Nat.Prime 187747613 := by
  apply certPrime 187747613 2 [2, 2, 13, 3610531] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr3610531, by decide⟩
private theorem pr190360211 : Nat.Prime 190360211 := by
  apply certPrime 190360211 2 [2, 5, 19036021] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr19036021, by decide⟩
private theorem pr198663473 : Nat.Prime 198663473 := by
  apply certPrime 198663473 3 [2, 2, 2, 2, 7, 1773781] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr1773781, by decide⟩
private theorem pr210650443 : Nat.Prime 210650443 := by
  apply certPrime 210650443 2 [2, 3, 163, 215389] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr163, by decide⟩
  · exact ⟨pr215389, by decide⟩
private theorem pr214264087 : Nat.Prime 214264087 := by
  apply certPrime 214264087 5 [2, 3, 61, 149, 3929] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr61, by decide⟩
  · exact ⟨pr149, by decide⟩
  · exact ⟨pr3929, by decide⟩
private theorem pr216576541 : Nat.Prime 216576541 := by
  apply certPrime 216576541 2 [2, 2, 3, 3, 5, 31, 37, 1049] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr31, by decide⟩
  · exact ⟨pr37, by decide⟩
  · exact ⟨pr1049, by decide⟩
private theorem pr221106887 : Nat.Prime 221106887 := by
  apply certPrime 221106887 5 [2, 7, 11, 13, 179, 617] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr179, by decide⟩
  · exact ⟨pr617, by decide⟩
private theorem pr227153357 : Nat.Prime 227153357 := by
  apply certPrime 227153357 2 [2, 2, 463, 122653] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr463, by decide⟩
  · exact ⟨pr122653, by decide⟩
private theorem pr252372143 : Nat.Prime 252372143 := by
  apply certPrime 252372143 5 [2, 11, 2719, 4219] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr2719, by decide⟩
  · exact ⟨pr4219, by decide⟩
private theorem pr258228037 : Nat.Prime 258228037 := by
  apply certPrime 258228037 2 [2, 2, 3, 3, 11, 11, 59281] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr59281, by decide⟩
private theorem pr267417203 : Nat.Prime 267417203 := by
  apply certPrime 267417203 2 [2, 13, 83, 83, 1493] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr83, by decide⟩
  · exact ⟨pr83, by decide⟩
  · exact ⟨pr1493, by decide⟩
private theorem pr281651387 : Nat.Prime 281651387 := by
  apply certPrime 281651387 2 [2, 41, 3434773] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr41, by decide⟩
  · exact ⟨pr3434773, by decide⟩
private theorem pr297537271 : Nat.Prime 297537271 := by
  apply certPrime 297537271 6 [2, 3, 5, 9917909] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr9917909, by decide⟩
private theorem pr298318063 : Nat.Prime 298318063 := by
  apply certPrime 298318063 3 [2, 3, 7, 79, 89909] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr79, by decide⟩
  · exact ⟨pr89909, by decide⟩
private theorem pr299699431 : Nat.Prime 299699431 := by
  apply certPrime 299699431 6 [2, 3, 5, 23, 434347] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr23, by decide⟩
  · exact ⟨pr434347, by decide⟩
private theorem pr324804509 : Nat.Prime 324804509 := by
  apply certPrime 324804509 2 [2, 2, 7, 11600161] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr11600161, by decide⟩
private theorem pr349579297 : Nat.Prime 349579297 := by
  apply certPrime 349579297 10 [2, 2, 2, 2, 2, 3, 3, 11, 17, 6491] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr17, by decide⟩
  · exact ⟨pr6491, by decide⟩
private theorem pr397326947 : Nat.Prime 397326947 := by
  apply certPrime 397326947 2 [2, 198663473] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr198663473, by decide⟩
private theorem pr424864463 : Nat.Prime 424864463 := by
  apply certPrime 424864463 5 [2, 11, 89, 97, 2237] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr89, by decide⟩
  · exact ⟨pr97, by decide⟩
  · exact ⟨pr2237, by decide⟩
private theorem pr433242853 : Nat.Prime 433242853 := by
  apply certPrime 433242853 5 [2, 2, 3, 7, 71, 72643] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr71, by decide⟩
  · exact ⟨pr72643, by decide⟩
private theorem pr448588207 : Nat.Prime 448588207 := by
  apply certPrime 448588207 3 [2, 3, 3, 3, 3, 3, 11, 83911] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr83911, by decide⟩
private theorem pr457747471 : Nat.Prime 457747471 := by
  apply certPrime 457747471 3 [2, 3, 3, 3, 5, 43, 89, 443] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr43, by decide⟩
  · exact ⟨pr89, by decide⟩
  · exact ⟨pr443, by decide⟩
private theorem pr469849427 : Nat.Prime 469849427 := by
  apply certPrime 469849427 2 [2, 67, 3506339] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr67, by decide⟩
  · exact ⟨pr3506339, by decide⟩
private theorem pr494504047 : Nat.Prime 494504047 := by
  apply certPrime 494504047 5 [2, 3, 3, 113, 243119] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr113, by decide⟩
  · exact ⟨pr243119, by decide⟩
private theorem pr601500941 : Nat.Prime 601500941 := by
  apply certPrime 601500941 2 [2, 2, 5, 30075047] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr30075047, by decide⟩
private theorem pr631951367 : Nat.Prime 631951367 := by
  apply certPrime 631951367 5 [2, 1319, 239557] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr1319, by decide⟩
  · exact ⟨pr239557, by decide⟩
private theorem pr751771061 : Nat.Prime 751771061 := by
  apply certPrime 751771061 2 [2, 2, 5, 29, 137, 9461] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr29, by decide⟩
  · exact ⟨pr137, by decide⟩
  · exact ⟨pr9461, by decide⟩
private theorem pr761620877 : Nat.Prime 761620877 := by
  apply certPrime 761620877 2 [2, 2, 17, 37, 302711] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr17, by decide⟩
  · exact ⟨pr37, by decide⟩
  · exact ⟨pr302711, by decide⟩
private theorem pr891741031 : Nat.Prime 891741031 := by
  apply certPrime 891741031 3 [2, 3, 5, 3049, 9749] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr3049, by decide⟩
  · exact ⟨pr9749, by decide⟩
private theorem pr954503603 : Nat.Prime 954503603 := by
  apply certPrime 954503603 5 [2, 13, 229, 160313] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr229, by decide⟩
  · exact ⟨pr160313, by decide⟩
private theorem pr964954009 : Nat.Prime 964954009 := by
  apply certPrime 964954009 7 [2, 2, 2, 3, 3, 113, 118603] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr113, by decide⟩
  · exact ⟨pr118603, by decide⟩
private theorem pr971650721 : Nat.Prime 971650721 := by
  apply certPrime 971650721 3 [2, 2, 2, 2, 2, 5, 6072817] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr6072817, by decide⟩
private theorem pr1263902659 : Nat.Prime 1263902659 := by
  apply certPrime 1263902659 2 [2, 3, 210650443] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr210650443, by decide⟩
private theorem pr1431349957 : Nat.Prime 1431349957 := by
  apply certPrime 1431349957 14 [2, 2, 3, 3, 937, 42433] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr937, by decide⟩
  · exact ⟨pr42433, by decide⟩
private theorem pr1575283739 : Nat.Prime 1575283739 := by
  apply certPrime 1575283739 2 [2, 7, 112520267] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr112520267, by decide⟩
private theorem pr1900989133 : Nat.Prime 1900989133 := by
  apply certPrime 1900989133 2 [2, 2, 3, 7, 151, 149873] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr151, by decide⟩
  · exact ⟨pr149873, by decide⟩
private theorem pr2379246893 : Nat.Prime 2379246893 := by
  apply certPrime 2379246893 2 [2, 2, 11, 41, 683, 1931] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr41, by decide⟩
  · exact ⟨pr683, by decide⟩
  · exact ⟨pr1931, by decide⟩
private theorem pr2532790297 : Nat.Prime 2532790297 := by
  apply certPrime 2532790297 5 [2, 2, 2, 3, 3, 3, 3, 379, 10313] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr379, by decide⟩
  · exact ⟨pr10313, by decide⟩
private theorem pr2596213651 : Nat.Prime 2596213651 := by
  apply certPrime 2596213651 10 [2, 3, 5, 5, 17, 1018123] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr17, by decide⟩
  · exact ⟨pr1018123, by decide⟩
private theorem pr3180146999 : Nat.Prime 3180146999 := by
  apply certPrime 3180146999 7 [2, 7, 227153357] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr227153357, by decide⟩
private theorem pr3404831497 : Nat.Prime 3404831497 := by
  apply certPrime 3404831497 5 [2, 2, 2, 3, 11, 23, 683, 821] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr11, by decide⟩
  · exact ⟨pr23, by decide⟩
  · exact ⟨pr683, by decide⟩
  · exact ⟨pr821, by decide⟩
private theorem pr4770415691 : Nat.Prime 4770415691 := by
  apply certPrime 4770415691 2 [2, 5, 19, 997, 25183] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr19, by decide⟩
  · exact ⟨pr997, by decide⟩
  · exact ⟨pr25183, by decide⟩
private theorem pr6633206611 : Nat.Prime 6633206611 := by
  apply certPrime 6633206611 2 [2, 3, 5, 221106887] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr221106887, by decide⟩
private theorem pr10065275401 : Nat.Prime 10065275401 := by
  apply certPrime 10065275401 7 [2, 2, 2, 3, 5, 5, 16775459] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr5, by decide⟩
  · exact ⟨pr16775459, by decide⟩
private theorem pr10940559677 : Nat.Prime 10940559677 := by
  apply certPrime 10940559677 2 [2, 2, 83, 32953493] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr83, by decide⟩
  · exact ⟨pr32953493, by decide⟩
private theorem pr15961065163 : Nat.Prime 15961065163 := by
  apply certPrime 15961065163 5 [2, 3, 7, 17, 22354433] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr3, by decide⟩
  · exact ⟨pr7, by decide⟩
  · exact ⟨pr17, by decide⟩
  · exact ⟨pr22354433, by decide⟩
private theorem pr19495926503 : Nat.Prime 19495926503 := by
  apply certPrime 19495926503 5 [2, 13, 17, 2029, 21739] (by decide) (by decide)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨pr2, by decide⟩
  · exact ⟨pr13, by decide⟩
  · exact ⟨pr17, by decide⟩
  · exact ⟨pr2029, by decide⟩
  · exact ⟨pr21739, by decide⟩

private def row0 : Finset ℕ := {17,30047,60077,90107,240257,270287,300317,330347,390407,29519507,50150117,53783747,131681567,281651387,397326947,761620877}

private theorem rowCert0 : (row0).card=16 ∧
    (∀ p ∈ row0, Nat.Prime p ∧ p≤19495926503 ∧ p % 30030 = 17) ∧
    (∀ r ∈ ({17,19,23,29,31,37,41,43,47,53,59,61,67,71,73} : Finset ℕ), Set.InjOn (fun p : ℕ => p % r) (row0 : Set ℕ)) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro p hp
    simp only [row0, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pr17, by decide, by decide⟩
    · exact ⟨pr30047, by decide, by decide⟩
    · exact ⟨pr60077, by decide, by decide⟩
    · exact ⟨pr90107, by decide, by decide⟩
    · exact ⟨pr240257, by decide, by decide⟩
    · exact ⟨pr270287, by decide, by decide⟩
    · exact ⟨pr300317, by decide, by decide⟩
    · exact ⟨pr330347, by decide, by decide⟩
    · exact ⟨pr390407, by decide, by decide⟩
    · exact ⟨pr29519507, by decide, by decide⟩
    · exact ⟨pr50150117, by decide, by decide⟩
    · exact ⟨pr53783747, by decide, by decide⟩
    · exact ⟨pr131681567, by decide, by decide⟩
    · exact ⟨pr281651387, by decide, by decide⟩
    · exact ⟨pr397326947, by decide, by decide⟩
    · exact ⟨pr761620877, by decide, by decide⟩
  · have h : ∀ r ∈ ({17,19,23,29,31,37,41,43,47,53,59,61,67,71,73} : Finset ℕ), ∀ x ∈ row0, ∀ y ∈ row0, x % r = y % r → x=y := by decide
    exact fun r hr x hx y hy hxy => h r hr x hx y hy hxy

private def row1 : Finset ℕ := {19,150169,210229,240259,300319,420439,480499,540559,19219219,23153149,50390359,63363319,81951889,136246129,964954009,1263902659}

private theorem rowCert1 : (row1).card=16 ∧
    (∀ p ∈ row1, Nat.Prime p ∧ p≤19495926503 ∧ p % 30030 = 19) ∧
    (∀ r ∈ ({17,19,23,29,31,37,41,43,47,53,59,61,67,71,73} : Finset ℕ), Set.InjOn (fun p : ℕ => p % r) (row1 : Set ℕ)) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro p hp
    simp only [row1, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pr19, by decide, by decide⟩
    · exact ⟨pr150169, by decide, by decide⟩
    · exact ⟨pr210229, by decide, by decide⟩
    · exact ⟨pr240259, by decide, by decide⟩
    · exact ⟨pr300319, by decide, by decide⟩
    · exact ⟨pr420439, by decide, by decide⟩
    · exact ⟨pr480499, by decide, by decide⟩
    · exact ⟨pr540559, by decide, by decide⟩
    · exact ⟨pr19219219, by decide, by decide⟩
    · exact ⟨pr23153149, by decide, by decide⟩
    · exact ⟨pr50390359, by decide, by decide⟩
    · exact ⟨pr63363319, by decide, by decide⟩
    · exact ⟨pr81951889, by decide, by decide⟩
    · exact ⟨pr136246129, by decide, by decide⟩
    · exact ⟨pr964954009, by decide, by decide⟩
    · exact ⟨pr1263902659, by decide, by decide⟩
  · have h : ∀ r ∈ ({17,19,23,29,31,37,41,43,47,53,59,61,67,71,73} : Finset ℕ), ∀ x ∈ row1, ∀ y ∈ row1, x % r = y % r → x=y := by decide
    exact fun r hr x hx y hy hxy => h r hr x hx y hy hxy

private def row2 : Finset ℕ := {23,60083,210233,240263,300323,390413,450473,480503,600623,660683,840863,48918893,120510413,252372143,424864463,2379246893}

private theorem rowCert2 : (row2).card=16 ∧
    (∀ p ∈ row2, Nat.Prime p ∧ p≤19495926503 ∧ p % 30030 = 23) ∧
    (∀ r ∈ ({17,19,23,29,31,37,41,43,47,53,59,61,67,71,73} : Finset ℕ), Set.InjOn (fun p : ℕ => p % r) (row2 : Set ℕ)) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro p hp
    simp only [row2, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pr23, by decide, by decide⟩
    · exact ⟨pr60083, by decide, by decide⟩
    · exact ⟨pr210233, by decide, by decide⟩
    · exact ⟨pr240263, by decide, by decide⟩
    · exact ⟨pr300323, by decide, by decide⟩
    · exact ⟨pr390413, by decide, by decide⟩
    · exact ⟨pr450473, by decide, by decide⟩
    · exact ⟨pr480503, by decide, by decide⟩
    · exact ⟨pr600623, by decide, by decide⟩
    · exact ⟨pr660683, by decide, by decide⟩
    · exact ⟨pr840863, by decide, by decide⟩
    · exact ⟨pr48918893, by decide, by decide⟩
    · exact ⟨pr120510413, by decide, by decide⟩
    · exact ⟨pr252372143, by decide, by decide⟩
    · exact ⟨pr424864463, by decide, by decide⟩
    · exact ⟨pr2379246893, by decide, by decide⟩
  · have h : ∀ r ∈ ({17,19,23,29,31,37,41,43,47,53,59,61,67,71,73} : Finset ℕ), ∀ x ∈ row2, ∀ y ∈ row2, x % r = y % r → x=y := by decide
    exact fun r hr x hx y hy hxy => h r hr x hx y hy hxy

private def row3 : Finset ℕ := {181,30211,90271,180361,210391,240421,270451,300481,360541,480661,68348461,139279321,216576541,457747471,891741031,10065275401}

private theorem rowCert3 : (row3).card=16 ∧
    (∀ p ∈ row3, Nat.Prime p ∧ p≤19495926503 ∧ p % 30030 = 181) ∧
    (∀ r ∈ ({17,19,23,29,31,37,41,43,47,53,59,61,67,71,73} : Finset ℕ), Set.InjOn (fun p : ℕ => p % r) (row3 : Set ℕ)) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro p hp
    simp only [row3, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pr181, by decide, by decide⟩
    · exact ⟨pr30211, by decide, by decide⟩
    · exact ⟨pr90271, by decide, by decide⟩
    · exact ⟨pr180361, by decide, by decide⟩
    · exact ⟨pr210391, by decide, by decide⟩
    · exact ⟨pr240421, by decide, by decide⟩
    · exact ⟨pr270451, by decide, by decide⟩
    · exact ⟨pr300481, by decide, by decide⟩
    · exact ⟨pr360541, by decide, by decide⟩
    · exact ⟨pr480661, by decide, by decide⟩
    · exact ⟨pr68348461, by decide, by decide⟩
    · exact ⟨pr139279321, by decide, by decide⟩
    · exact ⟨pr216576541, by decide, by decide⟩
    · exact ⟨pr457747471, by decide, by decide⟩
    · exact ⟨pr891741031, by decide, by decide⟩
    · exact ⟨pr10065275401, by decide, by decide⟩
  · have h : ∀ r ∈ ({17,19,23,29,31,37,41,43,47,53,59,61,67,71,73} : Finset ℕ), ∀ x ∈ row3, ∀ y ∈ row3, x % r = y % r → x=y := by decide
    exact fun r hr x hx y hy hxy => h r hr x hx y hy hxy

private def row4 : Finset ℕ := {29,30059,60089,270299,330359,390419,450479,480509,810839,11831849,53843819,107357279,147957839,324804509,1575283739,3180146999}

private theorem rowCert4 : (row4).card=16 ∧
    (∀ p ∈ row4, Nat.Prime p ∧ p≤19495926503 ∧ p % 30030 = 29) ∧
    (∀ r ∈ ({17,19,23,29,31,37,41,43,47,53,59,61,67,71,73} : Finset ℕ), Set.InjOn (fun p : ℕ => p % r) (row4 : Set ℕ)) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro p hp
    simp only [row4, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pr29, by decide, by decide⟩
    · exact ⟨pr30059, by decide, by decide⟩
    · exact ⟨pr60089, by decide, by decide⟩
    · exact ⟨pr270299, by decide, by decide⟩
    · exact ⟨pr330359, by decide, by decide⟩
    · exact ⟨pr390419, by decide, by decide⟩
    · exact ⟨pr450479, by decide, by decide⟩
    · exact ⟨pr480509, by decide, by decide⟩
    · exact ⟨pr810839, by decide, by decide⟩
    · exact ⟨pr11831849, by decide, by decide⟩
    · exact ⟨pr53843819, by decide, by decide⟩
    · exact ⟨pr107357279, by decide, by decide⟩
    · exact ⟨pr147957839, by decide, by decide⟩
    · exact ⟨pr324804509, by decide, by decide⟩
    · exact ⟨pr1575283739, by decide, by decide⟩
    · exact ⟨pr3180146999, by decide, by decide⟩
  · have h : ∀ r ∈ ({17,19,23,29,31,37,41,43,47,53,59,61,67,71,73} : Finset ℕ), ∀ x ∈ row4, ∀ y ∈ row4, x % r = y % r → x=y := by decide
    exact fun r hr x hx y hy hxy => h r hr x hx y hy hxy

private def row5 : Finset ℕ := {37,90127,120157,210247,270307,420457,450487,480517,540577,750787,31711717,64624597,214264087,494504047,1431349957,2532790297}

private theorem rowCert5 : (row5).card=16 ∧
    (∀ p ∈ row5, Nat.Prime p ∧ p≤19495926503 ∧ p % 30030 = 37) ∧
    (∀ r ∈ ({17,19,23,29,31,37,41,43,47,53,59,61,67,71,73} : Finset ℕ), Set.InjOn (fun p : ℕ => p % r) (row5 : Set ℕ)) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro p hp
    simp only [row5, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pr37, by decide, by decide⟩
    · exact ⟨pr90127, by decide, by decide⟩
    · exact ⟨pr120157, by decide, by decide⟩
    · exact ⟨pr210247, by decide, by decide⟩
    · exact ⟨pr270307, by decide, by decide⟩
    · exact ⟨pr420457, by decide, by decide⟩
    · exact ⟨pr450487, by decide, by decide⟩
    · exact ⟨pr480517, by decide, by decide⟩
    · exact ⟨pr540577, by decide, by decide⟩
    · exact ⟨pr750787, by decide, by decide⟩
    · exact ⟨pr31711717, by decide, by decide⟩
    · exact ⟨pr64624597, by decide, by decide⟩
    · exact ⟨pr214264087, by decide, by decide⟩
    · exact ⟨pr494504047, by decide, by decide⟩
    · exact ⟨pr1431349957, by decide, by decide⟩
    · exact ⟨pr2532790297, by decide, by decide⟩
  · have h : ∀ r ∈ ({17,19,23,29,31,37,41,43,47,53,59,61,67,71,73} : Finset ℕ), ∀ x ∈ row5, ∀ y ∈ row5, x % r = y % r → x=y := by decide
    exact fun r hr x hx y hy hxy => h r hr x hx y hy hxy

private def row6 : Finset ℕ := {41,30071,60101,180221,270311,480521,2432471,3153191,15645671,24744761,26906921,190360211,601500941,751771061,971650721,4770415691}

private theorem rowCert6 : (row6).card=16 ∧
    (∀ p ∈ row6, Nat.Prime p ∧ p≤19495926503 ∧ p % 30030 = 41) ∧
    (∀ r ∈ ({17,19,23,29,31,37,41,43,47,53,59,61,67,71,73} : Finset ℕ), Set.InjOn (fun p : ℕ => p % r) (row6 : Set ℕ)) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro p hp
    simp only [row6, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pr41, by decide, by decide⟩
    · exact ⟨pr30071, by decide, by decide⟩
    · exact ⟨pr60101, by decide, by decide⟩
    · exact ⟨pr180221, by decide, by decide⟩
    · exact ⟨pr270311, by decide, by decide⟩
    · exact ⟨pr480521, by decide, by decide⟩
    · exact ⟨pr2432471, by decide, by decide⟩
    · exact ⟨pr3153191, by decide, by decide⟩
    · exact ⟨pr15645671, by decide, by decide⟩
    · exact ⟨pr24744761, by decide, by decide⟩
    · exact ⟨pr26906921, by decide, by decide⟩
    · exact ⟨pr190360211, by decide, by decide⟩
    · exact ⟨pr601500941, by decide, by decide⟩
    · exact ⟨pr751771061, by decide, by decide⟩
    · exact ⟨pr971650721, by decide, by decide⟩
    · exact ⟨pr4770415691, by decide, by decide⟩
  · have h : ∀ r ∈ ({17,19,23,29,31,37,41,43,47,53,59,61,67,71,73} : Finset ℕ), ∀ x ∈ row6, ∀ y ∈ row6, x % r = y % r → x=y := by decide
    exact fun r hr x hx y hy hxy => h r hr x hx y hy hxy

private def row7 : Finset ℕ := {43,60103,120163,150193,240283,300343,390433,450493,780823,39729733,58288273,118138063,298318063,433242853,1900989133,15961065163}

private theorem rowCert7 : (row7).card=16 ∧
    (∀ p ∈ row7, Nat.Prime p ∧ p≤19495926503 ∧ p % 30030 = 43) ∧
    (∀ r ∈ ({17,19,23,29,31,37,41,43,47,53,59,61,67,71,73} : Finset ℕ), Set.InjOn (fun p : ℕ => p % r) (row7 : Set ℕ)) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro p hp
    simp only [row7, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pr43, by decide, by decide⟩
    · exact ⟨pr60103, by decide, by decide⟩
    · exact ⟨pr120163, by decide, by decide⟩
    · exact ⟨pr150193, by decide, by decide⟩
    · exact ⟨pr240283, by decide, by decide⟩
    · exact ⟨pr300343, by decide, by decide⟩
    · exact ⟨pr390433, by decide, by decide⟩
    · exact ⟨pr450493, by decide, by decide⟩
    · exact ⟨pr780823, by decide, by decide⟩
    · exact ⟨pr39729733, by decide, by decide⟩
    · exact ⟨pr58288273, by decide, by decide⟩
    · exact ⟨pr118138063, by decide, by decide⟩
    · exact ⟨pr298318063, by decide, by decide⟩
    · exact ⟨pr433242853, by decide, by decide⟩
    · exact ⟨pr1900989133, by decide, by decide⟩
    · exact ⟨pr15961065163, by decide, by decide⟩
  · have h : ∀ r ∈ ({17,19,23,29,31,37,41,43,47,53,59,61,67,71,73} : Finset ℕ), ∀ x ∈ row7, ∀ y ∈ row7, x % r = y % r → x=y := by decide
    exact fun r hr x hx y hy hxy => h r hr x hx y hy hxy

private def row8 : Finset ℕ := {31,60091,90121,180211,210241,240271,300331,360391,390421,450481,29579581,50150131,297537271,299699431,2596213651,6633206611}

private theorem rowCert8 : (row8).card=16 ∧
    (∀ p ∈ row8, Nat.Prime p ∧ p≤19495926503 ∧ p % 30030 = 31) ∧
    (∀ r ∈ ({17,19,23,29,31,37,41,43,47,53,59,61,67,71,73} : Finset ℕ), Set.InjOn (fun p : ℕ => p % r) (row8 : Set ℕ)) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro p hp
    simp only [row8, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pr31, by decide, by decide⟩
    · exact ⟨pr60091, by decide, by decide⟩
    · exact ⟨pr90121, by decide, by decide⟩
    · exact ⟨pr180211, by decide, by decide⟩
    · exact ⟨pr210241, by decide, by decide⟩
    · exact ⟨pr240271, by decide, by decide⟩
    · exact ⟨pr300331, by decide, by decide⟩
    · exact ⟨pr360391, by decide, by decide⟩
    · exact ⟨pr390421, by decide, by decide⟩
    · exact ⟨pr450481, by decide, by decide⟩
    · exact ⟨pr29579581, by decide, by decide⟩
    · exact ⟨pr50150131, by decide, by decide⟩
    · exact ⟨pr297537271, by decide, by decide⟩
    · exact ⟨pr299699431, by decide, by decide⟩
    · exact ⟨pr2596213651, by decide, by decide⟩
    · exact ⟨pr6633206611, by decide, by decide⟩
  · have h : ∀ r ∈ ({17,19,23,29,31,37,41,43,47,53,59,61,67,71,73} : Finset ℕ), ∀ x ∈ row8, ∀ y ∈ row8, x % r = y % r → x=y := by decide
    exact fun r hr x hx y hy hxy => h r hr x hx y hy hxy

private def row9 : Finset ℕ := {47,60107,120167,150197,210257,240287,300347,360407,390437,420467,480527,540587,151711607,469849427,631951367,10940559677}

private theorem rowCert9 : (row9).card=16 ∧
    (∀ p ∈ row9, Nat.Prime p ∧ p≤19495926503 ∧ p % 30030 = 47) ∧
    (∀ r ∈ ({17,19,23,29,31,37,41,43,47,53,59,61,67,71,73} : Finset ℕ), Set.InjOn (fun p : ℕ => p % r) (row9 : Set ℕ)) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro p hp
    simp only [row9, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pr47, by decide, by decide⟩
    · exact ⟨pr60107, by decide, by decide⟩
    · exact ⟨pr120167, by decide, by decide⟩
    · exact ⟨pr150197, by decide, by decide⟩
    · exact ⟨pr210257, by decide, by decide⟩
    · exact ⟨pr240287, by decide, by decide⟩
    · exact ⟨pr300347, by decide, by decide⟩
    · exact ⟨pr360407, by decide, by decide⟩
    · exact ⟨pr390437, by decide, by decide⟩
    · exact ⟨pr420467, by decide, by decide⟩
    · exact ⟨pr480527, by decide, by decide⟩
    · exact ⟨pr540587, by decide, by decide⟩
    · exact ⟨pr151711607, by decide, by decide⟩
    · exact ⟨pr469849427, by decide, by decide⟩
    · exact ⟨pr631951367, by decide, by decide⟩
    · exact ⟨pr10940559677, by decide, by decide⟩
  · have h : ∀ r ∈ ({17,19,23,29,31,37,41,43,47,53,59,61,67,71,73} : Finset ℕ), ∀ x ∈ row9, ∀ y ∈ row9, x % r = y % r → x=y := by decide
    exact fun r hr x hx y hy hxy => h r hr x hx y hy hxy

private def row10 : Finset ℕ := {53,150203,180233,210263,270323,330383,450503,480533,12042083,38018033,69459443,107807753,187747613,267417203,954503603,19495926503}

private theorem rowCert10 : (row10).card=16 ∧
    (∀ p ∈ row10, Nat.Prime p ∧ p≤19495926503 ∧ p % 30030 = 53) ∧
    (∀ r ∈ ({17,19,23,29,31,37,41,43,47,53,59,61,67,71,73} : Finset ℕ), Set.InjOn (fun p : ℕ => p % r) (row10 : Set ℕ)) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro p hp
    simp only [row10, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pr53, by decide, by decide⟩
    · exact ⟨pr150203, by decide, by decide⟩
    · exact ⟨pr180233, by decide, by decide⟩
    · exact ⟨pr210263, by decide, by decide⟩
    · exact ⟨pr270323, by decide, by decide⟩
    · exact ⟨pr330383, by decide, by decide⟩
    · exact ⟨pr450503, by decide, by decide⟩
    · exact ⟨pr480533, by decide, by decide⟩
    · exact ⟨pr12042083, by decide, by decide⟩
    · exact ⟨pr38018033, by decide, by decide⟩
    · exact ⟨pr69459443, by decide, by decide⟩
    · exact ⟨pr107807753, by decide, by decide⟩
    · exact ⟨pr187747613, by decide, by decide⟩
    · exact ⟨pr267417203, by decide, by decide⟩
    · exact ⟨pr954503603, by decide, by decide⟩
    · exact ⟨pr19495926503, by decide, by decide⟩
  · have h : ∀ r ∈ ({17,19,23,29,31,37,41,43,47,53,59,61,67,71,73} : Finset ℕ), ∀ x ∈ row10, ∀ y ∈ row10, x % r = y % r → x=y := by decide
    exact fun r hr x hx y hy hxy => h r hr x hx y hy hxy

private def row11 : Finset ℕ := {67,30097,60127,150217,180247,210277,270337,300367,11861917,18198247,47447467,50120137,258228037,349579297,448588207,3404831497}

private theorem rowCert11 : (row11).card=16 ∧
    (∀ p ∈ row11, Nat.Prime p ∧ p≤19495926503 ∧ p % 30030 = 67) ∧
    (∀ r ∈ ({17,19,23,29,31,37,41,43,47,53,59,61,67,71,73} : Finset ℕ), Set.InjOn (fun p : ℕ => p % r) (row11 : Set ℕ)) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro p hp
    simp only [row11, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pr67, by decide, by decide⟩
    · exact ⟨pr30097, by decide, by decide⟩
    · exact ⟨pr60127, by decide, by decide⟩
    · exact ⟨pr150217, by decide, by decide⟩
    · exact ⟨pr180247, by decide, by decide⟩
    · exact ⟨pr210277, by decide, by decide⟩
    · exact ⟨pr270337, by decide, by decide⟩
    · exact ⟨pr300367, by decide, by decide⟩
    · exact ⟨pr11861917, by decide, by decide⟩
    · exact ⟨pr18198247, by decide, by decide⟩
    · exact ⟨pr47447467, by decide, by decide⟩
    · exact ⟨pr50120137, by decide, by decide⟩
    · exact ⟨pr258228037, by decide, by decide⟩
    · exact ⟨pr349579297, by decide, by decide⟩
    · exact ⟨pr448588207, by decide, by decide⟩
    · exact ⟨pr3404831497, by decide, by decide⟩
  · have h : ∀ r ∈ ({17,19,23,29,31,37,41,43,47,53,59,61,67,71,73} : Finset ℕ), ∀ x ∈ row11, ∀ y ∈ row11, x % r = y % r → x=y := by decide
    exact fun r hr x hx y hy hxy => h r hr x hx y hy hxy

theorem Conjectures.Goldbach.FiniteWheelSixteenPrimeLifts :
    let P : Finset ℕ := {17,19,23,29,31,37,41,43,47,53,59,61,67,71,73}; ∀ b ∈ ({17,19,23,181,29,37,41,43,31,47,53,67} : Finset ℕ), ∃ S : Finset ℕ, S.card=16 ∧ (∀ p ∈ S, Nat.Prime p ∧ p≤19495926503 ∧ p % 30030=b) ∧ (∀ r ∈ P, Set.InjOn (fun p : ℕ => p % r) (S : Set ℕ)) := by
  intro P b hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨row0, rowCert0⟩
  · exact ⟨row1, rowCert1⟩
  · exact ⟨row2, rowCert2⟩
  · exact ⟨row3, rowCert3⟩
  · exact ⟨row4, rowCert4⟩
  · exact ⟨row5, rowCert5⟩
  · exact ⟨row6, rowCert6⟩
  · exact ⟨row7, rowCert7⟩
  · exact ⟨row8, rowCert8⟩
  · exact ⟨row9, rowCert9⟩
  · exact ⟨row10, rowCert10⟩
  · exact ⟨row11, rowCert11⟩
