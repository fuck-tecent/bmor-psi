import Mathlib

namespace Conjectures.Cuts

private def trialProduct : ℕ := 4014476939333036189094441199026045136645885247730

private theorem prime_dvd_trialProduct {q : ℕ} (hq : Nat.Prime q) (hBound : q ≤ 128) :
    q ∣ trialProduct := by
  have hs : (List.range 129).all (fun n => decide (Nat.Prime n → n ∣ trialProduct)) =
      true := by decide +kernel
  exact (of_decide_eq_true (List.all_eq_true.mp hs q (List.mem_range.mpr (by omega)))) hq

private def boundedPrimeCertificate (n : ℕ) : Prop :=
  2 ≤ n ∧ n ≤ 16384 ∧ (if n ≤ 128 then Nat.Prime n else n.Coprime trialProduct)

private instance (n : ℕ) : Decidable (boundedPrimeCertificate n) := by
  unfold boundedPrimeCertificate
  infer_instance

private theorem prime_of_bounded_certificate {n : ℕ} (h : boundedPrimeCertificate n) :
    Nat.Prime n := by
  obtain ⟨hn₂, hnBound, htest⟩ := h
  by_cases hs : n ≤ 128
  · simpa [hs] using htest
  · have hCo : n.Coprime trialProduct := by simpa [hs] using htest
    by_contra hNot
    have hp := Nat.minFac_prime (show n ≠ 1 by omega)
    have hPow := Nat.minFac_sq_le_self (show 0 < n by omega) hNot
    have hsmall : n.minFac ≤ 128 := by
      by_contra hn
      have hh := Nat.pow_le_pow_left (show 129 ≤ n.minFac by omega) 2
      norm_num at hh
      omega
    have hd := Nat.dvd_gcd (Nat.minFac_dvd n) (prime_dvd_trialProduct hp hsmall)
    rw [Nat.coprime_iff_gcd_eq_one.mp hCo] at hd
    exact hp.not_dvd_one hd


private def witness (b j : ℕ) : ℕ :=
  match b with
  | 0 => ((#[3, 3, 5, 3, 7, 7, 3, 19, 5, 3, 3, 11, 11, 13, 7, 5, 3, 5, 11, 3, 5, 3, 19, 5, 3, 7, 11, 5, 3, 13, 5, 3] : Array ℕ)[j]?).getD 0
  | 1 => ((#[5, 3, 3, 5, 5, 7, 5, 23, 3, 11, 5, 3, 11, 3, 13, 7, 11, 3, 5, 3, 19, 5, 3, 13, 5, 17, 3, 7, 5, 73, 11, 3] : Array ℕ)[j]?).getD 0
  | 2 => ((#[7, 5, 3, 19, 7, 3, 7, 23, 5, 3, 7, 3, 3, 11, 5, 3, 5, 5, 7, 17, 41, 3, 11, 41, 43, 7, 3, 13, 5, 5, 31, 5] : Array ℕ)[j]?).getD 0
  | 3 => ((#[3, 19, 5, 3, 3, 5, 11, 7, 11, 3, 3, 5, 3, 7, 17, 3, 7, 13, 17, 67, 5, 11, 3, 7, 3, 3, 17, 5, 3, 5, 3, 19] : Array ℕ)[j]?).getD 0
  | 4 => ((#[11, 11, 7, 13, 17, 3, 7, 23, 13, 5, 3, 3, 5, 3, 7, 7, 11, 3, 5, 11, 3, 7, 5, 43, 7, 5, 3, 19, 53, 7, 5, 3] : Array ℕ)[j]?).getD 0
  | 5 => ((#[19, 13, 17, 3, 7, 23, 13, 5, 5, 7, 5, 3, 19, 7, 3, 13, 13, 5, 3, 19, 17, 3, 11, 5, 3, 5, 23, 7, 5, 3, 7, 5] : Array ℕ)[j]?).getD 0
  | 6 => ((#[5, 37, 11, 17, 31, 5, 3, 13, 7, 3, 19, 5, 23, 37, 5, 5, 13, 13, 3, 3, 17, 11, 7, 7, 3, 19, 5, 3, 3, 5, 11, 3] : Array ℕ)[j]?).getD 0
  | 7 => ((#[7, 3, 19, 5, 5, 3, 5, 3, 19, 5, 41, 7, 13, 5, 3, 7, 3, 19, 7, 23, 3, 5, 5, 37, 17, 11, 3, 5, 29, 7, 7, 3] : Array ℕ)[j]?).getD 0
  | 8 => ((#[13, 17, 5, 3, 17, 53, 7, 5, 11, 3, 11, 5, 7, 23, 47, 3, 5, 11, 3, 7, 11, 7, 7, 17, 3, 5, 5, 31, 11, 29, 31, 5] : Array ℕ)[j]?).getD 0
  | 9 => ((#[3, 3, 5, 23, 31, 13, 17, 3, 19, 17, 61, 7, 3, 19, 17, 3, 3, 7, 3, 19, 7, 3, 3, 5, 5, 3, 17, 5, 13, 7, 3, 7] : Array ℕ)[j]?).getD 0
  | 10 => ((#[17, 5, 61, 5, 3, 7, 5, 11, 3, 7, 17, 3, 5, 11, 13, 29, 5, 61, 5, 3, 7, 23, 5, 3, 13, 5, 31, 5, 3, 19, 43, 41] : Array ℕ)[j]?).getD 0
  | 11 => ((#[7, 5, 11, 3, 11, 11, 3, 11, 59, 13, 7, 3, 13, 5, 3, 7, 7, 17, 13, 13, 29, 3, 13, 5, 3, 5, 11, 7, 5, 11, 7, 11] : Array ℕ)[j]?).getD 0
  | 12 => ((#[17, 3, 19, 5, 3, 11, 53, 3, 11, 3, 3, 7, 23, 7, 5, 3, 19, 5, 59, 13, 7, 5, 31, 7, 23, 7, 5, 11, 31, 5, 3, 3] : Array ℕ)[j]?).getD 0
  | 13 => ((#[11, 29, 3, 11, 3, 19, 5, 3, 7, 13, 3, 7, 7, 11, 13, 5, 11, 37, 11, 5, 31, 7, 5, 13, 13, 3, 19, 47, 11, 7, 23, 17] : Array ℕ)[j]?).getD 0
  | 14 => ((#[7, 7, 3, 3, 5, 11, 37, 13, 3, 7, 11, 11, 7, 23, 59, 7, 7, 5, 13, 7, 5, 3, 7, 3, 7, 7, 11, 13, 11, 5, 43, 7] : Array ℕ)[j]?).getD 0
  | 15 => ((#[5, 13, 5, 3, 3, 17, 3, 19, 7, 11, 3, 5, 5, 3, 13, 3, 3, 5, 47, 7, 5, 23, 31, 5, 11, 3, 11, 5, 43, 13, 5, 13] : Array ℕ)[j]?).getD 0
  | 16 => ((#[17, 3, 3, 13, 3, 19, 7, 3, 7, 23, 5, 7, 11, 29, 3, 5, 3, 13, 29, 11, 7, 5, 17, 3, 11, 11, 43, 11, 29, 3, 7, 5] : Array ℕ)[j]?).getD 0
  | 17 => ((#[7, 5, 5, 7, 5, 17, 13, 11, 11, 3, 13, 3, 19, 5, 3, 19, 5, 23, 7, 11, 11, 7, 5, 29, 13, 11, 3, 19, 7, 3, 13, 7] : Array ℕ)[j]?).getD 0
  | 18 => ((#[5, 7, 7, 3, 3, 19, 5, 3, 11, 5, 43, 5, 3, 3, 17, 5, 67, 7, 23, 3, 5, 17, 37, 13, 3, 3, 5, 3, 3, 7, 23, 7] : Array ℕ)[j]?).getD 0
  | 19 => ((#[5, 11, 7, 5, 5, 7, 7, 5, 13, 5, 3, 13, 5, 3, 19, 11, 59, 7, 23, 11, 3, 11, 3, 13, 17, 3, 19, 7, 11, 31, 13, 17] : Array ℕ)[j]?).getD 0
  | 20 => ((#[3, 5, 17, 3, 7, 3, 19, 11, 41, 31, 17, 3, 19, 5, 3, 19, 11, 29, 13, 29, 17, 3, 7, 11, 13, 5, 5, 31, 13, 11, 3, 13] : Array ℕ)[j]?).getD 0
  | 21 => ((#[29, 3, 11, 17, 43, 11, 3, 13, 5, 3, 19, 5, 3, 3, 5, 5, 31, 13, 29, 3, 5, 11, 3, 5, 3, 7, 7, 3, 3, 19, 5, 3] : Array ℕ)[j]?).getD 0
  | 22 => ((#[7, 17, 13, 7, 23, 7, 7, 23, 79, 13, 3, 13, 5, 5, 7, 17, 17, 3, 17, 5, 3, 19, 11, 31, 7, 3, 7, 11, 11, 13, 17, 59] : Array ℕ)[j]?).getD 0
  | 23 => ((#[3, 7, 3, 7, 17, 5, 61, 7, 11, 3, 11, 29, 3, 13, 5, 61, 5, 23, 7, 23, 3, 19, 31, 3, 13, 29, 5, 13, 13, 3, 3, 7] : Array ℕ)[j]?).getD 0
  | 24 => ((#[3, 19, 7, 5, 67, 5, 23, 3, 11, 11, 7, 7, 5, 61, 11, 3, 7, 7, 3, 7, 5, 3, 3, 13, 17, 7, 7, 23, 13, 5, 3, 19] : Array ℕ)[j]?).getD 0
  | 25 => ((#[7, 3, 7, 11, 59, 3, 5, 5, 3, 7, 3, 13, 5, 17, 3, 7, 23, 79, 5, 11, 37, 5, 5, 7, 13, 29, 3, 7, 5, 13, 5, 3] : Array ℕ)[j]?).getD 0
  | 26 => ((#[19, 5, 23, 37, 11, 11, 3, 19, 5, 3, 11, 5, 7, 13, 29, 31, 7, 3, 3, 5, 29, 31, 11, 3, 3, 5, 23, 3, 13, 3, 19, 17] : Array ℕ)[j]?).getD 0
  | 27 => ((#[11, 67, 13, 5, 3, 7, 3, 19, 5, 17, 3, 5, 3, 19, 7, 23, 13, 5, 41, 37, 7, 3, 19, 11, 3, 19, 5, 23, 7, 11, 17, 13] : Array ℕ)[j]?).getD 0
  | 28 => ((#[5, 41, 37, 11, 5, 13, 11, 3, 19, 7, 23, 67, 7, 3, 13, 29, 17, 3, 7, 3, 3, 5, 5, 3, 5, 5, 31, 5, 3, 3, 5, 5] : Array ℕ)[j]?).getD 0
  | 29 => ((#[13, 11, 5, 43, 5, 5, 3, 7, 23, 61, 7, 23, 3, 11, 5, 3, 13, 5, 3, 7, 11, 7, 17, 5, 7, 5, 3, 7, 5, 29, 13, 11] : Array ℕ)[j]?).getD 0
  | 30 => ((#[3, 19, 7, 11, 13, 5, 5, 37, 7, 23, 43, 11, 17, 3, 17, 47, 3, 5, 3, 13, 13, 29, 61, 5, 11, 3, 5, 5, 7, 17, 47, 13] : Array ℕ)[j]?).getD 0
  | 31 => ((#[7, 3, 7, 13, 29, 31, 11, 29, 43, 31, 41, 3, 7, 5, 43, 17, 3, 19, 37, 3, 19, 7, 11, 3, 5, 59, 3, 19, 3, 3, 5, 3] : Array ℕ)[j]?).getD 0
  | _ => 0

private def total (b j : ℕ) : ℕ := 16 * (32*b + j + 1)

private def valid (b j : ℕ) : Prop :=
  Nat.Prime (witness b j) ∧ Odd (witness b j) ∧
    boundedPrimeCertificate (total b j - witness b j) ∧ Odd (total b j - witness b j) ∧
      witness b j ≤ total b j

private instance (b j : ℕ) : Decidable (valid b j) := by
  unfold valid
  infer_instance

set_option maxHeartbeats 1800000 in
private theorem page0 :
    (List.range 32).all (fun j => decide (valid 0 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page1 :
    (List.range 32).all (fun j => decide (valid 1 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page2 :
    (List.range 32).all (fun j => decide (valid 2 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page3 :
    (List.range 32).all (fun j => decide (valid 3 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page4 :
    (List.range 32).all (fun j => decide (valid 4 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page5 :
    (List.range 32).all (fun j => decide (valid 5 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page6 :
    (List.range 32).all (fun j => decide (valid 6 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page7 :
    (List.range 32).all (fun j => decide (valid 7 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page8 :
    (List.range 32).all (fun j => decide (valid 8 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page9 :
    (List.range 32).all (fun j => decide (valid 9 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page10 :
    (List.range 32).all (fun j => decide (valid 10 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page11 :
    (List.range 32).all (fun j => decide (valid 11 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page12 :
    (List.range 32).all (fun j => decide (valid 12 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page13 :
    (List.range 32).all (fun j => decide (valid 13 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page14 :
    (List.range 32).all (fun j => decide (valid 14 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page15 :
    (List.range 32).all (fun j => decide (valid 15 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page16 :
    (List.range 32).all (fun j => decide (valid 16 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page17 :
    (List.range 32).all (fun j => decide (valid 17 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page18 :
    (List.range 32).all (fun j => decide (valid 18 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page19 :
    (List.range 32).all (fun j => decide (valid 19 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page20 :
    (List.range 32).all (fun j => decide (valid 20 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page21 :
    (List.range 32).all (fun j => decide (valid 21 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page22 :
    (List.range 32).all (fun j => decide (valid 22 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page23 :
    (List.range 32).all (fun j => decide (valid 23 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page24 :
    (List.range 32).all (fun j => decide (valid 24 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page25 :
    (List.range 32).all (fun j => decide (valid 25 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page26 :
    (List.range 32).all (fun j => decide (valid 26 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page27 :
    (List.range 32).all (fun j => decide (valid 27 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page28 :
    (List.range 32).all (fun j => decide (valid 28 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page29 :
    (List.range 32).all (fun j => decide (valid 29 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page30 :
    (List.range 32).all (fun j => decide (valid 30 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem page31 :
    (List.range 32).all (fun j => decide (valid 31 j)) = true := by
  decide +kernel

set_option maxHeartbeats 1800000 in
private theorem validated_page (b : ℕ) (hb : b < 32) :
    (List.range 32).all (fun j => decide (valid b j)) = true := by
  interval_cases b
  · exact page0
  · exact page1
  · exact page2
  · exact page3
  · exact page4
  · exact page5
  · exact page6
  · exact page7
  · exact page8
  · exact page9
  · exact page10
  · exact page11
  · exact page12
  · exact page13
  · exact page14
  · exact page15
  · exact page16
  · exact page17
  · exact page18
  · exact page19
  · exact page20
  · exact page21
  · exact page22
  · exact page23
  · exact page24
  · exact page25
  · exact page26
  · exact page27
  · exact page28
  · exact page29
  · exact page30
  · exact page31

set_option maxHeartbeats 1800000 in
theorem Taskdc0a505371b58c19da53c009 :
    have x1 : ℕ → Prop := fun (x1 : ℕ) => ∃ (x2 : ℕ) (x3 : ℕ), Nat.Prime x2 ∧ Odd x2 ∧ Nat.Prime x3 ∧ Odd x3 ∧ x2 + x3 = x1; ∀ x2 < (1024 : ℕ), x1 ((16 : ℕ) * (x2 + (1 : ℕ))) := by
  dsimp only
  intro i hi
  let b := i / 32
  let j := i % 32
  have hb : b < 32 := by dsimp [b]; omega
  have hj : j < 32 := Nat.mod_lt _ (by decide)
  have validWitness : valid b j :=
    of_decide_eq_true (List.all_eq_true.mp (validated_page b hb) j (List.mem_range.mpr hj))
  obtain ⟨hp, hpo, hq, hqo, hle⟩ := validWitness
  refine ⟨witness b j, total b j - witness b j, hp, hpo, prime_of_bounded_certificate hq, hqo, ?_⟩
  calc
    _ = total b j := Nat.add_sub_of_le hle
    _ = _ := by dsimp [total,b,j]; omega

end Conjectures.Cuts
