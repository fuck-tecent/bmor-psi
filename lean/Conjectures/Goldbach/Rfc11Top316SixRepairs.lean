import Mathlib
import Conjectures.Goldbach.Rfc11Top316FirstBankCover
import Conjectures.Goldbach.Rfc11Top316AnchorBank

/-!
### New route · V13 · Replay the prime pairs in the proposal for [10^316-24576, 10^316)

For 1 ≤ i ≤ 12288 the even number n = 10^316 - 2*i is written as
(10^316 - t) + (t - 2*i) with an offset t of the anchor bank. The accepted module
Conjectures.Goldbach.Rfc11Top316FirstBankCover supplies, for every i outside the six
indices 7564, 7909, 11134, 11329, 11989, 12154, an offset t among the first forty with
t - 2*i prime; the three repair offsets 71799, 73059, 66447 cover those six. The anchors
10^316 - t are the statement of the accepted module
Conjectures.Goldbach.Rfc11Top316AnchorBank.
-/

namespace Conjectures.Goldbach.Rfc11Top316SixRepairs_aux

theorem cover (h : ∀ t ∈ ([25787, 23073, 28121, 30291, 29519, 51747, 29183, 30693, 46539, 27299, 55077, 35117, 58401, 48851, 29673, 44813, 22041, 52193, 40623, 35561, 59667, 54623, 31341, 41939, 42603, 49467, 57963, 12377, 33269, 18117, 18191, 42833, 46341, 38403, 48893, 1821, 8307, 14831, 15039, 60269, 71799, 73059, 66447] : List ℕ), Nat.Prime (10^316-t)) :
    (fun (lo hi : ℕ) => ∀ n : ℕ, lo≤n → n<hi → 2∣n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n) (10^316-24576) (10^316) := by
  intro n h1 h2 h3
  have hA : (10^316) % 2 = 0 := by decide +kernel
  obtain ⟨i, hi⟩ : ∃ i, n = 10^316 - 2 * i := ⟨(10^316 - n) / 2, by omega⟩
  clear hA
  have hlo : 1 ≤ i := by omega
  have hhi : i ≤ 12288 := by omega
  have hfb := Conjectures.Goldbach.Rfc11Top316FirstBankCover
  dsimp only at hfb
  by_cases he : i ∈ ([7564,7909,11134,11329,11989,12154] : List ℕ)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨10^316 - 71799, 56671, h 71799 (by decide), by norm_num, by omega⟩
    · exact ⟨10^316 - 73059, 57241, h 73059 (by decide), by norm_num, by omega⟩
    · exact ⟨10^316 - 71799, 49531, h 71799 (by decide), by norm_num, by omega⟩
    · exact ⟨10^316 - 66447, 43789, h 66447 (by decide), by norm_num, by omega⟩
    · exact ⟨10^316 - 73059, 49081, h 73059 (by decide), by norm_num, by omega⟩
    · exact ⟨10^316 - 71799, 47491, h 71799 (by decide), by norm_num, by omega⟩
  · obtain ⟨t, ht, hprime⟩ := (hfb i hlo hhi).mpr he
    have hto : t ∈ ([25787, 23073, 28121, 30291, 29519, 51747, 29183, 30693, 46539, 27299, 55077, 35117, 58401, 48851, 29673, 44813, 22041, 52193, 40623, 35561, 59667, 54623, 31341, 41939, 42603, 49467, 57963, 12377, 33269, 18117, 18191, 42833, 46341, 38403, 48893, 1821, 8307, 14831, 15039, 60269, 71799, 73059, 66447] : List ℕ) :=
      List.mem_of_mem_take ht
    have htb : t ≤ 73059 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hto
      omega
    have hq : 2 * i < t := by
      have := Nat.Prime.pos hprime
      omega
    exact ⟨10^316 - t, t - 2 * i, h t hto, hprime, by omega⟩

end Conjectures.Goldbach.Rfc11Top316SixRepairs_aux

theorem Conjectures.Goldbach.Rfc11Top316SixRepairs : (fun (lo hi : ℕ) => ∀ n : ℕ, lo≤n → n<hi → 2∣n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n) (10^316-24576) (10^316) :=
  Conjectures.Goldbach.Rfc11Top316SixRepairs_aux.cover Conjectures.Goldbach.Rfc11Top316AnchorBank
