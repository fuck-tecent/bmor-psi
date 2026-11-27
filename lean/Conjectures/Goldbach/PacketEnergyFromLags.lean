import Mathlib

/-!
Packet energy from the two lag autocorrelations.

The high band of the prime weight is measured against the wheel model through two exact
lag expansions taken at one common threshold.  Writing the masked energy of a weight as
its short-lag part plus its long-lag part, for the high band and for the model, and then
adding the three budgets gives

  1/2304 + 1/2304 + 1/1152 = 1/576,

so the model budget, the short-lag difference budget and the long-lag difference budget
combine into the high-band energy budget.  The auxiliary definitions below repeat, one by
one, the local definitions of the statement, so that every hypothesis and the goal can be
read in a single common set of names.
-/

noncomputable section

namespace Conjectures.Goldbach.PacketEnergyFromLags_aux

/-- Two exact lag expansions on one mask, plus the three budgets, give the high-band budget. -/
theorem energyFromLags {U short long : ℕ → (ℕ → ℝ) → ℝ} {high : ℕ → ℕ → ℝ} {model : ℕ → ℝ}
    (expand : ∀ (n : ℕ) (a : ℕ → ℝ), U n a = short n a + long n a)
    (wheel : ∃ N : ℕ, ∀ n ≥ N, Even n → U n model ≤ (n:ℝ)/2304)
    (near : ∃ N : ℕ, ∀ n ≥ N, Even n →
      |short n (high n) - short n model| ≤ (n:ℝ)/2304)
    (far : ∃ N : ℕ, ∀ n ≥ N, Even n →
      long n (high n) - long n model ≤ (n:ℝ)/1152) :
    ∃ N : ℕ, ∀ n ≥ N, Even n → U n (high n) ≤ (n:ℝ)/576 := by
  obtain ⟨N₁, hwheel⟩ := wheel
  obtain ⟨N₂, hnear⟩ := near
  obtain ⟨N₃, hfar⟩ := far
  refine ⟨max N₁ (max N₂ N₃), fun n hn hEven => ?_⟩
  have hn₁ : N₁ ≤ n := le_trans (le_max_left N₁ _) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_left N₂ N₃) (le_trans (le_max_right N₁ _) hn)
  have hn₃ : N₃ ≤ n := le_trans (le_max_right N₂ N₃) (le_trans (le_max_right N₁ _) hn)
  have eHigh : U n (high n) = short n (high n) + long n (high n) := expand n (high n)
  have eModel : U n model = short n model + long n model := expand n model
  have bWheel : U n model ≤ (n:ℝ)/2304 := hwheel n hn₁ hEven
  have bNear : short n (high n) - short n model ≤ (n:ℝ)/2304 :=
    (abs_le.mp (hnear n hn₂ hEven)).2
  have bFar : long n (high n) - long n model ≤ (n:ℝ)/1152 := hfar n hn₃ hEven
  linarith only [eHigh, eModel, bWheel, bNear, bFar]

/-- The prime weight of the statement. -/
def pkW (k : ℕ) : ℝ := if Nat.Prime k then Real.log (k:ℝ) else 0

/-- The phase of the statement. -/
def pkE (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)

/-- The exponential sum of the statement. -/
def pkS (n : ℕ) (w : ℕ → ℝ) (t : ℝ) : ℂ :=
  Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*pkE ((k:ℝ)*t))

/-- The truncation height of the statement. -/
def pkQ (n : ℕ) : ℕ := (Nat.log 2 (n+2))^2

/-- The major arcs of the statement. -/
def pkArcs (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤pkQ n ∧ a≤q ∧ Nat.Coprime a q ∧
    |t-(a:ℝ)/(q:ℝ)| ≤ (pkQ n:ℝ)/((q:ℝ)*(n:ℝ))}

/-- The low band of the prime weight. -/
def pkLow (n k : ℕ) : ℝ := if k^3≤n then pkW k else 0

/-- The high band of the prime weight. -/
def pkHigh (n k : ℕ) : ℝ := pkW k-pkLow n k

/-- The dyadic length of the statement. -/
def pkL (n : ℕ) : ℕ := max 1 (Nat.log 2 n / 2)

/-- The kernel average of the statement. -/
def pkK (n : ℕ) (t : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (pkL n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(pkL n:ℝ)

/-- The resonant set of the statement. -/
def pkB (n : ℕ) : Set ℝ := {t : ℝ | t ∉ pkArcs n ∧ (1:ℝ)/2 < pkK n t}

/-- The masked energy of the statement. -/
def pkU (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  intervalIntegral ((pkB n).indicator (fun t => ‖pkS n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume

/-- The cosine moment of the statement. -/
def pkV (n h : ℕ) : ℝ :=
  intervalIntegral ((pkB n).indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t)))
    (0:ℝ) 1 MeasureTheory.volume

/-- The autocorrelation of the statement. -/
def pkA (n h : ℕ) (a : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range (n+1-h), a k * a (k+h)

/-- The wheel model of the statement. -/
def pkModel (k : ℕ) : ℝ := if Nat.Coprime k 30 then (30:ℝ)/8 else 0

/-- The short-lag part of the statement. -/
def pkShort (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  pkA n 0 a * pkV n 0 + 2*(∑ h ∈ Finset.Icc 1 (min n ((pkL n)^2)), pkA n h a * pkV n h)

/-- The long-lag part of the statement. -/
def pkLong (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  2*(∑ h ∈ Finset.Icc ((pkL n)^2+1) n, pkA n h a * pkV n h)

end Conjectures.Goldbach.PacketEnergyFromLags_aux

open Conjectures.Goldbach.PacketEnergyFromLags_aux

theorem Conjectures.Goldbach.PacketEnergyFromLags :
    (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; let V := fun (n h : ℕ) => intervalIntegral ((B n).indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume; let A := fun (n h : ℕ) (a : ℕ → ℝ) => ∑ k ∈ Finset.range (n+1-h), a k * a (k+h); let model := fun k : ℕ => if Nat.Coprime k 30 then (30:ℝ)/8 else 0; let short := fun (n : ℕ) (a : ℕ → ℝ) => A n 0 a * V n 0 + 2*(∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), A n h a * V n h); let long := fun (n : ℕ) (a : ℕ → ℝ) => 2*(∑ h ∈ Finset.Icc ((L n)^2+1) n, A n h a * V n h); ∀ (n : ℕ) (a : ℕ → ℝ), U n a = short n a + long n a) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; let V := fun (n h : ℕ) => intervalIntegral ((B n).indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume; let A := fun (n h : ℕ) (a : ℕ → ℝ) => ∑ k ∈ Finset.range (n+1-h), a k * a (k+h); let model := fun k : ℕ => if Nat.Coprime k 30 then (30:ℝ)/8 else 0; let short := fun (n : ℕ) (a : ℕ → ℝ) => A n 0 a * V n 0 + 2*(∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), A n h a * V n h); let long := fun (n : ℕ) (a : ℕ → ℝ) => 2*(∑ h ∈ Finset.Icc ((L n)^2+1) n, A n h a * V n h); ∃ N : ℕ, ∀ n ≥ N, Even n → U n model ≤ (n:ℝ)/2304) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; let V := fun (n h : ℕ) => intervalIntegral ((B n).indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume; let A := fun (n h : ℕ) (a : ℕ → ℝ) => ∑ k ∈ Finset.range (n+1-h), a k * a (k+h); let model := fun k : ℕ => if Nat.Coprime k 30 then (30:ℝ)/8 else 0; let short := fun (n : ℕ) (a : ℕ → ℝ) => A n 0 a * V n 0 + 2*(∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), A n h a * V n h); let long := fun (n : ℕ) (a : ℕ → ℝ) => 2*(∑ h ∈ Finset.Icc ((L n)^2+1) n, A n h a * V n h); ∃ N : ℕ, ∀ n ≥ N, Even n → |short n (high n) - short n model| ≤ (n:ℝ)/2304) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; let V := fun (n h : ℕ) => intervalIntegral ((B n).indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume; let A := fun (n h : ℕ) (a : ℕ → ℝ) => ∑ k ∈ Finset.range (n+1-h), a k * a (k+h); let model := fun k : ℕ => if Nat.Coprime k 30 then (30:ℝ)/8 else 0; let short := fun (n : ℕ) (a : ℕ → ℝ) => A n 0 a * V n 0 + 2*(∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), A n h a * V n h); let long := fun (n : ℕ) (a : ℕ → ℝ) => 2*(∑ h ∈ Finset.Icc ((L n)^2+1) n, A n h a * V n h); ∃ N : ℕ, ∀ n ≥ N, Even n → long n (high n) - long n model ≤ (n:ℝ)/1152) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → U n (high n) ≤ (n:ℝ)/576) := by
  intro hExpand hWheel hNear hFar
  have eExpand : ∀ (n : ℕ) (a : ℕ → ℝ), pkU n a = pkShort n a + pkLong n a := hExpand
  have eWheel : ∃ N : ℕ, ∀ n ≥ N, Even n → pkU n pkModel ≤ (n:ℝ)/2304 := hWheel
  have eNear : ∃ N : ℕ, ∀ n ≥ N, Even n →
    |pkShort n (pkHigh n) - pkShort n pkModel| ≤ (n:ℝ)/2304 := hNear
  have eFar : ∃ N : ℕ, ∀ n ≥ N, Even n →
    pkLong n (pkHigh n) - pkLong n pkModel ≤ (n:ℝ)/1152 := hFar
  exact energyFromLags eExpand eWheel eNear eFar
