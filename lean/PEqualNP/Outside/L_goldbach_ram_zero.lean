import Mathlib

theorem PEqualNP.Outside.L_goldbach_ram_zero :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ q, 0<q → ram q 0=(Nat.totient q:ℂ) := by
  dsimp only
  intro q _
  simp [Nat.totient, Nat.coprime_comm]
