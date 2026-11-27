import Mathlib
open scoped BigOperators

noncomputable section
namespace B1B1

def E (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)

def S (n : ℕ) (u : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n+1), (u k : ℂ) * E ((k:ℝ)*t)

/-- The logarithmic denominator cutoff `Q²`. -/
def Qs (n : ℕ) : ℕ := (Nat.log 2 (n+2))^2

/-- The major-arc denominator cutoff. -/
def Qcut (n : ℕ) : ℕ := ⌊(n:ℝ)^(1/3:ℝ)⌋₊

/-- The widened arc semi-width numerator. -/
def Hwide (n : ℕ) : ℕ := 256 * Qcut n * Qs n

/-- The widened arcs (deep-minor complement). -/
def wideArcs (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qcut n ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a:ℝ)/(q:ℝ)| ≤ (Hwide n:ℝ)/((q:ℝ)*(n:ℝ))}

/-- Lower cutoff of the balanced band. -/
def Ucut (n : ℕ) : ℕ := ⌊(n:ℝ)^(1/16:ℝ)⌋₊

/-- Upper cutoff of the balanced band. -/
def Bcut (n : ℕ) : ℕ := ⌊(n:ℝ)^(1/4:ℝ)⌋₊

/-- The Möbius coefficient of the inner divisor. -/
def ccoef (n a : ℕ) : ℝ :=
  ∑ d ∈ (Nat.divisors a).filter (fun d => Ucut n < d),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ)

/-- The balanced-frontier Type-II coefficient `τ₁`. -/
def tau1 (n m : ℕ) : ℝ :=
  ∑ a ∈ (Nat.divisors m).filter (fun a => Ucut n < a ∧ a ≤ Bcut n ∧ Ucut n < m / a),
    ccoef n a * ArithmeticFunction.vonMangoldt (m / a)

/-- The deep-minor integral over `wideArcsᶜ`. -/
def Jdeep (n : ℕ) (u v : ℕ → ℝ) : ℂ :=
  intervalIntegral (fun t => (wideArcs n)ᶜ.indicator
    (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume

/-- Packaged `L-goldbach-frontier-type2-b1-b1` target. -/
def Target : Prop :=
  ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
    ‖Jdeep n (tau1 n) (tau1 n)‖ ≤ e * (n : ℝ)

end B1B1

end B1B1
