import Mathlib

theorem PEqualNP.Outside.L_square_packing_axis_dot_certificate :
    let rad := fun (a b c s : ℝ) => (|a*c+b*s|+|b*c-a*s|)/2; ∀ a b c s k l x y u v i j m n : ℝ, |i|<1/2 → |j|<1/2 → |m|<1/2 → |n|<1/2 → 0<rad a b c s → 0<rad a b k l → rad a b c s+rad a b k l≤a*(u-x)+b*(v-y) → (x+c*i-s*j,y+s*i+c*j)≠(u+k*m-l*n,v+l*m+k*n) := by
  dsimp only
  intro a b c s k l x y u v i j m n hi hj hm hn hrad1 hrad2 hsep heq
  have hx : x + c * i - s * j = u + k * m - l * n := congrArg Prod.fst heq
  have hy : y + s * i + c * j = v + l * m + k * n := congrArg Prod.snd heq
  have dot_lt : ∀ p q t₁ t₂ : ℝ, |t₁| < 1 / 2 → |t₂| < 1 / 2 → 0 < (|p| + |q|) / 2 →
      p * t₁ + q * t₂ < (|p| + |q|) / 2 := by
    intro p q t₁ t₂ ht₁ ht₂ hpos
    have hpq : 0 < |p| + |q| := by linarith
    set δ := max |t₁| |t₂|
    have hδ : δ < 1 / 2 := max_lt ht₁ ht₂
    have h1 : p * t₁ ≤ |p| * δ := by
      calc
        p * t₁ ≤ |p * t₁| := le_abs_self _
        _ = |p| * |t₁| := abs_mul p t₁
        _ ≤ |p| * δ := mul_le_mul_of_nonneg_left (le_max_left _ _) (abs_nonneg p)
    have h2 : q * t₂ ≤ |q| * δ := by
      calc
        q * t₂ ≤ |q * t₂| := le_abs_self _
        _ = |q| * |t₂| := abs_mul q t₂
        _ ≤ |q| * δ := mul_le_mul_of_nonneg_left (le_max_right _ _) (abs_nonneg q)
    have h3 : (|p| + |q|) * δ < (|p| + |q|) * (1 / 2) := mul_lt_mul_of_pos_left hδ hpq
    linarith
  have hlt1 : (a * c + b * s) * i + (b * c - a * s) * j < (|a * c + b * s| + |b * c - a * s|) / 2 :=
    dot_lt (a * c + b * s) (b * c - a * s) i j hi hj hrad1
  have hlt2 : (a * k + b * l) * (-m) + (b * k - a * l) * (-n) <
      (|a * k + b * l| + |b * k - a * l|) / 2 :=
    dot_lt (a * k + b * l) (b * k - a * l) (-m) (-n) (by rwa [abs_neg]) (by rwa [abs_neg]) hrad2
  have hproj : a * (u - x) + b * (v - y) =
      ((a * c + b * s) * i + (b * c - a * s) * j) +
      ((a * k + b * l) * (-m) + (b * k - a * l) * (-n)) := by
    linear_combination -a * hx - b * hy
  linarith
