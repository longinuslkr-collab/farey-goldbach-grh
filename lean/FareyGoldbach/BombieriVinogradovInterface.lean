import FareyGoldbach.ChenSwitchingAssembly

/-! # Uniform primitive-character first moments of sharp Mangoldt sums -/

open Filter Finset
open scoped Topology Classical

namespace FareyGoldbach

def ChenPrimitiveMangoldtBV : Prop :=
  ∀ θ : ℝ, 11/24<θ → θ<1/2 → ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop, ∀ X : ℕ, X≤N →
    (∑ q ∈ Ico 2 (chenPowerLevel θ N), chenPrimitiveNorm q (fun χ =>
      ∑ n ∈ Icc 1 X, (ArithmeticFunction.vonMangoldt n:ℂ)*χ n)/(q:ℝ)) ≤
      ε*(N:ℝ)/Real.log (N:ℝ)^3

end FareyGoldbach
