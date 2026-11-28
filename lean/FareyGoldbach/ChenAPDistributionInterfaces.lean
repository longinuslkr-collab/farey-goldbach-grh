import FareyGoldbach.ChenAPScale
import FareyGoldbach.ChenAPSwitching

/-! # Distribution inputs for the Chen sieve in a prescribed progression -/

open Filter
open scoped Topology

namespace FareyGoldbach

noncomputable def chenAPPrimeError (N r b d : ℕ) : ℝ :=
  chenAPError (chenAPA N r b) (chenAPA N r b).card d

noncomputable def chenAPMediumError (N r b D : ℕ) : ℝ :=
  chenCarrierMediumError (r*N) (chenLowerCutoff N) (chenUpperCutoff N) D (chenAPA N r b)

/-- The index b refers to the product complementary to the switched element. -/
noncomputable def chenAPSwitchedError (N r b d : ℕ) : ℝ :=
  let B := chenAPUnrestrictedB N r b (chenLowerCutoff N) (chenUpperCutoff N)
  chenAPError B B.card d

/-- The outer eventual quantifier gives one threshold for every modulus,
compatible pair of classes, and all three prime-distribution estimates. -/
def ChenAPPrimeDistributionAt (δ θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop, Even N →
    ∀ (r b₁ b₂ : ℕ), 0<r → (r:ℝ)≤(N:ℝ)^δ →
      b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
        |((chenAPA N r b₁).card:ℝ)/chenAPMassScale N r-1|≤ε ∧
        chenReducedError (r*N) (chenPowerLevel θ N) (chenAPPrimeError N r b₁)≤
          ε*chenAPLogScale N r ∧
        chenAPMediumError N r b₁ (chenPowerLevel θ N)≤ε*chenAPLogScale N r

/-- The switched elements lie in the prime class b₁. The carrier is
indexed instead by the compatible product class b₂. -/
def ChenAPSwitchingDistributionAt (δ θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop, Even N →
    ∀ (r b₁ b₂ : ℕ), 0<r → (r:ℝ)≤(N:ℝ)^δ →
      b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
        ((chenAPUnrestrictedB N r b₂ (chenLowerCutoff N) (chenUpperCutoff N)).card:ℝ)≤
          (chenSwitchIntegral+ε)*chenAPMassScale N r ∧
        chenReducedError (r*N) (chenPowerLevel θ N) (chenAPSwitchedError N r b₂)≤
          ε*chenAPLogScale N r

end FareyGoldbach
