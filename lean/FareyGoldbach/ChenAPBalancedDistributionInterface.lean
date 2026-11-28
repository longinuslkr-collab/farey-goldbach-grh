import FareyGoldbach.ChenBalancedPairs
import FareyGoldbach.ChenAPDistributionInterfaces

/-! # Distribution estimates for the balanced switched carrier -/

open Filter
open scoped Topology

namespace FareyGoldbach

def ChenAPBalancedDistributionAt (δ θ η : ℝ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop, Even N →
    ∀ (r b₁ b₂ : ℕ), 0<r → (r:ℝ)≤(N:ℝ)^δ →
      b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
        let B := chenAPBalancedB N r b₂ (chenPowerLevel (1/2-η) N)
        (B.card:ℝ) ≤ (2*Real.log (1/(1-2*η))+ε)*chenAPMassScale N r ∧
        chenReducedError (r*N) (chenPowerLevel θ N) (chenAPError B B.card) ≤
          ε*chenAPLogScale N r

end FareyGoldbach
