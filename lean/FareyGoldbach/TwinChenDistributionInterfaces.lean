import FareyGoldbach.TwinChenCarriers
import FareyGoldbach.ChenAPDistributionInterfaces

/-! # Distribution inputs for Chen's sieve on the shifted primes -/

open Filter
open scoped Topology

namespace FareyGoldbach

noncomputable def twinChenPrimeError (X r b d : ℕ) : ℝ :=
  chenAPError (twinChenAPA X r b) (twinChenAPA X r b).card d

noncomputable def twinChenMediumError (X r b D : ℕ) : ℝ :=
  chenCarrierMediumError (2*r) (chenLowerCutoff (X+3)) (chenUpperCutoff (X+3)) D (twinChenAPA X r b)

def TwinChenPrimeDistributionAt (δ θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∀ᶠ X : ℕ in atTop, ∀ (r b : ℕ), 0<r → (r:ℝ)≤((X+3:ℕ):ℝ)^δ →
    b.Coprime r → (b+2).Coprime r →
      |((twinChenAPA X r b).card:ℝ)/chenAPMassScale (X+3) r-1|≤ε ∧
      chenReducedError (2*r) (chenPowerLevel θ (X+3)) (twinChenPrimeError X r b)≤
        ε*chenAPLogScale (X+3) r ∧
      twinChenMediumError X r b (chenPowerLevel θ (X+3))≤ε*chenAPLogScale (X+3) r

noncomputable def twinChenClassicCarrier (M r b : ℕ) : Finset ℕ :=
  twinChenAPUnrestrictedB M r b (chenLowerCutoff M) (chenUpperCutoff M)

noncomputable def twinChenBoundedCarrier (η : ℝ) (M r b : ℕ) : Finset ℕ :=
  twinChenAPBalancedB M r b (chenPowerLevel (1/2-η) M)

def TwinChenCarrierDistributionAt (δ θ c : ℝ) (carrier : ℕ→ℕ→ℕ→Finset ℕ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∀ᶠ M : ℕ in atTop, ∀ (r b : ℕ), 0<r → (r:ℝ)≤(M:ℝ)^δ →
    b.Coprime r → (b+2).Coprime r →
      let B := carrier M r b
      (B.card:ℝ)≤(c+ε)*chenAPMassScale M r ∧
        chenReducedError (2*r) (chenPowerLevel θ M) (chenAPError B B.card)≤ε*chenAPLogScale M r

end FareyGoldbach
