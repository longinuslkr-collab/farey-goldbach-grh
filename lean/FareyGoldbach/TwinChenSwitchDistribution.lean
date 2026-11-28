import FareyGoldbach.TwinChenSwitchMass
import FareyGoldbach.TwinChenBoxRemainderOfGRH
import FareyGoldbach.TwinChenBoxRemainderUnconditional

/-! # Combined mass and divisor-error bounds for the two shifted carriers -/

open Filter Finset
open scoped Topology

namespace FareyGoldbach

private theorem combined_distribution_of_dirichletGRH {δ θ c : ℝ}
    (hδ : 0<δ) (hθ : 11/24<θ) (hsum : δ+θ<1/2) (hGRH : DirichletGRH)
    {carrier : ℕ→ℕ→ℕ→Finset ℕ} (hboxes : TwinChenCarrierHasBoxes carrier)
    (hmass : ∀ ε : ℝ, 0<ε → ∀ᶠ M : ℕ in atTop,
      ∀ r b : ℕ, 0<r → (r:ℝ)≤(M:ℝ)^δ → (b+2).Coprime r →
        ((carrier M r b).card:ℝ)≤(c+ε)*chenAPMassScale M r) :
    TwinChenCarrierDistributionAt δ θ c carrier := by
  intro ε hε
  filter_upwards [hmass ε hε,twinChen_carrier_error_of_dirichletGRH hδ hθ hsum hGRH hε hboxes]
    with M hm he r b hr hpow _ hb
  exact ⟨hm r b hr hpow hb,he r b hr hpow hb⟩

theorem twinChenClassicDistribution_of_dirichletGRH {δ θ : ℝ}
    (hδ : 0<δ) (hθ : 11/24<θ) (hsum : δ+θ<1/2) (hGRH : DirichletGRH) :
    TwinChenCarrierDistributionAt δ θ chenSwitchIntegral twinChenClassicCarrier :=
  combined_distribution_of_dirichletGRH hδ hθ hsum hGRH twinChenClassicCarrier_hasBoxes
    (fun _ hε => twinChen_classic_mass_of_dirichletGRH hδ (by linarith only [hθ,hsum]) hGRH hε)

theorem twinChenBoundedDistribution_of_dirichletGRH {δ θ η : ℝ}
    (hδ : 0<δ) (hθ : 11/24<θ) (hsum : δ+θ<1/2)
    (hη : 0<η) (hη' : η<1/6) (hGRH : DirichletGRH) :
    TwinChenCarrierDistributionAt δ θ (2*Real.log (1/(1-2*η))) (twinChenBoundedCarrier η) :=
  combined_distribution_of_dirichletGRH hδ hθ hsum hGRH (twinChenBoundedCarrier_hasBoxes hη')
    (fun _ hε => twinChen_bounded_mass_of_dirichletGRH hη hη' hδ
      (by linarith only [hθ,hsum]) hGRH hε)

private theorem combined_distribution_at_zero {θ c : ℝ}
    (hθ : 11/24<θ) (hθ' : θ<1/2)
    {carrier : ℕ→ℕ→ℕ→Finset ℕ} (hboxes : TwinChenCarrierHasBoxes carrier)
    (hmass : ∀ ε : ℝ, 0<ε → ∀ᶠ M : ℕ in atTop, ∀ b : ℕ,
      ((carrier M 1 b).card:ℝ)≤(c+ε)*chenAPMassScale M 1) :
    TwinChenCarrierDistributionAt 0 θ c carrier := by
  intro ε hε
  filter_upwards [hmass ε hε,twinChen_carrier_error_unconditional hθ hθ' hε hboxes]
    with M hm he r b hr hpow _ _
  have hr₁ : r=1 := by
    have h : (r:ℝ)≤1 := by simpa only [Real.rpow_zero] using hpow
    have : r≤1 := by exact_mod_cast h
    omega
  subst r
  exact ⟨hm b,by simpa only [Nat.mul_one] using he b⟩

theorem twinChenClassicDistributionAt_zero_unconditional {θ : ℝ}
    (hθ : 11/24<θ) (hθ' : θ<1/2) :
    TwinChenCarrierDistributionAt 0 θ chenSwitchIntegral twinChenClassicCarrier :=
  combined_distribution_at_zero hθ hθ' twinChenClassicCarrier_hasBoxes
    (fun _ hε => twinChen_classic_mass_unconditional hε)

theorem twinChenBoundedDistributionAt_zero_unconditional {θ η : ℝ}
    (hθ : 11/24<θ) (hθ' : θ<1/2) (hη : 0<η) (hη' : η<1/6) :
    TwinChenCarrierDistributionAt 0 θ (2*Real.log (1/(1-2*η))) (twinChenBoundedCarrier η) :=
  combined_distribution_at_zero hθ hθ' (twinChenBoundedCarrier_hasBoxes hη')
    (fun _ hε => twinChen_bounded_mass_unconditional hη hη' hε)

end FareyGoldbach
