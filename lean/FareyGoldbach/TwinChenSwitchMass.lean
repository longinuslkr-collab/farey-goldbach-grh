import FareyGoldbach.TwinChenDistributionInterfaces
import FareyGoldbach.ChenAPSwitchingMass
import FareyGoldbach.ChenBalancedMass
import FareyGoldbach.PrimeNumberTheoremUnconditional

/-! # The shift by two preserves each product-class count -/

open Filter
open scoped Classical

namespace FareyGoldbach

theorem twinChen_classic_mass_of_dirichletGRH {δ ε : ℝ}
    (hδ : 0<δ) (hδ' : δ<1/8) (hGRH : DirichletGRH) (hε : 0<ε) :
    ∀ᶠ M : ℕ in atTop, ∀ r b : ℕ, 0<r → (r:ℝ)≤(M:ℝ)^δ → (b+2).Coprime r →
      ((twinChenClassicCarrier M r b).card:ℝ)≤(chenSwitchIntegral+ε)*chenAPMassScale M r := by
  filter_upwards [chenAP_switching_product_mass_of_dirichletGRH hδ hδ' hGRH hε]
    with M h r b hr hpow hb
  simpa only [twinChenClassicCarrier,twinChenAPUnrestrictedB_card_eq_pair_filter,
    chenAPUnrestrictedB_card_eq_pair_filter] using h r (b+2) hr hpow hb

theorem twinChen_bounded_mass_of_dirichletGRH {η δ ε : ℝ}
    (hη : 0<η) (hη' : η<1/6) (hδ : 0<δ) (hδ' : δ<1/8)
    (hGRH : DirichletGRH) (hε : 0<ε) :
    ∀ᶠ M : ℕ in atTop, ∀ r b : ℕ, 0<r → (r:ℝ)≤(M:ℝ)^δ → (b+2).Coprime r →
      ((twinChenBoundedCarrier η M r b).card:ℝ)≤
        (2*Real.log (1/(1-2*η))+ε)*chenAPMassScale M r := by
  filter_upwards [chen_ap_balanced_product_mass_of_dirichletGRH hη hη' hδ hδ' hGRH hε]
    with M h r b hr hpow hb
  simpa only [twinChenBoundedCarrier,twinChenAPBalancedB_card_eq_pair_filter,
    chenAPBalancedB_card_eq_pair_filter] using h r (b+2) hr hpow hb

theorem twinChen_classic_mass_unconditional {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ M : ℕ in atTop, ∀ b : ℕ,
      ((twinChenClassicCarrier M 1 b).card:ℝ)≤(chenSwitchIntegral+ε)*chenAPMassScale M 1 := by
  filter_upwards [chen_switching_mass_of_pnt primeCounting_ratio_unconditional ε hε] with M h b
  simpa [twinChenClassicCarrier,twinChenAPUnrestrictedB_card_eq_pair_filter,
    Nat.mod_one,chenAPMassScale,chenUnrestrictedB_card_eq_pairs] using h

theorem twinChen_bounded_mass_unconditional {η ε : ℝ}
    (hη : 0<η) (hη' : η<1/6) (hε : 0<ε) :
    ∀ᶠ M : ℕ in atTop, ∀ b : ℕ,
      ((twinChenBoundedCarrier η M 1 b).card:ℝ)≤
        (2*Real.log (1/(1-2*η))+ε)*chenAPMassScale M 1 := by
  filter_upwards [chen_balanced_mass_unconditional hη hη' hε] with M h b
  simpa [twinChenBoundedCarrier,twinChenAPBalancedB_card_eq_pair_filter,
    Nat.mod_one,chenAPMassScale,chenBalancedB_card_eq_pairs] using h

end FareyGoldbach
