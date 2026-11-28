import FareyGoldbach.ChenPrimeAPDistributionOfSmallConductor
import FareyGoldbach.ChenSwitchingDistribution
import FareyGoldbach.ChenUnconditionalComparisons

/-! # Chen's theorem from the prime number theorem and small-conductor twists -/

open Filter
open scoped Topology

namespace FareyGoldbach

theorem chen_count_lower_of_pnt_and_smallConductor
    (hPNT : Tendsto (fun N : ℕ => (N.primeCounting:ℝ)/((N:ℝ)/Real.log (N:ℝ))) atTop (𝓝 1))
    (hSmall : SmallConductorPrimeTwists) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop, Even N →
        c*(N:ℝ)/Real.log (N:ℝ)^2 ≤ (chenCount N:ℝ) :=
  chen_count_lower_of_distributions (chenPrimeAPDistribution_of_pnt_and_smallConductor hPNT hSmall)
    (chenSwitchingDistribution_of_pnt_and_smallConductor hPNT hSmall)

theorem chen_theorem_of_pnt_and_smallConductor
    (hPNT : Tendsto (fun N : ℕ => (N.primeCounting:ℝ)/((N:ℝ)/Real.log (N:ℝ))) atTop (𝓝 1))
    (hSmall : SmallConductorPrimeTwists) :
    ∀ᶠ N : ℕ in atTop, Even N → ∃ p m : ℕ, p.Prime ∧ IsAlmostPrimeTwo m ∧ p+m=N :=
  chen_theorem_of_distributions (chenPrimeAPDistribution_of_pnt_and_smallConductor hPNT hSmall)
    (chenSwitchingDistribution_of_pnt_and_smallConductor hPNT hSmall)

end FareyGoldbach
