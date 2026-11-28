import FareyGoldbach.ChenSwitchingDistribution
import FareyGoldbach.ChenPrimeAPDistributionOfGRH

/-! # Chen's theorem from Dirichlet GRH -/

open Filter
open scoped Topology

namespace FareyGoldbach

theorem chenSwitchingDistribution_of_dirichletGRH : DirichletGRH → ChenSwitchingDistribution :=
  fun hGRH => chenSwitchingDistribution_of_pnt_and_smallConductor
    (primeCounting_ratio_of_dirichletGRH hGRH) (smallConductorPrimeTwists_of_dirichletGRH hGRH)

theorem chen_count_lower_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop, Even N →
      c*(N:ℝ)/Real.log (N:ℝ)^2 ≤ (chenCount N:ℝ) :=
  chen_count_lower_of_dirichletGRH_and_switching hGRH (chenSwitchingDistribution_of_dirichletGRH hGRH)

theorem chen_theorem_of_dirichletGRH (hGRH : DirichletGRH) :
    ∀ᶠ N : ℕ in atTop, Even N → ∃ p m : ℕ, p.Prime ∧ IsAlmostPrimeTwo m ∧ p+m=N :=
  chen_theorem_of_dirichletGRH_and_switching hGRH (chenSwitchingDistribution_of_dirichletGRH hGRH)

end FareyGoldbach
