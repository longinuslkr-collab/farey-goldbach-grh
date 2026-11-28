import FareyGoldbach.ChenSwitchingMass
import FareyGoldbach.ChenSwitchingRemainder

/-! # Distribution of the switched sequence from the two analytic inputs -/

open Filter
open scoped Topology

namespace FareyGoldbach

theorem chenSwitchingDistribution_of_pnt_and_smallConductor
    (hPNT : Tendsto (fun N : ℕ => (N.primeCounting:ℝ)/((N:ℝ)/Real.log (N:ℝ))) atTop (𝓝 1))
    (hSmall : SmallConductorPrimeTwists) : ChenSwitchingDistribution := by
  intro θ hθ hh
  exact ⟨fun ε hε => (chen_switching_mass_of_pnt hPNT ε hε).mono (fun _ hm _ => hm),
    fun ε hε => (chen_switching_reduced_error_of_smallConductor hSmall hθ hh ε hε).mono
      (fun _ hm _ => hm)⟩

end FareyGoldbach
