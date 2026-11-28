import FareyGoldbach.PrimeNumberTheoremReduction
import FareyGoldbach.SiegelWalfisz

/-! # The prime number theorem and uniform prime twists for small conductors -/

open Filter
open scoped Topology

namespace FareyGoldbach

theorem primeCounting_ratio_unconditional :
    Tendsto (fun N : ℕ => (N.primeCounting:ℝ)/((N:ℝ)/Real.log (N:ℝ))) atTop (𝓝 1) :=
  primeCounting_ratio_of_smallConductorMangoldt unconditional_smallConductor_vonMangoldt

theorem smallConductorPrimeTwists_unconditional : SmallConductorPrimeTwists :=
  smallConductorPrimeTwists_of_smallConductorMangoldt unconditional_smallConductor_vonMangoldt

end FareyGoldbach
