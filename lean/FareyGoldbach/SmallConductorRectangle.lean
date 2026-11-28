import FareyGoldbach.SmallConductorEdges
import FareyGoldbach.ZeroFreeRectangle

/-! # Error bounds for a sharp Perron rectangle at small conductor -/

open Set MeasureTheory
open scoped Interval Classical

namespace FareyGoldbach

/-- The left edge uses the uniform multiplier bound. On each horizontal edge
the product gains three powers of the height from the twice-averaged cutoff. -/
theorem smallConductorRectangle_bound {X d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d)
    {δ η β T M : ℝ} (hX : 2≤X) (hδ : 0<δ) (hδ1 : δ≤1) (hη : 0<η) (hη1 : η≤1/4)
    (hβ : 1<β) (hβ2 : β≤2) (hT : 1≤T) (hM : 0≤M)
    (hz : ∀ s∈Icc (1-η) β ×ℂ Icc (-T) T, entireL χ s≠0)
    (hl : ∀ t∈Icc (-T) T, ‖negLogDerivL χ (((1-η:ℝ):ℂ)+(t:ℂ)*Complex.I)‖≤M)
    (hh : ∀ x∈Icc (1-η) β, ∀ t : ℝ, |t|=T →
      ‖negLogDerivL χ ((x:ℂ)+(t:ℂ)*Complex.I)‖≤M) :
    ‖(2*(Real.pi:ℂ))⁻¹*(∫ t in -T..T, smallConductorKernel X δ ((β:ℂ)+(t:ℂ)*Complex.I)*
      negLogDerivL χ ((β:ℂ)+(t:ℂ)*Complex.I))-
      (if χ=1 then smallConductorKernel X δ 1 else 0)‖ ≤
      50000*((X:ℝ)^(1-η)*M*T+(X:ℝ)^β*M/(δ^2*T^3)) := by
  apply smallConductorRectangle_edge_bounds χ hX hδ hδ1 hη hη1 hβ hβ2 hT hM _ hl hh
  exact zeroFreeRectangle_kernel_identity χ (by linarith) (by linarith) hβ (by linarith)
    (smallConductorKernel X δ) (fun _ hs =>
      (differentiableAt_smallConductorKernel (by omega) δ hs).differentiableWithinAt) hz

end FareyGoldbach
