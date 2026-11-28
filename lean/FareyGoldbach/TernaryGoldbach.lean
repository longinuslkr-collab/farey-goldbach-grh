import FareyGoldbach.TernaryFixedClasses
import FareyGoldbach.TernaryAveraged
import FareyGoldbach.TernaryCompatibleAverage
import FareyGoldbach.TernaryPowerRange

/-! # Ternary Goldbach consequences of the binary exceptional-set estimates -/

open Filter
open scoped Topology

namespace FareyGoldbach

/-- For each odd target in the block, the relative number of its failed compatible
class triples tends to zero along any sequence with `r ≤ X^(1-ε)`. -/
theorem ternary_compatible_bad_density_zero_of_subpower_of_dirichletGRH (hGRH : DirichletGRH)
    {ε : ℝ} (hε : 0<ε) (X r n : ℕ→ℕ) (hX : Tendsto X atTop atTop)
    (hlarge : ∀ j,16≤X j) (hr : ∀ j,0<r j) (hrX : ∀ j,r j≤X j)
    (hn : ∀ j,n j∈Finset.Ioc (X j/2) (X j)) (hodd : ∀ j,Odd (n j))
    (hpower : ∀ᶠ j in atTop, (r j:ℝ)≤(X j:ℝ)^(1-ε)) :
    Tendsto (fun j => ((ternaryBadTriples (r j) (n j)).card:ℝ)/
      ((ternaryCompatibleTriples (r j) (n j)).card:ℝ)) atTop (𝓝 0) := by
  apply ternary_compatible_bad_density_zero_of_dirichletGRH hGRH X r n hlarge hr hrX hn hodd
  exact ternary_compatible_budget_tendsto_of_subpower hε X r hX hr hpower

end FareyGoldbach
