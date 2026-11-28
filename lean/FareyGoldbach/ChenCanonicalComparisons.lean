import FareyGoldbach.ChenCanonicalNormalization
import FareyGoldbach.ChenMediumReciprocal
import FareyGoldbach.ChenRosserNormalization

/-! # The arithmetic factors for the Chen Rosser comparisons -/

open Filter Set
open scoped Topology

namespace FareyGoldbach

theorem chenCanonicalU_eventually_ge_half :
    ∀ᶠ N in chenEvenAtTop, (1:ℝ)/2 ≤ chenCanonicalU N := by
  apply eventually_inf_principal.mpr
  filter_upwards [eventually_ge_atTop (2:ℕ)] with N hN hE
  exact chenCanonicalU_ge_half hE hN

theorem chenCanonicalCutoffNormalization : ChenCutoffNormalization chenCanonicalU := by
  have h (a : ℝ) (ha : 0<a) (ha' : a≤1) :
      Tendsto (chenLocalNormalized chenCanonicalU a) chenEvenAtTop
        (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    apply eventually_inf_principal.mpr
    filter_upwards [chenDensityProduct_cutoff_normalized ha ha' (ε/2) (by positivity)] with N hN he
    rw [Real.dist_eq, chenLocalNormalized, mul_comm (chenDensityProduct _ _)]
    exact (hN he).trans_lt (half_lt_self hε)
  exact ⟨h _ (by norm_num) (by norm_num), h _ (by norm_num) (by norm_num)⟩

theorem chenRosserMainComparisons_of_floorProfiles {θ : ℝ}
    (hθ : 11/24<θ) (hθ₂ : θ<1/2) (hP : ChenFloorRosserProfiles θ) :
    ChenRosserMainComparisons θ chenCanonicalU := by
  apply chenRosserMainComparisons_of_profiles hθ hθ₂ _ chenCanonicalU_eventually_ge_half
    chenCanonicalCutoffNormalization hP
  exact chen_medium_reciprocal_tendsto (by linarith)

end FareyGoldbach
