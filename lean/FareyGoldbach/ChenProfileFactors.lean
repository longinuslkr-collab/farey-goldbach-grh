import FareyGoldbach.ChenConditionalMargin
import FareyGoldbach.LinearSieveFactors

/-! # Linear-sieve profiles at the physical Chen cutoffs -/

open MeasureTheory Set

namespace FareyGoldbach

/-- The three arguments are all in the ranges of the first explicit f/F branches. -/
theorem chen_profile_arguments_mem {θ : ℝ} (hθ : 11/24<θ) (hhalf : θ≤1/2) :
    8*θ ∈ Icc 2 4 ∧ 3*θ ∈ Icc 1 3 ∧ ∀ u ∈ Icc (1/8:ℝ) (1/3), 8*(θ-u) ∈ Icc 1 3 := by
  refine ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩,?_⟩
  intro u hu
  exact ⟨by linarith [hu.2],by linarith [hu.1]⟩

/-- Cancellation of the Mertens factor in the main lower sieve at log z / log N = 1/8. -/
theorem chen_lower_profile_eq {θ : ℝ} (hθ : 11/24<θ) :
    8*Real.exp (-Real.eulerMascheroniConstant)*linearSieveLowerFactor (8*θ) = chenLowerMainCoeff θ := by
  have hθ₀ : 0<θ := by linarith
  unfold chenLowerMainCoeff linearSieveLowerFactor
  rw [Real.exp_neg]
  field_simp

/-- Integration of the upper profile for the medium prime, including its 1/u density. -/
theorem chen_medium_profile_eq {θ : ℝ} (hθ : 11/24<θ) :
    (8*Real.exp (-Real.eulerMascheroniConstant)) *
      (∫ u in (1/8:ℝ)..1/3, linearSieveUpperFactor (8*(θ-u))/u) = chenMediumMainCoeff θ := by
  rw [←intervalIntegral.integral_const_mul,←chen_medium_integral_eq (by linarith : 1/3<θ)]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le (by norm_num : (1/8:ℝ)≤1/3)] at hu
  have h₀ : 0<u := by linarith [hu.1]
  have h₁ : 0<θ-u := by linarith [hu.2]
  unfold linearSieveUpperFactor
  rw [Real.exp_neg]
  field_simp

/-- The switched mass multiplies the upper profile at log y / log N = 1/3. -/
theorem chen_switched_profile_eq {θ : ℝ} (hθ : 11/24<θ) :
    3*Real.exp (-Real.eulerMascheroniConstant)*chenSwitchIntegral*linearSieveUpperFactor (3*θ) =
      chenSwitchedMainCoeff θ := by
  have hθ₀ : 0<θ := by linarith
  unfold chenSwitchedMainCoeff linearSieveUpperFactor
  rw [Real.exp_neg]
  field_simp

end FareyGoldbach
