import FareyGoldbach.ChenConditionalMargin

/-! # Explicit distribution exponents and margins for Chen representations -/

namespace FareyGoldbach

/-- The three sieve coefficients have a common denominator. -/
theorem chen_main_margin_log_product {θ : ℝ} (hθ : 1/3<θ) :
    chenMainMargin θ = (Real.log ((8*θ-1)*(3*θ-1))-chenSwitchIntegral)/θ := by
  have ha : 0<8*θ-1 := by linarith only [hθ]
  have hb : 0<3*θ-1 := by linarith only [hθ]
  unfold chenMainMargin chenLowerMainCoeff chenMediumMainCoeff chenSwitchedMainCoeff
  rw [Real.log_div ha.ne' hb.ne', Real.log_mul ha.ne' hb.ne']
  ring

private theorem margin_cert {θ η : ℝ} (hθ : 1/3<θ) (hη : 0<1-2*η)
    (hv : 0≤(8*θ-1)*(3*θ-1)-1)
    (hcert : let x := (8*θ-1)*(3*θ-1)-1
             4*(1/(1-2*η)-1)+367226/1000000 < x-x^2/2+x^3/3-x^4/4+x^5/5-x^6/6) :
    (2/θ)*(2*Real.log (1/(1-2*η))) < chenMainMargin θ := by
  have hθ₀ : 0<θ := by linarith only [hθ]
  have lower := chen_log_lower_six hv
  rw [show 1+((8*θ-1)*(3*θ-1)-1)=(8*θ-1)*(3*θ-1) by ring] at lower
  have upper := Real.log_le_sub_one_of_pos (one_div_pos.mpr hη)
  rw [chen_main_margin_log_product hθ,lt_div_iff₀ hθ₀]
  rw [show 2/θ*(2*Real.log (1/(1-2*η)))*θ=4*Real.log (1/(1-2*η)) by field_simp; ring]
  dsimp only at hcert
  linarith only [lower,upper,hcert,chenSwitchIntegral_le_refined]

theorem chen_main_margin_4959_pos : 0<chenMainMargin (4959/10000) := by
  simpa only [mul_zero,sub_zero,div_one,Real.log_one] using
    margin_cert (θ:=4959/10000) (η:=0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Margin after removing the small-factor pairs, at the fixed GRH parameters. -/
theorem chen_margin_gt_balanced_loss_grh :
    (2/((499:ℝ)/1000))*(2*Real.log (1/(1-2*((7:ℝ)/2000)))) < chenMainMargin (499/1000) :=
  margin_cert (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Margin after removing the small-factor pairs, for modulus one. -/
theorem chen_margin_gt_balanced_loss_unconditional :
    (2/((4999:ℝ)/10000))*(2*Real.log (1/(1-2*((9:ℝ)/2000)))) < chenMainMargin (4999/10000) :=
  margin_cert (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end FareyGoldbach
