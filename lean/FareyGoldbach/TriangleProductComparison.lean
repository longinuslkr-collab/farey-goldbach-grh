import FareyGoldbach.OddPrimeTriangleCoefficient
import FareyGoldbach.TriangleContinuousModel

/-! # The product comparison on the single principal arc -/

open MeasureTheory Set

namespace FareyGoldbach

private theorem triangle_model_l2 {r Y : ℕ} (hr : 0<r) (hrY : r≤Y) (hY : 1≤Y) (b : ℕ)
    {η : ℝ} (hη : 0<η) (hηh : η≤1/2) :
    (∫ t in -η..η, ‖triangleQOneModel r b Y t‖^2) ≤
      4096*((r:ℝ)/r.totient)^2*((Y:ℝ)/r) := by
  let H := (Y:ℝ)/r
  let κ := (r:ℝ)/r.totient
  let U := shortContKernel r b Y
  let F := fun t : ℝ => ‖U t‖^2
  let G := fun t : ℝ => (1+H*|t|)*F t
  have hc : Continuous F := (continuous_shortContKernel hY r b).norm.pow _
  have hg : Continuous G := (continuous_const.add (continuous_const.mul continuous_abs)).mul hc
  have hn (t : ℝ) : 0≤G t := by dsimp [G,F,H]; positivity
  have he (t : ℝ) : ‖triangleQOneModel r b Y t‖^2 = κ^2*F t := by
    unfold triangleQOneModel
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity),mul_pow]
  have ha : -η≤η := by linarith only [hη]
  have ⟨hs,ht⟩ : -(1/2:ℝ)≤-η ∧ η≤1/2 := ⟨neg_le_neg hηh,hηh⟩
  have hF : (∫ t in -η..η, F t) ≤ 4096*H := by
    calc
      _ ≤ ∫ t in -η..η, G t := intervalIntegral.integral_mono_on ha
        (hc.intervalIntegrable ..) (hg.intervalIntegrable ..) (fun t _ => by
          dsimp [G]; exact le_mul_of_one_le_left (sq_nonneg _) (le_add_of_nonneg_right (by dsimp [H]; positivity)))
      _ ≤ ∫ t in -(1/2:ℝ)..1/2, G t := intervalIntegral.integral_mono_interval hs ha ht
        (Filter.Eventually.of_forall hn) (hg.intervalIntegrable ..)
      _ ≤ _ := shortContKernel_weighted_l2 hr hrY hY b
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  exact (mul_le_mul_of_nonneg_left hF (sq_nonneg κ)).trans_eq (by ring)

private theorem triangle_product_norm_le (S₁ S₂ M₁ M₂ : ℂ) :
    ‖S₁*S₂-M₁*M₂‖ ≤
      ((2:ℝ)^34+1)/2*(‖S₁-M₁‖^2+‖S₂-M₂‖^2) +
      (1/(2:ℝ)^35)*(‖M₁‖^2+‖M₂‖^2) := by
  let R₁ := S₁-M₁
  let R₂ := S₂-M₂
  have he : S₁*S₂-M₁*M₂=R₁*R₂+R₁*M₂+M₁*R₂ := by dsimp [R₁,R₂]; ring
  rw [he]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add_left (norm_add_le (R₁*R₂) (R₁*M₂)) _).trans ?_
  simp only [norm_mul]
  change ‖R₁‖*‖R₂‖+‖R₁‖*‖M₂‖+‖M₁‖*‖R₂‖ ≤
    ((2:ℝ)^34+1)/2*(‖R₁‖^2+‖R₂‖^2)+(1/(2:ℝ)^35)*(‖M₁‖^2+‖M₂‖^2)
  have h0 := sq_nonneg (‖R₁‖-‖R₂‖)
  have h1 := sq_nonneg ((2:ℝ)^34*‖R₁‖-‖M₂‖)
  have h2 := sq_nonneg ((2:ℝ)^34*‖R₂‖-‖M₁‖)
  nlinarith only [h0,h1,h2]

/-- An error of at most half the principal-arc lower bound, uniformly in the
center. The hypotheses are integral bounds on the two individual remainders. -/
theorem triangle_prime_model_norm_sub_le (P : Progressions) {Y : ℕ}
    (hrY : P.r≤Y) (hY : 1≤Y) {η : ℝ} (hη : 0<η) (hηh : η≤1/2)
    (hR₁ : (∫ t in -η..η, ‖oddPrimeWindowSum P.r P.b₁ Y t-triangleQOneModel P.r P.b₁ Y t‖^2) ≤
      1/(2:ℝ)^60*((P.r:ℝ)/P.r.totient)^2*((Y:ℝ)/P.r))
    (hR₂ : (∫ t in -η..η, ‖oddPrimeWindowSum P.r P.b₂ Y t-triangleQOneModel P.r P.b₂ Y t‖^2) ≤
      1/(2:ℝ)^60*((P.r:ℝ)/P.r.totient)^2*((Y:ℝ)/P.r))
    (x : ℝ) :
    ‖trianglePrimeCoefficient P Y η x-triangleModelCoefficient P.r P.b₁ P.b₂ Y η x‖ ≤
      (1/65536:ℝ)*η⁻¹*((P.r:ℝ)/P.r.totient)^2*((Y:ℝ)/P.r) := by
  let E := ((P.r:ℝ)/P.r.totient)^2*((Y:ℝ)/P.r)
  let S₁ := oddPrimeWindowSum P.r P.b₁ Y
  let S₂ := oddPrimeWindowSum P.r P.b₂ Y
  let M₁ := triangleQOneModel P.r P.b₁ Y
  let M₂ := triangleQOneModel P.r P.b₂ Y
  let f₁ := fun t => ‖S₁ t-M₁ t‖^2
  let f₂ := fun t => ‖S₂ t-M₂ t‖^2
  let g₁ := fun t => ‖M₁ t‖^2
  let g₂ := fun t => ‖M₂ t‖^2
  let a := ((2:ℝ)^34+1)/2
  let b := 1/(2:ℝ)^35
  let f := fun t => (triangleWindow η t:ℂ)*(S₁ t*S₂ t*e (-(x*t)))
  let g := fun t => (triangleWindow η t:ℂ)*(M₁ t*M₂ t*e (-(x*t)))
  have hcS₁ : Continuous S₁ := continuous_oddPrimeWindowSum ..
  have hcS₂ : Continuous S₂ := continuous_oddPrimeWindowSum ..
  have hcM₁ : Continuous M₁ := continuous_const.mul (continuous_shortContKernel hY _ _)
  have hcM₂ : Continuous M₂ := continuous_const.mul (continuous_shortContKernel hY _ _)
  have hcf₁ : Continuous f₁ := (hcS₁.sub hcM₁).norm.pow _
  have hcf₂ : Continuous f₂ := (hcS₂.sub hcM₂).norm.pow _
  have hcg₁ : Continuous g₁ := hcM₁.norm.pow _
  have hcg₂ : Continuous g₂ := hcM₂.norm.pow _
  have hcW := Complex.continuous_ofReal.comp (continuous_triangleWindow η)
  have hcE : Continuous (fun t : ℝ => e (-(x*t))) := continuous_e_real.comp (continuous_const.mul continuous_id).neg
  have hcf : Continuous f := hcW.mul ((hcS₁.mul hcS₂).mul hcE)
  have hcg : Continuous g := hcW.mul ((hcM₁.mul hcM₂).mul hcE)
  have hμ : 0≤η⁻¹ := inv_nonneg.mpr hη.le
  have hab : -η≤η := by linarith only [hη]
  have hpoint (t : ℝ) : ‖f t-g t‖ ≤ η⁻¹*(a*(f₁ t+f₂ t)+b*(g₁ t+g₂ t)) := by
    have he : f t-g t=(triangleWindow η t:ℂ)*((S₁ t*S₂ t-M₁ t*M₂ t)*e (-(x*t))) := by
      dsimp only [f,g]; ring
    rw [he,norm_mul,norm_mul,norm_e,mul_one,Complex.norm_real,
      Real.norm_of_nonneg (triangleWindow_nonneg hη _)]
    exact mul_le_mul (by simpa only [one_div] using triangleWindow_le hη t)
      (triangle_product_norm_le ..) (norm_nonneg _) hμ
  have hcmajor : Continuous (fun t => η⁻¹*(a*(f₁ t+f₂ t)+b*(g₁ t+g₂ t))) :=
    continuous_const.mul ((continuous_const.mul (hcf₁.add hcf₂)).add
      (continuous_const.mul (hcg₁.add hcg₂)))
  change ‖(∫ t in -η..η,f t)-(∫ t in -η..η,g t)‖≤_
  rw [← intervalIntegral.integral_sub (hcf.intervalIntegrable ..) (hcg.intervalIntegrable ..)]
  refine (intervalIntegral.norm_integral_le_integral_norm hab).trans
    ((intervalIntegral.integral_mono_on hab ((hcf.sub hcg).norm.intervalIntegrable ..)
      (hcmajor.intervalIntegrable ..) (fun t _ => hpoint t)).trans ?_)
  have hfa : IntervalIntegrable (fun t => a*(f₁ t+f₂ t)) volume (-η) η :=
    (continuous_const.mul (hcf₁.add hcf₂)).intervalIntegrable ..
  have hga : IntervalIntegrable (fun t => b*(g₁ t+g₂ t)) volume (-η) η :=
    (continuous_const.mul (hcg₁.add hcg₂)).intervalIntegrable ..
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add hfa hga,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hcf₁.intervalIntegrable ..) (hcf₂.intervalIntegrable ..),
    intervalIntegral.integral_add (hcg₁.intervalIntegrable ..) (hcg₂.intervalIntegrable ..)]
  have hm₁ : (∫ t in -η..η,g₁ t) ≤ 4096*E := by
    simpa only [g₁,M₁,E,mul_assoc] using triangle_model_l2 P.r_pos hrY hY P.b₁ hη hηh
  have hm₂ : (∫ t in -η..η,g₂ t) ≤ 4096*E := by
    simpa only [g₂,M₂,E,mul_assoc] using triangle_model_l2 P.r_pos hrY hY P.b₂ hη hηh
  have hn₁ : (∫ t in -η..η,f₁ t)≤1/(2:ℝ)^60*E := by
    simpa only [f₁,S₁,M₁,E,mul_assoc] using hR₁
  have hn₂ : (∫ t in -η..η,f₂ t)≤1/(2:ℝ)^60*E := by
    simpa only [f₂,S₂,M₂,E,mul_assoc] using hR₂
  have hE : 0≤E := by dsimp [E]; positivity
  suffices h : a*((∫ t in -η..η,f₁ t)+∫ t in -η..η,f₂ t)+
      b*((∫ t in -η..η,g₁ t)+∫ t in -η..η,g₂ t) ≤ (1/65536:ℝ)*E by
    exact (mul_le_mul_of_nonneg_left h hμ).trans_eq (by dsimp [E]; ring)
  dsimp only [a,b]
  linarith only [hn₁,hn₂,hm₁,hm₂,hE]

end FareyGoldbach
