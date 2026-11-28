import FareyGoldbach.PrimeSums
import FareyGoldbach.QuarticMellin

/-! # The normalized triangular window and its squared-sinc Fourier coefficient -/

open MeasureTheory Real Complex
open scoped Classical

namespace FareyGoldbach

/-- The compact triangular window of mass one and radius `η > 0`. -/
noncomputable def triangleWindow (η t : ℝ) : ℝ := max 0 (1-|t|/η)/η

/-- Fourier transform of the triangle, with the project's `e(x)=exp(2πix)` convention. -/
noncomputable def triangleFrequency (η u : ℝ) : ℝ := (Real.sinc (Real.pi*η*u))^2

theorem continuous_triangleWindow (η : ℝ) : Continuous (triangleWindow η) := by
  unfold triangleWindow; fun_prop

theorem triangleWindow_nonneg {η : ℝ} (hη : 0<η) (t : ℝ) : 0 ≤ triangleWindow η t :=
  div_nonneg (le_max_left ..) hη.le

theorem triangleWindow_le {η : ℝ} (hη : 0<η) (t : ℝ) : triangleWindow η t ≤ 1/η := by
  exact div_le_div_of_nonneg_right (max_le zero_le_one (sub_le_self _ (div_nonneg (abs_nonneg _) hη.le))) hη.le

theorem triangleWindow_eq_of_abs_le {η t : ℝ} (hη : 0<η) (ht : |t|≤η) :
    triangleWindow η t = (1-|t|/η)/η := by
  unfold triangleWindow
  rw [max_eq_right (sub_nonneg.mpr ((div_le_one hη).2 ht))]

theorem triangleWindow_neg (η t : ℝ) : triangleWindow η (-t) = triangleWindow η t := by
  simp [triangleWindow]

theorem triangleFrequency_nonneg (η u : ℝ) : 0 ≤ triangleFrequency η u := sq_nonneg _

theorem triangleFrequency_le_one (η u : ℝ) : triangleFrequency η u ≤ 1 := by
  have h := pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sinc_le_one (Real.pi*η*u)) 2
  simpa only [triangleFrequency,sq_abs,one_pow] using h

theorem triangleFrequency_near {η u : ℝ} (hη : 0<η) (hu : |u| ≤ 1/(2*η)) :
    1/4 ≤ triangleFrequency η u := by
  let t := Real.pi*η*u
  have ht : |t| ≤ Real.pi/2 := by
    dsimp [t]; rw [abs_mul, abs_of_pos (mul_pos Real.pi_pos hη)]
    refine (mul_le_mul_of_nonneg_left hu (by positivity)).trans_eq ?_
    field_simp
  have he : Real.sinc |t| = Real.sinc t := by
    rcases le_total 0 t with h|h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, Real.sinc_neg]
  change (1:ℝ)/4 ≤ (Real.sinc t)^2
  rw [←he]
  by_cases hz : |t|=0
  · rw [hz,Real.sinc_zero]; norm_num
  have hpos := lt_of_le_of_ne (abs_nonneg t) (Ne.symm hz)
  have hs := Real.mul_le_sin hpos.le ht
  rw [Real.sinc_of_ne_zero hz]
  have hlow : 1/2 ≤ Real.sin |t| / |t| := by
    apply (le_div_iff₀ hpos).2
    apply le_trans _ hs
    apply mul_le_mul_of_nonneg_right _ hpos.le
    rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_four]
  have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) hlow 2
  norm_num at h; exact h

theorem triangleFrequency_decay {η u : ℝ} (hη : 0<η) (hu : u≠0) :
    triangleFrequency η u ≤ 1/(η*|u|)^2 := by
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hηu : 0<η*|u| := mul_pos hη (abs_pos.mpr hu)
  have ht : Real.pi*η*u ≠ 0 := mul_ne_zero (mul_ne_zero Real.pi_ne_zero hη.ne') hu
  unfold triangleFrequency
  rw [Real.sinc_of_ne_zero ht,← sq_abs, abs_div,abs_mul, abs_of_pos (mul_pos Real.pi_pos hη)]
  have hden : η*|u| ≤ Real.pi*η*|u| := by
    nlinarith only [mul_le_mul_of_nonneg_right hpi hηu.le]
  have h := div_le_div₀ zero_le_one (Real.abs_sin_le_one (Real.pi*η*u)) hηu hden
  simpa only [div_pow,one_pow] using pow_le_pow_left₀ (by positivity) h 2

private lemma triangle_exp_pair (u : ℝ) : e (-u)+e u = ((2*Real.cos (2*Real.pi*u):ℝ):ℂ) := by
  have he (z : ℝ) : e z = Complex.exp (((2*Real.pi*z:ℝ):ℂ)*Complex.I) := by
    unfold e; push_cast; rfl
  rw [he,he,show 2*Real.pi*(-u) = -(2*Real.pi*u) by ring,Complex.ofReal_neg,
    Complex.exp_mul_I,Complex.exp_mul_I,Complex.cos_neg,Complex.sin_neg]
  push_cast
  ring

private lemma triangle_cos_integral (η c : ℝ) (hc : c≠0) :
    (∫ t in (0:ℝ)..η, (η-t)*Real.cos (c*t)) = (1-Real.cos (c*η))/c^2 := by
  let F (t : ℝ) := (η-t)*Real.sin (c*t)/c - Real.cos (c*t)/c^2
  have hD (t : ℝ) : HasDerivAt F ((η-t)*Real.cos (c*t)) t := by
    have ht : HasDerivAt (fun x : ℝ => c*x) c t := by
      simpa only [id_eq,mul_one] using! (hasDerivAt_id t).const_mul c
    have h₁ := (Real.hasDerivAt_sin _).comp t ht
    have h₂ := (Real.hasDerivAt_cos _).comp t ht
    have h₃ := ((hasDerivAt_const t η).sub (hasDerivAt_id t)).mul h₁
    have hfull := (h₃.div_const c).sub (h₂.div_const (c^2))
    change HasDerivAt F (((0-1)*Real.sin (c*t)+(η-t)*(Real.cos (c*t)*c))/c -
      (-Real.sin (c*t)*c)/c^2) t at hfull
    convert hfull using 1
    field_simp; ring
  have hint : IntervalIntegrable (fun t : ℝ => (η-t)*Real.cos (c*t)) volume 0 η :=
    (show Continuous _ by fun_prop).intervalIntegrable ..
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hD t) hint]
  simp [F]; ring

/-- Exact Fourier coefficient for every real center, including zero. -/
theorem triangleWindow_fourier {η : ℝ} (hη : 0<η) (u : ℝ) :
    (∫ t in -η..η, (triangleWindow η t : ℂ)*e (u*t)) = (triangleFrequency η u : ℂ) := by
  let F (t : ℝ) := (triangleWindow η t : ℂ)*e (u*t)
  let c := 2*Real.pi*u
  have hF : Continuous F :=
    (Complex.continuous_ofReal.comp (continuous_triangleWindow η)).mul
      (continuous_e_real.comp (continuous_const.mul continuous_id))
  change (∫ t in -η..η, F t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (0:ℝ))
    (hF.intervalIntegrable ..) (hF.intervalIntegrable ..)]
  have hneg : (∫ t in (0:ℝ)..η, F (-t)) = ∫ t in -η..0,F t := by
    simpa only [neg_zero] using intervalIntegral.integral_comp_neg F (a:=0) (b:=η)
  rw [←hneg,←intervalIntegral.integral_add (f:=fun t : ℝ => F (-t)) (g:=F)
    ((hF.comp continuous_neg).intervalIntegrable ..) (hF.intervalIntegrable ..)]
  calc _ = ∫ t in (0:ℝ)..η, ((2/η^2*((η-t)*Real.cos (c*t)):ℝ):ℂ) := by
           apply intervalIntegral.integral_congr
           intro t ht
           rw [Set.uIcc_of_le hη.le] at ht
           have ha : |t|≤η := by rw [abs_of_nonneg ht.1]; exact ht.2
           dsimp only [F]
           rw [triangleWindow_neg,←mul_add, mul_neg,triangle_exp_pair,
             triangleWindow_eq_of_abs_le hη ha,abs_of_nonneg ht.1, ←Complex.ofReal_mul]
           apply congrArg Complex.ofReal
           dsimp [c]
           rw [mul_assoc (2*Real.pi) u t]
           field_simp
       _ = _ := by
         rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul]
         apply congrArg Complex.ofReal
         by_cases hu : u=0
         · subst u
           simp only [c, mul_zero,zero_mul,Real.cos_zero,mul_one,triangleFrequency,Real.sinc_zero,one_pow]
           rw [intervalIntegral.integral_sub (f:=fun _ : ℝ => η) (g:=fun t:ℝ => t) (continuous_const.intervalIntegrable ..) (continuous_id.intervalIntegrable ..),
             intervalIntegral.integral_const,integral_id]
           simp only [sub_zero,smul_eq_mul,zero_pow (by decide : 2≠0)]
           field_simp; ring
         · have hc : c≠0 := mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hu
           have hz : Real.pi*η*u≠0 := mul_ne_zero (mul_ne_zero Real.pi_ne_zero hη.ne') hu
           rw [triangle_cos_integral η c hc,show c*η=2*(Real.pi*η*u) by dsimp [c]; ring,
             Real.cos_two_mul_eq_one_sub,triangleFrequency,Real.sinc_of_ne_zero hz]
           dsimp [c]; field_simp; ring

end FareyGoldbach
