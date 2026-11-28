import FareyGoldbach.ContinuousShortModel
import FareyGoldbach.QuarterContourPlancherel

/-! # Weighted square energy of the continuous Farey kernel -/

open MeasureTheory Set Complex
open scoped FourierTransform

namespace FareyGoldbach

private lemma unit_supported_l2 {f : ℝ → ℂ} (hf : Measurable f) {A : ℝ}
    (ha : ∀ x, ‖f x‖ ≤ A) (hz : ∀ x ∉ Icc (0:ℝ) 1, f x=0) :
    MemLp f 2 ∧ (∫ x, ‖f x‖^2) ≤ A^2 := by
  have hsq (x : ℝ) : ‖f x‖^2≤A^2 := pow_le_pow_left₀ (norm_nonneg _) (ha x) 2
  have hInt : Integrable (fun x => ‖f x‖^2) :=
    measurable_integrable_of_bound_Icc (a:=0) (b:=1) (M:=A^2) (hf.norm.pow_const 2)
      (fun x => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hsq x)
      (fun x hx => by simp [hz x hx])
  refine ⟨(memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).2 hInt,?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (0:ℝ) 1)
    (f := fun x => ‖f x‖^2) (fun x hx => by simp [hz x hx])]
  calc _ ≤ ∫ x in Icc (0:ℝ) 1, A^2 := setIntegral_mono_on hInt.integrableOn
            continuous_const.continuousOn.integrableOn_Icc measurableSet_Icc (fun x _ => hsq x)
    _ = A^2 := by simp [Real.volume_real_Icc]

private lemma quartic_weighted_fourier_square :
    let w := fun x : ℝ => (quarticBump x : ℂ)
    Integrable (fun u => (1+|u|)*‖𝓕 w u‖^2) ∧
      (∫ u, (1+|u|)*‖𝓕 w u‖^2) ≤ 66 := by
  intro w
  have hwc : Continuous w := Complex.continuous_ofReal.comp continuous_quarticBump
  have hwd (x : ℝ) : HasDerivAt w (quarticBumpDeriv x : ℂ) x := (hasDerivAt_quarticBump x).ofReal_comp
  have hw0 (x : ℝ) (hx : x ∉ Icc (0:ℝ) 1) : w x=0 := by
    dsimp [w]; rw [quarticBump_eq_zero_of_not_mem (fun h => hx ⟨h.1.le,h.2.le⟩),Complex.ofReal_zero]
  have hw1 (x : ℝ) : ‖w x‖≤1 := by
    dsimp [w]; rw [Complex.norm_real,Real.norm_of_nonneg (quarticBump_nonneg x)]
    exact quarticBump_le_one x
  let g := deriv w
  have hg0 (x : ℝ) (hx : x ∉ Icc (0:ℝ) 1) : g x=0 := by
    have h : ¬(0<x ∧ x<1) := fun h => hx ⟨h.1.le,h.2.le⟩
    simp [g,(hwd x).deriv,quarticBumpDeriv,h]
  have hg8 (x : ℝ) : ‖g x‖≤8 := by
    apply norm_deriv_le_of_lip' (by norm_num)
    filter_upwards with y
    simpa [w,← Complex.ofReal_sub,Real.norm_eq_abs] using quarticBump_lipschitz y x
  have hgm : Measurable g := measurable_deriv _
  obtain ⟨hw₂,hwen⟩ := unit_supported_l2 hwc.measurable hw1 hw0
  obtain ⟨hg₂,hgen⟩ := unit_supported_l2 hgm hg8 hg0
  have hw₁ := measurable_integrable_of_bound_Icc hwc.measurable hw1 hw0
  have hg₁ := measurable_integrable_of_bound_Icc hgm hg8 hg0
  have hder : 𝓕 g = fun u : ℝ => (2 * (Real.pi:ℂ) * Complex.I * (u:ℂ)) • (𝓕 w u) :=
    Real.fourier_deriv hw₁ (fun x => (hwd x).differentiableAt) hg₁
  let F (u : ℝ) := (1+|u|)*‖𝓕 w u‖^2
  let M (u : ℝ) := 2*‖𝓕 w u‖^2+‖𝓕 g u‖^2
  have hF₀ (u : ℝ) : 0≤F u := by dsimp [F]; positivity
  have hpt (u : ℝ) : F u ≤ M u := by
    have hp : 1≤2*Real.pi := by linarith [Real.pi_gt_three]
    have hnorm : ‖𝓕 g u‖ = 2*Real.pi* |u| *‖𝓕 w u‖ := by
      rw [hder]
      simp only [smul_eq_mul,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,
        Real.norm_eq_abs,abs_of_pos Real.pi_pos]
      norm_num
    have hu : |u| *‖𝓕 w u‖≤‖𝓕 g u‖ := by
      rw [hnorm]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hp (abs_nonneg u)) (norm_nonneg (𝓕 w u))
    have hs := pow_le_pow_left₀ (by positivity) hu 2
    rw [mul_pow] at hs
    have hk : |u|≤1+|u|^2 := by nlinarith only [sq_nonneg (|u|-(1/2:ℝ))]
    have hm := mul_le_mul_of_nonneg_right hk (sq_nonneg ‖𝓕 w u‖)
    dsimp [F,M]
    nlinarith only [hs,hm]
  have hm : Integrable M := ((integrable_fourier_norm_sq hw₁ hw₂).const_mul 2).add
    (integrable_fourier_norm_sq hg₁ hg₂)
  have hwF : Continuous (𝓕 w) := VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hw₁
  have hFc : Continuous F := (continuous_const.add continuous_abs).mul (hwF.norm.pow 2)
  have hf : Integrable F := hm.mono' hFc.aestronglyMeasurable (Filter.Eventually.of_forall fun u => by
    rw [Real.norm_of_nonneg (hF₀ u)]; exact hpt u)
  refine ⟨hf,(integral_mono hf hm hpt).trans ?_⟩
  dsimp [M]
  rw [integral_add ((integrable_fourier_norm_sq hw₁ hw₂).const_mul _) (integrable_fourier_norm_sq hg₁ hg₂),
    integral_const_mul,integral_fourier_norm_sq_eq hw₁ hw₂,integral_fourier_norm_sq_eq hg₁ hg₂]
  linarith only [hwen,hgen]

/-- The first frequency moment of the squared kernel costs only its scale.
The derivative of the compact physical window controls this moment. -/
theorem shortContKernel_weighted_l2 {r Y : ℕ} (hr : 0<r) (_hrY : r≤Y) (hY : 1≤Y) (b:ℕ) :
    (∫ t in (-(1/2):ℝ)..1/2, (1+((Y:ℝ)/r)* |t|)*‖shortContKernel r b Y t‖^2) ≤
      4096*((Y:ℝ)/r) := by
  let w := fun x : ℝ => (quarticBump x : ℂ)
  let H := (Y:ℝ)/r
  let G (u : ℝ) := (1+|u|)*‖𝓕 w u‖^2
  have hH : 0<H := by dsimp [H]; positivity
  have hG (u : ℝ) : 0≤G u := by dsimp [G]; positivity
  obtain ⟨hi,hb⟩ : Integrable G ∧ (∫ u, G u)≤66 := quartic_weighted_fourier_square
  have he (t : ℝ) : (1+H* |t|)*‖shortContKernel r b Y t‖^2 = H^2*G ((-H)*t) := by
    rw [shortContKernel_fourier hY,norm_mul,norm_mul,norm_div,norm_e,mul_one]
    simp only [Complex.norm_natCast]
    have heq : -(t/(r:ℝ)*(Y:ℝ))=(-H)*t := by dsimp [H]; ring
    rw [heq]
    dsimp only [G]
    rw [abs_mul,abs_neg,abs_of_pos hH]
    dsimp [H]; ring
  simp_rw [← show H=(Y:ℝ)/r by rfl,he]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_of_le (by norm_num : (-(1/2):ℝ)≤1/2)]
  have hgc : Integrable (fun t => G ((-H)*t)) := hi.comp_mul_left' (neg_ne_zero.mpr hH.ne')
  have h : (∫ t in Ioc (-(1/2):ℝ) (1/2), G ((-H)*t)) ≤ ∫ t, G ((-H)*t) :=
    setIntegral_le_integral hgc (Filter.Eventually.of_forall fun t => hG ((-H)*t))
  rw [Measure.integral_comp_mul_left,inv_neg,abs_neg,abs_of_pos (inv_pos.mpr hH),smul_eq_mul] at h
  have hb' := (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hH.le))
  calc _ ≤ H^2*(H⁻¹*66) := mul_le_mul_of_nonneg_left (h.trans hb') (sq_nonneg _)
    _ = 66*H := by field_simp
    _ ≤ _ := by linarith only [hH.le]

end FareyGoldbach
