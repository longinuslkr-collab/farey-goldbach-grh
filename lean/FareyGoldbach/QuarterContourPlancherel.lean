import FareyGoldbach.LocalSpectralTails
import FareyGoldbach.CompactFourierL2

/-! # The local square integral of the truncated quarter line -/

open Complex Real MeasureTheory Set Filter
open scoped FourierTransform Classical

namespace FareyGoldbach

lemma measurable_integrable_of_bound_Icc {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {f : ℝ → E} (hf : Measurable f) {a b M : ℝ}
    (hbound : ∀ x, ‖f x‖ ≤ M) (hzero : ∀ x ∉ Icc a b, f x = 0) : Integrable f := by
  have hconst : IntegrableOn (fun _ : ℝ => M) (Icc a b) :=
    continuous_const.continuousOn.integrableOn_Icc
  have hlocal : IntegrableOn f (Icc a b) := hconst.mono' hf.aestronglyMeasurable
    (Eventually.of_forall hbound)
  have h := hlocal.integrable_indicator measurableSet_Icc
  convert h using 1
  ext x
  by_cases hx : x ∈ Icc a b
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, hzero x hx]

noncomputable def quarterPhysicalWeight (x : ℝ) : ℝ :=
  quarticBump x * x ^ (-(3 / 4 : ℝ))

private lemma quarterPhysicalWeight_nonneg (x : ℝ) : 0 ≤ quarterPhysicalWeight x := by
  unfold quarterPhysicalWeight
  by_cases hx : 0 < x
  · exact mul_nonneg (quarticBump_nonneg _) (Real.rpow_nonneg hx.le _)
  · simp [quarticBump_eq_zero_of_not_mem (fun h => hx h.1)]

private lemma quarterPhysicalWeight_le (x : ℝ) : quarterPhysicalWeight x ≤ 16 := by
  unfold quarterPhysicalWeight
  by_cases hx : 0 < x ∧ x < 1
  · rw [quarticBump_of_mem hx.1 hx.2]
    have hmul : x^2 * x ^ (-(3 / 4 : ℝ)) = x ^ (5 / 4 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hx.1]; norm_num
    have hpow := Real.rpow_le_one hx.1.le hx.2.le (by norm_num : (0:ℝ) ≤ 5/4)
    have hsq : (1-x)^2 ≤ 1 := by nlinarith only [hx.1,hx.2, mul_nonneg hx.1.le (show 0≤1-x by linarith)]
    calc _ = 16 * x ^ (5 / 4 : ℝ) * (1-x)^2 := by
           rw [← hmul]; ring
      _ ≤ 16 * 1 * 1 := by gcongr
      _ = 16 := by ring
  · simp [quarticBump_eq_zero_of_not_mem hx]

private lemma quarterPhysicalWeight_zero {x : ℝ} (h : x ∉ Icc (0 : ℝ) 1) :
    quarterPhysicalWeight x = 0 := by
  simp [quarterPhysicalWeight, quarticBump_eq_zero_of_not_mem (fun hx => h ⟨hx.1.le,hx.2.le⟩)]

private lemma measurable_quarterPhysicalWeight : Measurable quarterPhysicalWeight := by
  unfold quarterPhysicalWeight
  exact continuous_quarticBump.measurable.mul (by fun_prop)

private lemma integrable_quarterPhysicalWeight : Integrable quarterPhysicalWeight :=
  measurable_integrable_of_bound_Icc measurable_quarterPhysicalWeight (M := 16)
    (fun x => by rw [Real.norm_of_nonneg (quarterPhysicalWeight_nonneg x)]; exact quarterPhysicalWeight_le x)
    (fun _ h => quarterPhysicalWeight_zero h)

private lemma quarterKernel_fourier_integrand (lam u : ℝ) :
    quarticKernel lam (quarterPoint u) = ∫ x : ℝ,
      ((quarterPhysicalWeight x : ℝ) : ℂ) * Complex.exp (((u * Real.log x : ℝ) : ℂ) * Complex.I) * e (lam*x) := by
  unfold quarticKernel mellin
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0:ℝ))
    (f := fun x => (quarterPhysicalWeight x : ℂ) * Complex.exp (((u * Real.log x : ℝ) : ℂ) * Complex.I) * e (lam*x))]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : 0 < x := hx
    have hc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
    have him : (x : ℂ) ^ ((u : ℂ)*Complex.I) =
        Complex.exp (((u * Real.log x : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.cpow_def_of_ne_zero hc, ← Complex.ofReal_log hx0.le]
      congr 1
      push_cast
      ring
    have hp : (x : ℂ) ^ (quarterPoint u - 1) =
        ((x ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ) * Complex.exp (((u * Real.log x : ℝ) : ℂ) * Complex.I) := by
      rw [show quarterPoint u - 1 = ((-(3 / 4 : ℝ)) : ℂ) + (u : ℂ)*Complex.I by unfold quarterPoint; push_cast; ring,
        Complex.cpow_add _ _ hc]
      have hpow := Complex.ofReal_cpow (x := x) (y := -(3/4 : ℝ)) hx0.le
      simp only [Complex.ofReal_neg] at hpow
      rw [← hpow, him]
    dsimp only
    rw [hp, smul_eq_mul, quarticTilted, quarterPhysicalWeight]
    push_cast
    ring
  · intro x hx
    rw [show quarterPhysicalWeight x = 0 by
      simp [quarterPhysicalWeight, quarticBump_eq_zero_of_not_mem (fun h => hx h.1)]]
    simp

private lemma fourier_at_neg_over_two_pi (A : ℝ → ℂ) (s : ℝ) :
    𝓕 A (-s/(2*Real.pi)) = ∫ u : ℝ, A u * Complex.exp (((u*s:ℝ):ℂ)*Complex.I) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with u
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast
  field_simp [Real.pi_ne_zero]

private lemma quarter_quadratic_scaling (A : ℝ → ℂ) :
    (∫ s : ℝ, ‖𝓕 A (-s/(2*Real.pi))‖^2) =
      (2*Real.pi) * ∫ u : ℝ, ‖𝓕 A u‖^2 := by
  let H : ℝ → ℝ := fun x => ‖𝓕 A x‖^2
  change (∫ s : ℝ, H (-s/(2*Real.pi))) = (2*Real.pi) * ∫ u, H u
  simp_rw [neg_div, ← div_neg_eq_neg_div]
  rw [Measure.integral_comp_div, abs_neg, abs_of_pos (by positivity : 0 < 2*Real.pi), smul_eq_mul]

lemma quarterFourierEnergy {A : ℝ → ℂ} (hA₁ : Integrable A) (hA₂ : MemLp A 2) :
    let F : ℝ → ℂ := fun x => (quarterPhysicalWeight x : ℂ) * 𝓕 A (-Real.log x/(2*Real.pi))
    Integrable F ∧ MemLp F 2 ∧
      (∫ x : ℝ, ‖F x‖^2) ≤ 256 * (2*Real.pi) * ∫ u : ℝ, ‖A u‖^2 := by
  dsimp only
  let F : ℝ → ℂ := fun x => (quarterPhysicalWeight x : ℂ) * 𝓕 A (-Real.log x/(2*Real.pi))
  let B : ℝ → ℝ := fun x => ‖𝓕 A (-x/(2*Real.pi))‖^2
  have hcont : Continuous (𝓕 A) := VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hA₁
  have hFmeas : Measurable F := by
    exact (Complex.continuous_ofReal.measurable.comp measurable_quarterPhysicalWeight).mul
      (hcont.measurable.comp (Real.measurable_log.neg.div_const _))
  have hFzero (x : ℝ) (hx : x ∉ Icc (0 : ℝ) 1) : F x = 0 := by
    simp [F, quarterPhysicalWeight_zero hx]
  have hbound (x : ℝ) : ‖F x‖ ≤ 16 * ∫ u, ‖A u‖ := by
    have h := Real.norm_fourier_le_integral_norm A (-Real.log x/(2*Real.pi))
    dsimp only [F]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (quarterPhysicalWeight_nonneg x)]
    exact mul_le_mul (quarterPhysicalWeight_le x) h (norm_nonneg _) (by norm_num)
  have hF₁ := measurable_integrable_of_bound_Icc hFmeas hbound hFzero
  have hF₂ : Integrable (fun x => ‖F x‖^2) := by
    refine measurable_integrable_of_bound_Icc (hFmeas.norm.pow_const 2)
      (a := 0) (b := 1) (M := (16*∫ u, ‖A u‖)^2) ?_ ?_
    · intro x
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hbound x) 2
    · intro x hx; simp [hFzero x hx]
  refine ⟨hF₁, (memLp_two_iff_integrable_sq_norm hFmeas.aestronglyMeasurable).2 hF₂, ?_⟩
  have hB₂ : Integrable B := by
    have h := integrable_fourier_norm_sq hA₁ hA₂
    convert h.comp_mul_left' (R := -(2*Real.pi)⁻¹) (neg_ne_zero.mpr (inv_ne_zero (by positivity))) using 1
    ext x
    simp only [B, neg_mul, div_eq_mul_inv]
    rw [mul_comm]
  have hLog : IntegrableOn (fun x => x⁻¹ * B (Real.log x)) (Ioi (0:ℝ)) :=
    (integrableOn_comp_log_Ioi_zero B).2 hB₂
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0:ℝ))
    (f := fun x => ‖F x‖^2) (fun x hx => by
      have hw : quarterPhysicalWeight x = 0 := by
        simp [quarterPhysicalWeight, quarticBump_eq_zero_of_not_mem (fun h => hx h.1)]
      simp [F,hw])]
  calc ∫ x in Ioi (0:ℝ), ‖F x‖^2 ≤ ∫ x in Ioi (0:ℝ), 256*(x⁻¹ * B (Real.log x)) := by
        refine setIntegral_mono_on hF₂.integrableOn (hLog.const_mul _) measurableSet_Ioi fun x hx => ?_
        have hx' : 0 < x := hx
        by_cases h : x ≤ 1
        · have hw := pow_le_pow_left₀ (quarterPhysicalWeight_nonneg x) (quarterPhysicalWeight_le x) 2
          dsimp only [F]
          rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (quarterPhysicalWeight_nonneg x),mul_pow]
          change quarterPhysicalWeight x ^ 2 * B (Real.log x) ≤ _
          have hs := (one_le_inv₀ hx').2 h
          exact (mul_le_mul_of_nonneg_right hw (sq_nonneg _)).trans (by
            have := mul_le_mul_of_nonneg_right hs (show 0 ≤ 256 * B (Real.log x) by dsimp [B]; positivity)
            nlinarith only [this])
        · rw [hFzero x (fun h' => h h'.2), norm_zero, zero_pow (by decide : 2 ≠ 0)]
          dsimp [B]; positivity
    _ = 256 * (2*Real.pi) * ∫ u : ℝ, ‖A u‖^2 := by
      rw [integral_const_mul, show (∫ x in Ioi (0:ℝ), x⁻¹ * B (Real.log x)) = ∫ s, B s by
        simpa only [smul_eq_mul] using integral_comp_log_Ioi_zero (E := ℝ) B]
      change 256 * (∫ s : ℝ, ‖𝓕 A (-s/(2*Real.pi))‖^2) = _
      rw [quarter_quadratic_scaling, integral_fourier_norm_sq_eq hA₁ hA₂]
      ring

lemma quarterPhysical_fourier {Y : ℕ} (_hY : 1 ≤ Y) (A : ℝ → ℂ) (hA : Integrable A) (t : ℝ) :
    (∫ u : ℝ, A u * quarticKernel (t*(Y:ℝ)) (quarterPoint u)) =
      𝓕 (fun x : ℝ => (quarterPhysicalWeight x : ℂ) * 𝓕 A (-Real.log x/(2*Real.pi))) (-(t*(Y:ℝ))) := by
  let G (u x : ℝ) : ℂ := A u * ((quarterPhysicalWeight x : ℂ) *
    Complex.exp (((u * Real.log x : ℝ) : ℂ) * Complex.I) * e ((t*(Y:ℝ))*x))
  have hm : AEStronglyMeasurable (Function.uncurry G) (volume.prod volume) := by
    unfold G Function.uncurry
    have hA' := hA.aestronglyMeasurable.comp_fst (ν := (volume : Measure ℝ))
    have hrest : Measurable (fun p : ℝ × ℝ => (quarterPhysicalWeight p.2 : ℂ) *
        Complex.exp (((p.1 * Real.log p.2 : ℝ) : ℂ) * Complex.I) * e ((t*(Y:ℝ))*p.2)) := by
      have hw : Measurable (fun p : ℝ × ℝ => quarterPhysicalWeight p.2) :=
        measurable_quarterPhysicalWeight.comp measurable_snd
      have hl := Real.measurable_log.comp (measurable_snd : Measurable fun p : ℝ×ℝ => p.2)
      have he : Measurable (fun p : ℝ × ℝ => e ((t*(Y:ℝ))*p.2)) :=
        continuous_e_real.measurable.comp (measurable_const.mul measurable_snd)
      fun_prop
    exact hA'.mul hrest.aestronglyMeasurable
  have hG : Integrable (Function.uncurry G) (volume.prod volume) := by
    have hmajor := hA.norm.mul_prod integrable_quarterPhysicalWeight
    refine hmajor.mono' hm (Eventually.of_forall ?_)
    intro p
    dsimp [G,Function.uncurry]
    rw [norm_mul,norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (quarterPhysicalWeight_nonneg _),
      Complex.norm_exp_ofReal_mul_I,norm_e_real,mul_one,mul_one]
  simp_rw [quarterKernel_fourier_integrand, ← integral_const_mul]
  change (∫ u : ℝ, ∫ x : ℝ, G u x) = _
  rw [integral_integral_swap hG, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with x
  rw [fourier_at_neg_over_two_pi]
  have hphase : Complex.exp ((↑(-2 * Real.pi * x * -(t*(Y:ℝ))) : ℂ) * Complex.I) =
      e ((t*(Y:ℝ))*x) := by
    unfold e
    congr 1
    push_cast
    ring
  rw [hphase]
  calc ∫ u : ℝ, G u x = ∫ u : ℝ, (quarterPhysicalWeight x : ℂ) *
      (A u * Complex.exp (((u*Real.log x:ℝ):ℂ)*Complex.I)) * e ((t*(Y:ℝ))*x) := by
        apply integral_congr_ae
        filter_upwards with u
        dsimp [G]; ring
    _ = _ := by rw [integral_mul_const, integral_const_mul, smul_eq_mul]; ring

end FareyGoldbach
