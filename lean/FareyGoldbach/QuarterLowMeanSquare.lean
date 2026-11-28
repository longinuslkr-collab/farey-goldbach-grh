import FareyGoldbach.QuarterContourPlancherel

open Complex Real MeasureTheory Set Filter
open scoped FourierTransform Classical

namespace FareyGoldbach

private lemma continuous_quarterLogDeriv (hGRH : DirichletGRH) {d : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) :
    Continuous (fun u => negLogDerivL χ (quarterPoint u)) := by
  have hcont : Continuous quarterPoint := by unfold quarterPoint; fun_prop
  have h₁ (u : ℝ) : quarterPoint u ≠ 1 := fun h => by
    have h' := congrArg Complex.re h
    norm_num [quarterPoint] at h'
  have hz (u : ℝ) : entireL χ (quarterPoint u) ≠ 0 := fun h => by
    have hre : (quarterPoint u).re = 1/4 := by simp [quarterPoint]
    have he := entireL_re_eq_half_of_eq_zero hGRH hprim (by linarith : 0 < (quarterPoint u).re) h
    linarith only [he,hre]
  have heq (u : ℝ) := negLogDerivL_eq_of_ne_one χ (h₁ u) (fun h => hz u (by
    rw [entireL_apply_of_ne_one χ (h₁ u),h]
    split_ifs <;> simp))
  simp_rw [heq]
  have hf := differentiable_entireL χ
  apply Continuous.sub _ ((hf.deriv.continuous.comp hcont).div (hf.continuous.comp hcont) hz)
  by_cases hχ : χ = 1
  · simp only [ite_eq_left hχ]
    exact Continuous.div (f := fun _ : ℝ => (1 : ℂ)) (g := fun u => quarterPoint u - 1)
      continuous_const (hcont.sub continuous_const) (fun u => sub_ne_zero.mpr (h₁ u))
  · simp only [ite_eq_right hχ]
    exact continuous_const

private lemma quarter_log_height_le {d Y : ℕ} [NeZero d] (hY : 2 ≤ Y) {u : ℝ}
    (hu : |u| ≤ 11 * (Y:ℝ)) :
    Real.log (2*(d:ℝ)*(2+|u|)) ≤ 3*Real.log (2*(d:ℝ)*Y) := by
  have hd : (1:ℝ) ≤ d := Nat.one_le_cast.mpr (NeZero.pos d)
  have hy : (2:ℝ) ≤ Y := by exact_mod_cast hY
  have hy12 : 2+|u| ≤ 12*(Y:ℝ) := by linarith only [hy,hu]
  have hz : (4:ℝ) ≤ 2*(d:ℝ)*Y := by nlinarith only [mul_le_mul_of_nonneg_right hd (show (0:ℝ)≤Y by positivity),hy]
  calc _ ≤ Real.log (12*(2*(d:ℝ)*Y)) := by
        apply Real.log_le_log (by positivity)
        exact (mul_le_mul_of_nonneg_left hy12 (by positivity : 0≤2*(d:ℝ))).trans_eq (by ring)
    _ = Real.log 12 + Real.log (2*(d:ℝ)*Y) := by rw [Real.log_mul (by norm_num) (by positivity)]
    _ ≤ _ := by
      have h := Real.log_le_log (by norm_num : (0:ℝ)<12)
        (show (12:ℝ)≤(2*(d:ℝ)*Y)^2 by nlinarith only [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤4) hz 2])
      rw [Real.log_pow] at h
      norm_num at h
      linarith only [h]

theorem quarterLow_meanSquare (hGRH : DirichletGRH) :
    ∃ C : ℝ, 0<C ∧ ∀ {d Y : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}, χ.IsPrimitive →
      ∀ (T ξ : ℝ), 2 ≤ Y → 0 ≤ T → T ≤ 11*(Y:ℝ) → 0 ≤ ξ →
      Continuous (fun t => ∫ u in Icc (-T) T, quarterContourIntegrand χ Y t u) ∧
      (∫ t in -ξ..ξ, ‖∫ u in Icc (-T) T, quarterContourIntegrand χ Y t u‖^2) ≤
        C * (Y:ℝ)^(-(1/2:ℝ)) * T * Real.log (2*(d:ℝ)*Y)^2 := by
  refine ⟨256*(2*Real.pi)*2*(3*812870)^2, by positivity, ?_⟩
  intro d Y hd χ hprim T ξ hY hT hTY hξ
  let L := Real.log (2*(d:ℝ)*Y)
  let M := 3*812870*L
  let A := (Icc (-T) T).indicator fun u : ℝ =>
    ((Y:ℝ):ℂ)^((u:ℂ)*Complex.I) * negLogDerivL χ (quarterPoint u)
  have hY' : (0:ℝ)<Y := Nat.cast_pos.mpr (by omega)
  have hL : 0 ≤ L := zero_le_one.trans (one_le_log_two_d_Y hY)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hYpow (u : ℝ) : ‖((Y:ℝ):ℂ)^((u:ℂ)*Complex.I)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY']; simp
  have hAbound (u : ℝ) : ‖A u‖ ≤ M := by
    by_cases hu : u ∈ Icc (-T) T
    · dsimp only [A]; rw [Set.indicator_of_mem hu,norm_mul,hYpow,one_mul]
      have hlog := quarter_log_height_le (d := d) hY ((abs_le.mpr hu).trans hTY)
      have h := (negLogDeriv_quarter hGRH hprim u).trans
        (mul_le_mul_of_nonneg_left hlog (by norm_num : (0:ℝ)≤812870))
      exact h.trans_eq (by dsimp [M,L]; ring)
    · dsimp only [A]; rw [Set.indicator_of_notMem hu,norm_zero]; exact hM
  have hAzero (u : ℝ) (hu : u ∉ Icc (-T) T) : A u = 0 := Set.indicator_of_notMem hu _
  have hAmeas : Measurable A := by
    apply Measurable.indicator _ measurableSet_Icc
    have hD := continuous_quarterLogDeriv hGRH hprim
    exact (((Complex.continuous_ofReal.mul (continuous_const (y := Complex.I))).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hY'.ne'))).mul hD).measurable
  have hA₁ := measurable_integrable_of_bound_Icc hAmeas hAbound hAzero
  have hAi : Integrable (fun u => ‖A u‖^2) := by
    refine measurable_integrable_of_bound_Icc (a := -T) (b := T) (hAmeas.norm.pow_const 2) (M := M^2) ?_ ?_
    · intro u; rw [Real.norm_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (norm_nonneg _) (hAbound u) 2
    · intro u hu; simp [hAzero u hu]
  have hA₂ := (memLp_two_iff_integrable_sq_norm hAmeas.aestronglyMeasurable).2 hAi
  have hAint : (∫ u, ‖A u‖^2) ≤ 2*T*M^2 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-T) T)
      (f := fun u => ‖A u‖^2) (fun u hu => by simp [hAzero u hu])]
    calc _ ≤ ∫ u in Icc (-T) T, M^2 := setIntegral_mono_on hAi.integrableOn
            continuous_const.continuousOn.integrableOn_Icc measurableSet_Icc
            (fun u _ => pow_le_pow_left₀ (norm_nonneg _) (hAbound u) 2)
      _ = _ := by rw [setIntegral_const,Measure.real,Real.volume_Icc,ENNReal.toReal_ofReal (by linarith),smul_eq_mul]; ring
  let F : ℝ → ℂ := fun x => (quarterPhysicalWeight x : ℂ) * 𝓕 A (-Real.log x/(2*Real.pi))
  obtain ⟨hF₁,hF₂,hFen⟩ := quarterFourierEnergy hA₁ hA₂
  have hintegrand (t : ℝ) : (∫ u in Icc (-T) T, quarterContourIntegrand χ Y t u) =
      (((Y:ℝ)^((1/4):ℝ) : ℝ) : ℂ) * 𝓕 F (-(t*(Y:ℝ))) := by
    rw [← quarterPhysical_fourier (show 1≤Y by omega) A hA₁, ← integral_const_mul, ← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with u
    by_cases hu : u ∈ Icc (-T) T
    · dsimp only [A]
      rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, quarterContourIntegrand,
        mellin_scaledTiltedBump_eq (show 1≤Y by omega), quarterPoint,
        Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hY'.ne'), ← Complex.ofReal_cpow hY'.le]
      ring
    · rw [Set.indicator_of_notMem hu, hAzero u hu, zero_mul, mul_zero]
  constructor
  · simp_rw [hintegrand]
    have hf : Continuous (𝓕 F) := VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hF₁
    exact continuous_const.mul (hf.comp (continuous_id.mul_const _).neg)
  simp_rw [hintegrand,norm_mul,mul_pow,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg hY'.le _)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le (by linarith : -ξ ≤ ξ)]
  have hf := integrable_fourier_norm_sq hF₁ hF₂
  let D : ℝ → ℝ := fun v => ‖𝓕 F v‖^2
  have hDf : Integrable D := hf
  have hscaled : Integrable (fun t => D (-(t*(Y:ℝ)))) := by
    convert hDf.comp_mul_left' (R := -(Y:ℝ)) (neg_ne_zero.mpr hY'.ne') using 1
    ext t
    simp [mul_comm]
  have hrestrict : (∫ t in Ioc (-ξ) ξ, D (-(t*(Y:ℝ)))) ≤ ∫ t, D (-(t*(Y:ℝ))) :=
    setIntegral_le_integral hscaled (Eventually.of_forall fun _ => sq_nonneg _)
  have hscale : (∫ t, D (-(t*(Y:ℝ)))) = (Y:ℝ)⁻¹ * ∫ t, D t := by
    simp_rw [← mul_neg, mul_comm _ (-(Y:ℝ))]
    rw [Measure.integral_comp_mul_left, inv_neg, abs_neg, abs_of_pos (inv_pos.mpr hY'), smul_eq_mul]
  have hsize : (∫ t in Ioc (-ξ) ξ, D (-(t*(Y:ℝ)))) ≤
      (Y:ℝ)⁻¹ * (256*(2*Real.pi)*(2*T*M^2)) := by
    apply hrestrict.trans
    rw [hscale]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (integral_fourier_norm_sq_eq hF₁ hF₂).le.trans (hFen.trans
      (mul_le_mul_of_nonneg_left hAint (by positivity)))
  change ((Y:ℝ)^(1/4:ℝ))^2 * (∫ t in Ioc (-ξ) ξ, D (-(t*(Y:ℝ)))) ≤ _
  refine (mul_le_mul_of_nonneg_left hsize (sq_nonneg _)).trans_eq ?_
  have hpow : ((Y:ℝ)^(1/4:ℝ))^2 * (Y:ℝ)⁻¹ = (Y:ℝ)^(-(1/2:ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hY'.le, ← Real.rpow_neg_one,
      ← Real.rpow_add hY']; norm_num
  rw [← mul_assoc,hpow]
  dsimp [M,L]; ring

end FareyGoldbach
