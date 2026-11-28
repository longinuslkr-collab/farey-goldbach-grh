import FareyGoldbach.QuarticMellin

/-! # A compact logarithmic transition for Perron's formula -/

open Set Filter MeasureTheory Topology

namespace FareyGoldbach

private noncomputable def rampSquare (a x : ℝ) : ℝ :=
  if 0 < x then (max 0 (a - Real.log x)) ^ 2 else 0

/-- The average of the sharp cutoff after two independent logarithmic shifts in [0,δ]. -/
noncomputable def sharpPerronWeight (δ x : ℝ) : ℝ :=
  (rampSquare (2*δ) x - 2*rampSquare δ x + rampSquare 0 x)/(2*δ^2)

/-- Mellin multiplier for the twice-averaged cutoff. -/
noncomputable def sharpPerronKernel (δ : ℝ) (s : ℂ) : ℂ :=
  (Complex.exp ((δ:ℂ)*s)-1)^2 / ((δ:ℂ)^2*s^3)

theorem sharpPerronWeight_eq_one {δ x : ℝ} (hδ : 0<δ) (hx : 0<x) (hx1 : x≤1) :
    sharpPerronWeight δ x = 1 := by
  have ht := Real.log_nonpos hx.le hx1
  unfold sharpPerronWeight rampSquare
  simp only [ite_eq_left hx, max_eq_right (by linarith : 0≤2*δ-Real.log x),
    max_eq_right (by linarith : 0≤δ-Real.log x), max_eq_right (by linarith : 0≤0-Real.log x)]
  field_simp [hδ.ne']
  ring

theorem sharpPerronWeight_eq_zero {δ x : ℝ} (hδ : 0<δ) (hx : Real.exp (2*δ) ≤ x) :
    sharpPerronWeight δ x = 0 := by
  have hx0 := (Real.exp_pos _).trans_le hx
  have ht := (Real.le_log_iff_exp_le hx0).mpr hx
  unfold sharpPerronWeight rampSquare
  simp only [ite_eq_left hx0,max_eq_left (by linarith : 2*δ-Real.log x≤0),
    max_eq_left (by linarith : δ-Real.log x≤0),max_eq_left (by linarith : 0-Real.log x≤0)]
  norm_num

theorem sharpPerronWeight_mem_Icc {δ x : ℝ} (hδ : 0<δ) (hx : 0<x) :
    sharpPerronWeight δ x ∈ Icc 0 1 := by
  by_cases hx1 : x≤1
  · rw [sharpPerronWeight_eq_one hδ hx hx1]
    exact ⟨zero_le_one,le_rfl⟩
  by_cases hx2 : Real.exp (2*δ)≤x
  · rw [sharpPerronWeight_eq_zero hδ hx2]
    exact ⟨le_rfl,zero_le_one⟩
  have ht := Real.log_pos (lt_of_not_ge hx1)
  have ht2 := (Real.log_lt_iff_lt_exp hx).mpr (lt_of_not_ge hx2)
  have hden : 0<2*δ^2 := by positivity
  unfold sharpPerronWeight rampSquare
  simp only [ite_eq_left hx,max_eq_right (by linarith : 0≤2*δ-Real.log x),
    max_eq_left (by linarith : 0-Real.log x≤0), zero_pow (by decide : 2≠0),add_zero,mem_Icc]
  by_cases h : Real.log x≤δ
  · rw [max_eq_right (by linarith : 0≤δ-Real.log x)]
    have hsq := mul_self_le_mul_self ht.le h
    constructor
    · apply div_nonneg _ hden.le
      nlinarith [sq_nonneg δ]
    · apply (div_le_one hden).mpr
      nlinarith [sq_nonneg (Real.log x)]
  · rw [max_eq_left (by linarith : δ-Real.log x≤0)]
    have hsq := mul_self_le_mul_self (by linarith : 0≤2*δ-Real.log x) (by linarith : 2*δ-Real.log x≤δ)
    constructor
    · simp only [zero_pow (by decide : 2≠0), mul_zero,sub_zero]; positivity
    · apply (div_le_one hden).mpr
      nlinarith [sq_nonneg δ]

theorem continuousAt_sharpPerronWeight (δ : ℝ) {x : ℝ} (hx : 0<x) :
    ContinuousAt (sharpPerronWeight δ) x := by
  have hr (a : ℝ) : ContinuousAt (rampSquare a) x := by
    have ht : ContinuousAt (fun t : ℝ => (max 0 (a - Real.log t))^2) x := by
      fun_prop (disch := positivity)
    apply ht.congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hx] with t ht
    simp [rampSquare,ht]
  exact (((hr _).sub ((hr δ).const_mul 2)).add (hr 0)).div_const _

theorem differentiableAt_sharpPerronKernel (δ : ℝ) {s:ℂ} (hs:s≠0) :
    DifferentiableAt ℂ (sharpPerronKernel δ) s := by
  by_cases hδ : δ=0
  · subst δ
    have heq : sharpPerronKernel 0 = fun _ => 0 := by funext z; simp [sharpPerronKernel]
    rw [heq]
    exact differentiableAt_const _
  unfold sharpPerronKernel
  fun_prop (disch := exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hδ)) (pow_ne_zero _ hs))

theorem sharpPerronKernel_norm_le_min {δ : ℝ} (hδ : 0<δ) (hδ1 : δ≤1) {s:ℂ}
    (hs : 1/4≤s.re) (hs2 : s.re≤2) :
    ‖sharpPerronKernel δ s‖ ≤ 100 * min (1/‖s‖) (1/(δ^2*‖s‖^3)) := by
  have hs0 : 0<‖s‖ := norm_pos_iff.mpr fun h => by subst s; norm_num at hs
  have he2 : Real.exp (2:ℝ)≤9 := by
    rw [show (2:ℝ)=1+1 by norm_num,Real.exp_add]
    have h : Real.exp 1 ≤ 3 := by
      have ha := Real.abs_exp_sub_one_le (x:=1) (by norm_num)
      norm_num at ha
      linarith [le_abs_self (Real.exp 1-1)]
    exact (mul_self_le_mul_self (Real.exp_pos 1).le h).trans_eq (by norm_num)
  have hprod : δ*s.re≤2 := by nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hs2)]
  have hnorm : ‖(δ:ℂ)*s‖=δ*‖s‖ := by simp [Real.norm_eq_abs,abs_of_pos hδ]
  have hem : ‖Complex.exp ((δ:ℂ)*s)-1‖≤10 := by
    calc _ ≤ ‖Complex.exp ((δ:ℂ)*s)‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
         _ = Real.exp (δ*s.re)+1 := by simp [Complex.norm_exp,Complex.mul_re]
         _ ≤ 10 := by linarith [(Real.exp_le_exp.mpr hprod).trans he2]
  have hd : 0<δ^2*‖s‖^3 := by positivity
  unfold sharpPerronKernel
  rw [norm_div,norm_pow,norm_mul,norm_pow,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
  rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ)≤100)]
  apply le_min
  · have hsmall : ‖Complex.exp ((δ:ℂ)*s)-1‖ ≤ 10*(δ*‖s‖) := by
      by_cases h : δ*‖s‖≤1
      · have h' := Complex.norm_exp_sub_one_le (x:=(δ:ℂ)*s) (hnorm.trans_le h)
        rw [hnorm] at h'
        nlinarith [mul_nonneg hδ.le hs0.le]
      · nlinarith
    have hsq := mul_self_le_mul_self (norm_nonneg _) hsmall
    rw [div_le_iff₀ hd]
    field_simp [hs0.ne']
    nlinarith [mul_le_mul_of_nonneg_right hsq hs0.le]
  · have hsq := mul_self_le_mul_self (norm_nonneg _) hem
    rw [mul_one_div, div_le_div_iff_of_pos_right hd]
    nlinarith


private noncomputable def perronStep : ℝ→ℂ := (Ioc 0 1).indicator (fun _ => 1)
private noncomputable def perronLog (f : ℝ→ℂ) (x : ℝ) : ℂ := Real.log x • f x

private theorem perronStep_locally : LocallyIntegrableOn perronStep (Ioi 0) := by
  have h : Integrable perronStep := by
    apply (integrable_indicator_iff measurableSet_Ioc).mpr
    simp
  exact h.locallyIntegrable.locallyIntegrableOn _

private theorem perronStep_top (a : ℝ) : perronStep =O[atTop] (fun x : ℝ => x^(-a)) := by
  refine Asymptotics.isBigO_iff.mpr ⟨1,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
  simp [perronStep, not_le.mpr hx]

private theorem perronStep_zero : perronStep =O[𝓝[>] (0:ℝ)] (fun x : ℝ => x^(-(0:ℝ))) := by
  refine Asymptotics.isBigO_iff.mpr ⟨1,?_⟩
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one : (0:ℝ)<1))] with x hx hx1
  simp [perronStep, show x∈Ioc 0 1 from ⟨hx,hx1.le⟩]

private theorem perronLog_step {s:ℂ} (hs : 0<s.re) :
    HasMellin (perronLog perronStep) s (-1/s^2) := by
  obtain ⟨hi,hd⟩ := mellin_hasDerivAt_of_isBigO_rpow perronStep_locally
    (perronStep_top (s.re+1)) (lt_add_one _) perronStep_zero hs
  refine ⟨hi,hd.unique ?_⟩
  have hs0 : s≠0 := fun h => by subst s; simp at hs
  have hr : HasDerivAt (fun z:ℂ => 1/z) (-1/s^2) s := by
    apply ((hasDerivAt_const s (1:ℂ)).fun_div (hasDerivAt_id s) hs0).congr_deriv
    simp
  apply hr.congr_of_eventuallyEq
  filter_upwards [Complex.continuous_re.continuousAt.eventually (Ioi_mem_nhds hs)] with z hz
  exact (hasMellin_one_Ioc hz).2

private theorem perronLogSq_step {s:ℂ} (hs : 0<s.re) :
    HasMellin (perronLog (perronLog perronStep)) s (2/s^3) := by
  have hlocal : LocallyIntegrableOn (perronLog perronStep) (Ioi 0) :=
    perronStep_locally.continuousOn_smul isOpen_Ioi.isLocallyClosed
      (Real.continuousOn_log.mono fun _ hx => ne_of_gt hx)
  have htop : perronLog perronStep =O[atTop] (fun x : ℝ => x^(-(s.re+1))) :=
    isBigO_rpow_top_log_smul (show s.re+1<s.re+2 by linarith) (perronStep_top (s.re+2))
  have hzero : perronLog perronStep =O[𝓝[>] (0:ℝ)] (fun x : ℝ=>x^(-(s.re/2))) :=
    isBigO_rpow_zero_log_smul (show 0<s.re/2 by linarith) perronStep_zero
  obtain ⟨hi,hd⟩ := mellin_hasDerivAt_of_isBigO_rpow hlocal htop
    (lt_add_one _) hzero (show s.re/2<s.re by linarith)
  refine ⟨hi,hd.unique ?_⟩
  have hs0 : s≠0 := fun h => by subst s; simp at hs
  have hr : HasDerivAt (fun z:ℂ => -1/z^2) (2/s^3) s := by
    apply ((hasDerivAt_const s (-1:ℂ)).fun_div ((hasDerivAt_id s).fun_pow 2) (pow_ne_zero _ hs0)).congr_deriv
    simp only [id_eq]
    field_simp [hs0]
    ring
  apply hr.congr_of_eventuallyEq
  filter_upwards [Complex.continuous_re.continuousAt.eventually (Ioi_mem_nhds hs)] with z hz
  exact (perronLog_step hz).2

theorem sharpPerronKernel_one_sub_norm_le {δ : ℝ} (hδ : 0<δ) (hδ1 : δ≤1) :
    ‖sharpPerronKernel δ 1-1‖ ≤ 18*δ := by
  let q := (Real.exp δ-1)/δ
  have hq : 1≤q := (le_div_iff₀ hδ).mpr (by linarith [Real.add_one_le_exp δ])
  have he := Real.abs_exp_sub_one_sub_id_le (x:=δ) ((abs_of_pos hδ).trans_le hδ1)
  have hq' : q≤1+δ := (div_le_iff₀ hδ).mpr (by nlinarith [le_abs_self (Real.exp δ-1-δ)])
  have hpow : 1≤q^2 := by nlinarith [sq_nonneg (q-1)]
  have heq : sharpPerronKernel δ 1 = ((q^2 : ℝ):ℂ) := by
    unfold sharpPerronKernel q
    push_cast
    simp [div_pow]
  rw [heq,← Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hpow)]
  nlinarith only [mul_self_le_mul_self (by linarith : 0≤q) hq',
    mul_nonneg hδ.le (sub_nonneg.mpr hδ1), hδ]

private theorem rampSquare_scaled (a x : ℝ) :
    (rampSquare a x : ℂ) = perronLog (perronLog perronStep) (Real.exp (-a)*x) := by
  by_cases hx : 0<x
  · have hv := mul_pos (Real.exp_pos (-a)) hx
    have hlog : Real.log (Real.exp (-a)*x)=Real.log x-a := by
      rw [Real.log_mul (Real.exp_pos _).ne' hx.ne',Real.log_exp]; ring
    have hiff : Real.exp (-a)*x≤1 ↔ Real.log x≤a := by
      rw [←Real.log_le_log_iff hv zero_lt_one,hlog,Real.log_one]
      exact sub_nonpos
    by_cases h : Real.log x≤a
    · have hm : Real.exp (-a)*x∈Ioc 0 1 := ⟨hv,hiff.mpr h⟩
      simp only [rampSquare,ite_eq_left hx,max_eq_right (sub_nonneg.mpr h),
        perronLog,perronStep,indicator_of_mem hm,hlog,Complex.real_smul]
      push_cast
      ring
    · have hm : Real.exp (-a)*x∉Ioc 0 1 := fun h' => h (hiff.mp h'.2)
      simp [rampSquare,hx,max_eq_left (by linarith : a-Real.log x≤0),perronLog,perronStep,hm]
  · have hz : Real.exp (-a)*x∉Ioc 0 1 := fun h => not_lt_of_ge
          (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (le_of_not_gt hx)) h.1
    simp [rampSquare,hx,perronLog,perronStep,hz]

private theorem hasMellin_rampSquare (a : ℝ) {s : ℂ} (hs : 0<s.re) :
    HasMellin (fun x => (rampSquare a x : ℂ)) s (Complex.exp ((a:ℂ)*s)*(2/s^3)) := by
  have hb := perronLogSq_step hs
  rw [show (fun x => (rampSquare a x:ℂ)) = (fun x => perronLog (perronLog perronStep) (Real.exp (-a)*x))
    from funext (rampSquare_scaled a)]
  refine ⟨(MellinConvergent.comp_mul_left (Real.exp_pos (-a))).mpr hb.1,?_⟩
  rw [mellin_comp_mul_left _ _ (Real.exp_pos (-a)),hb.2,smul_eq_mul,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
    ←Complex.ofReal_log (Real.exp_pos _).le,Real.log_exp,Complex.ofReal_neg,neg_mul_neg]

/-- The Mellin transform of the logarithmic transition on its full half plane. -/
theorem hasMellin_sharpPerronWeight (δ : ℝ) {s:ℂ} (hs : 0<s.re) :
    HasMellin (fun x => (sharpPerronWeight δ x : ℂ)) s (sharpPerronKernel δ s) := by
  let f := fun a x : ℝ => (rampSquare a x : ℂ)
  obtain ⟨hi2,hm2⟩ := hasMellin_rampSquare (2*δ) hs
  obtain ⟨hi1,hm1⟩ := hasMellin_rampSquare δ hs
  obtain ⟨hi0,hm0⟩ := hasMellin_rampSquare 0 hs
  have hsub := hasMellin_sub hi2 (hi1.const_smul (2:ℂ))
  have hadd := hasMellin_add hsub.1 hi0
  have heq : (fun x => (sharpPerronWeight δ x : ℂ)) =
      fun x => (f (2*δ) x - (2:ℂ) • f δ x + f 0 x)/(2*(δ:ℂ)^2) := by
    funext x
    simp [sharpPerronWeight,f, smul_eq_mul]
  rw [heq]
  refine ⟨hadd.1.div_const _,?_⟩
  dsimp only [f]
  rw [mellin_div_const,hadd.2,hsub.2,mellin_const_smul,hm2,hm1,hm0]
  unfold sharpPerronKernel
  push_cast
  rw [show 2*(δ:ℂ)*s=(δ:ℂ)*s+(δ:ℂ)*s by ring, Complex.exp_add]
  simp only [smul_eq_mul,zero_mul,Complex.exp_zero,one_mul]
  by_cases hδ : δ=0
  · simp [hδ]
  have hs0 : s≠0 := fun h => by subst s; simp at hs
  field_simp [Complex.ofReal_ne_zero.mpr hδ,hs0]
  ring

theorem verticalIntegrable_sharpPerronKernel {δ σ:ℝ} (hδ : 0<δ) (hδ1 : δ≤1)
    (hσ : 1/4≤σ) (hσ2 : σ≤2) : Complex.VerticalIntegrable (sharpPerronKernel δ) σ := by
  have hc : Continuous (fun u : ℝ => sharpPerronKernel δ ((σ:ℂ)+u*Complex.I)) := by
    refine continuous_iff_continuousAt.mpr fun u => ?_
    have hs0 : (σ:ℂ)+(u:ℂ)*Complex.I≠0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    exact ContinuousAt.comp (f:=fun t:ℝ => (σ:ℂ)+t*Complex.I) (g:=sharpPerronKernel δ)
      (differentiableAt_sharpPerronKernel δ hs0).continuousAt (by fun_prop)
  apply (integrable_inv_one_add_sq.const_mul (6800/δ^2)).mono' hc.aestronglyMeasurable
  filter_upwards with u
  let s := (σ:ℂ)+(u:ℂ)*Complex.I
  have hr : s.re=σ := by simp [s]
  have hi : s.im=u := by simp [s]
  have hn : 1/4≤‖s‖ := by
    rw [←hr] at hσ
    exact hσ.trans ((le_abs_self _).trans (Complex.abs_re_le_norm s))
  have hn0 : 0<‖s‖ := by linarith
  have hsq : u^2 ≤ ‖s‖^2 := by
    rw [←sq_abs u]
    exact pow_le_pow_left₀ (abs_nonneg u) (hi ▸ Complex.abs_im_le_norm s) 2
  have hdom : 1+u^2≤68*‖s‖^3 := by
    nlinarith only [hsq,mul_self_le_mul_self (by norm_num : (0:ℝ)≤1/4) hn,
      mul_nonneg (sub_nonneg.mpr hn) (sq_nonneg ‖s‖)]
  have h := sharpPerronKernel_norm_le_min hδ hδ1 (s:=s) (hr ▸ hσ) (hr ▸ hσ2)
  apply h.trans ((mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num : (0:ℝ)≤100)).trans ?_)
  rw [mul_one_div,←div_eq_mul_inv,div_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [mul_nonneg (sq_nonneg δ) (sub_nonneg.mpr hdom)]

theorem mellinInv_sharpPerronKernel {δ σ x : ℝ} (hδ : 0<δ) (hδ1 : δ≤1)
    (hσ : 1/4≤σ) (hσ2 : σ≤2) (hx : 0<x) :
    mellinInv σ (sharpPerronKernel δ) x = (sharpPerronWeight δ x : ℂ) := by
  have hσ0 : 0<σ := by linarith
  let f := fun y => (sharpPerronWeight δ y : ℂ)
  have he (u:ℝ) : mellin f ((σ:ℂ)+u*Complex.I) = sharpPerronKernel δ ((σ:ℂ)+u*Complex.I) :=
    (hasMellin_sharpPerronWeight δ (by simpa using hσ0)).2
  have hv : Complex.VerticalIntegrable (mellin f) σ := by
    unfold Complex.VerticalIntegrable
    simp_rw [he]
    exact verticalIntegrable_sharpPerronKernel hδ hδ1 hσ hσ2
  have h := mellinInv_mellin_eq σ f hx (hasMellin_sharpPerronWeight δ hσ0).1 hv
    (Complex.continuous_ofReal.continuousAt.comp (continuousAt_sharpPerronWeight δ hx))
  unfold mellinInv at h ⊢
  simp_rw [he] at h
  exact h

/-- The height form used in dyadic sums over zeros. -/
theorem sharpPerronKernel_norm_le_min_height {δ : ℝ} (hδ : 0<δ) (hδ1 : δ≤1) {s:ℂ}
    (hs : 1/4≤s.re) (hs2 : s.re≤2) :
    ‖sharpPerronKernel δ s‖ ≤ 12500 * min (1/(1+|s.im|)) (1/(δ^2*(1+|s.im|)^3)) := by
  have hn : 1/4 ≤ ‖s‖ := hs.trans ((le_abs_self _).trans (Complex.abs_re_le_norm s))
  have hn0 : 0<‖s‖ := by linarith
  have ht : 1+|s.im|≤5*‖s‖ := by linarith [Complex.abs_im_le_norm s]
  have ht0 : 0<1+|s.im| := by positivity
  have h1 : 1/‖s‖≤125*(1/(1+|s.im|)) := by
    rw [mul_one_div,div_le_div_iff₀ hn0 ht0]
    linarith
  have h3 : 1/(δ^2*‖s‖^3) ≤ 125*(1/(δ^2*(1+|s.im|)^3)) := by
    rw [mul_one_div,div_le_div_iff₀ (by positivity) (by positivity)]
    have hpow := pow_le_pow_left₀ ht0.le ht 3
    nlinarith only [mul_le_mul_of_nonneg_left hpow (sq_nonneg δ)]
  apply (sharpPerronKernel_norm_le_min hδ hδ1 hs hs2).trans
  calc _ ≤ 100*min (125*(1/(1+|s.im|))) (125*(1/(δ^2*(1+|s.im|)^3))) :=
             mul_le_mul_of_nonneg_left (min_le_min h1 h3) (by norm_num)
       _ = _ := by rw [←mul_min_of_nonneg _ _ (by norm_num : (0:ℝ)≤125)]; ring

end FareyGoldbach
