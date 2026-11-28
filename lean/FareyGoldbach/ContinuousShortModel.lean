import FareyGoldbach.DoubleAverageGoldbach
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-! # Continuous quartic model for Goldbach coefficients in a short interval -/

open Real Complex Set Filter MeasureTheory
open scoped BigOperators Classical Topology FourierTransform Convolution ComplexConjugate

namespace FareyGoldbach

/-- Archimedean kernel for the compressed progression coordinate `(n-b)/r`. -/
noncomputable def shortContKernel (r b Y : ℕ) (β : ℝ) : ℂ :=
  (r : ℂ)⁻¹ * e (-(β * (b : ℝ) / (r : ℝ))) *
    mellin (scaledTiltedBump Y (β / (r : ℝ))) 1

/-- Full, untruncated order-`Q` Farey model, using the continuous quartic kernel. -/
noncomputable def shortContModel (r b Y Q : ℕ) (α : ℝ) : ℂ :=
  ∑ c ∈ (centers Q).filter (fun c ↦ c.q ≤ Q),
    (voronoiCell Q c).indicator
      (fun x ↦ modelCoeff r b c * shortContKernel r b Y (wrap (x - c.val))) α

private noncomputable def shortBump (x : ℝ) : ℂ := quarticBump x

private lemma shortBump_continuous : Continuous shortBump :=
  Complex.continuous_ofReal.comp continuous_quarticBump

private lemma shortBump_support : HasCompactSupport shortBump := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (0:ℝ)) (b := 1)) ?_
  intro x hx
  have h : ¬ (0 < x ∧ x < 1) := fun h ↦ hx ⟨h.1.le, h.2.le⟩
  simp [shortBump, quarticBump_eq_zero_of_not_mem h]

private lemma shortBump_integrable : Integrable shortBump :=
  shortBump_continuous.integrable_of_hasCompactSupport shortBump_support

private lemma fourier_shortBump (u : ℝ) :
    𝓕 shortBump (-u) = quarticKernel u 1 := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold quarticKernel mellin
  simp only [sub_self, Complex.cpow_zero, one_smul]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0:ℝ))
    (f := quarticTilted u) (fun x hx ↦ by
      have h : ¬ (0 < x ∧ x < 1) := fun h ↦ hx h.1
      simp [quarticTilted, quarticBump_eq_zero_of_not_mem h])]
  apply integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul, shortBump, quarticTilted, e]
  rw [mul_comm (Complex.exp _)]; congr 2; push_cast; ring

lemma shortContKernel_fourier {Y : ℕ} (hY : 1 ≤ Y) (r b : ℕ) (β : ℝ) :
    shortContKernel r b Y β = ((Y:ℂ) / (r:ℂ)) * e (-(β * (b:ℝ) / (r:ℝ))) *
      𝓕 (fun x : ℝ ↦ (quarticBump x : ℂ)) (-(β / (r:ℝ) * (Y:ℝ))) := by
  rw [shortContKernel, mellin_scaledTiltedBump_eq hY, Complex.cpow_one,
    ← fourier_shortBump]
  change _ = _ * _ * 𝓕 shortBump _
  push_cast
  ring

lemma continuous_shortContKernel {Y : ℕ} (hY : 1 ≤ Y) (r b : ℕ) :
    Continuous (shortContKernel r b Y) := by
  have hF : Continuous (𝓕 shortBump) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ shortBump_integrable
  simp_rw [funext (shortContKernel_fourier hY r b)]
  exact (continuous_const.mul (continuous_e_real.comp
    ((continuous_id.mul continuous_const).div_const _).neg)).mul
    (hF.comp (((continuous_id.div_const _).mul continuous_const).neg))

private lemma shortBump_L1 : ∫ x, ‖shortBump x‖ ≤ 1 := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc (0:ℝ) 1)
    (f := fun x ↦ ‖shortBump x‖) (fun x hx ↦ by
      have h : ¬ (0 < x ∧ x < 1) := fun h ↦ hx ⟨h.1, h.2.le⟩
      simp [shortBump, quarticBump_eq_zero_of_not_mem h])]
  calc
    _ ≤ ∫ _ in Ioc (0:ℝ) 1, (1:ℝ) := by
      apply setIntegral_mono_on shortBump_integrable.norm.integrableOn
        (integrableOn_const (by simp)) measurableSet_Ioc
      intro x _
      simpa [shortBump, Real.norm_eq_abs, abs_of_nonneg (quarticBump_nonneg x)] using
        quarticBump_le_one x
    _ = _ := by simp

lemma shortContKernel_bound_triv {Y : ℕ} (hY : 1 ≤ Y) (r b : ℕ) (β : ℝ) :
    ‖shortContKernel r b Y β‖ ≤ (Y:ℝ) / (r:ℝ) := by
  rw [shortContKernel_fourier hY, norm_mul, norm_mul, norm_div, norm_e, mul_one]
  simp only [Complex.norm_natCast]
  exact (mul_le_mul_of_nonneg_left
    ((Real.norm_fourier_le_integral_norm shortBump _).trans shortBump_L1)
    (by positivity : 0 ≤ (Y:ℝ) / r)).trans_eq (by ring)

private lemma shortBump_derivative (x : ℝ) :
    HasDerivAt shortBump (quarticBumpDeriv x : ℂ) x :=
  (hasDerivAt_quarticBump x).ofReal_comp

private lemma fourier_shortBump_decay (u : ℝ) :
    ‖𝓕 shortBump u‖ * |u| ≤ 2 := by
  let g : ℝ → ℝ := (Ioc (0:ℝ) 1).indicator (fun _ ↦ 8)
  have hg : Integrable g :=
    (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (by simp))
  have hd : ∀ x, ‖deriv shortBump x‖ ≤ g x := by
    intro x
    by_cases hx : x ∈ Ioc (0:ℝ) 1
    · rw [show g x = 8 from indicator_of_mem hx _]
      apply norm_deriv_le_of_lip' (by norm_num)
      filter_upwards with y
      simpa [shortBump, ← Complex.ofReal_sub, Real.norm_eq_abs] using
        quarticBump_lipschitz y x
    · have hz : ¬ (0 < x ∧ x < 1) := fun h ↦ hx ⟨h.1, h.2.le⟩
      simp [g, hx, (shortBump_derivative x).deriv, quarticBumpDeriv, hz]
  have hdi : Integrable (deriv shortBump) :=
    hg.mono' (measurable_deriv _).aestronglyMeasurable (ae_of_all _ hd)
  have hF := Real.norm_fourier_le_integral_norm (deriv shortBump) u
  rw [Real.fourier_deriv shortBump_integrable
    (fun x ↦ (shortBump_derivative x).differentiableAt) hdi] at hF
  simp only [smul_eq_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos] at hF
  have hg8 : ∫ x, g x = 8 := by simp [g, integral_indicator measurableSet_Ioc]
  have h8 := (integral_mono hdi.norm hg hd).trans_eq hg8
  norm_num at hF
  nlinarith [Real.pi_gt_three, mul_nonneg (norm_nonneg (𝓕 shortBump u)) (abs_nonneg u),
    mul_nonneg (by linarith [Real.pi_gt_three] : 0 ≤ Real.pi - 2)
      (mul_nonneg (norm_nonneg (𝓕 shortBump u)) (abs_nonneg u))]

lemma shortContKernel_bound_decay {r Y : ℕ} (hY : 1 ≤ Y)
    (b : ℕ) {β : ℝ} (hβ : β ≠ 0) : ‖shortContKernel r b Y β‖ ≤ 2 / |β| := by
  apply (le_div_iff₀ (abs_pos.mpr hβ)).2
  rw [shortContKernel_fourier hY, norm_mul, norm_mul, norm_div, norm_e, mul_one]
  simp only [Complex.norm_natCast]
  have h := fourier_shortBump_decay (-(β / (r:ℝ) * (Y:ℝ)))
  simp only [abs_neg, abs_mul, abs_div, Nat.abs_cast] at h
  change (Y:ℝ) / r * ‖𝓕 shortBump _‖ * |β| ≤ 2
  convert h using 1; ring

private lemma fourier_shortBump_square_integrable :
    Integrable (fun t : ℝ ↦ 𝓕 shortBump t * 𝓕 shortBump t) := by
  have hc : Continuous (𝓕 shortBump) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ shortBump_integrable
  refine (integrable_inv_one_add_sq.const_mul 5).mono' (hc.mul hc).aestronglyMeasurable ?_
  filter_upwards with t
  rw [norm_mul, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have h := fourier_shortBump_decay t
  have h' := (Real.norm_fourier_le_integral_norm shortBump t).trans shortBump_L1
  have hs := pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (abs_nonneg t)) h 2
  have hs' := pow_le_pow_left₀ (norm_nonneg _) h' 2
  rw [mul_pow, sq_abs] at hs
  nlinarith

noncomputable def shortBumpConvolution (v : ℝ) : ℝ :=
  ∫ x, quarticBump x * quarticBump (v - x)

private lemma fourier_shortBump_square_inverse (v : ℝ) :
    (∫ u, e (u*v) * (𝓕 shortBump u * 𝓕 shortBump u)) =
      (shortBumpConvolution v : ℂ) := by
  let B := ContinuousLinearMap.mul ℂ ℂ
  have hint := shortBump_integrable.integrable_convolution B shortBump_integrable
  have hc := shortBump_support.continuous_convolution_right B
    shortBump_integrable.locallyIntegrable shortBump_continuous
  have hF : 𝓕 (shortBump ⋆[B] shortBump) = fun u ↦ 𝓕 shortBump u * 𝓕 shortBump u :=
    funext (Real.fourier_mul_convolution_eq shortBump_integrable shortBump_integrable)
  have hinv := hint.fourierInv_fourier_eq (hF ▸ fourier_shortBump_square_integrable)
    (hc.continuousAt (x := v))
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul, hF,
    convolution_def] at hinv
  have hphys : (∫ t, B (shortBump t) (shortBump (v-t))) = (shortBumpConvolution v : ℂ) := by
    change (∫ t, (quarticBump t : ℂ) * (quarticBump (v-t) : ℂ)) = _
    simp only [← Complex.ofReal_mul, integral_complex_ofReal, shortBumpConvolution]
  rw [← hphys, ← hinv]
  apply integral_congr_ae
  filter_upwards with u
  simp only [smul_eq_mul, e]
  congr 2; push_cast; ring

lemma shortBumpConvolution_lower {v : ℝ} (hv₁ : 1/2 ≤ v) (hv₂ : v ≤ 1) :
    (1:ℝ) / 16384 ≤ shortBumpConvolution v := by
  let I := Ioc (v/2 - 1/8) (v/2 + 1/8)
  let f := fun x ↦ quarticBump x * quarticBump (v-x)
  have hi : Integrable f := by
    refine (continuous_quarticBump.mul
      (continuous_quarticBump.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (isCompact_Icc (a := (0:ℝ)) (b := 1)) ?_
    intro x hx
    have h : ¬ (0 < x ∧ x < 1) := fun h ↦ hx ⟨h.1.le, h.2.le⟩
    simp [quarticBump_eq_zero_of_not_mem h]
  calc
    (1:ℝ)/16384 = ∫ _ in I, (1:ℝ)/4096 := by
      simp [I]
      ring
    _ ≤ ∫ x in I, f x := by
      apply setIntegral_mono_on (integrableOn_const (by simp)) hi.integrableOn measurableSet_Ioc
      intro x hx
      have hx' : v/2 - 1/8 < x ∧ x ≤ v/2 + 1/8 := hx
      have h1 := quarticBump_ge_on_core (x := x) (by linarith) (by linarith)
      have h2 := quarticBump_ge_on_core (x := v-x) (by linarith) (by linarith)
      exact (by norm_num : (1:ℝ)/4096 = (1/64)*(1/64)).trans_le
        (mul_le_mul h1 h2 (by norm_num) (quarticBump_nonneg _))
    _ ≤ shortBumpConvolution v := setIntegral_le_integral hi
      (ae_of_all _ fun x ↦ mul_nonneg (quarticBump_nonneg _) (quarticBump_nonneg _))

/-- Completion over the real line has precisely the quartic convolution mass in the physical
progression variable. The translating phases recover the original, uncompressed target. -/
theorem integral_shortContKernel_mul_e {r Y : ℕ} (hr : 0 < r) (hY : 1 ≤ Y)
    (b₁ b₂ k : ℕ) :
    (∫ β : ℝ, shortContKernel r b₁ Y β * shortContKernel r b₂ Y β * e (-((k:ℝ)*β))) =
      (((Y:ℝ)/r) * shortBumpConvolution (((r:ℝ)*k+b₁+b₂)/Y) : ℝ) := by
  let H := (Y:ℝ) / r
  let v := ((r:ℝ)*k+b₁+b₂)/Y
  let F (u : ℝ) := e (u*v) * (𝓕 shortBump u * 𝓕 shortBump u)
  have hY0 : (Y:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hr0 : (r:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hH : 0 < H := div_pos (by positivity) (by positivity)
  have hpt (β : ℝ) :
      shortContKernel r b₁ Y β * shortContKernel r b₂ Y β * e (-((k:ℝ)*β)) =
        (H:ℂ)^2 * F (-H*β) := by
    simp only [shortContKernel_fourier hY]
    have ht : -(β / (r:ℝ) * (Y:ℝ)) = -H*β := by dsimp [H]; ring
    simp only [ht]
    have he : e (-(β * (b₁:ℝ) / r)) * e (-(β * (b₂:ℝ) / r)) * e (-((k:ℝ)*β)) =
        e ((-H*β)*v) := by
      rw [← e_add, ← e_add]; congr 1; dsimp [H, v]; field_simp; ring
    change _ = (H:ℂ)^2 * (e ((-H*β)*v) * (𝓕 shortBump _ * 𝓕 shortBump _))
    rw [← he]
    change (Y:ℂ)/r * _ * 𝓕 shortBump _ * ((Y:ℂ)/r * _ * 𝓕 shortBump _) * _ = _
    simp only [H, Complex.ofReal_div, Complex.ofReal_natCast]; ring
  simp_rw [hpt]
  rw [integral_const_mul, Measure.integral_comp_mul_left,
    show (∫ u, F u) = (shortBumpConvolution v : ℂ) from fourier_shortBump_square_inverse v]
  rw [abs_inv, abs_neg, abs_of_pos hH, Complex.real_smul, Complex.ofReal_inv]
  change _ = ((H * shortBumpConvolution v : ℝ) : ℂ)
  rw [Complex.ofReal_mul]
  field_simp [show (H:ℂ) ≠ 0 by exact_mod_cast hH.ne']

private lemma shortE_neg (u : ℝ) : e (-u) = conj (e u) := by
  simp only [e, ← Complex.exp_conj, Complex.ofReal_neg, map_mul, map_ofNat,
    Complex.conj_ofReal, Complex.conj_I]; congr 1; ring

private lemma shortCont_integrand_neg {Y : ℕ} (hY : 1 ≤ Y) (r b₁ b₂ k : ℕ) (β : ℝ) :
    shortContKernel r b₁ Y (-β) * shortContKernel r b₂ Y (-β) * e (-((k:ℝ)*(-β))) =
      conj (shortContKernel r b₁ Y β * shortContKernel r b₂ Y β * e (-((k:ℝ)*β))) := by
  have hk (b : ℕ) : shortContKernel r b Y (-β) = conj (shortContKernel r b Y β) := by
    have he : -(-β * (b:ℝ) / r) = -(-(β * (b:ℝ) / r)) := by ring
    have hI : (∫ x in (0:ℝ)..Y, scaledTiltedBump Y (-β / r) x) =
        conj (∫ x in (0:ℝ)..Y, scaledTiltedBump Y (β / r) x) := by
      rw [← intervalIntegral.intervalIntegral_conj]
      apply intervalIntegral.integral_congr
      intro x _
      simp only [scaledTiltedBump, map_mul, Complex.conj_ofReal, neg_div, neg_mul, shortE_neg]
    simp only [shortContKernel, mellin_scaledTiltedBump_one hY, map_mul, map_inv₀, map_natCast,
      he, shortE_neg (-(β * (b:ℝ) / r)), hI]
  rw [hk, hk, show -((k:ℝ) * -β) = -(-((k:ℝ)*β)) by ring, shortE_neg, map_mul, map_mul]

private lemma shortCont_unit_im {Y : ℕ} (hY : 1 ≤ Y) (r b₁ b₂ k : ℕ) :
    (∫ β in (-(1/2):ℝ)..1/2,
      shortContKernel r b₁ Y β * shortContKernel r b₂ Y β * e (-((k:ℝ)*β))).im = 0 := by
  let f := fun β ↦ shortContKernel r b₁ Y β * shortContKernel r b₂ Y β * e (-((k:ℝ)*β))
  have h : ∫ β in (-(1/2):ℝ)..1/2, f β = conj (∫ β in (-(1/2):ℝ)..1/2, f β) := by
    have hs := intervalIntegral.integral_comp_neg (f := f) (a := (-(1/2):ℝ)) (b := 1/2)
    rw [neg_neg] at hs
    refine hs.symm.trans ?_
    rw [← intervalIntegral.intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro β _
    exact shortCont_integrand_neg hY r b₁ b₂ k β
  have hh := congrArg Complex.im h
  change _ = -_ at hh
  change (∫ β in (-(1/2):ℝ)..1/2, f β).im = 0
  linarith

lemma shortCont_unit_tail {Y : ℕ} (hY : 1 ≤ Y) (r b₁ b₂ k : ℕ) :
    let f := fun β ↦ shortContKernel r b₁ Y β * shortContKernel r b₂ Y β * e (-((k:ℝ)*β))
    ‖(∫ β, f β) - (∫ β in (-(1/2):ℝ)..1/2, f β)‖ ≤ 80 := by
  intro f
  let I := Ioc (-(1/2):ℝ) (1/2)
  have hc : Continuous f := ((continuous_shortContKernel hY r b₁).mul
    (continuous_shortContKernel hY r b₂)).mul
    (continuous_e_real.comp (continuous_const.mul continuous_id).neg)
  have hd : ∀ x ∈ Iᶜ, ‖f x‖ ≤ 20 * (1+x^2)⁻¹ := by
    intro x hx
    have hhalf : 1/2 ≤ |x| := by
      by_contra! h
      exact hx ⟨(abs_lt.mp h).1, (abs_lt.mp h).2.le⟩
    have h0 : x ≠ 0 := by rintro rfl; norm_num at hhalf
    have hx2 : 1/4 ≤ x^2 := by nlinarith [sq_abs x, sq_nonneg (|x|-1/2)]
    change ‖_ * _ * e _‖ ≤ _
    rw [norm_mul, norm_mul, norm_e, mul_one]
    refine (mul_le_mul (shortContKernel_bound_decay hY b₁ h0)
      (shortContKernel_bound_decay hY b₂ h0) (norm_nonneg _) (by positivity)).trans ?_
    rw [div_mul_div_comm, ← sq, ← sq, sq_abs, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  have hg := integrable_inv_one_add_sq.const_mul (20:ℝ)
  have hfi : Integrable f := by
    rw [← integrableOn_univ, ← union_compl_self I]
    apply IntegrableOn.union hc.integrableOn_Ioc
    exact hg.integrableOn.mono' hc.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc.compl).2 (ae_of_all _ hd))
  rw [intervalIntegral.integral_of_le (by norm_num)]
  change ‖_ - ∫ x in I, f x‖ ≤ _
  rw [← setIntegral_compl measurableSet_Ioc hfi]
  refine (norm_integral_le_of_norm_le hg.integrableOn
    ((ae_restrict_iff' measurableSet_Ioc.compl).2 (ae_of_all _ hd))).trans ?_
  refine (setIntegral_le_integral hg (ae_of_all _ fun x ↦ by positivity)).trans ?_
  rw [integral_const_mul, integral_univ_inv_one_add_sq]
  linarith [Real.pi_lt_four]


/-- The continuous short-window model supplies a pointwise lower coefficient for every
admissible target and every cutoff whose square fits inside the ambient progression. -/
theorem shortContModel_conv_re_lower {r b₁ b₂ Y k Q : ℕ} (hr : 0 < r) (_hb₁ : b₁ < r)
    (_hb₂ : b₂ < r) (hn_lo : Y / 2 < r*k+b₁+b₂) (hn_hi : r*k+b₁+b₂ ≤ Y)
    (hn_even : Even (r*k+b₁+b₂)) (hQ_ge2 : 2 ≤ Q)
    (hQsmall : (2:ℝ)^24*(Q:ℝ)^2 ≤ (Y:ℝ)/r) :
    ((1:ℝ)/262144)*((r:ℝ)/(r.totient:ℝ))^2*((Y:ℝ)/r) ≤
      (∫ α in (0:ℝ)..1, shortContModel r b₁ Y Q α * shortContModel r b₂ Y Q α *
        e (-((k:ℝ)*α))).re := by
  set n := r*k+b₁+b₂
  have hn_pos : 0 < n := by omega
  have hY : 1 ≤ Y := by omega
  have hQ_pos : 0 < Q := by omega
  let Cset := (centers Q).filter (fun c => c.q ≤ Q)
  -- Step 1: Decompose integral over `Cset` using disjointness of Voronoi cells.
  have hpt : ∀ α : ℝ,
      shortContModel r b₁ Y Q α * shortContModel r b₂ Y Q α * e (-((k : ℝ) * α)) =
      ∑ c ∈ Cset, (voronoiCell Q c).indicator
        (fun x => modelCoeff r b₁ c * modelCoeff r b₂ c *
          shortContKernel r b₁ Y (wrap (x - c.val)) *
          shortContKernel r b₂ Y (wrap (x - c.val)) * e (-((k : ℝ) * x))) α := by
    intro α
    unfold shortContModel
    rw [mul_sum_disjoint_indicator Cset (voronoiCell Q) (fun c₁ _ c₂ _ hne => voronoiCell_disjoint hne)]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hα : α ∈ voronoiCell Q c
    · rw [Set.indicator_of_mem hα, Set.indicator_of_mem hα]; ring
    · rw [Set.indicator_of_notMem hα, Set.indicator_of_notMem hα, zero_mul]
  simp_rw [hpt]
  have hint_c : ∀ c ∈ Cset,
      IntervalIntegrable
        ((voronoiCell Q c).indicator
          (fun x => modelCoeff r b₁ c * modelCoeff r b₂ c *
            shortContKernel r b₁ Y (wrap (x - c.val)) *
            shortContKernel r b₂ Y (wrap (x - c.val)) * e (-((k : ℝ) * x))))
        MeasureTheory.volume 0 1 := by
    intro c _
    have hmeas : Measurable ((voronoiCell Q c).indicator
        (fun x => modelCoeff r b₁ c * modelCoeff r b₂ c *
          shortContKernel r b₁ Y (wrap (x - c.val)) *
          shortContKernel r b₂ Y (wrap (x - c.val)) * e (-((k : ℝ) * x)))) := by
      have he_meas : Measurable (fun x : ℝ => e (-((k : ℝ) * x))) := by
        have h : (fun x : ℝ => e (-((k : ℝ) * x))) = fun x : ℝ => e (-(k : ℝ) * x) := by funext x; ring_nf
        rw [h]; exact (continuous_e_mul (-(k : ℝ))).measurable
      refine Measurable.indicator ?_ (voronoiCell_measurable Q c)
      exact (((measurable_const.mul
        ((continuous_shortContKernel hY r b₁).measurable.comp (measurable_wrap.comp (measurable_id.sub measurable_const)))).mul
        ((continuous_shortContKernel hY r b₂).measurable.comp (measurable_wrap.comp (measurable_id.sub measurable_const)))).mul
        he_meas)
    refine intervalIntegrable_of_measurable_bounded
      (B := ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ * ((Y : ℝ) / (r : ℝ)) ^ 2) hmeas ?_
    intro x
    by_cases hx : x ∈ voronoiCell Q c
    · rw [Set.indicator_of_mem hx, norm_mul, norm_mul, norm_mul, norm_mul, norm_e, mul_one]
      have h1 := shortContKernel_bound_triv hY r b₁ (wrap (x - c.val))
      have h2 := shortContKernel_bound_triv hY r b₂ (wrap (x - c.val))
      have hprod : ‖shortContKernel r b₁ Y (wrap (x - c.val))‖ * ‖shortContKernel r b₂ Y (wrap (x - c.val))‖ ≤
          ((Y : ℝ) / (r : ℝ)) ^ 2 := by
        rw [sq]; exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      calc ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ *
            ‖shortContKernel r b₁ Y (wrap (x - c.val))‖ * ‖shortContKernel r b₂ Y (wrap (x - c.val))‖
          = ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ *
            (‖shortContKernel r b₁ Y (wrap (x - c.val))‖ * ‖shortContKernel r b₂ Y (wrap (x - c.val))‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by positivity)
    · rw [Set.indicator_of_notMem hx, norm_zero]; positivity
  rw [intervalIntegral_finset_sum hint_c]
  -- Step 2: Compare cell integrals with completed `[-1/2, 1/2]` integrals.
  let fullConv : ℂ :=
    ∫ β in (-(1 / 2) : ℝ)..(1 / 2),
      shortContKernel r b₁ Y β * shortContKernel r b₂ Y β * e (-((k : ℝ) * β))
  let completed : ℂ :=
    ∑ c ∈ Cset, modelCoeff r b₁ c * modelCoeff r b₂ c * e (-((k : ℝ) * c.val)) * fullConv
  have hcomp_err :
      ‖(∑ c ∈ Cset, ∫ α in (0 : ℝ)..1,
          (voronoiCell Q c).indicator
            (fun x => modelCoeff r b₁ c * modelCoeff r b₂ c *
              shortContKernel r b₁ Y (wrap (x - c.val)) *
              shortContKernel r b₂ Y (wrap (x - c.val)) * e (-((k : ℝ) * x))) α) - completed‖ ≤
      48 * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * (Q : ℝ) * (Q : ℝ) := by
    dsimp [completed]
    rw [← Finset.sum_sub_distrib]
    have hcell_err : ∀ c ∈ Cset,
        ‖(∫ α in (0 : ℝ)..1,
            (voronoiCell Q c).indicator
              (fun x => modelCoeff r b₁ c * modelCoeff r b₂ c *
                shortContKernel r b₁ Y (wrap (x - c.val)) *
                shortContKernel r b₂ Y (wrap (x - c.val)) * e (-((k : ℝ) * x))) α) -
          modelCoeff r b₁ c * modelCoeff r b₂ c * e (-((k : ℝ) * c.val)) * fullConv‖ ≤
        ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ * (16 * (c.q : ℝ) * (Q : ℝ)) := by
      intro c hc
      have hc_mem : c ∈ centers Q := (Finset.mem_filter.mp hc).1
      have hper : Function.Periodic ((voronoiCell Q c).indicator
          (fun x => modelCoeff r b₁ c * modelCoeff r b₂ c *
            shortContKernel r b₁ Y (wrap (x - c.val)) *
            shortContKernel r b₂ Y (wrap (x - c.val)) * e (-((k : ℝ) * x)))) 1 := by
        intro x
        by_cases hx : x ∈ voronoiCell Q c
        · rw [Set.indicator_of_mem ((voronoiCell_periodic Q c x).2 hx), Set.indicator_of_mem hx]
          have h1 : x + 1 - c.val = (x - c.val) + 1 := by ring
          have h2 : -((k : ℝ) * (x + 1)) = -((k : ℝ) * x) + ((-(k : ℤ) : ℤ) : ℝ) := by
            rw [Int.cast_neg, Int.cast_natCast]; ring
          rw [h1, wrap_add_one, h2, e_add_int]
        · rw [Set.indicator_of_notMem (fun h => hx ((voronoiCell_periodic Q c x).1 h)), Set.indicator_of_notMem hx]
      rw [intervalIntegral_shift_symm hper c.val]
      dsimp [fullConv]
      rw [← intervalIntegral.integral_const_mul]
      let f_cell : ℝ → ℂ := fun β =>
        (voronoiCell Q c).indicator
          (fun x => modelCoeff r b₁ c * modelCoeff r b₂ c *
            shortContKernel r b₁ Y (wrap (x - c.val)) *
            shortContKernel r b₂ Y (wrap (x - c.val)) * e (-((k : ℝ) * x))) (c.val + β)
      let f_full : ℝ → ℂ := fun β =>
        modelCoeff r b₁ c * modelCoeff r b₂ c * e (-((k : ℝ) * c.val)) *
          (shortContKernel r b₁ Y β * shortContKernel r b₂ Y β * e (-((k : ℝ) * β)))
      have hf_cell_int : IntervalIntegrable f_cell MeasureTheory.volume (-(1 / 2)) (1 / 2) := by
        have he_meas : Measurable (fun x : ℝ => e (-((k : ℝ) * x))) := by
          have h : (fun x : ℝ => e (-((k : ℝ) * x))) = fun x : ℝ => e (-(k : ℝ) * x) := by funext x; ring_nf
          rw [h]; exact (continuous_e_mul (-(k : ℝ))).measurable
        have hm0 : Measurable ((voronoiCell Q c).indicator
            (fun x => modelCoeff r b₁ c * modelCoeff r b₂ c *
              shortContKernel r b₁ Y (wrap (x - c.val)) *
              shortContKernel r b₂ Y (wrap (x - c.val)) * e (-((k : ℝ) * x)))) :=
          Measurable.indicator
            (((measurable_const.mul
              ((continuous_shortContKernel hY r b₁).measurable.comp (measurable_wrap.comp (measurable_id.sub measurable_const)))).mul
              ((continuous_shortContKernel hY r b₂).measurable.comp (measurable_wrap.comp (measurable_id.sub measurable_const)))).mul
              he_meas)
            (voronoiCell_measurable Q c)
        refine intervalIntegrable_of_measurable_bounded
          (B := ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ * ((Y : ℝ) / (r : ℝ)) ^ 2)
          (hm0.comp (measurable_const.add measurable_id)) ?_
        intro β; dsimp [f_cell]
        by_cases hx : c.val + β ∈ voronoiCell Q c
        · rw [Set.indicator_of_mem hx, norm_mul, norm_mul, norm_mul, norm_mul, norm_e, mul_one]
          have h1 := shortContKernel_bound_triv hY r b₁ (wrap (c.val + β - c.val))
          have h2 := shortContKernel_bound_triv hY r b₂ (wrap (c.val + β - c.val))
          have hprod : ‖shortContKernel r b₁ Y (wrap (c.val + β - c.val))‖ *
              ‖shortContKernel r b₂ Y (wrap (c.val + β - c.val))‖ ≤ ((Y : ℝ) / (r : ℝ)) ^ 2 := by
            rw [sq]; exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
          calc ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ *
                ‖shortContKernel r b₁ Y (wrap (c.val + β - c.val))‖ *
                ‖shortContKernel r b₂ Y (wrap (c.val + β - c.val))‖
              = ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ *
                (‖shortContKernel r b₁ Y (wrap (c.val + β - c.val))‖ *
                 ‖shortContKernel r b₂ Y (wrap (c.val + β - c.val))‖) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by positivity)
        · rw [Set.indicator_of_notMem hx, norm_zero]; positivity
      have hf_full_int : IntervalIntegrable f_full MeasureTheory.volume (-(1 / 2)) (1 / 2) := by
        have hcont : Continuous f_full := by
          dsimp [f_full]
          refine continuous_const.mul (((continuous_shortContKernel hY r b₁).mul (continuous_shortContKernel hY r b₂)).mul ?_)
          have h : (fun β : ℝ => e (-((k : ℝ) * β))) = fun β : ℝ => e (-(k : ℝ) * β) := by funext β; ring_nf
          rw [h]; exact continuous_e_mul (-(k : ℝ))
        exact hcont.intervalIntegrable _ _
      change ‖(∫ β in (-(1 / 2) : ℝ)..(1 / 2), f_cell β) - (∫ β in (-(1 / 2) : ℝ)..(1 / 2), f_full β)‖ ≤ _
      rw [← intervalIntegral.integral_sub hf_cell_int hf_full_int]
      set δ := 1 / (2 * (c.q : ℝ) * (Q : ℝ))
      let maj : ℝ → ℝ := fun β =>
        (‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖) * (if |β| < δ then 0 else 4 / β ^ 2)
      have hmaj_int : IntervalIntegrable maj MeasureTheory.volume (-(1 / 2)) (1 / 2) := by
        have hδ_pos : 0 < δ := by
          dsimp [δ]; have : (0 : ℝ) < c.q := Nat.cast_pos.mpr c.q_pos; positivity
        have hmeas : Measurable maj :=
          measurable_const.mul (Measurable.ite (measurableSet_lt continuous_abs.measurable measurable_const)
            measurable_const (measurable_const.div (measurable_id.pow_const 2)))
        refine intervalIntegrable_of_measurable_bounded
          (B := ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ * (4 / δ ^ 2)) hmeas ?_
        intro β; rw [Real.norm_eq_abs]; dsimp [maj]
        split_ifs with h
        · rw [mul_zero, abs_zero]; positivity
        · rw [abs_of_nonneg (by positivity)]
          have hge : δ ≤ |β| := not_lt.mp h
          have hsq : δ ^ 2 ≤ β ^ 2 := by rw [← sq_abs β]; exact pow_le_pow_left₀ hδ_pos.le hge 2
          exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by norm_num) (pow_pos hδ_pos 2) hsq) (by positivity)
      have hnorm_le : ‖∫ β in (-(1 / 2) : ℝ)..(1 / 2), (f_cell β - f_full β)‖ ≤
          ∫ β in (-(1 / 2) : ℝ)..(1 / 2), maj β := by
        refine intervalIntegral.norm_integral_le_of_norm_le (by norm_num) ?_ hmaj_int
        filter_upwards [volume.ae_ne (1/2:ℝ)] with β hβne hβ
        have hwrap : wrap β = β := wrap_eq_self_of_abs_lt_half
          (abs_lt.mpr ⟨hβ.1, lt_of_le_of_ne hβ.2 hβne⟩)
        by_cases hlt : |β| < δ
        · have hmem : c.val + β ∈ voronoiCell Q c := voronoiCell_inner_subset_beta hQ_pos hc_mem hlt
          have hsub0 : f_cell β - f_full β = 0 := by
            dsimp [f_cell, f_full]; rw [Set.indicator_of_mem hmem]
            have hs : c.val + β - c.val = β := by ring
            have he : e (-((k : ℝ) * (c.val + β))) = e (-((k : ℝ) * c.val)) * e (-((k : ℝ) * β)) := by
              rw [← e_add]; congr 1; ring
            rw [hs, hwrap, he]; ring
          rw [hsub0, norm_zero]; dsimp [maj]; rw [ite_eq_left hlt, mul_zero]
        · have hβ0 : β ≠ 0 := by
            intro hz; subst hz; rw [abs_zero] at hlt
            have hδ_pos : 0 < δ := by
              dsimp [δ]; have : (0 : ℝ) < c.q := Nat.cast_pos.mpr c.q_pos; positivity
            exact hlt hδ_pos
          have hpt_le : ‖f_cell β - f_full β‖ ≤ ‖f_full β‖ := by
            by_cases hmem : c.val + β ∈ voronoiCell Q c
            · have hsub0 : f_cell β - f_full β = 0 := by
                dsimp [f_cell, f_full]; rw [Set.indicator_of_mem hmem]
                have hs : c.val + β - c.val = β := by ring
                have he : e (-((k : ℝ) * (c.val + β))) = e (-((k : ℝ) * c.val)) * e (-((k : ℝ) * β)) := by
                  rw [← e_add]; congr 1; ring
                rw [hs, hwrap, he]; ring
              rw [hsub0, norm_zero]; exact norm_nonneg _
            · dsimp [f_cell]; rw [Set.indicator_of_notMem hmem, zero_sub, norm_neg]
          dsimp [maj]; rw [ite_eq_right hlt]
          refine hpt_le.trans ?_
          dsimp [f_full]
          rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_e, norm_e, mul_one, mul_one]
          have hd1 := shortContKernel_bound_decay (r := r) hY b₁ hβ0
          have hd2 := shortContKernel_bound_decay (r := r) hY b₂ hβ0
          have hprod : ‖shortContKernel r b₁ Y β‖ * ‖shortContKernel r b₂ Y β‖ ≤ 4 / β ^ 2 := by
            calc ‖shortContKernel r b₁ Y β‖ * ‖shortContKernel r b₂ Y β‖
                ≤ (2 / |β|) * (2 / |β|) := mul_le_mul hd1 hd2 (norm_nonneg _) (by positivity)
              _ = 4 / β ^ 2 := by rw [div_mul_div_comm, ← sq, ← sq, sq_abs]; norm_num
          exact mul_le_mul_of_nonneg_left hprod (by positivity)
      calc ‖∫ β in (-(1 / 2) : ℝ)..(1 / 2), (f_cell β - f_full β)‖
          ≤ ∫ β in (-(1 / 2) : ℝ)..(1 / 2), maj β := hnorm_le
        _ = (‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖) *
              ∫ β in (-(1 / 2) : ℝ)..(1 / 2), (if |β| < δ then (0 : ℝ) else 4 / β ^ 2) :=
            intervalIntegral.integral_const_mul _ _
        _ ≤ (‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖) * (16 * (c.q : ℝ) * (Q : ℝ)) :=
            mul_le_mul_of_nonneg_left (tail_integral_four_div_sq c.q_pos hQ_ge2) (by positivity)
    calc ‖∑ c ∈ Cset, ((∫ α in (0 : ℝ)..1,
            (voronoiCell Q c).indicator
              (fun x => modelCoeff r b₁ c * modelCoeff r b₂ c *
                shortContKernel r b₁ Y (wrap (x - c.val)) *
                shortContKernel r b₂ Y (wrap (x - c.val)) * e (-((k : ℝ) * x))) α) -
            modelCoeff r b₁ c * modelCoeff r b₂ c * e (-((k : ℝ) * c.val)) * fullConv)‖
        ≤ ∑ c ∈ Cset, ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ * (16 * (c.q : ℝ) * (Q : ℝ)) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum hcell_err)
      _ ≤ 16 * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * (Q : ℝ) *
            ∑ q ∈ (Finset.Icc 1 Q).filter Squarefree, ((q : ℝ) / (q.totient : ℝ)) := by
          let Qsf := (Finset.Icc 1 Q).filter Squarefree
          let Cgood := Cset.filter (fun c => c.q ∈ Qsf)
          have htrim : ∑ c ∈ Cset, ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ * (16 * (c.q : ℝ) * (Q : ℝ)) =
              ∑ c ∈ Cgood, ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ * (16 * (c.q : ℝ) * (Q : ℝ)) := by
            symm; rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun c hc => ?_
            split_ifs with h
            · rfl
            · have h0 : modelCoeff r b₁ c = 0 := by
                unfold modelCoeff
                by_cases hcop : Nat.Coprime c.q r
                · rw [ite_eq_left hcop]
                  have hnsf : ¬ Squarefree c.q := fun hsf =>
                    h (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨c.q_pos, (Finset.mem_filter.mp hc).2⟩, hsf⟩)
                  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsf]; simp
                · exact ite_eq_right hcop
              simp [h0]
          rw [htrim,
              ← Finset.sum_fiberwise_of_maps_to (s := Cgood) (t := Qsf) (g := fun c : RatCenter => c.q)
                (fun c hc => (Finset.mem_filter.mp hc).2),
              Finset.mul_sum]
          refine Finset.sum_le_sum fun q hq => ?_
          have hq_pos : 0 < q := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
          have hq_sf : Squarefree q := (Finset.mem_filter.mp hq).2
          have hcard_a : (Cgood.filter (fun c => c.q = q)).card ≤ q.totient := by
            have hsub : (Cgood.filter (fun c => c.q = q)).image (fun c => c.a) ⊆ coprimeClasses q := by
              intro a ha
              obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ha
              have hcq : c.q = q := (Finset.mem_filter.mp hc).2
              exact mem_coprimeClasses.mpr ⟨hcq ▸ c.a_lt, hcq ▸ c.coprime⟩
            have hinj : Set.InjOn (fun c : RatCenter => c.a) (Cgood.filter (fun c => c.q = q) : Set RatCenter) := by
              intro c₁ h1 c₂ h2 hEq
              exact RatCenter.ext hEq ((Finset.mem_filter.mp h1).2.trans (Finset.mem_filter.mp h2).2.symm)
            rw [← Finset.card_image_of_injOn hinj]
            exact (Finset.card_le_card hsub).trans (le_of_eq (card_coprimeClasses q))
          have hterm_le : ∀ c ∈ Cgood.filter (fun c => c.q = q),
              ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ * (16 * (c.q : ℝ) * (Q : ℝ)) ≤
                (((r : ℝ) / (r.totient : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2) * (16 * (q : ℝ) * (Q : ℝ)) := by
            intro c hc
            have hcq : c.q = q := (Finset.mem_filter.mp hc).2
            rw [hcq]
            have hm_le : ∀ b', ‖modelCoeff r b' c‖ ≤ ((r : ℝ) / (r.totient : ℝ)) / (q.totient : ℝ) := fun b' => by
              unfold modelCoeff; rw [hcq]
              split_ifs with hcop
              · rw [norm_mul, norm_mul, norm_e, one_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
                    abs_of_nonneg (by positivity), Complex.norm_intCast, Complex.norm_natCast,
                    ArithmeticFunction.moebius_apply_of_squarefree hq_sf]
                simp [div_eq_mul_inv]
              · rw [norm_zero]; positivity
            have hmul := mul_le_mul (hm_le b₁) (hm_le b₂) (norm_nonneg _) (by positivity)
            have hsq : (((r : ℝ) / (r.totient : ℝ)) / (q.totient : ℝ)) *
                (((r : ℝ) / (r.totient : ℝ)) / (q.totient : ℝ)) =
                ((r : ℝ) / (r.totient : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2 := by ring
            rw [hsq] at hmul
            exact mul_le_mul_of_nonneg_right hmul (by positivity)
          calc ∑ c ∈ Cgood.filter (fun c => c.q = q),
                ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ * (16 * (c.q : ℝ) * (Q : ℝ))
              ≤ ∑ _c ∈ Cgood.filter (fun c => c.q = q),
                  ((((r : ℝ) / (r.totient : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2) * (16 * (q : ℝ) * (Q : ℝ))) :=
                Finset.sum_le_sum hterm_le
            _ = ((Cgood.filter (fun c => c.q = q)).card : ℝ) *
                  ((((r : ℝ) / (r.totient : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2) * (16 * (q : ℝ) * (Q : ℝ))) := by
                simp [nsmul_eq_mul]
            _ ≤ (q.totient : ℝ) *
                  ((((r : ℝ) / (r.totient : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2) * (16 * (q : ℝ) * (Q : ℝ))) :=
                mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard_a) (by positivity)
            _ = 16 * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * (Q : ℝ) * ((q : ℝ) / (q.totient : ℝ)) := by
                have hqt0 : (q.totient : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hq_pos).ne'
                field_simp [hqt0]
      _ ≤ 16 * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * (Q : ℝ) * (3 * (Q : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_sqfree_div_totient_le Q) (by positivity)
      _ = 48 * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * (Q : ℝ) * (Q : ℝ) := by ring
  have hcomp_eq : completed =
      ((((r : ℝ) / (r.totient : ℝ)) ^ 2 : ℝ) : ℂ) * singularTrunc r n Q * fullConv := by
    dsimp only [completed]
    rw [← Finset.sum_mul]
    congr 1
    unfold singularTrunc
    rw [Finset.mul_sum]
    let Qcop := (Finset.Icc 1 Q).filter (fun q => Nat.Coprime q r)
    let Ccop := Cset.filter (fun c => c.q ∈ Qcop)
    have htrim : ∑ c ∈ Cset, modelCoeff r b₁ c * modelCoeff r b₂ c * e (-((k : ℝ) * c.val)) =
        ∑ c ∈ Ccop, modelCoeff r b₁ c * modelCoeff r b₂ c * e (-((k : ℝ) * c.val)) := by
      symm; rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun c hc => ?_
      split_ifs with h
      · rfl
      · have hncop : ¬ Nat.Coprime c.q r := fun hcop =>
          h (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨c.q_pos, (Finset.mem_filter.mp hc).2⟩, hcop⟩)
        unfold modelCoeff
        rw [ite_eq_right hncop, zero_mul, zero_mul]
    rw [htrim,
        ← Finset.sum_fiberwise_of_maps_to (s := Ccop) (t := Qcop) (g := fun c : RatCenter => c.q)
          (fun c hc => (Finset.mem_filter.mp hc).2)]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
    have hq_pos : 0 < q := hq_Icc.1
    have hq_le_Q : q ≤ Q := hq_Icc.2
    have hq_cop : Nat.Coprime q r := (Finset.mem_filter.mp hq).2
    have hbij : ∑ c ∈ Ccop.filter (fun c => c.q = q),
          modelCoeff r b₁ c * modelCoeff r b₂ c * e (-((k : ℝ) * c.val)) =
        ((((r : ℝ) / (r.totient : ℝ)) ^ 2 : ℝ) : ℂ) *
          ((ArithmeticFunction.moebius q : ℂ) ^ 2 / (q.totient : ℂ) ^ 2) *
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            e (-((a : ℝ) * (rInv r q : ℝ) * (b₁ : ℝ) / (q : ℝ))) *
            e (-((a : ℝ) * (rInv r q : ℝ) * (b₂ : ℝ) / (q : ℝ))) *
            e (-((k : ℝ) * ((a : ℝ) / (q : ℝ)))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun c _ => c.a) ?_ ?_ ?_ ?_
      · intro c hc
        have hcq : c.q = q := (Finset.mem_filter.mp hc).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hcq ▸ c.a_lt), hcq ▸ c.coprime⟩
      · intro c₁ h1 c₂ h2 hEq
        exact RatCenter.ext hEq ((Finset.mem_filter.mp h1).2.trans (Finset.mem_filter.mp h2).2.symm)
      · intro a ha
        have ha_lt := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
        have ha_cop := (Finset.mem_filter.mp ha).2
        let c : RatCenter := ⟨a, q, hq_pos, ha_lt, ha_cop⟩
        refine ⟨c, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨mem_centers_iff.mpr hq_le_Q, hq_le_Q⟩, hq⟩, rfl⟩
      · intro c hc
        have hcq : c.q = q := (Finset.mem_filter.mp hc).2
        unfold modelCoeff RatCenter.val
        rw [hcq, ite_eq_left hq_cop, ite_eq_left hq_cop]
        push_cast; ring
    rw [hbij, sum_modelCoeff_mul_e_eq_ramanujan hq_pos hq_cop]
    ring
  have hmain_re : ((1:ℝ)/131072)*((r:ℝ)/(r.totient:ℝ))^2*((Y:ℝ)/r) ≤ completed.re := by
    have him : fullConv.im = 0 := shortCont_unit_im hY r b₁ b₂ k
    have hsing := singularTrunc_re_ge_quarter hr hn_pos hn_even (by omega : 1 ≤ Q)
    have htail := shortCont_unit_tail hY r b₁ b₂ k
    dsimp only at htail
    rw [integral_shortContKernel_mul_e hr hY] at htail
    have hre := (Complex.abs_re_le_norm _).trans htail
    rw [Complex.sub_re, Complex.ofReal_re] at hre
    have hYpos : (0:ℝ) < Y := by positivity
    have hv₁ : 1/2 ≤ ((r:ℝ)*k+b₁+b₂)/Y := by
      apply (le_div_iff₀ hYpos).2
      have hnat : Y ≤ 2*(r*k+b₁+b₂) := by omega
      have hcast : (Y:ℝ) ≤ 2*((r:ℝ)*k+b₁+b₂) := by exact_mod_cast hnat
      linarith
    have hv₂ : ((r:ℝ)*k+b₁+b₂)/Y ≤ 1 := by
      apply (div_le_iff₀ hYpos).2
      simpa using (show (r:ℝ)*k+b₁+b₂ ≤ Y by exact_mod_cast hn_hi)
    have hconv := mul_le_mul_of_nonneg_left (shortBumpConvolution_lower hv₁ hv₂)
      (by positivity : 0 ≤ (Y:ℝ)/r)
    have hQ2 : (2:ℝ) ≤ Q := by exact_mod_cast hQ_ge2
    have hlarge : 2621440 ≤ (Y:ℝ)/r := by nlinarith [sq_nonneg ((Q:ℝ)-2)]
    have hfull : (1/32768:ℝ)*((Y:ℝ)/r) ≤ fullConv.re := by
      have hh := (abs_le.mp hre).2
      change _ - fullConv.re ≤ 80 at hh
      linarith
    have hn := mul_le_mul hsing hfull (by positivity) (by linarith)
    rw [hcomp_eq]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, him, mul_zero, zero_mul,
      sub_zero]
    have hm := mul_le_mul_of_nonneg_left hn (sq_nonneg ((r:ℝ)/(r.totient:ℝ)))
    linarith
  have herr_small : 48*((r:ℝ)/(r.totient:ℝ))^2*(Q:ℝ)*(Q:ℝ) ≤
      ((1:ℝ)/262144)*((r:ℝ)/(r.totient:ℝ))^2*((Y:ℝ)/r) := by
    have hh : 48*(Q:ℝ)^2 ≤ ((1:ℝ)/262144)*((Y:ℝ)/r) := by nlinarith [sq_nonneg (Q:ℝ)]
    have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg ((r:ℝ)/(r.totient:ℝ)))
    linarith
  have hre_diff : |(∑ c ∈ Cset, ∫ α in (0 : ℝ)..1,
      (voronoiCell Q c).indicator
        (fun x => modelCoeff r b₁ c * modelCoeff r b₂ c *
          shortContKernel r b₁ Y (wrap (x - c.val)) *
          shortContKernel r b₂ Y (wrap (x - c.val)) * e (-((k : ℝ) * x))) α).re - completed.re| ≤
      48 * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * (Q : ℝ) * (Q : ℝ) := by
    have h1 := Complex.abs_re_le_norm ((∑ c ∈ Cset, ∫ α in (0 : ℝ)..1,
      (voronoiCell Q c).indicator
        (fun x => modelCoeff r b₁ c * modelCoeff r b₂ c *
          shortContKernel r b₁ Y (wrap (x - c.val)) *
          shortContKernel r b₂ Y (wrap (x - c.val)) * e (-((k : ℝ) * x))) α) - completed)
    rw [Complex.sub_re] at h1
    exact h1.trans hcomp_err
  have hre_lo := (abs_le.mp hre_diff).1
  linarith

end FareyGoldbach
