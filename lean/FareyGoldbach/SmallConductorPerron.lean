import FareyGoldbach.SmallConductorKernel
import FareyGoldbach.SharpPerronInversion

/-! # Smoothing and inversion on the right-hand line -/

open Finset MeasureTheory Set

namespace FareyGoldbach

private noncomputable def rampCutoff (X : ℕ) (δ : ℝ) : ℕ :=
  ⌊Real.exp (2*δ)*(X:ℝ)⌋₊

noncomputable def smallConductorWeightedVonMangoldt {d : ℕ} [NeZero d]
    (χ : DirichletCharacter ℂ d) (X : ℕ) (δ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (rampCutoff X δ), (ArithmeticFunction.vonMangoldt n : ℂ) *
    χ (n : ZMod d) * (sharpPerronWeight δ ((n:ℝ)/X):ℂ)

theorem smallConductorKernel_vertical_integrable {X : ℕ} (hX : 0<X)
    {δ σ : ℝ} (hδ : 0<δ) (hδ₁ : δ≤1) (hσ : 1/4≤σ) (hσ₂ : σ≤2) :
    Integrable (fun u : ℝ => smallConductorKernel X δ ((σ:ℂ)+(u:ℂ)*Complex.I)) := by
  have hin := verticalIntegrable_sharpPerronKernel hδ hδ₁ hσ hσ₂
  change Integrable (fun u : ℝ => sharpPerronKernel δ ((σ:ℂ)+(u:ℂ)*Complex.I)) at hin
  have hmap : Continuous (fun u : ℝ => (σ:ℂ)+(u:ℂ)*Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hc : Continuous (fun u : ℝ => smallConductorKernel X δ ((σ:ℂ)+(u:ℂ)*Complex.I)) := by
    refine continuous_iff_continuousAt.mpr (fun u => ?_)
    have he : 0<((σ:ℂ)+(u:ℂ)*Complex.I).re := by
      simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.ofReal_im,
        zero_mul,mul_zero,sub_self,add_zero]
      linarith
    exact ContinuousAt.comp (f:=fun v : ℝ => (σ:ℂ)+(v:ℂ)*Complex.I)
      (g:=smallConductorKernel X δ)
      (differentiableAt_smallConductorKernel hX δ he).continuousAt hmap.continuousAt
  apply (hin.norm.const_mul ((X:ℝ)^σ)).mono' hc.aestronglyMeasurable
  filter_upwards with u
  rw [norm_smallConductorKernel hX]
  simp

/-- The ramp's support is finite, so inversion requires absolute convergence
only on the chosen right-hand line. -/
theorem smallConductorWeightedVonMangoldt_eq_integral {X d : ℕ} [NeZero d]
    (χ : DirichletCharacter ℂ d) (hX : 0<X) {δ σ : ℝ}
    (hδ : 0<δ) (hδ₁ : δ≤1) (hσ : 1<σ) (hσ₂ : σ≤2) :
    smallConductorWeightedVonMangoldt χ X δ =
      (2*(Real.pi:ℂ))⁻¹ * ∫ u : ℝ, smallConductorKernel X δ ((σ:ℂ)+(u:ℂ)*Complex.I) *
        negLogDerivL χ ((σ:ℂ)+(u:ℂ)*Complex.I) := by
  have hXr : (0:ℝ)<X := Nat.cast_pos.mpr hX
  have hσ₀ : (1:ℝ)/4≤σ := by linarith
  let w := fun x : ℝ => (sharpPerronWeight δ (x/(X:ℝ)):ℂ)
  have he : ∀ x : ℝ, 0<x → mellinInv σ (smallConductorKernel X δ) x = w x := by
    intro x hx
    change mellinInv σ (fun s => ((X:ℝ):ℂ)^s * sharpPerronKernel δ s) x = _
    rw [mellinInv_mul_positive_cpow hXr hx]
    exact mellinInv_sharpPerronKernel hδ hδ₁ hσ₀ hσ₂ (div_pos hx hXr)
  have hs : ∀ n : ℕ, rampCutoff X δ<n → w (n:ℝ)=0 := by
    intro n hn
    have hnn := (Nat.lt_of_floor_lt hn).le
    have h := sharpPerronWeight_eq_zero hδ ((le_div_iff₀ hXr).mpr hnn)
    simp only [w,h,Complex.ofReal_zero]
  have h := weightedVonMangoldt_eq_verticalIntegral_of_one_lt χ (smallConductorKernel X δ) w _
    hσ (smallConductorKernel_vertical_integrable hX hδ hδ₁ hσ₀ hσ₂) he hs
  simpa only [smallConductorWeightedVonMangoldt,w,one_div,Complex.ofReal_inv,
    Complex.ofReal_mul,Complex.ofReal_ofNat] using h

private theorem ramp_extra_size {X : ℕ} (hX : 2≤X) {δ : ℝ} (hδ : 0<δ) (hδ₁ : δ≤1/4) :
    X≤rampCutoff X δ ∧ ((rampCutoff X δ:ℕ):ℝ)≤2*(X:ℝ) ∧
      ((rampCutoff X δ-X:ℕ):ℝ)≤4*δ*(X:ℝ) := by
  let Y := rampCutoff X δ
  let t := 2*δ
  have ht : 0<t := by dsimp [t]; positivity
  have ht' : t≤1/2 := by dsimp [t]; linarith
  have hd : 0<2-t := by linarith
  have hXr : (0:ℝ)<X := Nat.cast_pos.mpr (by omega)
  have hbound : Real.exp t≤1+2*t := by
    apply (Real.exp_lt_two_add_div_two_sub ht (by linarith)).le.trans
    apply (div_le_iff₀ hd).mpr
    nlinarith only [ht,ht',mul_nonneg ht.le (sub_nonneg.mpr ht')]
  have hY : X≤Y := (Nat.le_floor_iff (by positivity)).mpr
    (le_mul_of_one_le_left hXr.le (Real.one_le_exp_iff.mpr ht.le))
  have hfloor : (Y:ℝ)≤Real.exp t*(X:ℝ) := Nat.floor_le (by positivity)
  have he : Real.exp t*(X:ℝ)≤(1+2*t)*(X:ℝ) :=
    mul_le_mul_of_nonneg_right hbound hXr.le
  refine ⟨hY,hfloor.trans (he.trans ?_),?_⟩
  · exact mul_le_mul_of_nonneg_right (by linarith only [ht']) hXr.le
  · change ((Y-X:ℕ):ℝ)≤_
    rw [Nat.cast_sub hY]
    dsimp only [t] at he
    linarith only [hfloor,he]

/-- Erasing a positive ramp changes the sharp character sum by at most
its width times a logarithmic coefficient bound. -/
theorem norm_smallConductorWeightedVonMangoldt_sub_sharp_le {X d : ℕ} [NeZero d]
    (χ : DirichletCharacter ℂ d) (hX : 2≤X) {δ : ℝ} (hδ : 0<δ) (hδ₁ : δ≤1/4) :
    ‖smallConductorWeightedVonMangoldt χ X δ -
      ∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n:ℂ)*χ (n:ZMod d)‖
      ≤ 8*δ*(X:ℝ)*Real.log (X:ℝ) := by
  let Y := rampCutoff X δ
  let g (n : ℕ) := (ArithmeticFunction.vonMangoldt n:ℂ) * χ (n:ZMod d)
  let f (n : ℕ) := g n * (sharpPerronWeight δ ((n:ℝ)/X):ℂ)
  have ⟨hXY,hY2,hwidth⟩ := ramp_extra_size hX hδ hδ₁
  have hXr : (0:ℝ)<X := Nat.cast_pos.mpr (by omega)
  have hstart : (∑ n ∈ Finset.Icc 1 X,f n) = ∑ n ∈ Finset.Icc 1 X,g n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn₁ := (Finset.mem_Icc.mp hn).1
    have hn₂ := (Finset.mem_Icc.mp hn).2
    have he := sharpPerronWeight_eq_one hδ (div_pos (Nat.cast_pos.mpr hn₁) hXr)
      ((div_le_one hXr).mpr (Nat.cast_le.mpr hn₂))
    simp only [f,he,Complex.ofReal_one,mul_one]
  have hsub : Finset.Icc 1 X ⊆ Finset.Icc 1 Y := Finset.Icc_subset_Icc_right hXY
  have hs : Finset.Icc 1 Y \ Finset.Icc 1 X = Finset.Ioc X Y := by
    ext n
    simp only [Finset.mem_sdiff,Finset.mem_Icc,Finset.mem_Ioc]
    omega
  change ‖(∑ n ∈ Finset.Icc 1 Y,f n) - ∑ n ∈ Finset.Icc 1 X,g n‖≤_
  rw [←hstart,←Finset.sum_sdiff_eq_sub hsub,hs]
  have hlog : Real.log (2*(X:ℝ))≤2*Real.log (X:ℝ) := by
    rw [Real.log_mul (by norm_num) hXr.ne']
    linarith only [Real.log_le_log (by norm_num : (0:ℝ)<2) (Nat.cast_le.mpr hX)]
  have hL : 0≤Real.log (X:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤X by omega))
  have hterm (n : ℕ) (hn : n ∈ Finset.Ioc X Y) : ‖f n‖ ≤ 2*Real.log (X:ℝ) := by
    have hn₀ : (0:ℝ)<n := Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : 0<X)
      (Finset.mem_Ioc.mp hn).1.le)
    have hnY : (n:ℝ)≤2*X := (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans hY2
    have hw := sharpPerronWeight_mem_Icc hδ (div_pos hn₀ hXr)
    dsimp only [f,g]
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw.1]
    apply le_trans (mul_le_of_le_one_right (by positivity) hw.2)
    apply le_trans (mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _))
    exact ArithmeticFunction.vonMangoldt_le_log.trans ((Real.log_le_log hn₀ hnY).trans hlog)
  calc
    _ ≤ ∑ n∈Finset.Ioc X Y, ‖f n‖ := norm_sum_le ..
    _ ≤ ∑ _n∈Finset.Ioc X Y, 2*Real.log (X:ℝ) := Finset.sum_le_sum hterm
    _ = ((Y-X:ℕ):ℝ)*(2*Real.log (X:ℝ)) := by simp [Nat.card_Ioc]
    _ ≤ (4*δ*(X:ℝ))*(2*Real.log (X:ℝ)) := mul_le_mul_of_nonneg_right hwidth (by positivity)
    _ = _ := by ring

theorem norm_smallConductorKernel_at_one_sub_le {X : ℕ} (hX : 0 < X) {δ : ℝ}
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ‖smallConductorKernel X δ 1-(X:ℂ)‖ ≤ 18*δ*(X:ℝ) := by
  have hx : (0:ℝ)<X := Nat.cast_pos.mpr hX
  calc
    _ = (X:ℝ)*‖sharpPerronKernel δ 1-1‖ := by
      rw [smallConductorKernel,Complex.cpow_one,Complex.ofReal_natCast,←mul_sub_one,norm_mul,
        Complex.norm_natCast]
    _ ≤ (X:ℝ)*(18*δ) :=
      mul_le_mul_of_nonneg_left (sharpPerronKernel_one_sub_norm_le hδ hδ₁) hx.le
    _ = _ := by ring

end FareyGoldbach
