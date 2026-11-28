import FareyGoldbach.SmoothedExplicitFormula
import FareyGoldbach.SharpPrimeMathlib

/-! # Integrable and summable majorants for a multiplicative Perron ramp -/

open Filter MeasureTheory Set
open scoped Topology Interval

namespace FareyGoldbach

/-- The majorant is harmonic up to height `T` and quadratic beyond it. -/
noncomputable def sharpPerronMajorant (T x : ℝ) : ℝ :=
  min (1/(1+|x|)) ((1+T)/(1+|x|)^2)

theorem sharpPerronMajorant_nonneg {T : ℝ} (hT : 0≤T) (x : ℝ) :
    0≤sharpPerronMajorant T x := by
  unfold sharpPerronMajorant
  positivity

theorem sharpPerronMajorant_continuous (T : ℝ) :
    Continuous (sharpPerronMajorant T) := by
  have h : Continuous (fun x : ℝ => 1+|x|) := continuous_const.add continuous_abs
  have hne (x : ℝ) : 1+|x| ≠ 0 := by positivity
  exact (continuous_const.div h hne).min
    (continuous_const.div (h.pow 2) (fun x => pow_ne_zero 2 (hne x)))

theorem sharpPerronMajorant_of_le {T x : ℝ} (hx : |x|≤T) :
    sharpPerronMajorant T x = 1/(1+|x|) := by
  apply min_eq_left
  have hp : 0 < 1+|x| := by positivity
  apply (le_div_iff₀ (sq_pos_of_pos hp)).mpr
  calc (1/(1+|x|))*((1+|x|)^2) = 1+|x| := by field_simp
    _ ≤ 1+T := add_le_add_right hx 1

theorem sharpPerronMajorant_of_ge {T x : ℝ} (hx : T≤|x|) :
    sharpPerronMajorant T x = (1+T)/(1+|x|)^2 := by
  apply min_eq_right
  have hp : 0 < 1+|x| := by positivity
  apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
  calc 1+T ≤ 1+|x| := add_le_add_right hx 1
    _ = (1/(1+|x|))*((1+|x|)^2) := by field_simp

private theorem sharpPerronMajorant_antitone {T : ℝ} (hT : 0≤T) :
    AntitoneOn (sharpPerronMajorant T) (Ici 0) := by
  intro x hx y hy hxy
  have hx' : 0≤x := hx
  have hy' : 0≤y := hy
  unfold sharpPerronMajorant
  rw [abs_of_nonneg hx',abs_of_nonneg hy']
  exact min_le_min
    (one_div_le_one_div_of_le (by positivity) (add_le_add_right hxy 1))
    (div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ (by positivity) (add_le_add_right hxy 1) 2))

private theorem sharpPerronMajorant_Ioi {T : ℝ} (hT : 0≤T) :
    IntegrableOn (sharpPerronMajorant T) (Ioi 0) ∧
      (∫ x in Ioi (0:ℝ), sharpPerronMajorant T x) = Real.log (1+T)+1 := by
  let f := sharpPerronMajorant T
  let g := fun x : ℝ => -(1+T)/(1+x)
  let dg := fun x : ℝ => (1+T)/(1+x)^2
  have hder (x : ℝ) (hx : x∈Ici T) : HasDerivAt g (dg x) x := by
    have hx' := hT.trans hx
    have hn : 1+x ≠ 0 := by positivity
    have had : HasDerivAt (fun y : ℝ => 1+y) 1 x := (hasDerivAt_id x).const_add 1
    convert (had.inv hn).const_mul (-(1+T)) using 1
    · ext y
      simp [g, div_eq_mul_inv]
    · dsimp [dg]
      ring
  have hnon (x : ℝ) (hx : x∈Ioi T) : 0≤dg x := by dsimp [dg]; positivity
  have hlim : Tendsto g atTop (𝓝 0) := by
    have h := tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop (1:ℝ) tendsto_id)
    simpa [g,div_eq_mul_inv] using h.const_mul (-(1+T))
  have htail_eq (x : ℝ) (hx : x∈Ioi T) : dg x = f x := by
    have hx' : T<x := hx
    dsimp [f,dg]
    have ha := abs_of_nonneg (hT.trans hx'.le)
    have ht : T≤|x| := by rw [ha]; exact hx'.le
    rw [sharpPerronMajorant_of_ge ht,ha]
  have htail := (integrableOn_Ioi_deriv_of_nonneg' hder hnon hlim).congr_fun
    htail_eq measurableSet_Ioi
  have hsmall : IntegrableOn f (Ioc 0 T) :=
    (sharpPerronMajorant_continuous T).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hint : IntegrableOn f (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi hT]
    exact hsmall.union htail
  have heq : (∫ x in Ioi T, f x) = 1 := by
    rw [← setIntegral_congr_fun measurableSet_Ioi htail_eq,
      integral_Ioi_of_hasDerivAt_of_nonneg' hder hnon hlim]
    dsimp [g]
    field_simp [show 1+T≠0 by positivity]
    norm_num
  have hlow : (∫ x in (0:ℝ)..T, f x) = Real.log (1+T) := by
    calc (∫ x in (0:ℝ)..T, f x) = ∫ x in (0:ℝ)..T, (1+x)⁻¹ := by
           apply intervalIntegral.integral_congr
           intro x hx
           rw [uIcc_of_le hT] at hx
           dsimp [f]
           rw [sharpPerronMajorant_of_le (by rw [abs_of_nonneg hx.1]; exact hx.2),
             abs_of_nonneg hx.1,one_div]
       _ = Real.log (1+T) := by
           have hcont : ContinuousOn (fun x : ℝ => (1+x)⁻¹) (Icc 0 T) :=
             (continuous_const.add continuous_id).continuousOn.inv₀ (fun x hx => by
               have hx' : 0≤x := hx.1
               change (1+x:ℝ) ≠ 0
               linarith only [hx'])
           rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
             (fun x hx => by
               rw [uIcc_of_le hT] at hx
               have hh : HasDerivAt (fun t : ℝ => 1+t) 1 x := (hasDerivAt_id x).const_add 1
               simpa [one_div] using hh.log (show 1+x≠0 from by have := hx.1; positivity))
             (hcont.intervalIntegrable_of_Icc hT)]
           simp
  refine ⟨hint,?_⟩
  have hh := intervalIntegral.integral_Ioi_sub_Ioi hint hT
  change (∫ x in Ioi (0:ℝ), f x) - (∫ x in Ioi T, f x) = _ at hh
  linarith only [hh,heq,hlow]

theorem sharpPerronMajorant_integrable {T : ℝ} (hT : 0≤T) :
    Integrable (sharpPerronMajorant T) := by
  have hpos := (sharpPerronMajorant_Ioi hT).1
  have hneg : IntegrableOn (sharpPerronMajorant T) (Iio 0) := by
    have hh := hpos.comp_neg
    rw [neg_Ioi,neg_zero] at hh
    have heq : (fun x : ℝ => sharpPerronMajorant T (-x)) = sharpPerronMajorant T := by
      funext x
      simp [sharpPerronMajorant]
    change IntegrableOn (fun x : ℝ => sharpPerronMajorant T (-x)) (Iio 0) at hh
    rwa [heq] at hh
  rw [← integrableOn_univ, ← Iic_union_Ioi (a:=(0:ℝ))]
  exact (hneg.congr_set_ae Iio_ae_eq_Iic.symm).union hpos

theorem sharpPerronMajorant_integral {T : ℝ} (hT : 0≤T) :
    (∫ x : ℝ, sharpPerronMajorant T x) = 2*(Real.log (1+T)+1) := by
  let f := fun x : ℝ => min (1/(1+x)) ((1+T)/(1+x)^2)
  change (∫ x : ℝ, f |x|) = _
  rw [integral_comp_abs]
  congr 1
  rw [← (sharpPerronMajorant_Ioi hT).2]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx' : 0<x := hx
  simp [f,sharpPerronMajorant,abs_of_pos hx']

theorem sharpPerronMajorant_int_summable {T : ℝ} (hT : 0≤T) :
    Summable (fun k : ℤ => sharpPerronMajorant T (k:ℝ)) := by
  have hs := (sharpPerronMajorant_antitone hT).summable_of_integrableOn_Ioi_zero
    (sharpPerronMajorant_Ioi hT).1 (fun x _ => sharpPerronMajorant_nonneg hT x)
  apply summable_int_iff_summable_nat_and_neg.mpr
  exact ⟨by simpa using hs, by simpa [sharpPerronMajorant,abs_neg] using hs⟩

theorem sharpPerronMajorant_int_tsum_le {T : ℝ} (hT : 0≤T) :
    (∑' k : ℤ, sharpPerronMajorant T (k:ℝ)) ≤ 1+2*(Real.log (1+T)+1) := by
  let f : ℤ → ℝ := fun k => sharpPerronMajorant T (k:ℝ)
  have heven : f.Even := by intro k; simp [f,sharpPerronMajorant]
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven (sharpPerronMajorant_int_summable hT)]
  have hnat := (sharpPerronMajorant_antitone hT).tsum_add_one_le_integral
    (sharpPerronMajorant_Ioi hT).1 (fun x _ => sharpPerronMajorant_nonneg hT x)
  rw [(sharpPerronMajorant_Ioi hT).2] at hnat
  have hf0 : f 0 = 1 := by
    have h0 : |(0:ℝ)|≤T := by simpa only [abs_zero] using hT
    change sharpPerronMajorant T 0 = 1
    rw [sharpPerronMajorant_of_le h0]
    norm_num
  rw [hf0]
  rw [nsmul_eq_mul]
  have hp : (∑' n : ℕ+, f (n:ℕ)) ≤ Real.log (1+T)+1 := by
    change (∑' n : ℕ+, sharpPerronMajorant T ((n:ℕ):ℝ)) ≤ _
    rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => sharpPerronMajorant T (n:ℝ))]
    exact hnat
  exact add_le_add_right (mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤2)) 1

end FareyGoldbach
