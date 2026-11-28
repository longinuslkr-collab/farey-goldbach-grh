import FareyGoldbach.LocalLogDerivative

/-! # Bounds on an L-function and its derivative in a shrinking disk at one -/

open Set Filter MeasureTheory
open scoped Topology

namespace FareyGoldbach

private theorem siegel_log_one {q : ℕ} (hq : 1<q) : 1≤Real.log (2*(q:ℝ)) := by
  have h : (2:ℝ)≤q := Nat.cast_le.mpr hq
  exact (Real.le_log_iff_exp_le (by positivity)).mpr
    (Real.exp_one_lt_three.le.trans (by linarith only [h]))

/-- A uniform right-half-plane bound that also applies to induced characters. -/
theorem norm_LFunction_le_of_ne_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ≠1) {s : ℂ} (hs : (1:ℝ)/16≤s.re) :
    ‖χ.LFunction s‖≤16*(q:ℝ)*‖s‖ := by
  let A (t : ℝ) := ∑ k∈Finset.Icc 1 ⌊t⌋₊,χ (k:ZMod q)
  have hm : Measurable (fun n : ℕ => ∑ k∈Finset.Icc 1 n, χ (k:ZMod q)) := measurable_of_countable _
  have hA : AEStronglyMeasurable A (volume.restrict (Ioi 1)) :=
    (hm.comp Nat.measurable_floor).aestronglyMeasurable
  have h := norm_dirichletIntegral_le (Nat.cast_nonneg q) hA
    (fun t _ => norm_charPartialSum_le hχ ⌊t⌋₊) hs
  have hv := entireL_eq_integral_of_ne_one hχ (by linarith only [hs] : 0<s.re)
  rw [entireL,ite_eq_right hχ] at hv
  rw [hv,norm_mul,mul_comm (16*(q:ℝ))]
  exact mul_le_mul_of_nonneg_left h (norm_nonneg _)

/-- Interpolation between the trivial prefix bound and a complete period. -/
private theorem siegel_partial_interpolate {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ≠1) {t a : ℝ} (ht : 1≤t) (ha : 0≤a) (ha' : a≤1) :
    ‖∑ k∈Finset.Icc 1 ⌊t⌋₊,χ (k:ZMod q)‖ ≤ (q:ℝ)^a*t^(1-a) := by
  have hq : (0:ℝ)<q := Nat.cast_pos.mpr (NeZero.pos q)
  have ht' := zero_lt_one.trans_le ht
  have hid (x : ℝ) (hx : 0<x) : x^a*x^(1-a)=x := by
    rw [←Real.rpow_add hx,show a+(1-a)=1 by ring,Real.rpow_one]
  by_cases hc : t≤q
  · calc _ ≤ ∑ k∈Finset.Icc 1 ⌊t⌋₊,‖χ (k:ZMod q)‖ := norm_sum_le _ _
      _ ≤ ∑ _k∈Finset.Icc 1 ⌊t⌋₊,(1:ℝ) := Finset.sum_le_sum fun _ _ => χ.norm_le_one _
      _ ≤ t := by simpa using Nat.floor_le ht'.le
      _ = t^a*t^(1-a) := (hid t ht').symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ht'.le hc ha) (by positivity)
  · apply (norm_charPartialSum_le hχ _).trans
    calc (q:ℝ) = (q:ℝ)^a*(q:ℝ)^(1-a) := (hid _ hq).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hq.le (le_of_not_ge hc) (sub_nonneg.mpr ha')) (by positivity)

theorem siegel_L_on_closedBall_le_of_ne_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ≠1) (hq : 1<q) {s : ℂ}
    (hs : s∈Metric.closedBall 1 (1/(4*Real.log (2*(q:ℝ))))) :
    ‖χ.LFunction s‖≤16*Real.log (2*(q:ℝ)) := by
  let L := Real.log (2*(q:ℝ))
  let b := 1/(4*L)
  let a := 2*b
  have hL : 1≤L := siegel_log_one hq
  have hLpos := zero_lt_one.trans_le hL
  have hb : 0<b := by dsimp only [b]; positivity
  have hb4 : b≤1/4 := by dsimp only [b]; gcongr; linarith only [hL]
  have ha : 0≤a := by dsimp [a]; positivity
  have ha' : a≤1 := by dsimp only [a]; linarith only [hb4]
  have hQ : (1:ℝ)≤q := Nat.one_le_cast.mpr hq.le
  have hQp := zero_lt_one.trans_le hQ
  have hqlog : Real.log q≤L := Real.log_le_log hQp (by linarith only [hQ])
  have hqa : (q:ℝ)^a≤2 := by
    rw [Real.rpow_def_of_pos hQp]
    apply (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hqlog ha)).trans
    have he : L*a=(1:ℝ)/2 := by dsimp only [a,b]; field_simp; ring
    rw [he]
    exact (Real.le_log_iff_exp_le (by norm_num : (0:ℝ)<2)).mp (by linarith only [Real.log_two_gt_d9])
  have hdist : ‖s-1‖≤b := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hs
  have hlow : 1-b≤s.re := by
    have hr := (abs_le.mp ((Complex.abs_re_le_norm (s-1)).trans hdist)).1
    simp only [Complex.sub_re,Complex.one_re] at hr
    linarith only [hr]
  have hsp : 0<s.re := by linarith only [hlow,hb4]
  have hsn : ‖s‖≤2 := by
    have h := norm_add_le (s-1) (1:ℂ)
    simp only [sub_add_cancel,norm_one] at h
    linarith only [h,hdist,hb4]
  let A (t : ℝ) := ∑ k∈Finset.Icc 1 ⌊t⌋₊,χ (k:ZMod q)
  let f (t : ℝ) := A t*(t:ℂ)^(-(s+1))
  let g (t : ℝ) := 2*t^(-1-b)
  have hme : AEStronglyMeasurable f (volume.restrict (Ioi 1)) := by
    have hm : Measurable (fun n : ℕ => ∑ k∈Finset.Icc 1 n,χ (k:ZMod q)) := measurable_of_countable _
    refine (hm.comp Nat.measurable_floor).aestronglyMeasurable.mul ?_
    exact ContinuousOn.aestronglyMeasurable
      (fun t ht => (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (zero_lt_one.trans ht).ne')).continuousWithinAt)
      measurableSet_Ioi
  have hdom : IntegrableOn g (Ioi (1:ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith only [hb] : -1-b < -1) zero_lt_one).const_mul 2
  have hpt (t : ℝ) (ht : t∈Ioi (1:ℝ)) : ‖f t‖≤g t := by
    have ht' : 1≤t := ht.le
    have htpos := zero_lt_one.trans_le ht'
    dsimp only [f,g]
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos htpos]
    simp only [Complex.neg_re,Complex.add_re,Complex.one_re]
    calc _ ≤ ((q:ℝ)^a*t^(1-a))*t^(-(s.re+1)) := mul_le_mul_of_nonneg_right
          (siegel_partial_interpolate hχ ht' ha ha') (by positivity)
      _ = (q:ℝ)^a*t^((1-a)+(-(s.re+1))) := by rw [Real.rpow_add htpos,mul_assoc]
      _ ≤ _ := mul_le_mul hqa (Real.rpow_le_rpow_of_exponent_le ht'
        (by dsimp only [a]; linarith only [hlow])) (by positivity) (by norm_num)
  have hint : IntegrableOn f (Ioi (1:ℝ)) :=
    hdom.mono' hme (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hpt t ht)
  have hG : (∫ t in Ioi (1:ℝ),g t)=8*L := by
    rw [show (∫ t in Ioi (1:ℝ),g t) = 2*∫ t in Ioi (1:ℝ),t^(-1-b) from integral_const_mul ..,
      integral_Ioi_rpow_of_lt (by linarith only [hb] : -1-b < -1) zero_lt_one,Real.one_rpow]
    dsimp only [b]
    field_simp
    ring
  have hnorm : ‖∫ t in Ioi (1:ℝ), f t‖ ≤ 8*L := (norm_integral_le_integral_norm _).trans
    ((setIntegral_mono_on hint.norm hdom measurableSet_Ioi hpt).trans_eq hG)
  have hval := entireL_eq_integral_of_ne_one hχ hsp
  change entireL χ s = s*(∫ t in Ioi (1:ℝ), f t) at hval
  rw [entireL,ite_eq_right hχ] at hval
  rw [hval,norm_mul]
  exact (mul_le_mul hsn hnorm (norm_nonneg _) (by norm_num)).trans_eq (by ring)

theorem siegel_L_on_closedBall_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (hq : 1<q) {s : ℂ}
    (hs : s∈Metric.closedBall 1 (1/(4*Real.log (2*(q:ℝ))))) :
    ‖χ.LFunction s‖≤16*Real.log (2*(q:ℝ)) :=
  siegel_L_on_closedBall_le_of_ne_one χ (fun hc =>
    (Nat.ne_of_gt hq) (eq_one_of_isPrimitive_of_eq_one hprim hc)) hq hs

theorem siegel_deriv_L_real_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (hq : 1<q) {β : ℝ}
    (hβ : 1-1/(8*Real.log (2*(q:ℝ)))≤β) (hβ' : β≤1) :
    ‖deriv χ.LFunction (β:ℂ)‖≤128*Real.log (2*(q:ℝ))^2 := by
  let L := Real.log (2*(q:ℝ))
  let r := 1/(8*L)
  have hL : 0<L := zero_lt_one.trans_le (siegel_log_one hq)
  have hr : 0<r := by dsimp only [r]; positivity
  have hχ : χ≠1 := fun hc => (Nat.ne_of_gt hq) (eq_one_of_isPrimitive_of_eq_one hprim hc)
  have hβd : dist (β:ℂ) 1≤r := by
    rw [dist_eq_norm,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hβ')]
    linarith only [hβ]
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c:=(β:ℂ)) (C:=16*L) hr
    (χ.differentiable_LFunction hχ).diffContOnCl (fun z hz => siegel_L_on_closedBall_le χ hprim hq (by
      apply (dist_triangle z (β:ℂ) 1).trans
      apply (add_le_add (Metric.mem_sphere.mp hz).le hβd).trans_eq
      dsimp only [r,L]
      ring))
  exact h.trans_eq (by dsimp only [r,L]; field_simp; ring)

end FareyGoldbach
