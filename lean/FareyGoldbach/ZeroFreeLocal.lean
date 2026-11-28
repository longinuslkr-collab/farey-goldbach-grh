import FareyGoldbach.LocalLogDerivative

/-! # One-sided logarithmic-derivative bounds with selected nearby zeros -/

open Complex Metric Set
open scoped Classical

namespace FareyGoldbach

noncomputable def zeroFreePoint (σ t : ℝ) : ℂ := (σ:ℂ)+(t:ℂ)*Complex.I
noncomputable def zeroFreeKernel (x y : ℝ) : ℝ := x/(x^2+y^2)

@[simp] theorem zeroFreePoint_re (σ t : ℝ) : (zeroFreePoint σ t).re = σ := by simp [zeroFreePoint]
@[simp] theorem zeroFreePoint_im (σ t : ℝ) : (zeroFreePoint σ t).im = t := by simp [zeroFreePoint]

theorem zeroFree_pole_re (σ t : ℝ) :
    ((1:ℂ)/(zeroFreePoint σ t-1)).re = zeroFreeKernel (σ-1) t := by
  simp [one_div,Complex.inv_re,Complex.normSq_apply,zeroFreeKernel,pow_two,Complex.sub_re,Complex.sub_im]

theorem zeroFree_primitive_nonzero_right {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    (hprim : χ.IsPrimitive) {s : ℂ} (hs : 1≤s.re) : entireL χ s ≠ 0 := by
  by_cases h : s=1
  · subst s
    by_cases hχ : χ=1
    · rw [entireL_apply_one_of_eq_one hprim hχ]; norm_num
    · simpa [entireL, hχ] using χ.LFunction_ne_zero_of_one_le_re (.inl hχ) hs
  · rw [entireL_apply_of_ne_one χ h]
    split
    · exact mul_ne_zero (sub_ne_zero.mpr h) (χ.LFunction_ne_zero_of_one_le_re (.inr h) hs)
    · exact χ.LFunction_ne_zero_of_one_le_re (.inr h) hs

private theorem zeroTerm_re (σ t : ℝ) (ρ : ℂ) (m : ℕ) :
    ((m:ℂ)/(zeroFreePoint σ t-ρ)).re = (m:ℝ)*zeroFreeKernel (σ-ρ.re) (t-ρ.im) := by
  rw [Complex.div_re,Complex.natCast_re,Complex.natCast_im,zero_mul,zero_div,add_zero]
  simp only [zeroFreeKernel,Complex.sub_re,Complex.sub_im,zeroFreePoint_re,zeroFreePoint_im,
    Complex.normSq_apply,pow_two]
  ring

theorem zeroFree_local_with_zeros {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    (hprim : χ.IsPrimitive) (σ t : ℝ) (hσ : 1<σ) (hσ' : σ≤2) (S : Finset ℂ)
    (hS : S ⊆ diskZeros χ (2+(t:ℂ)*I) (15/8)) :
    (negLogDerivL χ (zeroFreePoint σ t)).re ≤
      (if χ=1 then ((1:ℂ)/(zeroFreePoint σ t-1)).re else 0) +
      812000*Real.log (2*(d:ℝ)*(2+|t|)) - ∑ z∈S, zeroFreeKernel (σ-z.re) (t-z.im) := by
  let Z := diskZeros χ (2+(t:ℂ)*I) (15/8)
  let K (z : ℂ) := zeroFreeKernel (σ-z.re) (t-z.im)
  have hσc : zeroFreePoint σ t ≠ 1 := by
    intro hs
    have := congrArg Complex.re hs
    simp only [zeroFreePoint_re, Complex.one_re] at this
    linarith
  have hL := χ.LFunction_ne_zero_of_one_le_re (.inr hσc) (show 1≤(zeroFreePoint σ t).re by simpa using hσ.le)
  have hmem : zeroFreePoint σ t ∈ closedBall (2+(t:ℂ)*I) (7/4) := by
    rw [mem_closedBall, dist_eq_norm]
    have he : zeroFreePoint σ t - (2+(t:ℂ)*I) = ((σ-2:ℝ):ℂ) := by dsimp [zeroFreePoint]; push_cast; ring
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hσ')]
    linarith
  have hbound := local_negLogDeriv_approx hprim t hmem hσc hL
  have hre := (Complex.re_le_norm _).trans hbound
  have hweights (z : ℂ) (hz : z∈Z) : 0≤K z ∧ 1≤(zeroMult χ z:ℝ) := by
    have hzero := ((mem_diskZeros_iff χ).mp hz).2
    have hx : z.re < 1 := lt_of_not_ge (fun h => zeroFree_primitive_nonzero_right hprim h hzero)
    exact ⟨div_nonneg (sub_nonneg.mpr (hx.le.trans hσ.le)) (by positivity),
      Nat.one_le_cast.mpr ((zeroMult_pos_iff χ z).mpr hzero)⟩
  have hsub : (∑ z∈S, K z) ≤ ∑ z∈Z, (zeroMult χ z:ℝ)*K z := by
    calc _ ≤ ∑ z∈Z, K z := Finset.sum_le_sum_of_subset_of_nonneg hS (fun z hz _ => (hweights z hz).1)
         _ ≤ _ := Finset.sum_le_sum (fun z hz => by
           simpa only [one_mul] using mul_le_mul_of_nonneg_right (hweights z hz).2 (hweights z hz).1)
  simp only [Complex.sub_re, Complex.re_sum, zeroTerm_re] at hre
  change (∑ z∈S, K z) ≤ ∑ z∈Z, (zeroMult χ z:ℝ)*K z at hsub
  dsimp only [K,Z] at hsub
  by_cases h : χ=1
  · simp only [h,ite_true] at hre ⊢
    simp only [h] at hsub
    linarith only [hre,hsub]
  · simp only [h,ite_false,Complex.zero_re] at hre ⊢
    linarith only [hre,hsub]

theorem zeroFree_primitive_logDeriv_upper {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    (hprim : χ.IsPrimitive) (σ t : ℝ) (hσ : 1<σ) (hσ' : σ≤2) :
    (negLogDerivL χ ((σ:ℂ)+(t:ℂ)*I)).re ≤
      (if χ=1 then ((1:ℂ)/((σ:ℂ)+(t:ℂ)*I-1)).re else 0) +
      812000*Real.log (2*(d:ℝ)*(2+|t|)) := by
  simpa only [Finset.sum_empty,sub_zero,zeroFreePoint] using
    zeroFree_local_with_zeros hprim σ t hσ hσ' ∅ (Finset.empty_subset _)

end FareyGoldbach
