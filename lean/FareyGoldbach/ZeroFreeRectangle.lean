import FareyGoldbach.SmoothedExplicitFormula

/-! # A single Perron contour shift through a zero-free rectangle -/

open Set MeasureTheory
open scoped Classical

namespace FareyGoldbach

/-- Only the pole of the principal character contributes in this rectangle. -/
theorem zeroFreeRectangle_kernel_identity {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d)
    {a b T : ℝ} (ha : 0<a) (ha₁ : a<1) (hb : 1<b) (hT : 0<T)
    (K : ℂ→ℂ) (hK : DifferentiableOn ℂ K {s : ℂ | 0<s.re})
    (hz : ∀ s∈Icc a b ×ℂ Icc (-T) T, entireL χ s≠0) :
    rectIntegral (fun s => K s*negLogDerivL χ s) a b (-T) T =
      2*(Real.pi:ℂ)*Complex.I*(if χ=1 then K 1 else 0) := by
  classical
  let R := Icc a b ×ℂ Icc (-T) T
  let H : ℂ→ℂ := fun s => (if χ=1 then dslope K 1 s else 0)-
    K s*(deriv (entireL χ) s/entireL χ s)
  let residue : ℂ := if χ=1 then K 1 else 0
  have hsub : R ⊆ {s : ℂ | 0<s.re} := fun _ hs => ha.trans_le (Complex.mem_reProdIm.mp hs).1.1
  have hds : DifferentiableOn ℂ (dslope K 1) {s : ℂ | 0<s.re} :=
    (Complex.differentiableOn_dslope ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : 0<(1:ℂ).re))).mpr hK
  have hH : DifferentiableOn ℂ H R := by
    have h₁ : DifferentiableOn ℂ (fun s => if χ=1 then dslope K 1 s else 0) R := by
      split_ifs
      · exact hds.mono hsub
      · exact differentiableOn_const _
    exact h₁.fun_sub ((hK.mono hsub).fun_mul
      ((differentiable_entireL χ).deriv.differentiableOn.fun_div
        (differentiable_entireL χ).differentiableOn (fun s hs => hz s hs)))
  have hdec (s : ℂ) (hs : s∈R) (hne : s≠1) :
      K s*negLogDerivL χ s = H s+∑ p∈({1}:Finset ℂ), residue*(s-p)⁻¹ := by
    have hL : χ.LFunction s≠0 := by
      intro h
      apply hz s hs
      rw [entireL_apply_of_ne_one χ hne,h]
      split_ifs <;> simp
    rw [negLogDerivL_eq_of_ne_one χ hne hL]
    simp only [Finset.sum_singleton,H,residue]
    split_ifs
    · rw [dslope_of_ne K hne,slope_def_field]
      field_simp [sub_ne_zero.mpr hne]
      ring
    · ring
  have hab := ha₁.trans hb
  have ht : -T<T := by linarith
  have hrect (x t : ℝ) (hx : x∈Icc a b) (ht' : t∈Icc (-T) T) :
      (x:ℂ)+(t:ℂ)*Complex.I∈R := Complex.mem_reProdIm.mpr ⟨by simpa using hx,by simpa using ht'⟩
  have hne_im (x t : ℝ) (ht' : t≠0) : (x:ℂ)+(t:ℂ)*Complex.I≠1 := by
    intro h
    exact ht' (by simpa using congrArg Complex.im h)
  have hne_re (x t : ℝ) (hx : x≠1) : (x:ℂ)+(t:ℂ)*Complex.I≠1 := by
    intro h
    exact hx (by simpa using congrArg Complex.re h)
  have hi := rectIntegral_eq_sum_simple_poles (G:=fun s => K s*negLogDerivL χ s)
    hab ht ({1}:Finset ℂ) (fun _ => residue)
    (by simpa using (show a<1 ∧ 1<b ∧ -T<0 ∧ 0<T by exact ⟨ha₁,hb,by linarith,hT⟩))
    hH
    (fun x hx => hdec _ (hrect x (-T) hx (left_mem_Icc.mpr ht.le)) (hne_im x _ (neg_ne_zero.mpr hT.ne')))
    (fun x hx => hdec _ (hrect x T hx (right_mem_Icc.mpr ht.le)) (hne_im x _ hT.ne'))
    (fun t ht' => hdec _ (hrect b t (right_mem_Icc.mpr hab.le) ht') (hne_re b t hb.ne'))
    (fun t ht' => hdec _ (hrect a t (left_mem_Icc.mpr hab.le) ht') (hne_re a t ha₁.ne))
  simpa only [Finset.sum_singleton,residue] using hi

end FareyGoldbach
