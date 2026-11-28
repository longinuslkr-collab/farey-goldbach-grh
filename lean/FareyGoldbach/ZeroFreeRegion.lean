import FareyGoldbach.ZeroFreeInduction
import FareyGoldbach.ZeroFreeGeometry
import FareyGoldbach.ZeroFreePositivity
import FareyGoldbach.ZeroFreeSymmetry

/-! # A classical logarithmic zero-free region for primitive Dirichlet L-functions -/

open Complex
open scoped ComplexConjugate Classical

namespace FareyGoldbach

private def ZFUpper (C : ℝ) : Prop :=
  ∀ (d : ℕ) [NeZero d] (ψ : DirichletCharacter ℂ d) (σ t : ℝ), 1<σ → σ≤2 →
    (negLogDerivL ψ (zeroFreePoint σ t)).re ≤
      (if ψ=1 then ((1:ℂ)/(zeroFreePoint σ t-1)).re else 0) + C*Real.log (2*(d:ℝ)*(2+|t|))

private theorem zf_selection {C : ℝ} (hC : 0<C) (hu : ZFUpper C)
    {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive)
    (h t : ℝ) (hh : 0<h) (hh' : h≤1) (S : Finset ℂ)
    (hS : S ⊆ diskZeros χ (2+(t:ℂ)*I) (15/8)) :
    4*(h*∑ z∈S,zeroFreeKernel (1+h-z.re) (t-z.im)) ≤
      3 + 4*(h*(if χ=1 then zeroFreeKernel h t else 0)) +
      h*(if χ^2=1 then zeroFreeKernel h (2*t) else 0) +
      h*((5*C+3248000)*Real.log (2*(d:ℝ)*(2+|t|))) := by
  let L := Real.log (2*(d:ℝ)*(2+|t|))
  have hσ : 1 < 1+h := by linarith
  have hσ' : 1+h≤2 := by linarith
  have hd : (1:ℝ)≤d := Nat.one_le_cast.mpr (NeZero.pos d)
  have hl : Real.log (2*(1:ℝ)*(2+|0|))≤L := by
    apply Real.log_le_log (by norm_num)
    rw [abs_zero,add_zero]
    nlinarith only [hd, mul_nonneg (Nat.cast_nonneg (α:=ℝ) d) (abs_nonneg t)]
  have hl₂ : Real.log (2*(d:ℝ)*(2+|2*t|))≤2*L := by
    have hy : 2≤2*(d:ℝ)*(2+|t|) := by
      nlinarith only [hd,mul_nonneg (Nat.cast_nonneg (α:=ℝ) d) (abs_nonneg t)]
    calc _ ≤ Real.log ((2*(d:ℝ)*(2+|t|))^2) := by
              apply Real.log_le_log (by positivity)
              rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
              nlinarith only [mul_nonneg (sub_nonneg.mpr hy) (show 0≤2*(d:ℝ)*(2+|t|) by positivity),
                Nat.cast_nonneg (α:=ℝ) d]
         _ = 2*L := by simp [Real.log_pow,L]
  have h₀ := hu 1 (1:DirichletCharacter ℂ 1) (1+h) 0 hσ hσ'
  have h₁ := zeroFree_local_with_zeros hprim (1+h) t hσ hσ' S hS
  have h₂ := hu d (χ^2) (1+h) (2*t) hσ hσ'
  have hpos := zeroFree_logDeriv_341 χ (1+h) t hσ
  simp only [ite_true,zeroFree_pole_re,add_sub_cancel_left,Nat.cast_one] at h₀
  simp only [zeroFree_pole_re,add_sub_cancel_left] at h₁ h₂
  have hz : zeroFreeKernel h 0=1/h := by unfold zeroFreeKernel; field_simp [hh.ne']; ring
  rw [hz] at h₀
  have hder : 4*(∑ z∈S,zeroFreeKernel (1+h-z.re) (t-z.im)) ≤
      3/h + 4*(if χ=1 then zeroFreeKernel h t else 0) +
      (if χ^2=1 then zeroFreeKernel h (2*t) else 0) + (5*C+3248000)*L := by
    let p₁ := if χ=1 then zeroFreeKernel h t else 0
    let p₂ := if χ^2=1 then zeroFreeKernel h (2*t) else 0
    change (negLogDerivL χ (zeroFreePoint (1+h) t)).re ≤ p₁+812000*L-_ at h₁
    change (negLogDerivL (χ^2) (zeroFreePoint (1+h) (2*t))).re ≤ p₂+_ at h₂
    have b₀ := h₀.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hl hC.le))
    have b₂ := h₂.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hl₂ hC.le))
    calc
      _ ≤ 3*(1/h+C*L)+4*(p₁+812000*L)+(p₂+C*(2*L)) := by
        linarith only [hpos,b₀,h₁,b₂]
      _ = _ := by dsimp only [p₁,p₂]; ring
  have hm := mul_le_mul_of_nonneg_left hder hh.le
  have hcancel : h*(3/h)=3 := by field_simp
  dsimp only [L] at hm
  nlinarith only [hm,hcancel]

private theorem zf_from_upper {C : ℝ} (hC : 0<C) (hu : ZFUpper C) :
    ∃ c₀ : ℝ, 0<c₀ ∧ ∀ (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d), χ.IsPrimitive →
      ∀ s : ℂ, (χ=1 ∨ χ^2≠1 ∨ s.im≠0) →
        1-c₀/Real.log (2*(d:ℝ)*(2+|s.im|))≤s.re → entireL χ s≠0 := by
  obtain ⟨r,hr,hball⟩ := zeroFree_zeta_ball
  let A := 5*C+3248000
  let M := max (1024*A) (max 128 (16/r))
  have hA : 0<A := by dsimp [A]; positivity
  have hMa : 1024*A≤M := le_max_left ..
  have hM128 : 128≤M := (le_max_left ..).trans (le_max_right ..)
  have hMr : 16/r≤M := (le_max_right ..).trans (le_max_right ..)
  have hM : 0<M := by linarith only [hM128]
  refine ⟨1/(32*M),by positivity,?_⟩
  intro d _ χ hprim s hex hregion hzero
  let t := s.im
  let L := Real.log (2*(d:ℝ)*(2+|t|))
  let δ := 1/(M*L)
  have hL : 1≤L := one_le_log_two_mul_d_mul d t
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hc : δ*M*L=1 := by dsimp [δ]; field_simp
  have hδM : δ*M≤1 := by nlinarith only [hc,mul_nonneg (mul_nonneg hδ.le hM.le) (sub_nonneg.mpr hL)]
  have htiny : δ ≤ 1/128 := by
    linarith only [hδM,mul_le_mul_of_nonneg_left hM128 hδ.le]
  have herr : δ*(A*L) ≤ 1/1024 := by
    nlinarith only [hc, mul_le_mul_of_nonneg_right hMa (mul_nonneg hδ.le hLp.le)]
  have hscale : (1/(32*M))/L=δ/32 := by dsimp only [δ]; ring
  change 1-(1/(32*M))/L ≤ s.re at hregion
  rw [hscale] at hregion
  have hβ : s.re<1 := lt_of_not_ge (fun h => zeroFree_primitive_nonzero_right hprim h hzero)
  have hβlo : 3/4 ≤ s.re := by linarith only [hregion,htiny]
  have hsZ : s∈diskZeros χ (2+(t:ℂ)*I) (15/8) :=
    zeroFree_mem_disk hzero hβlo hβ.le (by simp [t])
  by_cases hgeneric : χ^2≠1 ∨ 4*δ≤|t|
  · have hm := zf_selection hC hu hprim δ t hδ (by linarith only [htiny]) {s}
        (Finset.singleton_subset_iff.mpr hsZ)
    simp only [Finset.sum_singleton] at hm
    have hmass := zeroFree_kernel_near (h:=δ) (x:=1+δ-s.re) (t:=t-s.im) hδ
      (by linarith only [hβ]) (by linarith only [hregion]) (by simp [t]; positivity)
    have hpole : δ*(if χ=1 then zeroFreeKernel δ t else 0) ≤ 1/16 := by
      split
      · rename_i he
        have ht := hgeneric.resolve_left (by simp [he])
        exact zeroFree_kernel_far hδ ht
      · simp
    have hsq : δ*(if χ^2=1 then zeroFreeKernel δ (2*t) else 0) ≤ 1/16 := by
      split
      · rename_i he
        have ht := hgeneric.resolve_left (not_not.mpr he)
        apply zeroFree_kernel_far hδ
        rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
        linarith only [ht,abs_nonneg t]
      · simp
    change _ ≤ 3+4*_+_+δ*(A*L) at hm
    linarith only [hm,hmass,hpole,hsq,herr]
  · push Not at hgeneric
    obtain ⟨hquad,ht⟩ := hgeneric
    by_cases hprincipal : χ=1
    · have hd := eq_one_of_isPrimitive_of_eq_one hprim hprincipal
      subst d
      subst χ
      have hrad : 16*δ ≤ r := by
        have hh := (div_le_iff₀ hr).mp hMr
        have ha := mul_le_mul_of_nonneg_left hh hδ.le
        have hb := mul_le_mul_of_nonneg_right hδM hr.le
        nlinarith only [ha,hb]
      apply hball s _ hzero
      apply (Complex.norm_le_abs_re_add_abs_im _).trans_lt
      simp only [Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im,sub_zero,
        abs_of_nonpos (sub_nonpos.mpr hβ.le)]
      change -(s.re-1)+|t|<r
      linarith only [hrad,hregion,ht,hδ]
    · have ht₀ : t≠0 := (hex.resolve_left hprincipal).resolve_left (not_not.mpr hquad)
      let v := conj s
      have hv : entireL χ v = 0 := by
        rw [show v=conj s by rfl,quadratic_entireL_conj hquad,hzero,map_zero]
      have hvt : v.im = -t := Complex.conj_im _
      have hvr : v.re = s.re := Complex.conj_re _
      have hne : s≠v := fun e => ht₀ (by
        have H := congrArg Complex.im e
        rw [hvt] at H
        change t= -t at H
        linarith)
      have ht₂ : |t-v.im|=2*|t| := by rw [hvt,sub_neg_eq_add,←two_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      have hvZ : v∈diskZeros χ (2+(t:ℂ)*I) (15/8) := by
        apply zeroFree_mem_disk hv (hvr.ge.trans' hβlo) (hvr.le.trans hβ.le)
        rw [abs_sub_comm,ht₂]
        linarith only [ht,htiny]
      let h := 32*δ
      have hh : 0<h := by dsimp [h]; positivity
      have hnear (z : ℂ) (hz : z.re=s.re) (hz' : |t-z.im|≤h/4) :
          7/8 ≤ h*zeroFreeKernel (1+h-z.re) (t-z.im) := by
        apply zeroFree_kernel_near hh _ _ hz'
        · linarith only [hz,hβ]
        · dsimp [h]; linarith only [hz,hregion,hδ]
      have hm₁ := hnear s rfl (by simp [t]; positivity)
      have hm₂ := hnear v hvr (by rw [ht₂]; dsimp only [h]; linarith only [ht])
      have H := zf_selection hC hu hprim h t hh (by dsimp only [h]; linarith only [htiny]) {s,v}
        (by simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro hsZ hvZ)
      simp only [Finset.sum_pair hne,hprincipal,ite_false,hquad,ite_true,mul_zero,add_zero] at H
      have hcap := zeroFree_kernel_upper hh (2*t)
      change _ ≤ 3+_+h*(A*L) at H
      have hherr : h*(A*L)≤1/32 := by dsimp only [h]; linarith only [herr]
      linarith only [H,hm₁,hm₂,hcap,hherr]

/-- The classical logarithmic zero-free region, allowing only a real zero of
a nonprincipal quadratic character as an exception. -/
theorem classical_zero_free_region :
    ∃ c₀ : ℝ, 0<c₀ ∧ ∀ (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d), χ.IsPrimitive →
      ∀ s : ℂ, (χ=1 ∨ χ^2≠1 ∨ s.im≠0) →
        1-c₀/Real.log (2*(d:ℝ)*(2+|s.im|)) ≤ s.re → entireL χ s ≠ 0 := by
  obtain ⟨C,hC,h⟩ := zeroFree_induced_logDeriv_upper
  exact zf_from_upper hC h

end FareyGoldbach
