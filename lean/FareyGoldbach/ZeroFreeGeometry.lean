import FareyGoldbach.ZeroFreeLocal

/-! # Real kernel estimates and the neighborhood of the zeta pole -/

open Complex Metric Set
open scoped ComplexConjugate Classical Topology

namespace FareyGoldbach

theorem zeroFree_kernel_upper {h : ℝ} (hh : 0<h) (t : ℝ) :
    h*zeroFreeKernel h t ≤ 1 := by
  unfold zeroFreeKernel
  rw [←mul_div_assoc,div_le_one (by positivity)]
  nlinarith only [sq_nonneg t]

theorem zeroFree_kernel_far {h t : ℝ} (hh : 0<h) (ht : 4*h≤|t|) :
    h*zeroFreeKernel h t ≤ 1/16 := by
  unfold zeroFreeKernel
  rw [←mul_div_assoc,div_le_div_iff₀ (by positivity) (by norm_num)]
  have hs := mul_self_le_mul_self (by positivity : 0≤4*h) ht
  rw [abs_mul_abs_self] at hs
  nlinarith only [hs,sq_nonneg h]

theorem zeroFree_kernel_near {h x t : ℝ} (hh : 0<h) (hx : h≤x) (hx' : x≤33*h/32)
    (ht : |t|≤h/4) : 7/8 ≤ h*zeroFreeKernel x t := by
  have hx₀ := hh.trans_le hx
  unfold zeroFreeKernel
  rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
  have ht₂ := mul_self_le_mul_self (abs_nonneg t) ht
  rw [abs_mul_abs_self] at ht₂
  have hx₂ := mul_self_le_mul_self hx₀.le hx'
  have h₁ := mul_le_mul_of_nonneg_left hx hh.le
  nlinarith only [ht₂,hx₂,h₁,sq_nonneg h]

theorem zeroFree_mem_disk {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    {z : ℂ} {t : ℝ} (hzero : entireL χ z=0)
    (hlo : 3/4≤z.re) (hhi : z.re≤1) (him : |z.im-t|≤1/2) :
    z∈diskZeros χ (2+(t:ℂ)*I) (15/8) := by
  apply (mem_diskZeros_iff χ).mpr
  refine ⟨?_,hzero⟩
  rw [Metric.mem_closedBall,dist_eq_norm]
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  change |(z-zeroFreePoint 2 t).re| + |(z-zeroFreePoint 2 t).im| ≤ _
  simp only [Complex.sub_re,Complex.sub_im,zeroFreePoint_re,zeroFreePoint_im]
  rw [abs_of_nonpos (by linarith : z.re-2≤0)]
  linarith only [hlo,him]

/-- Removing the pole from the level-one principal L-function leaves a
nonvanishing neighborhood of 1. -/
theorem zeroFree_zeta_ball :
    ∃ r : ℝ, 0<r ∧ ∀ z : ℂ, ‖z-1‖<r → entireL (1:DirichletCharacter ℂ 1) z≠0 := by
  let f := entireL (1:DirichletCharacter ℂ 1)
  have hf : Continuous f := (differentiable_entireL _).continuous
  have h₁ : f 1≠0 := by
    dsimp [f]
    rw [entireL_apply_one_of_eq_one DirichletCharacter.isPrimitive_one_level_one rfl]
    exact one_ne_zero
  have hn : {z : ℂ | f z≠0} ∈ 𝓝 (1:ℂ) := (isOpen_ne_fun hf continuous_const).mem_nhds h₁
  obtain ⟨r,hr,hh⟩ := Metric.mem_nhds_iff.mp hn
  exact ⟨r,hr,fun z hz => hh (by simpa only [Metric.mem_ball,dist_eq_norm] using hz)⟩

end FareyGoldbach
