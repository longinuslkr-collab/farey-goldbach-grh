import FareyGoldbach.EstermannDirichletSeries
import FareyGoldbach.ZeroFreeSymmetry

/-! # Signs of the real L-values used in the Siegel argument -/

open Complex Filter Metric Set
open scoped Topology ComplexOrder

namespace FareyGoldbach

theorem quadratic_LFunction_im_eq_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ^ 2 = 1) (hn : χ ≠ 1) (x : ℝ) :
    (χ.LFunction (x:ℂ)).im = 0 := by
  have h := quadratic_LFunction_conj hχ hn (x:ℂ)
  have hi := congrArg Complex.im h
  simp only [Complex.conj_ofReal,Complex.conj_im] at hi
  linarith

private theorem quadratic_LFunction_real_continuous {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hn : χ ≠ 1) :
    Continuous (fun x : ℝ => (χ.LFunction (x:ℂ)).re) :=
  Complex.continuous_re.comp ((χ.differentiable_LFunction hn).continuous.comp
    Complex.continuous_ofReal)

private theorem quadratic_LFunction_re_pos_of_one_lt {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1) {x : ℝ} (hx : 1<x) :
    0 < (χ.LFunction (x:ℂ)).re := by
  have hs : 1<(x:ℂ).re := by simpa using hx
  have hab := LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    (f:=χ.zetaMul) (x:=1) (fun _ ht => χ.LSeriesSummable_zetaMul ht)
  have hfirst : 0 < χ.zetaMul 1 := by rw [χ.isMultiplicative_zetaMul.map_one]; exact zero_lt_one
  have hpos := Complex.pos_iff.mp (LSeries.positive (DirichletCharacter.zetaMul_nonneg hχ)
    hfirst (lt_of_le_of_lt hab (by exact_mod_cast hx)))
  rw [estermannTwo_LSeries_eq χ hs,Complex.mul_re,riemannZeta_im_eq_zero_of_one_lt hx,
    zero_mul,sub_zero] at hpos
  exact pos_of_mul_pos_right hpos.1 (riemannZeta_re_pos_of_one_lt hx).le

theorem quadratic_LFunction_one_re_pos {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ^ 2 = 1) (hn : χ ≠ 1) :
    0 < (χ.LFunction 1).re := by
  have hlim := (quadratic_LFunction_real_continuous hn).continuousAt.continuousWithinAt
    (s:=Ioi (1:ℝ)) (x:=1)
  have hn₀ : 0 ≤ (χ.LFunction (↑(1:ℝ))).re :=
    ge_of_tendsto hlim (eventually_of_mem self_mem_nhdsWithin (fun x hx =>
      (quadratic_LFunction_re_pos_of_one_lt hχ hx).le))
  rw [Complex.ofReal_one] at hn₀
  refine lt_of_le_of_ne hn₀ (fun he => ?_)
  have him := quadratic_LFunction_im_eq_zero hχ hn 1
  rw [Complex.ofReal_one] at him
  exact χ.LFunction_ne_zero_of_one_le_re (.inl hn) (by simp)
    (Complex.ext he.symm him)

theorem quadratic_LFunction_one_eq_norm {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ^ 2 = 1) (hn : χ ≠ 1) :
    χ.LFunction 1 = (‖χ.LFunction 1‖ : ℂ) := by
  have hi := quadratic_LFunction_im_eq_zero hχ hn 1
  rw [Complex.ofReal_one] at hi
  have he : χ.LFunction 1 = (((χ.LFunction 1).re):ℂ) :=
    Complex.ext rfl hi
  conv_rhs => rw [he,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (quadratic_LFunction_one_re_pos hχ hn).le]
  exact he

theorem quadratic_LFunction_re_nonneg_of_zero_free_interval {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ^2=1) (hn : χ≠1)
    {β : ℝ} (hβ : β<1) (h : ∀ x∈Ico β 1, χ.LFunction (x:ℂ) ≠ 0) :
    0 ≤ (χ.LFunction (β:ℂ)).re := by
  by_contra! hneg
  have hr := quadratic_LFunction_one_re_pos hχ hn
  obtain ⟨x,hx,hz⟩ := intermediate_value_Icc hβ.le
    (quadratic_LFunction_real_continuous hn).continuousOn
    (show (0:ℝ) ∈ Icc (χ.LFunction (β:ℂ)).re (χ.LFunction (↑(1:ℝ))).re by
      rw [Complex.ofReal_one]; exact ⟨hneg.le,hr.le⟩)
  have hx' : x<1 := by
    refine lt_of_le_of_ne hx.2 (fun h₁ => ?_)
    subst x
    change (χ.LFunction (↑(1:ℝ))).re = 0 at hz
    rw [Complex.ofReal_one] at hz
    linarith only [hz,hr]
  exact h x ⟨hx.1,hx'⟩ (Complex.ext hz (quadratic_LFunction_im_eq_zero hχ hn x))

private theorem entire_zeta_eq {s : ℂ} (hs : s≠1) :
    entireL (1 : DirichletCharacter ℂ 1) s = (s-1)*riemannZeta s := by
  rw [entireL_apply_of_ne_one _ hs]
  simp

theorem riemannZeta_re_neg_left_near_one :
    ∃ r : ℝ, 0<r ∧ ∀ β : ℝ, 1-r<β → β<1 → (riemannZeta (β:ℂ)).re < 0 := by
  let Z : ℝ → ℝ := fun x => (entireL (1 : DirichletCharacter ℂ 1) (x:ℂ)).re
  have hZ : Z 1 = 1 := by simp [Z,entireL,DirichletCharacter.LFunctionTrivChar₁]
  have hZc : Continuous Z :=
    Complex.continuous_re.comp ((differentiable_entireL _).continuous.comp Complex.continuous_ofReal)
  obtain ⟨r,hr,hrc⟩ := Metric.continuousAt_iff.mp hZc.continuousAt (1/2) (by norm_num)
  refine ⟨r,hr,?_⟩
  intro β hlo hhi
  have hd : dist β 1 < r := by rw [Real.dist_eq,abs_of_neg (sub_neg.mpr hhi)]; linarith
  have hZβ := hrc hd
  rw [Real.dist_eq,hZ,abs_lt] at hZβ
  have hpos : 0 < Z β := by linarith only [hZβ.1]
  have hne : (β:ℂ)≠1 := by exact_mod_cast hhi.ne
  simp only [Z,entire_zeta_eq hne,Complex.mul_re,Complex.sub_re,Complex.sub_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.one_re,Complex.one_im,sub_self,zero_mul,
    sub_zero] at hpos
  exact neg_of_mul_pos_right hpos (sub_neg.mpr hhi).le

end FareyGoldbach
