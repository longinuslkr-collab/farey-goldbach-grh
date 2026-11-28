import FareyGoldbach.SharpPerronKernel

/-! # The sharp Perron kernel with a free smoothing width -/

namespace FareyGoldbach

noncomputable def smallConductorKernel (X : ℕ) (δ : ℝ) (s : ℂ) : ℂ :=
  ((X:ℝ):ℂ)^s * sharpPerronKernel δ s

theorem differentiableAt_smallConductorKernel {X : ℕ} (hX : 0 < X) (δ : ℝ)
    {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ (smallConductorKernel X δ) s := by
  have hx : ((X:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Nat.cast_ne_zero.mpr hX.ne')
  unfold smallConductorKernel
  simp_rw [Complex.cpow_def_of_ne_zero hx]
  apply DifferentiableAt.mul
  · fun_prop
  · exact differentiableAt_sharpPerronKernel _ (by rintro rfl; simp at hs)

theorem norm_smallConductorKernel {X : ℕ} (hX : 0 < X) (δ : ℝ) (s : ℂ) :
    ‖smallConductorKernel X δ s‖ = (X:ℝ)^s.re * ‖sharpPerronKernel δ s‖ := by
  rw [smallConductorKernel,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hX)]

end FareyGoldbach
