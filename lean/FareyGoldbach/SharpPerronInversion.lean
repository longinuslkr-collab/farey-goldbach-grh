import FareyGoldbach.SharpPerronScale
import FareyGoldbach.SharpPerronKernel
import FareyGoldbach.SmoothedExplicitFormula

/-! # Exact Perron inversion at a positive integer endpoint -/

open MeasureTheory

namespace FareyGoldbach

theorem mellinInv_mul_positive_cpow {X x : ℝ} (hX : 0<X) (hx : 0<x)
    (K : ℂ → ℂ) (σ : ℝ) :
    mellinInv σ (fun s => (X:ℂ)^s * K s) x = mellinInv σ K (x/X) := by
  have he (s : ℂ) : ((x/X:ℝ):ℂ)^(-s) = (x:ℂ)^(-s) * (X:ℂ)^s := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hx hX).ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hX.ne'), ← Complex.exp_add,
      ← Complex.ofReal_log (div_pos hx hX).le, ← Complex.ofReal_log hx.le,
      ← Complex.ofReal_log hX.le, Real.log_div hx.ne' hX.ne', Complex.ofReal_sub]
    congr 1
    ring
  unfold mellinInv
  simp only [smul_eq_mul, he, mul_assoc]

theorem differentiableAt_scaledSharpPerronKernel {X : ℕ} (hX : 2≤X) {s : ℂ}
    (hs : 0<s.re) : DifferentiableAt ℂ (scaledSharpPerronKernel X) s := by
  have hx : ((X:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))
  unfold scaledSharpPerronKernel
  simp_rw [Complex.cpow_def_of_ne_zero hx]
  apply DifferentiableAt.mul
  · fun_prop
  · exact differentiableAt_sharpPerronKernel _ (by rintro rfl; simp at hs)

theorem sharpPerron_pole_error {X : ℕ} (hX : 2≤X) :
    ‖scaledSharpPerronKernel X 1-(X:ℂ)‖≤5 := by
  have hx : (0:ℝ)<X := Nat.cast_pos.mpr (by omega)
  have h₁ := sharpPerronWidth_le_quarter hX
  have hp := sharpPerronKernel_one_sub_norm_le (sharpPerronWidth_pos hX)
    (h₁.trans (by norm_num))
  calc ‖scaledSharpPerronKernel X 1-(X:ℂ)‖
      = ‖(X:ℂ)*(sharpPerronKernel (sharpPerronWidth X) 1-1)‖ := by
        simp [scaledSharpPerronKernel,mul_sub]
    _ = (X:ℝ)*‖sharpPerronKernel (sharpPerronWidth X) 1-1‖ := by
        rw [norm_mul,Complex.norm_natCast]
    _ ≤ (X:ℝ)*(18*sharpPerronWidth X) := mul_le_mul_of_nonneg_left hp hx.le
    _ ≤ 5 := by
      dsimp [sharpPerronWidth,sharpPerronHeight]
      field_simp
      linarith

/-- The transition ramp lies strictly between the consecutive integers `X` and `X+1`. -/
theorem sharpPerron_vonMangoldt_eq_verticalIntegral {d : ℕ} [NeZero d]
    (χ : DirichletCharacter ℂ d) {X : ℕ} (hX : 2≤X)
    (hker : Integrable (fun u : ℝ => scaledSharpPerronKernel X (2+(u:ℂ)*Complex.I))) :
    (∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ)*χ (n : ZMod d)) =
      ((1/(2*Real.pi):ℝ):ℂ) * ∫ u : ℝ, scaledSharpPerronKernel X (2+(u:ℂ)*Complex.I) *
        negLogDerivL χ (2+(u:ℂ)*Complex.I) := by
  have hx : (0:ℝ)<X := Nat.cast_pos.mpr (by omega)
  have hδ := sharpPerronWidth_pos hX
  let w := fun x : ℝ => (sharpPerronWeight (sharpPerronWidth X) (x/X):ℂ)
  have hinv (x : ℝ) (hx' : 0<x) : mellinInv 2 (scaledSharpPerronKernel X) x = w x := by
    unfold scaledSharpPerronKernel
    rw [mellinInv_mul_positive_cpow hx hx']
    exact mellinInv_sharpPerronKernel hδ ((sharpPerronWidth_le_quarter hX).trans (by norm_num))
      (by norm_num) le_rfl (div_pos hx' hx)
  have hsupp (n : ℕ) (hn : X<n) : w n = 0 := by
    have hsucc : (X:ℝ)+1 ≤ n := by exact_mod_cast hn
    have h := sharpPerronWeight_eq_zero hδ ((le_div_iff₀ hx).mpr
      ((sharpPerron_end_lt_succ hX).le.trans hsucc))
    simp only [w,h,Complex.ofReal_zero]
  calc _ = ∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod d) * w n := by
            apply Finset.sum_congr rfl
            intro n hn
            obtain ⟨hn₁,hn₂⟩ := Finset.mem_Icc.mp hn
            have h := sharpPerronWeight_eq_one hδ (div_pos (Nat.cast_pos.mpr hn₁) hx)
              ((div_le_one hx).mpr (Nat.cast_le.mpr hn₂))
            simp only [w,h,Complex.ofReal_one,mul_one]
    _ = _ := weightedVonMangoldt_eq_verticalIntegral χ _ w X hker hinv hsupp

end FareyGoldbach
