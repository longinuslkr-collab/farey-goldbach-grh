import FareyGoldbach.SharpPerronEstimates
import FareyGoldbach.SharpPerronInversion
import FareyGoldbach.SharpPrimePrimitiveReduction

/-! # The sharp GRH bound for von Mangoldt sums twisted by Dirichlet characters -/

open MeasureTheory Set
open scoped Classical

namespace FareyGoldbach

private theorem primitive_sharpVonMangoldtTwist (hGRH : DirichletGRH) {X d : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) (hX : 2≤X) :
    ‖(∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n) -
        (if χ=1 then (X:ℂ) else 0)‖ ≤
      5000000000000 * Real.sqrt (X:ℝ) * Real.log (2*(d:ℝ)*(X:ℝ))^2 := by
  let K := scaledSharpPerronKernel X
  let G := fun u : ℝ => K ((1/4:ℝ)+(u:ℂ)*Complex.I)*negLogDerivL χ ((1/4:ℝ)+(u:ℂ)*Complex.I)
  let a := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  let L := Real.log (2*(d:ℝ)*(X:ℝ))
  let M := Real.sqrt (X:ℝ) * L^2
  obtain ⟨htwo,hright⟩ := sharpPerron_two_integrable χ hX
  obtain ⟨hleft,hleft_bound⟩ := sharpPerron_quarter_bound hGRH hprim hX
  obtain ⟨hzs,hzs_bound⟩ := sharpPerron_zero_bound hGRH hprim hX
  obtain ⟨A,hA,hhoriz⟩ := sharpPerron_horizontal_decay hX
  have hformula := primitive_kernel_contour_shift hGRH hprim K
    (scaledSharpPerronKernel_differentiableOn hX) hright hleft hzs.of_norm
    ⟨A,0,hA,fun σ hσ u _ => hhoriz σ hσ u⟩
  have hsum := (sharpPerron_vonMangoldt_eq_verticalIntegral χ hX htwo).trans hformula
  have hpole :
      ‖(if χ=1 then K 1 else 0) - (if χ=1 then (X:ℂ) else 0)‖ ≤ 5 := by
    by_cases hχ : χ=1
    · simpa only [K,hχ,ite_true] using sharpPerron_pole_error hX
    · simp [hχ]
  have hzero :
      ‖∑' ρ, kernelZeroTerm χ K ρ‖ ≤ 1000000000*M := by
    apply (norm_tsum_le_tsum_norm hzs).trans
    simpa only [M,L,K,mul_assoc] using hzs_bound
  have hcoef : ‖a‖≤1 := by
    have hpi : (1:ℝ)≤2*Real.pi := by linarith only [Real.pi_gt_three]
    dsimp [a]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact div_le_self zero_le_one hpi
  have hquarter : ‖a*(∫ u : ℝ, G u)‖ ≤ 4000000000000*M := by
    rw [norm_mul]
    refine (mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)).trans ?_
    simpa only [one_mul,M,L,G,K,mul_assoc] using hleft_bound
  have hMr : 1≤M := by
    have hL : 1≤L := sharpPerron_log_ge_one hX
    have hXr : (1:ℝ)≤X := Nat.one_le_cast.mpr (by omega)
    have hsqrt : 1≤Real.sqrt (X:ℝ) := by simpa using Real.sqrt_le_sqrt hXr
    exact one_le_mul_of_one_le_of_one_le hsqrt (one_le_pow₀ hL)
  rw [hsum]
  change ‖(if χ=1 then K 1 else 0) - (∑' ρ, kernelZeroTerm χ K ρ) + a*(∫ u : ℝ, G u) -
    (if χ=1 then (X:ℂ) else 0)‖ ≤ _
  rw [show (if χ=1 then K 1 else 0) - (∑' ρ, kernelZeroTerm χ K ρ) + a*(∫ u : ℝ, G u) -
      (if χ=1 then (X:ℂ) else 0) =
    ((if χ=1 then K 1 else 0) - (if χ=1 then (X:ℂ) else 0)) -
      (∑' ρ, kernelZeroTerm χ K ρ) + a*(∫ u : ℝ, G u) by ring]
  have htri := norm_add_le
    (((if χ=1 then K 1 else 0) - (if χ=1 then (X:ℂ) else 0)) - (∑' ρ, kernelZeroTerm χ K ρ))
    (a*(∫ u : ℝ, G u))
  have htri' := norm_sub_le ((if χ=1 then K 1 else 0) - (if χ=1 then (X:ℂ) else 0))
    (∑' ρ, kernelZeroTerm χ K ρ)
  change _ ≤ 5000000000000 * Real.sqrt (X:ℝ) * L^2
  rw [mul_assoc]
  change _ ≤ 5000000000000*M
  linarith only [htri,htri',hpole,hzero,hquarter,hMr]

/-- Dirichlet GRH gives the sharp-cutoff estimate for every character,
including characters induced from a smaller conductor. -/
theorem sharpVonMangoldtTwist_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ C : ℝ, 0<C ∧ ∀ (X d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d), 2≤X →
      ‖(∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n) -
          (if χ=1 then (X:ℂ) else 0)‖ ≤
        C * Real.sqrt (X:ℝ) * Real.log (2*(d:ℝ)*(X:ℝ))^2 := by
  refine ⟨5000000000000+4,by norm_num,?_⟩
  exact sharpVonMangoldtTwist_of_primitive_bound 5000000000000 (by norm_num)
    (fun _ _ _ _ hprim hX => primitive_sharpVonMangoldtTwist hGRH hprim hX)

end FareyGoldbach
