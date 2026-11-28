module

public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Integral Plancherel on the real line -/

public section

open MeasureTheory FourierTransform SchwartzMap Real
open scoped FourierTransform SchwartzMap ComplexInnerProductSpace

namespace FareyGoldbach

/-- On `L¹ ∩ L²`, the integral Fourier transform represents the Hilbert space transform. -/
theorem fourier_ae_eq_fourierL2 {f : ℝ → ℂ} (hf₁ : Integrable f) (hf₂ : MemLp f 2) :
    𝓕 f =ᵐ[volume] (𝓕 (hf₂.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) := by
  let u := hf₂.toLp f
  have hc : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf₁
  apply ae_eq_of_integral_contDiff_smul_eq hc.locallyIntegrable
    ((Lp.memLp (𝓕 u)).locallyIntegrable (by norm_num))
  intro ψ hψ hs
  let g : 𝓢(ℝ, ℂ) := (hs.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hψ)
  have hg (x : ℝ) : g x = (ψ x : ℂ) := rfl
  have ht := congrArg (fun T : 𝓢'(ℝ, ℂ) ↦ T g) (Lp.fourier_toTemperedDistribution_eq u)
  change (𝓕 (Lp.toTemperedDistribution u)) g = Lp.toTemperedDistribution (𝓕 u) g at ht
  rw [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply] at ht
  have hswap : (∫ x : ℝ, 𝓕 g x • f x) = ∫ x : ℝ, g x • 𝓕 f x := by
    simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner g.integrable hf₁
  have hrep : (∫ x : ℝ, 𝓕 g x • u x) = ∫ x : ℝ, 𝓕 g x • f x := by
    apply integral_congr_ae
    filter_upwards [hf₂.coeFn_toLp] with x hx
    rw [show u x = f x from hx]
  have hh := hswap.symm.trans (hrep.symm.trans ht)
  simp only [hg, smul_eq_mul] at hh
  simp only [RCLike.real_smul_eq_coe_mul]
  convert! hh using 3

/-- Square integrability of the classical integral Fourier transform. -/
theorem integrable_fourier_norm_sq {f : ℝ → ℂ} (hf₁ : Integrable f) (hf₂ : MemLp f 2) :
    Integrable (fun x : ℝ ↦ ‖𝓕 f x‖ ^ 2) := by
  have h : MemLp (𝓕 f) 2 := (memLp_congr_ae (fourier_ae_eq_fourierL2 hf₁ hf₂)).mpr (Lp.memLp _)
  exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h

/-- Plancherel for the classical integral Fourier transform of an `L¹ ∩ L²` function. -/
theorem integral_fourier_norm_sq_eq {f : ℝ → ℂ} (hf₁ : Integrable f) (hf₂ : MemLp f 2) :
    (∫ x : ℝ, ‖𝓕 f x‖ ^ 2) = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  let u := hf₂.toLp f
  have h := Lp.inner_fourier_eq u u
  rw [L2.inner_def, L2.inner_def] at h
  simp_rw [inner_self_eq_norm_sq_to_K] at h
  have h' : (∫ x : ℝ, ‖𝓕 u x‖ ^ 2) = ∫ x : ℝ, ‖u x‖ ^ 2 := by
    exact_mod_cast h
  calc
    _ = ∫ x : ℝ, ‖𝓕 u x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [fourier_ae_eq_fourierL2 hf₁ hf₂] with x hx using congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) hx
    _ = ∫ x : ℝ, ‖u x‖ ^ 2 := h'
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf₂.coeFn_toLp] with x hx using congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) hx

/-- Compact essential support supplies the `L¹` hypothesis, including for discontinuous cutoffs. -/
theorem compact_fourier_plancherel {f : ℝ → ℂ} {a b : ℝ} (hf₂ : MemLp f 2)
    (hs : ∀ᵐ x ∂volume, x ∉ Set.Icc a b → f x = 0) :
    Integrable (fun x : ℝ ↦ ‖𝓕 f x‖ ^ 2) ∧
      (∫ x : ℝ, ‖𝓕 f x‖ ^ 2) = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  have hi := (hf₂.locallyIntegrable (by norm_num)).integrableOn_isCompact
    (isCompact_Icc (a := a) (b := b))
  have hf₁ : Integrable f := (hi.integrable_indicator measurableSet_Icc).congr (by
    filter_upwards [hs] with x hx
    by_cases h : x ∈ Set.Icc a b
    · simp [h]
    · simp [h, hx h])
  exact ⟨integrable_fourier_norm_sq hf₁ hf₂, integral_fourier_norm_sq_eq hf₁ hf₂⟩

end FareyGoldbach
