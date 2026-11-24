import FareyGoldbach.Defs
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Module A2: Mellin Transform of the Tilted Quartic Bump

This module is completely independent of `DirichletGRH` and proves all analytic kernel
estimates needed for Stage 2 (`DirichletGRH → SmoothedTwistEstimate`):

1. `quarticTilted lam x := w(x) e(lam * x)`, `quarticKernel lam s := mellin (quarticTilted lam) s`,
   and `scaledTiltedBump Y t x := w(x / Y) e(t * x)` with scaling identity
   `mellin (scaledTiltedBump Y t) s = Y ^ s * quarticKernel (t * Y) s`.
2. Holomorphy `differentiableOn_quarticKernel` on `{s : ℂ | -2 < s.re}` and exact normalization
   `quarticKernel 0 s = 32 / ((s + 2) * (s + 3) * (s + 4))`, `quarticKernel 0 1 = 8 / 15`.
3. Log-variable representation `u = log x ∈ (-∞, 0]` and an elementary second-derivative
   van der Corput lemma `van_der_corput_second_deriv`.
4. Uniform stationary-phase bound `quarticKernel_norm_le_inv_sqrt`:
   `‖K_λ(σ + iγ)‖ ≤ 1792 / √(1 + |λ|)` for all `1/4 ≤ σ ≤ 2`, `γ ∈ ℝ`, `λ ∈ ℝ`.
5. Uniform tail bound `quarticKernel_norm_le_tail`:
   `‖K_λ(σ + iγ)‖ ≤ 15000 / (1 + |γ|)²` for all `1/4 ≤ σ ≤ 2` and `|γ| ≥ 4π|λ| + 2`
   (constant completely independent of `λ` via two integrations by parts with full phase).
6. Vertical integrability `verticalIntegrable_mellin_scaledTiltedBump` and Mellin inversion
   `mellinInv_scaledTiltedBump_eq` on `1/4 ≤ σ ≤ 2`.
-/

open Real Complex Set Filter MeasureTheory Topology

namespace FareyGoldbach

section DefinitionsAndHolomorphy

/-- Elementary quartic bump tilted by frequency `lam`: `x ↦ w(x) e(lam * x)`. -/
noncomputable def quarticTilted (lam : ℝ) (x : ℝ) : ℂ :=
  (quarticBump x : ℂ) * e (lam * x)

/-- Mellin transform `K_lam(s) = ∫_0^∞ x^(s-1) w(x) e(lam * x) dx`. -/
noncomputable def quarticKernel (lam : ℝ) (s : ℂ) : ℂ :=
  mellin (quarticTilted lam) s

/-- Scaled tilted bump `f_{Y,t}(x) = w(x / Y) e(t * x)` on `(0, ∞)`. -/
noncomputable def scaledTiltedBump (Y : ℕ) (t : ℝ) (x : ℝ) : ℂ :=
  (quarticBump (x / (Y : ℝ)) : ℂ) * e (t * x)

lemma continuous_e_real : Continuous e := by
  unfold e
  exact Complex.continuous_exp.comp
    (((continuous_const.mul Complex.continuous_ofReal).mul continuous_const))

lemma quarticBump_of_mem {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    quarticBump x = 16 * x ^ 2 * (1 - x) ^ 2 := by
  unfold quarticBump; simp [h0, h1]

lemma continuous_quarticBump : Continuous quarticBump := by
  have h_eq : quarticBump = fun x : ℝ =>
      if x ≤ 0 then 0 else if x ≤ 1 then 16 * x ^ 2 * (1 - x) ^ 2 else 0 := by
    funext x
    by_cases h0 : x ≤ 0
    · have hnot : ¬ (0 < x ∧ x < 1) := fun h => not_lt_of_ge h0 h.1
      unfold quarticBump; simp only [h0, hnot, ↓reduceIte]
    · by_cases h1 : x < 1
      · rw [quarticBump_of_mem (lt_of_not_ge h0) h1]
        simp only [h0, h1.le, ↓reduceIte]
      · have hnot : ¬ (0 < x ∧ x < 1) := fun h => h1 h.2
        unfold quarticBump
        by_cases h1eq : x = 1
        · subst h1eq; simp
        · have hnot1 : ¬ x ≤ 1 := not_le.mpr (lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h1eq))
          simp only [h0, hnot, hnot1, ↓reduceIte]
  rw [h_eq]
  refine Continuous.if_le continuous_const ?_ continuous_id continuous_const fun x hx => ?_
  · refine Continuous.if_le (by fun_prop) continuous_const continuous_id continuous_const fun x hx => ?_
    simp [hx]
  · simp [hx]

lemma continuous_quarticTilted (lam : ℝ) : Continuous (quarticTilted lam) := by
  unfold quarticTilted
  exact (Complex.continuous_ofReal.comp continuous_quarticBump).mul
    (continuous_e_real.comp (continuous_const.mul continuous_id))

lemma continuous_scaledTiltedBump (Y : ℕ) (t : ℝ) : Continuous (scaledTiltedBump Y t) := by
  unfold scaledTiltedBump
  exact (Complex.continuous_ofReal.comp (continuous_quarticBump.comp (continuous_id.div_const _))).mul
    (continuous_e_real.comp (continuous_const.mul continuous_id))

lemma quarticBump_eq_zero_of_not_mem {x : ℝ} (hx : ¬ (0 < x ∧ x < 1)) : quarticBump x = 0 := by
  unfold quarticBump; simp only [hx, ↓reduceIte]

lemma quarticBump_nonneg (x : ℝ) : 0 ≤ quarticBump x := by
  unfold quarticBump
  split_ifs
  · positivity
  · exact le_rfl

lemma norm_e_real (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  have h : 2 * (Real.pi : ℂ) * (x : ℂ) * Complex.I = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

lemma norm_quarticTilted (lam x : ℝ) : ‖quarticTilted lam x‖ = quarticBump x := by
  unfold quarticTilted
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (quarticBump_nonneg x),
      norm_e_real, mul_one]

lemma scaledTiltedBump_eq_quarticTilted {Y : ℕ} (hY : 1 ≤ Y) (t x : ℝ) :
    scaledTiltedBump Y t x = quarticTilted (t * (Y : ℝ)) ((Y : ℝ)⁻¹ * x) := by
  have hY0 : (Y : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold scaledTiltedBump quarticTilted
  congr 1
  · rw [div_eq_inv_mul]
  · congr 1; field_simp [hY0]

/-- Scaling identity: `mellin (scaledTiltedBump Y t) s = Y ^ s * quarticKernel (t * Y) s`. -/
theorem mellin_scaledTiltedBump_eq {Y : ℕ} (hY : 1 ≤ Y) (t : ℝ) (s : ℂ) :
    mellin (scaledTiltedBump Y t) s = ((Y : ℝ) : ℂ) ^ s * quarticKernel (t * (Y : ℝ)) s := by
  have hY_pos : (0 : ℝ) < (Y : ℝ) := Nat.cast_pos.mpr (by omega)
  have hfun : scaledTiltedBump Y t = fun x => quarticTilted (t * (Y : ℝ)) ((Y : ℝ)⁻¹ * x) :=
    funext (scaledTiltedBump_eq_quarticTilted hY t)
  rw [hfun, mellin_comp_mul_left (quarticTilted (t * (Y : ℝ))) s (inv_pos.mpr hY_pos),
      smul_eq_mul, quarticKernel]
  congr 1
  have hY_ne : ((Y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY_pos.ne'
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (inv_pos.mpr hY_pos).ne'),
      Complex.cpow_def_of_ne_zero hY_ne,
      ← Complex.ofReal_log (inv_pos.mpr hY_pos).le,
      ← Complex.ofReal_log hY_pos.le, Real.log_inv]
  congr 1; push_cast; ring

lemma quarticTilted_isBigO_atTop (lam : ℝ) :
    quarticTilted lam =O[atTop] fun x : ℝ => Real.exp (-1 * x) := by
  refine Asymptotics.isBigO_iff.mpr ⟨1, Filter.eventually_atTop.mpr ⟨1, fun x hx => ?_⟩⟩
  rw [norm_quarticTilted, quarticBump_eq_zero_of_not_mem (by intro h; linarith)]
  positivity

lemma quarticTilted_isBigO_zero (lam : ℝ) :
    quarticTilted lam =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ (-(-2 : ℝ)) := by
  refine Asymptotics.isBigO_iff.mpr ⟨16, ?_⟩
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)] with x hx0 hx1
  have hx0' : 0 < x := hx0
  have hx1' : x < 1 := hx1
  rw [norm_quarticTilted, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0'.le _),
      quarticBump_of_mem hx0' hx1']
  have hsq : (1 - x) ^ 2 ≤ 1 := by nlinarith only [hx0', hx1']
  have hrpow : x ^ (-(-2 : ℝ)) = x ^ (2 : ℕ) := by
    rw [neg_neg, ← Real.rpow_natCast]; norm_num
  rw [hrpow]
  have hx2 : 0 ≤ 16 * x ^ 2 := by positivity
  nlinarith only [hsq, hx2]

theorem mellinConvergent_quarticTilted {lam : ℝ} {s : ℂ} (hs : -2 < s.re) :
    MellinConvergent (quarticTilted lam) s :=
  mellinConvergent_of_isBigO_rpow_exp zero_lt_one
    ((continuous_quarticTilted lam).locallyIntegrable.locallyIntegrableOn (Ioi 0))
    (quarticTilted_isBigO_atTop lam) (quarticTilted_isBigO_zero lam) hs

theorem mellinConvergent_scaledTiltedBump {Y : ℕ} (hY : 1 ≤ Y) {t : ℝ} {s : ℂ} (hs : -2 < s.re) :
    MellinConvergent (scaledTiltedBump Y t) s := by
  have hY_pos : (0 : ℝ) < (Y : ℝ) := Nat.cast_pos.mpr (by omega)
  have hfun : scaledTiltedBump Y t = fun x => quarticTilted (t * (Y : ℝ)) ((Y : ℝ)⁻¹ * x) :=
    funext (scaledTiltedBump_eq_quarticTilted hY t)
  rw [hfun]
  exact (MellinConvergent.comp_mul_left (inv_pos.mpr hY_pos)).2 (mellinConvergent_quarticTilted hs)

theorem differentiableAt_quarticKernel {lam : ℝ} {s : ℂ} (hs : -2 < s.re) :
    DifferentiableAt ℂ (quarticKernel lam) s :=
  mellin_differentiableAt_of_isBigO_rpow_exp zero_lt_one
    ((continuous_quarticTilted lam).locallyIntegrable.locallyIntegrableOn (Ioi 0))
    (quarticTilted_isBigO_atTop lam) (quarticTilted_isBigO_zero lam) hs

theorem differentiableOn_quarticKernel (lam : ℝ) :
    DifferentiableOn ℂ (quarticKernel lam) {s : ℂ | -2 < s.re} :=
  fun _ hs => (differentiableAt_quarticKernel hs).differentiableWithinAt

theorem differentiableAt_mellin_scaledTiltedBump {Y : ℕ} (hY : 1 ≤ Y) (t : ℝ)
    {s : ℂ} (hs : -2 < s.re) :
    DifferentiableAt ℂ (mellin (scaledTiltedBump Y t)) s := by
  have hfun : mellin (scaledTiltedBump Y t) =
      fun w => ((Y : ℝ) : ℂ) ^ w * quarticKernel (t * (Y : ℝ)) w :=
    funext (mellin_scaledTiltedBump_eq hY t)
  rw [hfun]
  have hY_ne : ((Y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))
  exact (DifferentiableAt.const_cpow differentiableAt_id (Or.inl hY_ne)).mul
    (differentiableAt_quarticKernel hs)

end DefinitionsAndHolomorphy

section ExactNormalization

/-- Exact Mellin transform at zero frequency: `K_0(s) = 32 / ((s + 2)(s + 3)(s + 4))`. -/
theorem quarticKernel_zero {s : ℂ} (hs : -2 < s.re) :
    quarticKernel 0 s = 32 / ((s + 2) * (s + 3) * (s + 4)) := by
  have hs2 : 0 < s.re + (2 : ℂ).re := by simp; linarith
  have hs3 : 0 < s.re + (3 : ℂ).re := by simp; linarith
  have hs4 : 0 < s.re + (4 : ℂ).re := by simp; linarith
  have hm2 := hasMellin_cpow_Ioc (2 : ℂ) hs2
  have hm3 := hasMellin_cpow_Ioc (3 : ℂ) hs3
  have hm4 := hasMellin_cpow_Ioc (4 : ℂ) hs4
  let f₂ : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) * Set.indicator (Ioc 0 1) (fun u : ℝ => (u : ℂ) ^ (2 : ℂ)) t
  let f₃ : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) * Set.indicator (Ioc 0 1) (fun u : ℝ => (u : ℂ) ^ (3 : ℂ)) t
  let f₄ : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) * Set.indicator (Ioc 0 1) (fun u : ℝ => (u : ℂ) ^ (4 : ℂ)) t
  have hi2 : IntegrableOn f₂ (Ioi 0) := hm2.1
  have hi3 : IntegrableOn f₃ (Ioi 0) := hm3.1
  have hi4 : IntegrableOn f₄ (Ioi 0) := hm4.1
  have hval2 : (∫ t in Ioi (0 : ℝ), f₂ t) = 1 / (s + 2) := hm2.2
  have hval3 : (∫ t in Ioi (0 : ℝ), f₃ t) = 1 / (s + 3) := hm3.2
  have hval4 : (∫ t in Ioi (0 : ℝ), f₄ t) = 1 / (s + 4) := hm4.2
  have hpt : ∀ x ∈ Ioi (0 : ℝ),
      (x : ℂ) ^ (s - 1) • quarticTilted 0 x = 16 * f₂ x - 32 * f₃ x + 16 * f₄ x := by
    intro x hx
    have hx0 : 0 < x := hx
    have hpow : ∀ n : ℕ, (x : ℂ) ^ (n : ℂ) = (x : ℂ) ^ n := fun n => Complex.cpow_natCast _ n
    have he0 : e (0 * x) = 1 := by unfold e; simp
    dsimp [f₂, f₃, f₄]
    unfold quarticTilted
    rw [he0, mul_one]
    by_cases hx1 : x < 1
    · have hmem : x ∈ Ioc (0 : ℝ) 1 := ⟨hx0, hx1.le⟩
      rw [quarticBump_of_mem hx0 hx1]
      simp only [Set.indicator_of_mem hmem]
      rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num,
          show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num,
          show (4 : ℂ) = ((4 : ℕ) : ℂ) by norm_num, hpow 2, hpow 3, hpow 4]
      push_cast; ring
    · have hnot : ¬ (0 < x ∧ x < 1) := fun h => hx1 h.2
      rw [quarticBump_eq_zero_of_not_mem hnot, Complex.ofReal_zero, mul_zero]
      by_cases hx1eq : x = 1
      · subst hx1eq
        have hmem : (1 : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨zero_lt_one, le_rfl⟩
        simp only [Set.indicator_of_mem hmem, Complex.ofReal_one, Complex.one_cpow]
        ring
      · have hnotIoc : x ∉ Ioc (0 : ℝ) 1 := fun h => hx1eq (le_antisymm h.2 (not_lt.mp hx1))
        simp only [Set.indicator_of_notMem hnotIoc, mul_zero, sub_self, add_zero]
  have hm_eq : quarticKernel 0 s =
      (16 : ℂ) * (1 / (s + 2)) - (32 : ℂ) * (1 / (s + 3)) + (16 : ℂ) * (1 / (s + 4)) := by
    have hi2' : IntegrableOn (fun x => (16 : ℂ) * f₂ x) (Ioi 0) := hi2.const_mul 16
    have hi3' : IntegrableOn (fun x => (32 : ℂ) * f₃ x) (Ioi 0) := hi3.const_mul 32
    have hi4' : IntegrableOn (fun x => (16 : ℂ) * f₄ x) (Ioi 0) := hi4.const_mul 16
    have hi23 : IntegrableOn (fun x => (16 : ℂ) * f₂ x - (32 : ℂ) * f₃ x) (Ioi 0) := hi2'.sub hi3'
    unfold quarticKernel mellin
    rw [setIntegral_congr_fun measurableSet_Ioi hpt,
        integral_add hi23 hi4', integral_sub hi2' hi3',
        integral_const_mul, integral_const_mul, integral_const_mul,
        hval2, hval3, hval4]
  rw [hm_eq]
  have hne2 : s + 2 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  have hne3 : s + 3 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  have hne4 : s + 4 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  field_simp [hne2, hne3, hne4]
  ring

theorem quarticKernel_zero_one : quarticKernel 0 1 = 8 / 15 := by
  rw [quarticKernel_zero (by norm_num)]
  norm_num

/-- At `s = 1`, `mellin (scaledTiltedBump Y t) 1 = ∫ x in 0..Y, scaledTiltedBump Y t x`. -/
theorem mellin_scaledTiltedBump_one {Y : ℕ} (hY : 1 ≤ Y) (t : ℝ) :
    mellin (scaledTiltedBump Y t) 1 = ∫ x in (0 : ℝ)..(Y : ℝ), scaledTiltedBump Y t x := by
  have hY_pos : (0 : ℝ) < (Y : ℝ) := Nat.cast_pos.mpr (by omega)
  unfold mellin
  have hcongr : ∀ x ∈ Ioi (0 : ℝ),
      (x : ℂ) ^ ((1 : ℂ) - 1) • scaledTiltedBump Y t x = scaledTiltedBump Y t x := by
    intro x _
    rw [sub_self, Complex.cpow_zero, one_smul]
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
  have hzero : ∀ x ∈ Ioi (Y : ℝ), scaledTiltedBump Y t x = 0 := by
    intro x hx
    unfold scaledTiltedBump
    have hgt : 1 < x / (Y : ℝ) := (one_lt_div hY_pos).2 hx
    rw [quarticBump_eq_zero_of_not_mem (by intro h; linarith), Complex.ofReal_zero, zero_mul]
  have hsplit : Ioi (0 : ℝ) = Ioc (0 : ℝ) (Y : ℝ) ∪ Ioi (Y : ℝ) :=
    (Set.Ioc_union_Ioi_eq_Ioi hY_pos.le).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) (Y : ℝ)) (Ioi (Y : ℝ)) :=
    Set.disjoint_left.mpr fun x h1 h2 => not_lt_of_ge h1.2 h2
  have hint1 : IntegrableOn (scaledTiltedBump Y t) (Ioc (0 : ℝ) (Y : ℝ)) :=
    (continuous_scaledTiltedBump Y t).integrableOn_Ioc
  have hint2 : IntegrableOn (scaledTiltedBump Y t) (Ioi (Y : ℝ)) :=
    (integrableOn_zero (s := Ioi (Y : ℝ))).congr_fun (fun x hx => (hzero x hx).symm) measurableSet_Ioi
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioi hint1 hint2,
      setIntegral_eq_zero_of_forall_eq_zero hzero, add_zero,
      intervalIntegral.integral_of_le hY_pos.le]

end ExactNormalization

section LogVariableRepresentation

/-- Amplitude `a_σ(u) = 16 e^((σ+2)u) (1 - e^u)²` in log-coordinates `u = log x ≤ 0`. -/
noncomputable def quarticAmp (σ u : ℝ) : ℝ :=
  16 * Real.exp ((σ + 2) * u) * (1 - Real.exp u) ^ 2

/-- First derivative of `quarticAmp σ` with respect to `u`. -/
noncomputable def quarticAmp' (σ u : ℝ) : ℝ :=
  16 * (σ + 2) * Real.exp ((σ + 2) * u) -
    32 * (σ + 3) * Real.exp ((σ + 3) * u) +
    16 * (σ + 4) * Real.exp ((σ + 4) * u)

/-- Second derivative of `quarticAmp σ` with respect to `u`. -/
noncomputable def quarticAmp'' (σ u : ℝ) : ℝ :=
  16 * (σ + 2) ^ 2 * Real.exp ((σ + 2) * u) -
    32 * (σ + 3) ^ 2 * Real.exp ((σ + 3) * u) +
    16 * (σ + 4) ^ 2 * Real.exp ((σ + 4) * u)

/-- Phase `φ(u) = γ u + 2π lam e^u` in log-coordinates `u ≤ 0`. -/
noncomputable def quarticPhase (lam γ u : ℝ) : ℝ :=
  γ * u + 2 * Real.pi * lam * Real.exp u

/-- First derivative `φ'(u) = γ + 2π lam e^u`. -/
noncomputable def quarticPhase' (lam γ u : ℝ) : ℝ :=
  γ + 2 * Real.pi * lam * Real.exp u

/-- Second (and third) derivative `φ''(u) = 2π lam e^u`. -/
noncomputable def quarticPhase'' (lam u : ℝ) : ℝ :=
  2 * Real.pi * lam * Real.exp u

lemma quarticAmp_expand (σ u : ℝ) :
    quarticAmp σ u = 16 * Real.exp ((σ + 2) * u) -
      32 * Real.exp ((σ + 3) * u) + 16 * Real.exp ((σ + 4) * u) := by
  unfold quarticAmp
  have h1 : Real.exp ((σ + 2) * u) * Real.exp u = Real.exp ((σ + 3) * u) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp ((σ + 2) * u) * Real.exp u ^ 2 = Real.exp ((σ + 4) * u) := by
    rw [sq, ← mul_assoc, h1, ← Real.exp_add]; congr 1; ring
  calc 16 * Real.exp ((σ + 2) * u) * (1 - Real.exp u) ^ 2
      = 16 * Real.exp ((σ + 2) * u) - 32 * (Real.exp ((σ + 2) * u) * Real.exp u) +
        16 * (Real.exp ((σ + 2) * u) * Real.exp u ^ 2) := by ring
    _ = _ := by rw [h1, h2]

lemma quarticAmp_zero (σ : ℝ) : quarticAmp σ 0 = 0 := by
  simp [quarticAmp]

lemma quarticAmp'_zero (σ : ℝ) : quarticAmp' σ 0 = 0 := by
  simp [quarticAmp']; ring

lemma hasDerivAt_exp_const_mul (c u : ℝ) :
    HasDerivAt (fun x => Real.exp (c * x)) (c * Real.exp (c * u)) u := by
  have h1 : HasDerivAt (fun x => c * x) c u := by simpa using (hasDerivAt_id u).const_mul c
  convert h1.exp using 1
  ring

lemma hasDerivAt_quarticAmp (σ u : ℝ) :
    HasDerivAt (quarticAmp σ) (quarticAmp' σ u) u := by
  have hfun : quarticAmp σ = fun x =>
      16 * Real.exp ((σ + 2) * x) - 32 * Real.exp ((σ + 3) * x) + 16 * Real.exp ((σ + 4) * x) :=
    funext (quarticAmp_expand σ)
  rw [hfun]
  have h2 := (hasDerivAt_exp_const_mul (σ + 2) u).const_mul 16
  have h3 := (hasDerivAt_exp_const_mul (σ + 3) u).const_mul 32
  have h4 := (hasDerivAt_exp_const_mul (σ + 4) u).const_mul 16
  convert (h2.sub h3).add h4 using 1
  unfold quarticAmp'; ring

lemma hasDerivAt_quarticAmp' (σ u : ℝ) :
    HasDerivAt (quarticAmp' σ) (quarticAmp'' σ u) u := by
  unfold quarticAmp' quarticAmp''
  have h2 := (hasDerivAt_exp_const_mul (σ + 2) u).const_mul (16 * (σ + 2))
  have h3 := (hasDerivAt_exp_const_mul (σ + 3) u).const_mul (32 * (σ + 3))
  have h4 := (hasDerivAt_exp_const_mul (σ + 4) u).const_mul (16 * (σ + 4))
  convert (h2.sub h3).add h4 using 1
  ring

lemma hasDerivAt_quarticPhase (lam γ u : ℝ) :
    HasDerivAt (quarticPhase lam γ) (quarticPhase' lam γ u) u := by
  unfold quarticPhase quarticPhase'
  have h1 : HasDerivAt (fun x => γ * x) γ u := by simpa using (hasDerivAt_id u).const_mul γ
  have h2 := (Real.hasDerivAt_exp u).const_mul (2 * Real.pi * lam)
  exact h1.add h2

lemma hasDerivAt_quarticPhase' (lam γ u : ℝ) :
    HasDerivAt (quarticPhase' lam γ) (quarticPhase'' lam u) u := by
  unfold quarticPhase' quarticPhase''
  have h := (hasDerivAt_const u γ).add ((Real.hasDerivAt_exp u).const_mul (2 * Real.pi * lam))
  simpa only [Pi.add_def, zero_add] using h

lemma hasDerivAt_quarticPhase'' (lam u : ℝ) :
    HasDerivAt (quarticPhase'' lam) (quarticPhase'' lam u) u := by
  unfold quarticPhase''
  exact (Real.hasDerivAt_exp u).const_mul (2 * Real.pi * lam)

lemma abs_quarticAmp_le {σ u : ℝ} (hσ : (1 : ℝ) / 4 ≤ σ) (hu : u ≤ 0) :
    |quarticAmp σ u| ≤ 16 * Real.exp ((9 / 4 : ℝ) * u) := by
  unfold quarticAmp
  have hnn : 0 ≤ 16 * Real.exp ((σ + 2) * u) * (1 - Real.exp u) ^ 2 := by positivity
  rw [abs_of_nonneg hnn]
  have hexp_le1 : Real.exp u ≤ 1 := Real.exp_le_one_iff.mpr hu
  have hexp_pos : 0 < Real.exp u := Real.exp_pos u
  have hsq : (1 - Real.exp u) ^ 2 ≤ 1 := by nlinarith only [hexp_le1, hexp_pos]
  have hmon : Real.exp ((σ + 2) * u) ≤ Real.exp ((9 / 4 : ℝ) * u) :=
    Real.exp_le_exp.mpr (by nlinarith only [hσ, hu])
  have h16 : 0 ≤ 16 * Real.exp ((σ + 2) * u) := by positivity
  calc 16 * Real.exp ((σ + 2) * u) * (1 - Real.exp u) ^ 2
      ≤ 16 * Real.exp ((σ + 2) * u) * 1 := mul_le_mul_of_nonneg_left hsq h16
    _ ≤ 16 * Real.exp ((9 / 4 : ℝ) * u) := by linarith only [hmon]

lemma abs_quarticAmp'_le {σ u : ℝ} (hσ₁ : (1 : ℝ) / 4 ≤ σ) (hσ₂ : σ ≤ 2) (hu : u ≤ 0) :
    |quarticAmp' σ u| ≤ 320 * Real.exp ((9 / 4 : ℝ) * u) := by
  unfold quarticAmp'
  have he2 : Real.exp ((σ + 2) * u) ≤ Real.exp ((9 / 4 : ℝ) * u) :=
    Real.exp_le_exp.mpr (by nlinarith only [hσ₁, hu])
  have he3 : Real.exp ((σ + 3) * u) ≤ Real.exp ((9 / 4 : ℝ) * u) :=
    Real.exp_le_exp.mpr (by nlinarith only [hσ₁, hu])
  have he4 : Real.exp ((σ + 4) * u) ≤ Real.exp ((9 / 4 : ℝ) * u) :=
    Real.exp_le_exp.mpr (by nlinarith only [hσ₁, hu])
  have h1 : |16 * (σ + 2) * Real.exp ((σ + 2) * u)| ≤ 64 * Real.exp ((9 / 4 : ℝ) * u) := by
    rw [abs_of_nonneg (by nlinarith only [hσ₁, Real.exp_pos ((σ + 2) * u)])]
    nlinarith only [hσ₁, hσ₂, he2, Real.exp_pos ((σ + 2) * u)]
  have h2 : |32 * (σ + 3) * Real.exp ((σ + 3) * u)| ≤ 160 * Real.exp ((9 / 4 : ℝ) * u) := by
    rw [abs_of_nonneg (by nlinarith only [hσ₁, Real.exp_pos ((σ + 3) * u)])]
    nlinarith only [hσ₁, hσ₂, he3, Real.exp_pos ((σ + 3) * u)]
  have h3 : |16 * (σ + 4) * Real.exp ((σ + 4) * u)| ≤ 96 * Real.exp ((9 / 4 : ℝ) * u) := by
    rw [abs_of_nonneg (by nlinarith only [hσ₁, Real.exp_pos ((σ + 4) * u)])]
    nlinarith only [hσ₁, hσ₂, he4, Real.exp_pos ((σ + 4) * u)]
  have htri := abs_add_le (16 * (σ + 2) * Real.exp ((σ + 2) * u) -
      32 * (σ + 3) * Real.exp ((σ + 3) * u)) (16 * (σ + 4) * Real.exp ((σ + 4) * u))
  have htri2 := abs_sub (16 * (σ + 2) * Real.exp ((σ + 2) * u))
      (32 * (σ + 3) * Real.exp ((σ + 3) * u))
  linarith only [htri, htri2, h1, h2, h3]

lemma abs_quarticAmp''_le {σ u : ℝ} (hσ₁ : (1 : ℝ) / 4 ≤ σ) (hσ₂ : σ ≤ 2) (hu : u ≤ 0) :
    |quarticAmp'' σ u| ≤ 1632 * Real.exp ((9 / 4 : ℝ) * u) := by
  unfold quarticAmp''
  have he2 : Real.exp ((σ + 2) * u) ≤ Real.exp ((9 / 4 : ℝ) * u) :=
    Real.exp_le_exp.mpr (by nlinarith only [hσ₁, hu])
  have he3 : Real.exp ((σ + 3) * u) ≤ Real.exp ((9 / 4 : ℝ) * u) :=
    Real.exp_le_exp.mpr (by nlinarith only [hσ₁, hu])
  have he4 : Real.exp ((σ + 4) * u) ≤ Real.exp ((9 / 4 : ℝ) * u) :=
    Real.exp_le_exp.mpr (by nlinarith only [hσ₁, hu])
  have h1 : |16 * (σ + 2) ^ 2 * Real.exp ((σ + 2) * u)| ≤ 256 * Real.exp ((9 / 4 : ℝ) * u) := by
    rw [abs_of_nonneg (by positivity)]
    have hsq : (σ + 2) ^ 2 ≤ 16 := by nlinarith only [hσ₁, hσ₂]
    nlinarith only [hsq, he2, Real.exp_pos ((σ + 2) * u)]
  have h2 : |32 * (σ + 3) ^ 2 * Real.exp ((σ + 3) * u)| ≤ 800 * Real.exp ((9 / 4 : ℝ) * u) := by
    rw [abs_of_nonneg (by positivity)]
    have hsq : (σ + 3) ^ 2 ≤ 25 := by nlinarith only [hσ₁, hσ₂]
    nlinarith only [hsq, he3, Real.exp_pos ((σ + 3) * u)]
  have h3 : |16 * (σ + 4) ^ 2 * Real.exp ((σ + 4) * u)| ≤ 576 * Real.exp ((9 / 4 : ℝ) * u) := by
    rw [abs_of_nonneg (by positivity)]
    have hsq : (σ + 4) ^ 2 ≤ 36 := by nlinarith only [hσ₁, hσ₂]
    nlinarith only [hsq, he4, Real.exp_pos ((σ + 4) * u)]
  have htri := abs_add_le (16 * (σ + 2) ^ 2 * Real.exp ((σ + 2) * u) -
      32 * (σ + 3) ^ 2 * Real.exp ((σ + 3) * u)) (16 * (σ + 4) ^ 2 * Real.exp ((σ + 4) * u))
  have htri2 := abs_sub (16 * (σ + 2) ^ 2 * Real.exp ((σ + 2) * u))
      (32 * (σ + 3) ^ 2 * Real.exp ((σ + 3) * u))
  linarith only [htri, htri2, h1, h2, h3]

lemma integrableOn_quarticLogIntegrand (lam σ γ : ℝ) (hσ : (1 : ℝ) / 4 ≤ σ) :
    IntegrableOn
      (fun u : ℝ => (quarticAmp σ u : ℂ) * Complex.exp ((quarticPhase lam γ u : ℂ) * Complex.I))
      (Iic 0) := by
  have hcont : Continuous
      (fun u : ℝ => (quarticAmp σ u : ℂ) * Complex.exp ((quarticPhase lam γ u : ℂ) * Complex.I)) := by
    unfold quarticAmp quarticPhase
    fun_prop
  have hexp_int : IntegrableOn (fun u : ℝ => 16 * Real.exp ((9 / 4 : ℝ) * u)) (Iic 0) := by
    have h := (integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 9 / 4) 0).const_mul 16
    exact h
  refine hexp_int.mono' hcont.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one]
  exact abs_quarticAmp_le hσ hu

/-- Log-coordinate representation of `quarticKernel lam (σ + iγ)`. -/
theorem quarticKernel_eq_integral_Iic (lam σ γ : ℝ) (hσ : (1 : ℝ) / 4 ≤ σ) :
    quarticKernel lam (σ + γ * Complex.I) =
      ∫ u in Iic (0 : ℝ),
        (quarticAmp σ u : ℂ) * Complex.exp ((quarticPhase lam γ u : ℂ) * Complex.I) := by
  unfold quarticKernel mellin
  have hzero : ∀ x ∈ Ici (1 : ℝ),
      (x : ℂ) ^ ((σ + γ * Complex.I) - 1) • quarticTilted lam x = 0 := by
    intro x hx
    unfold quarticTilted
    rw [quarticBump_eq_zero_of_not_mem (by intro h; linarith [Set.mem_Ici.mp hx]),
        Complex.ofReal_zero, zero_mul, smul_zero]
  have hsplit : Ioi (0 : ℝ) = Ioo (0 : ℝ) 1 ∪ Ici (1 : ℝ) :=
    (Set.Ioo_union_Ici_eq_Ioi zero_lt_one).symm
  have hdisj : Disjoint (Ioo (0 : ℝ) 1) (Ici (1 : ℝ)) :=
    Set.disjoint_left.mpr fun x h1 h2 => not_lt_of_ge h2 h1.2
  have hmc := mellinConvergent_quarticTilted (lam := lam) (s := σ + γ * Complex.I) (by simp; linarith)
  have hint1 : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ ((σ + γ * Complex.I) - 1) • quarticTilted lam x) (Ioo 0 1) :=
    hmc.mono_set Set.Ioo_subset_Ioi_self
  have hint2 : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ ((σ + γ * Complex.I) - 1) • quarticTilted lam x) (Ici 1) :=
    (integrableOn_zero (s := Ici 1)).congr_fun (fun x hx => (hzero x hx).symm) measurableSet_Ici
  rw [hsplit, setIntegral_union hdisj measurableSet_Ici hint1 hint2,
      setIntegral_eq_zero_of_forall_eq_zero hzero, add_zero]
  -- Change of variables `x = Real.exp u` mapping `Iio 0` bijectively onto `Ioo 0 1`.
  have himg : Real.exp '' Iio (0 : ℝ) = Ioo 0 1 := by
    ext x
    simp only [Set.mem_image, Set.mem_Iio, Set.mem_Ioo]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨Real.exp_pos u, Real.exp_lt_one_iff.mpr hu⟩
    · rintro ⟨hx0, hx1⟩
      exact ⟨Real.log x, Real.log_neg hx0 hx1, Real.exp_log hx0⟩
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Iio
      (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn,
      integral_Iic_eq_integral_Iio]
  refine setIntegral_congr_fun measurableSet_Iio fun u hu => ?_
  have hu0 : u < 0 := hu
  have hexp_pos : 0 < Real.exp u := Real.exp_pos u
  have hexp_lt1 : Real.exp u < 1 := Real.exp_lt_one_iff.mpr hu0
  rw [abs_of_pos hexp_pos, Complex.real_smul, smul_eq_mul]
  unfold quarticTilted e quarticAmp quarticPhase
  rw [quarticBump_of_mem hexp_pos hexp_lt1]
  have hcpow : ((Real.exp u : ℝ) : ℂ) ^ ((σ + γ * Complex.I) - 1) * ((Real.exp u : ℝ) : ℂ) =
      Complex.exp ((σ : ℂ) * (u : ℂ)) * Complex.exp ((γ * u : ℝ) * Complex.I) := by
    have hne : ((Real.exp u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hexp_pos.ne'
    nth_rw 2 [← Complex.cpow_one ((Real.exp u : ℝ) : ℂ)]
    rw [← Complex.cpow_add _ _ hne, sub_add_cancel, Complex.ofReal_exp,
        Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
        Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_nonneg]),
        ← Complex.exp_add]
    congr 1; push_cast; ring
  have hreal_exp : Complex.exp ((σ : ℂ) * (u : ℂ)) * ((Real.exp u : ℝ) : ℂ) ^ 2 =
      ((Real.exp ((σ + 2) * u) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp, Complex.ofReal_exp, sq, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hphase_exp : Complex.exp ((γ * u : ℝ) * Complex.I) *
      Complex.exp (2 * ↑Real.pi * ↑(lam * Real.exp u) * Complex.I) =
      Complex.exp (↑(γ * u + 2 * Real.pi * lam * Real.exp u) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  calc ((Real.exp u : ℝ) : ℂ) * (((Real.exp u : ℝ) : ℂ) ^ (↑σ + ↑γ * Complex.I - 1) *
        (((16 * Real.exp u ^ 2 * (1 - Real.exp u) ^ 2 : ℝ) : ℂ) *
          Complex.exp (2 * ↑Real.pi * ↑(lam * Real.exp u) * Complex.I)))
      = (((Real.exp u : ℝ) : ℂ) ^ (↑σ + ↑γ * Complex.I - 1) * ((Real.exp u : ℝ) : ℂ)) *
        ((16 : ℂ) * ((Real.exp u : ℝ) : ℂ) ^ 2 * ((1 - Real.exp u : ℝ) : ℂ) ^ 2 *
          Complex.exp (2 * ↑Real.pi * ↑(lam * Real.exp u) * Complex.I)) := by push_cast; ring
    _ = (Complex.exp ((σ : ℂ) * (u : ℂ)) * ((Real.exp u : ℝ) : ℂ) ^ 2) *
        ((16 : ℂ) * ((1 - Real.exp u : ℝ) : ℂ) ^ 2) *
        (Complex.exp ((γ * u : ℝ) * Complex.I) *
          Complex.exp (2 * ↑Real.pi * ↑(lam * Real.exp u) * Complex.I)) := by rw [hcpow]; ring
    _ = (((16 * Real.exp ((σ + 2) * u) * (1 - Real.exp u) ^ 2 : ℝ) : ℂ)) *
        Complex.exp (↑(γ * u + 2 * Real.pi * lam * Real.exp u) * Complex.I) := by
        rw [hreal_exp, hphase_exp]; push_cast; ring

end LogVariableRepresentation

section VanDerCorput

/-- First-derivative oscillatory-integral bound on `[p, q]` when `φ'` is monotone (`φ'' ≥ 0`)
and stays bounded away from `0` by `δ > 0` with constant sign. -/
private lemma osc_first_deriv_bound {p q δ A : ℝ} (hpq : p ≤ q) (hδ : 0 < δ) (hA : 0 ≤ A)
    {a a' φ φ' φ'' : ℝ → ℝ}
    (ha : ∀ u ∈ Icc p q, HasDerivAt a (a' u) u)
    (ha_le : ∀ u ∈ Icc p q, |a u| ≤ A)
    (ha'_cont : ContinuousOn a' (Icc p q))
    (hφ : ∀ u ∈ Icc p q, HasDerivAt φ (φ' u) u)
    (hφ' : ∀ u ∈ Icc p q, HasDerivAt φ' (φ'' u) u)
    (hφ''_cont : ContinuousOn φ'' (Icc p q))
    (hφ''_nn : ∀ u ∈ Icc p q, 0 ≤ φ'' u)
    (hsign : (∀ u ∈ Icc p q, δ ≤ φ' u) ∨ (∀ u ∈ Icc p q, φ' u ≤ -δ)) :
    ‖∫ u in p..q, (a u : ℂ) * Complex.exp ((φ u : ℂ) * Complex.I)‖ ≤
      (3 * A + ∫ u in p..q, |a' u|) / δ := by
  have hIcc : uIcc p q = Icc p q := Set.uIcc_of_le hpq
  have hφ'_ne : ∀ u ∈ Icc p q, φ' u ≠ 0 := by
    intro u hu
    rcases hsign with hpos | hneg
    · linarith [hpos u hu]
    · linarith [hneg u hu]
  have hφ'_abs : ∀ u ∈ Icc p q, δ ≤ |φ' u| := by
    intro u hu
    rcases hsign with hpos | hneg
    · rw [abs_of_pos (lt_of_lt_of_le hδ (hpos u hu))]; exact hpos u hu
    · rw [abs_of_neg (by linarith [hneg u hu])]; linarith [hneg u hu]
  have ha_cont : ContinuousOn a (Icc p q) := fun u hu => (ha u hu).continuousAt.continuousWithinAt
  have hφ_cont : ContinuousOn φ (Icc p q) := fun u hu => (hφ u hu).continuousAt.continuousWithinAt
  have hφ'_cont : ContinuousOn φ' (Icc p q) := fun u hu => (hφ' u hu).continuousAt.continuousWithinAt
  -- Integration by parts: `u_f = a / (i φ')`, `v_f = exp (i φ)`, `u_f * v_f' = a * exp (i φ)`.
  let u_f : ℝ → ℂ := fun u => (a u : ℂ) / (Complex.I * (φ' u : ℂ))
  let u_f' : ℝ → ℂ := fun u =>
    ((a' u : ℂ) / (Complex.I * (φ' u : ℂ))) -
      ((a u : ℂ) * (φ'' u : ℂ)) / (Complex.I * ((φ' u : ℂ) ^ 2))
  let v_f : ℝ → ℂ := fun u => Complex.exp ((φ u : ℂ) * Complex.I)
  let v_f' : ℝ → ℂ := fun u => Complex.I * (φ' u : ℂ) * Complex.exp ((φ u : ℂ) * Complex.I)
  have hu_deriv : ∀ u ∈ uIcc p q, HasDerivAt u_f (u_f' u) u := by
    intro u hu
    rw [hIcc] at hu
    have hneC : (φ' u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hφ'_ne u hu)
    have hIφ_ne : Complex.I * (φ' u : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero hneC
    have h1 : HasDerivAt (fun x => (a x : ℂ)) (a' u : ℂ) u := (ha u hu).ofReal_comp
    have h2 : HasDerivAt (fun x => Complex.I * (φ' x : ℂ)) (Complex.I * (φ'' u : ℂ)) u :=
      ((hφ' u hu).ofReal_comp).const_mul Complex.I
    convert h1.div h2 hIφ_ne using 1
    dsimp [u_f']
    field_simp [Complex.I_ne_zero, hneC]
  have hv_deriv : ∀ u ∈ uIcc p q, HasDerivAt v_f (v_f' u) u := by
    intro u hu
    rw [hIcc] at hu
    have h1 : HasDerivAt (fun x => (φ x : ℂ) * Complex.I) ((φ' u : ℂ) * Complex.I) u :=
      ((hφ u hu).ofReal_comp).mul_const Complex.I
    convert h1.cexp using 1
    dsimp [v_f']; ring
  have hu'_int : IntervalIntegrable u_f' volume p q := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [hIcc]
    have hne : ∀ u ∈ Icc p q, Complex.I * (φ' u : ℂ) ≠ 0 :=
      fun u hu => mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (hφ'_ne u hu))
    have hne2 : ∀ u ∈ Icc p q, Complex.I * (φ' u : ℂ) ^ 2 ≠ 0 :=
      fun u hu => mul_ne_zero Complex.I_ne_zero (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (hφ'_ne u hu)))
    exact ((Complex.continuous_ofReal.comp_continuousOn ha'_cont).div
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hφ'_cont)) hne).sub
      (((Complex.continuous_ofReal.comp_continuousOn ha_cont).mul
        (Complex.continuous_ofReal.comp_continuousOn hφ''_cont)).div
        (continuousOn_const.mul ((Complex.continuous_ofReal.comp_continuousOn hφ'_cont).pow 2)) hne2)
  have hv'_int : IntervalIntegrable v_f' volume p q := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [hIcc]
    exact ((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hφ'_cont)).mul
      (Complex.continuous_exp.comp_continuousOn
        ((Complex.continuous_ofReal.comp_continuousOn hφ_cont).mul continuousOn_const)))
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu_deriv hv_deriv hu'_int hv'_int
  have hlhs : (∫ u in p..q, (a u : ℂ) * Complex.exp ((φ u : ℂ) * Complex.I)) =
      ∫ u in p..q, u_f u * v_f' u := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [hIcc] at hu
    have hneC : (φ' u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hφ'_ne u hu)
    dsimp [u_f, v_f']
    field_simp [Complex.I_ne_zero, hneC]
  rw [hlhs, hibp]
  -- Bound boundary terms.
  have hbd : ∀ u ∈ Icc p q, ‖u_f u * v_f u‖ ≤ A / δ := by
    intro u hu
    dsimp [u_f, v_f]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_div, norm_mul, Complex.norm_I,
        one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    exact div_le_div₀ hA (ha_le u hu) hδ (hφ'_abs u hu)
  have hbd_p := hbd p ⟨le_rfl, hpq⟩
  have hbd_q := hbd q ⟨hpq, le_rfl⟩
  -- Bound the remaining integral term.
  have hint_pt : ∀ u ∈ Icc p q, ‖u_f' u * v_f u‖ ≤ |a' u| / δ + A * (φ'' u / (φ' u) ^ 2) := by
    intro u hu
    dsimp [u_f', v_f]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    have h1 : ‖(a' u : ℂ) / (Complex.I * (φ' u : ℂ))‖ ≤ |a' u| / δ := by
      rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
      exact div_le_div₀ (abs_nonneg _) le_rfl hδ (hφ'_abs u hu)
    have h2 : ‖(a u : ℂ) * (φ'' u : ℂ) / (Complex.I * (φ' u : ℂ) ^ 2)‖ ≤ A * (φ'' u / (φ' u) ^ 2) := by
      rw [norm_div, norm_mul, norm_mul, Complex.norm_I, one_mul, norm_pow,
          Complex.norm_real, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
          abs_of_nonneg (hφ''_nn u hu), mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (ha_le u hu) (div_nonneg (hφ''_nn u hu) (sq_nonneg _))
    exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  -- Evaluate `∫_p^q φ'' / (φ')² = 1 / φ'(p) - 1 / φ'(q) ≤ 1 / δ`.
  have hftc : (∫ u in p..q, φ'' u / (φ' u) ^ 2) ≤ 1 / δ := by
    have hder : ∀ u ∈ uIcc p q, HasDerivAt (fun x => -(1 / φ' x)) (φ'' u / (φ' u) ^ 2) u := by
      intro u hu
      rw [hIcc] at hu
      have hne := hφ'_ne u hu
      have h1 : HasDerivAt (fun x => (φ' x)⁻¹) (-(φ'' u) / (φ' u) ^ 2) u := (hφ' u hu).inv hne
      convert h1.neg using 1
      · funext x; simp [one_div]
      · ring
    have hcont : ContinuousOn (fun u => φ'' u / (φ' u) ^ 2) (Icc p q) :=
      hφ''_cont.div (hφ'_cont.pow 2) (fun u hu => pow_ne_zero 2 (hφ'_ne u hu))
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder (by rw [← hIcc] at hcont; exact hcont.intervalIntegrable)]
    rcases hsign with hpos | hneg
    · have hp_ge : δ ≤ φ' p := hpos p ⟨le_rfl, hpq⟩
      have hq_ge : δ ≤ φ' q := hpos q ⟨hpq, le_rfl⟩
      have h1 : 1 / φ' p ≤ 1 / δ := one_div_le_one_div_of_le hδ hp_ge
      have h2 : 0 ≤ 1 / φ' q := div_nonneg zero_le_one (lt_of_lt_of_le hδ hq_ge).le
      linarith only [h1, h2]
    · have hp_le : φ' p ≤ -δ := hneg p ⟨le_rfl, hpq⟩
      have hq_le : φ' q ≤ -δ := hneg q ⟨hpq, le_rfl⟩
      have h1 : -(1 / φ' q) ≤ 1 / δ := by
        have hposq : δ ≤ -φ' q := by linarith only [hq_le]
        have hinv := one_div_le_one_div_of_le hδ hposq
        rw [div_neg] at hinv
        exact hinv
      have h2 : 1 / φ' p ≤ 0 := div_nonpos_of_nonneg_of_nonpos zero_le_one (by linarith only [hδ, hp_le])
      linarith only [h1, h2]
  have hint_norm : ‖∫ u in p..q, u_f' u * v_f u‖ ≤ (A + ∫ u in p..q, |a' u|) / δ := by
    have h1 : IntervalIntegrable (fun u => |a' u| / δ) volume p q :=
      (ContinuousOn.div_const (continuous_abs.comp_continuousOn ha'_cont) δ).intervalIntegrable_of_Icc hpq
    have h2 : IntervalIntegrable (fun u => A * (φ'' u / (φ' u) ^ 2)) volume p q :=
      (ContinuousOn.mul continuousOn_const
        (hφ''_cont.div (hφ'_cont.pow 2) (fun u hu => pow_ne_zero 2 (hφ'_ne u hu)))).intervalIntegrable_of_Icc hpq
    have hle := intervalIntegral.norm_integral_le_of_norm_le hpq
      (Eventually.of_forall fun u hu => hint_pt u ⟨hu.1.le, hu.2⟩) (h1.add h2)
    rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_div, intervalIntegral.integral_const_mul] at hle
    have hmul := mul_le_mul_of_nonneg_left hftc hA
    calc ‖∫ u in p..q, u_f' u * v_f u‖
        ≤ (∫ u in p..q, |a' u|) / δ + A * (∫ u in p..q, φ'' u / (φ' u) ^ 2) := hle
      _ ≤ (∫ u in p..q, |a' u|) / δ + A * (1 / δ) := add_le_add le_rfl hmul
      _ = (A + ∫ u in p..q, |a' u|) / δ := by ring
  calc ‖u_f q * v_f q - u_f p * v_f p - ∫ u in p..q, u_f' u * v_f u‖
      ≤ ‖u_f q * v_f q - u_f p * v_f p‖ + ‖∫ u in p..q, u_f' u * v_f u‖ := norm_sub_le _ _
    _ ≤ (‖u_f q * v_f q‖ + ‖u_f p * v_f p‖) + ‖∫ u in p..q, u_f' u * v_f u‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ (A / δ + A / δ) + (A + ∫ u in p..q, |a' u|) / δ :=
        add_le_add (add_le_add hbd_q hbd_p) hint_norm
    _ = (3 * A + ∫ u in p..q, |a' u|) / δ := by ring

/-- Second-derivative van der Corput lemma when `φ'' ≥ m > 0` on `[p, q]`. -/
private lemma van_der_corput_pos {p q m A V : ℝ} (hpq : p ≤ q) (hm : 0 < m) (hA : 0 ≤ A)
    {a a' φ φ' φ'' : ℝ → ℝ}
    (ha : ∀ u ∈ Icc p q, HasDerivAt a (a' u) u)
    (ha_le : ∀ u ∈ Icc p q, |a u| ≤ A)
    (ha'_cont : ContinuousOn a' (Icc p q))
    (hV : (∫ u in p..q, |a' u|) ≤ V)
    (hφ : ∀ u ∈ Icc p q, HasDerivAt φ (φ' u) u)
    (hφ' : ∀ u ∈ Icc p q, HasDerivAt φ' (φ'' u) u)
    (hφ''_cont : ContinuousOn φ'' (Icc p q))
    (hφ''_ge : ∀ u ∈ Icc p q, m ≤ φ'' u) :
    ‖∫ u in p..q, (a u : ℂ) * Complex.exp ((φ u : ℂ) * Complex.I)‖ ≤
      (8 * A + V) / Real.sqrt m := by
  set δ := Real.sqrt m
  have hδ : 0 < δ := Real.sqrt_pos.mpr hm
  have hφ'_cont : ContinuousOn φ' (Icc p q) := fun u hu => (hφ' u hu).continuousAt.continuousWithinAt
  have ha_cont : ContinuousOn a (Icc p q) := fun u hu => (ha u hu).continuousAt.continuousWithinAt
  have hφ_cont : ContinuousOn φ (Icc p q) := fun u hu => (hφ u hu).continuousAt.continuousWithinAt
  -- Slope lower bound `m * (v - u) ≤ φ' v - φ' u` for `p ≤ u ≤ v ≤ q`.
  have hslope : ∀ u v, p ≤ u → u ≤ v → v ≤ q → m * (v - u) ≤ φ' v - φ' u := by
    intro u v hpu huv hvq
    have hsub : Icc u v ⊆ Icc p q := Set.Icc_subset_Icc hpu hvq
    have hint1 : IntervalIntegrable (fun _ : ℝ => m) volume u v := intervalIntegrable_const
    have hint2 : IntervalIntegrable φ'' volume u v := (hφ''_cont.mono hsub).intervalIntegrable_of_Icc huv
    have hmono := intervalIntegral.integral_mono_on huv hint1 hint2 (fun x hx => hφ''_ge x (hsub hx))
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm,
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x hx => hφ' x (hsub (by rwa [Set.uIcc_of_le huv] at hx))) hint2] at hmono
    exact hmono
  have hmono_φ' : ∀ u v, p ≤ u → u ≤ v → v ≤ q → φ' u ≤ φ' v := fun u v hpu huv hvq => by
    have := hslope u v hpu huv hvq
    nlinarith only [hm, huv, this]
  -- Existence of clamped cutpoint for any target `y : ℝ`.
  have hex_cut : ∀ y : ℝ, ∃ c ∈ Icc p q,
      (p < c → ∀ u ∈ Icc p c, φ' u ≤ y) ∧
      (c < q → ∀ u ∈ Icc c q, y ≤ φ' u) ∧
      (p < c → φ' c ≤ y) ∧
      (c < q → y ≤ φ' c) := by
    intro y
    by_cases h1 : y ≤ φ' p
    · exact ⟨p, ⟨le_rfl, hpq⟩, fun h => (lt_irrefl _ h).elim,
        fun _ u hu => h1.trans (hmono_φ' p u le_rfl hu.1 hu.2),
        fun h => (lt_irrefl _ h).elim, fun _ => h1⟩
    · by_cases h2 : φ' q ≤ y
      · exact ⟨q, ⟨hpq, le_rfl⟩,
          fun _ u hu => (hmono_φ' u q hu.1 hu.2 le_rfl).trans h2,
          fun h => (lt_irrefl _ h).elim,
          fun _ => h2, fun h => (lt_irrefl _ h).elim⟩
      · have hy : y ∈ Icc (φ' p) (φ' q) := ⟨(not_le.mp h1).le, (not_le.mp h2).le⟩
        obtain ⟨c, hc, hcy⟩ := intermediate_value_Icc hpq hφ'_cont hy
        exact ⟨c, hc,
          fun _ u hu => (hmono_φ' u c hu.1 hu.2 hc.2).trans hcy.le,
          fun _ u hu => hcy.symm.le.trans (hmono_φ' c u hc.1 hu.1 hu.2),
          fun _ => hcy.le, fun _ => hcy.symm.le⟩
  obtain ⟨c₁, hc₁, hc₁_left, _, hc₁_le, hc₁_ge⟩ := hex_cut (-δ)
  obtain ⟨c₂, hc₂, _, hc₂_right, hc₂_le, hc₂_ge⟩ := hex_cut δ
  have hc12 : c₁ ≤ c₂ := by
    by_contra hlt
    push Not at hlt
    have h1 : φ' c₁ ≤ -δ := hc₁_le (lt_of_le_of_lt hc₂.1 hlt)
    have h2 : δ ≤ φ' c₂ := hc₂_ge (lt_of_lt_of_le hlt hc₁.2)
    have h3 : φ' c₂ ≤ φ' c₁ := hmono_φ' c₂ c₁ hc₂.1 hlt.le hc₁.2
    linarith only [hδ, h1, h2, h3]
  -- Split the integral into `[p, c₁]`, `[c₁, c₂]`, `[c₂, q]`.
  let F : ℝ → ℂ := fun u => (a u : ℂ) * Complex.exp ((φ u : ℂ) * Complex.I)
  have hF_cont : ContinuousOn F (Icc p q) :=
    (Complex.continuous_ofReal.comp_continuousOn ha_cont).mul
      (Complex.continuous_exp.comp_continuousOn
        ((Complex.continuous_ofReal.comp_continuousOn hφ_cont).mul continuousOn_const))
  have hF_int : ∀ x y, p ≤ x → x ≤ y → y ≤ q → IntervalIntegrable F volume x y :=
    fun x y hpx hxy hyq => (hF_cont.mono (Set.Icc_subset_Icc hpx hyq)).intervalIntegrable_of_Icc hxy
  have hsplit : (∫ u in p..q, F u) = (∫ u in p..c₁, F u) + (∫ u in c₁..c₂, F u) + (∫ u in c₂..q, F u) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hF_int p c₁ le_rfl hc₁.1 hc₁.2)
          (hF_int c₁ c₂ hc₁.1 hc12 hc₂.2),
        intervalIntegral.integral_add_adjacent_intervals (hF_int p c₂ le_rfl (hc₁.1.trans hc12) hc₂.2)
          (hF_int c₂ q hc₂.1 hc₂.2 le_rfl)]
  -- Bound the middle segment `[c₁, c₂]`.
  have hmid : ‖∫ u in c₁..c₂, F u‖ ≤ 2 * A / δ := by
    by_cases heq : c₁ = c₂
    · subst heq; simp; positivity
    · have hlt : c₁ < c₂ := lt_of_le_of_ne hc12 heq
      have h1 : -δ ≤ φ' c₁ := hc₁_ge (lt_of_lt_of_le hlt hc₂.2)
      have h2 : φ' c₂ ≤ δ := hc₂_le (lt_of_le_of_lt hc₁.1 hlt)
      have hsl := hslope c₁ c₂ hc₁.1 hc12 hc₂.2
      have hlen : c₂ - c₁ ≤ 2 / δ := by
        have hmul : m * (c₂ - c₁) ≤ 2 * δ := by linarith only [h1, h2, hsl]
        have hsq : δ * δ = m := Real.mul_self_sqrt hm.le
        rw [← hsq] at hmul
        rw [le_div_iff₀ hδ]
        nlinarith only [hδ, hmul]
      have hnorm : ‖∫ u in c₁..c₂, F u‖ ≤ A * (c₂ - c₁) := by
        have hpt : ∀ u ∈ Ioc c₁ c₂, ‖F u‖ ≤ A := fun u hu => by
          dsimp [F]
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one]
          exact ha_le u ⟨hc₁.1.trans hu.1.le, hu.2.trans hc₂.2⟩
        have hle := intervalIntegral.norm_integral_le_of_norm_le_const (C := A) (by
          intro u hu; rw [Set.uIoc_of_le hc12] at hu; exact hpt u hu)
        rwa [abs_of_nonneg (sub_nonneg.mpr hc12)] at hle
      calc ‖∫ u in c₁..c₂, F u‖ ≤ A * (c₂ - c₁) := hnorm
        _ ≤ A * (2 / δ) := mul_le_mul_of_nonneg_left hlen hA
        _ = 2 * A / δ := by ring
  -- Bound the left wing `[p, c₁]`.
  have hleft : ‖∫ u in p..c₁, F u‖ ≤ (3 * A + ∫ u in p..c₁, |a' u|) / δ := by
    by_cases heq : p = c₁
    · subst heq; simp; positivity
    · have hsub : Icc p c₁ ⊆ Icc p q := Set.Icc_subset_Icc le_rfl hc₁.2
      exact osc_first_deriv_bound hc₁.1 hδ hA
        (fun u hu => ha u (hsub hu)) (fun u hu => ha_le u (hsub hu)) (ha'_cont.mono hsub)
        (fun u hu => hφ u (hsub hu)) (fun u hu => hφ' u (hsub hu)) (hφ''_cont.mono hsub)
        (fun u hu => hm.le.trans (hφ''_ge u (hsub hu)))
        (Or.inr (hc₁_left (lt_of_le_of_ne hc₁.1 heq)))
  -- Bound the right wing `[c₂, q]`.
  have hright : ‖∫ u in c₂..q, F u‖ ≤ (3 * A + ∫ u in c₂..q, |a' u|) / δ := by
    by_cases heq : c₂ = q
    · subst heq; simp; positivity
    · have hsub : Icc c₂ q ⊆ Icc p q := Set.Icc_subset_Icc hc₂.1 le_rfl
      exact osc_first_deriv_bound hc₂.2 hδ hA
        (fun u hu => ha u (hsub hu)) (fun u hu => ha_le u (hsub hu)) (ha'_cont.mono hsub)
        (fun u hu => hφ u (hsub hu)) (fun u hu => hφ' u (hsub hu)) (hφ''_cont.mono hsub)
        (fun u hu => hm.le.trans (hφ''_ge u (hsub hu)))
        (Or.inl (hc₂_right (lt_of_le_of_ne hc₂.2 heq)))
  -- Combine `∫_p^{c₁} |a'| + ∫_{c₂}^q |a'| ≤ ∫_p^q |a'| ≤ V`.
  have ha'_abs_int : ∀ x y, p ≤ x → x ≤ y → y ≤ q → IntervalIntegrable (fun u => |a' u|) volume x y :=
    fun x y hpx hxy hyq =>
      (continuous_abs.comp_continuousOn (ha'_cont.mono (Set.Icc_subset_Icc hpx hyq))).intervalIntegrable_of_Icc hxy
  have hV_sum : (∫ u in p..c₁, |a' u|) + (∫ u in c₂..q, |a' u|) ≤ V := by
    have hmid_nn : 0 ≤ ∫ u in c₁..c₂, |a' u| :=
      intervalIntegral.integral_nonneg hc12 (fun _ _ => abs_nonneg _)
    have htot : (∫ u in p..c₁, |a' u|) + (∫ u in c₁..c₂, |a' u|) + (∫ u in c₂..q, |a' u|) =
        ∫ u in p..q, |a' u| := by
      rw [intervalIntegral.integral_add_adjacent_intervals
            (ha'_abs_int p c₁ le_rfl hc₁.1 hc₁.2) (ha'_abs_int c₁ c₂ hc₁.1 hc12 hc₂.2),
          intervalIntegral.integral_add_adjacent_intervals
            (ha'_abs_int p c₂ le_rfl (hc₁.1.trans hc12) hc₂.2) (ha'_abs_int c₂ q hc₂.1 hc₂.2 le_rfl)]
    linarith only [hmid_nn, htot, hV]
  calc ‖∫ u in p..q, F u‖
      = ‖(∫ u in p..c₁, F u) + (∫ u in c₁..c₂, F u) + (∫ u in c₂..q, F u)‖ := by rw [hsplit]
    _ ≤ ‖(∫ u in p..c₁, F u) + (∫ u in c₁..c₂, F u)‖ + ‖∫ u in c₂..q, F u‖ := norm_add_le _ _
    _ ≤ ‖∫ u in p..c₁, F u‖ + ‖∫ u in c₁..c₂, F u‖ + ‖∫ u in c₂..q, F u‖ :=
        add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (3 * A + ∫ u in p..c₁, |a' u|) / δ + 2 * A / δ + (3 * A + ∫ u in c₂..q, |a' u|) / δ :=
        add_le_add (add_le_add hleft hmid) hright
    _ = (8 * A + ((∫ u in p..c₁, |a' u|) + (∫ u in c₂..q, |a' u|))) / δ := by ring
    _ ≤ (8 * A + V) / δ := div_le_div_of_nonneg_right (by linarith only [hV_sum]) hδ.le

/-- Second-derivative van der Corput lemma for single-signed `φ''` (`φ'' ≥ m` or `φ'' ≤ -m`). -/
theorem van_der_corput_second_deriv {p q m A V : ℝ} (hpq : p ≤ q) (hm : 0 < m) (hA : 0 ≤ A)
    {a a' φ φ' φ'' : ℝ → ℝ}
    (ha : ∀ u ∈ Icc p q, HasDerivAt a (a' u) u)
    (ha_le : ∀ u ∈ Icc p q, |a u| ≤ A)
    (ha'_cont : ContinuousOn a' (Icc p q))
    (hV : (∫ u in p..q, |a' u|) ≤ V)
    (hφ : ∀ u ∈ Icc p q, HasDerivAt φ (φ' u) u)
    (hφ' : ∀ u ∈ Icc p q, HasDerivAt φ' (φ'' u) u)
    (hφ''_cont : ContinuousOn φ'' (Icc p q))
    (hφ''_sign : (∀ u ∈ Icc p q, m ≤ φ'' u) ∨ (∀ u ∈ Icc p q, φ'' u ≤ -m)) :
    ‖∫ u in p..q, (a u : ℂ) * Complex.exp ((φ u : ℂ) * Complex.I)‖ ≤
      (8 * A + V) / Real.sqrt m := by
  rcases hφ''_sign with hpos | hneg
  · exact van_der_corput_pos hpq hm hA ha ha_le ha'_cont hV hφ hφ' hφ''_cont hpos
  · -- Conjugate the integral to replace `φ` by `-φ`.
    have hconj_eq :
        starRingEnd ℂ (∫ u in p..q, (a u : ℂ) * Complex.exp ((φ u : ℂ) * Complex.I)) =
          ∫ u in p..q, (a u : ℂ) * Complex.exp (((-φ u : ℝ) : ℂ) * Complex.I) := by
      have ha_cont : ContinuousOn a (Icc p q) := fun u hu => (ha u hu).continuousAt.continuousWithinAt
      have hφ_cont : ContinuousOn φ (Icc p q) := fun u hu => (hφ u hu).continuousAt.continuousWithinAt
      have hint : IntervalIntegrable (fun u => (a u : ℂ) * Complex.exp ((φ u : ℂ) * Complex.I)) volume p q :=
        ((Complex.continuous_ofReal.comp_continuousOn ha_cont).mul
          (Complex.continuous_exp.comp_continuousOn
            ((Complex.continuous_ofReal.comp_continuousOn hφ_cont).mul continuousOn_const))).intervalIntegrable_of_Icc hpq
      have hmap : Complex.conjCLE (∫ u in p..q, (a u : ℂ) * Complex.exp ((φ u : ℂ) * Complex.I)) =
          ∫ u in p..q, Complex.conjCLE ((a u : ℂ) * Complex.exp ((φ u : ℂ) * Complex.I)) :=
        (Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm hint).symm
      change Complex.conjCLE (∫ u in p..q, (a u : ℂ) * Complex.exp ((φ u : ℂ) * Complex.I)) = _
      rw [hmap]
      refine intervalIntegral.integral_congr fun u _ => ?_
      change starRingEnd ℂ ((a u : ℂ) * Complex.exp ((φ u : ℂ) * Complex.I)) = _
      rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
      congr 2; push_cast; ring
    rw [← Complex.norm_conj, hconj_eq]
    exact van_der_corput_pos hpq hm hA ha ha_le ha'_cont hV
      (φ := fun u => -φ u) (φ' := fun u => -φ' u) (φ'' := fun u => -φ'' u)
      (fun u hu => (hφ u hu).neg) (fun u hu => (hφ' u hu).neg) hφ''_cont.neg
      (fun u hu => by linarith [hneg u hu])

end VanDerCorput

section UniformBounds

/-- **A2 Uniform Stationary-Phase Bound**:
For all `1/4 ≤ σ ≤ 2`, `γ ∈ ℝ`, and `lam ∈ ℝ`,
`‖quarticKernel lam (σ + γ * I)‖ ≤ 1792 / √(1 + |lam|)`. -/
theorem quarticKernel_norm_le_inv_sqrt {lam σ γ : ℝ} (hσ₁ : (1 : ℝ) / 4 ≤ σ) (hσ₂ : σ ≤ 2) :
    ‖quarticKernel lam (σ + γ * Complex.I)‖ ≤ 1792 / Real.sqrt (1 + |lam|) := by
  rw [quarticKernel_eq_integral_Iic lam σ γ hσ₁]
  let F : ℝ → ℂ := fun u =>
    (quarticAmp σ u : ℂ) * Complex.exp ((quarticPhase lam γ u : ℂ) * Complex.I)
  have hF_int : IntegrableOn F (Iic 0) := integrableOn_quarticLogIntegrand lam σ γ hσ₁
  by_cases hlam : |lam| ≤ 1
  · -- Small frequency `|lam| ≤ 1`: direct `L¹` bound `≤ 64/9 ≤ 1792 / √2`.
    have hexp_int : IntegrableOn (fun u : ℝ => 16 * Real.exp ((9 / 4 : ℝ) * u)) (Iic 0) :=
      (integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 9 / 4) 0).const_mul 16
    have hnorm : ‖∫ u in Iic (0 : ℝ), F u‖ ≤ ∫ u in Iic (0 : ℝ), 16 * Real.exp ((9 / 4 : ℝ) * u) := by
      calc ‖∫ u in Iic (0 : ℝ), F u‖
          ≤ ∫ u in Iic (0 : ℝ), ‖F u‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ u in Iic (0 : ℝ), 16 * Real.exp ((9 / 4 : ℝ) * u) := by
            refine setIntegral_mono_on hF_int.norm hexp_int measurableSet_Iic fun u hu => ?_
            dsimp [F]
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one]
            exact abs_quarticAmp_le hσ₁ hu
    have heval : (∫ u in Iic (0 : ℝ), 16 * Real.exp ((9 / 4 : ℝ) * u)) = 64 / 9 := by
      rw [integral_const_mul, integral_exp_mul_Iic (by norm_num : (0 : ℝ) < 9 / 4) 0]
      norm_num
    have hsqrt_le : Real.sqrt (1 + |lam|) ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      linarith only [hlam]
    have hdiv_ge : (64 : ℝ) / 9 ≤ 1792 / Real.sqrt (1 + |lam|) := by
      have hpos : 0 < Real.sqrt (1 + |lam|) := Real.sqrt_pos.mpr (by positivity)
      rw [le_div_iff₀ hpos]
      nlinarith only [hsqrt_le, hpos]
    exact hnorm.trans (heval.le.trans hdiv_ge)
  · -- Large frequency `|lam| > 1`: dyadic decomposition in `u = log x ≤ 0` + van der Corput.
    push Not at hlam
    have hlam_pos : 0 < |lam| := lt_trans zero_lt_one hlam
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2_le1 : Real.log 2 ≤ 1 := by
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      simpa using Real.log_le_log two_pos h2
    -- Dyadic block bound on `I_j = [-(j+1) log 2, -j log 2]`.
    have hblock : ∀ j : ℕ,
        ‖∫ u in (-((j + 1 : ℕ) : ℝ) * Real.log 2)..(-((j : ℕ) : ℝ) * Real.log 2), F u‖ ≤
          (448 / Real.sqrt |lam|) * ((1 / 2 : ℝ) ^ j) := by
      intro j
      set p := -((j + 1 : ℕ) : ℝ) * Real.log 2
      set q := -((j : ℕ) : ℝ) * Real.log 2
      have hpq : p ≤ q := by
        dsimp [p, q]; push_cast; nlinarith only [hlog2_pos]
      have hq0 : q ≤ 0 := by
        dsimp [q]; exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg j)) hlog2_pos.le
      have hexp_hi : ∀ u ∈ Icc p q, Real.exp u ≤ (1 / 2 : ℝ) ^ j := by
        intro u hu
        calc Real.exp u ≤ Real.exp q := Real.exp_le_exp.mpr hu.2
          _ = Real.exp ((j : ℕ) * (-Real.log 2)) := by dsimp [q]; congr 1; ring
          _ = (Real.exp (-Real.log 2)) ^ j := Real.exp_nat_mul (-Real.log 2) j
          _ = (1 / 2 : ℝ) ^ j := by rw [Real.exp_neg, Real.exp_log two_pos, one_div]
      have hexp_lo : ∀ u ∈ Icc p q, (1 / 2 : ℝ) ^ (j + 1) ≤ Real.exp u := by
        intro u hu
        calc (1 / 2 : ℝ) ^ (j + 1)
            = (Real.exp (-Real.log 2)) ^ (j + 1) := by rw [Real.exp_neg, Real.exp_log two_pos, one_div]
          _ = Real.exp (((j + 1 : ℕ) : ℝ) * (-Real.log 2)) := (Real.exp_nat_mul (-Real.log 2) (j + 1)).symm
          _ = Real.exp p := by dsimp [p]; congr 1; ring
          _ ≤ Real.exp u := Real.exp_le_exp.mpr hu.1
      have hexp94 : ∀ u ∈ Icc p q, Real.exp ((9 / 4 : ℝ) * u) ≤ ((1 / 2 : ℝ) ^ j) ^ 2 := by
        intro u hu
        have hu0 : u ≤ 0 := hu.2.trans hq0
        calc Real.exp ((9 / 4 : ℝ) * u)
            ≤ Real.exp (2 * u) := Real.exp_le_exp.mpr (by linarith only [hu0])
          _ = Real.exp u ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
          _ ≤ ((1 / 2 : ℝ) ^ j) ^ 2 := pow_le_pow_left₀ (Real.exp_pos u).le (hexp_hi u hu) 2
      set A_j : ℝ := 16 * ((1 / 2 : ℝ) ^ j) ^ 2
      set V_j : ℝ := 320 * ((1 / 2 : ℝ) ^ j) ^ 2
      set m_j : ℝ := |lam| * (1 / 2 : ℝ) ^ j
      have hm_pos : 0 < m_j := by positivity
      have ha_le : ∀ u ∈ Icc p q, |quarticAmp σ u| ≤ A_j := fun u hu =>
        (abs_quarticAmp_le hσ₁ (hu.2.trans hq0)).trans (mul_le_mul_of_nonneg_left (hexp94 u hu) (by norm_num))
      have hV_le : (∫ u in p..q, |quarticAmp' σ u|) ≤ V_j := by
        have hlen : q - p = Real.log 2 := by dsimp [p, q]; push_cast; ring
        have hpt : ∀ u ∈ uIoc p q, ‖|quarticAmp' σ u|‖ ≤ V_j := fun u hu => by
          rw [Set.uIoc_of_le hpq] at hu
          rw [Real.norm_eq_abs, abs_abs]
          exact (abs_quarticAmp'_le hσ₁ hσ₂ (hu.2.trans hq0)).trans
            (mul_le_mul_of_nonneg_left (hexp94 u ⟨hu.1.le, hu.2⟩) (by norm_num))
        have h1 := intervalIntegral.norm_integral_le_of_norm_le_const hpt
        have hnn : 0 ≤ ∫ u in p..q, |quarticAmp' σ u| :=
          intervalIntegral.integral_nonneg hpq (fun _ _ => abs_nonneg _)
        rw [Real.norm_eq_abs, abs_of_nonneg hnn, hlen, abs_of_pos hlog2_pos] at h1
        calc (∫ u in p..q, |quarticAmp' σ u|) ≤ V_j * Real.log 2 := h1
          _ ≤ V_j * 1 := mul_le_mul_of_nonneg_left hlog2_le1 (by positivity)
          _ = V_j := mul_one _
      have hpi_ge1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
      have hsign : (∀ u ∈ Icc p q, m_j ≤ quarticPhase'' lam u) ∨
          (∀ u ∈ Icc p q, quarticPhase'' lam u ≤ -m_j) := by
        rcases le_or_gt 0 lam with hpos | hneg
        · refine Or.inl fun u hu => ?_
          unfold quarticPhase''
          have h1 : |lam| = lam := abs_of_nonneg hpos
          have h2 := hexp_lo u hu
          rw [pow_succ] at h2
          dsimp [m_j]
          rw [h1]
          have hmul1 : lam * ((1 / 2 : ℝ) ^ j * (1 / 2)) ≤ lam * Real.exp u :=
            mul_le_mul_of_nonneg_left h2 hpos
          have hmul2 : (2 * Real.pi) * (lam * ((1 / 2 : ℝ) ^ j * (1 / 2))) ≤ 2 * Real.pi * (lam * Real.exp u) :=
            mul_le_mul_of_nonneg_left hmul1 (by positivity)
          have hpi_mul : lam * (1 / 2 : ℝ) ^ j ≤ Real.pi * (lam * (1 / 2 : ℝ) ^ j) :=
            le_mul_of_one_le_left (by positivity) hpi_ge1
          linarith only [hmul2, hpi_mul]
        · refine Or.inr fun u hu => ?_
          unfold quarticPhase''
          have h1 : |lam| = -lam := abs_of_neg hneg
          have h2 := hexp_lo u hu
          rw [pow_succ] at h2
          dsimp [m_j]
          rw [h1]
          have hmlam : 0 ≤ -lam := by linarith only [hneg]
          have hmul1 : (-lam) * ((1 / 2 : ℝ) ^ j * (1 / 2)) ≤ (-lam) * Real.exp u :=
            mul_le_mul_of_nonneg_left h2 hmlam
          have hmul2 : (2 * Real.pi) * ((-lam) * ((1 / 2 : ℝ) ^ j * (1 / 2))) ≤
              2 * Real.pi * ((-lam) * Real.exp u) :=
            mul_le_mul_of_nonneg_left hmul1 (by positivity)
          have hpi_mul : (-lam) * (1 / 2 : ℝ) ^ j ≤ Real.pi * ((-lam) * (1 / 2 : ℝ) ^ j) :=
            le_mul_of_one_le_left (mul_nonneg hmlam (by positivity)) hpi_ge1
          linarith only [hmul2, hpi_mul]
      have hvdc := van_der_corput_second_deriv hpq hm_pos (by positivity)
        (fun u _ => hasDerivAt_quarticAmp σ u) ha_le
        (by unfold quarticAmp'; fun_prop) hV_le
        (fun u _ => hasDerivAt_quarticPhase lam γ u)
        (fun u _ => hasDerivAt_quarticPhase' lam γ u)
        (by unfold quarticPhase''; fun_prop) hsign
      have halg : (8 * A_j + V_j) / Real.sqrt m_j ≤ (448 / Real.sqrt |lam|) * (1 / 2 : ℝ) ^ j := by
        dsimp [A_j, V_j, m_j]
        rw [Real.sqrt_mul hlam_pos.le]
        have hsqrt_ge : (1 / 2 : ℝ) ^ j ≤ Real.sqrt ((1 / 2 : ℝ) ^ j) := by
          have hle1 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
          have hnn : 0 ≤ (1 / 2 : ℝ) ^ j := by positivity
          rw [Real.le_sqrt hnn hnn]
          nlinarith only [hle1, hnn]
        have hden : Real.sqrt |lam| * (1 / 2 : ℝ) ^ j ≤ Real.sqrt |lam| * Real.sqrt ((1 / 2 : ℝ) ^ j) :=
          mul_le_mul_of_nonneg_left hsqrt_ge (Real.sqrt_nonneg _)
        have hnum : 8 * (16 * ((1 / 2 : ℝ) ^ j) ^ 2) + 320 * ((1 / 2 : ℝ) ^ j) ^ 2 =
            448 * ((1 / 2 : ℝ) ^ j) ^ 2 := by ring
        rw [hnum]
        have hpos_den : 0 < Real.sqrt |lam| * (1 / 2 : ℝ) ^ j := by positivity
        calc 448 * ((1 / 2 : ℝ) ^ j) ^ 2 / (Real.sqrt |lam| * Real.sqrt ((1 / 2 : ℝ) ^ j))
            ≤ 448 * ((1 / 2 : ℝ) ^ j) ^ 2 / (Real.sqrt |lam| * (1 / 2 : ℝ) ^ j) :=
              div_le_div_of_nonneg_left (by positivity) hpos_den hden
          _ = (448 / Real.sqrt |lam|) * (1 / 2 : ℝ) ^ j := by
              have hne1 : Real.sqrt |lam| ≠ 0 := (Real.sqrt_pos.mpr hlam_pos).ne'
              have hne2 : (1 / 2 : ℝ) ^ j ≠ 0 := by positivity
              field_simp [hne1, hne2]
      exact hvdc.trans halg
    -- Sum over `j ∈ Finset.range N` to bound `∫_{-N log 2}^0 F`.
    have hF_cont : Continuous F := by
      have ha_c : Continuous (quarticAmp σ) := by unfold quarticAmp; fun_prop
      have hφ_c : Continuous (quarticPhase lam γ) := by unfold quarticPhase; fun_prop
      exact (Complex.continuous_ofReal.comp ha_c).mul
        (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp hφ_c).mul continuous_const))
    have hpartial : ∀ N : ℕ,
        ‖∫ u in (-(N : ℝ) * Real.log 2)..(0 : ℝ), F u‖ ≤ 896 / Real.sqrt |lam| := by
      intro N
      have hsum_eq : (∫ u in (-(N : ℝ) * Real.log 2)..(0 : ℝ), F u) =
          ∑ j ∈ Finset.range N,
            ∫ u in (-((j + 1 : ℕ) : ℝ) * Real.log 2)..(-((j : ℕ) : ℝ) * Real.log 2), F u := by
        induction N with
        | zero => simp
        | succ k ih =>
          rw [Finset.sum_range_succ, ← ih]
          have h1 := hF_cont.intervalIntegrable (μ := volume) (-((k + 1 : ℕ) : ℝ) * Real.log 2) (-((k : ℕ) : ℝ) * Real.log 2)
          have h2 := hF_cont.intervalIntegrable (μ := volume) (-((k : ℕ) : ℝ) * Real.log 2) 0
          exact (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm.trans (add_comm _ _)
      rw [hsum_eq]
      have hgeom : (∑ j ∈ Finset.range N, ((1 / 2 : ℝ) ^ j)) ≤ 2 := by
        rw [geom_sum_eq (by norm_num) N]
        have hnn : 0 ≤ (1 / 2 : ℝ) ^ N := by positivity
        have hval : ((1 / 2 : ℝ) ^ N - 1) / (1 / 2 - 1) = 2 * (1 - (1 / 2 : ℝ) ^ N) := by ring
        linarith only [hnn, hval]
      calc ‖∑ j ∈ Finset.range N,
            ∫ u in (-((j + 1 : ℕ) : ℝ) * Real.log 2)..(-((j : ℕ) : ℝ) * Real.log 2), F u‖
          ≤ ∑ j ∈ Finset.range N,
              ‖∫ u in (-((j + 1 : ℕ) : ℝ) * Real.log 2)..(-((j : ℕ) : ℝ) * Real.log 2), F u‖ :=
            norm_sum_le _ _
        _ ≤ ∑ j ∈ Finset.range N, (448 / Real.sqrt |lam|) * ((1 / 2 : ℝ) ^ j) :=
            Finset.sum_le_sum fun j _ => hblock j
        _ = (448 / Real.sqrt |lam|) * ∑ j ∈ Finset.range N, ((1 / 2 : ℝ) ^ j) :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ (448 / Real.sqrt |lam|) * 2 :=
            mul_le_mul_of_nonneg_left hgeom (by positivity)
        _ = 896 / Real.sqrt |lam| := by ring
    -- Pass to the limit `N → ∞`.
    have htend_bot : Tendsto (fun N : ℕ => -(N : ℝ) * Real.log 2) atTop atBot := by
      have h1 : Tendsto (fun N : ℕ => (N : ℝ) * Real.log 2) atTop atTop :=
        Tendsto.atTop_mul_const hlog2_pos tendsto_natCast_atTop_atTop
      exact (tendsto_neg_atTop_atBot.comp h1).congr fun N => by simp [neg_mul]
    have htend := intervalIntegral_tendsto_integral_Iic 0 hF_int htend_bot
    have hlim : ‖∫ u in Iic (0 : ℝ), F u‖ ≤ 896 / Real.sqrt |lam| :=
      le_of_tendsto htend.norm (Eventually.of_forall hpartial)
    have hcmp : 896 / Real.sqrt |lam| ≤ 1792 / Real.sqrt (1 + |lam|) := by
      have h1 : Real.sqrt (1 + |lam|) ≤ 2 * Real.sqrt |lam| := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2), ← Real.sqrt_mul (by positivity)]
        exact Real.sqrt_le_sqrt (by linarith only [hlam])
      have hpos1 : 0 < Real.sqrt |lam| := Real.sqrt_pos.mpr hlam_pos
      have hpos2 : 0 < Real.sqrt (1 + |lam|) := Real.sqrt_pos.mpr (by positivity)
      rw [div_le_div_iff₀ hpos1 hpos2]
      nlinarith only [h1]
    exact hlim.trans hcmp

/-- Pointwise norm bound on the second-IBP integrand `g₂'`. -/
private lemma quarticKernel_tail_g2'_norm {lam σ γ u : ℝ} (hσ₁ : (1 : ℝ) / 4 ≤ σ) (hσ₂ : σ ≤ 2)
    (hγ : 4 * Real.pi * |lam| + 2 ≤ |γ|) (hu : u ≤ 0)
    (hφ'_lo : |γ| / 2 ≤ |quarticPhase' lam γ u|)
    (hφ''_hi : |quarticPhase'' lam u| ≤ |γ| / 2) :
    ‖-((quarticAmp'' σ u : ℂ) / ((quarticPhase' lam γ u : ℂ) ^ 2)) +
      3 * ((quarticAmp' σ u : ℂ) * (quarticPhase'' lam u : ℂ)) / ((quarticPhase' lam γ u : ℂ) ^ 3) +
      ((quarticAmp σ u : ℂ) * (quarticPhase'' lam u : ℂ)) / ((quarticPhase' lam γ u : ℂ) ^ 3) -
      3 * ((quarticAmp σ u : ℂ) * ((quarticPhase'' lam u : ℂ) ^ 2)) / ((quarticPhase' lam γ u : ℂ) ^ 4)‖ ≤
      (10624 / |γ| ^ 2) * Real.exp ((9 / 4 : ℝ) * u) := by
  have hγ_ge2 : 2 ≤ |γ| := by
    have : 0 ≤ 4 * Real.pi * |lam| := by positivity
    linarith only [hγ, this]
  have hγ_pos : 0 < |γ| := lt_of_lt_of_le two_pos hγ_ge2
  have hne : |γ| ≠ 0 := hγ_pos.ne'
  set a := quarticAmp σ u
  set a' := quarticAmp' σ u
  set a'' := quarticAmp'' σ u
  set φ' := quarticPhase' lam γ u
  set φ'' := quarticPhase'' lam u
  have h1 : ‖-((a'' : ℂ) / ((φ' : ℂ) ^ 2))‖ ≤ (6528 / |γ| ^ 2) * Real.exp ((9 / 4 : ℝ) * u) := by
    rw [norm_neg, norm_div, norm_pow, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
    calc |a''| / |φ'| ^ 2
        ≤ (1632 * Real.exp ((9 / 4 : ℝ) * u)) / (|γ| / 2) ^ 2 :=
          div_le_div₀ (by positivity) (abs_quarticAmp''_le hσ₁ hσ₂ hu) (by positivity)
            (pow_le_pow_left₀ (by positivity) hφ'_lo 2)
      _ = (6528 / |γ| ^ 2) * Real.exp ((9 / 4 : ℝ) * u) := by ring
  have h2 : ‖3 * ((a' : ℂ) * (φ'' : ℂ)) / ((φ' : ℂ) ^ 3)‖ ≤
      (3840 / |γ| ^ 2) * Real.exp ((9 / 4 : ℝ) * u) := by
    rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_ofNat,
        Complex.norm_real, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    have hnum : 3 * (|a'| * |φ''|) ≤ 3 * ((320 * Real.exp ((9 / 4 : ℝ) * u)) * (|γ| / 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (abs_quarticAmp'_le hσ₁ hσ₂ hu) hφ''_hi (abs_nonneg _) (by positivity))
        (by norm_num)
    calc 3 * (|a'| * |φ''|) / |φ'| ^ 3
        ≤ (3 * ((320 * Real.exp ((9 / 4 : ℝ) * u)) * (|γ| / 2))) / (|γ| / 2) ^ 3 :=
          div_le_div₀ (by positivity) hnum (by positivity)
            (pow_le_pow_left₀ (by positivity) hφ'_lo 3)
      _ = (3840 / |γ| ^ 2) * Real.exp ((9 / 4 : ℝ) * u) := by field_simp [hne]; ring
  have h3 : ‖((a : ℂ) * (φ'' : ℂ)) / ((φ' : ℂ) ^ 3)‖ ≤
      (64 / |γ| ^ 2) * Real.exp ((9 / 4 : ℝ) * u) := by
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    have hnum : |a| * |φ''| ≤ (16 * Real.exp ((9 / 4 : ℝ) * u)) * (|γ| / 2) :=
      mul_le_mul (abs_quarticAmp_le hσ₁ hu) hφ''_hi (abs_nonneg _) (by positivity)
    calc |a| * |φ''| / |φ'| ^ 3
        ≤ ((16 * Real.exp ((9 / 4 : ℝ) * u)) * (|γ| / 2)) / (|γ| / 2) ^ 3 :=
          div_le_div₀ (by positivity) hnum (by positivity)
            (pow_le_pow_left₀ (by positivity) hφ'_lo 3)
      _ = (64 / |γ| ^ 2) * Real.exp ((9 / 4 : ℝ) * u) := by field_simp [hne]; ring
  have h4 : ‖3 * ((a : ℂ) * ((φ'' : ℂ) ^ 2)) / ((φ' : ℂ) ^ 4)‖ ≤
      (192 / |γ| ^ 2) * Real.exp ((9 / 4 : ℝ) * u) := by
    rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_ofNat,
        Complex.norm_real, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    have hnum : 3 * (|a| * |φ''| ^ 2) ≤ 3 * ((16 * Real.exp ((9 / 4 : ℝ) * u)) * (|γ| / 2) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (abs_quarticAmp_le hσ₁ hu)
          (pow_le_pow_left₀ (abs_nonneg _) hφ''_hi 2) (by positivity) (by positivity))
        (by norm_num)
    calc 3 * (|a| * |φ''| ^ 2) / |φ'| ^ 4
        ≤ (3 * ((16 * Real.exp ((9 / 4 : ℝ) * u)) * (|γ| / 2) ^ 2)) / (|γ| / 2) ^ 4 :=
          div_le_div₀ (by positivity) hnum (by positivity)
            (pow_le_pow_left₀ (by positivity) hφ'_lo 4)
      _ = (192 / |γ| ^ 2) * Real.exp ((9 / 4 : ℝ) * u) := by field_simp [hne]; ring
  have t1 := norm_sub_le
    (-((a'' : ℂ) / ((φ' : ℂ) ^ 2)) + 3 * ((a' : ℂ) * (φ'' : ℂ)) / ((φ' : ℂ) ^ 3) +
      ((a : ℂ) * (φ'' : ℂ)) / ((φ' : ℂ) ^ 3))
    (3 * ((a : ℂ) * ((φ'' : ℂ) ^ 2)) / ((φ' : ℂ) ^ 4))
  have t2 := norm_add_le
    (-((a'' : ℂ) / ((φ' : ℂ) ^ 2)) + 3 * ((a' : ℂ) * (φ'' : ℂ)) / ((φ' : ℂ) ^ 3))
    (((a : ℂ) * (φ'' : ℂ)) / ((φ' : ℂ) ^ 3))
  have t3 := norm_add_le
    (-((a'' : ℂ) / ((φ' : ℂ) ^ 2)))
    (3 * ((a' : ℂ) * (φ'' : ℂ)) / ((φ' : ℂ) ^ 3))
  have hsum : (6528 / |γ| ^ 2) * Real.exp ((9 / 4 : ℝ) * u) +
      (3840 / |γ| ^ 2) * Real.exp ((9 / 4 : ℝ) * u) +
      (64 / |γ| ^ 2) * Real.exp ((9 / 4 : ℝ) * u) +
      (192 / |γ| ^ 2) * Real.exp ((9 / 4 : ℝ) * u) =
      (10624 / |γ| ^ 2) * Real.exp ((9 / 4 : ℝ) * u) := by ring
  linarith only [t1, t2, t3, h1, h2, h3, h4, hsum]

/-- Finite-interval two-IBP bound for the tail estimate on `[-M, 0]`. -/
private lemma quarticKernel_tail_ibp_bound {lam σ γ M : ℝ} (hσ₁ : (1 : ℝ) / 4 ≤ σ) (hσ₂ : σ ≤ 2)
    (hγ : 4 * Real.pi * |lam| + 2 ≤ |γ|) (hM : 0 ≤ M) :
    ‖∫ u in (-M)..(0 : ℝ),
        (quarticAmp σ u : ℂ) * Complex.exp ((quarticPhase lam γ u : ℂ) * Complex.I)‖ ≤
      ((32 / |γ|) + (1344 / |γ| ^ 2)) * Real.exp (-(9 / 4 : ℝ) * M) + (4722 / |γ| ^ 2) := by
  have hγ_ge2 : 2 ≤ |γ| := by
    have : 0 ≤ 4 * Real.pi * |lam| := by positivity
    linarith only [hγ, this]
  have hγ_pos : 0 < |γ| := lt_of_lt_of_le two_pos hγ_ge2
  let a := quarticAmp σ
  let a' := quarticAmp' σ
  let a'' := quarticAmp'' σ
  let φ := quarticPhase lam γ
  let φ' := quarticPhase' lam γ
  let φ'' := quarticPhase'' lam
  have hφ'_lo : ∀ u ≤ 0, |γ| / 2 ≤ |φ' u| := by
    intro u hu
    have hexp_le1 : Real.exp u ≤ 1 := Real.exp_le_one_iff.mpr hu
    have h2 : |2 * Real.pi * lam * Real.exp u| ≤ |γ| / 2 := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos two_pos, abs_of_pos Real.pi_pos,
          abs_of_pos (Real.exp_pos u)]
      have hmul : 2 * Real.pi * |lam| * Real.exp u ≤ 2 * Real.pi * |lam| * 1 :=
        mul_le_mul_of_nonneg_left hexp_le1 (by positivity)
      linarith only [hγ, hmul]
    have htri := abs_sub_abs_le_abs_sub γ (-(2 * Real.pi * lam * Real.exp u))
    rw [sub_neg_eq_add, abs_neg] at htri
    dsimp [φ']; unfold quarticPhase'
    linarith only [htri, h2]
  have hφ'_ne : ∀ u ≤ 0, φ' u ≠ 0 := fun u hu h0 => by
    have := hφ'_lo u hu; rw [h0, abs_zero] at this; linarith only [hγ_pos, this]
  have hφ''_hi : ∀ u ≤ 0, |φ'' u| ≤ |γ| / 2 := by
    intro u hu
    dsimp [φ'']; unfold quarticPhase''
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos two_pos, abs_of_pos Real.pi_pos,
        abs_of_pos (Real.exp_pos u)]
    have hmul : 2 * Real.pi * |lam| * Real.exp u ≤ 2 * Real.pi * |lam| * 1 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr hu) (by positivity)
    linarith only [hγ, hmul]
  let v_f : ℝ → ℂ := fun u => Complex.exp ((φ u : ℂ) * Complex.I)
  let v_f' : ℝ → ℂ := fun u => Complex.I * (φ' u : ℂ) * Complex.exp ((φ u : ℂ) * Complex.I)
  let g₁ : ℝ → ℂ := fun u => (a u : ℂ) / (Complex.I * (φ' u : ℂ))
  let g₁' : ℝ → ℂ := fun u =>
    ((a' u : ℂ) / (Complex.I * (φ' u : ℂ))) -
      ((a u : ℂ) * (φ'' u : ℂ)) / (Complex.I * ((φ' u : ℂ) ^ 2))
  let g₂ : ℝ → ℂ := fun u =>
    -((a' u : ℂ) / ((φ' u : ℂ) ^ 2)) + ((a u : ℂ) * (φ'' u : ℂ)) / ((φ' u : ℂ) ^ 3)
  let g₂' : ℝ → ℂ := fun u =>
    -((a'' u : ℂ) / ((φ' u : ℂ) ^ 2)) +
      3 * ((a' u : ℂ) * (φ'' u : ℂ)) / ((φ' u : ℂ) ^ 3) +
      ((a u : ℂ) * (φ'' u : ℂ)) / ((φ' u : ℂ) ^ 3) -
      3 * ((a u : ℂ) * ((φ'' u : ℂ) ^ 2)) / ((φ' u : ℂ) ^ 4)
  have hg₁_zero : g₁ 0 = 0 := by dsimp [g₁, a]; rw [quarticAmp_zero]; simp
  have hg₂_zero : g₂ 0 = 0 := by dsimp [g₂, a, a']; rw [quarticAmp_zero, quarticAmp'_zero]; simp
  have hg₁_norm : ∀ u ≤ 0, ‖g₁ u‖ ≤ (32 / |γ|) * Real.exp ((9 / 4 : ℝ) * u) := by
    intro u hu
    dsimp [g₁]
    rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
    calc |a u| / |φ' u|
        ≤ (16 * Real.exp ((9 / 4 : ℝ) * u)) / (|γ| / 2) :=
          div_le_div₀ (by positivity) (abs_quarticAmp_le hσ₁ hu) (by positivity) (hφ'_lo u hu)
      _ = (32 / |γ|) * Real.exp ((9 / 4 : ℝ) * u) := by ring
  have hg₂_norm : ∀ u ≤ 0, ‖g₂ u‖ ≤ (1344 / |γ| ^ 2) * Real.exp ((9 / 4 : ℝ) * u) := by
    intro u hu
    dsimp [g₂]
    have h1 : ‖-((a' u : ℂ) / ((φ' u : ℂ) ^ 2))‖ ≤ (1280 / |γ| ^ 2) * Real.exp ((9 / 4 : ℝ) * u) := by
      rw [norm_neg, norm_div, norm_pow, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
      calc |a' u| / |φ' u| ^ 2
          ≤ (320 * Real.exp ((9 / 4 : ℝ) * u)) / (|γ| / 2) ^ 2 :=
            div_le_div₀ (by positivity) (abs_quarticAmp'_le hσ₁ hσ₂ hu) (by positivity)
              (pow_le_pow_left₀ (by positivity) (hφ'_lo u hu) 2)
        _ = (1280 / |γ| ^ 2) * Real.exp ((9 / 4 : ℝ) * u) := by ring
    have h2 : ‖((a u : ℂ) * (φ'' u : ℂ)) / ((φ' u : ℂ) ^ 3)‖ ≤
        (64 / |γ| ^ 2) * Real.exp ((9 / 4 : ℝ) * u) := by
      rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
      have hnum : |a u| * |φ'' u| ≤ (16 * Real.exp ((9 / 4 : ℝ) * u)) * (|γ| / 2) :=
        mul_le_mul (abs_quarticAmp_le hσ₁ hu) (hφ''_hi u hu) (abs_nonneg _) (by positivity)
      calc |a u| * |φ'' u| / |φ' u| ^ 3
          ≤ ((16 * Real.exp ((9 / 4 : ℝ) * u)) * (|γ| / 2)) / (|γ| / 2) ^ 3 :=
            div_le_div₀ (by positivity) hnum (by positivity)
              (pow_le_pow_left₀ (by positivity) (hφ'_lo u hu) 3)
        _ = (64 / |γ| ^ 2) * Real.exp ((9 / 4 : ℝ) * u) := by
            have hne : |γ| ≠ 0 := hγ_pos.ne'
            field_simp [hne]; ring
    calc ‖-((a' u : ℂ) / ((φ' u : ℂ) ^ 2)) + ((a u : ℂ) * (φ'' u : ℂ)) / ((φ' u : ℂ) ^ 3)‖
        ≤ ‖-((a' u : ℂ) / ((φ' u : ℂ) ^ 2))‖ + ‖((a u : ℂ) * (φ'' u : ℂ)) / ((φ' u : ℂ) ^ 3)‖ :=
          norm_add_le _ _
      _ ≤ (1280 / |γ| ^ 2) * Real.exp ((9 / 4 : ℝ) * u) +
            (64 / |γ| ^ 2) * Real.exp ((9 / 4 : ℝ) * u) := add_le_add h1 h2
      _ = (1344 / |γ| ^ 2) * Real.exp ((9 / 4 : ℝ) * u) := by ring
  have hg₂'_norm : ∀ u ≤ 0, ‖g₂' u‖ ≤ (10624 / |γ| ^ 2) * Real.exp ((9 / 4 : ℝ) * u) := fun u hu =>
    quarticKernel_tail_g2'_norm hσ₁ hσ₂ hγ hu (hφ'_lo u hu) (hφ''_hi u hu)
  have hv_deriv : ∀ u ≤ 0, HasDerivAt v_f (v_f' u) u := fun u _ => by
    have h1 : HasDerivAt (fun x => (φ x : ℂ) * Complex.I) ((φ' u : ℂ) * Complex.I) u :=
      ((hasDerivAt_quarticPhase lam γ u).ofReal_comp).mul_const Complex.I
    convert h1.cexp using 1
    dsimp [v_f']; ring
  have hg₁_deriv : ∀ u ≤ 0, HasDerivAt g₁ (g₁' u) u := fun u hu => by
    have hneC : (φ' u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hφ'_ne u hu)
    have hIφ : Complex.I * (φ' u : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero hneC
    have h1 : HasDerivAt (fun x => (a x : ℂ)) (a' u : ℂ) u := (hasDerivAt_quarticAmp σ u).ofReal_comp
    have h2 : HasDerivAt (fun x => Complex.I * (φ' x : ℂ)) (Complex.I * (φ'' u : ℂ)) u :=
      ((hasDerivAt_quarticPhase' lam γ u).ofReal_comp).const_mul Complex.I
    convert h1.div h2 hIφ using 1
    dsimp [g₁']
    field_simp [Complex.I_ne_zero, hneC]
  have hg₂_deriv : ∀ u ≤ 0, HasDerivAt g₂ (g₂' u) u := fun u hu => by
    have hneC : (φ' u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hφ'_ne u hu)
    have ha1 : HasDerivAt (fun x => (a x : ℂ)) (a' u : ℂ) u := (hasDerivAt_quarticAmp σ u).ofReal_comp
    have ha2 : HasDerivAt (fun x => (a' x : ℂ)) (a'' u : ℂ) u := (hasDerivAt_quarticAmp' σ u).ofReal_comp
    have hφ1 : HasDerivAt (fun x => (φ' x : ℂ)) (φ'' u : ℂ) u := (hasDerivAt_quarticPhase' lam γ u).ofReal_comp
    have hφ2 : HasDerivAt (fun x => (φ'' x : ℂ)) (φ'' u : ℂ) u := (hasDerivAt_quarticPhase'' lam u).ofReal_comp
    have hd1 := (ha2.div (hφ1.fun_pow 2) (pow_ne_zero 2 hneC)).neg
    have hd2 := (ha1.fun_mul hφ2).div (hφ1.fun_pow 3) (pow_ne_zero 3 hneC)
    have hadd := hd1.add hd2
    convert hadd using 1
    dsimp [g₂']
    field_simp [hneC]; ring
  have hIcc : uIcc (-M) 0 = Icc (-M) 0 := Set.uIcc_of_le (by linarith only [hM])
  have hne_on : ∀ u ∈ Icc (-M) 0, (φ' u : ℂ) ≠ 0 :=
    fun u hu => Complex.ofReal_ne_zero.mpr (hφ'_ne u hu.2)
  have hcont_φ' : ContinuousOn (fun u => (φ' u : ℂ)) (Icc (-M) 0) :=
    (Complex.continuous_ofReal.comp (by dsimp [φ']; unfold quarticPhase'; fun_prop)).continuousOn
  have hcont_φ'' : ContinuousOn (fun u => (φ'' u : ℂ)) (Icc (-M) 0) :=
    (Complex.continuous_ofReal.comp (by dsimp [φ'']; unfold quarticPhase''; fun_prop)).continuousOn
  have hcont_a : ContinuousOn (fun u => (a u : ℂ)) (Icc (-M) 0) :=
    (Complex.continuous_ofReal.comp (by dsimp [a]; unfold quarticAmp; fun_prop)).continuousOn
  have hcont_a' : ContinuousOn (fun u => (a' u : ℂ)) (Icc (-M) 0) :=
    (Complex.continuous_ofReal.comp (by dsimp [a']; unfold quarticAmp'; fun_prop)).continuousOn
  have hcont_a'' : ContinuousOn (fun u => (a'' u : ℂ)) (Icc (-M) 0) :=
    (Complex.continuous_ofReal.comp (by dsimp [a'']; unfold quarticAmp''; fun_prop)).continuousOn
  have hv'_int : IntervalIntegrable v_f' volume (-M) 0 := by
    have hcont : Continuous v_f' := by dsimp [v_f', φ, φ']; unfold quarticPhase quarticPhase'; fun_prop
    exact hcont.intervalIntegrable (μ := volume) _ _
  have hg₁'_int : IntervalIntegrable g₁' volume (-M) 0 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [hIcc]
    exact (hcont_a'.div (continuousOn_const.mul hcont_φ')
        (fun u hu => mul_ne_zero Complex.I_ne_zero (hne_on u hu))).sub
      ((hcont_a.mul hcont_φ'').div (continuousOn_const.mul (hcont_φ'.pow 2))
        (fun u hu => mul_ne_zero Complex.I_ne_zero (pow_ne_zero 2 (hne_on u hu))))
  have hg₂'_int : IntervalIntegrable g₂' volume (-M) 0 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [hIcc]
    exact ((((hcont_a''.div (hcont_φ'.pow 2) (fun u hu => pow_ne_zero 2 (hne_on u hu))).neg).add
      ((continuousOn_const.mul (hcont_a'.mul hcont_φ'')).div (hcont_φ'.pow 3)
        (fun u hu => pow_ne_zero 3 (hne_on u hu)))).add
      ((hcont_a.mul hcont_φ'').div (hcont_φ'.pow 3)
        (fun u hu => pow_ne_zero 3 (hne_on u hu)))).sub
      ((continuousOn_const.mul (hcont_a.mul (hcont_φ''.pow 2))).div (hcont_φ'.pow 4)
        (fun u hu => pow_ne_zero 4 (hne_on u hu)))
  have hibp1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun u hu => hg₁_deriv u (by rw [hIcc] at hu; exact hu.2))
    (fun u hu => hv_deriv u (by rw [hIcc] at hu; exact hu.2)) hg₁'_int hv'_int
  have hibp2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun u hu => hg₂_deriv u (by rw [hIcc] at hu; exact hu.2))
    (fun u hu => hv_deriv u (by rw [hIcc] at hu; exact hu.2)) hg₂'_int hv'_int
  have hstep1 : (∫ u in (-M)..(0 : ℝ), (a u : ℂ) * v_f u) = ∫ u in (-M)..(0 : ℝ), g₁ u * v_f' u := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [hIcc] at hu
    have hne := hne_on u hu
    dsimp [g₁, v_f, v_f']
    field_simp [Complex.I_ne_zero, hne]
  have hstep2 : (∫ u in (-M)..(0 : ℝ), g₁' u * v_f u) = ∫ u in (-M)..(0 : ℝ), g₂ u * v_f' u := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [hIcc] at hu
    have hne := hne_on u hu
    dsimp [g₁', g₂, v_f, v_f']
    field_simp [Complex.I_ne_zero, hne]
    rw [Complex.I_sq]; ring
  have hcomb : (∫ u in (-M)..(0 : ℝ), (a u : ℂ) * v_f u) =
      -(g₁ (-M) * v_f (-M)) + g₂ (-M) * v_f (-M) + ∫ u in (-M)..(0 : ℝ), g₂' u * v_f u := by
    rw [hstep1, hibp1, hstep2, hibp2, hg₁_zero, hg₂_zero]
    ring
  change ‖∫ u in (-M)..(0 : ℝ), (a u : ℂ) * v_f u‖ ≤ _
  rw [hcomb]
  have hb1 : ‖-(g₁ (-M) * v_f (-M))‖ ≤ (32 / |γ|) * Real.exp (-(9 / 4 : ℝ) * M) := by
    rw [norm_neg, norm_mul]
    dsimp [v_f]; rw [Complex.norm_exp_ofReal_mul_I, mul_one]
    have := hg₁_norm (-M) (by linarith only [hM])
    rwa [mul_neg, ← neg_mul] at this
  have hb2 : ‖g₂ (-M) * v_f (-M)‖ ≤ (1344 / |γ| ^ 2) * Real.exp (-(9 / 4 : ℝ) * M) := by
    rw [norm_mul]
    dsimp [v_f]; rw [Complex.norm_exp_ofReal_mul_I, mul_one]
    have := hg₂_norm (-M) (by linarith only [hM])
    rwa [mul_neg, ← neg_mul] at this
  have hint_le : ‖∫ u in (-M)..(0 : ℝ), g₂' u * v_f u‖ ≤ 4722 / |γ| ^ 2 := by
    have hexp_int : IntervalIntegrable (fun u : ℝ => (10624 / |γ| ^ 2) * Real.exp ((9 / 4 : ℝ) * u))
        volume (-M) 0 :=
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable
        (μ := volume) (-M) 0
    have hpt : ∀ u ∈ Ioc (-M) 0, ‖g₂' u * v_f u‖ ≤ (10624 / |γ| ^ 2) * Real.exp ((9 / 4 : ℝ) * u) := by
      intro u hu
      rw [norm_mul]
      dsimp [v_f]; rw [Complex.norm_exp_ofReal_mul_I, mul_one]
      exact hg₂'_norm u hu.2
    have hle := intervalIntegral.norm_integral_le_of_norm_le (by linarith only [hM])
      (Eventually.of_forall hpt) hexp_int
    have heval : (∫ u in (-M)..(0 : ℝ), (10624 / |γ| ^ 2) * Real.exp ((9 / 4 : ℝ) * u)) ≤ 4722 / |γ| ^ 2 := by
      rw [intervalIntegral.integral_const_mul]
      have hftc : (∫ u in (-M)..(0 : ℝ), Real.exp ((9 / 4 : ℝ) * u)) =
          (4 / 9 : ℝ) * (1 - Real.exp (-(9 / 4 : ℝ) * M)) := by
        have hder : ∀ u ∈ uIcc (-M) 0,
            HasDerivAt (fun x => (4 / 9 : ℝ) * Real.exp ((9 / 4 : ℝ) * x)) (Real.exp ((9 / 4 : ℝ) * u)) u :=
          fun u _ => by
            convert (hasDerivAt_exp_const_mul (9 / 4 : ℝ) u).const_mul (4 / 9 : ℝ) using 1; ring
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
              ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable (μ := volume) (-M) 0)]
        simp [mul_neg, neg_mul]; ring
      rw [hftc]
      have hpos_e : 0 < Real.exp (-(9 / 4 : ℝ) * M) := Real.exp_pos _
      have h1 : (4 / 9 : ℝ) * (1 - Real.exp (-(9 / 4 : ℝ) * M)) ≤ 4 / 9 := by linarith only [hpos_e]
      calc (10624 / |γ| ^ 2) * ((4 / 9 : ℝ) * (1 - Real.exp (-(9 / 4 : ℝ) * M)))
          ≤ (10624 / |γ| ^ 2) * (4 / 9 : ℝ) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ 4722 / |γ| ^ 2 := by
            have hsq : 0 < |γ| ^ 2 := by positivity
            rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hsq]
            norm_num
    exact hle.trans heval
  calc ‖-(g₁ (-M) * v_f (-M)) + g₂ (-M) * v_f (-M) + ∫ u in (-M)..(0 : ℝ), g₂' u * v_f u‖
      ≤ ‖-(g₁ (-M) * v_f (-M)) + g₂ (-M) * v_f (-M)‖ + ‖∫ u in (-M)..(0 : ℝ), g₂' u * v_f u‖ :=
        norm_add_le _ _
    _ ≤ ‖-(g₁ (-M) * v_f (-M))‖ + ‖g₂ (-M) * v_f (-M)‖ + ‖∫ u in (-M)..(0 : ℝ), g₂' u * v_f u‖ :=
        add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (32 / |γ|) * Real.exp (-(9 / 4 : ℝ) * M) + (1344 / |γ| ^ 2) * Real.exp (-(9 / 4 : ℝ) * M) +
          4722 / |γ| ^ 2 := add_le_add (add_le_add hb1 hb2) hint_le
    _ = ((32 / |γ|) + (1344 / |γ| ^ 2)) * Real.exp (-(9 / 4 : ℝ) * M) + (4722 / |γ| ^ 2) := by ring

/-- **A2 Uniform Tail Decay Bound**:
For all `1/4 ≤ σ ≤ 2`, `lam ∈ ℝ`, and `4 * π * |lam| + 2 ≤ |γ|`,
`‖quarticKernel lam (σ + γ * I)‖ ≤ 15000 / (1 + |γ|)²`
with an absolute constant completely independent of `lam`. -/
theorem quarticKernel_norm_le_tail {lam σ γ : ℝ} (hσ₁ : (1 : ℝ) / 4 ≤ σ) (hσ₂ : σ ≤ 2)
    (hγ : 4 * Real.pi * |lam| + 2 ≤ |γ|) :
    ‖quarticKernel lam (σ + γ * Complex.I)‖ ≤ 15000 / (1 + |γ|) ^ 2 := by
  rw [quarticKernel_eq_integral_Iic lam σ γ hσ₁]
  have hγ_ge2 : 2 ≤ |γ| := by
    have : 0 ≤ 4 * Real.pi * |lam| := by positivity
    linarith only [hγ, this]
  have hγ_pos : 0 < |γ| := lt_of_lt_of_le two_pos hγ_ge2
  have hF_int := integrableOn_quarticLogIntegrand lam σ γ hσ₁
  have htend_lhs := (intervalIntegral_tendsto_integral_Iic 0 hF_int tendsto_neg_atTop_atBot).norm
  have htend_exp : Tendsto (fun M : ℝ => Real.exp (-(9 / 4 : ℝ) * M)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun M : ℝ => -(9 / 4 : ℝ) * M) atTop atBot :=
      Tendsto.const_mul_atTop_of_neg (by norm_num) tendsto_id
    exact Real.tendsto_exp_atBot.comp h1
  have htend_rhs : Tendsto (fun M : ℝ =>
      ((32 / |γ|) + (1344 / |γ| ^ 2)) * Real.exp (-(9 / 4 : ℝ) * M) + (4722 / |γ| ^ 2))
      atTop (𝓝 (4722 / |γ| ^ 2)) := by
    simpa only [mul_zero, zero_add] using
      (htend_exp.const_mul ((32 / |γ|) + (1344 / |γ| ^ 2))).add_const (4722 / |γ| ^ 2)
  have hlim : ‖∫ u in Iic (0 : ℝ),
      (quarticAmp σ u : ℂ) * Complex.exp ((quarticPhase lam γ u : ℂ) * Complex.I)‖ ≤ 4722 / |γ| ^ 2 :=
    le_of_tendsto_of_tendsto htend_lhs htend_rhs
      (Eventually.mono (eventually_ge_atTop (0 : ℝ)) fun M hM => quarticKernel_tail_ibp_bound hσ₁ hσ₂ hγ hM)
  have hcmp : 4722 / |γ| ^ 2 ≤ 15000 / (1 + |γ|) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 1 + |γ| ≤ (3 / 2 : ℝ) * |γ| := by linarith only [hγ_ge2]
    have h2 : (1 + |γ|) ^ 2 ≤ (9 / 4 : ℝ) * |γ| ^ 2 := by nlinarith only [h1, hγ_pos]
    nlinarith only [h2, hγ_pos]
  exact hlim.trans hcmp

end UniformBounds

section VerticalIntegrabilityAndInversion

/-- Vertical integrability of `quarticKernel lam` on any line `1/4 ≤ σ ≤ 2`. -/
theorem verticalIntegrable_quarticKernel (lam : ℝ) {σ : ℝ} (hσ₁ : (1 : ℝ) / 4 ≤ σ) (hσ₂ : σ ≤ 2) :
    Complex.VerticalIntegrable (quarticKernel lam) σ := by
  unfold Complex.VerticalIntegrable
  set R : ℝ := 4 * Real.pi * |lam| + 2
  set C_dom : ℝ := max (1792 * (1 + R ^ 2)) 30000
  have hcont : Continuous (fun γ : ℝ => quarticKernel lam (σ + γ * Complex.I)) := by
    refine continuous_iff_continuousAt.mpr fun γ => ?_
    have hdiff := differentiableAt_quarticKernel (lam := lam) (s := σ + γ * Complex.I) (by simp; linarith)
    have hmap : ContinuousAt (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) γ := by fun_prop
    exact ContinuousAt.comp (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) (g := quarticKernel lam)
      hdiff.continuousAt hmap
  have hdom : Integrable (fun γ : ℝ => C_dom * (1 + γ ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul C_dom
  refine hdom.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun γ => ?_)
  by_cases hγ : R ≤ |γ|
  · have h1 := quarticKernel_norm_le_tail hσ₁ hσ₂ hγ
    have hsq : 1 + γ ^ 2 ≤ (1 + |γ|) ^ 2 := by
      have : 0 ≤ |γ| := abs_nonneg γ
      rw [← sq_abs γ]; nlinarith only [this]
    have h2 : 15000 / (1 + |γ|) ^ 2 ≤ 30000 * (1 + γ ^ 2)⁻¹ := by
      rw [div_eq_mul_inv]
      have hinv : ((1 + |γ|) ^ 2)⁻¹ ≤ (1 + γ ^ 2)⁻¹ := inv_anti₀ (by positivity) hsq
      have hle : 15000 * ((1 + |γ|) ^ 2)⁻¹ ≤ 15000 * (1 + γ ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by norm_num)
      have hpos : 0 ≤ (1 + γ ^ 2)⁻¹ := by positivity
      linarith only [hle, hpos]
    exact h1.trans (h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
  · push Not at hγ
    have h1 := quarticKernel_norm_le_inv_sqrt (lam := lam) (γ := γ) hσ₁ hσ₂
    have hsqrt_ge1 : (1 : ℝ) ≤ Real.sqrt (1 + |lam|) := by
      rw [Real.le_sqrt zero_le_one (by positivity)]; linarith [abs_nonneg lam]
    have hle1792 : 1792 / Real.sqrt (1 + |lam|) ≤ 1792 :=
      div_le_self (by norm_num) hsqrt_ge1
    have hsq_le : 1 + γ ^ 2 ≤ 1 + R ^ 2 := by
      have hR_nn : 0 ≤ R := by dsimp [R]; positivity
      rw [← sq_abs γ]
      nlinarith only [hγ, abs_nonneg γ, hR_nn]
    have h2 : (1792 : ℝ) ≤ (1792 * (1 + R ^ 2)) * (1 + γ ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : (0 : ℝ) < 1 + γ ^ 2)]
      nlinarith only [hsq_le]
    exact h1.trans (hle1792.trans (h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))))

/-- Vertical integrability of `mellin (scaledTiltedBump Y t)` on any line `1/4 ≤ σ ≤ 2`. -/
theorem verticalIntegrable_mellin_scaledTiltedBump {Y : ℕ} (hY : 1 ≤ Y) (t : ℝ)
    {σ : ℝ} (hσ₁ : (1 : ℝ) / 4 ≤ σ) (hσ₂ : σ ≤ 2) :
    Complex.VerticalIntegrable (mellin (scaledTiltedBump Y t)) σ := by
  unfold Complex.VerticalIntegrable
  have hY_pos : (0 : ℝ) < (Y : ℝ) := Nat.cast_pos.mpr (by omega)
  have hfun : (fun γ : ℝ => mellin (scaledTiltedBump Y t) (σ + γ * Complex.I)) =
      fun γ : ℝ => ((Y : ℝ) : ℂ) ^ (σ + γ * Complex.I) * quarticKernel (t * (Y : ℝ)) (σ + γ * Complex.I) :=
    funext fun γ => mellin_scaledTiltedBump_eq hY t (σ + γ * Complex.I)
  rw [hfun]
  have hcont : Continuous (fun γ : ℝ => ((Y : ℝ) : ℂ) ^ (σ + γ * Complex.I)) := by
    have hY_ne : ((Y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY_pos.ne'
    exact Continuous.const_cpow (by fun_prop) (Or.inl hY_ne)
  have hker := verticalIntegrable_quarticKernel (t * (Y : ℝ)) hσ₁ hσ₂
  refine (hker.norm.const_mul ((Y : ℝ) ^ σ)).mono'
    (hcont.aestronglyMeasurable.mul hker.aestronglyMeasurable) (Eventually.of_forall fun γ => ?_)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY_pos]
  simp

/-- **A2 Mellin Inversion Formula**:
For all `Y ≥ 1`, `t ∈ ℝ`, `1/4 ≤ σ ≤ 2`, and `x > 0`,
`mellinInv σ (mellin (scaledTiltedBump Y t)) x = scaledTiltedBump Y t x`. -/
theorem mellinInv_scaledTiltedBump_eq {Y : ℕ} (hY : 1 ≤ Y) (t : ℝ)
    {σ : ℝ} (hσ₁ : (1 : ℝ) / 4 ≤ σ) (hσ₂ : σ ≤ 2) {x : ℝ} (hx : 0 < x) :
    mellinInv σ (mellin (scaledTiltedBump Y t)) x = scaledTiltedBump Y t x :=
  mellinInv_mellin_eq σ (scaledTiltedBump Y t) hx
    (mellinConvergent_scaledTiltedBump hY (by simp; linarith))
    (verticalIntegrable_mellin_scaledTiltedBump hY t hσ₁ hσ₂)
    (continuous_scaledTiltedBump Y t).continuousAt

end VerticalIntegrabilityAndInversion

end FareyGoldbach

