import FareyGoldbach.Defs
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Module A1: Local Zero Counting and Logarithmic Derivative Bounds in `Re(s) > 0`

Working entirely inside the right half-plane `Re(s) > 0` (avoiding functional equations,
Gamma factors, Stirling's formula, Phragmén–Lindelöf, and global Hadamard products),
this module proves under `DirichletGRH` for every primitive Dirichlet character `χ mod d`:

1. Elementary integral continuation & polynomial growth `‖entireL χ s‖ ≤ 17 d (1 + ‖s‖)²`
   for `Re(s) ≥ 1/16`, plus center lower bound `‖entireL χ (2 + iT)‖ ≥ 1/4`.
2. Local Jensen zero counting `zeroCount_unit`:
   at most `310 * log(2 d (2 + |T|))` zeros (with multiplicity) in any unit strip `|Im ρ - T| ≤ 1`.
3. Local partial-fraction representation `local_negLogDeriv_approx` on `closedBall (2 + iT) (7/4)`
   via `FactorizedRational`, Maximum Modulus Principle, `HasPrimitives`, `borelCaratheodory_zero`,
   and Cauchy's derivative bound.
4. `negLogDeriv_quarter`: `‖-L'/L(1/4 + iu, χ)‖ ≪ log(2 d (2 + |u|))`.
5. `exists_good_height`: for every `j ≥ 2`, there exists `T ∈ [j, j + 1]` avoiding all zeros
   on `Im s = ±T` with `‖-L'/L(σ ± iT, χ)‖ ≪ log²(2 d (2 + T))` uniformly on `1/4 ≤ σ ≤ 2`.
-/

open Real Complex Set Filter MeasureTheory Topology Metric
open scoped BigOperators Classical

namespace FareyGoldbach

section BasicDefinitions

/-- Entire completion of `L(s, χ)`: equals `LFunctionTrivChar₁ d` when `χ = 1` (removing the
simple pole at `s = 1`, with value `1` when `d = 1`) and `χ.LFunction` when `χ ≠ 1`. -/
noncomputable def entireL {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) : ℂ → ℂ :=
  if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ d else χ.LFunction

/-- Negative logarithmic derivative `-L'(s, χ) / L(s, χ)`. -/
noncomputable def negLogDerivL {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (s : ℂ) : ℂ :=
  -deriv χ.LFunction s / χ.LFunction s

/-- Zero multiplicity of `entireL χ` at `ρ : ℂ`. -/
noncomputable def zeroMult {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (ρ : ℂ) : ℕ :=
  (analyticOrderAt (entireL χ) ρ).toNat

lemma eq_one_of_isPrimitive_of_eq_one {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    (hprim : χ.IsPrimitive) (h1 : χ = 1) : d = 1 := by
  have hcond : χ.conductor = 1 := DirichletCharacter.eq_one_iff_conductor_eq_one.mp h1
  rw [DirichletCharacter.isPrimitive_def] at hprim
  exact hprim.symm.trans hcond

lemma differentiable_entireL {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) :
    Differentiable ℂ (entireL χ) := by
  classical
  unfold entireL
  split_ifs with h
  · exact DirichletCharacter.differentiable_LFunctionTrivChar₁ d
  · exact DirichletCharacter.differentiable_LFunction h

lemma analyticOnNhd_entireL {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) :
    AnalyticOnNhd ℂ (entireL χ) Set.univ :=
  Complex.analyticOnNhd_univ_iff_differentiable.mpr (differentiable_entireL χ)

lemma entireL_apply_of_ne_one {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) {s : ℂ} (hs : s ≠ 1) :
    entireL χ s = if χ = 1 then (s - 1) * χ.LFunction s else χ.LFunction s := by
  classical
  unfold entireL
  split_ifs with h
  · subst h
    simp [DirichletCharacter.LFunctionTrivChar₁, DirichletCharacter.LFunctionTrivChar,
      Function.update_of_ne hs]
  · rfl

lemma entireL_apply_one_of_eq_one {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    (hprim : χ.IsPrimitive) (h1 : χ = 1) : entireL χ 1 = 1 := by
  classical
  have hd1 := eq_one_of_isPrimitive_of_eq_one hprim h1
  subst hd1
  unfold entireL
  simp [h1, DirichletCharacter.LFunctionTrivChar₁]

/-- Relation between `negLogDerivL χ` and `-deriv (entireL χ) / entireL χ` away from `s = 1`. -/
lemma negLogDerivL_eq_of_ne_one {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) {s : ℂ}
    (hs : s ≠ 1) (hL : χ.LFunction s ≠ 0) :
    negLogDerivL χ s =
      (if χ = 1 then 1 / (s - 1) else 0) - deriv (entireL χ) s / entireL χ s := by
  classical
  unfold negLogDerivL entireL
  split_ifs with h
  · subst h
    have hval : DirichletCharacter.LFunctionTrivChar₁ d s = (s - 1) * (1 : DirichletCharacter ℂ d).LFunction s := by
      simp [DirichletCharacter.LFunctionTrivChar₁, DirichletCharacter.LFunctionTrivChar,
        Function.update_of_ne hs]
    have hder : deriv (DirichletCharacter.LFunctionTrivChar₁ d) s =
        (s - 1) * deriv (1 : DirichletCharacter ℂ d).LFunction s + (1 : DirichletCharacter ℂ d).LFunction s := by
      simpa [DirichletCharacter.LFunctionTrivChar] using
        DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one (n := d) hs
    rw [hval, hder]
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    field_simp [hs1, hL]
    ring
  · simp [sub_eq_add_neg, neg_div]

/-- For `1 < s.re`, `LSeries (χ * Λ) s = negLogDerivL χ s`. -/
lemma LSeries_twist_vonMangoldt_eq_negLogDerivL {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (χ (n : ZMod d)) * (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      negLogDerivL χ s := by
  have h1 := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  have h2 := DirichletCharacter.LFunction_eq_LSeries χ hs
  have h3 := DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs
  unfold negLogDerivL
  rw [h2, h3]
  exact h1

/-- Under `DirichletGRH`, every zero of `entireL χ` in `Re(s) > 0` lies on `Re(s) = 1/2`. -/
lemma entireL_re_eq_half_of_eq_zero (hGRH : DirichletGRH) {d : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) {s : ℂ}
    (hs0 : 0 < s.re) (hzero : entireL χ s = 0) : s.re = 1 / 2 := by
  classical
  by_cases hs1 : s.re < 1
  · have hne1 : s ≠ 1 := fun h => by rw [h] at hs1; simp at hs1
    rw [entireL_apply_of_ne_one χ hne1] at hzero
    have hLz : χ.LFunction s = 0 := by
      split_ifs at hzero with h1
      · exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne1)
      · exact hzero
    exact hGRH d χ hprim s hs0 hs1 hLz
  · exfalso
    push Not at hs1
    by_cases h1 : χ = 1
    · by_cases hseq : s = 1
      · subst hseq
        have hne := entireL_apply_one_of_eq_one hprim h1
        rw [hne] at hzero
        exact one_ne_zero hzero
      · rw [entireL_apply_of_ne_one χ hseq] at hzero
        simp only [h1, ↓reduceIte] at hzero
        have hLz : (1 : DirichletCharacter ℂ d).LFunction s = 0 :=
          (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hseq)
        rw [← h1] at hLz
        exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hseq) hs1 hLz
    · have hne : χ.LFunction s ≠ 0 :=
        DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl h1) hs1
      unfold entireL at hzero
      simp only [h1, ↓reduceIte] at hzero
      exact hne hzero

/-- Every value of a Dirichlet character has norm at most `1`. -/
lemma norm_dirichletChar_le_one {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (a : ZMod d) :
    ‖χ a‖ ≤ 1 := by
  by_cases hu : IsUnit a
  · have hmul : χ a * star (χ a) = 1 := by
      rw [MulChar.star_apply', MulChar.inv_apply, ← map_mul, Ring.inverse_of_isUnit hu]
      have h1 : a * (↑hu.unit⁻¹ : ZMod d) = 1 := by
        calc a * (↑hu.unit⁻¹ : ZMod d) = (↑hu.unit : ZMod d) * (↑hu.unit⁻¹ : ZMod d) := rfl
          _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [h1, map_one]
    have hsq : ‖χ a‖ ^ 2 = 1 := by
      have h := congrArg (fun z : ℂ => z.re) hmul
      rw [Complex.star_def, Complex.mul_conj'] at h
      rw [← Complex.ofReal_pow, Complex.ofReal_re, Complex.one_re] at h
      exact h
    nlinarith [norm_nonneg (χ a)]
  · rw [MulChar.map_nonunit χ hu, norm_zero]
    exact zero_le_one

end BasicDefinitions

section CenterAndGrowthBounds

/-- Elementary telescoping bound `∑' n : ℕ, (if 2 ≤ n then (1 : ℝ) / (n : ℝ) ^ 2 else 0) ≤ 3 / 4`. -/
private lemma tsum_inv_sq_from_two_le :
    (∑' n : ℕ, if 2 ≤ n then (1 : ℝ) / (n : ℝ) ^ 2 else 0) ≤ 3 / 4 := by
  have hsum_all : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := by
    simp [one_div]
  have hsum : Summable (fun n : ℕ => if 2 ≤ n then (1 : ℝ) / (n : ℝ) ^ 2 else 0) :=
    hsum_all.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
      (fun n => by split_ifs <;> [exact le_rfl; positivity])
  have hstrong : ∀ m : ℕ, 2 ≤ m →
      (∑ n ∈ Finset.range (m + 1), if 2 ≤ n then (1 : ℝ) / (n : ℝ) ^ 2 else 0) ≤
        3 / 4 - 1 / (m : ℝ) := by
    intro m hm
    induction m with
    | zero => omega
    | succ k ih =>
      by_cases hk2 : 2 ≤ k
      · have hk2' : 2 ≤ k + 1 := by omega
        rw [Finset.sum_range_succ]
        simp only [hk2', ↓reduceIte]
        have ih' := ih hk2
        have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
        have hstep : (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) := by
          push_cast
          have h1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith only [hk_pos]
          have hdiff : 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) = 1 / ((k : ℝ) * ((k : ℝ) + 1)) := by
            field_simp [hk_pos.ne', h1.ne']; ring
          rw [hdiff]
          refine one_div_le_one_div_of_le (by positivity) ?_
          nlinarith only [hk_pos]
        linarith only [ih', hstep]
      · have hk1 : k = 1 := by omega
        subst hk1
        simp [Finset.sum_range_succ]
        norm_num
  refine Real.tsum_le_of_sum_range_le (fun n => by split_ifs <;> positivity) fun N => ?_
  by_cases hN : 3 ≤ N
  · have hm : 2 ≤ N - 1 := by omega
    have hEq : N - 1 + 1 = N := by omega
    have h1 := hstrong (N - 1) hm
    rw [hEq] at h1
    have hpos : (0 : ℝ) ≤ 1 / ((N - 1 : ℕ) : ℝ) := by positivity
    linarith only [h1, hpos]
  · have hsub : Finset.range N ⊆ Finset.range 3 := Finset.range_mono (by omega)
    have hle : (∑ n ∈ Finset.range N, if 2 ≤ n then (1 : ℝ) / (n : ℝ) ^ 2 else 0) ≤
        ∑ n ∈ Finset.range 3, if 2 ≤ n then (1 : ℝ) / (n : ℝ) ^ 2 else 0 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by split_ifs <;> positivity
    have h3 : (∑ n ∈ Finset.range 3, if 2 ≤ n then (1 : ℝ) / (n : ℝ) ^ 2 else 0) ≤ 3 / 4 := by
      simp [Finset.sum_range_succ]; norm_num
    exact hle.trans h3

/-- Center lower bound: `‖entireL χ (2 + T * I)‖ ≥ 1/4` for every Dirichlet character `χ` and `T : ℝ`. -/
theorem norm_entireL_two_add_ge_quarter {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (T : ℝ) :
    (1 : ℝ) / 4 ≤ ‖entireL χ (2 + (T : ℂ) * Complex.I)‖ := by
  set c : ℂ := 2 + (T : ℂ) * Complex.I
  have hc_re : c.re = 2 := by simp [c]
  have hc1 : 1 < c.re := by linarith
  have hc_ne1 : c ≠ 1 := fun h => by rw [h] at hc_re; simp at hc_re
  -- First show `1/4 ≤ ‖χ.LFunction c‖` directly from the Dirichlet series.
  have hL_ge : (1 : ℝ) / 4 ≤ ‖χ.LFunction c‖ := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hc1]
    have hsumm : LSeriesSummable (fun n => χ (n : ZMod d)) c :=
      DirichletCharacter.LSeriesSummable_of_one_lt_re χ hc1
    have htail_summ : Summable (fun n : ℕ => if 2 ≤ n then LSeries.term (fun k => χ (k : ZMod d)) c n else 0) :=
      Summable.of_norm_bounded hsumm.norm fun n => by
        split_ifs
        · exact le_rfl
        · rw [norm_zero]; exact norm_nonneg _
    have hdecomp : LSeries (fun n => χ (n : ZMod d)) c =
        1 + ∑' n : ℕ, if 2 ≤ n then LSeries.term (fun k => χ (k : ZMod d)) c n else 0 := by
      unfold LSeries
      have hterm0 : LSeries.term (fun k => χ (k : ZMod d)) c 0 = 0 := by simp [LSeries.term]
      have hsplit := hsumm.sum_add_tsum_nat_add 2
      have hsum2 : ∑ i ∈ Finset.range 2, LSeries.term (fun k => χ (k : ZMod d)) c i = 1 := by
        simp [Finset.sum_range_succ, hterm0]
      rw [← hsplit, hsum2]
      congr 1
      rw [← htail_summ.sum_add_tsum_nat_add 2]
      have hz : ∑ i ∈ Finset.range 2,
          (if 2 ≤ i then LSeries.term (fun k => χ (k : ZMod d)) c i else 0) = 0 := by
        simp [Finset.sum_range_succ]
      rw [hz, zero_add]
      refine tsum_congr fun n => ?_
      have hge : 2 ≤ n + 2 := by omega
      simp only [hge, ↓reduceIte]
    have htail_le : ‖∑' n : ℕ, if 2 ≤ n then LSeries.term (fun k => χ (k : ZMod d)) c n else 0‖ ≤ 3 / 4 := by
      have hnorm_summ : Summable (fun n : ℕ => if 2 ≤ n then (1 : ℝ) / (n : ℝ) ^ 2 else 0) := by
        have hsum_all : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := by
          simp [one_div]
        exact hsum_all.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
          (fun n => by split_ifs <;> [exact le_rfl; positivity])
      have hpt : ∀ n : ℕ,
          ‖if 2 ≤ n then LSeries.term (fun k => χ (k : ZMod d)) c n else 0‖ ≤
            if 2 ≤ n then (1 : ℝ) / (n : ℝ) ^ 2 else 0 := by
        intro n
        split_ifs with hn
        · have hn0 : n ≠ 0 := by omega
          have hn_pos : 0 < n := by omega
          rw [LSeries.term_of_ne_zero hn0, norm_div, Complex.norm_natCast_cpow_of_pos hn_pos, hc_re]
          have hχ_le : ‖χ (n : ZMod d)‖ ≤ 1 := norm_dirichletChar_le_one χ _
          have hpow : (n : ℝ) ^ (2 : ℝ) = (n : ℝ) ^ (2 : ℕ) := Real.rpow_natCast _ 2
          rw [hpow]
          exact div_le_div_of_nonneg_right hχ_le (by positivity)
        · simp
      exact (norm_tsum_le_tsum_norm htail_summ.norm).trans
        ((htail_summ.norm.tsum_le_tsum hpt hnorm_summ).trans tsum_inv_sq_from_two_le)
    rw [hdecomp]
    have htri := norm_sub_le (1 + ∑' n : ℕ, if 2 ≤ n then LSeries.term (fun k => χ (k : ZMod d)) c n else 0)
      (∑' n : ℕ, if 2 ≤ n then LSeries.term (fun k => χ (k : ZMod d)) c n else 0)
    rw [add_sub_cancel_right, norm_one] at htri
    linarith only [htri, htail_le]
  rw [entireL_apply_of_ne_one χ hc_ne1]
  split_ifs with h1
  · rw [norm_mul]
    have hc1_ge : (1 : ℝ) ≤ ‖c - 1‖ := by
      have hre : (c - 1).re = 1 := by simp [c]; norm_num
      calc (1 : ℝ) = |(c - 1).re| := by rw [hre, abs_one]
        _ ≤ ‖c - 1‖ := Complex.abs_re_le_norm (c - 1)
    calc (1 : ℝ) / 4 = 1 * (1 / 4) := (one_mul _).symm
      _ ≤ ‖c - 1‖ * ‖χ.LFunction c‖ := mul_le_mul hc1_ge hL_ge (by norm_num) (by linarith only [hc1_ge])
  · exact hL_ge

lemma entireL_two_add_ne_zero {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (T : ℝ) :
    entireL χ (2 + (T : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have := norm_entireL_two_add_ge_quarter χ T
  rw [h, norm_zero] at this
  linarith

/-- Any bounded measurable function `A` on `(1, ∞)` defines a holomorphic Dirichlet integral
`s ↦ ∫ t in Ioi 1, A t * t ^ (-(s + 1))` on `Re(s) > 0`. -/
lemma differentiableOn_dirichletIntegral {A : ℝ → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hA_meas : AEStronglyMeasurable A (volume.restrict (Ioi 1)))
    (hA_bound : ∀ t ∈ Ioi (1 : ℝ), ‖A t‖ ≤ B) :
    DifferentiableOn ℂ (fun s : ℂ => ∫ t in Ioi (1 : ℝ), A t * (t : ℂ) ^ (-(s + 1)))
      {s : ℂ | 0 < s.re} := by
  intro s₀ hs₀
  refine DifferentiableAt.differentiableWithinAt ?_
  have hs₀_pos : 0 < s₀.re := hs₀
  set δ : ℝ := s₀.re / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith only [hs₀_pos]
  let F : ℂ → ℝ → ℂ := fun s t => A t * (t : ℂ) ^ (-(s + 1))
  let F' : ℂ → ℝ → ℂ := fun s t => A t * (-Complex.log (t : ℂ) * (t : ℂ) ^ (-(s + 1)))
  let bound : ℝ → ℝ := fun t => B * (2 / δ) * t ^ (-(1 + δ / 2))
  have hF_meas : ∀ s : ℂ, AEStronglyMeasurable (F s) (volume.restrict (Ioi 1)) := fun s => by
    have hcp : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (volume.restrict (Ioi 1)) :=
      ContinuousOn.aestronglyMeasurable
        (fun t ht => (Complex.continuousAt_ofReal_cpow_const _ _
          (Or.inr (zero_lt_one.trans ht).ne')).continuousWithinAt) measurableSet_Ioi
    exact hA_meas.mul hcp
  have hF'_meas : AEStronglyMeasurable (F' s₀) (volume.restrict (Ioi 1)) := by
    have hlog : AEStronglyMeasurable (fun t : ℝ => -Complex.log (t : ℂ)) (volume.restrict (Ioi 1)) := by
      have hc : ContinuousOn (fun t : ℝ => -((Real.log t : ℝ) : ℂ)) (Ioi 1) :=
        (Complex.continuous_ofReal.comp_continuousOn
          (Real.continuousOn_log.mono fun t ht => (zero_lt_one.trans ht).ne')).neg
      refine (hc.aestronglyMeasurable measurableSet_Ioi).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Complex.ofReal_log (zero_lt_one.trans ht).le]
    have hcp : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (-(s₀ + 1))) (volume.restrict (Ioi 1)) :=
      ContinuousOn.aestronglyMeasurable
        (fun t ht => (Complex.continuousAt_ofReal_cpow_const _ _
          (Or.inr (zero_lt_one.trans ht).ne')).continuousWithinAt) measurableSet_Ioi
    exact hA_meas.mul (hlog.mul hcp)
  have hF_int : Integrable (F s₀) (volume.restrict (Ioi 1)) := by
    have hdom : IntegrableOn (fun t : ℝ => B * t ^ (-(s₀.re + 1))) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith only [hs₀_pos]) zero_lt_one).const_mul B
    refine hdom.mono' (hF_meas s₀) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    dsimp [F]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : (-(s₀ + 1)).re = -(s₀.re + 1) := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_right (hA_bound t ht) (by positivity)
  have hbound_int : Integrable bound (volume.restrict (Ioi 1)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith only [hδ]) zero_lt_one).const_mul (B * (2 / δ))
  have h_bound : ∀ᵐ t ∂(volume.restrict (Ioi 1)), ∀ s ∈ ball s₀ δ, ‖F' s t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s hs
    have ht1 : 1 < t := ht
    have ht0 : 0 < t := zero_lt_one.trans ht1
    have hs_re : δ < s.re := by
      have hdist : ‖s - s₀‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hs
      have hre := (Complex.abs_re_le_norm (s - s₀)).trans_lt hdist
      have hsub : (s - s₀).re = s.re - s₀.re := by simp
      rw [hsub] at hre
      have := (abs_lt.mp hre).1
      dsimp [δ] at this ⊢; linarith only [this]
    have hlog_le : Real.log t ≤ (2 / δ) * t ^ (δ / 2) := by
      have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht0 (δ / 2))
      rw [Real.log_rpow ht0] at h1
      have h2 : (δ / 2) * Real.log t ≤ t ^ (δ / 2) := by linarith only [h1]
      have hmul := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 / δ)
      have hcancel : (2 / δ) * ((δ / 2) * Real.log t) = Real.log t := by field_simp [hδ.ne']
      linarith only [hmul, hcancel]
    have hrpow_le : t ^ (-(s.re + 1)) ≤ t ^ (-(δ + 1)) :=
      Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith only [hs_re])
    dsimp [F', bound]
    rw [norm_mul, norm_mul, norm_neg, ← Complex.ofReal_log ht0.le, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg ht1.le),
        Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : (-(s + 1)).re = -(s.re + 1) := by simp
    rw [hre]
    calc ‖A t‖ * (Real.log t * t ^ (-(s.re + 1)))
        ≤ B * (((2 / δ) * t ^ (δ / 2)) * t ^ (-(δ + 1))) :=
          mul_le_mul (hA_bound t ht)
            (mul_le_mul hlog_le hrpow_le (Real.rpow_nonneg ht0.le _)
              (mul_nonneg (by positivity) (Real.rpow_nonneg ht0.le _)))
            (mul_nonneg (Real.log_nonneg ht1.le) (Real.rpow_nonneg ht0.le _)) hB
      _ = B * (2 / δ) * (t ^ (δ / 2) * t ^ (-(δ + 1))) := by ring
      _ = B * (2 / δ) * t ^ (-(1 + δ / 2)) := by
          rw [← Real.rpow_add ht0]; congr 2; ring
  have h_diff : ∀ᵐ t ∂(volume.restrict (Ioi 1)), ∀ s ∈ ball s₀ δ, HasDerivAt (F · t) (F' s t) s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s _
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    have hexp : HasDerivAt (fun z : ℂ => -(z + 1)) (-1) s :=
      ((hasDerivAt_id s).add_const 1).neg
    have hcp : HasDerivAt (fun z : ℂ => (t : ℂ) ^ (-(z + 1)))
        ((t : ℂ) ^ (-(s + 1)) * Complex.log (t : ℂ) * (-1)) s :=
      hexp.const_cpow (Or.inl hne)
    convert hcp.const_mul (A t) using 1
    dsimp [F']; ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds s₀ hδ)
    (Eventually.of_forall hF_meas) hF_int hF'_meas h_bound hbound_int h_diff).2.differentiableAt

/-- Uniform bound on a bounded Dirichlet integral for `1/16 ≤ s.re`. -/
lemma norm_dirichletIntegral_le {A : ℝ → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hA_meas : AEStronglyMeasurable A (volume.restrict (Ioi 1)))
    (hA_bound : ∀ t ∈ Ioi (1 : ℝ), ‖A t‖ ≤ B)
    {s : ℂ} (hs : (1 : ℝ) / 16 ≤ s.re) :
    ‖∫ t in Ioi (1 : ℝ), A t * (t : ℂ) ^ (-(s + 1))‖ ≤ 16 * B := by
  have hdom : IntegrableOn (fun t : ℝ => B * t ^ (-(17 / 16 : ℝ))) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul B
  have hmeas : AEStronglyMeasurable (fun t : ℝ => A t * (t : ℂ) ^ (-(s + 1))) (volume.restrict (Ioi 1)) := by
    have hcp : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (volume.restrict (Ioi 1)) :=
      ContinuousOn.aestronglyMeasurable
        (fun t ht => (Complex.continuousAt_ofReal_cpow_const _ _
          (Or.inr (zero_lt_one.trans ht).ne')).continuousWithinAt) measurableSet_Ioi
    exact hA_meas.mul hcp
  have hpt : ∀ t ∈ Ioi (1 : ℝ), ‖A t * (t : ℂ) ^ (-(s + 1))‖ ≤ B * t ^ (-(17 / 16 : ℝ)) := by
    intro t ht
    have ht1 : 1 < t := ht
    have ht0 : 0 < t := zero_lt_one.trans ht1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : (-(s + 1)).re = -(s.re + 1) := by simp
    rw [hre]
    exact mul_le_mul (hA_bound t ht)
      (Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith only [hs]))
      (by positivity) hB
  have hint : IntegrableOn (fun t : ℝ => A t * (t : ℂ) ^ (-(s + 1))) (Ioi 1) :=
    hdom.mono' hmeas (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; exact hpt t ht)
  have heval : (∫ t in Ioi (1 : ℝ), B * t ^ (-(17 / 16 : ℝ))) = 16 * B := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
    norm_num; ring
  calc ‖∫ t in Ioi (1 : ℝ), A t * (t : ℂ) ^ (-(s + 1))‖
      ≤ ∫ t in Ioi (1 : ℝ), ‖A t * (t : ℂ) ^ (-(s + 1))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (1 : ℝ), B * t ^ (-(17 / 16 : ℝ)) :=
        setIntegral_mono_on hint.norm hdom measurableSet_Ioi hpt
    _ = 16 * B := heval

/-- Partial sums of a non-principal Dirichlet character `χ mod d` are uniformly bounded by `d`. -/
lemma norm_charPartialSum_le {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d} (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.Icc 1 n, χ (k : ZMod d)‖ ≤ (d : ℝ) := by
  have hd : 0 < d := NeZero.pos d
  induction n using Nat.strong_induction_on with
  | ind m ih =>
    by_cases hlt : m < d
    · calc ‖∑ k ∈ Finset.Icc 1 m, χ (k : ZMod d)‖
          ≤ ∑ k ∈ Finset.Icc 1 m, ‖χ (k : ZMod d)‖ := norm_sum_le _ _
        _ ≤ ∑ _k ∈ Finset.Icc 1 m, (1 : ℝ) := Finset.sum_le_sum fun k _ => norm_dirichletChar_le_one χ _
        _ = (m : ℝ) := by simp
        _ ≤ (d : ℝ) := Nat.cast_le.mpr hlt.le
    · push Not at hlt
      -- Split `Icc 1 m = Icc 1 (m - d) ∪ Icc (m - d + 1) m`; the upper block of length `d` sums to `0`.
      have hunion : Finset.Icc 1 m = Finset.Icc 1 (m - d) ∪ Finset.Icc (m - d + 1) m := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      have hdisj : Disjoint (Finset.Icc 1 (m - d)) (Finset.Icc (m - d + 1) m) :=
        Finset.disjoint_left.mpr fun k h1 h2 => by
          simp only [Finset.mem_Icc] at h1 h2; omega
      have hblock : ∑ k ∈ Finset.Icc (m - d + 1) m, χ (k : ZMod d) = 0 := by
        have hbij : ∑ k ∈ Finset.Icc (m - d + 1) m, χ (k : ZMod d) = ∑ a : ZMod d, χ a := by
          refine Finset.sum_bij (fun k _ => (k : ZMod d)) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
          · intro k₁ hk₁ k₂ hk₂ heq
            simp only [Finset.mem_Icc] at hk₁ hk₂
            have hmod : k₁ % d = k₂ % d := by
              have := (ZMod.natCast_eq_natCast_iff k₁ k₂ d).1 heq
              exact this
            -- Since `k₁, k₂ ∈ [m - d + 1, m]`, `|k₁ - k₂| < d` and `k₁ ≡ k₂ (mod d)` forces `k₁ = k₂`.
            by_cases hle : k₁ ≤ k₂
            · have hdvd' : d ∣ k₂ - k₁ := (Nat.modEq_iff_dvd' hle).1 hmod
              rcases hdvd' with ⟨q, hq⟩
              have hq0 : q = 0 := by
                by_contra hq_ne
                have hge : d ≤ d * q := by simpa using Nat.mul_le_mul_left d (by omega : 1 ≤ q)
                omega
              rw [hq0, mul_zero] at hq
              omega
            · have hle' : k₂ ≤ k₁ := by omega
              have hdvd' : d ∣ k₁ - k₂ := (Nat.modEq_iff_dvd' hle').1 hmod.symm
              rcases hdvd' with ⟨q, hq⟩
              have hq0 : q = 0 := by
                by_contra hq_ne
                have hge : d ≤ d * q := by simpa using Nat.mul_le_mul_left d (by omega : 1 ≤ q)
                omega
              rw [hq0, mul_zero] at hq
              omega
          · intro a _
            let r := (a - ((m - d + 1 : ℕ) : ZMod d)).val
            have hr : r < d := ZMod.val_lt _
            refine ⟨m - d + 1 + r, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
            simp [r, Nat.cast_add]
        rw [hbij]
        exact MulChar.sum_eq_zero_of_ne_one hχ
      rw [hunion, Finset.sum_union hdisj, hblock, add_zero]
      exact ih (m - d) (by omega)

/-- Integral continuation of `L(s, χ)` to `Re(s) > 0` for non-principal `χ`. -/
lemma entireL_eq_integral_of_ne_one {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d} (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    entireL χ s =
      s * ∫ t in Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod d)) * (t : ℂ) ^ (-(s + 1)) := by
  let A : ℝ → ℂ := fun t => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod d)
  have hA_meas : AEStronglyMeasurable A (volume.restrict (Ioi 1)) := by
    have hm : Measurable (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod d)) := measurable_of_countable _
    exact (hm.comp Nat.measurable_floor).aestronglyMeasurable
  have hA_bound : ∀ t ∈ Ioi (1 : ℝ), ‖A t‖ ≤ (d : ℝ) := fun t _ => norm_charPartialSum_le hχ ⌊t⌋₊
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  let G : ℂ → ℂ := fun z => z * ∫ t in Ioi (1 : ℝ), A t * (t : ℂ) ^ (-(z + 1))
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_conn : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hG_diff : DifferentiableOn ℂ G U :=
    differentiableOn_id.mul (differentiableOn_dirichletIntegral (Nat.cast_nonneg d) hA_meas hA_bound)
  have hG_ana : AnalyticOnNhd ℂ G U := hG_diff.analyticOnNhd hU_open
  have hF_ana : AnalyticOnNhd ℂ (entireL χ) U := (analyticOnNhd_entireL χ).mono (Set.subset_univ U)
  have hEq_gt1 : ∀ z : ℂ, 1 < z.re → entireL χ z = G z := by
    intro z hz
    have hz_ne1 : z ≠ 1 := fun h => by rw [h] at hz; simp at hz
    rw [entireL_apply_of_ne_one χ hz_ne1]
    simp only [hχ, ↓reduceIte]
    rw [DirichletCharacter.LFunction_eq_LSeries χ hz]
    have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod d)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (0 : ℝ) := by
      refine Asymptotics.isBigO_iff.mpr ⟨(d : ℝ), Eventually.of_forall fun n => ?_⟩
      simpa using norm_charPartialSum_le hχ n
    exact LSeries_eq_mul_integral (fun n => χ (n : ZMod d)) le_rfl (by linarith)
      (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hz) hO
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ), entireL χ z = G z := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2 : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by simp
    have hmem : {z : ℂ | 1 < z.re} ∈ 𝓝[≠] (2 : ℂ) := mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds h2)
    exact (Filter.eventually_of_mem hmem hEq_gt1).frequently
  exact hF_ana.eqOn_of_preconnected_of_frequently_eq hG_ana hU_conn (by simp [U] : (2 : ℂ) ∈ U) hfreq hs

/-- Evaluation of `∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-s) = 1 / (s - 1)` for `1 < s.re`. -/
private lemma integral_Ioi_one_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    (∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-s)) = 1 / (s - 1) := by
  have hs1 : s - 1 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  have h1s : 1 - s ≠ 0 := fun h => hs1 (by linear_combination -h)
  have hder : ∀ t ∈ Ici (1 : ℝ), HasDerivAt (fun x : ℝ => (x : ℂ) ^ (1 - s) / (1 - s)) ((t : ℂ) ^ (-s)) t := by
    intro t ht
    have ht0 : 0 < t := zero_lt_one.trans_le ht
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) ^ (1 - s)) ((1 - s) * (t : ℂ) ^ (1 - s - 1)) t := by
      have hcp := (Complex.hasStrictDerivAt_cpow_const (c := 1 - s)
        (Complex.ofReal_mem_slitPlane.mpr ht0)).hasDerivAt
      simpa using hcp.comp_ofReal
    convert h1.div_const (1 - s) using 1
    have hexp : (1 - s) - 1 = -s := by ring
    rw [hexp, mul_div_cancel_left₀ _ h1s]
  have hint : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one
  have htend : Tendsto (fun t : ℝ => (t : ℂ) ^ (1 - s) / (1 - s)) atTop (𝓝 0) := by
    have hnorm : Tendsto (fun t : ℝ => ‖(t : ℂ) ^ (1 - s) / (1 - s)‖) atTop (𝓝 0) := by
      have h0 : Tendsto (fun t : ℝ => t ^ (1 - s.re) / ‖1 - s‖) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < s.re - 1)).div_const ‖1 - s‖
      refine h0.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ht]
      have hre : (1 - s).re = 1 - s.re := by simp
      rw [hre]
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto' hder hint htend
  rw [hval, Complex.ofReal_one, Complex.one_cpow, zero_sub]
  field_simp [hs1, h1s]
  ring

/-- Integral continuation of `(s - 1) ζ(s)` to `Re(s) > 0` for the primitive principal character (`d = 1`). -/
lemma entireL_eq_integral_of_eq_one {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    (hprim : χ.IsPrimitive) (h1 : χ = 1) {s : ℂ} (hs : 0 < s.re) :
    entireL χ s =
      s - s * (s - 1) * ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hd1 := eq_one_of_isPrimitive_of_eq_one hprim h1
  subst hd1
  let A : ℝ → ℂ := fun t => ((Int.fract t : ℝ) : ℂ)
  have hA_meas : AEStronglyMeasurable A (volume.restrict (Ioi 1)) :=
    (Complex.continuous_ofReal.measurable.comp measurable_fract).aestronglyMeasurable
  have hA_bound : ∀ t ∈ Ioi (1 : ℝ), ‖A t‖ ≤ 1 := fun t _ => by
    dsimp [A]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t)]
    exact (Int.fract_lt_one t).le
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  let G : ℂ → ℂ := fun z => z - z * (z - 1) * ∫ t in Ioi (1 : ℝ), A t * (t : ℂ) ^ (-(z + 1))
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_conn : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hG_diff : DifferentiableOn ℂ G U :=
    differentiableOn_id.sub
      ((differentiableOn_id.mul (differentiableOn_id.sub (differentiableOn_const 1))).mul
        (differentiableOn_dirichletIntegral zero_le_one hA_meas hA_bound))
  have hG_ana : AnalyticOnNhd ℂ G U := hG_diff.analyticOnNhd hU_open
  have hF_ana : AnalyticOnNhd ℂ (entireL χ) U := (analyticOnNhd_entireL χ).mono (Set.subset_univ U)
  have hEq_gt1 : ∀ z : ℂ, 1 < z.re → entireL χ z = G z := by
    intro z hz
    have hz_ne1 : z ≠ 1 := fun h => by rw [h] at hz; simp at hz
    have hL : χ.LFunction z = z * ∫ t in Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℂ)) * (t : ℂ) ^ (-(z + 1)) := by
      rw [DirichletCharacter.LFunction_eq_LSeries χ hz]
      have hchar : (fun n : ℕ => χ (n : ZMod 1)) = fun _ => (1 : ℂ) := by
        ext n; rw [h1]; simp
      rw [hchar]
      have hO : (fun n : ℕ => ∑ _k ∈ Finset.Icc 1 n, (1 : ℂ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
        refine Asymptotics.isBigO_iff.mpr ⟨1, Eventually.of_forall fun n => ?_⟩
        simp
      exact LSeries_eq_mul_integral (fun _ => (1 : ℂ)) zero_le_one hz
        (by simpa [← hchar] using DirichletCharacter.LSeriesSummable_of_one_lt_re χ hz) hO
    have hint_t : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-z)) (Ioi 1) :=
      integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one
    have hint_A : IntegrableOn (fun t : ℝ => A t * (t : ℂ) ^ (-(z + 1))) (Ioi 1) := by
      have hdom : IntegrableOn (fun t : ℝ => (1 : ℝ) * t ^ (-(z.re + 1))) (Ioi 1) :=
        (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul 1
      have hcp : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (-(z + 1))) (volume.restrict (Ioi 1)) :=
        ContinuousOn.aestronglyMeasurable
          (fun t ht => (Complex.continuousAt_ofReal_cpow_const _ _
            (Or.inr (zero_lt_one.trans ht).ne')).continuousWithinAt) measurableSet_Ioi
      refine hdom.mono' (hA_meas.mul hcp) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht)]
      have hre : (-(z + 1)).re = -(z.re + 1) := by simp
      rw [hre]
      exact mul_le_mul_of_nonneg_right (hA_bound t ht) (Real.rpow_nonneg (zero_lt_one.trans ht).le _)
    have hpt : ∀ t ∈ Ioi (1 : ℝ),
        (∑ _k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℂ)) * (t : ℂ) ^ (-(z + 1)) =
          (t : ℂ) ^ (-z) - A t * (t : ℂ) ^ (-(z + 1)) := by
      intro t ht
      have ht0 : 0 < t := zero_lt_one.trans ht
      have hfl : (∑ _k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℂ)) = (t : ℂ) - A t := by
        simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one, A]
        have hflR : ((⌊t⌋₊ : ℕ) : ℝ) = t - Int.fract t := by
          rw [Int.fract, ← Int.natCast_floor_eq_floor ht0.le, Int.cast_natCast]; ring
        exact_mod_cast hflR
      have hmul : (t : ℂ) * (t : ℂ) ^ (-(z + 1)) = (t : ℂ) ^ (-z) := by
        nth_rw 1 [← Complex.cpow_one (t : ℂ)]
        rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht0.ne')]
        congr 1; ring
      rw [hfl, sub_mul, hmul]
    rw [entireL_apply_of_ne_one χ hz_ne1]
    simp only [h1, ↓reduceIte]
    rw [← h1, hL, setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub hint_t hint_A,
        integral_Ioi_one_cpow_neg hz]
    dsimp [G]
    have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz_ne1
    field_simp [hz1]
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ), entireL χ z = G z := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : {z : ℂ | 1 < z.re} ∈ 𝓝[≠] (2 : ℂ) := mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds (by simp))
    exact (Filter.eventually_of_mem hmem hEq_gt1).frequently
  exact hF_ana.eqOn_of_preconnected_of_frequently_eq hG_ana hU_conn (by simp [U] : (2 : ℂ) ∈ U) hfreq hs

/-- Uniform polynomial growth bound in `Re(s) ≥ 1/16` (no functional equation or Phragmén–Lindelöf!). -/
theorem norm_entireL_le {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive)
    {s : ℂ} (hs : (1 : ℝ) / 16 ≤ s.re) :
    ‖entireL χ s‖ ≤ 17 * (d : ℝ) * (1 + ‖s‖) ^ 2 := by
  have hs0 : 0 < s.re := lt_of_lt_of_le (by norm_num) hs
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := Nat.one_le_cast.mpr (NeZero.pos d)
  by_cases h1 : χ = 1
  · rw [entireL_eq_integral_of_eq_one hprim h1 hs0]
    let A : ℝ → ℂ := fun t => ((Int.fract t : ℝ) : ℂ)
    have hA_meas : AEStronglyMeasurable A (volume.restrict (Ioi 1)) :=
      (Complex.continuous_ofReal.measurable.comp measurable_fract).aestronglyMeasurable
    have hA_bound : ∀ t ∈ Ioi (1 : ℝ), ‖A t‖ ≤ 1 := fun t _ => by
      dsimp [A]; rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t)]
      exact (Int.fract_lt_one t).le
    have hint := norm_dirichletIntegral_le zero_le_one hA_meas hA_bound hs
    have hsn : ‖s - 1‖ ≤ 1 + ‖s‖ := by
      have := norm_sub_le s 1; rw [norm_one] at this; linarith only [this]
    calc ‖s - s * (s - 1) * ∫ t in Ioi (1 : ℝ), A t * (t : ℂ) ^ (-(s + 1))‖
        ≤ ‖s‖ + ‖s * (s - 1) * ∫ t in Ioi (1 : ℝ), A t * (t : ℂ) ^ (-(s + 1))‖ := norm_sub_le _ _
      _ = ‖s‖ + ‖s‖ * ‖s - 1‖ * ‖∫ t in Ioi (1 : ℝ), A t * (t : ℂ) ^ (-(s + 1))‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ ‖s‖ + ‖s‖ * (1 + ‖s‖) * (16 * 1) :=
          add_le_add le_rfl (mul_le_mul (mul_le_mul_of_nonneg_left hsn (norm_nonneg s)) hint
            (norm_nonneg _) (by positivity))
      _ ≤ 17 * 1 * (1 + ‖s‖) ^ 2 := by nlinarith only [norm_nonneg s]
      _ ≤ 17 * (d : ℝ) * (1 + ‖s‖) ^ 2 := by nlinarith only [hd1, sq_nonneg (1 + ‖s‖)]
  · rw [entireL_eq_integral_of_ne_one h1 hs0, norm_mul]
    let A : ℝ → ℂ := fun t => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod d)
    have hA_meas : AEStronglyMeasurable A (volume.restrict (Ioi 1)) := by
      have hm : Measurable (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod d)) := measurable_of_countable _
      exact (hm.comp Nat.measurable_floor).aestronglyMeasurable
    have hA_bound : ∀ t ∈ Ioi (1 : ℝ), ‖A t‖ ≤ (d : ℝ) := fun t _ => norm_charPartialSum_le h1 ⌊t⌋₊
    have hint := norm_dirichletIntegral_le (Nat.cast_nonneg d) hA_meas hA_bound hs
    have hsn : ‖s‖ ≤ (1 + ‖s‖) ^ 2 := by nlinarith only [norm_nonneg s]
    calc ‖s‖ * ‖∫ t in Ioi (1 : ℝ), A t * (t : ℂ) ^ (-(s + 1))‖
        ≤ ‖s‖ * (16 * (d : ℝ)) := mul_le_mul_of_nonneg_left hint (norm_nonneg s)
      _ ≤ 17 * (d : ℝ) * (1 + ‖s‖) ^ 2 := by nlinarith only [hd1, hsn, norm_nonneg s]

/-- Uniform upper bound on `closedBall (2 + T * I) (31/16)`. -/
theorem norm_entireL_on_disk_le {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive)
    (T : ℝ) {z : ℂ} (hz : z ∈ Metric.closedBall (2 + (T : ℂ) * Complex.I) ((31 : ℝ) / 16)) :
    ‖entireL χ z‖ ≤ 425 * (d : ℝ) * (2 + |T|) ^ 2 := by
  have hdist : ‖z - (2 + (T : ℂ) * Complex.I)‖ ≤ 31 / 16 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hre : (1 : ℝ) / 16 ≤ z.re := by
    have h1 := (Complex.abs_re_le_norm (z - (2 + (T : ℂ) * Complex.I))).trans hdist
    have hsub : (z - (2 + (T : ℂ) * Complex.I)).re = z.re - 2 := by simp
    rw [hsub] at h1
    linarith only [(abs_le.mp h1).1]
  have hnorm_z : ‖z‖ ≤ 4 + |T| := by
    have h1 := norm_le_norm_sub_add z (2 + (T : ℂ) * Complex.I)
    have h2 : ‖(2 : ℂ) + (T : ℂ) * Complex.I‖ ≤ 2 + |T| := by
      calc ‖(2 : ℂ) + (T : ℂ) * Complex.I‖
          ≤ ‖(2 : ℂ)‖ + ‖(T : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = 2 + |T| := by rw [Complex.norm_ofNat, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    linarith only [h1, h2, hdist]
  have h1z : 1 + ‖z‖ ≤ 5 / 2 * (2 + |T|) := by linarith only [hnorm_z, abs_nonneg T]
  have hsq : (1 + ‖z‖) ^ 2 ≤ 25 * (2 + |T|) ^ 2 := by
    have hnn : 0 ≤ 1 + ‖z‖ := by positivity
    have hnn2 : 0 ≤ 2 + |T| := by positivity
    nlinarith only [h1z, hnn, hnn2]
  have hmain := norm_entireL_le hprim hre
  have hd_nn : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  calc ‖entireL χ z‖ ≤ 17 * (d : ℝ) * (1 + ‖z‖) ^ 2 := hmain
    _ ≤ 17 * (d : ℝ) * (25 * (2 + |T|) ^ 2) := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 425 * (d : ℝ) * (2 + |T|) ^ 2 := by ring

end CenterAndGrowthBounds

section JensenAndLocalPartialFraction

/-- Elementary lower bound `1 ≤ log(2 * d * (2 + |T|))` for `d ≥ 1`. -/
lemma one_le_log_two_mul_d_mul (d : ℕ) [NeZero d] (T : ℝ) :
    1 ≤ Real.log (2 * (d : ℝ) * (2 + |T|)) := by
  have hd : (1 : ℝ) ≤ d := Nat.one_le_cast.mpr (NeZero.pos d)
  have harg : Real.exp 1 ≤ 2 * (d : ℝ) * (2 + |T|) := by
    have he : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h4 : (4 : ℝ) ≤ 2 * (d : ℝ) * (2 + |T|) := by nlinarith only [hd, abs_nonneg T]
    exact le_trans he.le h4
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (2 * (d : ℝ) * (2 + |T|)) := Real.log_le_log (Real.exp_pos 1) harg

/-- `entireL χ` is nowhere locally identically zero. -/
lemma analyticOrderAt_entireL_ne_top {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (z : ℂ) :
    analyticOrderAt (entireL χ) z ≠ ⊤ := by
  intro htop
  have hev : entireL χ =ᶠ[𝓝 z] 0 := analyticOrderAt_eq_top.mp htop
  have hfreq : ∃ᶠ w in 𝓝[≠] z, entireL χ w = (0 : ℂ) :=
    (hev.filter_mono nhdsWithin_le_nhds).frequently
  have hzero := (analyticOnNhd_entireL χ).eqOn_of_preconnected_of_frequently_eq
    (analyticOnNhd_const (v := (0 : ℂ))) isPreconnected_univ (mem_univ z) hfreq (mem_univ (2 : ℂ))
  have hne := entireL_two_add_ne_zero χ 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hne
  exact hne hzero

lemma meromorphicOrderAt_entireL_eq {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (z : ℂ) :
    meromorphicOrderAt (entireL χ) z = (zeroMult χ z : ℤ) := by
  have hana : AnalyticAt ℂ (entireL χ) z := analyticOnNhd_entireL χ z (mem_univ z)
  rw [hana.meromorphicOrderAt_eq]
  have hnt := analyticOrderAt_entireL_ne_top χ z
  unfold zeroMult
  lift analyticOrderAt (entireL χ) z to ℕ using hnt with n hn
  simp

lemma meromorphicOrderAt_entireL_ne_top {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (z : ℂ) :
    meromorphicOrderAt (entireL χ) z ≠ ⊤ := by
  rw [meromorphicOrderAt_entireL_eq]
  exact WithTop.coe_ne_top

lemma zeroMult_eq_zero_iff {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (z : ℂ) :
    zeroMult χ z = 0 ↔ entireL χ z ≠ 0 := by
  have hana : AnalyticAt ℂ (entireL χ) z := analyticOnNhd_entireL χ z (mem_univ z)
  have hnt := analyticOrderAt_entireL_ne_top χ z
  unfold zeroMult
  rw [← hana.analyticOrderAt_eq_zero]
  lift analyticOrderAt (entireL χ) z to ℕ using hnt with n hn
  simp

lemma zeroMult_pos_iff {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (z : ℂ) :
    0 < zeroMult χ z ↔ entireL χ z = 0 := by
  rw [Nat.pos_iff_ne_zero, ne_eq, zeroMult_eq_zero_iff, not_not]

lemma divisor_entireL_apply {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) {U : Set ℂ}
    {z : ℂ} (hz : z ∈ U) :
    MeromorphicOn.divisor (entireL χ) U z = (zeroMult χ z : ℤ) := by
  have hm : MeromorphicOn (entireL χ) U := ((analyticOnNhd_entireL χ).mono (subset_univ U)).meromorphicOn
  rw [hm.divisor_apply hz, meromorphicOrderAt_entireL_eq]
  rfl

/-- Finite set of zeros of `entireL χ` in `closedBall c r`. -/
noncomputable def diskZeros {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (c : ℂ) (r : ℝ) : Finset ℂ :=
  ((MeromorphicOn.divisor (entireL χ) (closedBall c r)).finiteSupport (isCompact_closedBall c r)).toFinset

lemma mem_diskZeros_iff {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) {c : ℂ} {r : ℝ} {ρ : ℂ} :
    ρ ∈ diskZeros χ c r ↔ ρ ∈ closedBall c r ∧ entireL χ ρ = 0 := by
  unfold diskZeros
  rw [Set.Finite.mem_toFinset, Function.mem_support, ne_eq]
  by_cases hmem : ρ ∈ closedBall c r
  · rw [divisor_entireL_apply χ hmem]
    simp only [hmem, true_and, Nat.cast_eq_zero]
    rw [zeroMult_eq_zero_iff, not_not]
  · have hzero : MeromorphicOn.divisor (entireL χ) (closedBall c r) ρ = 0 := by
      rw [MeromorphicOn.divisor_def]
      simp [hmem]
    simp [hmem, hzero]

/-- Local Jensen zero count on `closedBall (2 + T*I) (15/8)`:
total multiplicity of zeros is at most `217 * log(2 * d * (2 + |T|))`. -/
theorem diskZeroCount_le {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) (T : ℝ) :
    (∑ ρ ∈ diskZeros χ (2 + (T : ℂ) * Complex.I) ((15 : ℝ) / 8), (zeroMult χ ρ : ℝ)) ≤
      217 * Real.log (2 * (d : ℝ) * (2 + |T|)) := by
  set c : ℂ := 2 + (T : ℂ) * Complex.I
  set r : ℝ := 15 / 8
  set R : ℝ := 31 / 16
  set M : ℝ := 425 * (d : ℝ) * (2 + |T|) ^ 2
  have hd : (1 : ℝ) ≤ d := Nat.one_le_cast.mpr (NeZero.pos d)
  have hM : 1 ≤ M := by
    dsimp [M]; nlinarith only [hd, abs_nonneg T]
  have hr_abs : |r| = r := abs_of_pos (by norm_num [r])
  have hR_abs : |R| = R := abs_of_pos (by norm_num [R])
  have hjensen := AnalyticOnNhd.sum_divisor_le (c := c) (r := r) (R := R) (M := M)
    (by rw [hr_abs]; norm_num [r]) (by rw [hr_abs, hR_abs]; norm_num [r, R]) hM
    ((analyticOnNhd_entireL χ).mono (subset_univ _))
    (entireL_two_add_ne_zero χ T)
    (fun z hz => norm_entireL_on_disk_le hprim T (by rw [hR_abs] at hz; exact sphere_subset_closedBall hz))
  have hsum_eq : (∑ᶠ u, MeromorphicOn.divisor (entireL χ) (closedBall c |r|) u : ℤ) =
      ∑ ρ ∈ diskZeros χ c r, (zeroMult χ ρ : ℤ) := by
    rw [hr_abs]
    have hsupp : (MeromorphicOn.divisor (entireL χ) (closedBall c r)).support ⊆ (diskZeros χ c r : Set ℂ) := by
      intro u hu
      exact Set.Finite.mem_toFinset _ |>.mpr hu
    rw [finsum_eq_sum_of_support_subset _ hsupp]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    exact divisor_entireL_apply χ ((mem_diskZeros_iff χ).mp hρ).1
  have hsum_cast : ((∑ᶠ u, MeromorphicOn.divisor (entireL χ) (closedBall c |r|) u : ℤ) : ℝ) =
      ∑ ρ ∈ diskZeros χ c r, (zeroMult χ ρ : ℝ) := by
    rw [hsum_eq]; push_cast; rfl
  rw [hsum_cast] at hjensen
  have hfc : (1 : ℝ) / 4 ≤ ‖entireL χ c‖ := norm_entireL_two_add_ge_quarter χ T
  have hfc_pos : 0 < ‖entireL χ c‖ := lt_of_lt_of_le (by norm_num) hfc
  have hdiv_le : M / ‖entireL χ c‖ ≤ 4 * M := by
    rw [div_le_iff₀ hfc_pos]
    have hM_pos : 0 ≤ M := by linarith only [hM]
    nlinarith only [hfc, hM_pos]
  have h4M_le : 4 * M ≤ (2 * (d : ℝ) * (2 + |T|)) ^ 7 := by
    have h2T : (2 : ℝ) ≤ 2 + |T| := by linarith only [abs_nonneg T]
    have hpow_d : (d : ℝ) ≤ (d : ℝ) ^ 7 := by
      have : (d : ℝ) ^ 1 ≤ (d : ℝ) ^ 7 := pow_le_pow_right₀ hd (by norm_num)
      simpa using this
    have hpow_T : 32 * (2 + |T|) ^ 2 ≤ (2 + |T|) ^ 7 := by
      have h5 : (32 : ℝ) ≤ (2 + |T|) ^ 5 := by
        calc (32 : ℝ) = 2 ^ 5 := by norm_num
          _ ≤ (2 + |T|) ^ 5 := pow_le_pow_left₀ (by norm_num) h2T 5
      calc 32 * (2 + |T|) ^ 2 ≤ (2 + |T|) ^ 5 * (2 + |T|) ^ 2 :=
            mul_le_mul_of_nonneg_right h5 (sq_nonneg _)
        _ = (2 + |T|) ^ 7 := by ring
    dsimp [M]
    have h1 : (2 * (d : ℝ) * (2 + |T|)) ^ 7 = 128 * (d : ℝ) ^ 7 * (2 + |T|) ^ 7 := by ring
    rw [h1]
    have h2 : 128 * (d : ℝ) * (32 * (2 + |T|) ^ 2) ≤ 128 * (d : ℝ) ^ 7 * (2 + |T|) ^ 7 := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hpow_d (by norm_num)) hpow_T
        (by positivity) (by positivity)
    nlinarith only [h2, hd, h2T, sq_nonneg (2 + |T|)]
  have hlog_num : Real.log (M / ‖entireL χ c‖) ≤ 7 * Real.log (2 * (d : ℝ) * (2 + |T|)) := by
    have hpos1 : 0 < M / ‖entireL χ c‖ := div_pos (by linarith only [hM]) hfc_pos
    calc Real.log (M / ‖entireL χ c‖)
        ≤ Real.log (4 * M) := Real.log_le_log hpos1 hdiv_le
      _ ≤ Real.log ((2 * (d : ℝ) * (2 + |T|)) ^ 7) := Real.log_le_log (by linarith only [hM]) h4M_le
      _ = 7 * Real.log (2 * (d : ℝ) * (2 + |T|)) := by rw [Real.log_pow]; norm_num
  have hlog_den : (1 : ℝ) / 31 ≤ Real.log (R / r) := by
    have hRr : R / r = 31 / 30 := by norm_num [R, r]
    rw [hRr]
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 30 / 31 by norm_num)
    have hinv : Real.log ((30 : ℝ) / 31) = -Real.log ((31 : ℝ) / 30) := by
      rw [← Real.log_inv]; norm_num
    linarith only [h1, hinv]
  have hlog_den_pos : 0 < Real.log (R / r) := lt_of_lt_of_le (by norm_num) hlog_den
  have hlog_L_nn : 0 ≤ Real.log (2 * (d : ℝ) * (2 + |T|)) := by
    linarith only [one_le_log_two_mul_d_mul d T]
  have hrhs : Real.log (M / ‖entireL χ c‖) / Real.log (R / r) ≤
      217 * Real.log (2 * (d : ℝ) * (2 + |T|)) := by
    rw [div_le_iff₀ hlog_den_pos]
    calc Real.log (M / ‖entireL χ c‖)
        ≤ 7 * Real.log (2 * (d : ℝ) * (2 + |T|)) := hlog_num
      _ = 217 * Real.log (2 * (d : ℝ) * (2 + |T|)) * (1 / 31) := by ring
      _ ≤ 217 * Real.log (2 * (d : ℝ) * (2 + |T|)) * Real.log (R / r) :=
          mul_le_mul_of_nonneg_left hlog_den (by positivity)
  exact hjensen.trans hrhs

/-- Under `DirichletGRH`, every zero of `entireL χ` in `Re(ρ) > 0` with `|Im(ρ) - T| ≤ 1`
lies in `diskZeros χ (2 + T*I) (15/8)`. -/
lemma mem_diskZeros_of_im_sub_le_one (hGRH : DirichletGRH) {d : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) (T : ℝ) {ρ : ℂ}
    (hre : 0 < ρ.re) (hzero : entireL χ ρ = 0) (him : |ρ.im - T| ≤ 1) :
    ρ ∈ diskZeros χ (2 + (T : ℂ) * Complex.I) ((15 : ℝ) / 8) := by
  rw [mem_diskZeros_iff]
  refine ⟨?_, hzero⟩
  have hhalf : ρ.re = 1 / 2 := entireL_re_eq_half_of_eq_zero hGRH hprim hre hzero
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hsq : ‖ρ - (2 + (T : ℂ) * Complex.I)‖ ^ 2 ≤ ((15 : ℝ) / 8) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have h1 : (ρ - (2 + (T : ℂ) * Complex.I)).re = -3 / 2 := by simp [hhalf]; norm_num
    have h2 : (ρ - (2 + (T : ℂ) * Complex.I)).im = ρ.im - T := by simp
    rw [h1, h2]
    have h3 : (ρ.im - T) ^ 2 ≤ 1 := by
      have h1 := (abs_le.mp him).1
      have h2 := (abs_le.mp him).2
      nlinarith only [h1, h2]
    nlinarith only [h3]
  have hnn : 0 ≤ ‖ρ - (2 + (T : ℂ) * Complex.I)‖ := norm_nonneg _
  nlinarith only [hsq, hnn]

/-- A1 acceptance criterion 1: any finite set `S` of zeros of `entireL χ` in `Re(ρ) > 0`
with `|Im(ρ) - T| ≤ 1` has total multiplicity `≤ 217 * log(2 * d * (2 + |T|))`. -/
theorem zeroCount_unit (hGRH : DirichletGRH) {d : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) (T : ℝ)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, 0 < ρ.re ∧ entireL χ ρ = 0 ∧ |ρ.im - T| ≤ 1) :
    (∑ ρ ∈ S, (zeroMult χ ρ : ℝ)) ≤ 217 * Real.log (2 * (d : ℝ) * (2 + |T|)) := by
  have hsub : S ⊆ diskZeros χ (2 + (T : ℂ) * Complex.I) ((15 : ℝ) / 8) := by
    intro ρ hρ
    obtain ⟨hre, hzero, him⟩ := hS ρ hρ
    exact mem_diskZeros_of_im_sub_le_one hGRH hprim T hre hzero him
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _).trans
    (diskZeroCount_le hprim T)

/-- Elementary Cauchy derivative bound on a closed disk: if `f` is holomorphic on `closedBall s R`
(`R > 0`) and `‖f z‖ ≤ M` on `sphere s R`, then `‖deriv f s‖ ≤ M / R`. -/
private lemma norm_deriv_le_of_sphere_bound {f : ℂ → ℂ} {s : ℂ} {R M : ℝ} (hR : 0 < R)
    (hdiff : DifferentiableOn ℂ f (closedBall s R))
    (hbound : ∀ z ∈ sphere s R, ‖f z‖ ≤ M) :
    ‖deriv f s‖ ≤ M / R := by
  have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hci : CircleIntegrable f s R :=
    (hdiff.continuousOn.mono sphere_subset_closedBall).circleIntegrable hR.le
  have heq : f =ᶠ[𝓝 s] fun w => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • ∮ z in C(s, R), (z - w)⁻¹ • f z := by
    filter_upwards [Metric.ball_mem_nhds s hR] with w hw
    have hformula := hdiff.circleIntegral_sub_inv_smul hw
    rw [hformula, inv_smul_smul₀ h2pi]
  have hs_not_mem : s ∉ sphere s |R| := by
    simp [abs_of_pos hR, hR.ne]
  have hder : HasDerivAt
      (fun w => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • ∮ z in C(s, R), (z - w)⁻¹ • f z)
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ • ∮ z in C(s, R), (z - s) ^ (-2 : ℤ) • f z) s :=
    (Complex.hasDerivAt_circleIntegral_sub_inv_smul hci hs_not_mem).const_smul
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹
  have hderiv_eq : deriv f s =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • ∮ z in C(s, R), (z - s) ^ (-2 : ℤ) • f z := by
    rw [heq.deriv_eq, hder.deriv]
  rw [hderiv_eq]
  have hnorm_le := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (f := fun z => (z - s) ^ (-2 : ℤ) • f z) hR.le
    (C := R⁻¹ ^ 2 * M) fun z hz => by
      have hzs : ‖z - s‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
      rw [smul_eq_mul, norm_mul, norm_zpow, hzs, show (-2 : ℤ) = -(2 : ℕ) by norm_num,
          zpow_neg, zpow_natCast, ← inv_pow]
      exact mul_le_mul_of_nonneg_left (hbound z hz) (by positivity)
  calc ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ • ∮ z in C(s, R), (z - s) ^ (-2 : ℤ) • f z‖
      ≤ R * (R⁻¹ ^ 2 * M) := hnorm_le
    _ = M / R := by field_simp [hR.ne']

/-- Logarithmic derivative of a finite product `∏ ρ ∈ Z, (z - ρ) ^ m ρ`. -/
private lemma hasDerivAt_finset_prod_sub_pow (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ)
    (hs : ∀ ρ ∈ Z, s ≠ ρ) :
    HasDerivAt (fun z : ℂ => ∏ ρ ∈ Z, (z - ρ) ^ m ρ)
      ((∏ ρ ∈ Z, (s - ρ) ^ m ρ) * ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)) s := by
  induction Z using Finset.cons_induction with
  | empty =>
    simpa using hasDerivAt_const s (1 : ℂ)
  | cons a S ha ih =>
    have hsa : s ≠ a := hs a (Finset.mem_cons_self a S)
    have hS : ∀ ρ ∈ S, s ≠ ρ := fun ρ hρ => hs ρ (Finset.mem_cons_of_mem hρ)
    have ih' := ih hS
    have hfac : HasDerivAt (fun z : ℂ => (z - a) ^ m a) ((m a : ℂ) * (s - a) ^ (m a - 1)) s := by
      simpa using ((hasDerivAt_id s).sub_const a).fun_pow (m a)
    have hmul := hfac.fun_mul ih'
    have hfun : (fun z : ℂ => ∏ ρ ∈ Finset.cons a S ha, (z - ρ) ^ m ρ) =
        fun z => (z - a) ^ m a * ∏ ρ ∈ S, (z - ρ) ^ m ρ := by
      ext z; exact Finset.prod_cons ha
    rw [hfun]
    refine hmul.congr_deriv ?_
    rw [Finset.prod_cons ha, Finset.sum_cons ha]
    have hsa0 : s - a ≠ 0 := sub_ne_zero.mpr hsa
    cases m a with
    | zero =>
      simp
    | succ k =>
      simp only [Nat.add_sub_cancel, pow_succ]
      field_simp [hsa0]

/-- Factor out all zeros of `entireL χ` in `closedBall c r`, producing an ENTIRE function `g`
nonvanishing on `closedBall c r` with `entireL χ z = (∏ ρ ∈ diskZeros χ c r, (z - ρ) ^ m_ρ) * g z`
for every `z : ℂ`. -/
lemma extract_zeros_on_closedBall {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (c : ℂ) (r : ℝ) :
    ∃ g : ℂ → ℂ,
      Differentiable ℂ g ∧
      (∀ z ∈ closedBall c r, g z ≠ 0) ∧
      (∀ z : ℂ, entireL χ z = (∏ ρ ∈ diskZeros χ c r, (z - ρ) ^ zeroMult χ ρ) * g z) := by
  set Z := diskZeros χ c r
  let D : ℂ → ℤ := fun ρ => if ρ ∈ Z then (zeroMult χ ρ : ℤ) else 0
  have hD_supp : D.HasFiniteSupport := by
    refine Z.finite_toSet.subset fun ρ hρ => ?_
    by_contra hnot
    have hnot' : ρ ∉ Z := hnot
    exact hρ (by simp [D, hnot'])
  let P : ℂ → ℂ := ∏ᶠ u, (· - u) ^ D u
  have hP_eval : ∀ z : ℂ, P z = ∏ ρ ∈ Z, (z - ρ) ^ zeroMult χ ρ := by
    intro z
    have hms : (fun u => (fun w : ℂ => (w - u) ^ D u)).mulSupport ⊆ (Z : Set ℂ) := by
      intro u hu
      by_contra hnot
      have hnot' : u ∉ Z := hnot
      apply hu
      ext w
      simp [D, hnot']
    have h1 : P = ∏ u ∈ Z, fun w : ℂ => (w - u) ^ D u :=
      finprod_eq_prod_of_mulSupport_subset _ hms
    rw [h1, Finset.prod_apply]
    refine Finset.prod_congr rfl fun ρ hρ => ?_
    simp [D, hρ]
  have hP_nf : MeromorphicNFOn P Set.univ := Function.FactorizedRational.meromorphicNFOn D Set.univ
  have hP : MeromorphicOn P Set.univ := hP_nf.meromorphicOn
  have hF : MeromorphicOn (entireL χ) Set.univ := (analyticOnNhd_entireL χ).meromorphicOn
  let g : ℂ → ℂ := toMeromorphicNFOn (P⁻¹ • entireL χ) Set.univ
  have hg_nf : MeromorphicNFOn g Set.univ := meromorphicNFOn_toMeromorphicNFOn (P⁻¹ • entireL χ) Set.univ
  have hP_ord : ∀ z : ℂ, meromorphicOrderAt P z = D z := fun z =>
    Function.FactorizedRational.meromorphicOrderAt_eq D hD_supp
  have hg_ord : ∀ z : ℂ, meromorphicOrderAt g z = (((zeroMult χ z : ℤ) - D z : ℤ) : WithTop ℤ) := by
    intro z
    have hcongr := (MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE (hP.inv.smul hF) (mem_univ z)).symm
    rw [← meromorphicOrderAt_congr hcongr,
        meromorphicOrderAt_smul (hP z (mem_univ z)).inv (hF z (mem_univ z)),
        meromorphicOrderAt_inv, hP_ord z, meromorphicOrderAt_entireL_eq χ z]
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add]
    congr 1; ring
  have hg_ana : AnalyticOnNhd ℂ g Set.univ := by
    rw [← hg_nf.divisor_nonneg_iff_analyticOnNhd]
    intro z
    show (0 : ℤ) ≤ MeromorphicOn.divisor g Set.univ z
    rw [hg_nf.meromorphicOn.divisor_apply (mem_univ z), hg_ord z, WithTop.untop₀_coe]
    dsimp [D]
    split_ifs <;> simp
  have hg_diff : Differentiable ℂ g :=
    Complex.analyticOnNhd_univ_iff_differentiable.mp hg_ana
  have hg_ne_zero : ∀ z ∈ closedBall c r, g z ≠ 0 := by
    intro z hz
    rw [← (hg_nf (mem_univ z)).meromorphicOrderAt_eq_zero_iff, hg_ord z]
    have hDz : D z = (zeroMult χ z : ℤ) := by
      dsimp [D]
      split_ifs with hmem
      · rfl
      · have hne : entireL χ z ≠ 0 := fun h0 => hmem ((mem_diskZeros_iff χ).mpr ⟨hz, h0⟩)
        rw [(zeroMult_eq_zero_iff χ z).mpr hne]; rfl
    rw [hDz, sub_self]; rfl
  have hfac : ∀ z : ℂ, entireL χ z = (∏ ρ ∈ Z, (z - ρ) ^ zeroMult χ ρ) * g z := by
    intro z
    have hP_cont : Continuous P := by
      have : P = fun w => ∏ ρ ∈ Z, (w - ρ) ^ zeroMult χ ρ := funext hP_eval
      rw [this]
      fun_prop
    have hEq_nhds : (fun w => P w * g w) =ᶠ[𝓝[≠] z] entireL χ := by
      have hZ_avoid : ∀ᶠ w in 𝓝[≠] z, w ∉ Z := by
        have hopen : IsOpen ((Z.erase z : Set ℂ)ᶜ) := (Z.erase z).finite_toSet.isClosed.isOpen_compl
        have hmem : z ∈ ((Z.erase z : Set ℂ)ᶜ) := by simp
        filter_upwards [mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hmem), self_mem_nhdsWithin] with w hw hne
        intro hwZ
        exact hw (Finset.mem_erase.mpr ⟨hne, hwZ⟩)
      filter_upwards [MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE (hP.inv.smul hF) (mem_univ z),
        hZ_avoid] with w hw hnotZ
      have hPw : P w ≠ 0 := by
        rw [hP_eval w]
        exact Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr fun h => hnotZ (h ▸ hρ))
      dsimp only [g]
      rw [hw]
      simp only [Pi.smul_apply', Pi.inv_apply, smul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ hPw, one_mul]
    have ht1 : Tendsto (fun w => P w * g w) (𝓝[≠] z) (𝓝 (P z * g z)) :=
      (hP_cont.mul hg_diff.continuous).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have ht2 : Tendsto (entireL χ) (𝓝[≠] z) (𝓝 (entireL χ z)) :=
      (differentiable_entireL χ).continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have heq := tendsto_nhds_unique (ht1.congr' hEq_nhds) ht2
    rw [← hP_eval z]
    exact heq.symm
  exact ⟨g, hg_diff, hg_ne_zero, hfac⟩

/-- Local partial-fraction approximation on `closedBall (2 + T*I) (7/4)` with error
`≤ 812000 * log(2 * d * (2 + |T|))`. -/
theorem local_negLogDeriv_approx {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    (hprim : χ.IsPrimitive) (T : ℝ) {s : ℂ}
    (hs : s ∈ closedBall (2 + (T : ℂ) * Complex.I) ((7 : ℝ) / 4))
    (hs1 : s ≠ 1) (hL : χ.LFunction s ≠ 0) :
    ‖negLogDerivL χ s -
        ((if χ = 1 then (1 : ℂ) / (s - 1) else 0) -
          ∑ ρ ∈ diskZeros χ (2 + (T : ℂ) * Complex.I) ((15 : ℝ) / 8),
            (zeroMult χ ρ : ℂ) / (s - ρ))‖ ≤
      812000 * Real.log (2 * (d : ℝ) * (2 + |T|)) := by
  set c : ℂ := 2 + (T : ℂ) * Complex.I
  set Z := diskZeros χ c ((15 : ℝ) / 8)
  set L_T : ℝ := Real.log (2 * (d : ℝ) * (2 + |T|))
  set M_T : ℝ := 425 * (d : ℝ) * (2 + |T|) ^ 2
  have hL_ge1 : 1 ≤ L_T := one_le_log_two_mul_d_mul d T
  have hL_pos : 0 < L_T := lt_of_lt_of_le zero_lt_one hL_ge1
  have hd : (1 : ℝ) ≤ d := Nat.one_le_cast.mpr (NeZero.pos d)
  have hMT_ge1 : 1 ≤ M_T := by dsimp [M_T]; nlinarith only [hd, abs_nonneg T]
  obtain ⟨g, hg_diff, hg_ne, hfac⟩ := extract_zeros_on_closedBall χ c ((15 : ℝ) / 8)
  set N : ℕ := ∑ ρ ∈ Z, zeroMult χ ρ
  have hN_le : (N : ℝ) ≤ 217 * L_T := by
    have := diskZeroCount_le hprim T
    simpa [N, Z, c, L_T] using this
  -- Step 1: Maximum modulus bound `‖g z‖ ≤ M_T * 16^N` on `closedBall c (31/16)`.
  have hg_bound : ∀ z ∈ closedBall c ((31 : ℝ) / 16), ‖g z‖ ≤ M_T * (16 : ℝ) ^ N := by
    intro z hz
    have hfront : ∀ w ∈ frontier (ball c ((31 : ℝ) / 16)), ‖g w‖ ≤ M_T * (16 : ℝ) ^ N := by
      intro w hw
      have hws : w ∈ sphere c ((31 : ℝ) / 16) := by
        simpa [frontier_ball] using hw
      have hwc : w ∈ closedBall c ((31 : ℝ) / 16) := sphere_subset_closedBall hws
      have hw_dist : ‖w - c‖ = 31 / 16 := by simpa [Metric.mem_sphere, dist_eq_norm] using hws
      have hP_ge : ((1 : ℝ) / 16) ^ N ≤ ‖∏ ρ ∈ Z, (w - ρ) ^ zeroMult χ ρ‖ := by
        rw [norm_prod]
        have h1 : ((1 : ℝ) / 16) ^ N = ∏ ρ ∈ Z, ((1 : ℝ) / 16) ^ zeroMult χ ρ := by
          simp [N, Finset.prod_pow_eq_pow_sum]
        rw [h1]
        refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun ρ hρ => ?_
        rw [norm_pow]
        have hρ_dist : ‖ρ - c‖ ≤ 15 / 8 := by
          have := ((mem_diskZeros_iff χ).mp hρ).1
          simpa [Metric.mem_closedBall, dist_eq_norm] using this
        have htri : (1 : ℝ) / 16 ≤ ‖w - ρ‖ := by
          have h' := norm_sub_le (w - ρ) (c - ρ)
          have h2 : (w - ρ) - (c - ρ) = w - c := by ring
          rw [h2, norm_sub_rev c ρ, hw_dist] at h'
          linarith only [h', hρ_dist]
        exact pow_le_pow_left₀ (by positivity) htri _
      have hFw := norm_entireL_on_disk_le hprim T hwc
      rw [hfac w, norm_mul] at hFw
      have hmul : ((1 : ℝ) / 16) ^ N * ‖g w‖ ≤ M_T :=
        (mul_le_mul_of_nonneg_right hP_ge (norm_nonneg _)).trans hFw
      have h16 : (16 : ℝ) ^ N * ((1 : ℝ) / 16) ^ N = 1 := by
        rw [← mul_pow]; norm_num
      calc ‖g w‖ = ((16 : ℝ) ^ N * ((1 : ℝ) / 16) ^ N) * ‖g w‖ := by rw [h16, one_mul]
        _ = (16 : ℝ) ^ N * (((1 : ℝ) / 16) ^ N * ‖g w‖) := by ring
        _ ≤ (16 : ℝ) ^ N * M_T := mul_le_mul_of_nonneg_left hmul (by positivity)
        _ = M_T * (16 : ℝ) ^ N := mul_comm _ _
    have hz_cl : z ∈ closure (ball c ((31 : ℝ) / 16)) := by
      rwa [closure_ball c (by norm_num : ((31 : ℝ) / 16) ≠ 0)]
    exact Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      hg_diff.diffContOnCl hfront hz_cl
  -- Step 2: Center lower bound `‖g c‖ ≥ 1 / (4 * 2^N)`.
  have hgc_ge : (1 : ℝ) / (4 * (2 : ℝ) ^ N) ≤ ‖g c‖ := by
    have hP_le : ‖∏ ρ ∈ Z, (c - ρ) ^ zeroMult χ ρ‖ ≤ (2 : ℝ) ^ N := by
      rw [norm_prod]
      have h1 : (2 : ℝ) ^ N = ∏ ρ ∈ Z, (2 : ℝ) ^ zeroMult χ ρ := by
        simp [N, Finset.prod_pow_eq_pow_sum]
      rw [h1]
      refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun ρ hρ => ?_
      rw [norm_pow]
      have hρ_dist : ‖c - ρ‖ ≤ 2 := by
        have := ((mem_diskZeros_iff χ).mp hρ).1
        rw [Metric.mem_closedBall, dist_comm, dist_eq_norm] at this
        linarith only [this]
      exact pow_le_pow_left₀ (norm_nonneg _) hρ_dist _
    have hFc := norm_entireL_two_add_ge_quarter χ T
    rw [hfac c, norm_mul] at hFc
    have h1 : (1 : ℝ) / 4 ≤ (2 : ℝ) ^ N * ‖g c‖ :=
      hFc.trans (mul_le_mul_of_nonneg_right hP_le (norm_nonneg _))
    rw [div_le_iff₀ (by positivity)]
    linarith only [h1]
  have hgc_ne : g c ≠ 0 := hg_ne c (mem_closedBall_self (by norm_num))
  -- Step 3: Construct normalized holomorphic logarithm `φ` of `g / g c` on `ball c (15/8)`.
  have hlogd_diff : DifferentiableOn ℂ (fun z => deriv g z / g z) (ball c ((15 : ℝ) / 8)) :=
    hg_diff.deriv.differentiableOn.div hg_diff.differentiableOn fun z hz =>
      hg_ne z (ball_subset_closedBall hz)
  obtain ⟨φ, hφc, hφ_der⟩ := hlogd_diff.isExactOn_ball.with_val_at c 0
  have hφ_diff : DifferentiableOn ℂ φ (ball c ((15 : ℝ) / 8)) := fun z hz =>
    (hφ_der z hz).differentiableAt.differentiableWithinAt
  have hexp_φ : ∀ z ∈ ball c ((15 : ℝ) / 8), Complex.exp (φ z) = g z / g c := by
    let ψ : ℂ → ℂ := fun z => g z * Complex.exp (-φ z)
    have hψ_der : ∀ z ∈ ball c ((15 : ℝ) / 8), HasDerivAt ψ 0 z := by
      intro z hz
      have hgz : g z ≠ 0 := hg_ne z (ball_subset_closedBall hz)
      have h1 := (hg_diff z).hasDerivAt
      have h2 := (hφ_der z hz).neg.cexp
      convert h1.mul h2 using 1
      field_simp [hgz]
      ring
    intro z hz
    have hdist0 : ‖ψ z - ψ c‖ ≤ 0 * ‖z - c‖ :=
      (convex_ball c ((15 : ℝ) / 8)).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun w hw => (hψ_der w hw).hasDerivWithinAt)
        (fun _ _ => by simp)
        (mem_ball_self (by norm_num)) hz
    rw [zero_mul] at hdist0
    have hψ_eq : ψ z = ψ c := sub_eq_zero.mp (norm_le_zero_iff.mp hdist0)
    have hψc : ψ c = g c := by simp [ψ, hφc]
    rw [hψc] at hψ_eq
    have hexp_ne : Complex.exp (φ z) ≠ 0 := Complex.exp_ne_zero _
    rw [eq_div_iff hgc_ne]
    calc Complex.exp (φ z) * g c = Complex.exp (φ z) * (g z * Complex.exp (-φ z)) := by rw [← hψ_eq]
      _ = g z * (Complex.exp (φ z) * Complex.exp (-φ z)) := by ring
      _ = g z := by rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  -- Step 4: Upper bound `(φ z).re ≤ 875 * L_T` on `ball c (15/8)`.
  have h4M_le : 4 * M_T ≤ (2 * (d : ℝ) * (2 + |T|)) ^ 7 := by
    have h2T : (2 : ℝ) ≤ 2 + |T| := by linarith only [abs_nonneg T]
    have hpow_d : (d : ℝ) ≤ (d : ℝ) ^ 7 := by
      simpa using pow_le_pow_right₀ hd (show 1 ≤ 7 by norm_num)
    have hpow_T : 32 * (2 + |T|) ^ 2 ≤ (2 + |T|) ^ 7 := by
      have h5 : (32 : ℝ) ≤ (2 + |T|) ^ 5 := by
        calc (32 : ℝ) = 2 ^ 5 := by norm_num
          _ ≤ (2 + |T|) ^ 5 := pow_le_pow_left₀ (by norm_num) h2T 5
      calc 32 * (2 + |T|) ^ 2 ≤ (2 + |T|) ^ 5 * (2 + |T|) ^ 2 :=
            mul_le_mul_of_nonneg_right h5 (sq_nonneg _)
        _ = (2 + |T|) ^ 7 := by ring
    dsimp [M_T]
    have h1 : (2 * (d : ℝ) * (2 + |T|)) ^ 7 = 128 * (d : ℝ) ^ 7 * (2 + |T|) ^ 7 := by ring
    rw [h1]
    have h2 : 128 * (d : ℝ) * (32 * (2 + |T|) ^ 2) ≤ 128 * (d : ℝ) ^ 7 * (2 + |T|) ^ 7 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpow_d (by norm_num)) hpow_T (by positivity) (by positivity)
    nlinarith only [h2, hd, h2T, sq_nonneg (2 + |T|)]
  have hlog32 : Real.log 32 ≤ 4 := by
    have h32 : (32 : ℝ) ≤ Real.exp 4 := by
      have he : (2.7 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) Real.exp_one_gt_d9.le
      calc (32 : ℝ) ≤ (2.7 : ℝ) ^ 4 := by norm_num
        _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) he 4
        _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
    calc Real.log 32 ≤ Real.log (Real.exp 4) := Real.log_le_log (by norm_num) h32
      _ = 4 := Real.log_exp 4
  have hre_bound : ∀ z ∈ ball c ((15 : ℝ) / 8), (φ z).re ≤ 875 * L_T := by
    intro z hz
    have hzc : z ∈ closedBall c ((31 : ℝ) / 16) :=
      ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num)) hz
    have hratio : ‖g z / g c‖ ≤ 4 * M_T * (32 : ℝ) ^ N := by
      rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hgc_ne)]
      have h1 := hg_bound z hzc
      have h2 : 4 * M_T * (32 : ℝ) ^ N * (1 / (4 * (2 : ℝ) ^ N)) = M_T * (16 : ℝ) ^ N := by
        have h32 : (32 : ℝ) ^ N = (16 : ℝ) ^ N * (2 : ℝ) ^ N := by rw [← mul_pow]; norm_num
        rw [h32]; field_simp
      calc ‖g z‖ ≤ M_T * (16 : ℝ) ^ N := h1
        _ = 4 * M_T * (32 : ℝ) ^ N * (1 / (4 * (2 : ℝ) ^ N)) := h2.symm
        _ ≤ 4 * M_T * (32 : ℝ) ^ N * ‖g c‖ :=
            mul_le_mul_of_nonneg_left hgc_ge (by positivity)
    have hexp_le : Real.exp (φ z).re ≤ 4 * M_T * (32 : ℝ) ^ N := by
      rw [← Complex.norm_exp, hexp_φ z hz]
      exact hratio
    have hlog_le : (φ z).re ≤ Real.log (4 * M_T * (32 : ℝ) ^ N) := by
      rw [← Real.log_exp (φ z).re]
      exact Real.log_le_log (Real.exp_pos _) hexp_le
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog_le
    have hlog4M : Real.log (4 * M_T) ≤ 7 * L_T := by
      calc Real.log (4 * M_T) ≤ Real.log ((2 * (d : ℝ) * (2 + |T|)) ^ 7) :=
            Real.log_le_log (by positivity) h4M_le
        _ = 7 * L_T := by rw [Real.log_pow]; norm_num; rfl
    have hNlog : (N : ℝ) * Real.log 32 ≤ 868 * L_T := by
      calc (N : ℝ) * Real.log 32 ≤ (217 * L_T) * 4 :=
            mul_le_mul hN_le hlog32 (Real.log_nonneg (by norm_num)) (by positivity)
        _ = 868 * L_T := by ring
    linarith only [hlog_le, hlog4M, hNlog]
  -- Step 5: Borel–Carathéodory on `closedBall c (29/16)`.
  have hφ_norm : ∀ w ∈ closedBall c ((29 : ℝ) / 16), ‖φ w‖ ≤ 50750 * L_T := by
    intro w hw
    have hshift_diff : DifferentiableOn ℂ (fun z => φ (c + z)) (ball 0 ((15 : ℝ) / 8)) := by
      refine hφ_diff.comp (differentiableOn_const c |>.add differentiableOn_id) fun z hz => ?_
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hshift_re : Set.MapsTo (fun z => φ (c + z)) (ball 0 ((15 : ℝ) / 8)) {z | z.re ≤ 875 * L_T} := by
      intro z hz
      exact hre_bound (c + z) (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
    have hwc_norm : ‖w - c‖ ≤ 29 / 16 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
    have hwc_mem : w - c ∈ ball (0 : ℂ) ((15 : ℝ) / 8) := by
      rw [Metric.mem_ball, dist_zero_right]
      linarith only [hwc_norm]
    have hbc := Complex.borelCaratheodory_zero (f := fun z => φ (c + z)) (M := 875 * L_T)
      (by positivity) hshift_diff hshift_re (by norm_num) hwc_mem (by simpa using hφc)
    have hadd : c + (w - c) = w := by ring
    rw [hadd] at hbc
    have hden : (1 : ℝ) / 16 ≤ 15 / 8 - ‖w - c‖ := by linarith only [hwc_norm]
    calc ‖φ w‖ ≤ 2 * (875 * L_T) * ‖w - c‖ / (15 / 8 - ‖w - c‖) := hbc
      _ ≤ 2 * (875 * L_T) * (29 / 16) / (1 / 16) :=
          div_le_div₀ (by positivity)
            (mul_le_mul_of_nonneg_left hwc_norm (by positivity))
            (by norm_num) hden
      _ = 50750 * L_T := by ring
  -- Step 6: Cauchy derivative estimate on `closedBall s (1/16) ⊆ closedBall c (29/16)`.
  have hsub_disk : closedBall s ((1 : ℝ) / 16) ⊆ closedBall c ((29 : ℝ) / 16) := by
    intro w hw
    have h1 : dist s c ≤ 7 / 4 := Metric.mem_closedBall.mp hs
    have h2 : dist w s ≤ 1 / 16 := Metric.mem_closedBall.mp hw
    rw [Metric.mem_closedBall]
    linarith only [dist_triangle w s c, h1, h2]
  have hφ_diff_s : DifferentiableOn ℂ φ (closedBall s ((1 : ℝ) / 16)) :=
    hφ_diff.mono (hsub_disk.trans (closedBall_subset_ball (by norm_num)))
  have hderiv_φ_le : ‖deriv φ s‖ ≤ 812000 * L_T := by
    have h := norm_deriv_le_of_sphere_bound (show (0 : ℝ) < 1 / 16 by norm_num) hφ_diff_s
      fun w hw => hφ_norm w (hsub_disk (sphere_subset_closedBall hw))
    linarith only [h]
  -- Step 7: Identify `negLogDerivL χ s - (principal - zeroSum) = -deriv φ s`.
  have hs_ball : s ∈ ball c ((15 : ℝ) / 8) :=
    closedBall_subset_ball (by norm_num : (7 : ℝ) / 4 < 15 / 8) hs
  have hderiv_φ_eq : deriv φ s = deriv g s / g s := (hφ_der s hs_ball).deriv
  have hFs_ne : entireL χ s ≠ 0 := by
    rw [entireL_apply_of_ne_one χ hs1]
    split_ifs
    · exact mul_ne_zero (sub_ne_zero.mpr hs1) hL
    · exact hL
  have hs_ne_Z : ∀ ρ ∈ Z, s ≠ ρ := by
    intro ρ hρ heq
    subst heq
    exact hFs_ne ((mem_diskZeros_iff χ).mp hρ).2
  have hF_deriv : deriv (entireL χ) s / entireL χ s =
      (∑ ρ ∈ Z, (zeroMult χ ρ : ℂ) / (s - ρ)) + deriv g s / g s := by
    have hP_der := hasDerivAt_finset_prod_sub_pow Z (zeroMult χ) s hs_ne_Z
    have hmul_der := hP_der.mul (hg_diff s).hasDerivAt
    have hfun : entireL χ = fun z => (∏ ρ ∈ Z, (z - ρ) ^ zeroMult χ ρ) * g z := funext hfac
    have hder_eq : deriv (entireL χ) s =
        (∏ ρ ∈ Z, (s - ρ) ^ zeroMult χ ρ) * (∑ ρ ∈ Z, (zeroMult χ ρ : ℂ) / (s - ρ)) * g s +
          (∏ ρ ∈ Z, (s - ρ) ^ zeroMult χ ρ) * deriv g s := by
      rw [hfun]; exact hmul_der.deriv
    have hPs_ne : (∏ ρ ∈ Z, (s - ρ) ^ zeroMult χ ρ) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr (hs_ne_Z ρ hρ))
    have hgs_ne : g s ≠ 0 := hg_ne s (ball_subset_closedBall hs_ball)
    have hfac_s : entireL χ s = (∏ ρ ∈ Z, (s - ρ) ^ zeroMult χ ρ) * g s := hfac s
    rw [hder_eq, hfac_s]
    field_simp [hPs_ne, hgs_ne]
  have hdiff_eq : negLogDerivL χ s -
      ((if χ = 1 then (1 : ℂ) / (s - 1) else 0) -
        ∑ ρ ∈ Z, (zeroMult χ ρ : ℂ) / (s - ρ)) = -deriv φ s := by
    rw [negLogDerivL_eq_of_ne_one χ hs1 hL, hF_deriv, hderiv_φ_eq]
    ring
  rw [hdiff_eq, norm_neg]
  exact hderiv_φ_le

end JensenAndLocalPartialFraction

section VerticalAndHorizontalBounds

/-- A1 acceptance criterion 2: single-logarithm bound on the left vertical contour `Re(s) = 1/4`. -/
theorem negLogDeriv_quarter (hGRH : DirichletGRH) {d : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) (u : ℝ) :
    ‖negLogDerivL χ ((1 / 4 : ℝ) + (u : ℂ) * Complex.I)‖ ≤
      812870 * Real.log (2 * (d : ℝ) * (2 + |u|)) := by
  set s : ℂ := ((1 / 4 : ℝ) : ℂ) + (u : ℂ) * Complex.I
  set c : ℂ := 2 + (u : ℂ) * Complex.I
  set Z := diskZeros χ c ((15 : ℝ) / 8)
  set L_u : ℝ := Real.log (2 * (d : ℝ) * (2 + |u|))
  have hL_ge1 : 1 ≤ L_u := one_le_log_two_mul_d_mul d u
  have hs_re : s.re = 1 / 4 := by simp [s]
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs_re; norm_num at hs_re
  have hs_disk : s ∈ closedBall c ((7 : ℝ) / 4) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsub : s - c = ((-7 / 4 : ℝ) : ℂ) := by simp [s, c]; norm_num
    rw [hsub, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  have hFs_ne : entireL χ s ≠ 0 := by
    intro h0
    have := entireL_re_eq_half_of_eq_zero hGRH hprim (by linarith : 0 < s.re) h0
    linarith only [hs_re, this]
  have hLs_ne : χ.LFunction s ≠ 0 := by
    intro h0
    apply hFs_ne
    rw [entireL_apply_of_ne_one χ hs1, h0]
    split_ifs <;> simp
  have happrox := local_negLogDeriv_approx hprim u hs_disk hs1 hLs_ne
  have hprinc : ‖if χ = 1 then (1 : ℂ) / (s - 1) else 0‖ ≤ 2 * L_u := by
    split_ifs
    · rw [norm_div, norm_one]
      have hre : (3 : ℝ) / 4 ≤ ‖s - 1‖ := by
        have h1 : (s - 1).re = -3 / 4 := by simp [s]; norm_num
        calc (3 : ℝ) / 4 = |(s - 1).re| := by rw [h1]; norm_num
          _ ≤ ‖s - 1‖ := Complex.abs_re_le_norm (s - 1)
      have hdiv : 1 / ‖s - 1‖ ≤ 4 / 3 := by
        rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) hre)]
        linarith only [hre]
      linarith only [hdiv, hL_ge1]
    · rw [norm_zero]; linarith only [hL_ge1]
  have hzeros : ‖∑ ρ ∈ Z, (zeroMult χ ρ : ℂ) / (s - ρ)‖ ≤ 868 * L_u := by
    calc ‖∑ ρ ∈ Z, (zeroMult χ ρ : ℂ) / (s - ρ)‖
        ≤ ∑ ρ ∈ Z, ‖(zeroMult χ ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z, 4 * (zeroMult χ ρ : ℝ) := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          obtain ⟨hρ_disk, hρ_zero⟩ := (mem_diskZeros_iff χ).mp hρ
          have hρ_re_pos : 0 < ρ.re := by
            have hdist : ‖ρ - c‖ ≤ 15 / 8 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hρ_disk
            have h1 := (Complex.abs_re_le_norm (ρ - c)).trans hdist
            have h2 : (ρ - c).re = ρ.re - 2 := by simp [c]
            rw [h2] at h1
            linarith only [(abs_le.mp h1).1]
          have hρ_half : ρ.re = 1 / 2 := entireL_re_eq_half_of_eq_zero hGRH hprim hρ_re_pos hρ_zero
          have hdist_ge : (1 : ℝ) / 4 ≤ ‖s - ρ‖ := by
            have hsub : (s - ρ).re = -1 / 4 := by simp [hs_re, hρ_half]; norm_num
            calc (1 : ℝ) / 4 = |(s - ρ).re| := by rw [hsub]; norm_num
              _ ≤ ‖s - ρ‖ := Complex.abs_re_le_norm (s - ρ)
          rw [norm_div, Complex.norm_natCast, div_le_iff₀ (lt_of_lt_of_le (by norm_num) hdist_ge)]
          nlinarith only [hdist_ge, Nat.cast_nonneg (α := ℝ) (zeroMult χ ρ)]
      _ = 4 * ∑ ρ ∈ Z, (zeroMult χ ρ : ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ 4 * (217 * L_u) := mul_le_mul_of_nonneg_left (diskZeroCount_le hprim u) (by norm_num)
      _ = 868 * L_u := by ring
  have htri := norm_le_norm_sub_add (negLogDerivL χ s)
    ((if χ = 1 then (1 : ℂ) / (s - 1) else 0) - ∑ ρ ∈ Z, (zeroMult χ ρ : ℂ) / (s - ρ))
  have htri2 := norm_sub_le (if χ = 1 then (1 : ℂ) / (s - 1) else 0)
    (∑ ρ ∈ Z, (zeroMult χ ρ : ℂ) / (s - ρ))
  linarith only [htri, htri2, happrox, hprinc, hzeros]

/-- Helper for `exists_good_height`: horizontal bound on `Im(s) = τ` once `τ` stays at least
`δ = 1 / (2 * M)` away from all zero imaginary parts in `diskZeros χ (2 + τ*I) (15/8)`. -/
private lemma good_height_horizontal_bound {d : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) {T τ : ℝ} (hT_ge2 : (2 : ℝ) ≤ T)
    (hτ_abs : |τ| = T) {M : ℕ} (hM_pos : 0 < M)
    (h2M_le : 2 * (M : ℝ) ≤ 13890 * Real.log (2 * (d : ℝ) * (2 + T)))
    (havoid : ∀ ρ ∈ diskZeros χ (2 + (τ : ℂ) * Complex.I) ((15 : ℝ) / 8),
      1 / (2 * (M : ℝ)) ≤ |τ - ρ.im|)
    (hno_zero : ∀ σ ∈ Icc ((1 : ℝ) / 4) 2, entireL χ ((σ : ℂ) + (τ : ℂ) * Complex.I) ≠ 0) :
    ∀ σ ∈ Icc ((1 : ℝ) / 4) 2,
      ‖negLogDerivL χ ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
        4000000 * (Real.log (2 * (d : ℝ) * (2 + T))) ^ 2 := by
  intro σ hσ
  set s : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I
  set c : ℂ := 2 + (τ : ℂ) * Complex.I
  set Z := diskZeros χ c ((15 : ℝ) / 8)
  set L_T : ℝ := Real.log (2 * (d : ℝ) * (2 + T))
  have hM_posR : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM_pos
  have hδ_pos : (0 : ℝ) < 1 / (2 * (M : ℝ)) := by positivity
  have hLT_eq : Real.log (2 * (d : ℝ) * (2 + |τ|)) = L_T := by rw [hτ_abs]
  have hLT_ge1 : 1 ≤ L_T := by
    have := one_le_log_two_mul_d_mul d τ
    rwa [hLT_eq] at this
  have hs_disk : s ∈ closedBall c ((7 : ℝ) / 4) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsub : s - c = ((σ - 2 : ℝ) : ℂ) := by simp [s, c]
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith only [hσ.1, hσ.2]
  have hs1 : s ≠ 1 := by
    intro h
    have him : s.im = 0 := by rw [h]; simp
    have hs_im : s.im = τ := by simp [s]
    have hT0 : T = 0 := by rw [← hτ_abs, ← hs_im, him, abs_zero]
    linarith only [hT0, hT_ge2]
  have hFs_ne : entireL χ s ≠ 0 := hno_zero σ hσ
  have hLs_ne : χ.LFunction s ≠ 0 := by
    intro h0
    apply hFs_ne
    rw [entireL_apply_of_ne_one χ hs1, h0]
    split_ifs <;> simp
  have happrox : ‖negLogDerivL χ s -
      ((if χ = 1 then (1 : ℂ) / (s - 1) else 0) -
        ∑ ρ ∈ Z, (zeroMult χ ρ : ℂ) / (s - ρ))‖ ≤ 812000 * L_T := by
    have h := local_negLogDeriv_approx hprim τ hs_disk hs1 hLs_ne
    rwa [hLT_eq] at h
  have hprinc : ‖if χ = 1 then (1 : ℂ) / (s - 1) else 0‖ ≤ L_T ^ 2 := by
    split_ifs
    · rw [norm_div, norm_one]
      have him_ge : (2 : ℝ) ≤ ‖s - 1‖ := by
        have h1 : (s - 1).im = τ := by simp [s]
        calc (2 : ℝ) ≤ T := hT_ge2
          _ = |(s - 1).im| := by rw [h1, hτ_abs]
          _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm (s - 1)
      have hdiv : 1 / ‖s - 1‖ ≤ 1 := by
        rw [div_le_one (lt_of_lt_of_le (by norm_num) him_ge)]; linarith only [him_ge]
      nlinarith only [hdiv, hLT_ge1]
    · rw [norm_zero]; positivity
  have hzeros : ‖∑ ρ ∈ Z, (zeroMult χ ρ : ℂ) / (s - ρ)‖ ≤ 3014130 * L_T ^ 2 := by
    calc ‖∑ ρ ∈ Z, (zeroMult χ ρ : ℂ) / (s - ρ)‖
        ≤ ∑ ρ ∈ Z, ‖(zeroMult χ ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z, (2 * (M : ℝ)) * (zeroMult χ ρ : ℝ) := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          have hδ_le : 1 / (2 * (M : ℝ)) ≤ ‖s - ρ‖ := by
            have hsub : (s - ρ).im = τ - ρ.im := by simp [s]
            calc 1 / (2 * (M : ℝ)) ≤ |(s - ρ).im| := by rw [hsub]; exact havoid ρ hρ
              _ ≤ ‖s - ρ‖ := Complex.abs_im_le_norm (s - ρ)
          rw [norm_div, Complex.norm_natCast, div_le_iff₀ (lt_of_lt_of_le hδ_pos hδ_le)]
          have hinv : 2 * (M : ℝ) * (1 / (2 * (M : ℝ))) = 1 := by field_simp [hM_posR.ne']
          have hmul := mul_le_mul_of_nonneg_left hδ_le (by positivity : 0 ≤ 2 * (M : ℝ))
          rw [hinv] at hmul
          nlinarith only [hmul, Nat.cast_nonneg (α := ℝ) (zeroMult χ ρ)]
      _ = (2 * (M : ℝ)) * ∑ ρ ∈ Z, (zeroMult χ ρ : ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ (13890 * L_T) * (217 * L_T) := by
          have hcnt := diskZeroCount_le hprim τ
          rw [hLT_eq] at hcnt
          exact mul_le_mul h2M_le hcnt (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
            (by linarith only [hLT_ge1])
      _ = 3014130 * L_T ^ 2 := by ring
  have htri := norm_le_norm_sub_add (negLogDerivL χ s)
    ((if χ = 1 then (1 : ℂ) / (s - 1) else 0) - ∑ ρ ∈ Z, (zeroMult χ ρ : ℂ) / (s - ρ))
  have htri2 := norm_sub_le (if χ = 1 then (1 : ℂ) / (s - 1) else 0)
    (∑ ρ ∈ Z, (zeroMult χ ρ : ℂ) / (s - ρ))
  have hLT_le_sq : L_T ≤ L_T ^ 2 := by nlinarith only [hLT_ge1]
  linarith only [htri, htri2, happrox, hprinc, hzeros, hLT_le_sq, sq_nonneg L_T]

/-- Helper for `exists_good_height`: discrete pigeonhole picks `T ∈ [j, j + 1]` staying at least
`1 / (2 * (2 * Z.card + 1))` away from `±ρ.im` for every `ρ ∈ Z`. -/
private lemma exists_pigeonhole_height (j : ℕ) (Z : Finset ℂ) :
    ∃ T ∈ Icc (j : ℝ) (j + 1),
      ∀ ρ ∈ Z, 1 / (2 * ((2 * Z.card + 1 : ℕ) : ℝ)) ≤ |T - ρ.im| ∧
               1 / (2 * ((2 * Z.card + 1 : ℕ) : ℝ)) ≤ |-T - ρ.im| := by
  set M : ℕ := 2 * Z.card + 1
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
  let t : ℕ → ℝ := fun m => (j : ℝ) + (m : ℝ) / (M : ℝ)
  set δ : ℝ := 1 / (2 * (M : ℝ))
  have huniq : ∀ y : ℝ, ((Finset.range (M + 1)).filter fun m => |t m - y| < δ).card ≤ 1 := by
    intro y
    refine Finset.card_le_one.mpr fun m₁ hm₁ m₂ hm₂ => ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hm₁ hm₂
    by_contra hne
    have hdiff_ge : (1 : ℝ) / (M : ℝ) ≤ |t m₁ - t m₂| := by
      have htm : t m₁ - t m₂ = ((m₁ : ℝ) - (m₂ : ℝ)) / (M : ℝ) := by dsimp [t]; ring
      rw [htm, abs_div, abs_of_pos hM_pos]
      refine div_le_div_of_nonneg_right ?_ hM_pos.le
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hneg : (m₁ : ℝ) - (m₂ : ℝ) < 0 := sub_neg.mpr (Nat.cast_lt.mpr hlt)
        rw [abs_of_neg hneg]
        have hle : (m₁ : ℝ) + 1 ≤ (m₂ : ℝ) := by exact_mod_cast (show m₁ + 1 ≤ m₂ by omega)
        linarith only [hle]
      · have hpos : 0 < (m₁ : ℝ) - (m₂ : ℝ) := sub_pos.mpr (Nat.cast_lt.mpr hgt)
        rw [abs_of_pos hpos]
        have hle : (m₂ : ℝ) + 1 ≤ (m₁ : ℝ) := by exact_mod_cast (show m₂ + 1 ≤ m₁ by omega)
        linarith only [hle]
    have htri : |t m₁ - t m₂| ≤ |t m₁ - y| + |t m₂ - y| := by
      have : t m₁ - t m₂ = (t m₁ - y) - (t m₂ - y) := by ring
      rw [this]; exact abs_sub _ _
    have h2δ : 2 * δ = 1 / (M : ℝ) := by dsimp [δ]; field_simp [hM_pos.ne']
    linarith only [hdiff_ge, htri, hm₁.2, hm₂.2, h2δ]
  let badIdx : Finset ℕ :=
    Z.biUnion fun ρ =>
      ((Finset.range (M + 1)).filter fun m => |t m - ρ.im| < δ) ∪
      ((Finset.range (M + 1)).filter fun m => |t m - (-ρ.im)| < δ)
  have hbad_lt : badIdx.card < (Finset.range (M + 1)).card := by
    have h1 : badIdx.card ≤ ∑ ρ ∈ Z,
        (((Finset.range (M + 1)).filter fun m => |t m - ρ.im| < δ) ∪
         ((Finset.range (M + 1)).filter fun m => |t m - (-ρ.im)| < δ)).card :=
      Finset.card_biUnion_le
    have h2 : (∑ ρ ∈ Z,
        (((Finset.range (M + 1)).filter fun m => |t m - ρ.im| < δ) ∪
         ((Finset.range (M + 1)).filter fun m => |t m - (-ρ.im)| < δ)).card) ≤
        ∑ _ρ ∈ Z, 2 :=
      Finset.sum_le_sum fun ρ _ =>
        (Finset.card_union_le _ _).trans (Nat.add_le_add (huniq ρ.im) (huniq (-ρ.im)))
    have h3 : (∑ _ρ ∈ Z, 2) = 2 * Z.card := by simp [mul_comm]
    rw [Finset.card_range]
    omega
  obtain ⟨m₀, hm₀_mem, hm₀_not_bad⟩ : ∃ m₀ ∈ Finset.range (M + 1), m₀ ∉ badIdx := by
    by_contra hall
    push Not at hall
    have hsub : Finset.range (M + 1) ⊆ badIdx := fun m hm => hall m hm
    exact Nat.not_lt.mpr (Finset.card_le_card hsub) hbad_lt
  refine ⟨t m₀, ?_, ?_⟩
  · have hm₀_le : m₀ ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm₀_mem)
    have hdiv_le : (m₀ : ℝ) / (M : ℝ) ≤ 1 := (div_le_one hM_pos).mpr (Nat.cast_le.mpr hm₀_le)
    exact ⟨by dsimp [t]; linarith [div_nonneg (Nat.cast_nonneg m₀) hM_pos.le],
           by dsimp [t]; linarith only [hdiv_le]⟩
  · intro ρ hρ
    constructor
    · by_contra hlt
      push Not at hlt
      apply hm₀_not_bad
      refine Finset.mem_biUnion.mpr ⟨ρ, hρ, Finset.mem_union_left _ ?_⟩
      exact Finset.mem_filter.mpr ⟨hm₀_mem, hlt⟩
    · by_contra hlt
      push Not at hlt
      apply hm₀_not_bad
      refine Finset.mem_biUnion.mpr ⟨ρ, hρ, Finset.mem_union_right _ ?_⟩
      refine Finset.mem_filter.mpr ⟨hm₀_mem, ?_⟩
      have heq : |t m₀ - -ρ.im| = |-t m₀ - ρ.im| := by
        rw [← abs_neg (-t m₀ - ρ.im)]; ring_nf
      rwa [heq]

/-- A1 acceptance criterion 3: for every `j ≥ 2`, there exists a good height `T ∈ [j, j + 1]`
such that neither horizontal line `Im(s) = ±T` hits a zero of `entireL χ` in `Re(s) > 0`, and
`‖-L'/L(σ ± iT, χ)‖ ≤ 4000000 * log²(2 * d * (2 + T))` uniformly on `1/4 ≤ σ ≤ 2`. -/
theorem exists_good_height (hGRH : DirichletGRH) {d : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) {j : ℕ} (hj : 2 ≤ j) :
    ∃ T ∈ Icc (j : ℝ) (j + 1),
      (∀ s : ℂ, 0 < s.re → (s.im = T ∨ s.im = -T) → entireL χ s ≠ 0) ∧
      (∀ σ ∈ Icc ((1 : ℝ) / 4) 2,
        ‖negLogDerivL χ ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤
          4000000 * (Real.log (2 * (d : ℝ) * (2 + T))) ^ 2 ∧
        ‖negLogDerivL χ ((σ : ℂ) + (-T : ℂ) * Complex.I)‖ ≤
          4000000 * (Real.log (2 * (d : ℝ) * (2 + T))) ^ 2) := by
  let ks : Finset ℤ := {-1, 0, 1, 2}
  let Z_bad : Finset ℂ :=
    (ks.biUnion fun k => diskZeros χ (2 + ((((j : ℤ) + k : ℤ) : ℝ) : ℂ) * Complex.I) ((15 : ℝ) / 8)) ∪
    (ks.biUnion fun k => diskZeros χ (2 + (((-((j : ℤ) + k) : ℤ) : ℝ) : ℂ) * Complex.I) ((15 : ℝ) / 8))
  set L_j : ℝ := Real.log (2 * (d : ℝ) * (2 + (j : ℝ)))
  have hLj_ge1 : 1 ≤ L_j := by
    have := one_le_log_two_mul_d_mul d (j : ℝ)
    rwa [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) j)] at this
  have hdisk_card : ∀ y : ℝ, |y| ≤ (j : ℝ) + 2 →
      ((diskZeros χ (2 + (y : ℂ) * Complex.I) ((15 : ℝ) / 8)).card : ℝ) ≤ 434 * L_j := by
    intro y hy_abs
    have hcard_le_sum : ((diskZeros χ (2 + (y : ℂ) * Complex.I) ((15 : ℝ) / 8)).card : ℝ) ≤
        ∑ ρ ∈ diskZeros χ (2 + (y : ℂ) * Complex.I) ((15 : ℝ) / 8), (zeroMult χ ρ : ℝ) := by
      calc ((diskZeros χ (2 + (y : ℂ) * Complex.I) ((15 : ℝ) / 8)).card : ℝ)
          = ∑ _ρ ∈ diskZeros χ (2 + (y : ℂ) * Complex.I) ((15 : ℝ) / 8), (1 : ℝ) := by simp
        _ ≤ ∑ ρ ∈ diskZeros χ (2 + (y : ℂ) * Complex.I) ((15 : ℝ) / 8), (zeroMult χ ρ : ℝ) :=
          Finset.sum_le_sum fun ρ hρ =>
            Nat.one_le_cast.mpr ((zeroMult_pos_iff χ ρ).mpr ((mem_diskZeros_iff χ).mp hρ).2)
    have hcnt := diskZeroCount_le hprim y
    have hj_ge : (2 : ℝ) ≤ j := Nat.ofNat_le_cast.mpr hj
    have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
    have harg_le : 2 * (d : ℝ) * (2 + |y|) ≤ 2 * (2 * (d : ℝ) * (2 + (j : ℝ))) := by
      nlinarith only [hy_abs, hj_ge, hd_pos]
    have hlog_y : Real.log (2 * (d : ℝ) * (2 + |y|)) ≤ 2 * L_j := by
      calc Real.log (2 * (d : ℝ) * (2 + |y|))
          ≤ Real.log (2 * (2 * (d : ℝ) * (2 + (j : ℝ)))) :=
            Real.log_le_log (by positivity) harg_le
        _ = Real.log 2 + L_j := Real.log_mul (by norm_num) (by positivity)
        _ ≤ 1 + L_j := by linarith only [Real.log_two_lt_d9]
        _ ≤ 2 * L_j := by linarith only [hLj_ge1]
    exact hcard_le_sum.trans (hcnt.trans (by linarith only [hlog_y]))
  have hZbad_card : (Z_bad.card : ℝ) ≤ 3472 * L_j := by
    have h1 : Z_bad.card ≤
        (∑ k ∈ ks, (diskZeros χ (2 + ((((j : ℤ) + k : ℤ) : ℝ) : ℂ) * Complex.I) ((15 : ℝ) / 8)).card) +
        (∑ k ∈ ks, (diskZeros χ (2 + (((-((j : ℤ) + k) : ℤ) : ℝ) : ℂ) * Complex.I) ((15 : ℝ) / 8)).card) := by
      calc Z_bad.card
          ≤ (ks.biUnion fun k => diskZeros χ (2 + ((((j : ℤ) + k : ℤ) : ℝ) : ℂ) * Complex.I) ((15 : ℝ) / 8)).card +
            (ks.biUnion fun k => diskZeros χ (2 + (((-((j : ℤ) + k) : ℤ) : ℝ) : ℂ) * Complex.I) ((15 : ℝ) / 8)).card :=
            Finset.card_union_le _ _
        _ ≤ _ := Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
    have h1R : (Z_bad.card : ℝ) ≤
        (∑ k ∈ ks, ((diskZeros χ (2 + ((((j : ℤ) + k : ℤ) : ℝ) : ℂ) * Complex.I) ((15 : ℝ) / 8)).card : ℝ)) +
        (∑ k ∈ ks, ((diskZeros χ (2 + (((-((j : ℤ) + k) : ℤ) : ℝ) : ℂ) * Complex.I) ((15 : ℝ) / 8)).card : ℝ)) := by
      exact_mod_cast h1
    have hj_ge : (2 : ℝ) ≤ j := Nat.ofNat_le_cast.mpr hj
    have hs1 : (∑ k ∈ ks, ((diskZeros χ (2 + ((((j : ℤ) + k : ℤ) : ℝ) : ℂ) * Complex.I) ((15 : ℝ) / 8)).card : ℝ)) ≤
        ∑ _k ∈ ks, (434 * L_j) := by
      refine Finset.sum_le_sum fun k hk => hdisk_card _ ?_
      have hk_mem : k = -1 ∨ k = 0 ∨ k = 1 ∨ k = 2 := by simpa [ks] using hk
      rcases hk_mem with rfl | rfl | rfl | rfl <;> (push_cast; rw [abs_le]; constructor <;> linarith only [hj_ge])
    have hs2 : (∑ k ∈ ks, ((diskZeros χ (2 + (((-((j : ℤ) + k) : ℤ) : ℝ) : ℂ) * Complex.I) ((15 : ℝ) / 8)).card : ℝ)) ≤
        ∑ _k ∈ ks, (434 * L_j) := by
      refine Finset.sum_le_sum fun k hk => hdisk_card _ ?_
      have hk_mem : k = -1 ∨ k = 0 ∨ k = 1 ∨ k = 2 := by simpa [ks] using hk
      rcases hk_mem with rfl | rfl | rfl | rfl <;> (push_cast; rw [abs_le]; constructor <;> linarith only [hj_ge])
    have hks_card : ks.card = 4 := by decide
    have hconst : (∑ _k ∈ ks, (434 * L_j)) = 1736 * L_j := by
      rw [Finset.sum_const, hks_card, nsmul_eq_mul]; ring
    linarith only [h1R, hs1, hs2, hconst]
  obtain ⟨T, hT_mem, hT_avoid⟩ := exists_pigeonhole_height j Z_bad
  set M : ℕ := 2 * Z_bad.card + 1
  have hM_pos : 0 < M := by omega
  have hδ_pos : (0 : ℝ) < 1 / (2 * (M : ℝ)) := by positivity
  have hT_ge2 : (2 : ℝ) ≤ T := by
    have : (2 : ℝ) ≤ (j : ℝ) := Nat.ofNat_le_cast.mpr hj
    linarith only [this, hT_mem.1]
  have hdisk_pos_sub : diskZeros χ (2 + (T : ℂ) * Complex.I) ((15 : ℝ) / 8) ⊆ Z_bad := by
    intro ρ hρ
    obtain ⟨hρ_disk, hρ_zero⟩ := (mem_diskZeros_iff χ).mp hρ
    have hdist : ‖ρ - (2 + (T : ℂ) * Complex.I)‖ ≤ 15 / 8 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hρ_disk
    have hρ_re_pos : 0 < ρ.re := by
      have h1 := (Complex.abs_re_le_norm (ρ - (2 + (T : ℂ) * Complex.I))).trans hdist
      have h2 : (ρ - (2 + (T : ℂ) * Complex.I)).re = ρ.re - 2 := by simp
      rw [h2] at h1; linarith only [(abs_le.mp h1).1]
    have hρ_im : |ρ.im - T| ≤ 15 / 8 := by
      have h1 := (Complex.abs_im_le_norm (ρ - (2 + (T : ℂ) * Complex.I))).trans hdist
      have h2 : (ρ - (2 + (T : ℂ) * Complex.I)).im = ρ.im - T := by simp
      rwa [h2] at h1
    have hlo : (j : ℝ) - 2 ≤ ρ.im := by linarith only [(abs_le.mp hρ_im).1, hT_mem.1]
    have hhi : ρ.im ≤ (j : ℝ) + 3 := by linarith only [(abs_le.mp hρ_im).2, hT_mem.2]
    have hk_exists : ∃ k ∈ ks, |ρ.im - (((j : ℤ) + k : ℤ) : ℝ)| ≤ 1 := by
      by_cases h1 : ρ.im ≤ (j : ℝ)
      · refine ⟨-1, by simp [ks], ?_⟩; push_cast; rw [abs_le]; constructor <;> linarith only [hlo, h1]
      · by_cases h2 : ρ.im ≤ (j : ℝ) + 2
        · refine ⟨1, by simp [ks], ?_⟩; push_cast; rw [abs_le]; constructor <;> linarith only [h1, h2]
        · refine ⟨2, by simp [ks], ?_⟩; push_cast; rw [abs_le]; constructor <;> linarith only [h2, hhi]
    rcases hk_exists with ⟨k, hk, hkim⟩
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨k, hk,
      mem_diskZeros_of_im_sub_le_one hGRH hprim (((j : ℤ) + k : ℤ) : ℝ) hρ_re_pos hρ_zero hkim⟩)
  have hdisk_neg_sub : diskZeros χ (2 + ((-T : ℝ) : ℂ) * Complex.I) ((15 : ℝ) / 8) ⊆ Z_bad := by
    intro ρ hρ
    obtain ⟨hρ_disk, hρ_zero⟩ := (mem_diskZeros_iff χ).mp hρ
    have hdist : ‖ρ - (2 + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ 15 / 8 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hρ_disk
    have hρ_re_pos : 0 < ρ.re := by
      have h1 := (Complex.abs_re_le_norm (ρ - (2 + ((-T : ℝ) : ℂ) * Complex.I))).trans hdist
      have h2 : (ρ - (2 + ((-T : ℝ) : ℂ) * Complex.I)).re = ρ.re - 2 := by simp
      rw [h2] at h1; linarith only [(abs_le.mp h1).1]
    have hρ_im : |ρ.im - (-T)| ≤ 15 / 8 := by
      have h1 := (Complex.abs_im_le_norm (ρ - (2 + ((-T : ℝ) : ℂ) * Complex.I))).trans hdist
      have h2 : (ρ - (2 + ((-T : ℝ) : ℂ) * Complex.I)).im = ρ.im - (-T) := by simp
      rwa [h2] at h1
    have hlo : -((j : ℝ) + 3) ≤ ρ.im := by linarith only [(abs_le.mp hρ_im).1, hT_mem.2]
    have hhi : ρ.im ≤ -((j : ℝ) - 2) := by linarith only [(abs_le.mp hρ_im).2, hT_mem.1]
    have hk_exists : ∃ k ∈ ks, |ρ.im - ((-((j : ℤ) + k) : ℤ) : ℝ)| ≤ 1 := by
      by_cases h1 : ρ.im ≤ -((j : ℝ) + 1)
      · refine ⟨2, by simp [ks], ?_⟩; push_cast; rw [abs_le]; constructor <;> linarith only [hlo, h1]
      · by_cases h2 : ρ.im ≤ -(j : ℝ)
        · refine ⟨1, by simp [ks], ?_⟩; push_cast; rw [abs_le]; constructor <;> linarith only [h1, h2]
        · refine ⟨-1, by simp [ks], ?_⟩; push_cast; rw [abs_le]; constructor <;> linarith only [h2, hhi]
    rcases hk_exists with ⟨k, hk, hkim⟩
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, hk,
      mem_diskZeros_of_im_sub_le_one hGRH hprim ((-((j : ℤ) + k) : ℤ) : ℝ) hρ_re_pos hρ_zero hkim⟩)
  have hno_zero : ∀ s : ℂ, 0 < s.re → (s.im = T ∨ s.im = -T) → entireL χ s ≠ 0 := by
    intro s hs_re him hzero
    rcases him with hpos | hneg
    · have hs_bad : s ∈ Z_bad := hdisk_pos_sub
        (mem_diskZeros_of_im_sub_le_one hGRH hprim T hs_re hzero (by simp [hpos]))
      have hge := (hT_avoid s hs_bad).1
      rw [hpos, sub_self, abs_zero] at hge
      linarith only [hge, hδ_pos]
    · have hs_bad : s ∈ Z_bad := hdisk_neg_sub
        (mem_diskZeros_of_im_sub_le_one hGRH hprim (-T) hs_re hzero (by simp [hneg]))
      have hge := (hT_avoid s hs_bad).2
      rw [hneg, sub_self, abs_zero] at hge
      linarith only [hge, hδ_pos]
  have hLj_le_LT : L_j ≤ Real.log (2 * (d : ℝ) * (2 + T)) := by
    have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
    exact Real.log_le_log (by positivity) (by nlinarith only [hd_pos, hT_mem.1])
  have h2M_le : 2 * (M : ℝ) ≤ 13890 * Real.log (2 * (d : ℝ) * (2 + T)) := by
    have hM_cast : (M : ℝ) = 2 * (Z_bad.card : ℝ) + 1 := by dsimp [M]; push_cast; ring
    linarith only [hM_cast, hZbad_card, hLj_le_LT, hLj_ge1]
  have hpos_bd := good_height_horizontal_bound hprim hT_ge2
    (abs_of_nonneg (by linarith only [hT_ge2])) hM_pos h2M_le
    (fun ρ hρ => (hT_avoid ρ (hdisk_pos_sub hρ)).1)
    (fun σ hσ => hno_zero _ (by simp; linarith only [hσ.1]) (Or.inl (by simp)))
  have hneg_bd := good_height_horizontal_bound hprim hT_ge2
    (by rw [abs_neg, abs_of_nonneg (by linarith only [hT_ge2])]) hM_pos h2M_le
    (fun ρ hρ => (hT_avoid ρ (hdisk_neg_sub hρ)).2)
    (fun σ hσ => hno_zero _ (by simp; linarith only [hσ.1]) (Or.inr (by simp)))
  refine ⟨T, hT_mem, hno_zero, fun σ hσ => ⟨hpos_bd σ hσ, ?_⟩⟩
  simpa using hneg_bd σ hσ

end VerticalAndHorizontalBounds

end FareyGoldbach
