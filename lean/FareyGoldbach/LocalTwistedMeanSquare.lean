import FareyGoldbach.PrimitiveSmoothedTwist
import FareyGoldbach.ModelAndRemainder

/-! # Local continuous-principal-term input for the short-interval circle method -/

open MeasureTheory
open scoped BigOperators Classical

namespace FareyGoldbach

/-- The continuous principal contribution for the scaled quartic bump. -/
noncomputable def shortContinuousMain (Y : ℕ) (t : ℝ) : ℂ :=
  ∫ x in (0 : ℝ)..(Y : ℝ), scaledTiltedBump Y t x

theorem shortContinuousMain_eq_mellin {Y : ℕ} (hY : 1 ≤ Y) (t : ℝ) :
    shortContinuousMain Y t = mellin (scaledTiltedBump Y t) 1 :=
  (mellin_scaledTiltedBump_one hY t).symm

theorem continuous_shortContinuousMain (Y : ℕ) : Continuous (shortContinuousMain Y) := by
  unfold shortContinuousMain
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  change Continuous (fun p : ℝ × ℝ => scaledTiltedBump Y p.1 p.2)
  unfold scaledTiltedBump
  exact (Complex.continuous_ofReal.comp
    (continuous_quarticBump.comp (continuous_snd.div_const _))).mul
    (continuous_e_real.comp (continuous_fst.mul continuous_snd))

/-- Smoothed twisted prime sum over a character, with a continuous principal term. -/
noncomputable def shortTwistedRemainderWith (weight : ℕ → ℝ) {d : ℕ}
    (χ : DirichletCharacter ℂ d) (Y : ℕ) (t : ℝ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 Y, (weight n : ℂ) * χ (n : ZMod d) *
      scaledTiltedBump Y t (n : ℝ)) -
    (if χ = 1 then shortContinuousMain Y t else 0)

noncomputable def continuousTwistedRemainder {d : ℕ}
    (χ : DirichletCharacter ℂ d) (Y : ℕ) (t : ℝ) : ℂ :=
  shortTwistedRemainderWith ArithmeticFunction.vonMangoldt χ Y t

noncomputable def shortPrimeTwistedRemainder {d : ℕ}
    (χ : DirichletCharacter ℂ d) (Y : ℕ) (t : ℝ) : ℂ :=
  shortTwistedRemainderWith primeWeight χ Y t

theorem continuousTwistedRemainder_eq {d : ℕ} (χ : DirichletCharacter ℂ d) (Y : ℕ) (t : ℝ) :
    continuousTwistedRemainder χ Y t = smoothedTiltedRemainder χ Y t +
      (if χ = 1 then (∑ n ∈ Finset.Icc 1 Y, scaledTiltedBump Y t (n : ℝ)) -
        shortContinuousMain Y t else 0) := by
  unfold continuousTwistedRemainder shortTwistedRemainderWith smoothedTiltedRemainder
  by_cases hχ : χ = 1
  · simp only [hχ, ite_true]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    have he : ∀ n : ℕ, ((quarticBump ((n : ℝ) / Y) : ℂ) * e (t * (n : ℝ))) =
        scaledTiltedBump Y t (n : ℝ) := fun _ => rfl
    simp only [mul_assoc, one_mul, he]
    ring
  · simp only [hχ, ite_false, sub_zero, add_zero]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold scaledTiltedBump
    ring

/-- GRH input for the short-interval argument, formulated for all characters. -/
def LocalTwistedMeanSquare : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (Y d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (ξ : ℝ),
    2 ≤ Y → 1 / (Y : ℝ) ≤ ξ → ξ ≤ 1 / 2 →
    (∫ t in (-ξ)..ξ, ‖continuousTwistedRemainder χ Y t‖ ^ 2) ≤
      C * (Y : ℝ) * ξ * Real.log (2 * (d : ℝ) * Y) ^ 2

theorem continuous_shortTwistedRemainderWith {d : ℕ} (weight : ℕ → ℝ)
    (χ : DirichletCharacter ℂ d) (Y : ℕ) :
    Continuous (shortTwistedRemainderWith weight χ Y) := by
  unfold shortTwistedRemainderWith
  refine (continuous_sum_finset _ fun n _ => continuous_const.mul ?_).sub ?_
  · unfold scaledTiltedBump
    exact continuous_const.mul (continuous_e_real.comp (continuous_id.mul_const _))
  · by_cases hχ : χ = 1
    · simpa only [hχ, ite_true] using continuous_shortContinuousMain Y
    · simpa only [hχ, ite_false] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))

theorem shortPrimeTwistedRemainder_sub_le {d Y : ℕ} [NeZero d]
    (χ : DirichletCharacter ℂ d) (hY : 1 ≤ Y) (t : ℝ) :
    ‖shortPrimeTwistedRemainder χ Y t - continuousTwistedRemainder χ Y t‖ ≤
      Real.sqrt (Y : ℝ) * Real.log (Y : ℝ) := by
  unfold shortPrimeTwistedRemainder continuousTwistedRemainder shortTwistedRemainderWith
  rw [sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun n hn => ?_).trans (primePowerMass_le Y hY))
  rw [← sub_mul, ← sub_mul, norm_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_sub_comm]
  have he : ‖scaledTiltedBump Y t (n : ℝ)‖ ≤ 1 := by
    unfold scaledTiltedBump
    rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (quarticBump_nonneg _)]
    exact quarticBump_le_one _
  have hc := norm_dirichletChar_le_one χ (n : ZMod d)
  calc _ ≤ (|ArithmeticFunction.vonMangoldt n - primeWeight n| * 1) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hc (abs_nonneg _)) he (norm_nonneg _) (by positivity)
    _ = _ := by simp

theorem shortPrimeTwistedMeanSquare (h : LocalTwistedMeanSquare) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (ξ : ℝ),
      2 ≤ Y → 1 / (Y : ℝ) ≤ ξ → ξ ≤ 1 / 2 →
      (∫ t in (-ξ)..ξ, ‖shortPrimeTwistedRemainder χ Y t‖ ^ 2) ≤
        C * (Y : ℝ) * ξ * Real.log (2 * (d : ℝ) * Y) ^ 2 := by
  obtain ⟨C, hC, hm⟩ := h
  refine ⟨2*C+4, by linarith, ?_⟩
  intro Y d hd χ ξ hY hξ hξ'
  have hY' : (0 : ℝ) < Y := Nat.cast_pos.mpr (by omega)
  have hξ0 : 0 ≤ ξ := (by positivity : 0 ≤ 1/(Y : ℝ)).trans hξ
  have hYlog : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Y))
  have hd1 : (1 : ℝ) ≤ d := Nat.one_le_cast.mpr (NeZero.pos d)
  have hlog : Real.log (Y : ℝ) ≤ Real.log (2 * (d : ℝ) * Y) :=
    Real.log_le_log hY' (by nlinarith only [mul_le_mul_of_nonneg_right hd1 hY'.le, hY'.le])
  set P : ℝ := (Y : ℝ) * Real.log (2 * (d : ℝ) * Y)^2
  let F := continuousTwistedRemainder χ Y
  let G := shortPrimeTwistedRemainder χ Y
  have hF : Continuous F := continuous_shortTwistedRemainderWith _ _ _
  have hG : Continuous G := continuous_shortTwistedRemainderWith _ _ _
  have hsq t : ‖G t - F t‖^2 ≤ P := by
    have hb := shortPrimeTwistedRemainder_sub_le χ (show 1 ≤ Y by omega) t
    have h := pow_le_pow_left₀ (norm_nonneg _) hb 2
    rw [mul_pow, Real.sq_sqrt hY'.le] at h
    exact h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hYlog hlog 2) hY'.le)
  have hpt t : ‖G t‖^2 ≤ 2 * ‖F t‖^2 + 2*P := by
    have htri : ‖G t‖ ≤ ‖F t‖ + ‖G t - F t‖ := by
      have ht := norm_add_le (F t) (G t - F t)
      rwa [show F t + (G t - F t) = G t by abel] at ht
    have h := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith only [h, hsq t, sq_nonneg (‖F t‖ - ‖G t - F t‖)]
  have hF2 : Continuous (fun t => ‖F t‖^2) := hF.norm.pow 2
  have hconst : IntervalIntegrable (fun _ : ℝ => 2 * P) volume (-ξ) ξ :=
    continuous_const.intervalIntegrable _ _
  have hi : (∫ t in -ξ..ξ, ‖G t‖^2) ≤ ∫ t in -ξ..ξ, 2 * ‖F t‖^2 + 2*P :=
    intervalIntegral.integral_mono_on (μ := volume) (show -ξ ≤ ξ by linarith)
    ((hG.norm.pow 2).intervalIntegrable _ _)
    (((hF2.const_mul 2).add continuous_const).intervalIntegrable _ _) (fun t _ => hpt t)
  rw [intervalIntegral.integral_add ((hF2.const_mul _).intervalIntegrable _ _)
    hconst, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hi
  have hj := mul_le_mul_of_nonneg_left (hm Y d χ ξ hY hξ hξ') (show (0:ℝ) ≤ 2 by norm_num)
  change (2:ℝ) * (∫ t in -ξ..ξ, ‖F t‖^2) ≤ _ at hj
  change (∫ t in -ξ..ξ, ‖G t‖^2) ≤ _
  simp only [smul_eq_mul] at hi
  dsimp [P] at hi
  linarith only [hi, hj]

end FareyGoldbach
