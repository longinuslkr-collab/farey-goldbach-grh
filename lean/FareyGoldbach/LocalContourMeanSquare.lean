import FareyGoldbach.QuarticSpectralGram
import FareyGoldbach.QuarterLowMeanSquare

/-! # Local twisted mean square for primitive characters under Dirichlet GRH -/

open Real Complex MeasureTheory Set
open scoped Classical

namespace FareyGoldbach

private lemma continuousTwistedRemainder_explicit (hGRH : DirichletGRH)
    {d Y : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive)
    (hY : 2 ≤ Y) (t : ℝ) :
    continuousTwistedRemainder χ Y t = -(∑' ρ, zeroTerm χ Y t ρ) +
      ((1 / (2*Real.pi) : ℝ) : ℂ) * ∫ u, quarterContourIntegrand χ Y t u := by
  have h := primitive_smoothed_explicit_formula hGRH hprim hY t
  unfold continuousTwistedRemainder shortTwistedRemainderWith
  rw [shortContinuousMain_eq_mellin (by omega : 1 ≤ Y)]
  push_cast
  rw [h]
  unfold quarterContourIntegrand quarterPoint
  push_cast
  ring

private lemma norm_add_add_sq_le (a b c : ℂ) :
    ‖a+b+c‖^2 ≤ 3 * (‖a‖^2 + ‖b‖^2 + ‖c‖^2) := by
  have hadd : ‖a+b‖+‖c‖ ≤ ‖a‖+‖b‖+‖c‖ := add_le_add (norm_add_le a b) le_rfl
  have h := (norm_add_le (a+b) c).trans hadd
  have hp := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith only [hp, sq_nonneg (‖a‖-‖b‖),sq_nonneg (‖a‖-‖c‖),sq_nonneg (‖b‖-‖c‖)]

set_option maxHeartbeats 1000000 in
theorem primitive_local_twisted_mean_square (hGRH : DirichletGRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d), χ.IsPrimitive →
      ∀ ξ : ℝ, 2 ≤ Y → 1/(Y:ℝ) ≤ ξ → ξ ≤ 1/2 →
      (∫ t in -ξ..ξ, ‖continuousTwistedRemainder χ Y t‖^2) ≤ C*(Y:ℝ)*ξ*Real.log (2*(d:ℝ)*Y)^2 := by
  obtain ⟨Cz,hCz,hzero⟩ := lowZeroBand_meanSquare hGRH
  obtain ⟨Cl,hCl,hline⟩ := quarterLow_meanSquare hGRH
  obtain ⟨Dz,hDz,hztail⟩ := zeroSpectralTail_bound hGRH
  obtain ⟨Dl,hDl,hltail⟩ := quarterSpectralTail_bound hGRH
  refine ⟨3*(21*Cz+21*Cl+2*(Dz+Dl)^2), by positivity, ?_⟩
  intro Y d hd χ hprim ξ hY hξmin hξmax
  let T := localSpectralCutoff Y ξ
  let L := Real.log (2*(d:ℝ)*Y)
  let c : ℂ := ((1/(2*Real.pi):ℝ):ℂ)
  let Z (t : ℝ) := ∑ ρ ∈ localLowZeros χ T, zeroTerm χ Y t ρ
  let Q (t : ℝ) := ∫ u in Icc (-(T:ℝ)) (T:ℝ), quarterContourIntegrand χ Y t u
  let W := continuousTwistedRemainder χ Y
  let E (t : ℝ) := W t + Z t - c*Q t
  have hyp : (0:ℝ)<Y := Nat.cast_pos.mpr (by omega)
  have hY₁ : (1:ℝ)≤Y := Nat.one_le_cast.mpr (by omega)
  have hξ : 0 ≤ ξ := (by positivity : 0 ≤ 1/(Y:ℝ)).trans hξmin
  have hLog : 0 ≤ L := zero_le_one.trans (one_le_log_two_d_Y hY)
  obtain ⟨hT₁,hT₂,hTξ⟩ := localSpectralCutoff_bounds hY hξmin hξmax
  have hT₂' : (T:ℝ) ≤ 11*(Y:ℝ) := by exact_mod_cast hT₂
  obtain ⟨hZ,hZbd⟩ := hzero hprim T ξ hY hT₁ hT₂ hξ
  obtain ⟨hQ,hQbd⟩ := hline hprim (T:ℝ) ξ hY (Nat.cast_nonneg _) hT₂' hξ
  have hW : Continuous W := continuous_shortTwistedRemainderWith _ _ _
  have hc : ‖c‖ ≤ 1 := by
    dsimp [c]
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hπ : 1 ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
    exact div_le_self zero_le_one hπ
  let B := (Dz+Dl)*Real.sqrt (Y:ℝ)*L
  have hE (t : ℝ) (ht : t ∈ Icc (-ξ) ξ) : ‖E t‖ ≤ B := by
    have hTtail := localSpectralCutoff_tail hY hξmin (abs_le.mpr ht)
    have hz := hztail hprim T t hY hTtail
    have hq := hltail hprim (T:ℝ) t hY hTtail
    change ‖(∑' ρ, zeroTerm χ Y t ρ) - Z t‖ ≤ Dz * Real.sqrt (Y:ℝ) * L at hz
    change ‖(∫ u, quarterContourIntegrand χ Y t u) - Q t‖ ≤ Dl * Real.sqrt (Y:ℝ) * L at hq
    let a : ℂ := (∑' ρ, zeroTerm χ Y t ρ) - Z t
    let b : ℂ := (∫ u, quarterContourIntegrand χ Y t u) - Q t
    have heq : E t = -a+c*b := by
      dsimp only [E,W,a,b,c]
      rw [continuousTwistedRemainder_explicit hGRH hprim hY]
      ring
    have hb : ‖c*b‖ ≤ ‖b‖ := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_eq (one_mul _)
    calc ‖E t‖ ≤ ‖a‖ + ‖b‖ := by
          rw [heq]; exact (norm_add_le _ _).trans (by rw [norm_neg]; exact add_le_add le_rfl hb)
      _ ≤ _ := (add_le_add hz hq).trans_eq (by dsimp [B]; ring)
  have hWpoint (t : ℝ) (ht : t ∈ Icc (-ξ) ξ) :
      ‖W t‖^2 ≤ 3*(‖Z t‖^2 + ‖Q t‖^2 + B^2) := by
    have h := norm_add_add_sq_le (-(Z t)) (c*Q t) (E t)
    rw [show -Z t+c*Q t+E t=W t by dsimp only [E]; ring, norm_neg] at h
    have hq : ‖c*Q t‖ ≤ ‖Q t‖ := by
      rw [norm_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (norm_nonneg (Q t))
    have hq' : ‖c*Q t‖^2 ≤ ‖Q t‖^2 := pow_le_pow_left₀ (norm_nonneg _) hq 2
    have he' : ‖E t‖^2 ≤ B^2 := pow_le_pow_left₀ (norm_nonneg _) (hE t ht) 2
    have h' : ‖Z t‖^2 + ‖c*Q t‖^2 + ‖E t‖^2 ≤ ‖Z t‖^2 + ‖Q t‖^2 + B^2 :=
      add_le_add (add_le_add le_rfl hq') he'
    exact h.trans (mul_le_mul_of_nonneg_left h' (by norm_num))
  have hZ' : Continuous (fun t => ‖Z t‖^2) := hZ.norm.pow 2
  have hQ' : Continuous (fun t => ‖Q t‖^2) := hQ.norm.pow 2
  have hconst : IntervalIntegrable (fun _ : ℝ => B^2) volume (-ξ) ξ := continuous_const.intervalIntegrable _ _
  have hiv : IntervalIntegrable (fun t => ‖Z t‖^2 + ‖Q t‖^2) volume (-ξ) ξ :=
    (hZ'.add hQ').intervalIntegrable _ _
  have hI : (∫ t in -ξ..ξ, ‖W t‖^2) ≤ ∫ t in -ξ..ξ, 3*(‖Z t‖^2 + ‖Q t‖^2 + B^2) :=
    intervalIntegral.integral_mono_on (μ := volume) (show -ξ≤ξ by linarith)
      (hW.norm.pow 2 |>.intervalIntegrable _ _) ((hiv.add hconst).const_mul _)
      hWpoint
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hiv hconst,
    intervalIntegral.integral_add (hZ'.intervalIntegrable _ _) (hQ'.intervalIntegrable _ _),
    intervalIntegral.integral_const, smul_eq_mul] at hI
  have hZb : (∫ t in -ξ..ξ, ‖Z t‖^2) ≤ (21*Cz)*(Y:ℝ)*ξ*L^2 := by
    refine hZbd.trans ?_
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTξ hCz.le) (sq_nonneg L)
    linarith only [h]
  have hQb : (∫ t in -ξ..ξ, ‖Q t‖^2) ≤ (21*Cl)*(Y:ℝ)*ξ*L^2 := by
    have hYpow : (Y:ℝ)^(-(1/2:ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hY₁ (by norm_num)
    have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYpow hCl.le)
      (show 0 ≤ (T:ℝ)*L^2 by positivity)
    have ht := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTξ hCl.le) (sq_nonneg L)
    exact hQbd.trans (show _ ≤ _ by linarith only [hb,ht])
  have hB : B^2 = (Dz+Dl)^2*(Y:ℝ)*L^2 := by
    dsimp [B]; rw [mul_pow,mul_pow,Real.sq_sqrt hyp.le]
  rw [hB] at hI
  change (∫ t in -ξ..ξ, ‖W t‖^2) ≤ 3*(21*Cz+21*Cl+2*(Dz+Dl)^2)*(Y:ℝ)*ξ*L^2
  linarith only [hI,hZb,hQb]

end FareyGoldbach
