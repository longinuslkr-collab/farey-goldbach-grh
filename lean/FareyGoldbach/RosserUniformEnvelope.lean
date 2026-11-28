import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13HatLayersKappaOne

/-! Uniform bound on both Suzuki error envelopes on the first sieve intervals. -/

open Set
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

namespace FareyGoldbach

/-- The selected stopping depth varies with the finite prime set. On [1,4] both
possible hat functions have one common bound, independent of that depth. -/
theorem rosser_uniform_error_envelope (H : Section13HatLayers) (hH : Section13HatContract H 2) :
    ∃ B : ℝ, 0 < B ∧ ∀ {D s : ℝ} (depth : ℕ), 1 < D →
      (4:ℝ)^(16:ℝ) ≤ Real.log D → 1 ≤ s → s ≤ 4 →
      errorEnvelope H depth D 16 s ≤ B := by
  have hb (sign : ErrorSign) : BddAbove ((H.T sign) '' Icc (1:ℝ) 4) :=
    isCompact_Icc.bddAbove_image ((hH.continuous sign).mono fun x hx =>
      (by norm_num : (0:ℝ)<1).trans_le hx.1)
  obtain ⟨Bplus,hplus⟩ := hb .plus
  obtain ⟨Bminus,hminus⟩ := hb .minus
  let M := 1 + |Bplus| + |Bminus|
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨64*M,by positivity,?_⟩
  intro D s depth hD hlog hs hs4
  have hs0 := (by norm_num : (0:ℝ) < 1).trans_le hs
  have hr : s^(16:ℝ) / Real.log D ≤ 1 :=
    (div_le_one (Real.log_pos hD)).mpr ((Real.rpow_le_rpow hs0.le hs4 (by norm_num)).trans hlog)
  have hgeom0 : 0 ≤ 1 + s^(16:ℝ)/Real.log D := by positivity
  have hgeom : (1 + s^(16:ℝ)/Real.log D)^s ≤ 16 := by
    calc _ ≤ (2:ℝ)^s := Real.rpow_le_rpow hgeom0 (by linarith) hs0.le
         _ ≤ (2:ℝ)^(4:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs4
         _ = _ := by norm_num
  have hT (sign : ErrorSign) : H.T sign s ≤ M := by
    cases sign with
    | plus =>
      apply (hplus ⟨s,⟨hs,hs4⟩,rfl⟩).trans
      dsimp only [M]
      linarith only [le_abs_self Bplus,abs_nonneg Bminus]
    | minus =>
      apply (hminus ⟨s,⟨hs,hs4⟩,rfl⟩).trans
      dsimp only [M]
      linarith only [le_abs_self Bminus,abs_nonneg Bplus]
  have hn : 0 ≤ H.T (ErrorSign.ofDepth depth) s := (hH.positive _ s hs0).le
  simp only [errorEnvelope, Section13HatLayers.kappaHat, sub_self, zero_add, Real.rpow_one]
  calc _ ≤ (16*4)*M := mul_le_mul (mul_le_mul hgeom hs4 hs0.le (by norm_num)) (hT _) hn (by norm_num)
       _ = _ := by norm_num

end FareyGoldbach