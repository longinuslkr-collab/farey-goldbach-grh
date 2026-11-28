module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Data.Nat.Totient

/-! # Vanishing of the ternary compatible-class budget in the subpower range -/

public section

open Filter
open scoped Topology

namespace FareyGoldbach

/-- If `r ≤ X^(1-ε)`, both terms in the compatible-class bound vanish. -/
theorem ternary_compatible_budget_tendsto_of_subpower {ε : ℝ} (hε : 0<ε)
    (X r : ℕ→ℕ) (hX : Tendsto X atTop atTop) (hr : ∀ j,0<r j)
    (hpower : ∀ᶠ j in atTop, (r j:ℝ)≤(X j:ℝ)^(1-ε)) :
    Tendsto (fun j =>
      let L := Real.log (2*(X j:ℝ))
      let H := (X j:ℝ)/r j
      let κ := (r j:ℝ)/(r j).totient
      L^2/H+L^4/(κ^2*Real.sqrt H)) atTop (𝓝 0) := by
  have he : 0<(ε/2:ℝ) := by positivity
  have hlog := (isLittleO_log_rpow_rpow_atTop (4:ℝ) he).tendsto_div_nhds_zero
  have hnat : Tendsto (fun x : ℝ => Real.log x^4/x^(ε/2)) atTop (𝓝 0) := by
    apply hlog.congr
    intro x
    rw [← Real.rpow_natCast]
    norm_num
  have hx : Tendsto (fun j => (X j:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hX
  have hupper : Tendsto (fun j => 32*(Real.log (X j:ℝ)^4/(X j:ℝ)^(ε/2))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,mul_zero] using (hnat.comp hx).const_mul 32
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall fun j => by dsimp; positivity
  · filter_upwards [(tendsto_atTop.1 hX) 2,hpower,(Real.tendsto_log_atTop.comp hx).eventually_ge_atTop 1] with j hj hp hlogx
    let x := (X j:ℝ)
    let q := (r j:ℝ)
    let L := Real.log (2*x)
    let H := x/q
    let κ := q/(r j).totient
    let R := x^(ε/2)
    have hx₂ : 2≤x := Nat.ofNat_le_cast.mpr hj
    have hxp : 0<x := by linarith only [hx₂]
    have hq : 0<q := Nat.cast_pos.mpr (hr j)
    have hφ : (0:ℝ)<(r j).totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (hr j))
    have hk : 1≤κ := (le_div_iff₀ hφ).2 (by
      rw [one_mul]
      exact Nat.cast_le.mpr (Nat.totient_le (r j)))
    have hh : x^ε≤H := by
      apply (le_div_iff₀ hq).2
      calc x^ε*q ≤ x^ε*x^(1-ε) := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hxp.le _)
        _ = x := by rw [← Real.rpow_add hxp,show ε+(1-ε)=1 by ring,Real.rpow_one]
    have hR : 0<R := Real.rpow_pos_of_pos hxp _
    have hR₁ : R≤H := (Real.rpow_le_rpow_of_exponent_le (by linarith only [hx₂]) (by linarith only [hε])).trans hh
    have hs : R≤Real.sqrt H := by
      rw [show R=Real.sqrt (x^ε) by dsimp [R]; rw [Real.sqrt_eq_rpow,← Real.rpow_mul hxp.le]; ring_nf]
      exact Real.sqrt_le_sqrt hh
    have hk₂ : 1≤κ^2 := by simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hk 2
    have hkH : R≤κ^2*Real.sqrt H := hs.trans (by
      have h := mul_le_mul_of_nonneg_right hk₂ (Real.sqrt_nonneg H)
      simpa only [one_mul] using h)
    have hL : 1≤L := hlogx.trans (Real.log_le_log hxp (by linarith only [hxp.le]))
    have hL₂ : L≤2*Real.log x := by
      have h := Real.log_le_log (show 0<2*x by positivity)
        (show 2*x≤x^2 by nlinarith only [mul_le_mul_of_nonneg_right hx₂ hxp.le])
      rwa [Real.log_pow] at h
    have hLL : L^2≤L^4 := pow_le_pow_right₀ hL (by decide : 2≤4)
    have h4 : L^4≤16*Real.log x^4 := by
      have h := pow_le_pow_left₀ (zero_le_one.trans hL) hL₂ 4
      rwa [mul_pow,show (2:ℝ)^4=16 by norm_num] at h
    change L^2/H+L^4/(κ^2*Real.sqrt H) ≤ 32*(Real.log x^4/R)
    calc _ ≤ L^2/R+L^4/R := add_le_add (div_le_div_of_nonneg_left (sq_nonneg _) hR hR₁)
          (div_le_div_of_nonneg_left (pow_nonneg (zero_le_one.trans hL) 4) hR hkH)
      _ ≤ 2*(L^4/R) := by linarith only [div_le_div_of_nonneg_right hLL hR.le]
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h4 hR.le)
          (by norm_num : (0:ℝ)≤2)
        exact h.trans_eq (by ring)

end FareyGoldbach
