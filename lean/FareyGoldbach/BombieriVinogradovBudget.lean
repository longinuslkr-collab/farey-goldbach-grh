import FareyGoldbach.BombieriVinogradovSmall
import FareyGoldbach.ChenSwitchingScales

/-! # Logarithmic savings in the Vaughan mean value -/

open Filter
open scoped Topology

namespace FareyGoldbach

theorem bv_mangoldt_budget_small {θ C ε : ℝ} (hθ : θ<1/2) (hC : 0≤C) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,
      let L := chenSwitchLog N
      let R := ⌈L^12⌉₊
      let D := chenPowerLevel θ N
      (R:ℝ)*C*((N:ℝ)/L^29+Real.sqrt (N:ℝ)*L)+13*L^2*(N:ℝ)^(19/20:ℝ) +
        600000*L^6*((N:ℝ)/R+(N:ℝ)^(9/10:ℝ)+(D:ℝ)*Real.sqrt N) ≤
        ε*(N:ℝ)/Real.log (N:ℝ)^3 := by
  let E (N : ℕ) :=
    2*C*((chenSwitchLog N)⁻¹^14+(chenSwitchLog N)^16/(N:ℝ)^(1/2:ℝ))+
    13*((chenSwitchLog N)^5/(N:ℝ)^(1/20:ℝ))+
    600000*((chenSwitchLog N)⁻¹^3+(chenSwitchLog N)^9/(N:ℝ)^(1/10:ℝ)+
      (chenSwitchLog N)^9/(N:ℝ)^(1/2-θ))
  have hinv := tendsto_inv_atTop_zero.comp chenSwitchLog_tendsto_atTop
  have hh₁ := chenSwitchLog_pow_div_power_tendsto 16 (by norm_num : (0:ℝ)<1/2)
  have hh₂ := chenSwitchLog_pow_div_power_tendsto 5 (by norm_num : (0:ℝ)<1/20)
  have hh₃ := chenSwitchLog_pow_div_power_tendsto 9 (by norm_num : (0:ℝ)<1/10)
  have hh₄ := chenSwitchLog_pow_div_power_tendsto 9 (sub_pos.mpr hθ)
  have hE : Tendsto E atTop (𝓝 0) := by
    have H₁ := ((hinv.pow 14).add hh₁).const_mul (2*C)
    have H₂ := (((hinv.pow 3).add hh₃).add hh₄).const_mul 600000
    have H := (H₁.add (hh₂.const_mul 13)).add H₂
    simpa only [E,Function.comp_apply,zero_pow (by decide : 14≠0),
      zero_pow (by decide : 3≠0),mul_zero,add_zero] using H
  filter_upwards [hE.eventually_lt_const hε,eventually_ge_atTop (2:ℕ)] with N hsmall hN
  let L := chenSwitchLog N
  let R := ⌈L^12⌉₊
  let D := chenPowerLevel θ N
  have hp : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  have hL : 0<L := zero_lt_one.trans_le (one_le_chenSwitchLog (by omega))
  have hl := Real.log_pos (Nat.one_lt_cast.mpr hN)
  obtain ⟨_,hRlo,hRhi⟩ := bv_cutoff_bounds (by omega : 1≤N)
  have hD : (D:ℝ)≤(N:ℝ)^θ := Nat.floor_le (Real.rpow_nonneg hp.le _)
  have hR : (N:ℝ)/R ≤ (N:ℝ)/L^12 := div_le_div_of_nonneg_left hp.le (by positivity) hRlo
  have hhalf : Real.sqrt (N:ℝ)=(N:ℝ)/(N:ℝ)^(1/2:ℝ) := by
    rw [Real.sqrt_eq_rpow]
    apply (eq_div_iff (Real.rpow_pos_of_pos hp _).ne').mpr
    rw [←Real.rpow_add hp]; norm_num
  have powDiv (a b : ℝ) (he : a+b=1) : (N:ℝ)^a=(N:ℝ)/(N:ℝ)^b := by
    apply (eq_div_iff (Real.rpow_pos_of_pos hp _).ne').mpr
    rw [←Real.rpow_add hp,he,Real.rpow_one]
  have hθp : (N:ℝ)^θ*Real.sqrt N=(N:ℝ)/(N:ℝ)^(1/2-θ) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add hp]
    apply powDiv
    ring
  change (R:ℝ)*C*((N:ℝ)/L^29+Real.sqrt (N:ℝ)*L)+13*L^2*(N:ℝ)^(19/20:ℝ) +
    600000*L^6*((N:ℝ)/R+(N:ℝ)^(9/10:ℝ)+(D:ℝ)*Real.sqrt N) ≤ _
  calc _ ≤ 2*L^12*C*((N:ℝ)/L^29+Real.sqrt (N:ℝ)*L)+13*L^2*(N:ℝ)^(19/20:ℝ) +
             600000*L^6*((N:ℝ)/L^12+(N:ℝ)^(9/10:ℝ)+(N:ℝ)^θ*Real.sqrt N) := by
           exact add_le_add (add_le_add_left (mul_le_mul_of_nonneg_right
             (mul_le_mul_of_nonneg_right hRhi hC) (by positivity)) _)
             (mul_le_mul_of_nonneg_left (add_le_add (add_le_add_left hR _)
               (mul_le_mul_of_nonneg_right hD (Real.sqrt_nonneg _))) (by positivity))
       _ = E N*((N:ℝ)/L^3) := by
         rw [hθp,hhalf,powDiv (19/20) (1/20) (by norm_num),powDiv (9/10) (1/10) (by norm_num)]
         change _ = (2*C*(L⁻¹^14+L^16/(N:ℝ)^(1/2:ℝ))+13*(L^5/(N:ℝ)^(1/20:ℝ))+
           600000*(L⁻¹^3+L^9/(N:ℝ)^(1/10:ℝ)+L^9/(N:ℝ)^(1/2-θ)))*((N:ℝ)/L^3)
         field_simp [hL.ne']
       _ ≤ ε*((N:ℝ)/L^3) := mul_le_mul_of_nonneg_right hsmall.le (by positivity)
       _ ≤ _ := by
         rw [←mul_div_assoc]
         exact div_le_div_of_nonneg_left (mul_nonneg hε.le hp.le) (pow_pos hl _)
           (pow_le_pow_left₀ hl.le (log_le_chenSwitchLog (by omega : 1≤N)) _)

end FareyGoldbach
