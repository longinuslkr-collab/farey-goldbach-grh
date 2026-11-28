import FareyGoldbach.ChenSwitchingScales

/-! # Comparison of the switching error with the Chen main term -/

open Filter
open scoped Topology

namespace FareyGoldbach

theorem chenSwitching_budget_small {β C ε : ℝ} (hβ : β<1) (hC : 0≤C) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, C*((N:ℝ)/(chenSwitchLog N)^4 + (N:ℝ)^β*(chenSwitchLog N)^20)
      ≤ ε*chenLogScale N := by
  have hpower := chenSwitchLog_pow_div_power_tendsto 22 (sub_pos.mpr hβ)
  have hinv := (tendsto_inv_atTop_zero.comp chenSwitchLog_tendsto_atTop).pow 2
  have hlim : Tendsto (fun N : ℕ => C*(1/(chenSwitchLog N)^2 +
      (chenSwitchLog N)^22/(N:ℝ)^(1-β))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, inv_pow, zero_pow (by decide : 2 ≠ 0), zero_add,
      mul_zero, one_div] using (hinv.add hpower).const_mul C
  filter_upwards [hlim.eventually_lt_const hε,eventually_ge_atTop (2:ℕ)] with N hsmall hN
  have hn₁ : 1≤N := by omega
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  have hlog : 0<Real.log (N:ℝ) := Real.log_pos (Nat.one_lt_cast.mpr hN)
  have hL : 0<chenSwitchLog N := zero_lt_one.trans_le (one_le_chenSwitchLog hn₁)
  have hpow : (N:ℝ)^β=(N:ℝ)/(N:ℝ)^(1-β) := by
    apply (eq_div_iff (Real.rpow_pos_of_pos hn _).ne').mpr
    rw [← Real.rpow_add hn, show β+(1-β)=1 by ring, Real.rpow_one]
  calc
    _ = C*(1/(chenSwitchLog N)^2+(chenSwitchLog N)^22/(N:ℝ)^(1-β))*
        ((N:ℝ)/(chenSwitchLog N)^2) := by
      rw [hpow]
      field_simp [hL.ne', (Real.rpow_pos_of_pos hn (1-β)).ne']
    _ ≤ C*(1/(chenSwitchLog N)^2+(chenSwitchLog N)^22/(N:ℝ)^(1-β))*chenLogScale N := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (by positivity))
      exact div_le_div_of_nonneg_left hn.le (sq_pos_of_pos hlog)
        (pow_le_pow_left₀ hlog.le (log_le_chenSwitchLog hn₁) 2)
    _ ≤ ε*chenLogScale N :=
      mul_le_mul_of_nonneg_right hsmall.le (div_nonneg hn.le (sq_nonneg _))

end FareyGoldbach
