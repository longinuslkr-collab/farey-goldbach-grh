import FareyGoldbach.ChenAPScale
import FareyGoldbach.ChenSwitchingScales

/-! # Absorption of a power saving uniformly over an auxiliary modulus -/

open Filter
open scoped Topology

namespace FareyGoldbach

theorem chenAP_log_power_absorb {δ β C ε : ℝ} (j b : ℕ)
    (hgap : β+δ<1) (hC : 0≤C) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ r : ℕ, 0<r → (r:ℝ)≤(N:ℝ)^δ →
      C*(N:ℝ)^β*(chenSwitchLog N)^j≤ε*((N:ℝ)/((r.totient:ℝ)*Real.log (N:ℝ)^b)) := by
  let e := 1-(β+δ)
  have he : 0<e := sub_pos.mpr hgap
  have h := (chenSwitchLog_pow_div_power_tendsto (j+b) he).const_mul C
  rw [mul_zero] at h
  filter_upwards [h.eventually_lt_const hε,eventually_ge_atTop (2:ℕ)] with N hsmall hN r hr hrN
  let L := chenSwitchLog N
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  have hL : 0≤L := zero_le_one.trans (one_le_chenSwitchLog (by omega))
  have hl := Real.log_pos (Nat.one_lt_cast.mpr hN)
  have hφ : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hp : (r.totient:ℝ)≤(N:ℝ)^δ := (Nat.cast_le.mpr (Nat.totient_le _)).trans hrN
  have hlog : Real.log (N:ℝ)^b≤L^b := pow_le_pow_left₀ hl.le (log_le_chenSwitchLog (by omega)) _
  have hd : 0<(r.totient:ℝ)*Real.log (N:ℝ)^b := mul_pos hφ (pow_pos hl _)
  have h₀ : C*L^(j+b)≤ε*(N:ℝ)^e := by
    change C*(L^(j+b)/(N:ℝ)^e)<ε at hsmall
    rw [←mul_div_assoc] at hsmall
    exact ((div_lt_iff₀ (Real.rpow_pos_of_pos hn _)).mp hsmall).le
  rw [←mul_div_assoc,le_div_iff₀ hd]
  calc
    _ ≤ (C*(N:ℝ)^β*L^j)*((N:ℝ)^δ*L^b) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hp hlog (pow_nonneg hl.le _) (by positivity)) (by positivity)
    _ = (C*L^(j+b))*(N:ℝ)^(β+δ) := by rw [Real.rpow_add hn,pow_add]; ring
    _ ≤ (ε*(N:ℝ)^e)*(N:ℝ)^(β+δ) := mul_le_mul_of_nonneg_right h₀ (by positivity)
    _ = _ := by rw [mul_assoc,←Real.rpow_add hn,show e+(β+δ)=1 by dsimp [e]; ring,Real.rpow_one]

end FareyGoldbach
