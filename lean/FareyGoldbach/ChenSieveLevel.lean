import FareyGoldbach.ChenDistributionInterfaces
import FareyGoldbach.TernaryPowerRange

/-! # Comparison of Chen's cutoff, power and logarithmically reduced levels -/

open Filter
open scoped Topology

namespace FareyGoldbach

theorem chenPowerLevel_cutoffs {θ : ℝ} (hθ : 11/24<θ) {N : ℕ} (hN : 2^24≤N) :
    2≤chenLowerCutoff N ∧ 2≤chenUpperCutoff N ∧
      chenLowerCutoff N * chenUpperCutoff N ≤ chenPowerLevel θ N := by
  have hn : (2:ℝ)^8≤N := by exact_mod_cast (show 2^8≤N by omega)
  have hp : (0:ℝ)<N := by linarith
  have hn₁ : (1:ℝ)≤N := by linarith
  have hpow : ((2:ℝ)^8)^(1/8:ℝ)=2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : 0≤(2:ℝ))]
    norm_num
  have hlo : (2:ℝ)≤(N:ℝ)^(1/8:ℝ) :=
    hpow ▸ Real.rpow_le_rpow (by positivity) hn (by norm_num : (0:ℝ)≤1/8)
  have hhi := hlo.trans (Real.rpow_le_rpow_of_exponent_le hn₁ (by norm_num : (1/8:ℝ)≤1/3))
  refine ⟨Nat.le_floor (by exact_mod_cast hlo),Nat.le_floor (by exact_mod_cast hhi),?_⟩
  apply Nat.le_floor
  rw [Nat.cast_mul]
  calc _ ≤ (N:ℝ)^(1/8:ℝ)*(N:ℝ)^(1/3:ℝ) :=
        mul_le_mul (Nat.floor_le (Real.rpow_nonneg hp.le _)) (Nat.floor_le (Real.rpow_nonneg hp.le _))
          (Nat.cast_nonneg _) (Real.rpow_nonneg hp.le _)
       _ ≤ _ := by
         rw [←Real.rpow_add hp]
         exact Real.rpow_le_rpow_of_exponent_le hn₁ (by linarith)

/-- Each fixed subcritical power lies below the usual log-reduced square-root level. -/
theorem chenPowerLevel_eventually_le_chenLogLevel (θ : ℝ) (hθ : θ<1/2) (A : ℕ) :
    ∀ᶠ N : ℕ in atTop, chenPowerLevel θ N ≤ chenLogLevel A N := by
  have he : 0<1/2-θ := by linarith
  have hl := (isLittleO_log_rpow_rpow_atTop (A:ℝ) he).tendsto_div_nhds_zero
  have hreal : Tendsto (fun x : ℝ => Real.log x^A/x^(1/2-θ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using hl
  have hnat := hreal.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hnat.eventually_lt_const zero_lt_one,eventually_ge_atTop (2:ℕ)] with N h hN
  have hn : (2:ℝ)≤N := by exact_mod_cast hN
  have hp : (0:ℝ)<N := by linarith
  have hL : 0<Real.log (N:ℝ)^A := pow_pos (Real.log_pos (by linarith)) _
  have hx : 0<(N:ℝ)^(1/2-θ) := Real.rpow_pos_of_pos hp _
  change Real.log (N:ℝ)^A/(N:ℝ)^(1/2-θ)<1 at h
  apply Nat.floor_le_floor
  apply (le_div_iff₀ hL).2
  calc _ ≤ (N:ℝ)^θ*(N:ℝ)^(1/2-θ) :=
        mul_le_mul_of_nonneg_left ((div_lt_one hx).mp h).le (Real.rpow_nonneg hp.le _)
       _ = _ := by rw [←Real.rpow_add hp,Real.sqrt_eq_rpow]; ring_nf

theorem chenPrimeAPDistribution_of_logLevel {A : ℕ}
    (h : ChenPrimeAPDistributionAt (chenLogLevel A)) : ChenPrimeAPDistribution :=
  fun θ _ hθ => h.mono (chenPowerLevel_eventually_le_chenLogLevel θ hθ A)

theorem chenSwitchingDistribution_of_logLevel {A : ℕ}
    (h : ChenSwitchingDistributionAt (chenLogLevel A)) : ChenSwitchingDistribution :=
  fun θ _ hθ => h.mono (chenPowerLevel_eventually_le_chenLogLevel θ hθ A)

end FareyGoldbach
