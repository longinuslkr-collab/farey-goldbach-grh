import FareyGoldbach.ChenAPDistributionInterfaces
import FareyGoldbach.ChenTheoremUnconditional

/-! # Specializing the progression distribution inputs to modulus one -/

open Filter
open scoped Topology

namespace FareyGoldbach

private theorem modulus_one_of_exponent_zero {r N : ℕ} (hr : 0<r) (h : (r:ℝ)≤(N:ℝ)^(0:ℝ)) :
    r=1 := by
  rw [Real.rpow_zero] at h
  have hr' : r≤1 := by exact_mod_cast h
  omega

theorem chenAPPrimeDistributionAt_zero_of_primeDistributionAt {θ : ℝ}
    (hA : ChenPrimeAPDistributionAt (chenPowerLevel θ)) : ChenAPPrimeDistributionAt 0 θ := by
  intro ε hε
  have hmass := (Metric.tendsto_nhds.mp hA.1) ε hε
  filter_upwards [hmass,hA.2 ε hε] with N hm he hEven r b₁ b₂ hr hpow _ _ _
  obtain rfl := modulus_one_of_exponent_zero hr hpow
  have hcarrier : chenAPA N 1 b₁=chenA N := by simp [chenAPA,Nat.mod_one]
  have hAerr : chenAPPrimeError N 1 b₁ = chenPrimeAPError N := by
    funext d
    simp only [chenAPPrimeError,chenPrimeAPError,hcarrier]
  have hMedium : chenAPMediumError N 1 b₁ (chenPowerLevel θ N)=chenMediumError N (chenPowerLevel θ N) := by
    simp only [chenAPMediumError,one_mul,hcarrier]
    rfl
  obtain ⟨e₁,e₂⟩ := he hEven
  simpa only [hcarrier,hAerr,hMedium,one_mul,chenAPMassScale,chenAPLogScale,Nat.totient_one,
    Nat.cast_one,chenLogScale,Real.dist_eq] using And.intro hm.le (And.intro e₁ e₂)

theorem chenAPSwitchingDistributionAt_zero_of_switchingDistributionAt {θ : ℝ}
    (hB : ChenSwitchingDistributionAt (chenPowerLevel θ)) : ChenAPSwitchingDistributionAt 0 θ := by
  intro ε hε
  filter_upwards [hB.1 ε hε,hB.2 ε hε] with N hm he hEven r b₁ b₂ hr hpow _ _ _
  obtain rfl := modulus_one_of_exponent_zero hr hpow
  have hBcarrier (z y : ℕ) : chenAPUnrestrictedB N 1 b₂ z y=chenUnrestrictedB N z y := by
    simp [chenAPUnrestrictedB,Nat.mod_one]
  have hBerr : chenAPSwitchedError N 1 b₂ = chenSwitchingAPError N := by
    funext d
    simp only [chenAPSwitchedError,chenSwitchingAPError,hBcarrier]
  simpa only [hBcarrier,hBerr,one_mul,chenAPMassScale,chenAPLogScale,Nat.totient_one,
    Nat.cast_one,chenLogScale] using And.intro (hm hEven) (he hEven)

theorem chenAPPrimeDistributionAt_zero_unconditional {θ : ℝ} (hθ : 11/24<θ) (hθ' : θ<1/2) :
    ChenAPPrimeDistributionAt 0 θ :=
  chenAPPrimeDistributionAt_zero_of_primeDistributionAt (chenPrimeAPDistribution_unconditional θ hθ hθ')

theorem chenAPSwitchingDistributionAt_zero_unconditional {θ : ℝ} (hθ : 11/24<θ) (hθ' : θ<1/2) :
    ChenAPSwitchingDistributionAt 0 θ :=
  chenAPSwitchingDistributionAt_zero_of_switchingDistributionAt (chenSwitchingDistribution_unconditional θ hθ hθ')

end FareyGoldbach
