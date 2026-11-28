import FareyGoldbach.BombieriVinogradov
import FareyGoldbach.ChenMediumErrorReduction
import FareyGoldbach.ChenPrimeAPBridge

/-! # Distribution of the prime sequence at Chen's sieve levels -/

open Filter
open scoped Topology

namespace FareyGoldbach

/-- The sharp primitive first moment supplies the reduced errors. A medium
prime dividing N incurs an additional summable error. -/
theorem chenPrimeAPDistribution_of_pnt_and_primitiveMangoldt
    (hPNT : Tendsto (fun N : ℕ => (N.primeCounting:ℝ)/((N:ℝ)/Real.log (N:ℝ))) atTop (𝓝 1))
    (hBV : ChenPrimitiveMangoldtBV) : ChenPrimeAPDistribution := by
  intro θ hθ hh
  refine ⟨by simpa only [chenA_card_eq_primeCounting] using hPNT, ?_⟩
  intro ε hε
  have he : 0<ε/2 := by positivity
  filter_upwards [chen_prime_reduced_error_of_primitive_mangoldt hBV hθ hh (ε/2) he,
    chen_medium_reduced_loss_small (θ:=θ) (by linarith only [hh]) he,
    eventually_ge_atTop (2:ℕ)] with N hred hloss hN _
  have hmed := chenMediumError_le_reducedError_add (D:=chenPowerLevel θ N) hN
  have hscale : 0 ≤ chenLogScale N := by unfold chenLogScale; positivity
  exact ⟨by nlinarith only [hred,mul_nonneg hε.le hscale], by linarith only [hmed,hred,hloss]⟩

theorem chenPrimeAPDistribution_of_pnt_and_smallConductor
    (hPNT : Tendsto (fun N : ℕ => (N.primeCounting:ℝ)/((N:ℝ)/Real.log (N:ℝ))) atTop (𝓝 1))
    (hSmall : SmallConductorPrimeTwists) : ChenPrimeAPDistribution :=
  chenPrimeAPDistribution_of_pnt_and_primitiveMangoldt hPNT (bombieri_vinogradov_of_smallConductor hSmall)

end FareyGoldbach
