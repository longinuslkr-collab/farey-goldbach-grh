/-
Adapted from subfish-zhou/goldbach-lean, SuzukiUpperRosserAllDepth.lean,
commit 9d4c3a4010d42aedd9e7231bf94386019cfffccc. Licensed under Apache-2.0.
This version permits 1 < s in the finite upper-density comparison.
-/
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserAllDepth

/-! # All-depth upper Rosser estimate at every first-branch parameter above one -/

open Set Filter Topology
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

namespace FareyGoldbach

noncomputable section

theorem upperRosserDensity_at_natCeil_above_one
    (H : Section13HatLayers) (hH : Section13HatSourceContract H)
    (S : BoundingSieve)
    {C K d Δ : ℝ} (hall : ∀ N : ℕ, 1 ≤ N →
      Lemma144MovingDomainNatCeilAt S H C K d Δ N 2)
    (D : ℕ) (s : ℝ)
    (hD : 2 ≤ D) (hslo : 1 < s) (_hshi : s ≤ 4)
    (hsSigma : s ≤ sourceSigma (D : ℝ) d)
    (hz2 : 2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors,
      p < ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) ≤
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
        (suzukiContinuousUpperFactor s +
          C * Real.exp (Real.sqrt K) *
            errorEnvelope H
              (2 * S.prodPrimes.primeFactors.card + 1)
              (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-Δ)) := by
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  let m : ℕ := S.prodPrimes.primeFactors.card
  let N : ℕ := 2 * m + 1
  have hNodd : Odd N := by dsimp [N]; exact ⟨m, by omega⟩
  have hN1 : 1 ≤ N := by dsimp [N]; omega
  have hsdom : s ∈ KappaOneModel.parityDomain 2 N := by
    simpa [KappaOneModel.parityDomain, Nat.odd_iff.mp hNodd] using
      (show (2:ℝ)-1<s by linarith)
  have hSuzuki := hall N hN1 D (by omega) hD s hsdom hsSigma hz2
  have hfinite := finiteSourceLayer_odd_le_suzukiContinuousUpperFactor_sub_one
    H hH m hslo
  have hVeq : suzukiVProduct S (z : ℝ) =
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    unfold suzukiVProduct
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
    congr 1
    ext p
    simp only [Finset.mem_filter]
    constructor
    · exact fun hp => hp.1
    · intro hp
      exact ⟨hp, by simpa [z] using hcut p hp⟩
  have hzD : z ≤ D := by
    apply Nat.ceil_le.mpr
    have hbase : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
    have hexp : 1 / s ≤ (1 : ℝ) := by
      rw [div_le_one (by linarith : 0 < s)]
      linarith
    simpa [z] using Real.rpow_le_rpow_of_exponent_le hbase hexp
  have hlevel : ∀ p ∈ S.prodPrimes.primeFactors, p < D := by
    intro p hp
    exact lt_of_lt_of_le (hcut p hp) hzD
  have hexact := upperRosserSuzukiExactBridge S D z (by omega) hlevel
    (by simpa [z] using hcut)
  dsimp only [N, m, z] at hSuzuki hexact ⊢
  rw [hVeq] at hSuzuki
  have hprod : 0 ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    rw [← hVeq]
    exact (suzukiVProduct_pos S (z : ℝ)).le
  calc
    S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) ≤
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
          suzukiActualT S
            (2 * S.prodPrimes.primeFactors.card + 1) D z := by
              simpa [z] using hexact
    _ ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
          (finiteSourceLayer 1 2
              (2 * S.prodPrimes.primeFactors.card + 1) s +
            C * Real.exp (Real.sqrt K) *
              errorEnvelope H
                (2 * S.prodPrimes.primeFactors.card + 1)
                (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-Δ)) := by
          gcongr
    _ ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
        (suzukiContinuousUpperFactor s +
          C * Real.exp (Real.sqrt K) *
            errorEnvelope H
              (2 * S.prodPrimes.primeFactors.card + 1)
              (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-Δ)) := by
          have hf := hfinite
          dsimp [m] at hf
          nlinarith only [mul_nonneg hprod (sub_nonneg.mpr hf)]

/-- Production wrapper: the all-depth Suzuki producer feeds the direct odd-depth
consumer with constants selected before the bounding sieve.  The exact bridge
is a proved internal dependency, not a proposition-valued premise. -/
theorem exists_upperRosserDensity_at_natCeil_above_one
    (H : Section13HatLayers) {d Δ Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hsrc : SuzukiClaim145SourceParameters d Δ Θ) :
    ∃ C1min : ℝ, 0 < C1min ∧
      ∀ C1 : ℝ, C1min ≤ C1 →
        ∃ C145 Clow C : ℝ,
          0 < C145 ∧ 0 ≤ Clow ∧ 3 ≤ C ∧
          ∀ (S : BoundingSieve) (K : ℝ),
            2 ≤ K → HasDimensionOneLocalProductBound S K →
            ∀ D : ℕ, 2 ≤ D → ∀ s : ℝ,
              1 < s → s ≤ 4 → s ≤ sourceSigma (D : ℝ) d →
              2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊ →
              (∀ p ∈ S.prodPrimes.primeFactors,
                p < ⌈(D : ℝ) ^ (1 / s)⌉₊) →
              S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) ≤
                AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
                  (suzukiContinuousUpperFactor s +
                    C * Real.exp (Real.sqrt K) *
                      errorEnvelope H
                        (2 * S.prodPrimes.primeFactors.card + 1)
                        (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-Δ)) := by
  obtain ⟨C1min, hC1min, hall⟩ :=
    exists_lemma14_4_movingRange_rounded_allDepth_uniform_in_S_of_source H hH hsrc
  refine ⟨C1min, hC1min, ?_⟩
  intro C1 hC1
  obtain ⟨C145, Clow, C, hC145, hClow, hC, hdepth⟩ := hall C1 hC1
  refine ⟨C145, Clow, C, hC145, hClow, hC, ?_⟩
  intro S K hK hlocal D hD s hslo hshi hsSigma hz2 hcut
  exact upperRosserDensity_at_natCeil_above_one H hH S
    (hdepth S K hK hlocal) D s hD hslo hshi hsSigma hz2 hcut


end
end FareyGoldbach
