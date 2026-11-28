import FareyGoldbach.TwinChenDistributionInterfaces
import FareyGoldbach.TwinChenComparisons

/-! # Sieve estimates for shifted primes and an arbitrary switched carrier -/

open Filter
open scoped Classical Topology

namespace FareyGoldbach

theorem twinChen_eventually_add_three {P : ℕ→Prop} (h : ∀ᶠ M : ℕ in atTop, P M) :
    ∀ᶠ X : ℕ in atTop, P (X+3) := by
  obtain ⟨M,hM⟩ := Filter.eventually_atTop.mp h
  exact Filter.eventually_atTop.mpr ⟨M,fun X hX => hM _ (by omega)⟩

noncomputable def twinChenSieveScale (M r : ℕ) : ℝ := twinChenU M r*chenAPLogScale M r

noncomputable def twinChenLowerTerm (X r b : ℕ) : ℝ :=
  (chenSifted (2*r) (chenLowerCutoff (X+3)) (twinChenAPA X r b)).card

noncomputable def twinChenMediumTerm (X r b : ℕ) : ℝ :=
  ∑ q ∈ chenMediumPrimes (chenLowerCutoff (X+3)) (chenUpperCutoff (X+3)),
    ((chenSifted (2*r) (chenLowerCutoff (X+3)) (chenDivisible (twinChenAPA X r b) q)).card:ℝ)

noncomputable def twinChenSiftedCarrierTerm (M r b : ℕ) (carrier : ℕ→ℕ→ℕ→Finset ℕ) : ℝ :=
  (chenSifted (2*r) (chenUpperCutoff M) (carrier M r b)).card

theorem twinChen_sieve_terms_of_distributions {δ θ c : ℝ} (hδ₀ : 0≤δ) (hδ : δ<1/8)
    (hθ₁ : 11/24<θ) (hθ₂ : θ<1/2) (hc : 0≤c) {carrier : ℕ→ℕ→ℕ→Finset ℕ}
    (hA : TwinChenPrimeDistributionAt δ θ) (hB : TwinChenCarrierDistributionAt δ θ c carrier)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ X : ℕ in atTop, ∀ (r b : ℕ), 0<r → (r:ℝ)≤((X+3:ℕ):ℝ)^δ →
      b.Coprime r → (b+2).Coprime r →
        (chenLowerMainCoeff θ-ε)*twinChenSieveScale (X+3) r≤twinChenLowerTerm X r b ∧
        twinChenMediumTerm X r b≤(chenMediumMainCoeff θ+ε)*twinChenSieveScale (X+3) r ∧
        twinChenSiftedCarrierTerm (X+3) r b carrier≤((2/θ)*c+ε)*twinChenSieveScale (X+3) r := by
  let a := chenLowerMainCoeff θ
  let m := chenMediumMainCoeff θ
  let b := 2/θ
  have ⟨ha,hm,hb⟩ : 0<a ∧ 0≤m ∧ 0<b := chen_coeff_pos hθ₁
  obtain ⟨τ,hτ,_,hτa,hbud₁,hbud₂,hbud₃⟩ := chen_profile_budget ha hm hb.le hc hε
  filter_upwards [eventually_ge_atTop (2^24:ℕ), hA τ hτ,
    twinChen_eventually_add_three (hB τ hτ), twinChen_eventually_add_three
      (twinChenRosserMainComparisons_unconditional hδ₀ hδ hθ₁ hθ₂ τ hτ)]
    with X hX hA' hB' hProfile
  intro r residue hr hrpow hpr hcop
  let N := X+3
  let K := 2*r
  let z := chenLowerCutoff N
  let y := chenUpperCutoff N
  let D := chenPowerLevel θ N
  let A := twinChenAPA X r residue
  let B := carrier N r residue
  let R := chenAPMassScale N r
  let v := twinChenU N r/Real.log (N:ℝ)
  let T := twinChenSieveScale N r
  have hN : 2^24≤N := by dsimp only [N]; omega
  have hN₂ : 2≤N := by omega
  have hL : 0<Real.log (N:ℝ) := Real.log_pos (Nat.one_lt_cast.mpr hN₂)
  have hφ : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hU := twinChenU_ge_half hN₂ r
  have hU₀ : 0≤twinChenU N r := by linarith only [hU]
  have hv : 0≤v := by dsimp [v]; positivity
  have hR : 0<R := by dsimp [R,chenAPMassScale]; positivity
  have hT : T=R*v := by
    dsimp only [T,twinChenSieveScale,chenAPLogScale,R,chenAPMassScale,v]
    field_simp
  have hT₀ : 0≤T := hT.symm ▸ mul_nonneg hR.le hv
  have hS : 0≤chenAPLogScale N r := by unfold chenAPLogScale; positivity
  have hlog : chenAPLogScale N r≤2*T := by
    have hh := mul_le_mul_of_nonneg_right hU hS
    dsimp only [T,twinChenSieveScale]
    linarith only [hh]
  have hErr := mul_le_mul_of_nonneg_left hlog hτ.le
  obtain ⟨hAr,he₁,he₂⟩ := hA' r residue hr hrpow hpr hcop
  obtain ⟨hBu,he₃⟩ := hB' r residue hr hrpow hpr hcop
  have hAr' := abs_le.mp hAr
  change -τ≤(A.card:ℝ)/R-1 ∧ (A.card:ℝ)/R-1≤τ at hAr'
  have hAl : (1-τ)*R≤(A.card:ℝ) := (le_div_iff₀ hR).mp (by linarith only [hAr'.1])
  have hAu : (A.card:ℝ)≤(1+τ)*R := (div_le_iff₀ hR).mp (by linarith only [hAr'.2])
  have ⟨hP₁,hP₂,hP₃⟩ := hProfile r hr hrpow
  obtain ⟨hFin₁,hFin₂,hFin₃⟩ := chen_finite_sieve_terms_for_carriers hθ₁ hN K A B
  let P := chenSiftingProduct K z
  let P' := chenSiftingProduct K y
  let W := ∑ q∈chenMediumPrimes z y,
    if q∣K then 0 else chenDivisorDensity q*linearSieveMain true P (D/q) chenDivisorDensity
  have hLow : ((1-τ)*(a-τ))*T ≤ (A.card:ℝ)*linearSieveMain false P D chenDivisorDensity := by
    calc
      _ = ((1-τ)*R)*((a-τ)*v) := by rw [hT]; ring
      _ ≤ (A.card:ℝ)*((a-τ)*v) := mul_le_mul_of_nonneg_right hAl (mul_nonneg (sub_nonneg.mpr hτa) hv)
      _ ≤ _ := mul_le_mul_of_nonneg_left hP₁ (Nat.cast_nonneg _)
  have hMed : (A.card:ℝ)*W≤((1+τ)*(m+τ))*T := by
    calc
      _ ≤ (A.card:ℝ)*((m+τ)*v) := mul_le_mul_of_nonneg_left hP₂ (Nat.cast_nonneg _)
      _ ≤ ((1+τ)*R)*((m+τ)*v) := mul_le_mul_of_nonneg_right hAu (by positivity)
      _ = _ := by rw [hT]; ring
  have hSwi : (B.card:ℝ)*linearSieveMain true P' D chenDivisorDensity≤((c+τ)*(b+τ))*T := by
    calc
      _ ≤ (B.card:ℝ)*((b+τ)*v) := mul_le_mul_of_nonneg_left hP₃ (Nat.cast_nonneg _)
      _ ≤ ((c+τ)*R)*((b+τ)*v) := mul_le_mul_of_nonneg_right hBu (by positivity)
      _ = _ := by rw [hT]; ring
  have h₁ := mul_le_mul_of_nonneg_right hbud₁ hT₀
  have h₂ := mul_le_mul_of_nonneg_right hbud₂ hT₀
  have h₃ := mul_le_mul_of_nonneg_right hbud₃ hT₀
  change (A.card:ℝ)*linearSieveMain false P D chenDivisorDensity -
    chenReducedError K D (twinChenPrimeError X r residue) ≤ twinChenLowerTerm X r residue at hFin₁
  change twinChenMediumTerm X r residue ≤ (A.card:ℝ)*W+twinChenMediumError X r residue D at hFin₂
  change twinChenSiftedCarrierTerm N r residue carrier ≤ (B.card:ℝ)*linearSieveMain true P' D chenDivisorDensity +
    chenReducedError K D (chenAPError B B.card) at hFin₃
  change (a-ε)*T≤twinChenLowerTerm X r residue ∧ twinChenMediumTerm X r residue≤(m+ε)*T ∧
    twinChenSiftedCarrierTerm N r residue carrier≤(b*c+ε)*T
  exact ⟨by linarith only [h₁,hLow,hFin₁,he₁,hErr],
    by linarith only [h₂,hMed,hFin₂,he₂,hErr],
    by linarith only [h₃,hSwi,hFin₃,he₃,hErr]⟩

end FareyGoldbach
