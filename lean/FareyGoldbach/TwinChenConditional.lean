import FareyGoldbach.TwinChenSieveTerms
import FareyGoldbach.TwinChenBoundedSwitching
import FareyGoldbach.ChenAPSwitchingPower

/-! # Quantitative Chen bounds for shifted primes from distribution estimates -/

open Filter
open scoped Classical Topology

namespace FareyGoldbach

private theorem modulus_shift {X r : ℕ} {δ : ℝ} (hδ : 0≤δ) (h : (r:ℝ)≤(X:ℝ)^δ) :
    (r:ℝ)≤((X+3:ℕ):ℝ)^δ :=
  h.trans (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr (by omega)) hδ)

private theorem logScale_le {M : ℕ} (hM : 2≤M) (r : ℕ) :
    chenAPLogScale M r≤2*twinChenSieveScale M r := by
  have hS : 0≤chenAPLogScale M r := by unfold chenAPLogScale; positivity
  have hh := mul_le_mul_of_nonneg_right (twinChenU_ge_half hM r) hS
  unfold twinChenSieveScale
  linarith only [hh]

private theorem shifted_logScale {X r : ℕ} (hX : 3≤X) (hr : 0<r) :
    chenAPLogScale X r≤8*twinChenSieveScale (X+3) r := by
  have hx : (3:ℝ)≤X := by exact_mod_cast hX
  have hφ : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hl : 0<Real.log (X:ℝ) := Real.log_pos (Nat.one_lt_cast.mpr (by omega))
  have hl' : 0<Real.log ((X+3:ℕ):ℝ) := Real.log_pos (Nat.one_lt_cast.mpr (by omega))
  have hxx : ((X+3:ℕ):ℝ)≤(X:ℝ)^2 := by
    push_cast
    nlinarith only [hx,mul_nonneg (sub_nonneg.mpr hx) (Nat.cast_nonneg X)]
  have hlog := Real.log_le_log (Nat.cast_pos.mpr (by omega : 0<X+3)) hxx
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hs : chenAPLogScale X r≤4*chenAPLogScale (X+3) r := by
    unfold chenAPLogScale
    rw [←mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    calc
      _ ≤ (X:ℝ)*((r.totient:ℝ)*(2*Real.log (X:ℝ))^2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hl'.le hlog 2) hφ.le) (Nat.cast_nonneg _)
      _ = (4*(X:ℝ))*((r.totient:ℝ)*Real.log (X:ℝ)^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (by omega : X≤X+3)) (by norm_num)) (by positivity)
  linarith only [hs,logScale_le (M:=X+3) (by omega) r]

private theorem transfer_count {X r : ℕ} {m B : ℝ} (hX : 3≤X) (hr : 0<r) (hm : 0<m)
    (hB : (m/2)*twinChenSieveScale (X+3) r≤B) :
    (m/16)*(X:ℝ)/((r.totient:ℝ)*Real.log (X:ℝ)^2)≤B := by
  rw [mul_div_assoc]
  change (m/16)*chenAPLogScale X r≤B
  calc _ ≤ (m/16)*(8*twinChenSieveScale (X+3) r) :=
            mul_le_mul_of_nonneg_left (shifted_logScale hX hr) (by positivity)
       _ = (m/2)*twinChenSieveScale (X+3) r := by ring
       _ ≤ B := hB

private theorem balanced_cutoff_error {δ εcut η ε : ℝ} (hδcut : δ<εcut)
    (hεη : εcut<η) (hη : η<1/6) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ r : ℕ, 0<r → (r:ℝ)≤(N:ℝ)^δ →
      (chenPowerLevel (1-εcut) N:ℝ)+1+(chenUpperCutoff N:ℝ) ≤ ε*chenAPLogScale N r := by
  have habs := chenAP_log_power_absorb (δ:=δ) (β:=1-εcut) (C:=3) 0 2
    (by linarith only [hδcut]) (by norm_num) hε
  filter_upwards [habs,eventually_ge_atTop (1:ℕ)] with N h N₁ r hr hpow
  have hn : 1≤(N:ℝ) := Nat.one_le_cast.mpr N₁
  have h₁ : 1≤(N:ℝ)^(1-εcut) := Real.one_le_rpow hn (by linarith only [hεη,hη])
  have h₂ : (N:ℝ)^(1/3:ℝ)≤(N:ℝ)^(1-εcut) :=
    Real.rpow_le_rpow_of_exponent_le hn (by linarith only [hεη,hη])
  have hM : (chenPowerLevel (1-εcut) N:ℝ)≤(N:ℝ)^(1-εcut) := Nat.floor_le (by positivity)
  have hy : (chenUpperCutoff N:ℝ)≤(N:ℝ)^(1/3:ℝ) := Nat.floor_le (by positivity)
  have ht := h r hr hpow
  simp only [pow_zero,mul_one] at ht
  exact (show _≤3*(N:ℝ)^(1-εcut) by linarith only [h₁,h₂,hM,hy]).trans ht


/-- The two distribution estimates imply the shifted-prime Chen lower bound. -/
theorem twinChen_count_lower_of_distributions {δ θ : ℝ}
    (hδ₀ : 0≤δ) (hδ : δ<1/8) (hθ₁ : 11/24<θ) (hθ₂ : θ<1/2)
    (hmargin : 0<chenMainMargin θ) (hA : TwinChenPrimeDistributionAt δ θ)
    (hB : TwinChenCarrierDistributionAt δ θ chenSwitchIntegral twinChenClassicCarrier) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ X : ℕ in atTop, ∀ (r b : ℕ), 0<r → (r:ℝ)≤(X:ℝ)^δ →
      b.Coprime r → (b+2).Coprime r → c*(X:ℝ)/((r.totient:ℝ)*Real.log (X:ℝ)^2)≤
        ((twinChenRepresentations X r b).card:ℝ) := by
  let m := chenMainMargin θ
  have hm : 0<m := hmargin
  refine ⟨m/16,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (2^24:ℕ), twinChen_sieve_terms_of_distributions
    hδ₀ hδ hθ₁ hθ₂ chenSwitchIntegral_nonneg hA hB (ε:=m/8) (by positivity),
    twinChen_eventually_add_three (chenAP_power_error_eventually_le hδ (ε:=m/16) (by positivity))]
    with X hX ht hp
  intro r b hr hrX hb hb'
  have hrM := modulus_shift hδ₀ hrX
  obtain ⟨hLo,hMed,hSwi⟩ := ht r b hr hrM hb hb'
  let M := X+3
  let T := twinChenSieveScale M r
  have hM : 2^24≤M := by dsimp only [M]; omega
  have hSw := twinChen_switching_inequality hM hb'
  change twinChenLowerTerm X r b-(1/2)*twinChenMediumTerm X r b-
    (1/2)*twinChenSiftedCarrierTerm M r b twinChenClassicCarrier-
    (2*(M:ℝ)^(7/8:ℝ)+(M:ℝ)^(1/3:ℝ))≤_ at hSw
  change (chenLowerMainCoeff θ-m/8)*T≤_ at hLo
  change _≤(chenMediumMainCoeff θ+m/8)*T at hMed
  change _≤(chenSwitchedMainCoeff θ+m/8)*T at hSwi
  have hhalf := logScale_le (M:=M) (by omega) r
  have htol := mul_le_mul_of_nonneg_left hhalf (show 0≤m/16 by positivity)
  have he : m*T=(chenLowerMainCoeff θ-(1/2)*chenMediumMainCoeff θ-
    (1/2)*chenSwitchedMainCoeff θ)*T := rfl
  have hT : 0≤T := by
    have hS : 0≤chenAPLogScale M r := by unfold chenAPLogScale; positivity
    linarith only [hhalf,hS]
  have hPow := hp r hr hrM
  apply transfer_count (by omega) hr hm
  change (m/2)*T≤_
  linarith only [hSw,hLo,hMed,hSwi,hPow,htol,he,mul_nonneg hm.le hT]

/-- The balanced switching estimate gives a quantitative bound for complements
whose smaller prime factor is at most the prescribed power of the larger. -/
theorem twinChen_bounded_count_lower_of_distributions {δ θ η εcut α : ℝ}
    (hδ₀ : 0≤δ) (hδ : δ<1/8) (hδcut : δ<εcut) (hη : 0<η) (hη' : η<1/6)
    (hε : 0<εcut) (hεη : εcut<η) (hα : 1<α)
    (hratio : (1/2-η)/(1/2+η-εcut)≤α-1) (hθ₁ : 11/24<θ) (hθ₂ : θ<1/2)
    (hmargin : (2/θ)*(2*Real.log (1/(1-2*η)))<chenMainMargin θ)
    (hA : TwinChenPrimeDistributionAt δ θ)
    (hB : TwinChenCarrierDistributionAt δ θ chenSwitchIntegral twinChenClassicCarrier)
    (hBalanced : TwinChenCarrierDistributionAt δ θ (2*Real.log (1/(1-2*η))) (twinChenBoundedCarrier η)) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ X : ℕ in atTop, ∀ (r b : ℕ), 0<r → (r:ℝ)≤(X:ℝ)^δ →
      b.Coprime r → (b+2).Coprime r → c*(X:ℝ)/((r.totient:ℝ)*Real.log (X:ℝ)^2)≤
        ((twinChenBoundedRepresentations X r b α).card:ℝ) := by
  let t := (2/θ)*(2*Real.log (1/(1-2*η)))
  let m := chenMainMargin θ-t
  have hm : 0<m := sub_pos.mpr hmargin
  have hc : 0≤2*Real.log (1/(1-2*η)) := by
    apply mul_nonneg (by norm_num)
    apply Real.log_nonneg
    apply (one_le_div (by linarith only [hη'] : 0<1-2*η)).mpr
    linarith only [hη]
  refine ⟨m/16,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (2^24:ℕ), twinChen_sieve_terms_of_distributions
    hδ₀ hδ hθ₁ hθ₂ chenSwitchIntegral_nonneg hA hB (ε:=m/16) (by positivity),
    twinChen_sieve_terms_of_distributions hδ₀ hδ hθ₁ hθ₂ hc hA hBalanced (ε:=m/16) (by positivity),
    twinChen_eventually_add_three (chenAP_power_error_eventually_le hδ (ε:=m/32) (by positivity)),
    twinChen_eventually_add_three (balanced_cutoff_error hδcut hεη hη' (ε:=m/32) (by positivity))]
    with X hX ht ht' hp hcut
  intro r b hr hrX hb hb'
  have hrM := modulus_shift hδ₀ hrX
  obtain ⟨hLo,hMed,hSwi⟩ := ht r b hr hrM hb hb'
  have hBal := (ht' r b hr hrM hb hb').2.2
  let M := X+3
  let T := twinChenSieveScale M r
  have hM : 2^24≤M := by dsimp only [M]; omega
  have hSw := twinChen_bounded_switching_inequality hM hb' hη hη' hε hεη hα hratio
  change twinChenLowerTerm X r b-(1/2)*twinChenMediumTerm X r b-
    (1/2)*twinChenSiftedCarrierTerm M r b twinChenClassicCarrier-
    (2*(M:ℝ)^(7/8:ℝ)+(M:ℝ)^(1/3:ℝ))-twinChenSiftedCarrierTerm M r b (twinChenBoundedCarrier η)-
    ((chenPowerLevel (1-εcut) M:ℝ)+1+(chenUpperCutoff M:ℝ))≤_ at hSw
  change (chenLowerMainCoeff θ-m/16)*T≤_ at hLo
  change _≤(chenMediumMainCoeff θ+m/16)*T at hMed
  change _≤(chenSwitchedMainCoeff θ+m/16)*T at hSwi
  change _≤(t+m/16)*T at hBal
  have hhalf := logScale_le (M:=M) (by omega) r
  have htol := mul_le_mul_of_nonneg_left hhalf (show 0≤m/32 by positivity)
  have he : m*T=(chenLowerMainCoeff θ-(1/2)*chenMediumMainCoeff θ-
    (1/2)*chenSwitchedMainCoeff θ-t)*T := rfl
  have hT : 0≤T := by
    have hS : 0≤chenAPLogScale M r := by unfold chenAPLogScale; positivity
    linarith only [hhalf,hS]
  have hPow := hp r hr hrM
  have hCut := hcut r hr hrM
  apply transfer_count (by omega) hr hm
  change (m/2)*T≤_
  linarith only [hSw,hLo,hMed,hSwi,hBal,hPow,hCut,htol,he,mul_nonneg hm.le hT]

end FareyGoldbach
