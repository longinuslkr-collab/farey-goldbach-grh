import FareyGoldbach.ChenAPBalancedDistributionInterface
import FareyGoldbach.ChenBalancedSwitching
import FareyGoldbach.ChenAPConditional
import FareyGoldbach.ChenAPSwitchingPower

/-! # The bounded-factor Chen theorem from three distribution estimates -/

open Filter
open scoped Classical Topology

namespace FareyGoldbach

private noncomputable def balancedSiftedTerm (N r b : ℕ) (η : ℝ) : ℝ :=
  (chenSifted (r*N) (chenUpperCutoff N) (chenAPBalancedB N r b (chenPowerLevel (1/2-η) N))).card

private theorem balanced_term_of_distribution {δ θ η : ℝ} (hδ : δ<1)
    (hη : 0<η) (hη' : η<1/6) (hθ₁ : 11/24<θ) (hθ₂ : θ<1/2)
    (hB : ChenAPBalancedDistributionAt δ θ η) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ (r b₁ b₂ : ℕ), 0<r → (r:ℝ)≤(N:ℝ)^δ →
      b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
        balancedSiftedTerm N r b₂ η ≤ (2/θ*(2*Real.log (1/(1-2*η)))+ε)*apSieveScale N r := by
  let b := 2/θ
  let c := 2*Real.log (1/(1-2*η))
  have ⟨ha,hm,hb⟩ := chen_coeff_pos hθ₁
  have hc : 0≤c := by
    apply mul_nonneg (by norm_num)
    apply Real.log_nonneg
    apply (one_le_div (by linarith only [hη'] : 0<1-2*η)).mpr
    linarith only [hη]
  obtain ⟨τ,hτ,_,_,_,_,hbud⟩ := chen_profile_budget ha hm hb.le hc hε
  filter_upwards [eventually_ge_atTop (2^24:ℕ), hB τ hτ,
    chenAPRosserMainComparisons_unconditional hθ₁ hθ₂ τ hτ] with N hN hdist hprofile hEven
  intro r b₁ b₂ hr hrpow hb₁ hb₂ hcompat
  let B := chenAPBalancedB N r b₂ (chenPowerLevel (1/2-η) N)
  let K := r*N
  let R := chenAPMassScale N r
  let v := chenCanonicalU K/Real.log (N:ℝ)
  let T := apSieveScale N r
  have hn : 1≤(N:ℝ) := Nat.one_le_cast.mpr (by omega)
  have hrN : r≤N := Nat.cast_le.mp (hrpow.trans
    (by simpa using Real.rpow_le_rpow_of_exponent_le hn hδ.le))
  have hlog : 0<Real.log (N:ℝ) := Real.log_pos (Nat.one_lt_cast.mpr (by omega))
  have hU := chenCanonicalU_ge_half (hEven.mul_left r)
    ((by omega : 2≤N).trans (Nat.le_mul_of_pos_left N hr))
  have hU₀ : 0≤chenCanonicalU K := by linarith only [hU]
  have hv : 0≤v := div_nonneg hU₀ hlog.le
  have hScale : 0≤chenAPLogScale N r := by unfold chenAPLogScale; positivity
  have hT₀ : 0≤T := mul_nonneg hU₀ hScale
  have hφ : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hT : T=R*v := by
    dsimp only [T,apSieveScale,chenAPLogScale,R,chenAPMassScale,v,K]
    field_simp
  have hhalf : chenAPLogScale N r≤2*T := by
    have hh := mul_le_mul_of_nonneg_right hU hScale
    dsimp only [T,apSieveScale]
    linarith only [hh]
  obtain ⟨hMass,hError⟩ := hdist hEven r b₁ b₂ hr hrpow hb₁ hb₂ hcompat
  have hPoly := (hprofile hEven r hr hrN).2.2
  have hfin := (chen_finite_sieve_terms_for_carriers hθ₁ hN K (∅ : Finset ℕ) B).2.2
  change balancedSiftedTerm N r b₂ η ≤
    (B.card:ℝ)*chenAPSwitchedPolynomial θ N K + chenReducedError K (chenPowerLevel θ N)
      (chenAPError B B.card) at hfin
  have hmain : (B.card:ℝ)*chenAPSwitchedPolynomial θ N K ≤ ((c+τ)*(b+τ))*T := by
    calc
      _ ≤ (B.card:ℝ)*((b+τ)*v) := mul_le_mul_of_nonneg_left hPoly (Nat.cast_nonneg _)
      _ ≤ ((c+τ)*R)*((b+τ)*v) := mul_le_mul_of_nonneg_right hMass (by positivity)
      _ = _ := by rw [hT]; ring
  have htol := mul_le_mul_of_nonneg_left hhalf hτ.le
  have hcoef := mul_le_mul_of_nonneg_right hbud hT₀
  change balancedSiftedTerm N r b₂ η ≤ (b*c+ε)*T
  change chenReducedError K (chenPowerLevel θ N) (chenAPError B B.card)≤τ*chenAPLogScale N r at hError
  change ((c+τ)*(b+τ)+2*τ)*T≤(c*b+ε)*T at hcoef
  linarith only [hfin,hmain,hError,htol,hcoef]

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

/-- A strict surplus over the balanced upper sieve gives a uniform positive
lower bound for bounded-factor representations in both prescribed classes. -/
theorem chen_ap_bounded_count_lower_of_distributions {δ θ η εcut α : ℝ}
    (hδ : δ<1/8) (hδcut : δ<εcut) (hη : 0<η) (hη' : η<1/6)
    (hε : 0<εcut) (hεη : εcut<η) (hα : 1<α)
    (hratio : (1/2-η)/(1/2+η-εcut)≤α-1) (hθ₁ : 11/24<θ) (hθ₂ : θ<1/2)
    (hmargin : (2/θ)*(2*Real.log (1/(1-2*η)))<chenMainMargin θ)
    (hA : ChenAPPrimeDistributionAt δ θ) (hB : ChenAPSwitchingDistributionAt δ θ)
    (hBalanced : ChenAPBalancedDistributionAt δ θ η) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (r b₁ b₂ : ℕ), 0<r → (r:ℝ)≤(N:ℝ)^δ →
        b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
        c*(N:ℝ)/((r.totient:ℝ)*Real.log (N:ℝ)^2) ≤
          ((chenAPBoundedRepresentations N r b₁ b₂ α).card:ℝ) := by
  let t := (2/θ)*(2*Real.log (1/(1-2*η)))
  let m := chenMainMargin θ-t
  have hm : 0<m := sub_pos.mpr hmargin
  have hδ₁ : δ<1 := by linarith only [hδ]
  refine ⟨m/4,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (2^24:ℕ),
    ap_sieve_terms_of_distributions hδ₁ hθ₁ hθ₂ hA hB (ε:=m/16) (by positivity),
    balanced_term_of_distribution hδ₁ hη hη' hθ₁ hθ₂ hBalanced (ε:=m/16) (by positivity),
    chenAP_power_error_eventually_le hδ (ε:=m/32) (by positivity),
    balanced_cutoff_error hδcut hεη hη' (ε:=m/32) (by positivity)]
    with N hN ht hbalanced hpow hcut hEven
  intro r b₁ b₂ hr hrpow hb₁ hb₂ hcompat
  have ⟨hLo,hMed,hSwi⟩ := ht hEven r b₁ b₂ hr hrpow hb₁ hb₂ hcompat
  have hBal := hbalanced hEven r b₁ b₂ hr hrpow hb₁ hb₂ hcompat
  have hSw := chen_ap_bounded_switching_inequality hN hb₂ hcompat hη hη' hε hεη hα hratio
  let T := apSieveScale N r
  have hU := chenCanonicalU_ge_half (hEven.mul_left r)
    ((by omega : 2≤N).trans (Nat.le_mul_of_pos_left N hr))
  have hScale : 0≤chenAPLogScale N r := by unfold chenAPLogScale; positivity
  have hhalf : chenAPLogScale N r≤2*T := by
    have hh := mul_le_mul_of_nonneg_right hU hScale
    dsimp only [T,apSieveScale]
    linarith only [hh]
  have htol := mul_le_mul_of_nonneg_left hhalf (show (0:ℝ)≤m/32 by positivity)
  have h₁ := hpow r hr hrpow
  have h₂ := hcut r hr hrpow
  change apLowerTerm N r b₁ - (1/2)*apMediumTerm N r b₁ - (1/2)*apSwitchedTerm N r b₂ -
    (2*(N:ℝ)^(7/8:ℝ)+(N:ℝ)^(1/3:ℝ)) - balancedSiftedTerm N r b₂ η -
    ((chenPowerLevel (1-εcut) N:ℝ)+1+(chenUpperCutoff N:ℝ)) ≤ _ at hSw
  change balancedSiftedTerm N r b₂ η ≤ (t+m/16)*T at hBal
  change (chenLowerMainCoeff θ-m/16)*T≤_ at hLo
  change _≤(chenMediumMainCoeff θ+m/16)*T at hMed
  change _≤(chenSwitchedMainCoeff θ+m/16)*T at hSwi
  have he : m*T = (chenLowerMainCoeff θ-(1/2)*chenMediumMainCoeff θ-
    (1/2)*chenSwitchedMainCoeff θ-t)*T := rfl
  have hT₀ : 0≤T := mul_nonneg (by linarith only [hU]) hScale
  have hCount : (m/2)*T≤((chenAPBoundedRepresentations N r b₁ b₂ α).card:ℝ) := by
    linarith only [hSw,hLo,hMed,hSwi,hBal,h₁,h₂,htol,he,mul_nonneg hm.le hT₀]
  rw [mul_div_assoc]
  change (m/4)*chenAPLogScale N r ≤ _
  calc _ ≤ (m/4)*(2*T) := mul_le_mul_of_nonneg_left hhalf (by positivity)
       _ = (m/2)*T := by ring
       _ ≤ _ := hCount

/-- Existence follows directly since the bounded-factor predicate excludes one. -/
theorem chen_ap_bounded_theorem_of_distributions {δ θ η εcut α : ℝ}
    (hδ : δ<1/8) (hδcut : δ<εcut) (hη : 0<η) (hη' : η<1/6)
    (hε : 0<εcut) (hεη : εcut<η) (hα : 1<α)
    (hratio : (1/2-η)/(1/2+η-εcut)≤α-1) (hθ₁ : 11/24<θ) (hθ₂ : θ<1/2)
    (hmargin : (2/θ)*(2*Real.log (1/(1-2*η)))<chenMainMargin θ)
    (hA : ChenAPPrimeDistributionAt δ θ) (hB : ChenAPSwitchingDistributionAt δ θ)
    (hBalanced : ChenAPBalancedDistributionAt δ θ η) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ (r b₁ b₂ : ℕ), 0<r → (r:ℝ)≤(N:ℝ)^δ →
      b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
      ∃ p m : ℕ, p.Prime ∧ IsAlmostPrimeTwoBounded α m ∧ 1<m ∧
        p+m=N ∧ p%r=b₁%r ∧ m%r=b₂%r := by
  obtain ⟨c,hc,hLower⟩ := chen_ap_bounded_count_lower_of_distributions hδ hδcut hη hη'
    hε hεη hα hratio hθ₁ hθ₂ hmargin hA hB hBalanced
  filter_upwards [hLower,eventually_ge_atTop (2:ℕ)] with N hLower hN hEven
  intro r b₁ b₂ hr hrpow hb₁ hb₂ hcompat
  have hL := hLower hEven r b₁ b₂ hr hrpow hb₁ hb₂ hcompat
  have hlog : 0<Real.log (N:ℝ) := Real.log_pos (Nat.one_lt_cast.mpr hN)
  have hφ : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hpos : (0:ℝ)<(chenAPBoundedRepresentations N r b₁ b₂ α).card :=
    (by positivity : 0<c*(N:ℝ)/((r.totient:ℝ)*Real.log (N:ℝ)^2)).trans_le hL
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (Nat.cast_pos.mp hpos)
  obtain ⟨hp,hm⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpR,hres₁,hres₂⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpN,hprime,_⟩ := Finset.mem_filter.mp hpR
  have hpN' : p≤N := by simpa using Finset.mem_range.mp hpN
  have hm₁ : 1<N-p := by
    rcases hm with h|⟨u,v,hu,hv,hprod,_⟩
    · exact h.one_lt
    · rw [hprod]
      exact hu.one_lt.trans_le (Nat.le_mul_of_pos_right u hv.pos)
  exact ⟨p,N-p,hprime,hm,hm₁,Nat.add_sub_of_le hpN',hres₁,hres₂⟩

end FareyGoldbach
