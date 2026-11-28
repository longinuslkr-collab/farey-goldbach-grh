import FareyGoldbach.ChenMediumReciprocal
import FareyGoldbach.ChenActualSieveParameters

/-! # A prime-reciprocal majorant for an unrestricted inner switching band -/

open Filter Finset
open scoped Topology Classical

namespace FareyGoldbach

noncomputable def chenSwitchBandMass (N : ℕ) (a b : ℝ) : ℝ :=
  ∑ p∈chenMediumPrimes (chenPowerLevel a N) (chenPowerLevel b N), 1/(p:ℝ)

noncomputable def chenSwitchBandKernel (N : ℕ) (a b θ : ℝ) : ℝ :=
  ∑ p∈chenMediumPrimes (chenPowerLevel a N) (chenPowerLevel b N),
    (1/(p:ℝ))*(1/(θ-Real.log (p:ℝ)/Real.log (N:ℝ)))

theorem chenSwitchBandMass_tendsto {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    Tendsto (fun N => chenSwitchBandMass N a b) atTop (𝓝 (Real.log b-Real.log a)) :=
  chen_prime_harmonic_band_tendsto chen_prime_reciprocal_mertens ha hab

/-- A prime divisor of N discarded by the coprime band contributes at most
one lower-endpoint reciprocal times a uniform bound for the log kernel. -/
theorem chenSwitchBandKernel_eventually_le {a b θ : ℝ} (ha : 0<a) (hab : a<b)
    (hbθ : b<θ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, chenSwitchBandKernel N a b θ ≤
      (∫ u in a..b, 2/(u*(θ-u)))/2 + ε := by
  let Q (N : ℕ) := chenMediumPrimes (chenPowerLevel a N) (chenPowerLevel b N)
  let T (N : ℕ) := ∑ p∈Q N, if p∣N then (0:ℝ) else
    (1/(p.totient:ℝ))*(2/(θ-Real.log (p:ℝ)/Real.log (N:ℝ)))
  have hT : Tendsto T atTop (𝓝 (∫ u in a..b, 2/(u*(θ-u)))) :=
    chen_prime_reciprocal_kernel_tendsto ha hab hbθ
  have hc := (chenLogTwo_div_powerLevel_tendsto ha).const_mul (2/(θ-b))
  rw [mul_zero] at hc
  have hlim := (hT.div_const 2).add hc
  rw [add_zero] at hlim
  filter_upwards [hlim.eventually_lt_const (lt_add_of_pos_right _ hε),
    eventually_ge_atTop (2:ℕ),(chenPowerLevel_tendsto_atTop ha).eventually_ge_atTop 1]
    with N hlim hn hz
  let z := chenPowerLevel a N
  let H := 1/((z:ℝ)*(θ-b))
  let B := (Q N).filter (fun p => p∣N)
  have hnr : (1:ℝ)<N := by exact_mod_cast hn
  have hnr₀ : (0:ℝ)<N := zero_lt_one.trans hnr
  have hL := Real.log_pos hnr
  have hz' : (0:ℝ)<z := Nat.cast_pos.mpr hz
  have hθ := sub_pos.mpr hbθ
  have hpt (p : ℕ) (hp : p∈Q N) :
      1/(p:ℝ)*(1/(θ-Real.log (p:ℝ)/Real.log (N:ℝ))) ≤
      (if p∣N then (0:ℝ) else (1/(p.totient:ℝ))*(2/(θ-Real.log (p:ℝ)/Real.log (N:ℝ))))/2
      + (if p∣N then H else 0) := by
    obtain ⟨hI,hpr⟩ := mem_filter.mp hp
    obtain ⟨hpz,hpb⟩ := mem_Ico.mp hI
    have hp' : (0:ℝ)<p := Nat.cast_pos.mpr hpr.pos
    have hpa : (z:ℝ)≤p := Nat.cast_le.mpr hpz
    have hpu : (p:ℝ)≤(N:ℝ)^b := (Nat.cast_le.mpr hpb.le).trans
      (Nat.floor_le (Real.rpow_nonneg hnr₀.le _))
    have hlog := Real.log_le_log hp' hpu
    rw [Real.log_rpow hnr₀] at hlog
    have htag := (div_le_iff₀ hL).mpr hlog
    have hd : 0<θ-Real.log (p:ℝ)/Real.log (N:ℝ) := by linarith
    by_cases hpn : p∣N
    · simp only [hpn,ite_true,zero_div,zero_add,H]
      rw [one_div_mul_one_div]
      exact one_div_le_one_div_of_le (mul_pos hz' hθ)
        (mul_le_mul hpa (sub_le_sub_left htag θ) hθ.le hp'.le)
    · simp only [hpn,ite_false,add_zero]
      calc _ ≤ (1/(p.totient:ℝ))*(1/(θ-Real.log (p:ℝ)/Real.log (N:ℝ))) :=
            mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le
              (Nat.cast_pos.mpr (Nat.totient_pos.mpr hpr.pos)) (Nat.cast_le.mpr (Nat.totient_le p)))
              (by positivity)
        _ = _ := by ring
  have hbad : B⊆N.primeFactors := by
    intro p hp
    obtain ⟨hp,hd⟩ := mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(mem_filter.mp hp).2,hd,by omega⟩
  have hcard := (Nat.cast_le (α:=ℝ).mpr (card_le_card hbad)).trans
    (primeFactors_card_le_two_log (by omega : 1≤N))
  have hsum : (∑ p∈Q N, if p∣N then H else 0) = (B.card:ℝ)*H := by
    simp [B,Finset.sum_ite]
  have hh := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib,hsum,← Finset.sum_div] at hh
  refine hh.trans (le_trans (add_le_add_right (mul_le_mul_of_nonneg_right hcard
    (show 0≤H by dsimp [H]; positivity)) _) ?_)
  apply le_trans _ hlim.le
  change T N/2 + 2*Real.log (2*(N:ℝ))*H ≤ T N/2 + (2/(θ-b))*(Real.log (2*(N:ℝ))/(z:ℝ))
  dsimp only [H]
  exact le_of_eq (by simp only [div_eq_mul_inv,mul_inv_rev]; ring)

end FareyGoldbach
