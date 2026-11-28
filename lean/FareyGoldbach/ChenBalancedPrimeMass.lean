import FareyGoldbach.ChenSwitchingKernel
import FareyGoldbach.PrimeNumberTheoremUnconditional

/-! # The first-prime sum for products of two balanced primes -/

open Filter Finset
open scoped Topology

namespace FareyGoldbach

noncomputable def chenBalancedFirstBand (N L : ℕ) := chenMediumPrimes L (chenPowerLevel (1/2) N+1)

noncomputable def chenBalancedPrimeMajorant (N L : ℕ) : ℝ :=
  ∑ p∈chenBalancedFirstBand N L, ((N/p).primeCounting:ℝ)

theorem chenBalanced_root_floor {N : ℕ} :
    (chenPowerLevel (1/2) N:ℝ)≤Real.sqrt N := by
  rw [Real.sqrt_eq_rpow]
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem chenBalanced_root_le_quot {N p : ℕ} (hp : 0<p) (hpy : p≤chenPowerLevel (1/2) N) :
    chenPowerLevel (1/2) N≤N/p := by
  let y := chenPowerLevel (1/2) N
  have hyy : y*y≤N := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg y : (0:ℝ)≤y) (chenBalanced_root_floor (N:=N)) 2
    rw [Real.sq_sqrt (Nat.cast_nonneg _),pow_two] at h
    exact_mod_cast h
  exact (Nat.le_div_iff_mul_le hp).mpr ((Nat.mul_le_mul_left y hpy).trans hyy)

theorem chenBalancedFirstBand_card_le (N L : ℕ) :
    (chenBalancedFirstBand N L).card≤chenPowerLevel (1/2) N := by
  have h : chenBalancedFirstBand N L⊆Icc 1 (chenPowerLevel (1/2) N) := by
    intro p hp
    obtain ⟨hI,hp⟩ := mem_filter.mp hp
    exact mem_Icc.mpr ⟨hp.pos,Nat.lt_succ_iff.mp (mem_Ico.mp hI).2⟩
  simpa using card_le_card h

private theorem balanced_band_mass_tendsto {a : ℝ} (ha : 0<a) (ha' : a≤1/2) :
    Tendsto (fun N => ∑ p∈chenBalancedFirstBand N (chenPowerLevel a N),1/(p:ℝ)) atTop
      (𝓝 (Real.log (1/2)-Real.log a)) := by
  let z := chenPowerLevel a
  let y := chenPowerLevel (1/2)
  let E (N : ℕ) : ℝ := (if (y N).Prime then 1/(y N:ℝ) else 0)
  have hy := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp
    (chenPowerLevel_tendsto_atTop (by norm_num : (0:ℝ)<1/2))
  have hE : Tendsto E atTop (𝓝 0) := by
    apply squeeze_zero (fun N => ?_) (fun N => ?_) (tendsto_inv_atTop_zero.comp hy)
    · dsimp only [E]; split_ifs <;> positivity
    · change E N≤(y N:ℝ)⁻¹
      dsimp only [E]; split_ifs <;> simp [one_div]
  have hh := (chenSwitchBandMass_tendsto ha ha').add hE
  rw [add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  have hzy : z N≤y N := Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le
    (Nat.one_le_cast.mpr hN) ha')
  change (∑ p∈chenMediumPrimes (z N) (y N),1/(p:ℝ))+E N=
    ∑ p∈chenMediumPrimes (z N) (y N+1),1/(p:ℝ)
  simp only [chenMediumPrimes,sum_filter,sum_Ico_succ_top hzy,E]

theorem chen_balanced_prime_majorant {η : ℝ} (hη : 0<η) (hη' : η<1/6)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, chenBalancedPrimeMajorant N (chenPowerLevel (1/2-η) N) ≤
      (2*Real.log (1/(1-2*η))+ε)*((N:ℝ)/Real.log (N:ℝ)) := by
  let a := 1/2-η
  let y := chenPowerLevel (1/2)
  let S (N : ℕ) := chenBalancedFirstBand N (chenPowerLevel a N)
  let H (N : ℕ) := ∑ p∈S N,1/(p:ℝ)
  let c := Real.log (1/(1-2*η))
  have ha : 0<a := by dsimp [a]; linarith
  have ha' : a≤1/2 := by dsimp [a]; linarith
  have hc : Real.log (1/2)-Real.log a=c := by
    rw [←Real.log_div (by norm_num : (1/2:ℝ)≠0) ha.ne']
    dsimp [c,a]
    congr 1
    field_simp
  let τ := ε/(4*(|c|+1))
  have hτ : 0<τ := by dsimp [τ]; positivity
  have hτc : 2*τ*c<ε := by
    have h := mul_le_mul_of_nonneg_left (le_abs_self c) hτ.le
    have hh : τ*(4*(|c|+1))=ε := by dsimp [τ]; field_simp
    nlinarith only [h,hh,hτ,mul_nonneg hτ.le (abs_nonneg c)]
  have hH : Tendsto H atTop (𝓝 c) := hc ▸ balanced_band_mass_tendsto ha ha'
  have hratio := (chenLogPowerLevel_tendsto (by norm_num : (0:ℝ)<1/2)).inv₀ (by norm_num)
  have hratio' : Tendsto (fun N : ℕ => Real.log (N:ℝ)/Real.log (y N:ℝ)) atTop (𝓝 2) := by
    simpa [one_div,y] using hratio
  have hlim := (hratio'.const_mul (1+τ)).mul hH
  have hgood := hlim.eventually_lt_const (show (1+τ)*2*c<2*c+ε by linarith only [hτc])
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    (primeCounting_ratio_unconditional.eventually_lt_const (lt_add_of_pos_right 1 hτ))
  have hy := (chenPowerLevel_tendsto_atTop (by norm_num : (0:ℝ)<1/2)).eventually_ge_atTop (max K 2)
  filter_upwards [hgood,hy,eventually_ge_atTop (2:ℕ)] with N hgood hy hN
  have hn : 0<Real.log (N:ℝ) := Real.log_pos (Nat.one_lt_cast.mpr hN)
  have hy₂ : 2≤y N := (le_max_right ..).trans hy
  have hyl : 0<Real.log (y N:ℝ) := Real.log_pos (Nat.one_lt_cast.mpr hy₂)
  have hpt (p : ℕ) (hp : p∈S N) :
      ((N/p).primeCounting:ℝ) ≤ ((1+τ)*((N:ℝ)/Real.log (y N:ℝ)))*(1/(p:ℝ)) := by
    obtain ⟨hI,hpr⟩ := mem_filter.mp hp
    have hpy := Nat.lt_succ_iff.mp (mem_Ico.mp hI).2
    have hq := chenBalanced_root_le_quot hpr.pos hpy
    have hq₂ := hy₂.trans hq
    have hqL : 0<Real.log ((N/p:ℕ):ℝ) := Real.log_pos (Nat.one_lt_cast.mpr hq₂)
    have hq₀ : (0:ℝ)<(N/p:ℕ) := Nat.cast_pos.mpr (by omega)
    have h : ((N/p).primeCounting:ℝ)≤(1+τ)*(((N/p:ℕ):ℝ)/Real.log ((N/p:ℕ):ℝ)) :=
      ((div_lt_iff₀ (div_pos hq₀ hqL)).mp (hK _ (((le_max_left ..).trans hy).trans hq))).le
    calc _ ≤ _ := h
         _ ≤ (1+τ)*(((N:ℝ)/p)/Real.log (y N:ℝ)) := mul_le_mul_of_nonneg_left
           (div_le_div₀ (by positivity) Nat.cast_div_le hyl
             (Real.log_le_log (Nat.cast_pos.mpr (by omega)) (Nat.cast_le.mpr hq))) (by positivity)
         _ = _ := by ring
  calc _ ≤ ∑ p∈S N, ((1+τ)*((N:ℝ)/Real.log (y N:ℝ)))*(1/(p:ℝ)) := sum_le_sum hpt
       _ = ((1+τ)*(Real.log (N:ℝ)/Real.log (y N:ℝ))*H N)*((N:ℝ)/Real.log (N:ℝ)) := by
         rw [←mul_sum]; dsimp only [H]; field_simp
       _ ≤ _ := mul_le_mul_of_nonneg_right hgood.le (div_nonneg (Nat.cast_nonneg _) hn.le)

end FareyGoldbach
