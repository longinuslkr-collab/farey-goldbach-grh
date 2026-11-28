import FareyGoldbach.ChenSieveLevel
import FareyGoldbach.ChenConditionalMargin

/-! # Mertens mass in Chen's moving power intervals -/

open Filter Finset
open scoped Topology Classical

namespace FareyGoldbach

def ChenReciprocalMertens : Prop :=
  ∃ B : ℝ, Tendsto (fun x : ℝ => (∑ p ∈ (⌊x⌋₊).primesLE, 1/(p:ℝ))-Real.log (Real.log x)) atTop (𝓝 B)

noncomputable def chenBandWeight (N p : ℕ) : ℝ := if p.Prime ∧ ¬p∣N then 1/(p.totient:ℝ) else 0

theorem chenBandWeight_nonneg (N p : ℕ) : 0≤chenBandWeight N p := by
  unfold chenBandWeight; split_ifs <;> positivity

private noncomputable def harmonicWeight (p : ℕ) : ℝ := if p.Prime then 1/(p:ℝ) else 0

private theorem harmonic_prefix (m : ℕ) :
    ∑ p ∈ range m, harmonicWeight p = (∑ p ∈ m.primesLE, 1/(p:ℝ)) - harmonicWeight m := by
  have h : m.primesLE = (range (m+1)).filter Nat.Prime := by
    ext p
    simp [Nat.mem_primesLE]
  rw [h,sum_filter]
  change _ = (∑ p ∈ range (m+1),harmonicWeight p)-_
  rw [sum_range_succ]; ring

private theorem chen_cutoff_tendsto {u : ℝ} (hu : 0<u) :
    Tendsto (chenPowerLevel u) atTop atTop :=
  tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop hu).comp (tendsto_natCast_atTop_atTop (R:=ℝ)))

private theorem hweight_cutoff_tendsto {u : ℝ} (hu : 0<u) :
    Tendsto (fun N => harmonicWeight (chenPowerLevel u N)) atTop (𝓝 0) := by
  have hn := tendsto_natCast_atTop_atTop (R:=ℝ) |>.comp (chen_cutoff_tendsto hu)
  apply squeeze_zero (fun N => by unfold harmonicWeight; split_ifs <;> positivity)
    (fun N => show harmonicWeight (chenPowerLevel u N)≤(chenPowerLevel u N:ℝ)⁻¹ by
      unfold harmonicWeight; split_ifs <;> first | rw [one_div] | positivity)
  exact tendsto_inv_atTop_zero.comp hn

private theorem harmonic_power_prefix (h : ChenReciprocalMertens) :
    ∃ B : ℝ, ∀ {u : ℝ}, 0<u → Tendsto (fun N : ℕ =>
      (∑ p ∈ range (chenPowerLevel u N), harmonicWeight p)-Real.log (Real.log (N:ℝ))) atTop (𝓝 (B+Real.log u)) := by
  obtain ⟨B,hB⟩ := h
  refine ⟨B,fun {u} hu => ?_⟩
  have h₁ := hB.comp ((tendsto_rpow_atTop hu).comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  have h₂ := (h₁.sub (hweight_cutoff_tendsto hu)).add_const (Real.log u)
  rw [sub_zero] at h₂
  apply h₂.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ)] with N hN
  have hn : (2:ℝ)≤N := by exact_mod_cast hN
  have hn₀ : (0:ℝ)<N := by linarith
  have hl : 0<Real.log (N:ℝ) := Real.log_pos (by linarith)
  rw [harmonic_prefix]
  simp only [Function.comp_apply,Real.log_rpow hn₀, Real.log_mul hu.ne' hl.ne',chenPowerLevel]
  ring

private theorem harmonic_band_tendsto (h : ChenReciprocalMertens) {u v : ℝ} (hu:0<u) (huv:u≤v) :
    Tendsto (fun N => ∑ p ∈ Ico (chenPowerLevel u N) (chenPowerLevel v N), harmonicWeight p)
      atTop (𝓝 (Real.log v-Real.log u)) := by
  obtain ⟨B,hp⟩ := harmonic_power_prefix h
  have ht := (hp (hu.trans_le huv)).sub (hp hu)
  rw [show B+Real.log v-(B+Real.log u)=Real.log v-Real.log u by ring] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  have hz : chenPowerLevel u N ≤ chenPowerLevel v N := Nat.floor_le_floor
    (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hN) huv)
  have hi := sum_range_add_sum_Ico harmonicWeight hz
  linarith only [hi]

private theorem reciprocal_band_diff {N z : ℕ} (y : ℕ) (hN : 1≤N) (hz : 2≤z) :
    let H := ∑ p ∈ Ico z y, harmonicWeight p
    let W := ∑ p ∈ Ico z y, chenBandWeight N p
    H - 2*Real.log (2*(N:ℝ))/(z:ℝ) ≤ W ∧ W ≤ H+(2/(z:ℝ))*H := by
  let s := Ico z y
  let bad := s.filter (fun p => p.Prime ∧ p∣N)
  have hsub : bad⊆N.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨(mem_filter.mp hp).2.1,(mem_filter.mp hp).2.2,by omega⟩
  have hbad : (bad.card:ℝ)≤2*Real.log (2*(N:ℝ)) :=
    (Nat.cast_le.mpr (card_le_card hsub)).trans (primeFactors_card_le_two_log hN)
  have hz' : (2:ℝ)≤z := by exact_mod_cast hz
  have hz₀ : 0<(z:ℝ) := by linarith
  have hrough {p : ℕ} (hp:p∈s) : (z:ℝ)≤p := Nat.cast_le.mpr (mem_Ico.mp hp).1
  have hlo (p) (hp:p∈s) : harmonicWeight p ≤ chenBandWeight N p + (if p.Prime ∧ p∣N then 1/(z:ℝ) else 0) := by
    have hzp := hrough hp
    by_cases hpr : p.Prime
    · by_cases hd : p∣N
      · simp only [harmonicWeight,chenBandWeight,hpr,hd,true_and,not_true_eq_false,ite_true,ite_false,zero_add]
        exact one_div_le_one_div_of_le hz₀ hzp
      · have hphi := Nat.cast_le (α:=ℝ).mpr (Nat.totient_le p)
        simpa [harmonicWeight,chenBandWeight,hpr,hd] using
          (one_div_le_one_div_of_le (Nat.cast_pos.mpr (Nat.totient_pos.mpr hpr.pos)) hphi)
    · simp [harmonicWeight,chenBandWeight,hpr]
  have hup (p) (hp:p∈s) : chenBandWeight N p ≤ (1+2/(z:ℝ))*harmonicWeight p := by
    have hzp := hrough hp
    by_cases hpr : p.Prime
    · by_cases hd : p∣N
      · simp [harmonicWeight,chenBandWeight,hpr,hd]
        positivity
      · have hp₁ : (1:ℝ)<p := by linarith
        have hf : (p.totient:ℝ)=(p:ℝ)-1 := by rw [Nat.totient_prime hpr,Nat.cast_sub hpr.one_le,Nat.cast_one]
        simp only [chenBandWeight,harmonicWeight,hpr,hd,not_false_eq_true,and_self,ite_true,hf]
        field_simp
        nlinarith only [hzp,hz']
    · simp [harmonicWeight,chenBandWeight,hpr]
  have hh := sum_le_sum hlo
  have hsum : (∑ p∈s, if p.Prime ∧ p∣N then (1:ℝ)/z else 0) = (bad.card:ℝ)/z := by
    simp [bad,Finset.sum_ite,div_eq_mul_inv]
  rw [sum_add_distrib,hsum] at hh
  have hu' := sum_le_sum hup
  rw [←Finset.mul_sum] at hu'
  exact ⟨by linarith only [hh,div_le_div_of_nonneg_right hbad hz₀.le],by linarith only [hu']⟩

/-- The exact moving floors, the omitted prime divisors of N, and the local factor
1/φ(p) all occur in this band mass. -/
theorem chen_band_mass_tendsto_of_mertens (h : ChenReciprocalMertens) {u v : ℝ} (hu:0<u) (huv:u≤v) :
    Tendsto (fun N => ∑ p ∈ Ico (chenPowerLevel u N) (chenPowerLevel v N), chenBandWeight N p)
      atTop (𝓝 (Real.log v-Real.log u)) := by
  have hH := harmonic_band_tendsto h hu huv
  have hz := chen_cutoff_tendsto hu
  have hi := tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp hz)
  have hlog := (isLittleO_log_rpow_atTop hu).tendsto_div_nhds_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hinv := tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop hu).comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  have hlog' : Tendsto (fun N:ℕ => 4*Real.log (2*(N:ℝ))/(N:ℝ)^u) atTop (𝓝 0) := by
    have hh := ((hinv.const_mul (Real.log 2)).add hlog).const_mul 4
    simp only [mul_zero,add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    have hp : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
    simp only [Function.comp_apply,Real.log_mul (by norm_num : (2:ℝ)≠0) hp.ne']
    ring
  have hU := hH.add ((hi.const_mul 2).mul hH)
  simp only [mul_zero,zero_mul,add_zero] at hU
  have hL := hH.sub hlog'
  rw [sub_zero] at hL
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU
  · filter_upwards [hz.eventually_ge_atTop 2,eventually_ge_atTop (1:ℕ)] with N hz₂ hn
    refine le_trans ?_ (reciprocal_band_diff (chenPowerLevel v N) hn hz₂).1
    apply sub_le_sub_left
    have hz' : (2:ℝ)≤chenPowerLevel u N := by exact_mod_cast hz₂
    have hN : (1:ℝ)≤N := Nat.one_le_cast.mpr hn
    have hp : 0<(N:ℝ)^u := Real.rpow_pos_of_pos (by linarith) _
    have hfl : (N:ℝ)^u<(chenPowerLevel u N:ℝ)+1 := Nat.lt_floor_add_one _
    have hlog₀ : 0≤Real.log (2*(N:ℝ)) := Real.log_nonneg (by linarith)
    apply (div_le_div_iff₀ (by linarith) hp).2
    nlinarith only [mul_le_mul_of_nonneg_right (show (N:ℝ)^u≤2*(chenPowerLevel u N:ℝ) by linarith) hlog₀]
  · filter_upwards [hz.eventually_ge_atTop 2,eventually_ge_atTop (1:ℕ)] with N hz₂ hn
    simpa only [Function.comp_apply,div_eq_mul_inv] using (reciprocal_band_diff (chenPowerLevel v N) hn hz₂).2

/-- Mertens mass for the full prime band, without omitting divisors of the ambient integer. -/
theorem chen_prime_harmonic_band_tendsto (h : ChenReciprocalMertens) {u v : ℝ}
    (hu : 0<u) (huv : u≤v) :
    Tendsto (fun N : ℕ => ∑ p∈chenMediumPrimes (chenPowerLevel u N) (chenPowerLevel v N),
      1/(p:ℝ)) atTop (𝓝 (Real.log v-Real.log u)) := by
  apply (harmonic_band_tendsto h hu huv).congr
  intro N
  simp only [chenMediumPrimes,Finset.sum_filter,harmonicWeight]

end FareyGoldbach
