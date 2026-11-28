import FareyGoldbach.ChenActualSieveParameters
import FareyGoldbach.SharpRankin

/-! # Scalar estimates for the switching distribution -/

open Filter Set
open scoped Topology Classical

namespace FareyGoldbach

noncomputable def chenSwitchLog (N : ℕ) : ℝ := 1+Real.log (2*(N:ℝ))

theorem one_le_chenSwitchLog {N : ℕ} (hN : 1≤N) : 1≤chenSwitchLog N := by
  have hn : (1:ℝ)≤N := Nat.one_le_cast.mpr hN
  unfold chenSwitchLog
  linarith only [Real.log_nonneg (by linarith only [hn] : 1≤2*(N:ℝ))]

theorem log_le_chenSwitchLog {N : ℕ} (hN : 1≤N) : Real.log (N:ℝ)≤chenSwitchLog N := by
  have hn : (1:ℝ)≤N := Nat.one_le_cast.mpr hN
  unfold chenSwitchLog
  have h := Real.log_le_log (by linarith only [hn] : 0<(N:ℝ)) (by linarith only [hn] : (N:ℝ)≤2*(N:ℝ))
  linarith only [h]

theorem chenSwitchLog_le_three_log {N : ℕ} (hN : 3≤N) :
    chenSwitchLog N≤3*Real.log (N:ℝ) := by
  have hn : (3:ℝ)≤N := Nat.cast_le.mpr hN
  have hp : (0:ℝ)<N := by linarith only [hn]
  have h₁ : 1≤Real.log (N:ℝ) := (Real.le_log_iff_exp_le hp).mpr
    (Real.exp_one_lt_three.le.trans hn)
  have h₂ : Real.log 2≤Real.log (N:ℝ) := Real.log_le_log (by norm_num) (by linarith only [hn])
  rw [chenSwitchLog,Real.log_mul (by norm_num) hp.ne']
  linarith only [h₁,h₂]

theorem chenSwitchLog_tendsto_atTop : Tendsto chenSwitchLog atTop atTop := by
  have h := Real.tendsto_log_atTop.comp
    ((tendsto_natCast_atTop_atTop (R:=ℝ)).const_mul_atTop (by norm_num : (0:ℝ)<2))
  exact tendsto_atTop_add_const_left atTop 1 h

theorem chenSwitchLog_pow_div_power_tendsto (j : ℕ) {a : ℝ} (ha : 0<a) :
    Tendsto (fun N : ℕ => (chenSwitchLog N)^j/(N:ℝ)^a) atTop (𝓝 0) := by
  have hnat := ((isLittleO_log_rpow_rpow_atTop (j:ℝ) ha).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul ((3:ℝ)^j)
  have ht : Tendsto (fun N : ℕ => ((3:ℝ)^j)*((Real.log (N:ℝ))^j/(N:ℝ)^a)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,Real.rpow_natCast,mul_zero] using hnat
  refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ ht
  · have hL : 0≤chenSwitchLog N := by
      by_cases h : N=0
      · simp [h,chenSwitchLog]
      · exact zero_le_one.trans (one_le_chenSwitchLog (Nat.one_le_iff_ne_zero.mpr h))
    exact div_nonneg (pow_nonneg hL _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  filter_upwards [eventually_ge_atTop (3:ℕ)] with N hN
  have hl := one_le_chenSwitchLog (show 1≤N by omega)
  have hh := pow_le_pow_left₀ (zero_le_one.trans hl) (chenSwitchLog_le_three_log hN) j
  rw [mul_pow] at hh
  calc _ ≤ ((3:ℝ)^j*(Real.log (N:ℝ))^j)/(N:ℝ)^a :=
    div_le_div_of_nonneg_right hh (by positivity)
    _ = _ := by ring

/-- A smaller positive exponent stays below an integer power cutoff even with
an extra unit of room. -/
theorem eventually_rpow_add_one_le_powerLevel {a b : ℝ} (ha : 0≤a) (hab : a<b) :
    ∀ᶠ N : ℕ in atTop, (N:ℝ)^a+1≤(chenPowerLevel b N:ℝ) := by
  have hh := ((tendsto_rpow_atTop (sub_pos.mpr hab)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 3
  filter_upwards [hh,eventually_ge_atTop (1:ℕ)] with N hR hN
  have hn : (1:ℝ)≤N := Nat.one_le_cast.mpr hN
  have hp : (0:ℝ)<N := zero_lt_one.trans_le hn
  have hR' : 3≤(N:ℝ)^(b-a) := hR
  have ha₁ : 1≤(N:ℝ)^a := Real.one_le_rpow hn ha
  have hb₁ : 3*(N:ℝ)^a≤(N:ℝ)^b := by
    calc _ ≤ (N:ℝ)^(b-a)*(N:ℝ)^a := mul_le_mul_of_nonneg_right hR' (by positivity)
      _ = _ := by rw [←Real.rpow_add hp]; congr 1; ring
  have hfl : (N:ℝ)^b<(chenPowerLevel b N:ℝ)+1 := Nat.lt_floor_add_one _
  linarith only [ha₁,hb₁,hfl]

theorem chenSwitching_cutoffs_eventually :
    ∀ᶠ N : ℕ in atTop,
      (N:ℝ)^((1:ℝ)/4)+1≤(chenUpperCutoff N:ℝ) ∧
      (N:ℝ)^((1:ℝ)/16)+1≤(chenLowerCutoff N:ℝ) :=
  (eventually_rpow_add_one_le_powerLevel (a:=1/4) (b:=1/3) (by norm_num) (by norm_num)).and
    (eventually_rpow_add_one_le_powerLevel (a:=1/16) (b:=1/8) (by norm_num) (by norm_num))

theorem chen_sum_inv_totient_le {N : ℕ} (hN : 1≤N) :
    ∑ d ∈ Finset.Icc 1 N, 1/(d.totient:ℝ)≤2*(chenSwitchLog N)^2 := by
  have hL := one_le_chenSwitchLog hN
  have hNr : (1:ℝ)≤N := Nat.one_le_cast.mpr hN
  have hle (d : ℕ) (hd : d∈Finset.Icc 1 N) : 1/(d.totient:ℝ)≤2*chenSwitchLog N*(1/(d:ℝ)) := by
    obtain ⟨hd₁,hdN⟩ := Finset.mem_Icc.mp hd
    have hp : (0:ℝ)<d := Nat.cast_pos.mpr hd₁
    have hl := Real.log_le_log (show 0<2*(d:ℝ) by positivity)
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hdN) (by norm_num : (0:ℝ)≤2))
    have hr := div_totient_le_two_log hd₁
    calc _ = ((d:ℝ)/(d.totient:ℝ))*(1/(d:ℝ)) := by field_simp [hp.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right (hr.trans
        (by unfold chenSwitchLog; linarith only [hl])) (by positivity)
  calc _ ≤ ∑ d ∈ Finset.Icc 1 N, 2*chenSwitchLog N*(1/(d:ℝ)) := Finset.sum_le_sum hle
    _ = (2*chenSwitchLog N)*∑ d∈Finset.Icc 1 N,1/(d:ℝ) := by rw [Finset.mul_sum]
    _ ≤ (2*chenSwitchLog N)*chenSwitchLog N := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h := harmonic_le_one_add_log hN
      have hl := Real.log_le_log (show (0:ℝ)<N by linarith only [hNr])
        (show (N:ℝ)≤2*(N:ℝ) by linarith only [hNr])
      exact h.trans (by unfold chenSwitchLog; linarith only [hl])
    _ = _ := by ring

/-- Every integer at least two belongs to exactly one shell `(Q,2Q]`. -/
def chenShellIndex (n : ℕ) : ℕ := (n-1).log2

theorem chenShell_mem {n : ℕ} (hn : 2≤n) :
    n∈Finset.Ioc (2^chenShellIndex n) (2*2^chenShellIndex n) := by
  have hn₁ : n-1≠0 := by omega
  have hlo := Nat.log2_self_le hn₁
  have hup := (Nat.log2_lt hn₁).mp (Nat.lt_succ_self (n-1).log2)
  rw [pow_succ, Nat.mul_comm] at hup
  exact Finset.mem_Ioc.mpr ⟨by dsimp [chenShellIndex]; omega,by dsimp [chenShellIndex]; omega⟩

theorem chenShellIndex_eq_of_mem {n i : ℕ}
    (hn : n∈Finset.Ioc (2^i) (2*2^i)) : chenShellIndex n=i := by
  obtain ⟨hl,hu⟩ := Finset.mem_Ioc.mp hn
  have hp : 0<(2:ℕ)^i := by positivity
  have h₀ : n-1≠0 := by omega
  apply Nat.le_antisymm
  · refine Nat.le_of_lt_succ ((Nat.log2_lt h₀).mpr ?_)
    rw [pow_succ,Nat.mul_comm]
    omega
  · exact (Nat.le_log2 h₀).mpr (by omega)

theorem chenShellIndex_mem_range {n N : ℕ} (hn : 2≤n) (hN : n≤N) :
    chenShellIndex n∈Finset.range (N.log2+1) := by
  have hp := (Finset.mem_Ioc.mp (chenShell_mem hn)).1
  have h0 : N≠0 := by omega
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_log2 h0).mpr (by omega)))

theorem chen_log2_range_card_le {N : ℕ} (hN : 1≤N) :
    ((Finset.range (N.log2+1)).card:ℝ)≤3*chenSwitchLog N := by
  have h₀ : N≠0 := by omega
  have hpow : (2:ℝ)^N.log2≤(N:ℝ) := by exact_mod_cast Nat.log2_self_le h₀
  have h := Real.log_le_log (show 0<(2:ℝ)^N.log2 by positivity) hpow
  rw [Real.log_pow] at h
  have hc : (1:ℝ)/2≤Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hNlog := log_le_chenSwitchLog hN
  have hL := one_le_chenSwitchLog hN
  rw [Finset.card_range,Nat.cast_add,Nat.cast_one]
  nlinarith only [h,hc,hNlog,hL,
    mul_nonneg (Nat.cast_nonneg (α:=ℝ) N.log2) (sub_nonneg.mpr hc)]

end FareyGoldbach
