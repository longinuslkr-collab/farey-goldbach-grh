import FareyGoldbach.ChenElementaryError
import FareyGoldbach.ChenNumericalCertificate
import FareyGoldbach.TernaryPowerRange

/-! # The main coefficients and absorption of the elementary error in Chen's sieve -/

open Filter Set MeasureTheory
open scoped Topology

namespace FareyGoldbach

noncomputable def chenLowerMainCoeff (θ : ℝ) : ℝ := (2/θ)*Real.log (8*θ-1)
noncomputable def chenMediumMainCoeff (θ : ℝ) : ℝ := (2/θ)*Real.log ((8*θ-1)/(3*θ-1))
noncomputable def chenSwitchedMainCoeff (θ : ℝ) : ℝ := (2/θ)*chenSwitchIntegral
noncomputable def chenMainMargin (θ : ℝ) : ℝ :=
  chenLowerMainCoeff θ-(1/2)*chenMediumMainCoeff θ-(1/2)*chenSwitchedMainCoeff θ

/-- The weight carried by the middle prime between the two fixed Chen cutoffs. -/
theorem chen_medium_integral_eq {θ : ℝ} (hθ : 1/3<θ) :
    (∫ u in (1/8:ℝ)..1/3, 2/(u*(θ-u))) = chenMediumMainCoeff θ := by
  let F (t : ℝ) := (2/θ)*(Real.log t - Real.log (θ-t))
  have hθ₀ : 0<θ := by linarith
  have hD (t : ℝ) (ht : t∈uIcc (1/8:ℝ) (1/3)) : HasDerivAt F (2/(t*(θ-t))) t := by
    rw [uIcc_of_le (by norm_num : (1/8:ℝ)≤1/3)] at ht
    have ht₀ : 0<t := by linarith [ht.1]
    have hs : 0<θ-t := by linarith [ht.2]
    have hid : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id _
    have hd : HasDerivAt (fun x : ℝ => θ-x) (-1) t := hid.const_sub θ
    convert ((Real.hasDerivAt_log ht₀.ne').sub (hd.log hs.ne')).const_mul (2/θ) using 1
    field_simp
    ring
  have hI : IntervalIntegrable (fun u : ℝ => 2/(u*(θ-u))) volume (1/8:ℝ) (1/3) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    intro t ht
    have ht₀ : 0<t := by linarith [ht.1]
    have hs : 0<θ-t := by linarith [ht.2]
    fun_prop (disch := positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hD hI]
  have ht₃ : 0<θ-1/3 := by linarith
  have ht₈ : 0<θ-1/8 := by linarith
  have hratio : (8*θ-1)/(3*θ-1) = ((1/3)/(θ-1/3))/((1/8)/(θ-1/8)) := by
    field_simp [show 3*θ-1≠0 by linarith]
  dsimp [F,chenMediumMainCoeff]
  rw [hratio,Real.log_div (x:=(1/3)/(θ-1/3)) (y:=(1/8)/(θ-1/8)) (by positivity) (by positivity),
    Real.log_div (x:=1/3) (y:=θ-1/3) (by norm_num) ht₃.ne',
    Real.log_div (x:=1/8) (y:=θ-1/8) (by norm_num) ht₈.ne']
  ring

theorem chen_main_margin_at_half :
    chenMainMargin (1/2) = 4*Real.log 3-2*Real.log 6-2*chenSwitchIntegral := by
  norm_num [chenMainMargin,chenLowerMainCoeff,chenMediumMainCoeff,chenSwitchedMainCoeff]
  ring

/-- A fixed distribution exponent strictly below one half suffices. The interval also
keeps the linear upper-sieve parameter of every medium prime above one. -/
theorem chen_margin_near_half :
    ∃ θ₀ : ℝ, θ₀∈Ioo (11/24) (1/2) ∧ ∀ θ∈Icc θ₀ (1/2), (1:ℝ)/20<chenMainMargin θ := by
  have hcont : ContinuousAt chenMainMargin (1/2) := by
    unfold chenMainMargin chenLowerMainCoeff chenMediumMainCoeff chenSwitchedMainCoeff
    fun_prop (disch := norm_num)
  have hp : 1/20<chenMainMargin (1/2) := by rw [chen_main_margin_at_half]; exact chen_numerical_margin
  obtain ⟨δ,hδ,hw⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually (lt_mem_nhds hp))
  let s : ℝ := min δ (1/24)/2
  have hs : 0<s := div_pos (lt_min hδ (by norm_num)) (by norm_num)
  have hsδ : s<δ := by dsimp [s]; linarith [min_le_left δ (1/24)]
  have hsI : s<1/24 := by dsimp [s]; linarith [min_le_right δ (1/24)]
  refine ⟨1/2-s,⟨by linarith,by linarith⟩,fun θ hθ => hw ?_⟩
  rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hθ.2)]
  linarith [hθ.1]

noncomputable def chenSieveScale (U : ℕ→ℝ) (N : ℕ) : ℝ := U N*(N:ℝ)/Real.log (N:ℝ)^2

noncomputable def chenFloorLowerTerm (N : ℕ) : ℝ := (chenSifted N (chenLowerCutoff N) (chenA N)).card

noncomputable def chenFloorMediumTerm (N : ℕ) : ℝ :=
  ∑ q ∈ chenMediumPrimes (chenLowerCutoff N) (chenUpperCutoff N),
    ((chenSifted N (chenLowerCutoff N) (chenDivisible (chenA N) q)).card:ℝ)

noncomputable def chenFloorSwitchedTerm (N : ℕ) : ℝ :=
  (chenSifted N (chenUpperCutoff N) (chenUnrestrictedB N (chenLowerCutoff N) (chenUpperCutoff N))).card

/-- Uniform in all singular factors bounded below by one half. -/
theorem chen_power_error_eventually_le (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ U : ℕ→ℝ, (1:ℝ)/2≤U N →
      2*(N:ℝ)^(7/8:ℝ)+(N:ℝ)^(1/3:ℝ) ≤ ε*chenSieveScale U N := by
  have hl := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1/8)).tendsto_div_nhds_zero
  have hl' : Tendsto (fun x : ℝ => Real.log x^2/x^(1/8:ℝ)) atTop (𝓝 0) := by
    apply hl.congr
    intro x
    rw [←Real.rpow_natCast]
    norm_num
  have hnat := hl'.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hnat.eventually_lt_const (show (0:ℝ)<ε/6 by positivity),eventually_ge_atTop (2:ℕ)]
    with N h hN U hU
  have hn : (2:ℝ)≤N := by exact_mod_cast hN
  have hp : (0:ℝ)<N := by linarith
  have hL : 0<Real.log (N:ℝ)^2 := sq_pos_of_pos (Real.log_pos (by linarith))
  have hR : 0<(N:ℝ)^(1/8:ℝ) := Real.rpow_pos_of_pos hp _
  have hR' : 0≤(N:ℝ)^(7/8:ℝ) := Real.rpow_nonneg hp.le _
  change Real.log (N:ℝ)^2/(N:ℝ)^(1/8:ℝ)<ε/6 at h
  have he : (N:ℝ)^(1/8:ℝ)*(N:ℝ)^(7/8:ℝ)=(N:ℝ) := by
    rw [←Real.rpow_add hp]; norm_num
  have hsmall := mul_le_mul_of_nonneg_right (((div_lt_iff₀ hR).mp h).le) hR'
  have hsmaller := Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ)≤N) (by norm_num : (1/3:ℝ)≤7/8)
  have hh := mul_le_mul_of_nonneg_right hsmaller hL.le
  have hU' := mul_le_mul_of_nonneg_right hU (mul_nonneg hε.le hp.le)
  unfold chenSieveScale
  rw [←mul_div_assoc,le_div_iff₀ hL]
  calc _ ≤ 3*((Real.log (N:ℝ)^2)*(N:ℝ)^(7/8:ℝ)) := by linarith only [hh]
       _ ≤ (ε/2)*((N:ℝ)^(1/8:ℝ)*(N:ℝ)^(7/8:ℝ)) := by linarith only [hsmall]
       _ ≤ _ := by rw [he]; linarith only [hU']

/-- Transfer estimates for the actual three floored sieve sums into a lower bound
for the number of rough, squarefree Chen representations. -/
theorem chen_rough_count_lower_of_sieve_terms (U : ℕ→ℝ) {θ : ℝ} (hmargin : 1/20<chenMainMargin θ)
    (hU : ∀ᶠ N : ℕ in atTop, Even N → (1:ℝ)/2≤U N)
    (hterms : ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop, Even N →
      (chenLowerMainCoeff θ-ε)*chenSieveScale U N ≤ chenFloorLowerTerm N ∧
      chenFloorMediumTerm N ≤ (chenMediumMainCoeff θ+ε)*chenSieveScale U N ∧
      chenFloorSwitchedTerm N ≤ (chenSwitchedMainCoeff θ+ε)*chenSieveScale U N) :
    ∀ᶠ N : ℕ in atTop, Even N → (1:ℝ)/100*(N:ℝ)/Real.log (N:ℝ)^2 ≤
      ((chenRoughRepresentations N (chenLowerCutoff N)).card:ℝ) := by
  filter_upwards [hU,hterms (1/200) (by norm_num),chen_power_error_eventually_le (1/200) (by norm_num),
    eventually_ge_atTop (2^24:ℕ)] with N hU hterms hpower hN hEven
  have hs := chen_switching_inequality_floor_rough_explicit hN
  change chenFloorLowerTerm N-(1/2)*chenFloorMediumTerm N-(1/2)*chenFloorSwitchedTerm N-
    (2*(N:ℝ)^(7/8:ℝ)+(N:ℝ)^(1/3:ℝ)) ≤ ((chenRoughRepresentations N (chenLowerCutoff N)).card:ℝ) at hs
  obtain ⟨hA,hM,hB⟩ := hterms hEven
  have hu := hU hEven
  have hp := hpower U hu
  have hU₀ : 0≤U N := by linarith
  have hT : 0≤chenSieveScale U N := by unfold chenSieveScale; positivity
  have hmargin' := mul_le_mul_of_nonneg_right hmargin.le hT
  unfold chenMainMargin at hmargin'
  have hcount : (1/50)*chenSieveScale U N ≤ ((chenRoughRepresentations N (chenLowerCutoff N)).card:ℝ) := by
    linarith only [hs,hA,hM,hB,hp,hmargin',hT]
  refine le_trans ?_ hcount
  unfold chenSieveScale
  rw [←mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  nlinarith only [mul_le_mul_of_nonneg_right hu (Nat.cast_nonneg (α:=ℝ) N)]

/-- Transfer estimates for the actual three floored sieve sums into a lower bound
for the number of prime complements with at most two prime factors. -/
theorem chen_count_lower_of_sieve_terms (U : ℕ→ℝ) {θ : ℝ} (hmargin : 1/20<chenMainMargin θ)
    (hU : ∀ᶠ N : ℕ in atTop, Even N → (1:ℝ)/2≤U N)
    (hterms : ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop, Even N →
      (chenLowerMainCoeff θ-ε)*chenSieveScale U N ≤ chenFloorLowerTerm N ∧
      chenFloorMediumTerm N ≤ (chenMediumMainCoeff θ+ε)*chenSieveScale U N ∧
      chenFloorSwitchedTerm N ≤ (chenSwitchedMainCoeff θ+ε)*chenSieveScale U N) :
    ∀ᶠ N : ℕ in atTop, Even N → (1:ℝ)/100*(N:ℝ)/Real.log (N:ℝ)^2 ≤ (chenCount N:ℝ) := by
  filter_upwards [chen_rough_count_lower_of_sieve_terms U hmargin hU hterms] with N hN hEven
  exact (hN hEven).trans (Nat.cast_le.mpr (chenRoughRepresentations_card_le_chenCount N (chenLowerCutoff N)))

end FareyGoldbach
