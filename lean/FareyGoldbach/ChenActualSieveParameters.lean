import FareyGoldbach.ChenSieveLevel

/-! # Logarithmic sieve parameters at exact integer levels -/

open Filter Set
open scoped Topology Classical

namespace FareyGoldbach

noncomputable def chenSieveParameter (D w : ℕ) : ℝ :=
  Real.log (D:ℝ)/Real.log (w:ℝ)

private theorem chen_log_floor_power {a : ℝ} {N : ℕ} (hN : 0<N)
    (hpow : 2≤(N:ℝ)^a) :
    a*Real.log (N:ℝ)-Real.log 2≤Real.log (chenPowerLevel a N : ℝ) ∧
    Real.log (chenPowerLevel a N : ℝ)≤a*Real.log (N:ℝ) := by
  let t := (N:ℝ)^a
  let d := chenPowerLevel a N
  have ht : 0<t := by linarith only [hpow]
  have hlo : t/2≤(d:ℝ) := by
    have h := Nat.lt_floor_add_one t
    change t<(d:ℝ)+1 at h
    linarith only [h,hpow]
  have hhi : (d:ℝ)≤t := Nat.floor_le ht.le
  have hd : 0<(d:ℝ) := (by positivity : 0<t/2).trans_le hlo
  have hlog := Real.log_rpow (Nat.cast_pos.mpr hN : (0:ℝ)<N) a
  have h0 := Real.log_le_log (by positivity : 0<t/2) hlo
  rw [Real.log_div (by positivity : t≠0) (by norm_num),show Real.log t=a*Real.log (N:ℝ) from hlog] at h0
  exact ⟨h0,(Real.log_le_log hd hhi).trans_eq hlog⟩

private theorem chen_log_ratio_error_eventually (c : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, c/Real.log (N:ℝ) < ε := by
  have hL := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hh := (tendsto_const_nhds (x:=c)).div_atTop hL
  exact hh.eventually_lt_const hε

/-- Integer part changes the power-scale logarithm by a bounded additive error. -/
theorem chenLogPowerLevel_tendsto {a : ℝ} (ha : 0<a) :
    Tendsto (fun N : ℕ => Real.log (chenPowerLevel a N : ℝ)/Real.log (N:ℝ)) atTop (𝓝 a) := by
  have hp := (tendsto_rpow_atTop ha).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  filter_upwards [hp.eventually_ge_atTop (2:ℝ),eventually_ge_atTop (2:ℕ),
    chen_log_ratio_error_eventually (Real.log 2) hε] with N hpow hN he
  have hN' : (2:ℝ)≤N := by exact_mod_cast hN
  have hL : 0<Real.log (N:ℝ) := Real.log_pos (by linarith)
  obtain ⟨hlo,hhi⟩ := chen_log_floor_power (by omega : 0<N) hpow
  have hh := (div_lt_iff₀ hL).mp he
  rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr ((div_le_iff₀ hL).2 hhi))]
  have hs := (lt_div_iff₀ hL).mpr (show (a-ε)*Real.log (N:ℝ)<Real.log (chenPowerLevel a N:ℝ) by
    linarith only [hh,hlo])
  linarith only [hs]

private theorem chen_log_nat_div {D q : ℕ} (hq : 0<q) (hdiv : 2≤D/q) :
    Real.log (D:ℝ)-Real.log (q:ℝ)-Real.log 2≤Real.log (D/q:ℕ) ∧
      Real.log (D/q:ℕ)≤Real.log (D:ℝ)-Real.log (q:ℝ) := by
  have hqR : (0:ℝ)<q := Nat.cast_pos.mpr hq
  have hdivR : (2:ℝ)≤(D/q:ℕ) := by exact_mod_cast hdiv
  have hpos : (0:ℝ)<(D/q:ℕ) := zero_lt_two.trans_le hdivR
  have hD₂ : (0:ℝ)<D := Nat.cast_pos.mpr (by
    have h := Nat.div_le_self D q
    omega)
  have h₁ : (D:ℝ)/(q:ℝ)/2≤(D/q:ℕ) := by
    have hh : (D:ℝ)<(q:ℝ)*((D/q:ℕ)+1) := by
      exact_mod_cast (Nat.lt_mul_div_succ D hq)
    have hb : (D:ℝ)/(q:ℝ)<((D/q:ℕ):ℝ)+1 := (div_lt_iff₀ hqR).2 (by linarith only [hh])
    linarith only [hb,hdivR]
  have h₂ : ((D/q:ℕ):ℝ)≤(D:ℝ)/(q:ℝ) := Nat.cast_div_le
  have hlo := Real.log_le_log (by positivity : 0<(D:ℝ)/(q:ℝ)/2) h₁
  have hhi := Real.log_le_log hpos h₂
  rw [Real.log_div (by positivity : (D:ℝ)/(q:ℝ)≠0) (by norm_num),
    Real.log_div hD₂.ne' hqR.ne'] at hlo
  rw [Real.log_div hD₂.ne' hqR.ne'] at hhi
  exact ⟨hlo,hhi⟩

theorem chen_mediumNat_div_ge_lower {θ : ℝ} (hθ : 11/24<θ) {N q : ℕ}
    (hN : 2^24≤N) (hq : q∈chenMediumPrimes (chenLowerCutoff N) (chenUpperCutoff N)) :
    chenLowerCutoff N≤chenPowerLevel θ N/q := by
  obtain ⟨hqI,hqP⟩ := Finset.mem_filter.mp hq
  have hy := (Finset.mem_Ico.mp hqI).2.le
  apply (Nat.le_div_iff_mul_le hqP.pos).2
  exact (Nat.mul_le_mul_left _ hy).trans (chenPowerLevel_cutoffs hθ hN).2.2

/-- Uniform additive error after normalizing the logarithm of the conditioned level. -/
theorem chenMediumLogRatio_eventually {θ : ℝ} (hθ : 11/24<θ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ q∈chenMediumPrimes (chenLowerCutoff N) (chenUpperCutoff N),
      |Real.log ((chenPowerLevel θ N/q:ℕ):ℝ)/Real.log (N:ℝ) -
        (θ-Real.log (q:ℝ)/Real.log (N:ℝ))| ≤ ε := by
  have hθp : 0<θ := by linarith
  have hp := (tendsto_rpow_atTop hθp).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hp.eventually_ge_atTop (2:ℝ),eventually_ge_atTop (2^24:ℕ),
      chen_log_ratio_error_eventually (Real.log 2+Real.log 2) hε] with N hp hN he q hq
  have hN' : (2:ℝ)≤N := by exact_mod_cast (show (2:ℕ)≤N by omega)
  have hL : 0<Real.log (N:ℝ) := Real.log_pos (by linarith)
  have hqpos := (Finset.mem_filter.mp hq).2.pos
  have hz₂ := (chenPowerLevel_cutoffs hθ hN).1
  have hdiv := hz₂.trans (chen_mediumNat_div_ge_lower hθ hN hq)
  obtain ⟨hD₁,hD₂⟩ := chen_log_floor_power (by omega : 0<N) hp
  obtain ⟨h₁,h₂⟩ := chen_log_nat_div hqpos hdiv
  have hhi : Real.log ((chenPowerLevel θ N/q:ℕ):ℝ)/Real.log (N:ℝ) ≤
      θ-Real.log (q:ℝ)/Real.log (N:ℝ) := by
    calc _ ≤ (θ*Real.log (N:ℝ)-Real.log (q:ℝ))/Real.log (N:ℝ) :=
         div_le_div_of_nonneg_right (by linarith only [hD₂,h₂]) hL.le
       _ = _ := by rw [sub_div,mul_div_cancel_right₀ θ hL.ne']
  have hlow : (θ-ε)-Real.log (q:ℝ)/Real.log (N:ℝ) ≤
      Real.log ((chenPowerLevel θ N/q:ℕ):ℝ)/Real.log (N:ℝ) := by
    have hh := (div_lt_iff₀ hL).mp he
    have hEq : ((θ-ε)*Real.log (N:ℝ)-Real.log (q:ℝ))/Real.log (N:ℝ) =
        θ-ε-Real.log (q:ℝ)/Real.log (N:ℝ) := by
      rw [sub_div,mul_div_cancel_right₀ (θ-ε) hL.ne']
    rw [←hEq]
    exact div_le_div_of_nonneg_right (by linarith only [hD₁,h₁,hh]) hL.le
  rw [abs_of_nonpos (sub_nonpos.mpr hhi)]
  linarith only [hlow]

/-- The two unconditioned parameters converge to the values used in the
closed linear-sieve profiles. -/
theorem chenSieveParameter_tendsto {θ a : ℝ} (hθ : 0<θ) (ha : 0<a) :
    Tendsto (fun N : ℕ => chenSieveParameter (chenPowerLevel θ N) (chenPowerLevel a N))
      atTop (𝓝 (θ/a)) := by
  have h := (chenLogPowerLevel_tendsto hθ).div (chenLogPowerLevel_tendsto ha) ha.ne'
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ)] with N hN
  have hN' : (2:ℝ)≤N := by exact_mod_cast hN
  have hL : 0<Real.log (N:ℝ) := Real.log_pos (by linarith)
  unfold chenSieveParameter
  exact div_div_div_cancel_right₀ hL.ne' _ _

/-- A natural cutoff is recovered exactly from the logarithmic sieve argument. -/
theorem chenSieveParameter_cutoff {D w : ℕ} (hD : 2≤D) (hw : 2≤w) :
    ⌈(D:ℝ)^(1/chenSieveParameter D w)⌉₊ = w := by
  have hDr : (1:ℝ)<D := by exact_mod_cast (show 1<D by omega)
  have hwr : (0:ℝ)<w := by exact_mod_cast (show 0<w by omega)
  have hlog := Real.log_pos hDr
  rw [chenSieveParameter,one_div_div,Real.rpow_def_of_pos (by linarith : (0:ℝ)<D),
    show Real.log (D:ℝ)*(Real.log (w:ℝ)/Real.log (D:ℝ)) = Real.log (w:ℝ) by field_simp,
    Real.exp_log hwr,Nat.ceil_natCast]

/-- All uses of F and f in Chen's argument are inside their first intervals,
with the actual floored cutoff and the natural quotient D/q. -/
theorem chenActualSieveParameters_eventually_mem {θ : ℝ} (hθ : 11/24<θ) (hθ₂ : θ<1/2) :
    ∀ᶠ N : ℕ in atTop,
      chenSieveParameter (chenPowerLevel θ N) (chenLowerCutoff N)∈Icc 2 4 ∧
      chenSieveParameter (chenPowerLevel θ N) (chenUpperCutoff N)∈Icc 1 3 ∧
      ∀ q∈chenMediumPrimes (chenLowerCutoff N) (chenUpperCutoff N),
        chenSieveParameter (chenPowerLevel θ N/q) (chenLowerCutoff N)∈Icc 1 3 := by
  have hθ₀ : 0<θ := by linarith
  have h₁ := chenSieveParameter_tendsto hθ₀ (by norm_num : (0:ℝ)<1/8)
  have h₂ := chenSieveParameter_tendsto hθ₀ (by norm_num : (0:ℝ)<1/3)
  have hL := h₁.eventually (Ioo_mem_nhds (show (2:ℝ)<θ/(1/8) by linarith)
    (show θ/(1/8)<4 by linarith))
  have hU := h₂.eventually (Ioo_mem_nhds (show (1:ℝ)<θ/(1/3) by linarith)
    (show θ/(1/3)<3 by linarith))
  filter_upwards [hL,hU,eventually_ge_atTop (2^24:ℕ)] with N hL hU hN
  have hz₂ := (chenPowerLevel_cutoffs hθ hN).1
  let z := chenLowerCutoff N
  let D := chenPowerLevel θ N
  change chenSieveParameter D z∈Ioo 2 4 at hL
  change chenSieveParameter D (chenUpperCutoff N)∈Ioo 1 3 at hU
  refine ⟨Ioo_subset_Icc_self hL,Ioo_subset_Icc_self hU,?_⟩
  intro q hq
  have hqI := (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).1
  have hqP := (Finset.mem_filter.mp hq).2
  have hzq := chen_mediumNat_div_ge_lower hθ hN hq
  have h2z : (2:ℝ)≤z := by exact_mod_cast hz₂
  have hlogz : 0<Real.log (z:ℝ) := Real.log_pos (by linarith)
  have hlogq : Real.log (z:ℝ)≤Real.log (q:ℝ) :=
    Real.log_le_log (by linarith) (Nat.cast_le.mpr hqI)
  have hge : Real.log (z:ℝ)≤Real.log ((D/q:ℕ):ℝ) :=
    Real.log_le_log (by linarith) (Nat.cast_le.mpr hzq)
  have hle := (chen_log_nat_div hqP.pos (hz₂.trans hzq)).2
  have htop := (div_lt_iff₀ hlogz).mp hL.2
  exact ⟨(one_le_div hlogz).2 hge,(div_le_iff₀ hlogz).2 (by linarith only [hlogq,hle,htop])⟩

/-- The upper branches of the Chen argument stay a positive distance from the
endpoint 1, including the quotients by all medium primes. -/
theorem chenUpperParameters_eventually_gt_one {θ : ℝ} (hθ : 11/24<θ) :
    ∀ᶠ N : ℕ in atTop,
      1<chenSieveParameter (chenPowerLevel θ N) (chenUpperCutoff N) ∧
      ∀ q∈chenMediumPrimes (chenLowerCutoff N) (chenUpperCutoff N),
        1<chenSieveParameter (chenPowerLevel θ N/q) (chenLowerCutoff N) := by
  let ε := (θ-11/24)/3
  have hε : 0<ε := by dsimp [ε]; linarith
  have hU := (chenSieveParameter_tendsto (show 0<θ by linarith)
    (by norm_num : (0:ℝ)<1/3)).eventually (Ioi_mem_nhds (show (1:ℝ)<θ/(1/3) by linarith))
  have hZ := (chenLogPowerLevel_tendsto (by norm_num : (0:ℝ)<1/8)).eventually
    (Iio_mem_nhds (show (1:ℝ)/8<(1:ℝ)/8+ε by linarith))
  filter_upwards [hU,hZ,chenMediumLogRatio_eventually hθ hε,eventually_ge_atTop (2^24:ℕ)]
    with N hU hZ hM hN
  refine ⟨hU,?_⟩
  intro q hq
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hL := Real.log_pos hNr
  have hZr : (1:ℝ)<chenLowerCutoff N := by
    exact_mod_cast (show 1<chenLowerCutoff N from (chenPowerLevel_cutoffs hθ hN).1)
  have hLp := Real.log_pos hZr
  have hqbound := (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).2
  have htop : Real.log (q:ℝ)/Real.log (N:ℝ)≤1/3 := by
    have hqpos : (0:ℝ)<q := Nat.cast_pos.mpr (Finset.mem_filter.mp hq).2.pos
    have hqr : (q:ℝ)≤(N:ℝ)^((1:ℝ)/3) :=
      (Nat.cast_le.mpr hqbound.le).trans (Nat.floor_le (Real.rpow_nonneg (by linarith) _))
    apply (div_le_iff₀ hL).2
    simpa [Real.log_rpow (by linarith : (0:ℝ)<N)] using Real.log_le_log hqpos hqr
  have hLo := (abs_le.mp (hM q hq)).1
  have hZ' : Real.log (chenLowerCutoff N:ℝ)/Real.log (N:ℝ)<1/8+ε := hZ
  have hcmp : Real.log (chenLowerCutoff N:ℝ)/Real.log (N:ℝ) <
      Real.log ((chenPowerLevel θ N/q:ℕ):ℝ)/Real.log (N:ℝ) := by
    dsimp [ε] at hLo hZ'
    linarith only [hLo,hZ',htop,hθ]
  exact (one_lt_div hLp).2 ((div_lt_div_iff_of_pos_right hL).1 hcmp)

/-- A positive power cutoff grows to infinity despite the integer part. -/
theorem chenPowerLevel_tendsto_atTop {a : ℝ} (ha : 0<a) :
    Tendsto (chenPowerLevel a) atTop atTop :=
  tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop ha).comp (tendsto_natCast_atTop_atTop (R:=ℝ)))

theorem chenPowerLevel_le_self {a : ℝ} (ha : a≤1) {N : ℕ} (hN : 0<N) :
    chenPowerLevel a N≤N := by
  have hn : (1:ℝ)≤N := Nat.one_le_cast.mpr hN
  have hpos : (0:ℝ)<N := Nat.cast_pos.mpr hN
  exact_mod_cast (show (chenPowerLevel a N:ℝ)≤(N:ℝ) from
    (Nat.floor_le (Real.rpow_nonneg hpos.le _)).trans (Real.rpow_le_self_of_one_le hn ha))

/-- The ratio needed for the uniform singular-series tail. -/
theorem chenLogTwo_div_powerLevel_tendsto {a : ℝ} (ha : 0<a) :
    Tendsto (fun N : ℕ => Real.log (2*(N:ℝ))/(chenPowerLevel a N : ℝ)) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_atTop ha).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hconst := (tendsto_const_nhds (x:=Real.log 2)).div_atTop ht
  have hlog := (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hnum : Tendsto (fun N : ℕ => Real.log (2*(N:ℝ))/(N:ℝ)^a) atTop (𝓝 0) := by
    have h := hconst.add hlog
    rw [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    have hp : (0:ℝ)<N := Nat.cast_pos.mpr hN
    change Real.log 2/(N:ℝ)^a+Real.log (N:ℝ)/(N:ℝ)^a = _
    rw [←add_div,Real.log_mul (by norm_num) hp.ne']
  have hden := (tendsto_nat_floor_div_atTop (R:=ℝ)).comp ht
  have h := hnum.div hden (by norm_num : (1:ℝ)≠0)
  rw [zero_div] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  have hp : (0:ℝ)<N := Nat.cast_pos.mpr hN
  change (Real.log (2*(N:ℝ))/(N:ℝ)^a)/((chenPowerLevel a N:ℝ)/(N:ℝ)^a)=_
  exact div_div_div_cancel_right₀ (Real.rpow_pos_of_pos hp _).ne' _ _

/-- Medium primes have logarithmic coordinates between zero and one third. -/
theorem chenMediumLogPrimeRatio_bounds {N q : ℕ} (hN : 2≤N)
    (hq : q∈chenMediumPrimes (chenLowerCutoff N) (chenUpperCutoff N)) :
    0≤Real.log (q:ℝ)/Real.log (N:ℝ) ∧ Real.log (q:ℝ)/Real.log (N:ℝ)≤1/3 := by
  obtain ⟨hI,hP⟩ := Finset.mem_filter.mp hq
  have hN' : (2:ℝ)≤N := by exact_mod_cast hN
  have hL : 0<Real.log (N:ℝ) := Real.log_pos (by linarith)
  have hq₀ : (0:ℝ)<q := Nat.cast_pos.mpr hP.pos
  have hq₁ : (1:ℝ)≤q := Nat.one_le_cast.mpr hP.pos
  have hqY : (q:ℝ)≤(N:ℝ)^(1/3:ℝ) :=
    (Nat.cast_le.mpr (Finset.mem_Ico.mp hI).2.le).trans (Nat.floor_le (by positivity))
  have h := Real.log_le_log hq₀ hqY
  rw [Real.log_rpow (by positivity : 0<(N:ℝ))] at h
  exact ⟨div_nonneg (Real.log_nonneg hq₁) hL.le,(div_le_iff₀ hL).2 h⟩

/-- Uniform replacement of the reciprocal of the conditioned logarithm by
the continuous kernel in the prime coordinate. -/
theorem chenMediumReciprocalFloor_eventually_le {θ : ℝ} (hθ : 11/24<θ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ q∈chenMediumPrimes (chenLowerCutoff N) (chenUpperCutoff N),
      2/(Real.log ((chenPowerLevel θ N/q:ℕ):ℝ)/Real.log (N:ℝ)) ≤
        2/(θ-Real.log (q:ℝ)/Real.log (N:ℝ))+ε := by
  let b := θ-1/3
  let δ := min (b/2) (ε*b^2/4)
  have hb : 0<b := by dsimp [b]; linarith
  have hd : 0<δ := by dsimp [δ]; positivity
  have hd₁ : δ≤b/2 := min_le_left ..
  have hd₂ : δ≤ε*b^2/4 := min_le_right ..
  filter_upwards [chenMediumLogRatio_eventually hθ hd,eventually_ge_atTop (2:ℕ)] with N h hN q hq
  let a := Real.log ((chenPowerLevel θ N/q:ℕ):ℝ)/Real.log (N:ℝ)
  let c := θ-Real.log (q:ℝ)/Real.log (N:ℝ)
  have hc : b≤c := by dsimp [b,c]; linarith only [(chenMediumLogPrimeRatio_bounds hN hq).2]
  have hca : c-a≤δ := by have hh := (abs_le.mp (h q hq)).1; change -δ≤a-c at hh; linarith only [hh]
  have ha : b/2≤a := by linarith only [hc,hca,hd₁]
  have ha₀ : 0<a := (by positivity : 0<b/2).trans_le ha
  have hc₀ : 0<c := hb.trans_le hc
  have hz : 0<a*c := mul_pos ha₀ hc₀
  have hh : b^2/2≤a*c := by
    have hm := mul_le_mul ha hc hb.le ha₀.le
    nlinarith only [hm]
  have h := mul_le_mul_of_nonneg_left hh hε.le
  have hp : 2*(c-a)≤ε*(a*c) := by linarith only [hca,hd₂,h]
  change (2:ℝ)/a ≤ 2/c+ε
  have ht : (2:ℝ)/a-2/c≤ε := by
    rw [show (2:ℝ)/a-2/c=2*(c-a)/(a*c) by field_simp]
    exact (div_le_iff₀ hz).2 hp
  linarith only [ht]

end FareyGoldbach
