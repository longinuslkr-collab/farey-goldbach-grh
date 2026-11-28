import FareyGoldbach.TwinChenPrimeMedium
import FareyGoldbach.ChenAPPrimeDistributionOfGRH
import FareyGoldbach.ChenTheoremUnconditional

/-! # Prime and medium-prime distribution for Chen's twin-prime sieve -/

open Filter Finset
open scoped Topology Classical

namespace FareyGoldbach

private theorem shift_three_atTop : Tendsto (fun X : ℕ => X+3) atTop atTop :=
  tendsto_atTop.mpr fun n => (eventually_ge_atTop n).mono (fun _ h => by omega)

private theorem shift_log_atTop : ∀ᶠ X : ℕ in atTop, 1≤Real.log ((X+3:ℕ):ℝ) :=
  shift_three_atTop.eventually ((Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1)

theorem twinChenPrimeDistribution_of_dirichletGRH {δ θ : ℝ} (_hδ : 0<δ) (hθ : 11/24<θ)
    (hsum : δ+θ<1/2) (hGRH : DirichletGRH) : TwinChenPrimeDistributionAt δ θ := by
  have hθ₀ : 0≤θ := by linarith only [hθ]
  intro ε hε
  have hh : 0<ε/2 := by positivity
  have hpnt := Metric.tendsto_nhds.mp primeCounting_ratio_unconditional (ε/2) hh
  filter_upwards [shift_three_atTop.eventually (chenAP_prime_class_budget hθ₀ hsum hGRH hh),
    shift_three_atTop.eventually hpnt,shift_log_atTop,eventually_ge_atTop (3^8:ℕ)]
    with X hbudget hpi hL hX r b hr hrδ hb hb₂
  let M := X+3
  let D := chenPowerLevel θ M
  obtain ⟨U,hU,hclass,hone,hall⟩ := hbudget r hr hrδ
  have hD : 1≤D := Nat.le_floor (by
    simpa only [Nat.cast_one] using Real.one_le_rpow (Nat.one_le_cast.mpr (by dsimp [M]; omega : 1≤M)) hθ₀)
  have hshifted (e u : ℕ) (he : 0<e) (heD : e≤r*D) (hu : u.Coprime e) :
      |((X.primesLE.filter fun p => p%e=u%e).card:ℝ)-(M.primeCounting:ℝ)/e.totient|≤U+3 := by
    exact (abs_sub_le _ (((X+3).primesLE.filter fun p => p%e=u%e).card:ℝ) _).trans
      ((add_le_add (twin_prime_class_shift X e u) (hclass e u he heD hu)).trans_eq (by ring))
  have hmass := hshifted r b hr (Nat.le_mul_of_pos_right r hD) hb
  rw [←twinChenAPA_card_eq_prime_class] at hmass
  have hplain : chenReducedError (2*r) D (twinChenPrimeError X r b)≤(D:ℝ)*(2*(U+3)) := by
    apply sum_filtered_Ico_abs_le _ _ (by positivity) _
    intro d hd
    obtain ⟨hi,hc⟩ := mem_filter.mp hd
    refine twinChenPrimeError_le_of_classes hr (mem_Ico.mp hi).1 hb hc (fun e u he heD hu =>
      hshifted e u he (heD.trans (Nat.mul_le_mul_left r (mem_Ico.mp hi).2.le)) hu)
  have hs : 0≤chenAPLogScale M r := by unfold chenAPLogScale; positivity
  have hred : chenReducedError (2*r) D (twinChenPrimeError X r b)≤ε*chenAPLogScale M r := by
    refine hplain.trans ((le_mul_of_one_le_right (by positivity) ?_).trans
      (hall.trans (mul_le_mul_of_nonneg_right (by linarith only [hε]) hs)))
    linarith only [hL]
  refine ⟨chenAP_prime_mass_of_count hr hL (by omega) hε hmass
    ((by linarith only [hU] : U+3≤2*(U+3)).trans hone) ?_,hred,
    (twinChenMediumError_le_reducedError (twin_lower_cutoff_ge_three (by omega)) hb₂).trans hred⟩
  simpa only [Real.dist_eq] using hpi.le

private theorem twin_one_card (X b : ℕ) :
    (twinChenAPA X 1 b).card=X.primeCounting := by
  simp [twinChenAPA_card_eq_prime_class,Nat.mod_one,Nat.primesLE_card_eq_primeCounting]

private theorem twin_count_shift (X : ℕ) :
    |(X.primeCounting:ℝ)-((X+3).primeCounting:ℝ)|≤3 := by
  simpa [Nat.mod_one,Nat.primesLE_card_eq_primeCounting] using twin_prime_class_shift X 1 0

private theorem twin_one_reduced_shift (X b D : ℕ) :
    chenReducedError 2 D (twinChenPrimeError X 1 b) ≤
      chenReducedError 2 D (fun d => (((X+3).primesLE.filter fun p => p%d=twinNegTwo d%d).card:ℝ) -
        ((X+3).primeCounting:ℝ)/(d.totient:ℝ))+(D:ℝ)*6 := by
  let R := (Ico 1 D).filter (fun d => d.Coprime 2)
  let err (d : ℕ) : ℝ := (((X+3).primesLE.filter fun p => p%d=twinNegTwo d%d).card:ℝ) -
    ((X+3).primeCounting:ℝ)/d.totient
  have hpoint (d : ℕ) (hd : d∈R) : |twinChenPrimeError X 1 b d| ≤ |err d|+6 := by
    have hd₁ := (mem_Ico.mp (mem_filter.mp hd).1).1
    have hφ : (1:ℝ)≤d.totient := Nat.one_le_cast.mpr (Nat.totient_pos.mpr hd₁)
    have he := twinChenAPA_divisible_card (X:=X) (r:=1) (b:=b) hd₁
    simp only [Nat.mod_one,true_and] at he
    unfold twinChenPrimeError chenAPError
    rw [he,twin_one_card]
    let A : ℝ := (X.primesLE.filter fun p => p%d=twinNegTwo d%d).card
    let B : ℝ := ((X+3).primesLE.filter fun p => p%d=twinNegTwo d%d).card
    let U : ℝ := ((X+3).primeCounting:ℝ)/d.totient
    let V : ℝ := (X.primeCounting:ℝ)/d.totient
    have ha : |A-B|≤3 := twin_prime_class_shift X d (twinNegTwo d)
    have hv : |U-V|≤3 := by
      dsimp only [U,V]
      rw [←sub_div,abs_div,abs_of_nonneg (show (0:ℝ)≤d.totient by positivity),abs_sub_comm]
      exact (div_le_self (abs_nonneg _) hφ).trans (twin_count_shift X)
    change |A-V|≤|B-U|+6
    linarith only [abs_sub_le A B V,abs_sub_le B U V,ha,hv]
  change (∑ d∈R, |twinChenPrimeError X 1 b d|) ≤ (∑ d∈R, |err d|)+(D:ℝ)*6
  refine (sum_le_sum hpoint).trans ?_
  rw [Finset.sum_add_distrib,sum_const,nsmul_eq_mul]
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_right _ (by norm_num)
  exact Nat.cast_le.mpr ((card_filter_le ..).trans (by simp [Nat.card_Ico]))

theorem twinChenPrimeDistributionAt_zero_unconditional {θ : ℝ} (hθ : 11/24<θ) (hh : θ<1/2) :
    TwinChenPrimeDistributionAt 0 θ := by
  intro ε hε
  have hhalf : 0<ε/2 := by positivity
  have htwelfth : 0<ε/12 := by positivity
  have hpnt := Metric.tendsto_nhds.mp primeCounting_ratio_unconditional (ε/2) hhalf
  have hb := bv_prime_classes_of_primitive_mangoldt bombieri_vinogradov_unconditional hθ hh (ε/2) hhalf
  have hsmall := chen_medium_reduced_loss_small (by linarith only [hh] : θ<1) htwelfth
  filter_upwards [shift_three_atTop.eventually hb,shift_three_atTop.eventually hsmall,
    shift_three_atTop.eventually hpnt,shift_log_atTop,eventually_ge_atTop (3^8:ℕ)]
    with X hBV hrem hpi hL hX r b hr hrpow _ hb₂
  have hr₁ : r=1 := by
    rw [Real.rpow_zero] at hrpow
    have hh' : r≤1 := by exact_mod_cast hrpow
    omega
  subst r
  let M := X+3
  let D := chenPowerLevel θ M
  have hM : 0<M := by dsimp [M]; omega
  have hD : 1≤D := Nat.le_floor (by
    simpa only [Nat.cast_one] using Real.one_le_rpow (Nat.one_le_cast.mpr hM)
      (by linarith only [hθ] : 0≤θ))
  have hbase := hBV 2 twinNegTwo (fun _ hd hc => twinNegTwo_coprime hd hc)
  have he : (D:ℝ)≤(ε/12)*chenLogScale M := (le_mul_of_one_le_right (Nat.cast_nonneg D)
    (by linarith only [hL] : 1≤1+Real.log (M:ℝ))).trans hrem
  have hscale : chenAPLogScale M 1=chenLogScale M := by simp only [chenAPLogScale,chenLogScale,Nat.totient_one,Nat.cast_one,one_mul]
  have hred : chenReducedError (2*1) D (twinChenPrimeError X 1 b)≤ε*chenAPLogScale M 1 := by
    rw [mul_one,hscale]
    exact (twin_one_reduced_shift X b D).trans (by linarith only [hbase,he])
  have hm : |((twinChenAPA X 1 b).card:ℝ)-(M.primeCounting:ℝ)/Nat.totient 1|≤3 := by
    simpa only [twin_one_card,Nat.totient_one,Nat.cast_one,div_one] using twin_count_shift X
  have hmass : 3≤(ε/2)*chenAPLogScale M 1 := by
    rw [hscale]
    linarith only [he,(Nat.one_le_cast.mpr hD : (1:ℝ)≤D)]
  refine ⟨chenAP_prime_mass_of_count (by decide) hL hM hε hm hmass ?_,hred,
    (twinChenMediumError_le_reducedError (twin_lower_cutoff_ge_three (by omega)) hb₂).trans hred⟩
  simpa only [Real.dist_eq] using hpi.le

end FareyGoldbach
