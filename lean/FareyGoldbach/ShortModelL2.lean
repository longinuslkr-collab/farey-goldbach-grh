import FareyGoldbach.ContinuousShortModel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Regularity and mean square of the continuous Farey model -/

open Real Complex Set MeasureTheory
open scoped BigOperators Classical

namespace FareyGoldbach

lemma shortContModel_periodic (r b Y Q : ℕ) : Function.Periodic (shortContModel r b Y Q) 1 := by
  intro α
  unfold shortContModel
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hα : α ∈ voronoiCell Q c
  · rw [Set.indicator_of_mem ((voronoiCell_periodic Q c α).2 hα),Set.indicator_of_mem hα]
    rw [show α+1-c.val=(α-c.val)+1 by ring,wrap_add_one]
  · rw [Set.indicator_of_notMem (fun h => hα ((voronoiCell_periodic Q c α).1 h)),Set.indicator_of_notMem hα]

lemma shortContModel_measurable {Y : ℕ} (hY : 1 ≤ Y) (r b Q : ℕ) : Measurable (shortContModel r b Y Q) := by
  unfold shortContModel
  refine Finset.measurable_sum _ fun c _ => Measurable.indicator ?_ (voronoiCell_measurable Q c)
  exact measurable_const.mul ((continuous_shortContKernel hY r b).measurable.comp
    (measurable_wrap.comp (measurable_id.sub measurable_const)))

lemma shortContModel_norm_bounded {Y : ℕ} (hY : 1≤Y) (r b Q : ℕ) :
    ∃ B : ℝ, ∀ α : ℝ, ‖shortContModel r b Y Q α‖ ≤ B := by
  refine ⟨∑ c ∈ (centers Q).filter (fun c => c.q ≤ Q), ‖modelCoeff r b c‖ * ((Y:ℝ)/r), fun α => ?_⟩
  unfold shortContModel
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  by_cases hα : α ∈ voronoiCell Q c
  · rw [Set.indicator_of_mem hα,norm_mul]
    exact mul_le_mul_of_nonneg_left (shortContKernel_bound_triv hY r b _) (norm_nonneg _)
  · rw [Set.indicator_of_notMem hα,norm_zero]; positivity

private noncomputable def shortEnvelope (H t : ℝ) : ℝ := 5*H^2*(1+(H*t)^2)⁻¹

private lemma shortEnvelope_nonneg (H t : ℝ) : 0 ≤ shortEnvelope H t := by unfold shortEnvelope; positivity

private lemma shortEnvelope_le (H t : ℝ) : shortEnvelope H t ≤ 5*H^2 := by
  unfold shortEnvelope; rw [←div_eq_mul_inv,div_le_iff₀ (by positivity)]; nlinarith [mul_nonneg (sq_nonneg H) (sq_nonneg (H*t))]

private lemma shortEnvelope_continuous (H : ℝ) : Continuous (shortEnvelope H) := by
  unfold shortEnvelope
  exact continuous_const.mul (((continuous_const.add ((continuous_const.mul continuous_id).pow 2)).inv₀ (by intro x; change (1:ℝ)+(H*x)^2 ≠ 0; positivity)))

private lemma shortKernel_sq_le {r b Y : ℕ} (hY : 1≤Y) (t : ℝ) :
    ‖shortContKernel r b Y t‖^2 ≤ shortEnvelope ((Y:ℝ)/r) t := by
  let H := (Y:ℝ)/r
  let v := ‖shortContKernel r b Y t‖
  have hv : 0≤v := norm_nonneg _
  have hvH : v ≤ H := shortContKernel_bound_triv hY r b t
  have htv : v*|t| ≤ 2 := by
    by_cases hz : t=0
    · rw [hz,abs_zero,mul_zero]; norm_num
    · exact (le_div_iff₀ (abs_pos.mpr hz)).1 (shortContKernel_bound_decay (r:=r) hY b hz)
  have hs := pow_le_pow_left₀ (mul_nonneg hv (abs_nonneg t)) htv 2
  rw [mul_pow,sq_abs] at hs
  change v^2 ≤ 5*H^2*(1+(H*t)^2)⁻¹
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  nlinarith only [pow_le_pow_left₀ hv hvH 2,mul_le_mul_of_nonneg_left hs (sq_nonneg H)]

private lemma shortEnvelope_integral (H : ℝ) (hH : 0<H) :
    (∫ β in (-(1/2):ℝ)..1/2, shortEnvelope H β) ≤ 20*H := by
  unfold shortEnvelope
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left
    (fun u : ℝ => (1+u^2)⁻¹) hH.ne',integral_inv_one_add_sq]
  change 5*H^2 * (H⁻¹ * (Real.arctan (H*(1/2))-Real.arctan (H*(-(1/2))))) ≤ _
  have hdiff : Real.arctan (H*(1/2))-Real.arctan (H*(-(1/2))) ≤ 4 := by
    linarith [Real.arctan_lt_pi_div_two (H*(1/2)),Real.neg_pi_div_two_lt_arctan (H*(-(1/2))),Real.pi_lt_four]
  have he (v : ℝ) : 5*H^2*(H⁻¹*v) = 5*H*v := by field_simp
  rw [he]; nlinarith only [mul_le_mul_of_nonneg_left hdiff hH.le]

private lemma shortEnvelope_center_integral (H : ℝ) (hH : 0<H) (c : RatCenter) :
    (∫ α in (0:ℝ)..1, shortEnvelope H (wrap (α-c.val))) ≤ 20*H := by
  have hper : Function.Periodic (fun α : ℝ => shortEnvelope H (wrap (α-c.val))) 1 := by
    intro α; simp only; rw [show α+1-c.val=(α-c.val)+1 by ring,wrap_add_one]
  rw [intervalIntegral_shift_symm hper c.val]
  apply le_trans (le_of_eq ?_) (shortEnvelope_integral H hH)
  apply intervalIntegral.integral_congr
  intro t ht
  have hbounds : t ∈ Set.Icc (-(1/2):ℝ) (1/2) := by simpa [Set.uIcc_of_le (by norm_num : (-(1/2):ℝ)≤1/2)] using ht
  have hwt := abs_wrap_eq_abs_of_abs_le_half (t := t) (abs_le.mpr hbounds)
  have hsq : (wrap t)^2=t^2 := by calc _ = |wrap t|^2 := (sq_abs _).symm
                                  _ = |t|^2 := congrArg (fun z:ℝ=>z^2) hwt
                                  _ = t^2 := sq_abs _
  simp only [add_sub_cancel_left]; unfold shortEnvelope; rw [mul_pow,mul_pow,hsq]

private lemma shortEnvelope_term_int (H : ℝ) (c : RatCenter) (r b : ℕ) :
    IntervalIntegrable (fun x : ℝ => ‖modelCoeff r b c‖^2*shortEnvelope H (wrap (x-c.val))) volume 0 1 := by
  apply intervalIntegrable_of_measurable_bounded (B:=‖modelCoeff r b c‖^2*(5*H^2))
  · exact measurable_const.mul ((shortEnvelope_continuous H).measurable.comp
      (measurable_wrap.comp (measurable_id.sub measurable_const)))
  · intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (shortEnvelope_nonneg ..))]
    exact mul_le_mul_of_nonneg_left (shortEnvelope_le ..) (sq_nonneg _)

/-- The continuous model on full Farey cells has the same `κ H log(2Y)` scale as its discrete counterpart. -/
theorem shortContModel_l2_le {r b Y Q : ℕ} (hr : 0<r) (hrY : r≤Y) (hQY : Q≤Y) (hYlarge : 2^72≤Y) :
    (∫ α in (0:ℝ)..1, ‖shortContModel r b Y Q α‖^2) ≤
      360*((r:ℝ)/r.totient)*((Y:ℝ)/r)*Real.log (2*(Y:ℝ)) := by
  classical
  let Cset := (centers Q).filter (fun c => c.q ≤ Q)
  let H := (Y:ℝ)/r
  have hY : 1≤Y := hr.trans_le hrY
  have hH : 0<H := div_pos (Nat.cast_pos.mpr hY) (Nat.cast_pos.mpr hr)
  have hpt (α : ℝ) : ‖shortContModel r b Y Q α‖^2 ≤
      ∑ c ∈ Cset, ‖modelCoeff r b c‖^2*shortEnvelope H (wrap (α-c.val)) := by
    unfold shortContModel
    rw [norm_sq_sum_disjoint_indicator Cset (voronoiCell Q) (fun a _ b _ hab => voronoiCell_disjoint hab)]
    apply Finset.sum_le_sum
    intro c _
    by_cases he : α ∈ voronoiCell Q c
    · rw [Set.indicator_of_mem he,norm_mul,mul_pow]
      exact mul_le_mul_of_nonneg_left (shortKernel_sq_le hY _) (sq_nonneg _)
    · rw [Set.indicator_of_notMem he]; exact mul_nonneg (sq_nonneg _) (shortEnvelope_nonneg ..)
  have hreal : IntervalIntegrable (fun x : ℝ => ‖shortContModel r b Y Q x‖^2) volume 0 1 := by
    obtain ⟨B,hB⟩ := shortContModel_norm_bounded hY r b Q
    refine intervalIntegrable_of_measurable_bounded (B:=B^2) ((shortContModel_measurable hY r b Q).norm.pow_const 2) ?_
    intro x; rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (norm_nonneg _) (hB x) 2
  have hint (c : RatCenter) (_ : c ∈ Cset) := shortEnvelope_term_int H c r b
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hreal
    (intervalIntegrable_finset_sum Cset hint) (fun α _ => hpt α)
  rw [intervalIntegral_finset_sum hint] at hmono
  have hterms (c : RatCenter) (_ : c ∈ Cset) :
      (∫ α in (0:ℝ)..1, ‖modelCoeff r b c‖^2*shortEnvelope H (wrap (α-c.val))) ≤ ‖modelCoeff r b c‖^2*(20*H) := by
    rw [intervalIntegral.integral_const_mul]; exact mul_le_mul_of_nonneg_left (shortEnvelope_center_integral H hH c) (sq_nonneg _)
  have hsum_coeff : ∑ c ∈ Cset, ‖modelCoeff r b c‖ ^ 2 ≤
      ((r : ℝ) / (r.totient : ℝ)) ^ 2 *
        ∑ q ∈ ((Finset.Icc 1 Q).filter (fun q => Nat.Coprime q r)).filter Squarefree,
          (1 : ℝ) / (q.totient : ℝ) := by
    let Qset := ((Finset.Icc 1 Q).filter (fun q => Nat.Coprime q r)).filter Squarefree
    -- Every `c ∈ Cset` with `modelCoeff r b c ≠ 0` has `c.q ∈ Qset`.
    let Cgood := Cset.filter (fun c => c.q ∈ Qset)
    have htrim : ∑ c ∈ Cset, ‖modelCoeff r b c‖ ^ 2 = ∑ c ∈ Cgood, ‖modelCoeff r b c‖ ^ 2 := by
      symm; rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun c hc => ?_
      split_ifs with h
      · rfl
      · have h0 : modelCoeff r b c = 0 := by
          unfold modelCoeff
          by_cases hcop : Nat.Coprime c.q r
          · rw [ite_eq_left hcop]
            have hnot_sf : ¬ Squarefree c.q := by
              intro hsf
              exact h (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
                ⟨Finset.mem_Icc.mpr ⟨c.q_pos, (Finset.mem_filter.mp hc).2⟩, hcop⟩, hsf⟩)
            rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnot_sf]; simp
          · exact ite_eq_right hcop
        simp [h0]
    rw [htrim]
    -- Fiber over `q ∈ Qset`: at most `φ(q)` centers `c ∈ Cgood` have `c.q = q`.
    have hfiber : ∑ c ∈ Cgood, ‖modelCoeff r b c‖ ^ 2 =
        ∑ q ∈ Qset, ∑ c ∈ Cgood.filter (fun c => c.q = q), ‖modelCoeff r b c‖ ^ 2 :=
      (Finset.sum_fiberwise_of_maps_to (s := Cgood) (t := Qset) (g := fun c : RatCenter => c.q)
        (fun c hc => (Finset.mem_filter.mp hc).2) (fun c => ‖modelCoeff r b c‖ ^ 2)).symm
    rw [hfiber, Finset.mul_sum]
    refine Finset.sum_le_sum fun q hq => ?_
    have hq_pos : 0 < q := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).1
    have hq_cop : Nat.Coprime q r := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
    have hq_sf : Squarefree q := (Finset.mem_filter.mp hq).2
    have hcard_a : (Cgood.filter (fun c => c.q = q)).card ≤ q.totient := by
      have hsub : (Cgood.filter (fun c => c.q = q)).image (fun c => c.a) ⊆
          (Finset.range q).filter (fun a => Nat.Coprime a q) := by
        intro a ha
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ha
        have hcq : c.q = q := (Finset.mem_filter.mp hc).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hcq ▸ c.a_lt), hcq ▸ c.coprime⟩
      have hinj : Set.InjOn (fun c : RatCenter => c.a) (Cgood.filter (fun c => c.q = q) : Set RatCenter) := by
        intro c₁ h1 c₂ h2 hEq
        have hq1 : c₁.q = q := (Finset.mem_filter.mp h1).2
        have hq2 : c₂.q = q := (Finset.mem_filter.mp h2).2
        exact RatCenter.ext hEq (hq1.trans hq2.symm)
      rw [← Finset.card_image_of_injOn hinj]
      calc ((Cgood.filter (fun c => c.q = q)).image (fun c => c.a)).card
          ≤ ((Finset.range q).filter (fun a => Nat.Coprime a q)).card := Finset.card_le_card hsub
        _ = q.totient := by
            rw [Nat.totient_eq_card_coprime]
            congr 1; ext a; simp [Nat.coprime_comm]
    have hnorm_eq : ∀ c ∈ Cgood.filter (fun c => c.q = q),
        ‖modelCoeff r b c‖ ^ 2 = ((r : ℝ) / (r.totient : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2 := by
      intro c hc
      have hcq : c.q = q := (Finset.mem_filter.mp hc).2
      unfold modelCoeff
      rw [hcq, ite_eq_left hq_cop, norm_mul, norm_mul, norm_e, one_mul, norm_div,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
          Complex.norm_intCast, Complex.norm_natCast,
          ArithmeticFunction.moebius_apply_of_squarefree hq_sf]
      simp [mul_pow, div_pow]; ring
    calc ∑ c ∈ Cgood.filter (fun c => c.q = q), ‖modelCoeff r b c‖ ^ 2
        = ((Cgood.filter (fun c => c.q = q)).card : ℝ) *
            (((r : ℝ) / (r.totient : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2) := by
          rw [Finset.sum_congr rfl hnorm_eq, Finset.sum_const, nsmul_eq_mul]
      _ ≤ (q.totient : ℝ) * (((r : ℝ) / (r.totient : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard_a) (by positivity)
      _ = ((r : ℝ) / (r.totient : ℝ)) ^ 2 * (1 / (q.totient : ℝ)) := by
          have hqt0 : (q.totient : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hq_pos).ne'
          field_simp [hqt0]

  have hsum := hsum_coeff.trans (mul_le_mul_of_nonneg_left (sum_coprime_inv_totient_le hr hrY hQY hYlarge) (by positivity))
  have hbound := (hmono.trans (Finset.sum_le_sum hterms))
  rw [←Finset.sum_mul] at hbound
  refine hbound.trans ((mul_le_mul_of_nonneg_right hsum (by positivity : 0 ≤ 20*H)).trans_eq ?_)
  have hr0 : (r:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have ht0 : (r.totient:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hr).ne'
  dsimp [H]; field_simp; ring

end FareyGoldbach

