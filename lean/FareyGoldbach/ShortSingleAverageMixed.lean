import FareyGoldbach.ShortResidualArcMass
import FareyGoldbach.ShortModelL2
import FareyGoldbach.SelbergFourthMoment
import FareyGoldbach.ShortFixedNumeratorRemainder
import FareyGoldbach.ShortWeightedKernel

/-! # Fixed-class continuous mixed term on the full circle -/

open Real Complex Set MeasureTheory
open scoped BigOperators Classical

namespace FareyGoldbach

private abbrev ShortNumeratorInput (C : ℝ) : Prop :=
  ∀ {r b Y q : ℕ}, 0<r → r≤Y → 2≤Y → 0<q → q≤Y → b<r → Nat.Coprime b r →
    ∀ [NeZero (r*q)] {t : ℝ}, |t| ≤ 1/2 →
    (∑ a ∈ coprimeClasses q, ‖shortLocalRemainder r b Y a q t‖^2) ≤
      C*(q:ℝ)*Y*(1+((Y:ℝ)/r)*|t|)*Real.log (2*(Y:ℝ))^2

private abbrev ShortKernelInput : Prop :=
  ∀ {r Y : ℕ}, 0<r → r≤Y → 1≤Y → ∀ b : ℕ,
    (∫ t in (-(1/2):ℝ)..1/2, (1+((Y:ℝ)/r)*|t|)*‖shortContKernel r b Y t‖^2) ≤
      4096*((Y:ℝ)/r)

private lemma wrappedIntegral_continuous_input {f : ℝ → ℝ} (hf : Continuous f) (u : ℝ) :
    IntervalIntegrable (fun x ↦ f (wrap (x-u))) volume 0 1 := by
  obtain ⟨v,_,hv⟩ := (isCompact_Icc (a:=-(1/2:ℝ)) (b:=(1/2:ℝ))).exists_isMaxOn
    ⟨0,by norm_num⟩ hf.norm.continuousOn
  exact intervalIntegrable_of_measurable_bounded (B:=‖f v‖)
    (hf.measurable.comp (measurable_wrap.comp (measurable_id.sub measurable_const)))
    (fun x ↦ hv (abs_le.mp (abs_wrap_le_half _)))

private lemma wrappedIntegral_shift (f : ℝ → ℝ) (u : ℝ) :
    (∫ x in (0:ℝ)..1, f (wrap (x-u))) = ∫ t in (-(1/2):ℝ)..1/2, f t := by
  have hp : Function.Periodic (fun x ↦ f (wrap (x-u))) 1 := by
    intro x; simp only; rw [show x+1-u=x-u+1 by ring,wrap_add_one]
  rw [intervalIntegral_shift_symm hp u]
  simp only [add_sub_cancel_left]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne (1/2:ℝ)] with t hne ht
  have hm : t ∈ Ioc (-(1/2):ℝ) (1/2) := by simpa [uIoc_of_le (by norm_num : -(1/2:ℝ)≤1/2)] using ht
  rw [wrap_eq_self_of_abs_lt_half (abs_lt.mpr ⟨hm.1,lt_of_le_of_ne hm.2 hne⟩)]

private lemma shortModel_on_cell {Q : ℕ} {c : RatCenter} {x : ℝ} (hx : x ∈ voronoiCell Q c)
    (r b Y : ℕ) :
    shortContModel r b Y Q x = modelCoeff r b c * shortContKernel r b Y (wrap (x-c.val)) := by
  have hc : c ∈ (centers Q).filter (fun c ↦ c.q≤Q) :=
    Finset.mem_filter.mpr ⟨hx.1,mem_centers_iff.mp hx.1⟩
  unfold shortContModel
  rw [Finset.sum_eq_single_of_mem c hc]
  · exact Set.indicator_of_mem hx _
  · intro c' _ hn
    exact Set.indicator_of_notMem (fun h ↦ Set.disjoint_left.mp (voronoiCell_disjoint hn) h hx) _

private noncomputable def localMixed (r b b' Y a q : ℕ) (t : ℝ) : ℝ :=
  if h : r*q ≠ 0 then
    ‖@shortLocalRemainder r b Y a q ⟨h⟩ t‖^2 * ‖shortContKernel r b' Y t‖^2 else 0

private lemma localMixed_nonneg (r b b' Y a q : ℕ) (t : ℝ) : 0 ≤ localMixed r b b' Y a q t := by
  unfold localMixed; split <;> positivity

private lemma localMixed_cont {Y : ℕ} (hY : 1≤Y) (r b b' a q : ℕ) :
    Continuous (localMixed r b b' Y a q) := by
  change Continuous (fun t ↦ localMixed r b b' Y a q t)
  by_cases h : r*q≠0
  · let _ : NeZero (r*q) := ⟨h⟩
    simp only [localMixed,dite_eq_left h]
    exact ((continuous_shortLocalRemainder r b Y a q).norm.pow 2).mul
      ((continuous_shortContKernel hY r b').norm.pow 2)
  · simp only [localMixed,dite_eq_right h]; exact continuous_const

private lemma fixed_mixed_numerator_integral {C : ℝ} (hC : 0<C) (hN : ShortNumeratorInput C)
    (hW : ShortKernelInput) {r b b' Y q : ℕ} (hr : 0<r) (hrY : r≤Y) (hY : 2≤Y)
    (hq : 0<q) (hqY : q≤Y) (hb : b<r) (hc : Nat.Coprime b r) :
    (∑ a ∈ coprimeClasses q, ∫ x in (0:ℝ)..1, localMixed r b b' Y a q (wrap (x-(a:ℝ)/q))) ≤
      (C*(q:ℝ)*Y*(Real.log (2*(Y:ℝ)))^2) * (4096*((Y:ℝ)/r)) := by
  let _ : NeZero (r*q) := ⟨(Nat.mul_pos hr hq).ne'⟩
  simp_rw [wrappedIntegral_shift]
  have hY1 : 1≤Y := by omega
  rw [← intervalIntegral_finset_sum (fun a _ ↦ (localMixed_cont hY1 r b b' a q).intervalIntegrable _ _)]
  let k := C*(q:ℝ)*Y*Real.log (2*(Y:ℝ))^2
  have hk : 0≤k := by dsimp [k]; positivity
  have h := intervalIntegral.integral_mono_on (μ:=volume)
    (f:=fun t ↦ ∑ a ∈ coprimeClasses q, localMixed r b b' Y a q t)
    (g:=fun t ↦ k*((1+((Y:ℝ)/r)*|t|)*‖shortContKernel r b' Y t‖^2))
    (by norm_num : -(1/2:ℝ)≤1/2)
    ((continuous_sum_finset _ fun a _ ↦ localMixed_cont hY1 r b b' a q).intervalIntegrable _ _)
    ((continuous_const.mul ((continuous_const.add (continuous_const.mul continuous_abs)).mul
      ((continuous_shortContKernel hY1 r b').norm.pow 2))).intervalIntegrable _ _) (fun t ht ↦ by
      have hn := hN hr hrY hY hq hqY hb hc (t:=t) (abs_le.mpr ht)
      simp only [localMixed,dite_eq_left (NeZero.ne (r*q)),← Finset.sum_mul]
      calc _ ≤ _ := mul_le_mul_of_nonneg_right hn (sq_nonneg ‖shortContKernel r b' Y t‖)
           _ = _ := by dsimp [k]; ring)
  rw [intervalIntegral.integral_const_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left (hW hr hrY hY1 b') hk)

private lemma mixed_coeff_norm {r b : ℕ} (c : RatCenter) :
    ‖modelCoeff r b c‖ =
      if Nat.Coprime c.q r ∧ Squarefree c.q then ((r:ℝ)/r.totient)/(c.q.totient:ℝ) else 0 := by
  classical
  unfold modelCoeff
  by_cases hc : Nat.Coprime c.q r
  · by_cases hs : Squarefree c.q
    · simp only [ite_eq_left hc, ite_eq_left (And.intro hc hs), norm_mul, norm_div, norm_e, one_mul,
        Complex.norm_real, Real.norm_eq_abs, Complex.norm_intCast, Complex.norm_natCast,
        
        ArithmeticFunction.moebius_apply_of_squarefree hs]
      simp [div_eq_mul_inv]
    · simp [hs, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
  · simp [hc]

private lemma mixed_integrables (r b b' Y Q : ℕ) (hY1 : 1≤Y) :
    let R := fun x => smoothedPrimeSum r b Y x - shortContModel r b Y Q x
    IntervalIntegrable (fun x => ‖R x‖^2) MeasureTheory.volume 0 1 ∧
    IntervalIntegrable (fun x => ‖R x‖^2 * ‖shortContModel r b' Y Q x‖^2) MeasureTheory.volume 0 1 := by
  intro R
  obtain ⟨A,hA⟩ := shortContModel_norm_bounded hY1 r b Q
  obtain ⟨B,hB⟩ := shortContModel_norm_bounded hY1 r b' Q
  let T := ∑ j ∈ Finset.range (Y/r+1), |quarticBump ((r*j+b :ℝ)/Y) * primeWeight (r*j+b)|
  have hS (x : ℝ) : ‖smoothedPrimeSum r b Y x‖ ≤ T := by
    unfold smoothedPrimeSum T
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hR (x : ℝ) : ‖R x‖^2 ≤ (T+A)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (add_le_add (hS x) (hA x))) 2
  have hm : Measurable (fun x => ‖R x‖^2) := (((continuous_smoothedPrimeSum r b Y).measurable.sub
    (shortContModel_measurable hY1 r b Q)).norm).pow_const 2
  constructor
  · refine intervalIntegrable_of_measurable_bounded (B := (T+A)^2) hm fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖R x‖)]
    exact hR x
  · refine intervalIntegrable_of_measurable_bounded (B := (T+A)^2*B^2) (hm.mul ((shortContModel_measurable hY1 r b' Q).norm.pow_const 2)) fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact mul_le_mul (hR x) (pow_le_pow_left₀ (norm_nonneg _) (hB x) 2) (sq_nonneg _) (sq_nonneg _)

private lemma mixed_split_error {C : ℝ} (hC : 0 < C) (hN : ShortNumeratorInput C) (hW : ShortKernelInput)
    {r b b' Y Q : ℕ} (hr : 0 < r) (hrY : r ≤ Y) (hY : 2 ≤ Y) (hQ : 0 < Q)
    (hb : b < r) (hc : Nat.Coprime b r) (_hb' : b' < r)
    (s : Finset ℕ) (hs : ∀ q ∈ s, 0 < q ∧ q ≤ Y) (E : ℝ → ℝ)
    (hEi : IntervalIntegrable E MeasureTheory.volume 0 1) (hE0 : ∀ x, 0 ≤ E x)
    (hE : ∀ c ∈ centers Q, c.q ∉ s → ∀ x ∈ voronoiCell Q c,
      ‖smoothedPrimeSum r b Y x - shortContModel r b Y Q x‖^2 * ‖shortContModel r b' Y Q x‖^2 ≤ E x) :
    let κ := (r:ℝ)/r.totient
    let R := fun x => smoothedPrimeSum r b Y x - shortContModel r b Y Q x
    (∫ x in (0:ℝ)..1, ‖R x‖^2 * ‖shortContModel r b' Y Q x‖^2) ≤
      (C*4096 * κ^2 * Y * ((Y:ℝ)/r) * (Real.log (2*(Y:ℝ)))^2) *
        (∑ q ∈ s, (q:ℝ)/(q.totient:ℝ)^2) +
        (∫ x in (0:ℝ)..1, E x) := by
  classical
  intro κ R
  let g := fun (q a : ℕ) (x : ℝ) => localMixed r b b' Y a q (wrap (x-(a:ℝ)/q))
  let V := fun (q : ℕ) (x : ℝ) => (κ/(q.totient:ℝ))^2 * ∑ a ∈ coprimeClasses q, g q a x
  have hg (q a : ℕ) : IntervalIntegrable (g q a) volume 0 1 :=
    wrappedIntegral_continuous_input (localMixed_cont (by omega : 1≤Y) r b b' a q) _
  have hv (q : ℕ) : IntervalIntegrable (V q) volume 0 1 :=
    (intervalIntegrable_finset_sum _ fun a _ ↦ hg q a).const_mul _
  have vg (q : ℕ) (x : ℝ) : 0 ≤ V q x := mul_nonneg (sq_nonneg _)
    (Finset.sum_nonneg fun a _ ↦ localMixed_nonneg ..)
  obtain ⟨_, hint⟩ := mixed_integrables r b b' Y Q (by omega)
  have hi := intervalIntegral.integral_mono_on zero_le_one hint
      ((intervalIntegrable_finset_sum s fun q _ ↦ hv q).add hEi)
      (fun x _ => by
        change ‖R x‖^2 * ‖shortContModel r b' Y Q x‖^2 ≤ (∑ q ∈ s, V q x) + E x
        obtain ⟨c,hcq,hx⟩ := voronoiCell_cover Q hQ x
        by_cases h : c.q ∈ s
        · let _ : NeZero (r*c.q) := ⟨(Nat.mul_pos hr c.q_pos).ne'⟩
          have hrx : R x = shortLocalRemainder r b Y c.a c.q (wrap (x-c.val)) :=
            shortResidual_eq_on_cell hr hY hx hb hc
          have hm : ‖shortContModel r b' Y Q x‖^2 ≤ (κ/(c.q.totient:ℝ))^2 * ‖shortContKernel r b' Y (wrap (x-c.val))‖^2 := by
            rw [shortModel_on_cell hx, norm_mul, mul_pow,
              mixed_coeff_norm]
            split_ifs
            · exact le_rfl
            · simp only [zero_pow (by decide : 2 ≠ 0), zero_mul]; positivity
          have hterm : ‖R x‖^2 * ‖shortContModel r b' Y Q x‖^2 ≤ V c.q x := by
            calc _ ≤ ‖R x‖^2 * ((κ/(c.q.totient:ℝ))^2 * ‖shortContKernel r b' Y (wrap (x-c.val))‖^2) :=
                   mul_le_mul_of_nonneg_left hm (sq_nonneg _)
                 _ = (κ/(c.q.totient:ℝ))^2 * g c.q c.a x := by rw [hrx]; simp only [g,localMixed,dite_eq_left (NeZero.ne (r*c.q)),RatCenter.val]; ring
                 _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.single_le_sum
                     (f := fun a => g c.q a x) (fun a _ => localMixed_nonneg ..)
                     (mem_coprimeClasses.mpr ⟨c.a_lt,c.coprime⟩)) (sq_nonneg _)
          exact (hterm.trans (Finset.single_le_sum (fun q _ => vg q x) h)).trans
            (le_add_of_nonneg_right (hE0 x))
        · exact (hE c hcq h x hx).trans (le_add_of_nonneg_left (Finset.sum_nonneg fun q _ => vg q x)))
  rw [intervalIntegral.integral_add (intervalIntegrable_finset_sum s fun q _ ↦ hv q)
         hEi,
      intervalIntegral_finset_sum (fun q _ => hv q)] at hi
  refine hi.trans (add_le_add ?_ le_rfl)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q hq => ?_
  dsimp only [V]
  rw [intervalIntegral.integral_const_mul, intervalIntegral_finset_sum
        (fun a _ => hg q a)]
  have bound := fixed_mixed_numerator_integral (b':=b') hC hN hW hr hrY hY (hs q hq).1 (hs q hq).2 hb hc
  exact (mul_le_mul_of_nonneg_left bound (sq_nonneg (κ / (q.totient:ℝ)))).trans_eq (by ring)

private lemma kernel_fourth_mean (hW : ShortKernelInput) {r b Y : ℕ} (hr : 0<r)
    (hrY : r≤Y) (u : ℝ) :
    (∫ x in (0:ℝ)..1, ‖shortContKernel r b Y (wrap (x-u))‖^4) ≤ 4096*((Y:ℝ)/r)^3 := by
  let H := (Y:ℝ)/r
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hY : 1≤Y := by omega
  let f := fun t ↦ ‖shortContKernel r b Y t‖
  have hc : Continuous f := (continuous_shortContKernel hY r b).norm
  rw [wrappedIntegral_shift (fun t ↦ ‖shortContKernel r b Y t‖^4) u]
  calc
    _ ≤ ∫ t in (-(1/2):ℝ)..1/2, H^2*((1+H*|t|)*f t^2) := by
      apply intervalIntegral.integral_mono_on (by norm_num) ((hc.pow 4).intervalIntegrable _ _)
        ((continuous_const.mul ((continuous_const.add (continuous_const.mul continuous_abs)).mul
          (hc.pow 2))).intervalIntegrable _ _)
      intro t _
      have h1 := pow_le_pow_left₀ (norm_nonneg _) (shortContKernel_bound_triv hY r b t) 2
      change f t^2 ≤ H^2 at h1
      have hh := mul_le_mul_of_nonneg_right h1 (sq_nonneg (f t))
      change f t^4 ≤ H^2*((1+H*|t|)*f t^2)
      nlinarith only [hh,mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg H) hH) (abs_nonneg t)) (sq_nonneg (f t))]
    _ = H^2*(∫ t in (-(1/2):ℝ)..1/2, (1+H*|t|)*f t^2) := intervalIntegral.integral_const_mul .. 
    _ ≤ H^2*(4096*H) := mul_le_mul_of_nonneg_left (hW hr hrY hY b) (sq_nonneg _)
    _ = _ := by ring
private noncomputable def fourthEnvelope (r b Y : ℕ) (s : Finset ℕ) (x : ℝ) : ℝ :=
  ∑ q ∈ s, (((r:ℝ)/r.totient)/(q.totient:ℝ))^4 *
    ∑ a ∈ coprimeClasses q, ‖shortContKernel r b Y (wrap (x-(a:ℝ)/q))‖^4

private lemma fourthEnvelope_int (r b Y : ℕ) (hY : 1≤Y) (s : Finset ℕ) :
    IntervalIntegrable (fourthEnvelope r b Y s) volume 0 1 := by
  unfold fourthEnvelope
  apply intervalIntegrable_finset_sum
  intro q _
  exact (intervalIntegrable_finset_sum (coprimeClasses q) fun a _ ↦
    wrappedIntegral_continuous_input (((continuous_shortContKernel hY r b).norm).pow 4) ((a:ℝ)/q)).const_mul _

private lemma fourthEnvelope_nonneg (r b Y : ℕ) (s : Finset ℕ) (x : ℝ) : 0 ≤ fourthEnvelope r b Y s x := by
  unfold fourthEnvelope
  positivity

private lemma fourthEnvelope_on_cell {r b Y Q : ℕ} {c : RatCenter} {x : ℝ}
    (hx : x ∈ voronoiCell Q c) {s : Finset ℕ} (hc : c.q ∈ s) :
    ‖shortContModel r b Y Q x‖^4 ≤ fourthEnvelope r b Y s x := by
  classical
  rw [shortModel_on_cell hx,
    norm_mul,mul_pow,mixed_coeff_norm]
  split_ifs
  · refine le_trans ?_ (Finset.single_le_sum
      (f := fun q => (((r:ℝ)/r.totient)/(q.totient:ℝ))^4 *
        ∑ a ∈ coprimeClasses q, ‖shortContKernel r b Y (wrap (x-(a:ℝ)/q))‖^4)
      (fun q _ => by positivity) hc)
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum
      (f := fun a : ℕ => ‖shortContKernel r b Y (wrap (x-(a:ℝ)/c.q))‖^4)
      (fun a _ => by positivity) (mem_coprimeClasses.mpr ⟨c.a_lt,c.coprime⟩)) (by positivity)
  · simp only [zero_pow (by decide : 4 ≠ 0),zero_mul]
    exact fourthEnvelope_nonneg _ _ _ _ _

private lemma fourthEnvelope_integral (hW : ShortKernelInput) {r b Y : ℕ} (hr : 0 < r) (hrY : r ≤ Y) (s : Finset ℕ)
    (hs : ∀ q ∈ s, 0 < q) :
    (∫ x in (0:ℝ)..1, fourthEnvelope r b Y s x) ≤
      (4096*((r:ℝ)/r.totient)^4*((Y:ℝ)/r)^3)*∑ q ∈ s, (1:ℝ)/(q.totient:ℝ)^3 := by
  classical
  let f := fun (q a : ℕ) (x : ℝ) => ‖shortContKernel r b Y (wrap (x-(a:ℝ)/q))‖^4
  have hf (q a : ℕ) : IntervalIntegrable (f q a) volume 0 1 :=
    wrappedIntegral_continuous_input (((continuous_shortContKernel (by omega : 1≤Y) r b).norm).pow 4) _
  let J := fun (q : ℕ) (x : ℝ) => (((r:ℝ)/r.totient)/(q.totient:ℝ))^4 * ∑ a ∈ coprimeClasses q, f q a x
  have cj (q : ℕ) : IntervalIntegrable (J q) volume 0 1 :=
    (intervalIntegrable_finset_sum _ fun a _ ↦ hf q a).const_mul _
  change (∫ x in (0:ℝ)..1, ∑ q ∈ s, J q x) ≤ _
  rw [intervalIntegral_finset_sum (fun q _ => cj q), Finset.mul_sum]
  refine Finset.sum_le_sum fun q hq => ?_
  dsimp only [J]
  rw [intervalIntegral.integral_const_mul, intervalIntegral_finset_sum (fun a _ => hf q a)]
  have hh : (∑ a ∈ coprimeClasses q, ∫ x in (0:ℝ)..1, f q a x) ≤
      (q.totient:ℝ)*(4096*((Y:ℝ)/r)^3) := by
    calc _ ≤ ∑ _a ∈ coprimeClasses q, (4096*((Y:ℝ)/r)^3) := Finset.sum_le_sum
           (fun a _ => kernel_fourth_mean hW (b:=b) hr hrY ((a:ℝ)/q))
         _ = _ := by rw [Finset.sum_const,card_coprimeClasses,nsmul_eq_mul]
  refine (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq ?_
  have hφ : (q.totient:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (hs q hq)).ne'
  field_simp [hφ]

private lemma all_inv_totient_cube (Q : ℕ) :
    ∑ q ∈ Finset.Icc 1 Q, (1:ℝ)/(q.totient:ℝ)^3 ≤ 5*(Real.exp 2 + 4*Real.exp 8) := by
  classical
  let small := (Finset.Icc 1 Q).filter (fun q => q.totient ≤ 1)
  have hs : (∑ q ∈ small, (1:ℝ)/(q.totient:ℝ)^3) ≤ (small.card:ℝ) := by
    calc _ ≤ ∑ _q ∈ small, (1:ℝ) := Finset.sum_le_sum (fun q hq => by
           have hp := Nat.totient_pos.mpr (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
           have he := (Finset.mem_filter.mp hq).2
           have : q.totient = 1 := by omega
           simp [this])
         _ = _ := by simp
  have h1 := hs.trans (card_totient_le_le Q 1 (by decide))
  have h2 := sum_inv_totient_cube_of_totient_gt Q 1 (by decide)
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 Q) (fun q => q.totient ≤ 1)]
  simp only [not_le, one_div]
  norm_num at h1 h2
  dsimp only [small] at h1
  linarith

private lemma norm_sub_fourth (s m : ℂ) : ‖s-m‖^4 ≤ 8*(‖s‖^4+‖m‖^4) := by
  have h : (‖s‖+‖m‖)^2 ≤ 2*(‖s‖^2+‖m‖^2) := by nlinarith [sq_nonneg (‖s‖-‖m‖)]
  calc _ ≤ (‖s‖+‖m‖)^4 := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 4
       _ = ((‖s‖+‖m‖)^2)^2 := by ring
       _ ≤ (2*(‖s‖^2+‖m‖^2))^2 := pow_le_pow_left₀ (sq_nonneg _) h 2
       _ ≤ _ := by nlinarith [sq_nonneg (‖s‖^2-‖m‖^2)]

private lemma mixed_young (a b d : ℝ) (hd : 0 < d) :
    a^2*b^2 ≤ a^4/d + d*b^4 := by
  field_simp
  nlinarith [sq_nonneg (a^2-d*b^2), mul_nonneg hd.le (mul_nonneg (sq_nonneg a) (sq_nonneg b))]

private theorem short_fixed_mixed_fourth_of_inputs {C : ℝ} (hC : 0<C)
    (hN : ShortNumeratorInput C) (hW : ShortKernelInput) :
    ∃ A : ℝ, 0<A ∧ ∀ {r b₁ b₂ Y Q : ℕ}, 0<r → b₁<r → Nat.Coprime b₁ r → b₂<r →
      r≤Y → 2≤Y → 0<Q → Q≤Y → (r:ℝ)≤4*((Y:ℝ)/r) → ∀ D : ℕ, 1≤D →
      let κ := (r:ℝ)/r.totient
      let H := (Y:ℝ)/r
      let L := Real.log (2*(Y:ℝ))
      let R := fun x ↦ smoothedPrimeSum r b₁ Y x - shortContModel r b₁ Y Q x
      let I := ∫ x in (0:ℝ)..1, ‖R x‖^2*‖shortContModel r b₂ Y Q x‖^2
      I ≤ A*(κ^2*Y*H*L^2*Real.log (2*(D:ℝ))+κ^4*H^3/(D:ℝ)) := by
  obtain ⟨K,hK,hfour⟩ := smoothedPrimeSum_fourth_le_selberg
  let F := C*4096
  let J := 8*Real.exp 4 + 8*Real.exp 16
  let G := Real.exp 2 + 4*Real.exp 8
  let B := 8*(K+20480*G)+16384*G
  let A := 1+F*J+B
  have hF : 0 < F := by dsimp [F]; positivity
  have hJ : 0 < J := by dsimp [J]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hfA : F*J ≤ A := by dsimp [A]; linarith
  have hbA : B ≤ A := by dsimp [A]; nlinarith [mul_pos hF hJ]
  refine ⟨A,hA,?_⟩
  intro r b₁ b₂ Y Q hr hb₁ hcop hb₂ hrY hY hQ hQY hr4 D hD κ H L R I
  have hS := hfour hr hb₁ hcop hrY hr4
  change (∫ x in (0:ℝ)..1, ‖smoothedPrimeSum r b₁ Y x‖^4) ≤ K*κ^4*H^3 at hS
  have hrR : (0:ℝ) < r := Nat.cast_pos.mpr hr
  have hφ : (0:ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hκ : 0 < κ := div_pos hrR hφ
  have hH : 0 < H := div_pos (by exact_mod_cast lt_of_lt_of_le hr hrY) hrR
  have hL : 1 ≤ L := one_le_log_two_mul (by omega)
  have hD' : (0:ℝ) < D := Nat.cast_pos.mpr hD
  have hlog : 0 ≤ Real.log (2*(D:ℝ)) := Real.log_nonneg (by
    have : (1:ℝ) ≤ D := by exact_mod_cast hD
    linarith)
  let full := Finset.Icc 1 Q
  let low := full.filter (fun q => q.totient ≤ D)
  let high := full.filter (fun q => D < q.totient)
  let U := fourthEnvelope r b₁ Y full
  let V := fourthEnvelope r b₂ Y high
  let S := fun x => ‖smoothedPrimeSum r b₁ Y x‖^4
  let E := fun x => (8/(D:ℝ))*(S x+U x)+(D:ℝ)*V x
  have cu : IntervalIntegrable U volume 0 1 := fourthEnvelope_int _ _ _ (by omega) _
  have cv : IntervalIntegrable V volume 0 1 := fourthEnvelope_int _ _ _ (by omega) _
  have cs : Continuous S := (continuous_smoothedPrimeSum r b₁ Y).norm.pow 4
  have ce : IntervalIntegrable E volume 0 1 := (((cs.intervalIntegrable _ _).add cu).const_mul _).add (cv.const_mul _)
  have hnn (x : ℝ) : 0 ≤ E x := by
    have hu : 0 ≤ U x := fourthEnvelope_nonneg _ _ _ _ _
    have hv : 0 ≤ V x := fourthEnvelope_nonneg _ _ _ _ _
    dsimp only [E,S]; positivity
  have hpt : ∀ c ∈ centers Q, c.q ∉ low → ∀ x ∈ voronoiCell Q c,
      ‖R x‖^2 * ‖shortContModel r b₂ Y Q x‖^2 ≤ E x := by
    intro c hc hn x hx
    have hfull : c.q ∈ full := Finset.mem_Icc.mpr ⟨c.q_pos,mem_centers_iff.mp hc⟩
    have hhigh : c.q ∈ high := Finset.mem_filter.mpr ⟨hfull,lt_of_not_ge
      (fun h => hn (Finset.mem_filter.mpr ⟨hfull,h⟩))⟩
    have hR : ‖R x‖^4 ≤ 8*(S x+U x) := (norm_sub_fourth _ _).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (fourthEnvelope_on_cell (b:=b₁) hx hfull)) (by norm_num))
    calc _ ≤ ‖R x‖^4 / (D:ℝ) + (D:ℝ)*‖shortContModel r b₂ Y Q x‖^4 :=
            mixed_young _ _ _ hD'
         _ ≤ (8*(S x+U x))/(D:ℝ) + (D:ℝ)*V x := add_le_add
            (div_le_div_of_nonneg_right hR hD'.le)
            (mul_le_mul_of_nonneg_left (fourthEnvelope_on_cell (b:=b₂) hx hhigh) hD'.le)
         _ = _ := by dsimp [E]; ring
  have hu : (∫ x in (0:ℝ)..1, U x) ≤ 20480*G*κ^4*H^3 := by
    have e := fourthEnvelope_integral hW (b:=b₁) hr hrY full (fun q hq => (Finset.mem_Icc.mp hq).1)
    exact (e.trans (mul_le_mul_of_nonneg_left (all_inv_totient_cube Q) (by positivity))).trans_eq (by dsimp [κ,H,G]; ring)
  have hv : (∫ x in (0:ℝ)..1, V x) ≤ 16384*G*κ^4*H^3/(D:ℝ)^2 := by
    have e := fourthEnvelope_integral hW (b:=b₂) hr hrY high (fun q hq => (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1)
    exact (e.trans (mul_le_mul_of_nonneg_left (sum_inv_totient_cube_of_totient_gt Q D hD)
      (by positivity))).trans_eq (by dsimp [κ,H,G]; ring)
  have he : (∫ x in (0:ℝ)..1, E x) ≤ B*(κ^4*H^3/(D:ℝ)) := by
    dsimp only [E]
    have hi1 : IntervalIntegrable (fun x => (8/(D:ℝ))*(S x+U x)) MeasureTheory.volume 0 1 :=
      ((cs.intervalIntegrable _ _).add cu).const_mul _
    have hi2 : IntervalIntegrable (fun x => (D:ℝ)*V x) MeasureTheory.volume 0 1 :=
      cv.const_mul _
    rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,intervalIntegral.integral_add
      (cs.intervalIntegrable _ _) cu]
    refine (add_le_add (mul_le_mul_of_nonneg_left (add_le_add hS hu) (by positivity : 0 ≤ 8/(D:ℝ)))
      (mul_le_mul_of_nonneg_left hv hD'.le)).trans_eq ?_
    dsimp only [B]
    field_simp
  have hlow : ∀ q ∈ low, 0 < q ∧ q ≤ Y := by
    intro q hq
    have h := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
    exact ⟨h.1,h.2.trans hQY⟩
  have h := mixed_split_error hC hN hW hr hrY (by omega) hQ hb₁ hcop hb₂ low hlow E
    ce hnn hpt
  let P := F*κ^2*(Y:ℝ)*H*L^2
  have hP : 0 ≤ P := by dsimp [P]; positivity
  change I ≤ P * (∑ q ∈ low, (q:ℝ)/(q.totient:ℝ)^2) + ∫ x in (0:ℝ)..1, E x at h
  calc I ≤ _ := h
       _ ≤ P*(J*Real.log (2*(D:ℝ))) + B*(κ^4*H^3/(D:ℝ)) := add_le_add
         (mul_le_mul_of_nonneg_left (sum_div_totient_sq_of_totient_le Q D hD) hP) he
       _ = (F*J)*(κ^2*Y*H*L^2*Real.log (2*(D:ℝ))) + B*(κ^4*H^3/(D:ℝ)) := by dsimp [P]; ring
       _ ≤ _ := (add_le_add (mul_le_mul_of_nonneg_right hfA (by positivity))
         (mul_le_mul_of_nonneg_right hbA (by positivity))).trans_eq (mul_add _ _ _).symm

/-- Taking every denominator gives both a logarithm of the cutoff and an independent
bound retaining the coprime, squarefree denominator restriction. -/
private theorem short_fixed_mixed_all_of_inputs {C : ℝ} (hC : 0<C)
    (hN : ShortNumeratorInput C) (hW : ShortKernelInput) :
    ∃ A : ℝ, 0<A ∧ ∀ {r b₁ b₂ Y Q : ℕ}, 0<r → b₁<r → Nat.Coprime b₁ r → b₂<r →
      r≤Y → 2≤Y → 0<Q → Q≤Y → 2^72≤Y →
      let κ := (r:ℝ)/r.totient
      let H := (Y:ℝ)/r
      let L := Real.log (2*(Y:ℝ))
      let R := fun x ↦ smoothedPrimeSum r b₁ Y x - shortContModel r b₁ Y Q x
      let I := ∫ x in (0:ℝ)..1, ‖R x‖^2*‖shortContModel r b₂ Y Q x‖^2
      I ≤ A*(κ^2*Y*H*L^2*Real.log (2*(Q:ℝ))) ∧ I ≤ A*(κ*Y*H*L^3) := by
  let F := C*4096
  let J := 8*Real.exp 4+8*Real.exp 16
  let A := F*(J+72)
  have hF : 0<F := by dsimp [F]; positivity
  have hJ : 0<J := by dsimp [J]; positivity
  have hA : 0<A := by dsimp [A]; positivity
  have hA₁ : F*J≤A := by dsimp [A]; nlinarith
  have hA₂ : 72*F≤A := by dsimp [A]; nlinarith [mul_pos hF hJ]
  refine ⟨A,hA,?_⟩
  intro r b₁ b₂ Y Q hr hb₁ hcop hb₂ hrY hY hQ hQY hy κ H L R I
  let active := ((Finset.Icc 1 Q).filter (fun q ↦ Nat.Coprime q r)).filter Squarefree
  have hdom : ∀ q∈active, 0<q ∧ q≤Y := by
    intro q hq
    have hh := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    exact ⟨hh.1,hh.2.trans hQY⟩
  have hzero : ∀ c∈centers Q, c.q∉active → ∀ x∈voronoiCell Q c,
      ‖R x‖^2*‖shortContModel r b₂ Y Q x‖^2 ≤ (0:ℝ) := by
    intro c hc hnot x hx
    rw [shortModel_on_cell hx,norm_mul,mixed_coeff_norm]
    rw [ite_eq_right (fun h ↦ hnot (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨c.q_pos,mem_centers_iff.mp hc⟩,h.1⟩,h.2⟩))]
    simp
  have hi := mixed_split_error hC hN hW hr hrY hY hQ hb₁ hcop hb₂ active hdom
    (fun _ ↦ 0) (continuous_const.intervalIntegrable _ _) (fun _ ↦ le_rfl) hzero
  let P := F*κ^2*(Y:ℝ)*H*L^2
  have hP : 0≤P := by dsimp [P,H]; positivity
  change I ≤ P * (∑ q ∈ active, (q:ℝ)/(q.totient:ℝ)^2) + _ at hi
  simp only [intervalIntegral.integral_zero,add_zero] at hi
  have hsub : active ⊆ (Finset.Icc 1 Q).filter (fun q ↦ q.totient≤Q) := by
    intro q hq
    have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    exact Finset.mem_filter.mpr ⟨hh,(Nat.totient_le q).trans (Finset.mem_Icc.mp hh).2⟩
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f:=fun q : ℕ ↦ (q:ℝ)/(q.totient:ℝ)^2)
    hsub (fun q _ _ ↦ by positivity)
  have hQlog : 0 ≤ Real.log (2*(Q:ℝ)) := Real.log_nonneg (by
    have h : (1:ℝ) ≤ Q := Nat.one_le_cast.mpr hQ; linarith)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hL : 0 ≤ L := (by linarith [one_le_log_two_mul hY] : 0 ≤ Real.log (2*(Y:ℝ)))
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  constructor
  · refine (hi.trans (mul_le_mul_of_nonneg_left (hsum.trans (sum_div_totient_sq_of_totient_le Q Q hQ)) hP)).trans ?_
    change P*(J*Real.log (2*(Q:ℝ))) ≤ _
    calc _ = (F*J)*(κ^2*Y*H*L^2*Real.log (2*(Q:ℝ))) := by dsimp [P]; ring
         _ ≤ _ := mul_le_mul_of_nonneg_right hA₁ (by positivity)
  · have hcanc : κ*((r.totient:ℝ)/r)=1 := by
      have hr' : (r:ℝ) ≠0 := Nat.cast_ne_zero.mpr hr.ne'
      have ht' : (r.totient:ℝ) ≠0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hr).ne'
      dsimp [κ]; field_simp
    refine (hi.trans (mul_le_mul_of_nonneg_left (sum_coprime_sqfree_div_totient_sq_le hr hrY hQY hy) hP)).trans ?_
    calc _ = (72*F*(κ*Y*H*L^3))*(κ*((r.totient:ℝ)/r)) := by dsimp [P,L]; ring
         _ = (72*F)*(κ*Y*H*L^3) := by rw [hcanc,mul_one]
         _ ≤ _ := mul_le_mul_of_nonneg_right hA₂ (by positivity)

/-- Splitting at `φ(q) = D` gives a uniform bound for every order of the short Farey model. -/
theorem short_fixed_mixed_integral_fourth_bound (hGRH : DirichletGRH) :
    ∃ A : ℝ, 0<A ∧ ∀ {r b₁ b₂ Y Q : ℕ}, 0<r → b₁<r → Nat.Coprime b₁ r → b₂<r →
      r≤Y → 2≤Y → 0<Q → Q≤Y → (r:ℝ)≤4*((Y:ℝ)/r) → ∀ D : ℕ, 1≤D →
      let κ := (r:ℝ)/r.totient
      let H := (Y:ℝ)/r
      let L := Real.log (2*(Y:ℝ))
      let R := fun x ↦ smoothedPrimeSum r b₁ Y x - shortContModel r b₁ Y Q x
      let I := ∫ x in (0:ℝ)..1, ‖R x‖^2*‖shortContModel r b₂ Y Q x‖^2
      I ≤ A*(κ^2*Y*H*L^2*Real.log (2*(D:ℝ))+κ^4*H^3/(D:ℝ)) := by
  obtain ⟨C,hC,hN⟩ := short_fixed_num_remainder_sq_of_smoothedTwist
    (smoothedTwistEstimate_of_dirichletGRH hGRH)
  exact short_fixed_mixed_fourth_of_inputs hC hN shortContKernel_weighted_l2

/-- The two all-denominator estimates preserve, respectively, the order of the model and
the saving from squarefree denominators coprime to the fixed modulus. -/
theorem short_fixed_mixed_integral_all_bounds (hGRH : DirichletGRH) :
    ∃ A : ℝ, 0<A ∧ ∀ {r b₁ b₂ Y Q : ℕ}, 0<r → b₁<r → Nat.Coprime b₁ r → b₂<r →
      r≤Y → 2≤Y → 0<Q → Q≤Y → 2^72≤Y →
      let κ := (r:ℝ)/r.totient
      let H := (Y:ℝ)/r
      let L := Real.log (2*(Y:ℝ))
      let R := fun x ↦ smoothedPrimeSum r b₁ Y x - shortContModel r b₁ Y Q x
      let I := ∫ x in (0:ℝ)..1, ‖R x‖^2*‖shortContModel r b₂ Y Q x‖^2
      I ≤ A*(κ^2*Y*H*L^2*Real.log (2*(Q:ℝ))) ∧ I ≤ A*(κ*Y*H*L^3) := by
  obtain ⟨C,hC,hN⟩ := short_fixed_num_remainder_sq_of_smoothedTwist
    (smoothedTwistEstimate_of_dirichletGRH hGRH)
  exact short_fixed_mixed_all_of_inputs hC hN shortContKernel_weighted_l2

end FareyGoldbach
