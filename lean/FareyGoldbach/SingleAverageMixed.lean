import FareyGoldbach.AveragedRemainder

/-! The mixed fixed-class remainder/model term. Reduced numerators are summed
before the kernel is integrated. A totient cutoff isolates large denominators
without a pointwise loss from replacing φ(q) by q. -/

open Real Complex Set
open scoped BigOperators Classical

namespace FareyGoldbach

private abbrev MixedTwist (C : ℝ) :=
  ∀ (Y d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (t : ℝ),
    2 ≤ Y → |t| ≤ 1 / 2 →
      ‖smoothedTiltedRemainder χ Y t‖ ≤
        C * Real.sqrt ((Y : ℝ) * (1 + |t| * Y)) * Real.log (2 * (d : ℝ) * Y)

private noncomputable def localMixed (r b b' Y a q : ℕ) (t : ℝ) : ℝ :=
  ‖localRemainder r b Y a q t‖ ^ 2 * ‖smoothedKernel r b' Y t‖ ^ 2

private lemma localMixed_cont (r b b' Y a q : ℕ) : Continuous (localMixed r b b' Y a q) := by
  unfold localMixed localRemainder localModelTerm
  have hS := (continuous_smoothedPrimeSum r b Y).comp (continuous_const.add continuous_id : Continuous (fun t : ℝ => (a:ℝ)/q + t))
  have hV := continuous_smoothedKernel r b Y
  have hW := continuous_smoothedKernel r b' Y
  split_ifs
  · exact (((hS.sub (continuous_const.mul hV)).norm).pow 2).mul (hW.norm.pow 2)
  · exact (((hS.sub continuous_const).norm).pow 2).mul (hW.norm.pow 2)

private lemma primeSum_period_one (r b Y : ℕ) : Function.Periodic (smoothedPrimeSum r b Y) 1 := by
  intro t
  unfold smoothedPrimeSum
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  apply e_eq_of_sub_int (k := (j : ℤ))
  push_cast
  ring

private lemma localMixed_period (r b b' Y a q : ℕ) : Function.Periodic (localMixed r b b' Y a q) 1 := by
  intro t
  unfold localMixed localRemainder localModelTerm
  rw [← add_assoc, primeSum_period_one r b Y, smoothedKernel_periodic r b' Y t]
  split_ifs <;> simp [smoothedKernel_periodic r b Y t]

private lemma localMixed_shift (r b b' Y a q : ℕ) :
    (∫ x in (0:ℝ)..1, localMixed r b b' Y a q (x - (a:ℝ)/q)) =
      ∫ t in (-(1/2):ℝ)..(1/2), localMixed r b b' Y a q t := by
  have hper : Function.Periodic (fun x => localMixed r b b' Y a q (x - (a:ℝ)/q)) 1 := by
    intro x
    change localMixed _ _ _ _ _ _ (x + 1 - _) = _
    rw [show x + 1 - (a:ℝ)/q = (x - (a:ℝ)/q) + 1 by ring]
    exact localMixed_period _ _ _ _ _ _ _
  rw [intervalIntegral_shift_symm hper ((a:ℝ)/q)]
  simp only [add_sub_cancel_left]

private lemma fixed_mixed_numerator_integral {C : ℝ} (hC : 0 < C) (hTw : MixedTwist C)
    {r b b' Y q : ℕ} (hr : 0 < r) (hrY : r ≤ Y) (hY : 2 ≤ Y)
    (hq : 0 < q) (hqY : q ≤ Y) (hb : b < r) (hc : Nat.Coprime b r) (hb' : b' < r) :
    (∑ a ∈ coprimeClasses q, ∫ x in (0:ℝ)..1, localMixed r b b' Y a q (x - (a:ℝ)/q)) ≤
      ((3 * (3*C+1)^2 + 3075) * (q:ℝ) * Y * (Real.log (2*(Y:ℝ)))^2) *
        (4096 * ((Y:ℝ)/r)) := by
  simp_rw [localMixed_shift]
  rw [← intervalIntegral_finset_sum (fun a _ => (localMixed_cont r b b' Y a q).intervalIntegrable _ _)]
  let k := (3*(3*C+1)^2 + 3075) * (q:ℝ) * Y * (Real.log (2*(Y:ℝ)))^2
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (f := fun t => ∑ a ∈ coprimeClasses q, localMixed r b b' Y a q t)
      (g := fun t => k * ((1+((Y:ℝ)/r)*|t|) * ‖smoothedKernel r b' Y t‖^2))
      (by norm_num : (-(1/2):ℝ) ≤ 1/2)
      ((continuous_sum_finset (coprimeClasses q) fun a _ => localMixed_cont r b b' Y a q).intervalIntegrable _ _)
      ((continuous_const.mul ((continuous_const.add (continuous_const.mul continuous_abs)).mul
        ((continuous_norm.comp (continuous_smoothedKernel r b' Y)).pow 2))).intervalIntegrable _ _)
      (fun t ht => by
        have hn := fixed_num_remainder_sq hC hTw hr hrY hY hq hqY hb hc (β:=t) (abs_le.mpr ht)
        simp only [localMixed, ← Finset.sum_mul]
        calc _ ≤ _ := mul_le_mul_of_nonneg_right hn (sq_nonneg ‖smoothedKernel r b' Y t‖)
             _ = _ := by dsimp [k]; ring)
  rw [intervalIntegral.integral_const_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left (integral_one_add_mul_norm_smoothedKernel_sq_le hr hrY hb') hk)



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

private lemma mixed_integrables (r b b' Y Q : ℕ) :
    let R := fun x => smoothedPrimeSum r b Y x - modelSum r b Y Q Q x
    IntervalIntegrable (fun x => ‖R x‖^2) MeasureTheory.volume 0 1 ∧
    IntervalIntegrable (fun x => ‖R x‖^2 * ‖modelSum r b' Y Q Q x‖^2) MeasureTheory.volume 0 1 := by
  intro R
  obtain ⟨A,hA⟩ := modelSum_norm_bounded r b Y Q Q
  obtain ⟨B,hB⟩ := modelSum_norm_bounded r b' Y Q Q
  let T := ∑ j ∈ Finset.range (Y/r+1), |quarticBump ((r*j+b :ℝ)/Y) * primeWeight (r*j+b)|
  have hS (x : ℝ) : ‖smoothedPrimeSum r b Y x‖ ≤ T := by
    unfold smoothedPrimeSum T
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hR (x : ℝ) : ‖R x‖^2 ≤ (T+A)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (add_le_add (hS x) (hA x))) 2
  have hm : Measurable (fun x => ‖R x‖^2) := (((continuous_smoothedPrimeSum r b Y).measurable.sub
    (modelSum_measurable r b Y Q Q)).norm).pow_const 2
  constructor
  · refine intervalIntegrable_of_measurable_bounded (B := (T+A)^2) hm fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖R x‖)]
    exact hR x
  · refine intervalIntegrable_of_measurable_bounded (B := (T+A)^2*B^2) (hm.mul ((modelSum_measurable r b' Y Q Q).norm.pow_const 2)) fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact mul_le_mul (hR x) (pow_le_pow_left₀ (norm_nonneg _) (hB x) 2) (sq_nonneg _) (sq_nonneg _)

/-- A family of complete numerator sums majorizes the cells with denominators
in `s`. An integrable nonnegative error covers the remaining cells. -/
private lemma mixed_split_error {C : ℝ} (hC : 0 < C) (hTw : MixedTwist C)
    {r b b' Y Q : ℕ} (hr : 0 < r) (hrY : r ≤ Y) (hY : 2 ≤ Y) (hQ : 0 < Q)
    (hb : b < r) (hc : Nat.Coprime b r) (hb' : b' < r)
    (s : Finset ℕ) (hs : ∀ q ∈ s, 0 < q ∧ q ≤ Y) (E : ℝ → ℝ)
    (hEi : IntervalIntegrable E MeasureTheory.volume 0 1) (hE0 : ∀ x, 0 ≤ E x)
    (hE : ∀ c ∈ centers Q, c.q ∉ s → ∀ x ∈ voronoiCell Q c,
      ‖smoothedPrimeSum r b Y x - modelSum r b Y Q Q x‖^2 * ‖modelSum r b' Y Q Q x‖^2 ≤ E x) :
    let κ := (r:ℝ)/r.totient
    let R := fun x => smoothedPrimeSum r b Y x - modelSum r b Y Q Q x
    (∫ x in (0:ℝ)..1, ‖R x‖^2 * ‖modelSum r b' Y Q Q x‖^2) ≤
      ((3*(3*C+1)^2+3075)*4096 * κ^2 * Y * ((Y:ℝ)/r) * (Real.log (2*(Y:ℝ)))^2) *
        (∑ q ∈ s, (q:ℝ)/(q.totient:ℝ)^2) +
        (∫ x in (0:ℝ)..1, E x) := by
  classical
  intro κ R
  let g := fun (q a : ℕ) (x : ℝ) => localMixed r b b' Y a q (x-(a:ℝ)/q)
  let V := fun (q : ℕ) (x : ℝ) => (κ/(q.totient:ℝ))^2 * ∑ a ∈ coprimeClasses q, g q a x
  have hg (q a : ℕ) : Continuous (g q a) :=
    (localMixed_cont r b b' Y a q).comp (continuous_id.sub continuous_const)
  have hv (q : ℕ) : Continuous (V q) :=
    continuous_const.mul (continuous_sum_finset (coprimeClasses q) fun a _ => hg q a)
  have vg (q : ℕ) (x : ℝ) : 0 ≤ V q x := by
    dsimp [V,g,localMixed]; positivity
  obtain ⟨_, hint⟩ := mixed_integrables r b b' Y Q
  have hi := intervalIntegral.integral_mono_on zero_le_one hint
      (((continuous_sum_finset s fun q _ => hv q).intervalIntegrable _ _).add hEi)
      (fun x _ => by
        change ‖R x‖^2 * ‖modelSum r b' Y Q Q x‖^2 ≤ (∑ q ∈ s, V q x) + E x
        obtain ⟨c,hcq,hx⟩ := voronoiCell_cover Q hQ x
        by_cases h : c.q ∈ s
        · have hrx : R x = localRemainder r b Y c.a c.q (x-c.val) := by
            dsimp [R,localRemainder,localModelTerm]
            rw [modelSum_eq_on_cell_le hx (mem_centers_iff.mp hcq), smoothedKernel_wrap]
            unfold modelCoeff RatCenter.val
            simp only [add_sub_cancel]; split_ifs <;> ring
          have hm : ‖modelSum r b' Y Q Q x‖^2 ≤ (κ/(c.q.totient:ℝ))^2 * ‖smoothedKernel r b' Y (x-c.val)‖^2 := by
            rw [modelSum_eq_on_cell_le hx (mem_centers_iff.mp hcq), smoothedKernel_wrap, norm_mul, mul_pow,
              mixed_coeff_norm]
            split_ifs
            · exact le_rfl
            · simp only [zero_pow (by decide : 2 ≠ 0), zero_mul]; positivity
          have hterm : ‖R x‖^2 * ‖modelSum r b' Y Q Q x‖^2 ≤ V c.q x := by
            calc _ ≤ ‖R x‖^2 * ((κ/(c.q.totient:ℝ))^2 * ‖smoothedKernel r b' Y (x-c.val)‖^2) :=
                   mul_le_mul_of_nonneg_left hm (sq_nonneg _)
                 _ = (κ/(c.q.totient:ℝ))^2 * g c.q c.a x := by rw [hrx]; dsimp [g,localMixed,RatCenter.val]; ring
                 _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.single_le_sum
                     (f := fun a => g c.q a x) (fun a _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
                     (mem_coprimeClasses.mpr ⟨c.a_lt,c.coprime⟩)) (sq_nonneg _)
          exact (hterm.trans (Finset.single_le_sum (fun q _ => vg q x) h)).trans
            (le_add_of_nonneg_right (hE0 x))
        · exact (hE c hcq h x hx).trans (le_add_of_nonneg_left (Finset.sum_nonneg fun q _ => vg q x)))
  rw [intervalIntegral.integral_add ((continuous_sum_finset s fun q _ => hv q).intervalIntegrable _ _)
         hEi,
      intervalIntegral_finset_sum (fun q _ => (hv q).intervalIntegrable _ _)] at hi
  refine hi.trans (add_le_add ?_ le_rfl)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q hq => ?_
  dsimp only [V]
  rw [intervalIntegral.integral_const_mul, intervalIntegral_finset_sum
        (fun a _ => (hg q a).intervalIntegrable _ _)]
  have bound := fixed_mixed_numerator_integral hC hTw hr hrY hY (hs q hq).1 (hs q hq).2 hb hc hb'
  exact (mul_le_mul_of_nonneg_left bound (sq_nonneg (κ / (q.totient:ℝ)))).trans_eq (by ring)





private lemma mixed_split {C : ℝ} (hC : 0 < C) (hTw : MixedTwist C)
    {r b b' Y Q : ℕ} (hr : 0 < r) (hrY : r ≤ Y) (hY : 2 ≤ Y) (hQ : 0 < Q)
    (hb : b < r) (hc : Nat.Coprime b r) (hb' : b' < r)
    (s : Finset ℕ) (hs : ∀ q ∈ s, 0 < q ∧ q ≤ Y) (T : ℝ)
    (hT0 : 0 ≤ T) (hT : ∀ c ∈ centers Q, c.q ∉ s → ∀ x ∈ voronoiCell Q c,
      ‖modelSum r b' Y Q Q x‖ ^ 2 ≤ T) :
    let κ := (r:ℝ)/r.totient
    let R := fun x => smoothedPrimeSum r b Y x - modelSum r b Y Q Q x
    (∫ x in (0:ℝ)..1, ‖R x‖^2 * ‖modelSum r b' Y Q Q x‖^2) ≤
      ((3*(3*C+1)^2+3075)*4096 * κ^2 * Y * ((Y:ℝ)/r) * (Real.log (2*(Y:ℝ)))^2) *
        (∑ q ∈ s, (q:ℝ)/(q.totient:ℝ)^2) + T * (∫ x in (0:ℝ)..1, ‖R x‖^2) := by
  intro κ R
  have h := mixed_split_error hC hTw hr hrY hY hQ hb hc hb' s hs (fun x => T * ‖R x‖^2)
    ((mixed_integrables r b b' Y Q).1.const_mul T) (fun x => mul_nonneg hT0 (sq_nonneg _))
    (fun c hh h x hx => by
      rw [mul_comm T]
      exact mul_le_mul_of_nonneg_left (hT c hh h x hx) (sq_nonneg _))
  simpa only [intervalIntegral.integral_const_mul] using h

/-- Cutoff and unrestricted estimates for the same fixed-class mixed integral. -/
theorem fixed_mixed_integral_bounds {C : ℝ} (hC : 0 < C)
    (hTw : ∀ (Y d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (t : ℝ),
      2 ≤ Y → |t| ≤ 1 / 2 → ‖smoothedTiltedRemainder χ Y t‖ ≤
        C * Real.sqrt ((Y : ℝ) * (1 + |t| * Y)) * Real.log (2 * (d : ℝ) * Y))
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ A : ℝ, 0 < A ∧ ∀ {r b₁ b₂ Y : ℕ}, 0 < r → b₁ < r → Nat.Coprime b₁ r → b₂ < r →
      2^72 ≤ Y/r →
      let Q := routeAQ Y r
      let κ := (r:ℝ)/r.totient
      let H := (Y:ℝ)/r
      let L := Real.log (2*(Y:ℝ))
      let R := fun x => smoothedPrimeSum r b₁ Y x - modelSum r b₁ Y Q Q x
      let I := ∫ x in (0:ℝ)..1, ‖R x‖^2 * ‖modelSum r b₂ Y Q Q x‖^2
      (∫ x in (0:ℝ)..1, ‖R x‖^2) ≤ K*κ*H*L → ∀ D : ℕ, 1 ≤ D →
        I ≤ A*(κ^2*Y*H*L^2*Real.log (2*(D:ℝ)) + κ^3*H^3*L/(D:ℝ)^2) ∧
        I ≤ A*(κ*Y*H*L^3) := by
  classical
  let F := (3*(3*C+1)^2+3075)*4096
  let J := 8*Real.exp 4 + 8*Real.exp 16
  let A := 1 + F*(J+72) + 4*K
  have hF : 0 < F := by dsimp [F]; positivity
  have hJ : 0 < J := by dsimp [J]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hA1 : F*J ≤ A := by dsimp [A]; nlinarith
  have hA2 : 4*K ≤ A := by dsimp [A]; nlinarith [mul_pos hF hJ]
  have hA3 : 72*F ≤ A := by dsimp [A]; nlinarith [mul_pos hF hJ]
  refine ⟨A,hA,?_⟩
  intro r b₁ b₂ Y hr hb₁ hcop hb₂ hHuge Q κ H L R I hR D hD
  have hy : 2^72 ≤ Y := hHuge.trans (Nat.div_le_self _ _)
  have hrY : r ≤ Y := by
    calc r = r*1 := (mul_one _).symm
         _ ≤ r*(Y/r) := Nat.mul_le_mul_left _ (by omega)
         _ ≤ Y := Nat.mul_div_le _ _
  obtain ⟨hQ2,_,_,hQY⟩ := routeAQ_bounds hr (by exact le_trans (by norm_num : 2^26 ≤ 2^72) hHuge)
  have hQ : 0 < Q := by omega
  have hrR : (0:ℝ) < r := Nat.cast_pos.mpr hr
  have hφ : (0:ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hκ : 0 < κ := div_pos hrR hφ
  have hH : 1 ≤ H := (one_le_div hrR).2 (Nat.cast_le.mpr hrY)
  have hL : 1 ≤ L := one_le_log_two_mul (by omega)
  have hH0 : 0 < H := by linarith
  have hL0 : 0 < L := by linarith
  have hD' : (0:ℝ) < D := Nat.cast_pos.mpr hD
  have hlog : 0 ≤ Real.log (2*(D:ℝ)) := Real.log_nonneg (by
    have : (1:ℝ) ≤ D := by exact_mod_cast hD
    linarith)
  let active := ((Finset.Icc 1 Q).filter (fun q => Nat.Coprime q r)).filter Squarefree
  let small := (Finset.Icc 1 Q).filter (fun q => q.totient ≤ D)
  have active_dom : ∀ q ∈ active, 0 < q ∧ q ≤ Y := by
    intro q hq
    have hh := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    exact ⟨hh.1,hh.2.trans hQY⟩
  have small_dom : ∀ q ∈ small, 0 < q ∧ q ≤ Y := by
    intro q hq
    have hh := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
    exact ⟨hh.1,hh.2.trans hQY⟩
  let P := F*κ^2*(Y:ℝ)*H*L^2
  have hP : 0 ≤ P := by dsimp [P]; positivity
  constructor
  · let T := (2*κ*H/(D:ℝ))^2
    have hh : ∀ c ∈ centers Q, c.q ∉ small → ∀ x ∈ voronoiCell Q c,
        ‖modelSum r b₂ Y Q Q x‖^2 ≤ T := by
      intro c hc hnot x hx
      have hqd : D < c.q.totient := lt_of_not_ge (fun h => hnot (Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨c.q_pos, mem_centers_iff.mp hc⟩,h⟩))
      have hge : (D:ℝ) ≤ c.q.totient := Nat.cast_le.mpr hqd.le
      rw [modelSum_eq_on_cell_le hx (mem_centers_iff.mp hc), norm_mul, mixed_coeff_norm]
      split_ifs
      · apply pow_le_pow_left₀ (by positivity)
        calc _ ≤ (κ/(D:ℝ))*(2*H) := by
               apply mul_le_mul (div_le_div_of_nonneg_left hκ.le hD' hge)
                 ((smoothedKernel_bound_triv r b₂ Y _).trans (by change H+1≤2*H; linarith))
                 (norm_nonneg _) (by positivity)
             _ = _ := by ring
      · simp only [zero_mul, zero_pow (by decide : 2 ≠ 0)]; exact sq_nonneg _
    have h := mixed_split hC hTw hr hrY (by omega) hQ hb₁ hcop hb₂ small small_dom T (sq_nonneg _) hh
    change I ≤ P*(∑ q ∈ small, (q:ℝ)/(q.totient:ℝ)^2) + T*(∫ x in (0:ℝ)..1, ‖R x‖^2) at h
    have lower := sum_div_totient_sq_of_totient_le Q D hD
    calc I ≤ _ := h
         _ ≤ P*(J*Real.log (2*(D:ℝ))) + T*(K*κ*H*L) :=
           add_le_add (mul_le_mul_of_nonneg_left lower hP) (mul_le_mul_of_nonneg_left hR (sq_nonneg _))
         _ = (F*J)*(κ^2*Y*H*L^2*Real.log (2*(D:ℝ))) + (4*K)*(κ^3*H^3*L/(D:ℝ)^2) := by
           dsimp [P,T]; ring
         _ ≤ _ := by
           exact (add_le_add (mul_le_mul_of_nonneg_right hA1 (by positivity))
             (mul_le_mul_of_nonneg_right hA2 (by positivity))).trans_eq (mul_add _ _ _).symm
  · have hh : ∀ c ∈ centers Q, c.q ∉ active → ∀ x ∈ voronoiCell Q c,
        ‖modelSum r b₂ Y Q Q x‖^2 ≤ 0 := by
      intro c hc hnot x hx
      rw [modelSum_eq_on_cell_le hx (mem_centers_iff.mp hc),norm_mul,mixed_coeff_norm]
      rw [ite_eq_right (fun h => hnot (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨c.q_pos,mem_centers_iff.mp hc⟩,h.1⟩,h.2⟩))]
      simp
    have h := mixed_split hC hTw hr hrY (by omega) hQ hb₁ hcop hb₂ active active_dom 0 le_rfl hh
    change I ≤ P*(∑ q ∈ active, (q:ℝ)/(q.totient:ℝ)^2) + 0*_ at h
    simp only [zero_mul,add_zero] at h
    have hcanc : κ * ((r.totient:ℝ)/r) = 1 := by dsimp [κ]; field_simp
    calc I ≤ _ := h
         _ ≤ P*(72*((r.totient:ℝ)/r)*L) := mul_le_mul_of_nonneg_left
           (sum_coprime_sqfree_div_totient_sq_le hr hrY hQY hy) hP
         _ = 72*F*(κ*Y*H*L^3) := by
           calc _ = (72*F*(κ*Y*H*L^3))*(κ*((r.totient:ℝ)/r)) := by dsimp [P]; ring
                _ = _ := by rw [hcanc,mul_one]
         _ ≤ _ := mul_le_mul_of_nonneg_right hA3 (by positivity)







private lemma integral_periodic_translate {f : ℝ → ℝ} (hf : Function.Periodic f 1) (u : ℝ) :
    (∫ x in (0:ℝ)..1, f (x-u)) = ∫ x in (0:ℝ)..1, f x := by
  have hs : Function.Periodic (fun x => f (x-u)) 1 := by
    intro x
    change f (x+1-u) = _
    rw [show x+1-u=(x-u)+1 by ring,hf]
  rw [intervalIntegral_shift_symm hs u, intervalIntegral_shift_symm hf 0]
  simp

set_option maxHeartbeats 1600000 in
private lemma kernel_fourth_mean {r b Y : ℕ} (hr : 0 < r) (hrY : r ≤ Y) (u : ℝ) :
    (∫ x in (0:ℝ)..1, ‖smoothedKernel r b Y (x-u)‖^4) ≤ 8*((Y:ℝ)/r)^3 := by
  let H := (Y:ℝ)/r
  have hH : 1 ≤ H := (one_le_div (Nat.cast_pos.mpr hr)).2 (Nat.cast_le.mpr hrY)
  let f := fun t => ‖smoothedKernel r b Y t‖
  have hcont : Continuous f := (continuous_smoothedKernel r b Y).norm
  have hper : Function.Periodic (fun t => (f t)^4) 1 := by
    intro t; dsimp [f]; rw [smoothedKernel_periodic r b Y]
  have hpoint (x : ℝ) : f x^4 ≤ (2*H)^2*f x^2 := by
    have h1 : f x ≤ 2*H := (smoothedKernel_bound_triv r b Y x).trans (by change H+1 ≤ 2*H; linarith)
    calc f x^4 = f x^2*f x^2 := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) h1 2) (sq_nonneg _)
  have hshift := intervalIntegral_shift_symm hper 0
  simp only [zero_add] at hshift
  have hl₂ : (∫ t in (-(1/2):ℝ)..1/2, f t^2) ≤ H+1 := smoothedKernel_l2_le r b Y
  change (∫ x in (0:ℝ)..1, (f (x-u))^4) ≤ 8*H^3
  rw [integral_periodic_translate (f := fun t => (f t)^4) hper u,hshift]
  calc (∫ t in (-(1/2):ℝ)..1/2, f t^4) ≤ ∫ t in (-(1/2):ℝ)..1/2, (2*H)^2*f t^2 :=
         intervalIntegral.integral_mono_on (by norm_num)
           ((hcont.pow 4).intervalIntegrable _ _)
           ((continuous_const.mul (hcont.pow 2)).intervalIntegrable _ _) (fun t _ => hpoint t)
       _ = (2*H)^2*(∫ t in (-(1/2):ℝ)..1/2, f t^2) := intervalIntegral.integral_const_mul ..
       _ ≤ (2*H)^2*(2*H) := mul_le_mul_of_nonneg_left (hl₂.trans (by linarith)) (sq_nonneg _)
       _ = _ := by ring
/-- An everywhere nonnegative continuous majorant for the fourth power of the model
on the cells belonging to the supplied set of denominators. -/
private noncomputable def fourthEnvelope (r b Y : ℕ) (s : Finset ℕ) (x : ℝ) : ℝ :=
  ∑ q ∈ s, (((r:ℝ)/r.totient)/(q.totient:ℝ))^4 *
    ∑ a ∈ coprimeClasses q, ‖smoothedKernel r b Y (x-(a:ℝ)/q)‖^4

private lemma fourthEnvelope_cont (r b Y : ℕ) (s : Finset ℕ) : Continuous (fourthEnvelope r b Y s) := by
  unfold fourthEnvelope
  refine continuous_sum_finset s fun q _ => continuous_const.mul (continuous_sum_finset (coprimeClasses q) fun a _ => ?_)
  exact (((continuous_smoothedKernel r b Y).comp (continuous_id.sub continuous_const)).norm).pow 4

private lemma fourthEnvelope_nonneg (r b Y : ℕ) (s : Finset ℕ) (x : ℝ) : 0 ≤ fourthEnvelope r b Y s x := by
  unfold fourthEnvelope
  positivity

private lemma fourthEnvelope_on_cell {r b Y Q : ℕ} {c : RatCenter} {x : ℝ}
    (hx : x ∈ voronoiCell Q c) {s : Finset ℕ} (hc : c.q ∈ s) :
    ‖modelSum r b Y Q Q x‖^4 ≤ fourthEnvelope r b Y s x := by
  classical
  rw [modelSum_eq_on_cell_le hx (mem_centers_iff.mp hx.1), smoothedKernel_wrap,
    norm_mul,mul_pow,mixed_coeff_norm]
  split_ifs
  · refine le_trans ?_ (Finset.single_le_sum
      (f := fun q => (((r:ℝ)/r.totient)/(q.totient:ℝ))^4 *
        ∑ a ∈ coprimeClasses q, ‖smoothedKernel r b Y (x-(a:ℝ)/q)‖^4)
      (fun q _ => by positivity) hc)
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum
      (f := fun a : ℕ => ‖smoothedKernel r b Y (x-(a:ℝ)/c.q)‖^4)
      (fun a _ => by positivity) (mem_coprimeClasses.mpr ⟨c.a_lt,c.coprime⟩)) (by positivity)
  · simp only [zero_pow (by decide : 4 ≠ 0),zero_mul]
    exact fourthEnvelope_nonneg _ _ _ _ _

private lemma fourthEnvelope_integral {r b Y : ℕ} (hr : 0 < r) (hrY : r ≤ Y) (s : Finset ℕ)
    (hs : ∀ q ∈ s, 0 < q) :
    (∫ x in (0:ℝ)..1, fourthEnvelope r b Y s x) ≤
      (8*((r:ℝ)/r.totient)^4*((Y:ℝ)/r)^3)*∑ q ∈ s, (1:ℝ)/(q.totient:ℝ)^3 := by
  classical
  let f := fun (q a : ℕ) (x : ℝ) => ‖smoothedKernel r b Y (x-(a:ℝ)/q)‖^4
  have hf (q a : ℕ) : Continuous (f q a) :=
    (((continuous_smoothedKernel r b Y).comp (continuous_id.sub continuous_const)).norm).pow 4
  let J := fun (q : ℕ) (x : ℝ) => (((r:ℝ)/r.totient)/(q.totient:ℝ))^4 * ∑ a ∈ coprimeClasses q, f q a x
  have cj (q : ℕ) : Continuous (J q) := continuous_const.mul (continuous_sum_finset (coprimeClasses q) fun a _ => hf q a)
  change (∫ x in (0:ℝ)..1, ∑ q ∈ s, J q x) ≤ _
  rw [intervalIntegral_finset_sum (fun q _ => (cj q).intervalIntegrable _ _), Finset.mul_sum]
  refine Finset.sum_le_sum fun q hq => ?_
  dsimp only [J]
  rw [intervalIntegral.integral_const_mul, intervalIntegral_finset_sum (fun a _ => (hf q a).intervalIntegrable _ _)]
  have hh : (∑ a ∈ coprimeClasses q, ∫ x in (0:ℝ)..1, f q a x) ≤
      (q.totient:ℝ)*(8*((Y:ℝ)/r)^3) := by
    calc _ ≤ ∑ _a ∈ coprimeClasses q, (8*((Y:ℝ)/r)^3) := Finset.sum_le_sum
           (fun a _ => kernel_fourth_mean (b:=b) hr hrY ((a:ℝ)/q))
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

/-- The fixed-class fourth-moment input changes the high-totient term to
κ⁴ H³/D. All other inputs are the smoothed twist and the existing kernel bound. -/
theorem fixed_mixed_integral_fourth_bound {C : ℝ} (hC : 0 < C)
    (hTw : ∀ (Y d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (t : ℝ),
      2 ≤ Y → |t| ≤ 1 / 2 → ‖smoothedTiltedRemainder χ Y t‖ ≤
        C * Real.sqrt ((Y : ℝ) * (1 + |t| * Y)) * Real.log (2 * (d : ℝ) * Y))
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ A : ℝ, 0 < A ∧ ∀ {r b₁ b₂ Y : ℕ}, 0 < r → b₁ < r → Nat.Coprime b₁ r → b₂ < r →
      2^72 ≤ Y/r →
      let Q := routeAQ Y r
      let κ := (r:ℝ)/r.totient
      let H := (Y:ℝ)/r
      let L := Real.log (2*(Y:ℝ))
      let R := fun x => smoothedPrimeSum r b₁ Y x - modelSum r b₁ Y Q Q x
      let I := ∫ x in (0:ℝ)..1, ‖R x‖^2 * ‖modelSum r b₂ Y Q Q x‖^2
      (∫ x in (0:ℝ)..1, ‖smoothedPrimeSum r b₁ Y x‖^4) ≤ K*κ^4*H^3 → ∀ D : ℕ, 1 ≤ D →
        I ≤ A*(κ^2*Y*H*L^2*Real.log (2*(D:ℝ)) + κ^4*H^3/(D:ℝ)) := by
  classical
  let F := (3*(3*C+1)^2+3075)*4096
  let J := 8*Real.exp 4 + 8*Real.exp 16
  let G := Real.exp 2 + 4*Real.exp 8
  let B := 8*(K+40*G)+32*G
  let A := 1+F*J+B
  have hF : 0 < F := by dsimp [F]; positivity
  have hJ : 0 < J := by dsimp [J]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hfA : F*J ≤ A := by dsimp [A]; linarith
  have hbA : B ≤ A := by dsimp [A]; nlinarith [mul_pos hF hJ]
  refine ⟨A,hA,?_⟩
  intro r b₁ b₂ Y hr hb₁ hcop hb₂ hHuge Q κ H L R I hS D hD
  have hy : 2^72 ≤ Y := hHuge.trans (Nat.div_le_self _ _)
  have hrY : r ≤ Y := by
    calc r = r*1 := (mul_one _).symm
         _ ≤ r*(Y/r) := Nat.mul_le_mul_left _ (by omega)
         _ ≤ Y := Nat.mul_div_le _ _
  obtain ⟨hQ2,_,_,hQY⟩ := routeAQ_bounds hr (by exact le_trans (by norm_num : 2^26 ≤ 2^72) hHuge)
  have hQ : 0 < Q := by omega
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
  have cu : Continuous U := fourthEnvelope_cont _ _ _ _
  have cv : Continuous V := fourthEnvelope_cont _ _ _ _
  have cs : Continuous S := (continuous_smoothedPrimeSum r b₁ Y).norm.pow 4
  have ce : Continuous E := (continuous_const.mul (cs.add cu)).add (continuous_const.mul cv)
  have hnn (x : ℝ) : 0 ≤ E x := by
    have hu : 0 ≤ U x := fourthEnvelope_nonneg _ _ _ _ _
    have hv : 0 ≤ V x := fourthEnvelope_nonneg _ _ _ _ _
    dsimp only [E,S]; positivity
  have hpt : ∀ c ∈ centers Q, c.q ∉ low → ∀ x ∈ voronoiCell Q c,
      ‖R x‖^2 * ‖modelSum r b₂ Y Q Q x‖^2 ≤ E x := by
    intro c hc hn x hx
    have hfull : c.q ∈ full := Finset.mem_Icc.mpr ⟨c.q_pos,mem_centers_iff.mp hc⟩
    have hhigh : c.q ∈ high := Finset.mem_filter.mpr ⟨hfull,lt_of_not_ge
      (fun h => hn (Finset.mem_filter.mpr ⟨hfull,h⟩))⟩
    have hR : ‖R x‖^4 ≤ 8*(S x+U x) := (norm_sub_fourth _ _).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (fourthEnvelope_on_cell (b:=b₁) hx hfull)) (by norm_num))
    calc _ ≤ ‖R x‖^4 / (D:ℝ) + (D:ℝ)*‖modelSum r b₂ Y Q Q x‖^4 :=
            mixed_young _ _ _ hD'
         _ ≤ (8*(S x+U x))/(D:ℝ) + (D:ℝ)*V x := add_le_add
            (div_le_div_of_nonneg_right hR hD'.le)
            (mul_le_mul_of_nonneg_left (fourthEnvelope_on_cell (b:=b₂) hx hhigh) hD'.le)
         _ = _ := by dsimp [E]; ring
  have hu : (∫ x in (0:ℝ)..1, U x) ≤ 40*G*κ^4*H^3 := by
    have e := fourthEnvelope_integral (b:=b₁) hr hrY full (fun q hq => (Finset.mem_Icc.mp hq).1)
    exact (e.trans (mul_le_mul_of_nonneg_left (all_inv_totient_cube Q) (by positivity))).trans_eq (by dsimp [κ,H,G]; ring)
  have hv : (∫ x in (0:ℝ)..1, V x) ≤ 32*G*κ^4*H^3/(D:ℝ)^2 := by
    have e := fourthEnvelope_integral (b:=b₂) hr hrY high (fun q hq => (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1)
    exact (e.trans (mul_le_mul_of_nonneg_left (sum_inv_totient_cube_of_totient_gt Q D hD)
      (by positivity))).trans_eq (by dsimp [κ,H,G]; ring)
  have he : (∫ x in (0:ℝ)..1, E x) ≤ B*(κ^4*H^3/(D:ℝ)) := by
    dsimp only [E]
    have hi1 : IntervalIntegrable (fun x => (8/(D:ℝ))*(S x+U x)) MeasureTheory.volume 0 1 :=
      ((cs.add cu).intervalIntegrable _ _).const_mul _
    have hi2 : IntervalIntegrable (fun x => (D:ℝ)*V x) MeasureTheory.volume 0 1 :=
      (cv.intervalIntegrable _ _).const_mul _
    rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,intervalIntegral.integral_add
      (cs.intervalIntegrable _ _) (cu.intervalIntegrable _ _)]
    refine (add_le_add (mul_le_mul_of_nonneg_left (add_le_add hS hu) (by positivity : 0 ≤ 8/(D:ℝ)))
      (mul_le_mul_of_nonneg_left hv hD'.le)).trans_eq ?_
    dsimp only [B]
    field_simp
  have hlow : ∀ q ∈ low, 0 < q ∧ q ≤ Y := by
    intro q hq
    have h := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
    exact ⟨h.1,h.2.trans hQY⟩
  have h := mixed_split_error hC hTw hr hrY (by omega) hQ hb₁ hcop hb₂ low hlow E
    (ce.intervalIntegrable _ _) hnn hpt
  let P := F*κ^2*(Y:ℝ)*H*L^2
  have hP : 0 ≤ P := by dsimp [P]; positivity
  change I ≤ P * (∑ q ∈ low, (q:ℝ)/(q.totient:ℝ)^2) + ∫ x in (0:ℝ)..1, E x at h
  calc I ≤ _ := h
       _ ≤ P*(J*Real.log (2*(D:ℝ))) + B*(κ^4*H^3/(D:ℝ)) := add_le_add
         (mul_le_mul_of_nonneg_left (sum_div_totient_sq_of_totient_le Q D hD) hP) he
       _ = (F*J)*(κ^2*Y*H*L^2*Real.log (2*(D:ℝ))) + B*(κ^4*H^3/(D:ℝ)) := by dsimp [P]; ring
       _ ≤ _ := (add_le_add (mul_le_mul_of_nonneg_right hfA (by positivity))
         (mul_le_mul_of_nonneg_right hbA (by positivity))).trans_eq (mul_add _ _ _).symm

end FareyGoldbach

