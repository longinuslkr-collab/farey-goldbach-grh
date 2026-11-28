import FareyGoldbach.ShortAveragedRemainder

/-! # Numerator Parseval for the continuous model -/

open MeasureTheory Set
open scoped Classical

namespace FareyGoldbach

private lemma continuous_prime_twist_le {C : ℝ}
    (hTw : ∀ (Y d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (t : ℝ),
      2≤Y → |t|≤1/2 → ‖smoothedTiltedRemainder χ Y t‖ ≤
        C*Real.sqrt ((Y:ℝ)*(1+|t| *Y))*Real.log (2*(d:ℝ)*Y))
    {Y d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) {t : ℝ} (hY : 2≤Y) (ht : |t|≤1/2) :
    ‖shortPrimeTwistedRemainder χ Y t‖ ≤
      (C+9)*Real.sqrt ((Y:ℝ)*(1+|t| *Y))*Real.log (2*(d:ℝ)*Y) := by
  let A := 1+|t| *(Y:ℝ)
  let L := Real.log (2*(d:ℝ)*Y)
  let P := Real.sqrt ((Y:ℝ)*A)
  let U := smoothedTiltedRemainder χ Y t
  let V := continuousTwistedRemainder χ Y t
  let W := shortPrimeTwistedRemainder χ Y t
  have hy : (2:ℝ)≤Y := by exact_mod_cast hY
  have hypos : (0:ℝ)<Y := by linarith
  have hY1 : 1≤Y := by omega
  have hL : 1≤L := one_le_log_two_d_Y hY
  have hA₁ : 1 ≤ A := by
    dsimp [A]
    exact le_add_of_nonneg_right (by positivity)
  have hAy : A≤(Y:ℝ) := by
    dsimp [A]; nlinarith only [mul_le_mul_of_nonneg_right ht hypos.le,hy]
  have hP : 0≤P := Real.sqrt_nonneg _
  have hAP : A≤P := by
    apply (Real.le_sqrt (zero_le_one.trans hA₁) (by positivity)).2
    nlinarith only [mul_le_mul_of_nonneg_right hAy (zero_le_one.trans hA₁)]
  have hYp : Real.sqrt (Y:ℝ) ≤ P := Real.sqrt_le_sqrt (by
    nlinarith only [mul_le_mul_of_nonneg_left hA₁ hypos.le])
  have hUV : ‖V-U‖≤8*A := by
    dsimp [V,U]
    rw [continuousTwistedRemainder_eq,add_sub_cancel_left]
    split_ifs
    · rw [norm_sub_rev,shortContinuousMain_eq_mellin hY1]
      exact principal_integral_sub_sum_le hY1 t
    · rw [norm_zero]; positivity
  have hUW : ‖W-V‖≤P*L := by
    have h := shortPrimeTwistedRemainder_sub_le χ hY1 t
    have hd : (1:ℝ)≤d := Nat.one_le_cast.mpr (NeZero.pos d)
    have hl : Real.log (Y:ℝ)≤L := Real.log_le_log hypos (by
      nlinarith only [mul_le_mul_of_nonneg_right hd hypos.le,hy])
    exact h.trans (mul_le_mul hYp hl (Real.log_nonneg (by linarith)) hP)
  have hV : ‖V‖ ≤ C*P*L+8*A := by
    have h := norm_add_le U (V-U)
    rw [show U+(V-U)=V by abel] at h
    exact h.trans (add_le_add (hTw Y d χ t hY ht) hUV)
  have ht' := norm_add_le V (W-V)
  rw [show V+(W-V)=W by abel] at ht'
  change ‖W‖≤(C+9)*P*L
  have hpL := mul_le_mul_of_nonneg_left hL hP
  linarith only [ht',hV,hUW,hAP,hpL]

set_option maxHeartbeats 1000000 in
/-- Once the principal term is continuous, the character error and the
nonunit primes are the only terms in the fixed numerator estimate. -/
theorem short_fixed_num_remainder_sq_of_smoothedTwist (h : SmoothedTwistEstimate) :
    ∃ C : ℝ, 0<C ∧ ∀ {r b Y q : ℕ}, 0<r → r≤Y → 2≤Y → 0<q → q≤Y → b<r →
      Nat.Coprime b r → ∀ [NeZero (r*q)] {β : ℝ}, |β|≤1/2 →
      (∑ a ∈ coprimeClasses q, ‖shortLocalRemainder r b Y a q β‖^2) ≤
        C*(q:ℝ)*(Y:ℝ)*(1+((Y:ℝ)/r)* |β|)*Real.log (2*(Y:ℝ))^2 := by
  obtain ⟨C,hC,hTw⟩ := h
  refine ⟨2*(3*(C+9))^2+2, by positivity, ?_⟩
  intro r b Y q hr hrY hY hq hqY hb hbr inst β hβ
  let d := r*q
  let H := (Y:ℝ)/r
  let L := Real.log (2*(Y:ℝ))
  let F := shortUnitDiscrepancy r q Y β
  let P := (3*(C+9))^2*(Y:ℝ)*(1+H* |β|)*L^2
  have hYp : (0:ℝ)<Y := Nat.cast_pos.mpr (by omega)
  have hY₁ : (1:ℝ)≤Y := Nat.one_le_cast.mpr (by omega)
  have hrp : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have hqp : (0:ℝ)<q := Nat.cast_pos.mpr hq
  have hdp : (0:ℝ)<d := by dsimp [d]; push_cast; positivity
  have hφ : (0:ℝ)<d.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.mul_pos hr hq))
  have ht : |β/(r:ℝ)|≤1/2 := by
    rw [abs_div,abs_of_pos hrp]
    exact (div_le_self (abs_nonneg β) (Nat.one_le_cast.mpr hr)).trans hβ
  have hlog : Real.log (2*(d:ℝ)*Y) ≤ 3*L := by
    have hprod := mul_le_mul (Nat.cast_le.mpr hrY : (r:ℝ)≤Y) (Nat.cast_le.mpr hqY : (q:ℝ)≤Y)
      hqp.le hYp.le
    have he : 2*(d:ℝ)*(Y:ℝ)≤(2*(Y:ℝ))^3 := by
      dsimp [d]; push_cast
      nlinarith only [mul_le_mul_of_nonneg_right hprod hYp.le, pow_nonneg hYp.le 3]
    have h := Real.log_le_log (by positivity : 0<2*(d:ℝ)*(Y:ℝ)) he
    rwa [Real.log_pow] at h
  have hscale : 1+|β/(r:ℝ)| *(Y:ℝ) = 1+H* |β| := by
    rw [abs_div,abs_of_pos hrp]; dsimp [H]; ring
  have hchar (χ : DirichletCharacter ℂ d) : ‖shortPrimeTwistedRemainder χ Y (β/r)‖^2≤P := by
    have hc := continuous_prime_twist_le hTw χ hY ht
    rw [hscale] at hc
    have hcoef : 0≤(C+9)*Real.sqrt ((Y:ℝ)*(1+H* |β|)) := by positivity
    have h := pow_le_pow_left₀ (norm_nonneg _) (hc.trans (mul_le_mul_of_nonneg_left hlog hcoef)) 2
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity)] at h
    exact h.trans_eq (by dsimp [P]; ring)
  have hsum : ∑ u ∈ zmodUnitsFinset d, ‖F u‖^2 ≤ P := by
    rw [mul_parseval_units (Nat.mul_pos hr hq)]
    calc _ ≤ (1/(d.totient:ℝ))*∑ _χ : DirichletCharacter ℂ d, P :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun χ _ => by
            change ‖∑ u ∈ zmodUnitsFinset (r*q), shortUnitDiscrepancy r q Y β u*χ u‖^2 ≤ P
            rw [shortUnitDiscrepancy_character hr hq]
            exact hchar χ) (by positivity)
      _ = (1/(d.totient:ℝ))*(P*∑ _χ : DirichletCharacter ℂ d, (1:ℝ)) := by
          congr 1; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => (mul_one P).symm
      _ = P := by rw [sum_one_dirichletChar d]; field_simp
  let D (a : ℕ) := ∑ u ∈ charSupp r q b, e ((a:ℝ)*((u.val/r:ℕ):ℝ)/q)*F u
  have hs (a : ℕ) : ‖shortLocalRemainder r b Y a q β‖^2 ≤ 2*‖D a‖^2+2*L^2 := by
    have h := shortLocalRemainder_le (a:=a) hr hq hqY hY hb hbr β
    change ‖shortLocalRemainder r b Y a q β‖≤‖D a‖+L at h
    nlinarith only [pow_le_pow_left₀ (norm_nonneg _) h 2,sq_nonneg (‖D a‖-L)]
  have hD : ∑ a ∈ coprimeClasses q, ‖D a‖^2 ≤ (q:ℝ)*P := by
    have hu : charSupp r q b ⊆ zmodUnitsFinset d := fun u hu =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2.1⟩
    calc _ ≤ ∑ a ∈ Finset.range q, ‖D a‖^2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _
      _ = (q:ℝ)*∑ u ∈ charSupp r q b, ‖F u‖^2 := fixed_fiber_additive_parseval hr hq hb F
      _ ≤ (q:ℝ)*∑ u ∈ zmodUnitsFinset d, ‖F u‖^2 :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hu fun _ _ _ => sq_nonneg _) hqp.le
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum hqp.le
  have hqtot : (q.totient:ℝ)≤q := Nat.cast_le.mpr (Nat.totient_le q)
  have hJ : 0≤H* |β| := by positivity
  have hp2 : (q.totient:ℝ)*L^2 ≤ (q:ℝ)*(Y:ℝ)*(1+H* |β|)*L^2 := by
    have hqY' := mul_le_mul_of_nonneg_left hY₁ hqp.le
    have hqJ := mul_le_mul_of_nonneg_left (show 1≤1+H* |β| by linarith) (show 0≤(q:ℝ)*(Y:ℝ) by positivity)
    exact mul_le_mul_of_nonneg_right (show (q.totient:ℝ)≤(q:ℝ)*(Y:ℝ)*(1+H* |β|) by
      linarith only [hqtot,hqY',hqJ]) (sq_nonneg L)
  have hf := Finset.sum_le_sum (fun a (_ : a ∈ coprimeClasses q) => hs a)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,nsmul_eq_mul,card_coprimeClasses] at hf
  dsimp only [P] at hD
  change _ ≤ (2*(3*(C+9))^2+2)*(q:ℝ)*(Y:ℝ)*(1+H* |β|)*L^2
  linarith only [hf,hD,hp2]

end FareyGoldbach
