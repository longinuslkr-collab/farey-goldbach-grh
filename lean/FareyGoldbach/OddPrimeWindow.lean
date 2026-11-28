import FareyGoldbach.ShortAveragedRemainder
import FareyGoldbach.ContinuousShortModel

/-! # The short-arc remainder for the odd primes in one residue class -/

open MeasureTheory Set
open scoped Classical

namespace FareyGoldbach

noncomputable def oddPrimeWindowWeight (r b Y j : ℕ) : ℝ :=
  if 2 < r*j+b then quarticBump ((r*j+b : ℝ)/Y) * primeWeight (r*j+b) else 0

noncomputable def oddPrimeWindowSum (r b Y : ℕ) (t : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (Y/r+1), (oddPrimeWindowWeight r b Y j : ℂ) * e (t*(j:ℝ))

theorem oddPrimeWindowWeight_nonneg (r b Y j : ℕ) : 0 ≤ oddPrimeWindowWeight r b Y j := by
  unfold oddPrimeWindowWeight
  split_ifs
  · exact mul_nonneg (quarticBump_nonneg _) (primeWeight_nonneg _)
  · exact le_rfl

theorem oddPrimeWindowWeight_prime_odd {r b Y j : ℕ} (h : 0 < oddPrimeWindowWeight r b Y j) :
    (r*j+b).Prime ∧ Odd (r*j+b) := by
  by_cases h₂ : 2<r*j+b
  · have hp : (r*j+b).Prime := by
      by_contra hn
      simp [oddPrimeWindowWeight,h₂,primeWeight,hn] at h
    exact ⟨hp,hp.odd_iff.mpr (by omega)⟩
  · simp [oddPrimeWindowWeight,h₂] at h

theorem continuous_oddPrimeWindowSum (r b Y : ℕ) : Continuous (oddPrimeWindowSum r b Y) := by
  unfold oddPrimeWindowSum
  exact continuous_sum_finset _ fun j _ => continuous_const.mul
    (continuous_e_real.comp (continuous_id.mul_const _))

/-- At most one coefficient is changed, and its absolute weight is at most `log 2`. -/
theorem oddPrimeWindowSum_sub_le_one {r : ℕ} (hr : 0<r) (b Y : ℕ) (t : ℝ) :
    ‖oddPrimeWindowSum r b Y t - smoothedPrimeSum r b Y t‖ ≤ 1 := by
  let I := Finset.range (Y/r+1)
  let J := I.filter (fun j => r*j+b=2)
  have hcard : J.card ≤ 1 := Finset.card_le_one.mpr (fun j hj k hk =>
    Nat.eq_of_mul_eq_mul_left hr (by
      have hj' := (Finset.mem_filter.mp hj).2
      have hk' := (Finset.mem_filter.mp hk).2
      omega))
  unfold oddPrimeWindowSum smoothedPrimeSum
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ j ∈ I, if r*j+b=2 then (1:ℝ) else 0 := by
        refine Finset.sum_le_sum fun j _ => ?_
        by_cases h₂ : r*j+b=2
        · have hle : ¬2<r*j+b := by omega
          rw [oddPrimeWindowWeight,ite_eq_right hle]
          simp only [h₂,ite_true,Complex.ofReal_zero,
            zero_mul,zero_sub,norm_neg,norm_mul,norm_e,mul_one,Complex.norm_real]
          rw [Real.norm_of_nonneg (quarticBump_nonneg _), Real.norm_of_nonneg (primeWeight_nonneg _)]
          have hw := quarticBump_le_one (((r:ℝ)*(j:ℝ)+b)/Y)
          have hp : primeWeight 2≤1 := by
            rw [primeWeight,ite_eq_left Nat.prime_two]
            have h := Real.log_two_lt_d9
            exact h.le.trans (by norm_num)
          exact (mul_le_mul hw hp (primeWeight_nonneg 2) zero_le_one).trans_eq (one_mul _)
        · by_cases h₃ : 2<r*j+b
          · simp [h₂,oddPrimeWindowWeight,h₃]
          · have hp : ¬(r*j+b).Prime := fun h => h₂ (by have := h.two_le; omega)
            simp [h₂,oddPrimeWindowWeight,h₃,primeWeight,hp]
      _ = (J.card:ℝ) := by simp [J]
      _ ≤ 1 := Nat.cast_le.mpr hcard

private theorem shortLocalMain_qOne {r b Y : ℕ} (hr : 0<r) (hY : 1≤Y)
    (hb : b<r) (hbr : Nat.Coprime b r) [NeZero (r*1)] (t : ℝ) :
    shortLocalMain r b Y 0 1 t = (((r:ℝ)/r.totient : ℝ):ℂ)*shortContKernel r b Y t := by
  have he := charCoeff_one_coprime hr (by decide : 0<(1:ℕ)) hb
    (by decide : Nat.Coprime 0 1) hbr (Nat.coprime_one_left r)
  unfold shortLocalMain shortContKernel
  rw [he,shortContinuousMain_eq_mellin hY]
  have hr' : (r:ℂ)≠0 := Nat.cast_ne_zero.mpr hr.ne'
  have hp : (r.totient:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hr).ne'
  simp only [Nat.cast_zero,zero_mul,zero_div,neg_zero,e_zero,ArithmeticFunction.moebius_apply_one,
    Int.cast_one,Nat.totient_one,Nat.cast_one,mul_one,one_div,Complex.ofReal_div,Complex.ofReal_natCast]
  field_simp

private theorem oddPrimeWindow_remainder_l2_of_input {C : ℝ} (hC : 0<C)
    (ht : ∀ (Y d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (ξ : ℝ),
      2≤Y → 1/(Y:ℝ)≤ξ → ξ≤1/2 → (∫ t in -ξ..ξ, ‖shortPrimeTwistedRemainder χ Y t‖^2) ≤
        C*(Y:ℝ)*ξ*Real.log (2*(d:ℝ)*Y)^2)
    {r b Y : ℕ} (hr : 0<r) (hrY : r≤Y) (hY : 2≤Y) (hb : b<r) (hbr : Nat.Coprime b r)
    {η : ℝ} (hη : (r:ℝ)/Y≤η) (hη₂ : η≤1/2) :
    (∫ t in -η..η, ‖oddPrimeWindowSum r b Y t - (((r:ℝ)/r.totient:ℝ):ℂ)*shortContKernel r b Y t‖^2) ≤
      (36*C+12)*(Y:ℝ)*η*Real.log (2*(Y:ℝ))^2 := by
  let _ : NeZero (r*1) := ⟨by simpa using hr.ne'⟩
  let M := fun t => (((r:ℝ)/r.totient:ℝ):ℂ)*shortContKernel r b Y t
  let S := smoothedPrimeSum r b Y
  let O := oddPrimeWindowSum r b Y
  let R (j : ℕ) := shortLocalRemainder r j Y 0 1
  let L := Real.log (2*(Y:ℝ))
  let p := (r.totient:ℝ)
  have hp : 0<p := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hη₀ : 0≤η := (by positivity : 0≤(r:ℝ)/Y).trans hη
  have hab : -η≤η := by linarith only [hη₀]
  have hR (t : ℝ) : R b t = S t-M t := by
    dsimp [R,shortLocalRemainder]
    rw [shortLocalMain_qOne hr (by omega) hb hbr]
    simp [S,M]
  have hcR (j : ℕ) : Continuous (R j) := continuous_shortLocalRemainder r j Y 0 1
  let F (t : ℝ) := ∑ j ∈ coprimeClasses r, ‖R j t‖^2
  have hcF : Continuous F := continuous_sum_finset (coprimeClasses r) fun j _ => (hcR j).norm.pow 2
  have hmean := shortLocalRemainder_avg_interval_bound hC ht (a:=0) hr (by decide : 0<1) hrY
    (by omega : 1≤Y) hY hη hη₂
  change (∫ t in -η..η, (1/p)*F t) ≤ (18*C+4)*(1*(Y:ℝ)/p)*η*L^2 at hmean
  rw [intervalIntegral.integral_const_mul] at hmean
  have hsum : (∫ t in -η..η, F t) ≤ (18*C+4)*(Y:ℝ)*η*L^2 := by
    have hm := mul_le_mul_of_nonneg_left hmean hp.le
    convert hm using 1 <;> field_simp
  have hsingle : (∫ t in -η..η, ‖R b t‖^2) ≤ (18*C+4)*(Y:ℝ)*η*L^2 :=
    (intervalIntegral.integral_mono_on hab ((hcR b).norm.pow 2 |>.intervalIntegrable _ _)
      (hcF.intervalIntegrable _ _) (fun t _ => Finset.single_le_sum (fun j _ => sq_nonneg ‖R j t‖)
        (mem_coprimeClasses.mpr ⟨hb,hbr⟩))).trans hsum
  have hcM : Continuous M := continuous_const.mul (continuous_shortContKernel (by omega : 1≤Y) r b)
  have hcO : Continuous O := continuous_oddPrimeWindowSum ..
  have hpt (t : ℝ) : ‖O t-M t‖^2≤2*‖R b t‖^2+2 := by
    have h := norm_add_le (O t-S t) (S t-M t)
    rw [show O t-S t+(S t-M t)=O t-M t by abel,←hR] at h
    have hh := h.trans (add_le_add (oddPrimeWindowSum_sub_le_one hr b Y t) le_rfl)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hh 2
    nlinarith only [hsq,sq_nonneg (‖R b t‖-1)]
  have hfi : IntervalIntegrable (fun t => 2*‖R b t‖^2) volume (-η) η :=
    (((hcR b).norm.pow 2).intervalIntegrable _ _).const_mul 2
  have htwo : IntervalIntegrable (fun _ : ℝ => (2:ℝ)) volume (-η) η := continuous_const.intervalIntegrable _ _
  have ha : (∫ t in -η..η, ‖O t-M t‖^2) ≤ ∫ t in -η..η, 2*‖R b t‖^2+2 :=
    intervalIntegral.integral_mono_on hab ((hcO.sub hcM).norm.pow 2 |>.intervalIntegrable _ _)
      (hfi.add htwo) (fun t _ => hpt t)
  rw [intervalIntegral.integral_add hfi htwo,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const,smul_eq_mul] at ha
  have hl : 1≤L := one_le_log_two_mul hY
  have hy : (1:ℝ)≤Y := Nat.one_le_cast.mpr (by omega)
  have hW : (1:ℝ)≤(Y:ℝ)*L^2 := by
    have hL := pow_le_pow_left₀ zero_le_one hl 2
    have h := mul_le_mul hy hL (by norm_num : (0:ℝ)≤1^2) (by positivity : 0≤(Y:ℝ))
    simpa using h
  have hlast := mul_le_mul_of_nonneg_right hW hη₀
  change (∫ t in -η..η, ‖O t-M t‖^2) ≤ (36*C+12)*(Y:ℝ)*η*L^2
  linarith only [ha,hsingle,hlast]

theorem oddPrimeWindow_remainder_l2 (h : LocalTwistedMeanSquare) :
    ∃ C : ℝ, 0<C ∧ ∀ {r b Y : ℕ}, 0<r → r≤Y → 2≤Y → b<r → Nat.Coprime b r →
      ∀ {η : ℝ}, (r:ℝ)/Y≤η → η≤1/2 →
      (∫ t in -η..η, ‖oddPrimeWindowSum r b Y t - (((r:ℝ)/r.totient:ℝ):ℂ)*shortContKernel r b Y t‖^2) ≤
        C*(Y:ℝ)*η*Real.log (2*(Y:ℝ))^2 := by
  obtain ⟨C,hC,ht⟩ := shortPrimeTwistedMeanSquare h
  exact ⟨36*C+12,by positivity,oddPrimeWindow_remainder_l2_of_input hC ht⟩

end FareyGoldbach
