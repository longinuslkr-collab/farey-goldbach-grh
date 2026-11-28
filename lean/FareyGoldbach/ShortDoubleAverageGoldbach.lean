import FareyGoldbach.ShortIntervalExceptions
import FareyGoldbach.LocalizedProductBessel
import FareyGoldbach.ShortModelL2
import FareyGoldbach.ShortResidualArcMass

/-! # Double-averaged exceptions in a translated interval

Bad frequencies share one window of width ⌊Δ/r⌋+3. The product Bessel
estimate controls that window from the local mean square of the residual
and the global energies of the prime sum and the continuous Farey model. -/

open MeasureTheory Filter
open scoped BigOperators Classical Topology

namespace FareyGoldbach

noncomputable def shortPrimeFunction (r b Y : ℕ) : BoundedPeriodicFunction where
  toFun := smoothedPrimeSum r b Y
  measurable := (continuous_smoothedPrimeSum r b Y).measurable
  bounded := by
    refine ⟨∑ j ∈ Finset.range (Y/r+1),
      |quarticBump ((r*j+b:ℝ)/Y)*primeWeight (r*j+b)|,fun x => ?_⟩
    unfold smoothedPrimeSum
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => by
      rw [norm_mul,norm_e,mul_one,Complex.norm_real,Real.norm_eq_abs]))
  periodic := by
    intro t
    unfold smoothedPrimeSum
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    apply e_eq_of_sub_int (k := (j : ℤ))
    push_cast
    ring

def shortDifference (s m : BoundedPeriodicFunction) : BoundedPeriodicFunction where
  toFun := fun x => s x - m x
  measurable := s.measurable.sub m.measurable
  bounded := by
    obtain ⟨A,hA⟩ := s.bounded
    obtain ⟨B,hB⟩ := m.bounded
    exact ⟨A+B,fun x => (norm_sub_le _ _).trans (add_le_add (hA x) (hB x))⟩
  periodic := s.periodic.sub m.periodic

noncomputable def shortPC (u v : BoundedPeriodicFunction) (k : ℕ) :=
  shortFourierCoeff (fun x => u x*v x) k

private lemma shortPC_int (u v : BoundedPeriodicFunction) (k : ℕ) :
    IntervalIntegrable (fun x : ℝ => (u x*v x)*e (-((k:ℝ)*x))) volume 0 1 := by
  obtain ⟨A,hA⟩ := u.bounded
  obtain ⟨B,hB⟩ := v.bounded
  have he : Measurable (fun x : ℝ => e (-((k:ℝ)*x))) := by
    simpa only [neg_mul] using (continuous_e_mul (-(k:ℝ))).measurable
  apply intervalIntegrable_of_measurable_bounded (B:=A*B) ((u.measurable.mul v.measurable).mul he)
  intro x
  change ‖u x*v x*e (-((k:ℝ)*x))‖ ≤ _
  rw [norm_mul,norm_e,mul_one,norm_mul]
  exact mul_le_mul (hA _) (hB _) (norm_nonneg _) ((norm_nonneg _).trans (hA 0))

private lemma shortPC_split (s₁ s₂ m₁ m₂ : BoundedPeriodicFunction) (k : ℕ) :
    shortPC s₁ s₂ k - shortPC m₁ m₂ k =
      shortPC (shortDifference s₂ m₂) s₁ k + shortPC (shortDifference s₁ m₁) m₂ k := by
  unfold shortPC shortFourierCoeff
  rw [← intervalIntegral.integral_sub (shortPC_int s₁ s₂ k) (shortPC_int m₁ m₂ k),
    ← intervalIntegral.integral_add (shortPC_int (shortDifference s₂ m₂) s₁ k)
      (shortPC_int (shortDifference s₁ m₁) m₂ k)]
  apply intervalIntegral.integral_congr
  intro x _
  change _ = ((s₂ x-m₂ x)*s₁ x)*_ + ((s₁ x-m₁ x)*m₂ x)*_
  ring

lemma shortCountPair (P : Progressions) {X Δ : ℕ} (hrX : P.r ≤ X)
    (_hΔ : Δ ≤ X) (M₁ M₂ : BoundedPeriodicFunction) {T : ℝ} (hT : 0 ≤ T)
    (hmodel : ∀ k ∈ shortBadFrequencies P X Δ, T ≤ (shortPC M₁ M₂ k).re) :
    let S₁ := shortPrimeFunction P.r P.b₁ (X+Δ)
    let S₂ := shortPrimeFunction P.r P.b₂ (X+Δ)
    let m := X/P.r-2
    let K := Δ/P.r+3
    ((shortIntervalExceptions P X Δ).card : ℝ)*T^2 ≤
      2*(productWindowEnergy (shortDifference S₂ M₂) S₁ m K +
         productWindowEnergy (shortDifference S₁ M₁) M₂ m K) := by
  intro S₁ S₂ m K
  let eq₁ := fun k => ‖shortPC (shortDifference S₂ M₂) S₁ k‖^2
  let eq₂ := fun k => ‖shortPC (shortDifference S₁ M₁) M₂ k‖^2
  let s := shortBadFrequencies P X Δ
  let w := Finset.Icc m (m+K)
  have hsub : s ⊆ w := shortBadFrequencies_subset_window P hrX
  have hpt (k : ℕ) (hk : k ∈ s) : T^2 ≤ 2*(eq₁ k+eq₂ k) := by
    have hl := (hmodel k hk).trans (Complex.re_le_norm _)
    obtain ⟨n,hn,hnk⟩ := Finset.mem_image.mp hk
    have hr := shortBadFrequencies_recover P hrX hn
    rw [hnk] at hr
    have hbad := (shortIntervalExceptions_mem hn).2.2.2.2
    rw [← hr] at hbad
    have hkY : k ≤ (X+Δ)/P.r := (Nat.le_div_iff_mul_le P.r_pos).2 (by
      have hh := (shortIntervalExceptions_mem hn).2.1
      nlinarith only [hr,hh])
    have hz : shortPC S₁ S₂ k = 0 := primeConvolution_eq_zero_of_exception P hkY hbad
    have he := shortPC_split S₁ S₂ M₁ M₂ k
    rw [hz,zero_sub] at he
    have hnorm := congrArg norm he
    rw [norm_neg] at hnorm
    have ht := hl.trans (hnorm.le.trans (norm_add_le _ _))
    exact (pow_le_pow_left₀ hT ht 2).trans (by dsimp [eq₁,eq₂]; nlinarith only [sq_nonneg (‖shortPC (shortDifference S₂ M₂) S₁ k‖-‖shortPC (shortDifference S₁ M₁) M₂ k‖)])
  rw [← shortBadFrequencies_card P hrX]
  calc _ = ∑ _k ∈ s, T^2 := by simp [s]
       _ ≤ ∑ k ∈ s, 2*(eq₁ k+eq₂ k) := Finset.sum_le_sum hpt
       _ ≤ ∑ k ∈ w, 2*(eq₁ k+eq₂ k) := Finset.sum_le_sum_of_subset_of_nonneg hsub
         (fun k _ _ => by dsimp [eq₁,eq₂]; positivity)
       _ = _ := by rw [← Finset.mul_sum,Finset.sum_add_distrib]; rfl

set_option maxHeartbeats 900000 in
private lemma shortAverageFromEnergies {r X Δ : ℕ} (hr : 0 < r) (hrX : r ≤ X) (hΔ : Δ ≤ X)
    (M : ℕ → BoundedPeriodicFunction) {T A B D : ℝ} (hT : 0 ≤ T)
    (hmodel : ∀ (b c : {b // b ∈ coprimeClasses r}) k,
      k ∈ shortBadFrequencies (shortProgressions hr b c) X Δ → T ≤ (shortPC (M b.1) (M c.1) k).re)
    (hlocal : ∀ x : ℝ,
      (∑ b ∈ coprimeClasses r, localizedArcMass
        (shortDifference (shortPrimeFunction r b (X+Δ)) (M b)) (Δ/r+3) x)/(r.totient:ℝ) ≤ A)
    (hprime : (∑ b ∈ coprimeClasses r, ∫ x in (0:ℝ)..1, ‖smoothedPrimeSum r b (X+Δ) x‖^2)/(r.totient:ℝ) ≤ B)
    (hmod : (∑ b ∈ coprimeClasses r, ∫ x in (0:ℝ)..1, ‖M b x‖^2)/(r.totient:ℝ) ≤ D) :
    shortDoubleAvgExceptions X Δ r hr*T^2 ≤ 64*(Δ/r+3:ℕ)*A*(B+D) := by
  let s := coprimeClasses r
  let S := fun b => shortPrimeFunction r b (X+Δ)
  let R := fun b => shortDifference (S b) (M b)
  let m := X/r-2
  let K := Δ/r+3
  have hs : s.Nonempty := Finset.card_pos.mp (by dsimp [s]; rw [card_coprimeClasses]; exact Nat.totient_pos.mpr hr)
  have hc : (s.card:ℝ) = r.totient := by dsimp [s]; rw [card_coprimeClasses]
  have ht : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hk : 0 < K := Nat.zero_lt_succ _
  have hL (x : ℝ) : (∑ i ∈ s, localizedArcMass (R i) K x)/(s.card:ℝ) ≤ A := by
    rw [hc]; exact hlocal x
  have hposA : 0 ≤ A := by
    apply le_trans _ (hL 0)
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    have hrad : 0 ≤ 1/(K:ℝ) := by positivity
    exact fun _ _ => intervalIntegral.integral_nonneg (by linarith : (0:ℝ)-1/(K:ℝ) ≤ 0+1/(K:ℝ)) (fun _ _ => sq_nonneg _)
  have hfac : 0 ≤ 32*(K:ℝ)*A := by positivity
  let E (V : ℕ → BoundedPeriodicFunction) := ∑ i ∈ s, ∑ j ∈ s, productWindowEnergy (R i) (V j) m K
  have hE (V : ℕ → BoundedPeriodicFunction) {Z : ℝ}
      (hV : (∑ j ∈ s, ∫ x in (0:ℝ)..1, ‖V j x‖^2)/(r.totient:ℝ) ≤ Z) :
      E V / (r.totient:ℝ)^2 ≤ 32*(K:ℝ)*A*Z := by
    have h := averaged_localized_product_bessel s s hs hs R V m K hk hL
    rw [hc,← sq] at h
    exact h.trans (mul_le_mul_of_nonneg_left hV hfac)
  have hsum : ((∑ b ∈ s.attach, ∑ c ∈ s.attach,
      ((shortIntervalExceptions (shortProgressions hr b c) X Δ).card:ℝ))*T^2) ≤ 2*(E S+E M) := by
    rw [Finset.sum_mul]
    calc _ ≤ ∑ b ∈ s.attach, ∑ c ∈ s.attach,
          2*(productWindowEnergy (R c.1) (S b.1) m K + productWindowEnergy (R b.1) (M c.1) m K) := by
             refine Finset.sum_le_sum fun b _ => ?_
             rw [Finset.sum_mul]
             exact Finset.sum_le_sum fun c _ => shortCountPair (shortProgressions hr b c) hrX hΔ
               (M b.1) (M c.1) hT (hmodel b c)
         _ = _ := by
           rw [Finset.sum_attach s (fun b => ∑ c ∈ s.attach,
             2*(productWindowEnergy (R c.1) (S b) m K + productWindowEnergy (R b) (M c.1) m K))]
           have heq (b : ℕ) := Finset.sum_attach s (fun c => 2*(productWindowEnergy (R c) (S b) m K + productWindowEnergy (R b) (M c) m K))
           simp_rw [heq,← Finset.mul_sum,Finset.sum_add_distrib]
           dsimp only [E]
           have hswap := Finset.sum_comm (s:=s) (t:=s) (f:=fun b c => productWindowEnergy (R c) (S b) m K)
           rw [hswap]
  change ((1/(r.totient:ℝ)^2)*_)*T^2 ≤ _
  have hcount := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 1/(r.totient:ℝ)^2)
  calc _ ≤ (1/(r.totient:ℝ)^2)*(2*(E S+E M)) := by rw [mul_assoc]; exact hcount
       _ = 2*(E S/(r.totient:ℝ)^2 + E M/(r.totient:ℝ)^2) := by ring
       _ ≤ 2*(32*(K:ℝ)*A*B+32*(K:ℝ)*A*D) :=
           mul_le_mul_of_nonneg_left (add_le_add (hE S hprime) (hE M hmod)) (by norm_num)
       _ = _ := by change _ = 64*(K:ℝ)*A*(B+D); ring

set_option maxHeartbeats 1500000 in
private theorem short_assemble
    (model : ∀ _r _b Y _Q : ℕ, 1 ≤ Y → BoundedPeriodicFunction)
    (hmodel : ∀ (r b Y Q : ℕ) (hY : 1 ≤ Y), (model r b Y Q hY).toFun = shortContModel r b Y Q)
    (hmain : ∀ {r b₁ b₂ Y k Q : ℕ}, 0 < r → b₁ < r → b₂ < r →
      Y/2 < r*k+b₁+b₂ → r*k+b₁+b₂ ≤ Y → Even (r*k+b₁+b₂) → 2 ≤ Q →
      (2:ℝ)^24*(Q:ℝ)^2 ≤ (Y:ℝ)/r →
      (1:ℝ)/262144*((r:ℝ)/r.totient)^2*((Y:ℝ)/r) ≤
        (shortFourierCoeff (fun x => shortContModel r b₁ Y Q x*shortContModel r b₂ Y Q x) k).re)
    (hmodelL2 : ∀ {r b Y Q : ℕ}, 0 < r → r ≤ Y → Q ≤ Y → 2^72 ≤ Y →
      (∫ x in (0:ℝ)..1, ‖shortContModel r b Y Q x‖^2) ≤
        360*((r:ℝ)/r.totient)*((Y:ℝ)/r)*Real.log (2*(Y:ℝ)))
    (hres : ∃ C : ℝ, 0 < C ∧ ∀ {r Y Q K : ℕ}, 0 < r → r ≤ Y → 2 ≤ Y → 3 ≤ Q →
      Q^2 ≤ K → Q^2 ≤ Y/r → ∀ x : ℝ,
      (∫ α in x-1/(K:ℝ)..x+1/(K:ℝ), (1/(r.totient:ℝ)) * ∑ b ∈ coprimeClasses r,
        ‖smoothedPrimeSum r b Y α-shortContModel r b Y Q α‖^2) ≤
        C*(Y:ℝ)/((r.totient:ℝ)*Q)*Real.log (2*(Y:ℝ))^2) : ShortDoubleAvgBound := by
  obtain ⟨C,hC,hl⟩ := hres
  let J : ℝ := 64*362*262144^2
  have hJ : 0 < J := by norm_num [J]
  apply shortDoubleAvgBound_of_large_cap (2^72)
  refine ⟨J*C*(2:ℝ)^16*8,by positivity,?_⟩
  intro X Δ r hr hX hrX hΔ hΔX hbig
  let Y := X+Δ
  let K := Δ/r+3
  let Q := routeAQ Δ r
  let k := (Δ:ℝ)/r
  let H := (Y:ℝ)/r
  let κ := (r:ℝ)/r.totient
  let a := (r.totient:ℝ)/r
  let L := Real.log (2*(Y:ℝ))
  let L₀ := Real.log (2*(X:ℝ))
  let thresh := (1:ℝ)/262144*κ^2*H
  have hΔY : Δ ≤ Y := by dsimp [Y]; omega
  have hXY : X ≤ Y := by dsimp [Y]; omega
  have hY2 : 2 ≤ Y := hX.trans hXY
  have hY72 : 2^72 ≤ Y := hbig.trans ((Nat.div_le_self _ _).trans hΔY)
  have hrY : r ≤ Y := hrX.trans hXY
  have hrp : (0:ℝ) < r := Nat.cast_pos.mpr hr
  have ht : (0:ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hYp : (0:ℝ)<Y := Nat.cast_pos.mpr (by omega)
  have hHp : 0 < H := div_pos hYp hrp
  have hκp : 0 < κ := div_pos hrp ht
  have ha : 0 < a := div_pos ht hrp
  have hT : 0 < thresh := by dsimp only [thresh]; positivity
  have hk0 : 0 < k := div_pos (Nat.cast_pos.mpr hΔ) hrp
  have hfloor : ((Δ/r:ℕ):ℝ) ≤ k := (le_div_iff₀ hrp).2 (by exact_mod_cast (Nat.div_mul_le_self Δ r))
  have hk1 : 1 ≤ k := by
    have h1 : (1:ℝ) ≤ (Δ/r:ℕ) := by exact_mod_cast (show 1 ≤ Δ/r from le_trans (by norm_num) hbig)
    exact h1.trans hfloor
  have hK4 : (K:ℝ) ≤ 4*k := by dsimp only [K]; push_cast; linarith
  have hKn : 0 < K := Nat.zero_lt_succ _
  obtain ⟨hQ2,hQlo,hQhi,hQΔ⟩ := routeAQ_bounds hr (le_trans (by norm_num : 2^26 ≤ 2^72) hbig)
  have hQ3 : 3 ≤ Q := by
    dsimp [Q,routeAQ]
    apply (Nat.le_div_iff_mul_le (by norm_num : 0<2^12)).2
    rw [Nat.le_sqrt]
    exact le_trans (by norm_num) hbig
  have hQp : (0:ℝ)<Q := Nat.cast_pos.mpr (by omega)
  have hqSq : Q^2 ≤ Δ/r := by
    have h : Q ≤ Nat.sqrt (Δ/r) := Nat.div_le_self _ _
    simpa only [sq] using (Nat.pow_le_pow_left h 2).trans (by simpa only [sq] using Nat.sqrt_le (Δ/r))
  have hQK : Q^2 ≤ K := hqSq.trans (Nat.le_add_right _ _)
  have hQY : Q^2 ≤ Y/r := hqSq.trans (Nat.div_le_div_right hΔY)
  have hHk : k ≤ H := div_le_div_of_nonneg_right (Nat.cast_le.mpr hΔY) hrp.le
  have hsmall : (2:ℝ)^24*(Q:ℝ)^2 ≤ H := by
    change (Q:ℝ) ≤ (1/(2:ℝ)^12)*Real.sqrt k at hQhi
    have hs := pow_le_pow_left₀ (Nat.cast_nonneg Q) hQhi 2
    rw [mul_pow,Real.sq_sqrt hk0.le] at hs
    norm_num at hs ⊢
    linarith
  have hroot : 0 ≤ Real.sqrt k := Real.sqrt_nonneg _
  have hratio : (K:ℝ)/(Q:ℝ) ≤ (2:ℝ)^16*Real.sqrt k := by
    change 1/(2:ℝ)^14*Real.sqrt k ≤ (Q:ℝ) at hQlo
    apply (div_le_iff₀ hQp).2
    have hq := mul_le_mul_of_nonneg_right hQlo hroot
    nlinarith only [hq,Real.sq_sqrt hk0.le,hK4]
  have hL₀ : 0 < L₀ := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (one_le_log_two_mul hX)
  have hL : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (one_le_log_two_mul hY2)
  have hlogs : L^3 ≤ 8*L₀^3 := by
    have hy : (Y:ℝ) ≤ 2*(X:ℝ) := by exact_mod_cast (show Y≤2*X by dsimp [Y]; omega)
    have h2x : (1:ℝ) ≤ X := by exact_mod_cast (show 1≤X by omega)
    have h := Real.log_le_log (by positivity : 0<2*(Y:ℝ)) (show 2*(Y:ℝ)≤(2*(X:ℝ))^2 by nlinarith [mul_le_mul_of_nonneg_right h2x (Nat.cast_nonneg (α:=ℝ) X)])
    rw [Real.log_pow] at h
    have h' : L≤2*L₀ := by simpa only [L,L₀,Nat.cast_ofNat] using h
    have hh := pow_le_pow_left₀ hL.le h' 3
    linarith only [hh]
  let M := fun b => model r b Y Q (by omega)
  let A := C*(Y:ℝ)/((r.totient:ℝ)*Q)*L^2
  have hML (b : ℕ) : (M b).toFun = shortContModel r b Y Q := hmodel r b Y Q _
  have hm (b c : {b // b ∈ coprimeClasses r}) (j : ℕ) (hj : j ∈ shortBadFrequencies (shortProgressions hr b c) X Δ) :
      thresh ≤ (shortPC (M b.1) (M c.1) j).re := by
    obtain ⟨n,hn,hj'⟩ := Finset.mem_image.mp hj
    have hrec := shortBadFrequencies_recover (shortProgressions hr b c) hrX hn
    rw [hj'] at hrec
    change r*j+b.1+c.1=n at hrec
    obtain ⟨hlo,hhi,hev,_,_⟩ := shortIntervalExceptions_mem hn
    have hy : Y/2 < n := by dsimp [Y]; omega
    have h := hmain hr (mem_coprimeClasses.mp b.2).1 (mem_coprimeClasses.mp c.2).1
      (hrec ▸ hy) (hrec ▸ hhi) (hrec ▸ hev) hQ2 hsmall
    change _ ≤ (shortFourierCoeff (fun x => (M b.1).toFun x*(M c.1).toFun x) j).re
    rw [hML,hML]; exact h
  have hlocal (x : ℝ) :
      (∑ b ∈ coprimeClasses r, localizedArcMass (shortDifference (shortPrimeFunction r b (X+Δ)) (M b)) K x)/(r.totient:ℝ) ≤ A := by
    have hinter (b : ℕ) : IntervalIntegrable (fun α => ‖smoothedPrimeSum r b Y α - (M b) α‖^2) volume
        (x-1/(K:ℝ)) (x+1/(K:ℝ)) := by
      let R := shortDifference (shortPrimeFunction r b Y) (M b)
      obtain ⟨T,hT'⟩ := R.bounded
      apply intervalIntegrable_of_measurable_bounded (B:=T^2) (R.measurable.norm.pow_const 2)
      exact fun t => by change ‖‖R t‖^2‖ ≤ T^2; rw [Real.norm_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (norm_nonneg _) (hT' t) 2
    have h := hl hr hrY hY2 hQ3 hQK hQY x
    change (∑ b ∈ coprimeClasses r, ∫ α in x-1/(K:ℝ)..x+1/(K:ℝ), ‖smoothedPrimeSum r b Y α - (M b) α‖^2)/(r.totient:ℝ) ≤ A
    rw [← intervalIntegral_finset_sum (fun b _ => hinter b),div_eq_inv_mul,← one_div,← intervalIntegral.integral_const_mul]
    simpa only [hML] using h
  have hp : (∑ b ∈ coprimeClasses r, ∫ x in (0:ℝ)..1, ‖smoothedPrimeSum r b (X+Δ) x‖^2)/(r.totient:ℝ) ≤ 2*κ*H*L := by
    rw [div_eq_inv_mul,← one_div]
    exact avg_smoothedPrimeSum_l2_le hr hrY hY2
  have hmo : (∑ b ∈ coprimeClasses r, ∫ x in (0:ℝ)..1, ‖(M b) x‖^2)/(r.totient:ℝ) ≤ 360*κ*H*L := by
    apply (div_le_iff₀ ht).2
    calc _ ≤ ∑ _b ∈ coprimeClasses r, 360*κ*H*L := by
           refine Finset.sum_le_sum fun b _ => ?_
           change (∫ α in (0:ℝ)..1, ‖(M b).toFun α‖^2) ≤ _
           rw [hML]; exact hmodelL2 hr hrY (hQΔ.trans hΔY) hY72
         _ = _ := by rw [Finset.sum_const,nsmul_eq_mul,card_coprimeClasses,mul_comm]
  have hE := shortAverageFromEnergies hr hrX hΔX M hT.le hm hlocal hp hmo
  have hE' : shortDoubleAvgExceptions X Δ r hr ≤ J*C*a^2*((K:ℝ)/Q)*L^3 := by
    apply le_of_mul_le_mul_right _ (pow_pos hT 2)
    refine hE.trans_eq ?_
    change 64*(K:ℝ)*(C*(Y:ℝ)/((r.totient:ℝ)*Q)*L^2)*(2*κ*H*L+360*κ*H*L) = _
    dsimp only [J,a,κ,H,thresh]
    field_simp
    ring
  have ht1 := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ J*C*a^2)
  have ht2 := mul_le_mul ht1 hlogs (by positivity) (by positivity)
  change _ ≤ J*C*(2:ℝ)^16*8*(a^2*Real.sqrt k*L₀^3)
  exact hE'.trans (ht2.trans_eq (by ring))

/-- Mean square for the continuous twisted Dirichlet remainder implies the
double-averaged Goldbach exceptional-set estimate on every translated window. -/
theorem short_double_average_of_localTwistedMeanSquare (h : LocalTwistedMeanSquare) :
    ShortDoubleAvgBound := by
  let M (r b Y Q : ℕ) (hY : 1 ≤ Y) : BoundedPeriodicFunction :=
    ⟨shortContModel r b Y Q, shortContModel_measurable hY r b Q,
      shortContModel_norm_bounded hY r b Q, shortContModel_periodic r b Y Q⟩
  exact short_assemble M (fun _ _ _ _ _ => rfl)
    (fun hr hb hc hlo hhi hev hQ hsmall => shortContModel_conv_re_lower hr hb hc hlo hhi hev hQ hsmall)
    (fun hr hrY hQY hY => shortContModel_l2_le hr hrY hQY hY)
    (shortResidual_average_local_of_meanSquare h)

/-- The clean length-over-modulus cap holds uniformly for windows of length at
least one modulus. -/
theorem short_double_average_long_window_of_localTwistedMeanSquare (h : LocalTwistedMeanSquare) :
    ∃ C : ℝ, 0<C ∧ ∀ {X Δ r : ℕ} (hr : 0<r), 2≤X → r≤Δ → Δ≤X →
      shortDoubleAvgExceptions X Δ r hr ≤ C*min ((Δ:ℝ)/r) (shortDoubleAvgAnalyticCap X Δ r) :=
  shortDoubleAvgBound_long_window (short_double_average_of_localTwistedMeanSquare h)

/-- Along any sequence with diverging short-window parameter, the exceptional
count per period tends to zero. -/
theorem short_double_average_density_one_of_localTwistedMeanSquare (h : LocalTwistedMeanSquare)
    (X Δ r : ℕ→ℕ) (hr : ∀ n,0<r n) (hX : ∀ n,2≤X n) (hrX : ∀ n,r n≤X n)
    (hΔ : ∀ n,1≤Δ n) (hΔX : ∀ n,Δ n≤X n)
    (hP : Tendsto (fun n => shortDoubleAvgParameter (X n) (Δ n) (r n)) atTop atTop) :
    Tendsto (fun n => shortDoubleAvgExceptions (X n) (Δ n) (r n) (hr n) / ((Δ n:ℝ)/r n)) atTop (𝓝 0) :=
  shortDoubleAvgDensity_of_bound (short_double_average_of_localTwistedMeanSquare h) X Δ r hr hX hrX hΔ hΔX hP

end FareyGoldbach
