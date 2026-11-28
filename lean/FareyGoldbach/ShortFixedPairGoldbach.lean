import FareyGoldbach.LocalTwistedMeanSquareOfGRH
import FareyGoldbach.SingleAverageCore
import FareyGoldbach.SingleAverageAssembly
import FareyGoldbach.ShortProductWindow
import FareyGoldbach.ShortFixedResidualArcMass

/-! # Exceptional sets for two fixed reduced residue classes in a translated interval -/

open MeasureTheory Filter
open scoped BigOperators Classical Topology

namespace FareyGoldbach

/-- The analytic term loses one totient relative to the double average. -/
noncomputable def shortFixedPairAnalyticCap (X Δ r : ℕ) : ℝ :=
  (r.totient : ℝ) * shortDoubleAvgAnalyticCap X Δ r

/-- The endpoint correction covers windows shorter than their modulus. -/
noncomputable def shortFixedPairBudget (X Δ r : ℕ) : ℝ :=
  min ((Δ : ℝ)/r + 1) (shortFixedPairAnalyticCap X Δ r)

def ShortFixedPairBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (P : Progressions) {X Δ : ℕ},
    2 ≤ X → P.r ≤ X → 1 ≤ Δ → Δ ≤ X →
    ((shortIntervalExceptions P X Δ).card : ℝ) ≤ C * shortFixedPairBudget X Δ P.r

/-- The fixed-pair density parameter is `κ⁶ (Δ/r) / (r² log⁶(2X))`. -/
noncomputable def shortFixedPairParameter (X Δ r : ℕ) : ℝ :=
  ((r : ℝ)/r.totient)^6 * ((Δ : ℝ)/r) / ((r : ℝ)^2 * Real.log (2*(X : ℝ))^6)

private lemma fixed_cap_eq {r : ℕ} (hr : 0 < r) (X Δ : ℕ) :
    shortFixedPairAnalyticCap X Δ r =
      (r : ℝ) * (((r.totient : ℝ)/r) * Real.log (2*(X : ℝ)))^3 * Real.sqrt ((Δ : ℝ)/r) := by
  have hr' : (r : ℝ) ≠ 0 := (Nat.cast_pos.mpr hr).ne'
  unfold shortFixedPairAnalyticCap shortDoubleAvgAnalyticCap
  field_simp

private lemma fixed_count_trivial (P : Progressions) (X Δ : ℕ) :
    ((shortIntervalExceptions P X Δ).card : ℝ) ≤ (Δ : ℝ)/P.r+1 := by
  have h : ((Δ/P.r : ℕ) : ℝ) ≤ (Δ:ℝ)/P.r :=
    (le_div_iff₀ (Nat.cast_pos.mpr P.r_pos)).2 (by exact_mod_cast Nat.div_mul_le_self Δ P.r)
  have h' := shortIntervalExceptions_card_le P X Δ
  exact (show ((shortIntervalExceptions P X Δ).card : ℝ) ≤ (Δ/P.r : ℕ)+1 by exact_mod_cast h').trans (by linarith)

private lemma fixed_logs_le {X Δ : ℕ} (hX : 2 ≤ X) (hΔX : Δ ≤ X) :
    Real.log (2*((X+Δ : ℕ) : ℝ)) ≤ 2*Real.log (2*(X : ℝ)) := by
  have h2x : (1:ℝ) ≤ X := by exact_mod_cast (show 1≤X by omega)
  have hy : ((X+Δ : ℕ) : ℝ) ≤ 2*(X:ℝ) := by exact_mod_cast (show X+Δ ≤ 2*X by omega)
  have h := Real.log_le_log (by positivity : 0<2*((X+Δ : ℕ) : ℝ))
    (show 2*((X+Δ : ℕ) : ℝ)≤(2*(X:ℝ))^2 by
      nlinarith [mul_le_mul_of_nonneg_right h2x (Nat.cast_nonneg (α:=ℝ) X)])
  simpa only [Real.log_pow,Nat.cast_ofNat] using h

/-- Trivial counting supplies both the inactive Farey range and the range in which
the GRH error in the fixed prime energy exceeds its main term. -/
private lemma fixed_bound_of_active (T : ℕ)
    (input : ∃ C : ℝ, 0 < C ∧ ∀ (P : Progressions) {X Δ : ℕ},
      2 ≤ X → P.r ≤ X → 1 ≤ Δ → Δ ≤ X → T ≤ Δ/P.r →
      ((P.r.totient : ℝ)/P.r)^2*(P.r : ℝ)*Real.log (2*((X+Δ : ℕ) : ℝ))^2 ≤
        ((X+Δ : ℕ) : ℝ)/P.r →
      ((shortIntervalExceptions P X Δ).card : ℝ) ≤ C * shortFixedPairAnalyticCap X Δ P.r) :
    ShortFixedPairBound := by
  obtain ⟨C,hC,hactive⟩ := input
  let c := C + 8*((T : ℝ)+1) + 16
  have hc : 16 ≤ c := by dsimp [c]; linarith [Nat.cast_nonneg (α := ℝ) T]
  refine ⟨c,by linarith,?_⟩
  intro P X Δ hX hrX hΔ hΔX
  let r := P.r
  let a := (r.totient : ℝ)/r
  let k := (Δ : ℝ)/r
  let L := Real.log (2*(X : ℝ))
  let L' := Real.log (2*((X+Δ : ℕ) : ℝ))
  let z := a*L
  let A := shortFixedPairAnalyticCap X Δ r
  have hr : 0 < r := P.r_pos
  have hr' : (0:ℝ) < r := Nat.cast_pos.mpr hr
  have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hΔ' : (1:ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hk : 0 < k := div_pos (Nat.cast_pos.mpr hΔ) hr'
  have ha : 0 ≤ a := div_nonneg (Nat.cast_nonneg _) hr'.le
  have hz : 1/2 ≤ z := single_half_le_ratio_log hr hrX
  have hzpos : 0 ≤ z := by linarith
  have hz3 : (1/8:ℝ) ≤ z^3 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) hz 3
    norm_num at this; exact this
  have hid : A = (r:ℝ)*z^3*Real.sqrt k := fixed_cap_eq hr _ _
  have hA : 0 ≤ A := by rw [hid]; positivity
  have hrk : 1 ≤ (r:ℝ)*Real.sqrt k := by
    have hprod : (r:ℝ)^2*k = (r:ℝ)*(Δ:ℝ) := by dsimp [k]; field_simp
    have h1 : 1 ≤ ((r:ℝ)*Real.sqrt k)^2 := by
      rw [mul_pow, Real.sq_sqrt hk.le, hprod]
      simpa using mul_le_mul hr1 hΔ' (by norm_num) hr'.le
    nlinarith only [h1, show 0 ≤ (r:ℝ)*Real.sqrt k by positivity]
  have hA1 : 1 ≤ 8*A := by
    have h := mul_le_mul_of_nonneg_right hz3 (show 0 ≤ (r:ℝ)*Real.sqrt k by positivity)
    rw [hid]; nlinarith only [h,hrk]
  have htr := fixed_count_trivial P X Δ
  change _ ≤ k+1 at htr
  change _ ≤ c * min (k+1) A
  rw [mul_min_of_nonneg _ _ (by linarith : 0≤c)]
  refine le_min (htr.trans (by nlinarith only [mul_le_mul_of_nonneg_right (show 1≤c by linarith) (show 0≤k+1 by positivity)])) ?_
  by_cases hbig : T ≤ Δ/r
  · by_cases hB : a^2*(r:ℝ)*L'^2 ≤ ((X+Δ : ℕ) : ℝ)/r
    · exact (hactive P hX hrX hΔ hΔX hbig hB).trans (mul_le_mul_of_nonneg_right
        (by dsimp [c]; linarith [Nat.cast_nonneg (α := ℝ) T] : C ≤ c) hA)
    · have hL' : 0 ≤ L' := (one_le_log_two_mul (show 2≤X+Δ by omega)).trans' zero_le_one
      have hlogs : L'^2 ≤ (2*L)^2 := pow_le_pow_left₀ hL' (fixed_logs_le hX hΔX) 2
      have hkH : k ≤ ((X+Δ : ℕ) : ℝ)/r :=
        div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_add_left Δ X) hr'.le
      have hkB := hkH.trans (le_of_not_ge hB)
      have hlogB := mul_le_mul_of_nonneg_left hlogs (show 0≤a^2*(r:ℝ) by positivity)
      have hbound : k ≤ 4*(r:ℝ)*z^2 := hkB.trans (hlogB.trans_eq (by dsimp [z]; ring))
      have hs : Real.sqrt k ≤ 2*(r:ℝ)*z := by
        apply (Real.sqrt_le_left (by positivity)).2
        have h := mul_le_mul_of_nonneg_right hr1 (show 0≤4*(r:ℝ)*z^2 by positivity)
        nlinarith only [h,hbound]
      have h4 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) hz 2
      have h8 : 2*(r:ℝ)*z ≤ 8*(r:ℝ)*z^3 := by
        nlinarith only [mul_le_mul_of_nonneg_right h4 (show 0≤8*(r:ℝ)*z by positivity)]
      have hk8 := mul_le_mul_of_nonneg_right (hs.trans h8) (Real.sqrt_nonneg k)
      rw [← sq,Real.sq_sqrt hk.le] at hk8
      have : k+1 ≤ 16*A := by rw [hid] at hA1 ⊢; nlinarith only [hk8,hA1]
      exact htr.trans (this.trans (mul_le_mul_of_nonneg_right hc hA))
  · have hn := (Nat.div_lt_iff_lt_mul hr).mp (lt_of_not_ge hbig)
    have hkT : k ≤ T := (div_le_iff₀ hr').2 (by exact_mod_cast hn.le)
    have hTA := mul_le_mul_of_nonneg_left hA1 (show 0≤(T:ℝ)+1 by positivity)
    have hfill : k+1 ≤ (8*((T:ℝ)+1))*A := by linarith only [hkT,hTA]
    exact htr.trans (hfill.trans (mul_le_mul_of_nonneg_right (by dsimp [c]; linarith) hA))

set_option maxHeartbeats 1300000 in
private theorem fixed_pair_from_energies (hTw : SmoothedTwistEstimate)
    (hres : ∃ C : ℝ, 0 < C ∧ ∀ {r b Y Q K : ℕ}, 0 < r → r ≤ Y → 2 ≤ Y →
      b < r → Nat.Coprime b r → 3 ≤ Q → Q^2 ≤ K → Q^2 ≤ Y/r → ∀ x : ℝ,
      (∫ α in x-1/(K:ℝ)..x+1/(K:ℝ), ‖smoothedPrimeSum r b Y α-shortContModel r b Y Q α‖^2) ≤
        C*(Y:ℝ)/(Q:ℝ)*Real.log (2*(Y:ℝ))^2) : ShortFixedPairBound := by
  obtain ⟨C,hC,hl⟩ := hres
  obtain ⟨D,hD,hd⟩ := hTw
  let J : ℝ := 64*(361+2*D)*262144^2
  have hJ : 0 < J := by dsimp [J]; positivity
  apply fixed_bound_of_active (2^72)
  refine ⟨J*C*(2:ℝ)^16*8,by positivity,?_⟩
  intro P X Δ hX hrX hΔ hΔX hbig hB
  let r := P.r
  have hr : 0<r := P.r_pos
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
  obtain ⟨_,hQlo,_,hQΔ⟩ := routeAQ_bounds hr (le_trans (by norm_num : 2^26 ≤ 2^72) hbig)
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
  have hroot : 0 ≤ Real.sqrt k := Real.sqrt_nonneg _
  have hratio : (K:ℝ)/(Q:ℝ) ≤ (2:ℝ)^16*Real.sqrt k := by
    change 1/(2:ℝ)^14*Real.sqrt k ≤ (Q:ℝ) at hQlo
    apply (div_le_iff₀ hQp).2
    have hq := mul_le_mul_of_nonneg_right hQlo hroot
    nlinarith only [hq,Real.sq_sqrt hk0.le,hK4]
  have hL₀ : 0 < L₀ := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (one_le_log_two_mul hX)
  have hL : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (one_le_log_two_mul hY2)
  have hlogs : L^3 ≤ 8*L₀^3 := by
    have h' : L≤2*L₀ := fixed_logs_le hX hΔX
    have hh := pow_le_pow_left₀ hL.le h' 3
    linarith only [hh]

  let M (b : ℕ) : BoundedPeriodicFunction := ⟨shortContModel r b Y Q,
    shortContModel_measurable (by omega) r b Q, shortContModel_norm_bounded (by omega) r b Q,
    shortContModel_periodic r b Y Q⟩
  let S b := shortPrimeFunction r b Y
  let R b := shortDifference (S b) (M b)
  let A := C*(Y:ℝ)/(Q:ℝ)*L^2
  have hA : 0≤A := by dsimp only [A]; positivity
  have hfac : 0≤32*(K:ℝ)*A := by positivity
  have hm (j : ℕ) (hj : j ∈ shortBadFrequencies P X Δ) :
      thresh ≤ (shortPC (M P.b₁) (M P.b₂) j).re := by
    exact short_model_bad_freq_lower_progressions P hrX hΔX hbig hj
  have hlocal (b : ℕ) (hb : b<r) (hbr : Nat.Coprime b r) (x : ℝ) :
      localizedArcMass (R b) K x ≤ A := hl hr hrY hY2 hb hbr hQ3 hQK hQY x
  have hbigY : 2^72 ≤ Y/r := hbig.trans (Nat.div_le_div_right hΔY)
  have hp := (routeA_fixed_l2 hD hd hr P.b₁_lt P.coprime₁ hbigY hB).1
  have hmo := shortContModel_l2_le (b := P.b₂) hr hrY (hQΔ.trans hΔY) hY72
  have h₁ := (localized_product_bessel (R P.b₂) (S P.b₁) (X/r-2) K hKn
    (hlocal P.b₂ P.b₂_lt P.coprime₂)).trans (mul_le_mul_of_nonneg_left hp hfac)
  have h₂ := (localized_product_bessel (R P.b₁) (M P.b₂) (X/r-2) K hKn
    (hlocal P.b₁ P.b₁_lt P.coprime₁)).trans (mul_le_mul_of_nonneg_left hmo hfac)
  have hE := (shortCountPair P hrX hΔX (M P.b₁) (M P.b₂) hT.le hm).trans
    (mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (by norm_num : (0:ℝ) ≤ 2))
  have hE' : ((shortIntervalExceptions P X Δ).card : ℝ) ≤
      J*C*(r.totient:ℝ)*a^2*((K:ℝ)/Q)*L^3 := by
    apply le_of_mul_le_mul_right _ (pow_pos hT 2)
    refine hE.trans_eq ?_
    change 2*(32*(K:ℝ)*A *((1+2*D)*κ*H*L) + 32*(K:ℝ)*A*(360*κ*H*L)) = _
    dsimp only [A,J,a,κ,H,thresh]
    field_simp
    ring
  have ht1 := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ J*C*(r.totient:ℝ)*a^2)
  have ht2 := mul_le_mul ht1 hlogs (by positivity) (by positivity)
  change _ ≤ J*C*(2:ℝ)^16*8*((r.totient:ℝ)*(a^2*Real.sqrt k*L₀^3))
  exact hE'.trans (ht2.trans_eq (by ring))

/-- For a window at least one period long, the endpoint correction is absorbed by `Δ/r`. -/
theorem shortFixedPairBound_long_window (h : ShortFixedPairBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Progressions) {X Δ : ℕ}, 2 ≤ X → P.r ≤ Δ → Δ ≤ X →
      ((shortIntervalExceptions P X Δ).card : ℝ) ≤
        C * min ((Δ : ℝ)/P.r) (shortFixedPairAnalyticCap X Δ P.r) := by
  obtain ⟨C,hC,hbound⟩ := h
  refine ⟨C+2,by positivity,?_⟩
  intro P X Δ hX hrΔ hΔX
  have hp := P.r_pos
  have hr' : (0:ℝ)<P.r := Nat.cast_pos.mpr hp
  have hk : (1:ℝ) ≤ (Δ:ℝ)/P.r := (one_le_div hr').2 (Nat.cast_le.mpr hrΔ)
  have hA : 0 ≤ shortFixedPairAnalyticCap X Δ P.r := by
    have hL := one_le_log_two_mul hX
    dsimp [shortFixedPairAnalyticCap,shortDoubleAvgAnalyticCap]; positivity
  have htr := fixed_count_trivial P X Δ
  have he := (hbound P hX (hrΔ.trans hΔX) (hp.trans_le hrΔ) hΔX).trans
    (mul_le_mul_of_nonneg_left (min_le_right ..) hC.le)
  rw [mul_min_of_nonneg _ _ (by positivity : 0 ≤ C+2)]
  refine le_min (htr.trans ?_) (he.trans (mul_le_mul_of_nonneg_right (by linarith) hA))
  nlinarith only [hk,mul_nonneg hC.le (show 0 ≤ (Δ:ℝ)/P.r by positivity)]

private lemma fixed_normalized_term {X Δ r : ℕ} (hr : 0<r) (hX : 2≤X) (hΔ : 1≤Δ) :
    shortFixedPairAnalyticCap X Δ r / ((Δ : ℝ)/r) = (Real.sqrt (shortFixedPairParameter X Δ r))⁻¹ := by
  let k := (Δ:ℝ)/r
  let z := ((r.totient:ℝ)/r)*Real.log (2*(X:ℝ))
  have hr' : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have ht : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hL : 0<Real.log (2*(X:ℝ)) := zero_lt_one.trans_le (one_le_log_two_mul hX)
  have hk : 0<k := div_pos (Nat.cast_pos.mpr hΔ) hr'
  have hz : 0<z := mul_pos (div_pos ht hr') hL
  have hs : (Real.sqrt k)^2 = k := Real.sq_sqrt hk.le
  have hrz : (r:ℝ)*z^3 ≠ 0 := by positivity
  have hpar : shortFixedPairParameter X Δ r = k/((r:ℝ)*z^3)^2 := by
    dsimp [shortFixedPairParameter,z,k]
    field_simp
  rw [fixed_cap_eq hr, hpar,Real.sqrt_div hk.le,Real.sqrt_sq (le_of_lt (by positivity : 0<(r:ℝ)*z^3))]
  change (r:ℝ)*z^3*Real.sqrt k/k = (Real.sqrt k/((r:ℝ)*z^3))⁻¹
  have hks := Real.sqrt_pos.mpr hk
  field_simp
  exact hs

/-- Uniform fixed pairs may vary with the modulus along the sequence. -/
theorem shortFixedPairDensity_of_bound (h : ShortFixedPairBound) (P : ℕ → Progressions)
    (X Δ : ℕ → ℕ) (hX : ∀ n, 2 ≤ X n) (hrX : ∀ n, (P n).r ≤ X n)
    (hΔ : ∀ n, 1 ≤ Δ n) (hΔX : ∀ n, Δ n ≤ X n)
    (hP : Tendsto (fun n => shortFixedPairParameter (X n) (Δ n) (P n).r) atTop atTop) :
    Tendsto (fun n => ((shortIntervalExceptions (P n) (X n) (Δ n)).card : ℝ) / ((Δ n : ℝ)/(P n).r))
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := h
  have hs := (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hP)).const_mul C
  rw [mul_zero] at hs
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hs
  · exact Eventually.of_forall fun n => by positivity
  · refine Eventually.of_forall fun n => ?_
    have he := (hbound (P n) (hX n) (hrX n) (hΔ n) (hΔX n)).trans
      (mul_le_mul_of_nonneg_left (min_le_right ..) hC.le)
    refine (div_le_div_of_nonneg_right he (by positivity)).trans_eq ?_
    rw [mul_div_assoc, fixed_normalized_term (P n).r_pos (hX n) (hΔ n)]
    rfl

/-- The local residual and the single-class prime energy give the fixed-pair estimate. -/
theorem short_fixed_pair_of_localTwistedMeanSquare
    (h : LocalTwistedMeanSquare) (hTw : SmoothedTwistEstimate) : ShortFixedPairBound :=
  fixed_pair_from_energies hTw (shortResidual_fixed_local_of_meanSquare h)

/-- Uniformly in both fixed reduced classes, GRH supplies the short-window exceptional count. -/
theorem short_fixed_pair_of_dirichletGRH (hGRH : DirichletGRH) : ShortFixedPairBound :=
  short_fixed_pair_of_localTwistedMeanSquare (localTwistedMeanSquare_of_dirichletGRH hGRH)
    (smoothedTwistEstimate_of_dirichletGRH hGRH)

theorem short_fixed_pair_long_window_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Progressions) {X Δ : ℕ}, 2 ≤ X → P.r ≤ Δ → Δ ≤ X →
      ((shortIntervalExceptions P X Δ).card : ℝ) ≤
        C * min ((Δ : ℝ)/P.r) (shortFixedPairAnalyticCap X Δ P.r) :=
  shortFixedPairBound_long_window (short_fixed_pair_of_dirichletGRH hGRH)

theorem short_fixed_pair_density_one_of_dirichletGRH (hGRH : DirichletGRH) (P : ℕ → Progressions)
    (X Δ : ℕ → ℕ) (hX : ∀ n, 2 ≤ X n) (hrX : ∀ n, (P n).r ≤ X n)
    (hΔ : ∀ n, 1 ≤ Δ n) (hΔX : ∀ n, Δ n ≤ X n)
    (hP : Tendsto (fun n => shortFixedPairParameter (X n) (Δ n) (P n).r) atTop atTop) :
    Tendsto (fun n => ((shortIntervalExceptions (P n) (X n) (Δ n)).card : ℝ) / ((Δ n : ℝ)/(P n).r))
      atTop (𝓝 0) :=
  shortFixedPairDensity_of_bound (short_fixed_pair_of_dirichletGRH hGRH) P X Δ hX hrX hΔ hΔX hP

end FareyGoldbach