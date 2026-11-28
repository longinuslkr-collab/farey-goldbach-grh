import FareyGoldbach.ShortIntervalExceptions
import FareyGoldbach.SingleAverageAssembly

/-! # Single-average short-window budgets and their density consequences -/

open Filter
open scoped BigOperators Topology Classical

set_option maxRecDepth 8192

namespace FareyGoldbach

noncomputable def shortSingleAvgExceptions (X Δ r : ℕ) (hr : 0<r) (b₁ : ReducedClass r) : ℝ :=
  (1/(r.totient:ℝ))*∑ b₂ ∈ (coprimeClasses r).attach,
    ((shortIntervalExceptions (shortProgressions hr b₁ b₂) X Δ).card:ℝ)

noncomputable def shortSingleBase (X r : ℕ) : ℝ :=
  ((r.totient:ℝ)/r)^2*(r:ℝ)*Real.log (2*(X:ℝ))^2

noncomputable def shortSingleMixedCap (X Δ r : ℕ) : ℝ :=
  let B := shortSingleBase X r
  let K := (Δ:ℝ)/r
  let H := (X:ℝ)/r
  min (B*(1+Real.log (2+min K (H/B)))) (((r.totient:ℝ)/r)^3*(r:ℝ)*Real.log (2*(X:ℝ))^3)

noncomputable def shortSingleAvgAnalyticCap (X Δ r : ℕ) : ℝ :=
  shortDoubleAvgAnalyticCap X Δ r + shortSingleMixedCap X Δ r

noncomputable def shortSingleAvgBudget (X Δ r : ℕ) : ℝ :=
  min (min ((Δ:ℝ)/r+1) ((Δ:ℝ)/r.totient)) (shortSingleAvgAnalyticCap X Δ r)

def ShortSingleAvgBound : Prop :=
  ∃ C : ℝ, 0<C ∧ ∀ {X Δ r : ℕ} (hr : 0<r) (b₁ : ReducedClass r),
    2≤X → r≤X → 1≤Δ → Δ≤X → shortSingleAvgExceptions X Δ r hr b₁ ≤ C*shortSingleAvgBudget X Δ r

theorem shortSingleAvgExceptions_trivial {r : ℕ} (hr : 0<r) (b₁ : ReducedClass r) (X Δ : ℕ) :
    shortSingleAvgExceptions X Δ r hr b₁ ≤ min ((Δ:ℝ)/r+1) ((Δ:ℝ)/r.totient) := by
  have hr' : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have ht : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hfloor : ((Δ/r:ℕ):ℝ) ≤ (Δ:ℝ)/r := (le_div_iff₀ hr').2 (by exact_mod_cast Nat.div_mul_le_self Δ r)
  have hp (b₂ : ReducedClass r) :
      ((shortIntervalExceptions (shortProgressions hr b₁ b₂) X Δ).card:ℝ) ≤ (Δ:ℝ)/r+1 := by
    have h := shortIntervalExceptions_card_le (shortProgressions hr b₁ b₂) X Δ
    change _ ≤ Δ/r+1 at h
    exact (Nat.cast_le.mpr h).trans (by push_cast; linarith)
  unfold shortSingleAvgExceptions
  apply le_min
  · calc _ ≤ (1/(r.totient:ℝ))*∑ _b₂ ∈ (coprimeClasses r).attach, ((Δ:ℝ)/r+1) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun b _ => hp b)) (by positivity)
        _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_attach,card_coprimeClasses]; field_simp
  · rw [one_div,←div_eq_inv_mul]
    exact div_le_div_of_nonneg_right (by exact_mod_cast short_fixed_first_sum_le hr b₁ X Δ) ht.le

theorem shortSingleMixedCap_nonneg {X Δ r : ℕ} (hX : 2≤X) : 0 ≤ shortSingleMixedCap X Δ r := by
  have hL := one_le_log_two_mul hX
  have hB : 0≤shortSingleBase X r := by unfold shortSingleBase; positivity
  have hh : 0 ≤ min ((Δ:ℝ)/r) (((X:ℝ)/r)/shortSingleBase X r) := le_min (by positivity) (by positivity)
  have hl := Real.log_nonneg (by linarith : 1≤2+min ((Δ:ℝ)/r) (((X:ℝ)/r)/shortSingleBase X r))
  unfold shortSingleMixedCap
  exact le_min (by positivity) (by positivity)

private theorem analyticCap_nonneg {X Δ r : ℕ} (hX : 2≤X) : 0 ≤ shortSingleAvgAnalyticCap X Δ r := by
  have hL := one_le_log_two_mul hX
  exact add_nonneg (by unfold shortDoubleAvgAnalyticCap; positivity) (shortSingleMixedCap_nonneg hX)

theorem shortSingleAvgBound_of_active
    (h : ∃ C : ℝ, 0<C ∧ ∀ {X Δ r : ℕ} (hr : 0<r) (b₁ : ReducedClass r),
      2≤X → r≤X → 1≤Δ → Δ≤X → 2^72≤Δ/r → shortSingleBase X r ≤ (X:ℝ)/r →
      shortSingleAvgExceptions X Δ r hr b₁ ≤ C*shortSingleAvgAnalyticCap X Δ r) :
    ShortSingleAvgBound := by
  obtain ⟨C,hC,hb⟩ := h
  let c : ℝ := C+8*((2:ℝ)^72+1)+4
  have hc : 1≤c := by dsimp [c]; linarith
  have hC' : C≤c := by dsimp [c]; linarith
  refine ⟨c,by linarith,fun {X Δ r} hr b₁ hX hrX hΔ hΔX => ?_⟩
  let K := (Δ:ℝ)/r
  let H := (X:ℝ)/r
  let a := (r.totient:ℝ)/r
  let κ := (r:ℝ)/r.totient
  let L := Real.log (2*(X:ℝ))
  let B := shortSingleBase X r
  let E := shortSingleAvgExceptions X Δ r hr b₁
  let A := shortDoubleAvgAnalyticCap X Δ r
  let V := shortSingleMixedCap X Δ r
  have hr' : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have ht : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hK : 0<K := div_pos (Nat.cast_pos.mpr hΔ) hr'
  have hH : 0<H := div_pos (Nat.cast_pos.mpr (by omega)) hr'
  have hL : 1≤L := one_le_log_two_mul hX
  have hκ : 0<κ := div_pos hr' ht
  have ha : 0<a := div_pos ht hr'
  have hB : 0<B := by dsimp [B,shortSingleBase]; positivity
  have hA : 0≤A := by change 0≤a^2*Real.sqrt K*L^3; positivity
  have hV : 0≤V := shortSingleMixedCap_nonneg hX
  have hA' : A≤shortSingleAvgAnalyticCap X Δ r := by change A≤A+V; linarith
  have htr := shortSingleAvgExceptions_trivial hr b₁ X Δ
  have htr' : E ≤ c*min (K+1) ((Δ:ℝ)/r.totient) :=
    htr.trans (le_mul_of_one_le_left (le_min (by positivity) (by positivity)) hc)
  unfold shortSingleAvgBudget
  rw [mul_min_of_nonneg _ _ (by linarith : 0≤c)]
  refine le_min htr' ?_
  by_cases hbig : 2^72≤Δ/r
  · by_cases hact : B≤H
    · exact (hb hr b₁ hX hrX hΔ hΔX hbig hact).trans
        (mul_le_mul_of_nonneg_right hC' (analyticCap_nonneg hX))
    · have hKB : K≤B := (div_le_div_of_nonneg_right (Nat.cast_le.mpr hΔX) hr'.le).trans (le_of_not_ge hact)
      have hK1 : 1≤K := by
        apply (one_le_div hr').2
        exact_mod_cast (show r≤Δ by have hh := (Nat.le_div_iff_mul_le hr).1 (show 1≤Δ/r by omega); simpa using hh)
      have hal : 1/2 ≤ a*L := single_half_le_ratio_log hr hrX
      have hlog : 0 ≤ Real.log (2+min K (H/B)) := Real.log_nonneg (by
        have hh := le_min hK.le (div_pos hH hB).le; linarith)
      have hVL : K ≤ B*(1+Real.log (2+min K (H/B))) :=
        hKB.trans (le_mul_of_one_le_right hB.le (by linarith))
      have hVR : K ≤ 2*(a^3*r*L^3) := by
        have hh := mul_le_mul_of_nonneg_left hal hB.le
        change K≤2*(a^3*(r:ℝ)*L^3)
        change a^2*(r:ℝ)*L^2*(1/2)≤a^2*(r:ℝ)*L^2*(a*L) at hh
        change K≤a^2*(r:ℝ)*L^2 at hKB
        nlinarith only [hh,hKB]
      have hv : K≤2*V := by
        change K≤2*min _ _
        rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ)≤2)]
        exact le_min (by linarith only [hVL,hK]) hVR
      have he := htr.trans (min_le_left ..)
      change E≤K+1 at he
      refine (show E ≤ 4*shortSingleAvgAnalyticCap X Δ r by change E≤4*(A+V); linarith only [he,hv,hK1,hA]).trans ?_
      exact mul_le_mul_of_nonneg_right (by dsimp [c]; linarith : 4≤c) (analyticCap_nonneg hX)
  · have hkT : K ≤ (2:ℝ)^72 := by
      apply (div_le_iff₀ hr').2
      exact_mod_cast (Nat.div_lt_iff_lt_mul hr).mp (lt_of_not_ge hbig) |>.le
    have hs : Real.sqrt K ≤ (2:ℝ)^72+1 := by
      apply (Real.sqrt_le_left (by positivity)).2
      nlinarith only [hkT]
    have haL : 1/2 ≤ a*L := single_half_le_ratio_log hr hrX
    have hκa : κ*a=1 := by dsimp [κ,a]; field_simp
    have hkL : κ ≤ 2*L := by
      have hh := mul_le_mul_of_nonneg_left haL hκ.le
      rw [←mul_assoc,hκa,one_mul] at hh; linarith
    have hco : κ ≤ 8*(a^2*L^3) := by
      have he : a^2*κ^3=κ := by calc _ = (κ*a)^2*κ := by ring
                                      _ = _ := by rw [hκa]; ring
      nlinarith only [he,mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hκ.le hkL 3) (sq_nonneg a)]
    have hE : E≤κ*K := by
      exact (htr.trans (min_le_right ..)).trans_eq (by dsimp [κ,K]; field_simp)
    have hmul := mul_le_mul_of_nonneg_right (mul_le_mul hco hs (Real.sqrt_nonneg _) (by positivity)) (Real.sqrt_nonneg K)
    have hrel : κ*Real.sqrt K*Real.sqrt K = κ*K := by rw [mul_assoc,←sq,Real.sq_sqrt hK.le]
    rw [hrel] at hmul
    have hsmall : E≤8*((2:ℝ)^72+1)*A := by
      change E≤8*((2:ℝ)^72+1)*(a^2*Real.sqrt K*L^3)
      nlinarith only [hE,hmul]
    exact hsmall.trans (mul_le_mul (by dsimp [c]; linarith : 8*((2:ℝ)^72+1)≤c) hA' hA (zero_le_one.trans hc))

/-- On intervals containing a complete period, the endpoint correction is absorbed in K. -/
theorem shortSingleAvgBound_long_window (h : ShortSingleAvgBound) :
    ∃ C : ℝ, 0<C ∧ ∀ {X Δ r : ℕ} (hr : 0<r) (b₁ : ReducedClass r), 2≤X → r≤Δ → Δ≤X →
      shortSingleAvgExceptions X Δ r hr b₁ ≤ C*min ((Δ:ℝ)/r) (shortSingleAvgAnalyticCap X Δ r) := by
  obtain ⟨C,hC,hb⟩ := h
  refine ⟨C+2,by linarith,fun {X Δ r} hr b hX hrΔ hΔX => ?_⟩
  have hK : 1 ≤ (Δ:ℝ)/r := (one_le_div (Nat.cast_pos.mpr hr)).2 (Nat.cast_le.mpr hrΔ)
  have htr := (shortSingleAvgExceptions_trivial hr b X Δ).trans (min_le_left ..)
  have hcap := (hb hr b hX (hrΔ.trans hΔX) (hr.trans_le hrΔ) hΔX).trans
    (mul_le_mul_of_nonneg_left (min_le_right ..) hC.le)
  rw [mul_min_of_nonneg _ _ (by linarith : 0≤C+2)]
  refine le_min ?_ (hcap.trans (mul_le_mul_of_nonneg_right (by linarith : C≤C+2) (analyticCap_nonneg hX)))
  nlinarith only [htr,hK,mul_nonneg hC.le (show 0≤(Δ:ℝ)/r by positivity)]

theorem shortSingleAvgDensity_of_bound (h : ShortSingleAvgBound) (X Δ r : ℕ→ℕ)
    (hr : ∀ n,0<r n) (b₁ : ∀ n, ReducedClass (r n)) (hX : ∀ n,2≤X n)
    (hrX : ∀ n,r n≤X n) (hΔ : ∀ n,1≤Δ n) (hΔX : ∀ n,Δ n≤X n)
    (hP : Tendsto (fun n => shortSingleAvgAnalyticCap (X n) (Δ n) (r n)/((Δ n:ℝ)/r n)) atTop (𝓝 0)) :
    Tendsto (fun n => shortSingleAvgExceptions (X n) (Δ n) (r n) (hr n) (b₁ n)/((Δ n:ℝ)/r n)) atTop (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := h
  have hs := hP.const_mul C
  rw [mul_zero] at hs
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hs
    (Filter.Eventually.of_forall fun n => by unfold shortSingleAvgExceptions; positivity) (Filter.Eventually.of_forall fun n => ?_)
  have hc := (hb (hr n) (b₁ n) (hX n) (hrX n) (hΔ n) (hΔX n)).trans
    (mul_le_mul_of_nonneg_left (min_le_right ..) hC.le)
  rw [←mul_div_assoc]
  exact div_le_div_of_nonneg_right hc (by positivity)

noncomputable def shortSingleSufficientParameter (X Δ r : ℕ) : ℝ :=
  let a := (r.totient:ℝ)/r
  let L := Real.log (2*(X:ℝ))
  (Δ:ℝ)/((r:ℝ)*a^4*L^6+a^3*(r:ℝ)^2*L^3)

theorem shortSingleAvgParameter_suffices (X Δ r : ℕ→ℕ) (hr : ∀ n,0<r n)
    (hX : ∀ n,2≤X n) (hΔ : ∀ n,1≤Δ n)
    (hP : Tendsto (fun n => shortSingleSufficientParameter (X n) (Δ n) (r n)) atTop atTop) :
    Tendsto (fun n => shortSingleAvgAnalyticCap (X n) (Δ n) (r n)/((Δ n:ℝ)/r n)) atTop (𝓝 0) := by
  let p := fun n => (shortSingleSufficientParameter (X n) (Δ n) (r n))⁻¹
  have hp : Tendsto p atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hP
  have hh : Tendsto (fun n => Real.sqrt (p n)+p n) atTop (𝓝 0) := by simpa using hp.sqrt.add hp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hh
    (Filter.Eventually.of_forall fun n => div_nonneg (analyticCap_nonneg (hX n)) (by positivity)) (Filter.Eventually.of_forall fun n => ?_)
  let K := (Δ n:ℝ)/r n
  let a := ((r n).totient:ℝ)/r n
  let L := Real.log (2*(X n:ℝ))
  have hr' : (0:ℝ)<r n := Nat.cast_pos.mpr (hr n)
  have hd : (0:ℝ)<Δ n := Nat.cast_pos.mpr (hΔ n)
  have hK : 0<K := div_pos hd hr'
  have ha : 0≤a := by dsimp [a]; positivity
  have hL : 1≤L := one_le_log_two_mul (hX n)
  have he : p n = ((r n:ℝ)*a^4*L^6+a^3*(r n:ℝ)^2*L^3)/(Δ n:ℝ) := by dsimp [p,shortSingleSufficientParameter,a,L]; rw [inv_div]
  have hs : shortDoubleAvgAnalyticCap (X n) (Δ n) (r n)/K ≤ Real.sqrt (p n) := by
    apply Real.le_sqrt_of_sq_le
    change (a^2*Real.sqrt K*L^3/K)^2 ≤ _
    rw [he,div_pow,mul_pow,mul_pow,Real.sq_sqrt hK.le]
    have heq : (a^2)^2*K*(L^3)^2/K^2 = (r n:ℝ)*a^4*L^6/(Δ n:ℝ) := by dsimp [K]; field_simp
    rw [heq]
    exact div_le_div_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hd.le
  have hv : shortSingleMixedCap (X n) (Δ n) (r n)/K ≤ p n := by
    rw [he]
    have hh : shortSingleMixedCap (X n) (Δ n) (r n) ≤ a^3*(r n:ℝ)*L^3 := min_le_right ..
    refine (div_le_div_of_nonneg_right hh hK.le).trans ?_
    calc _ = a^3*(r n:ℝ)^2*L^3/(Δ n:ℝ) := by dsimp [K]; field_simp
         _ ≤ _ := div_le_div_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hd.le
  rw [shortSingleAvgAnalyticCap,add_div]
  exact add_le_add hs hv

end FareyGoldbach



