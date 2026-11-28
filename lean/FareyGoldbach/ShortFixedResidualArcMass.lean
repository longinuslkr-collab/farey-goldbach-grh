import FareyGoldbach.ShortDoubleAverageGoldbach

/-! # Fixed-class energies for short intervals -/

open MeasureTheory Set
open scoped Classical

namespace FareyGoldbach

noncomputable def shortContModelFunction (r b Y Q : ℕ) (hY : 1 ≤ Y) : BoundedPeriodicFunction :=
  ⟨shortContModel r b Y Q, shortContModel_measurable hY r b Q,
    shortContModel_norm_bounded hY r b Q, shortContModel_periodic r b Y Q⟩

lemma short_norm_sq_intervalIntegrable (f : BoundedPeriodicFunction) (a b : ℝ) :
    IntervalIntegrable (fun x => ‖f x‖^2) volume a b := by
  obtain ⟨F,hF⟩ := f.bounded
  apply intervalIntegrable_of_measurable_bounded (B := F^2) (f.measurable.norm.pow_const 2)
  intro x
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hF x) 2

/-- Selecting one class from the nonnegative sum undoes exactly the factor `1/φ(r)`
in the averaged local mass. -/
theorem shortResidual_fixed_local_of_meanSquare (h : LocalTwistedMeanSquare) :
    ∃ C : ℝ, 0<C ∧ ∀ {r b Y Q K : ℕ}, 0<r → r≤Y → 2≤Y → b<r → Nat.Coprime b r →
      3≤Q → Q^2≤K → Q^2≤Y/r → ∀ x : ℝ,
      (∫ α in x-1/(K:ℝ)..x+1/(K:ℝ), ‖smoothedPrimeSum r b Y α-shortContModel r b Y Q α‖^2) ≤
        C*(Y:ℝ)/(Q:ℝ)*Real.log (2*(Y:ℝ))^2 := by
  obtain ⟨C,hC,hmean⟩ := shortResidual_average_local_of_meanSquare h
  refine ⟨C,hC,?_⟩
  intro r b Y Q K hr hrY hY hb hbr hQ hQK hQY x
  let A := x-1/(K:ℝ)
  let B := x+1/(K:ℝ)
  let φ : ℝ := r.totient
  let L := Real.log (2*(Y:ℝ))
  let R (i : ℕ) := shortDifference (shortPrimeFunction r i Y) (shortContModelFunction r i Y Q (by omega))
  have hφ : 0 < φ := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hQp : (0:ℝ) < Q := Nat.cast_pos.mpr (by omega)
  have hAB : A ≤ B := by
    have h : (0:ℝ) ≤ 1/(K:ℝ) := by positivity
    dsimp [A,B]; linarith only [h]
  have hsum : IntervalIntegrable (fun α => ∑ i ∈ coprimeClasses r, ‖R i α‖^2) volume A B := by
    have hf : (∑ i ∈ coprimeClasses r, fun α : ℝ => ‖R i α‖^2) =
        (fun α => ∑ i ∈ coprimeClasses r, ‖R i α‖^2) := by
      funext α; exact Finset.sum_apply α _ _
    rw [← hf]
    exact IntervalIntegrable.sum (coprimeClasses r) (fun i _ => short_norm_sq_intervalIntegrable (R i) A B)
  have hpoint (α : ℝ) : ‖R b α‖^2 ≤ ∑ i ∈ coprimeClasses r, ‖R i α‖^2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg ‖R i α‖) (mem_coprimeClasses.mpr ⟨hb,hbr⟩)
  have hle := intervalIntegral.integral_mono_on hAB (short_norm_sq_intervalIntegrable (R b) A B)
    hsum (fun α _ => hpoint α)
  have hm := hmean hr hrY hY hQ hQK hQY x
  change (∫ α in A..B, (1/φ)*∑ i ∈ coprimeClasses r, ‖R i α‖^2) ≤ C*(Y:ℝ)/(φ*Q)*L^2 at hm
  rw [intervalIntegral.integral_const_mul] at hm
  have hmul := mul_le_mul_of_nonneg_left hm hφ.le
  change (∫ α in A..B, ‖R b α‖^2) ≤ _
  refine hle.trans ?_
  calc (∫ α in A..B, ∑ i ∈ coprimeClasses r, ‖R i α‖^2) =
      φ*((1/φ)*(∫ α in A..B, ∑ i ∈ coprimeClasses r, ‖R i α‖^2)) := by field_simp
    _ ≤ φ*(C*(Y:ℝ)/(φ*Q)*L^2) := hmul
    _ = C*(Y:ℝ)/(Q:ℝ)*L^2 := by field_simp

/-- The fixed prime energy at `Y=X+Δ` is uniform on the active branch tested at `X`. -/
theorem short_fixed_prime_l2_of_smoothedTwist (h : SmoothedTwistEstimate) :
    ∃ C : ℝ, 0<C ∧ ∀ {X Δ r b : ℕ}, 0<r → 2≤X → r≤X → Δ≤X → b<r → Nat.Coprime b r →
      ((r.totient:ℝ)/r)^2*(r:ℝ)*Real.log (2*(X:ℝ))^2 ≤ (X:ℝ)/r →
      let Y := X+Δ
      (∫ α in (0:ℝ)..1, ‖smoothedPrimeSum r b Y α‖^2) ≤
        C*((r:ℝ)/r.totient)*((Y:ℝ)/r)*Real.log (2*(Y:ℝ)) := by
  obtain ⟨C,hC,hTw⟩ := h
  refine ⟨1+8*C,by positivity,?_⟩
  intro X Δ r b hr hX hrX hΔ hb hbr hB Y
  let φ : ℝ := r.totient
  let L := Real.log (2*(X:ℝ))
  let LY := Real.log (2*(Y:ℝ))
  have hr' : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have hφ : 0<φ := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hx : (0:ℝ)<X := Nat.cast_pos.mpr (by omega)
  have hx₂ : (2:ℝ)≤X := by exact_mod_cast hX
  have hxy : X≤Y := by dsimp [Y]; omega
  have hy₂ := hX.trans hxy
  have hy : (0:ℝ)<Y := Nat.cast_pos.mpr (by omega)
  have hY2X : (Y:ℝ) ≤ 2*(X:ℝ) := by exact_mod_cast (show Y≤2*X by dsimp [Y]; omega)
  have hL : 0≤L := zero_le_one.trans (one_le_log_two_mul hX)
  have hLY : 0≤LY := zero_le_one.trans (one_le_log_two_mul hy₂)
  have hBS : (φ*L)^2 ≤ X := by
    have he := mul_le_mul_of_nonneg_right hB hr'.le
    change ((φ/(r:ℝ))^2*(r:ℝ)*L^2)*(r:ℝ) ≤ ((X:ℝ)/r)*(r:ℝ) at he
    convert he using 1 <;> field_simp
  have hroot : φ*L ≤ Real.sqrt (X:ℝ) := (Real.le_sqrt (by positivity) hx.le).mpr hBS
  have hLYL : LY ≤ 2*L := by
    have h := Real.log_le_log (show 0<2*(Y:ℝ) by positivity)
      (show 2*(Y:ℝ)≤(2*(X:ℝ))^2 by nlinarith only [hY2X,hx₂,sq_nonneg ((X:ℝ)-1)])
    rw [Real.log_pow] at h
    exact h
  have hrootY : Real.sqrt (Y:ℝ) ≤ 2*Real.sqrt (X:ℝ) := by
    have h := Real.sqrt_le_sqrt (show (Y:ℝ)≤4*(X:ℝ) by linarith only [hY2X,hx.le])
    have h4 : Real.sqrt 4=2 := by rw [show (4:ℝ)=2^2 by norm_num, Real.sqrt_sq (by norm_num)]
    rwa [Real.sqrt_mul (by norm_num : (0:ℝ)≤4),h4] at h
  have hmain : Real.sqrt (Y:ℝ)*LY ≤ 4*((Y:ℝ)/φ) := by
    have h := mul_le_mul hrootY hLYL hLY (by positivity)
    have hs := mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg (X:ℝ))
    have hs' : Real.sqrt (X:ℝ)*L ≤ (X:ℝ)/φ := by
      apply (le_div_iff₀ hφ).2
      nlinarith only [hs,Real.sq_sqrt hx.le]
    have hdiff := div_le_div_of_nonneg_right (show (X:ℝ)≤Y from Nat.cast_le.mpr hxy) hφ.le
    linarith only [h,hs',hdiff]
  have hS := smoothedPrimeSum_l2_le hC hTw hr (hrX.trans hxy) hy₂ hb hbr
  have hn : ((r:ℝ)/φ)*((Y:ℝ)/r) = (Y:ℝ)/φ := by field_simp
  have hcalc := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmain
    (show 0≤2*C by positivity)) hLY
  change _ ≤ (1+8*C)*((r:ℝ)/φ)*((Y:ℝ)/r)*LY
  rw [show (1+8*C)*((r:ℝ)/φ)*((Y:ℝ)/r) = (1+8*C)*((Y:ℝ)/φ) by rw [mul_assoc,hn]]
  change _ ≤ (((r:ℝ)/φ)*((Y:ℝ)/r) + 2*C*Real.sqrt (Y:ℝ)*LY)*LY at hS
  rw [hn] at hS
  linarith only [hS,hcalc]

end FareyGoldbach
