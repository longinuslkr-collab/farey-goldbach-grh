import FareyGoldbach.ShortFixedResidualArcMass
import FareyGoldbach.LocalTwistedMeanSquareOfGRH
import FareyGoldbach.SingleAverageAssembly

/-! # The first mixed term in the single average -/

open MeasureTheory
open scoped Classical

namespace FareyGoldbach

set_option maxHeartbeats 1200000 in
theorem short_single_prime_residual_energy (h : DirichletGRH) :
    ∃ C : ℝ, 0<C ∧ ∀ {r X Δ : ℕ}, 0<r → ∀ b₁ : ReducedClass r,
      2≤X → r≤X → 1≤Δ → Δ≤X → 2^72≤Δ/r →
      ((r.totient:ℝ)/r)^2*(r:ℝ)*Real.log (2*(X:ℝ))^2 ≤ (X:ℝ)/r →
      let Y := X+Δ
      let Q := routeAQ Δ r
      let S := fun b => smoothedPrimeSum r b Y
      let R := fun b (x:ℝ) => S b x-shortContModel r b Y Q x
      let T := (1:ℝ)/262144*((r:ℝ)/r.totient)^2*((Y:ℝ)/r)
      (∑ b ∈ coprimeClasses r, productWindowEnergy (R b) (S b₁.1) (X/r-2) (Δ/r+3))/(r.totient:ℝ)
        ≤ C*T^2*shortDoubleAvgAnalyticCap X Δ r := by
  obtain ⟨Ca,hCa,hmean⟩ := shortResidual_average_local_of_meanSquare (localTwistedMeanSquare_of_dirichletGRH h)
  obtain ⟨Cb,hCb,hprime⟩ := short_fixed_prime_l2_of_smoothedTwist (smoothedTwistEstimate_of_dirichletGRH h)
  let C : ℝ := 32*Ca*Cb*(2:ℝ)^16*8*(262144:ℝ)^2
  refine ⟨C,by positivity,?_⟩
  intro r X Δ hr b hX hrX hΔ hΔX hbig hB Y Q S R T
  let W := Δ/r+3
  let k := (Δ:ℝ)/r
  let H := (Y:ℝ)/r
  let κ := (r:ℝ)/r.totient
  let L := Real.log (2*(Y:ℝ))
  let L₀ := Real.log (2*(X:ℝ))
  let M (j : ℕ) := shortContModelFunction r j Y Q (by dsimp [Y]; omega)
  let P (j : ℕ) := shortPrimeFunction r j Y
  let U (j : ℕ) := shortDifference (P j) (M j)
  let A := Ca*(Y:ℝ)/((r.totient:ℝ)*Q)*L^2
  have hXY : X≤Y := by dsimp [Y]; omega
  have hΔY : Δ≤Y := by dsimp [Y]; omega
  have hY : 2≤Y := hX.trans hXY
  have hrY : r≤Y := hrX.trans hXY
  have hrp : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have hφ : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hYp : (0:ℝ)<Y := Nat.cast_pos.mpr (by omega)
  have hL : 0≤L := zero_le_one.trans (one_le_log_two_mul hY)
  have hL₀ : 0≤L₀ := zero_le_one.trans (one_le_log_two_mul hX)
  have hw : 0<W := by dsimp [W]; omega
  have hQ3 : 3≤Q := by
    dsimp [Q,routeAQ]
    apply (Nat.le_div_iff_mul_le (by norm_num : 0<2^12)).2
    rw [Nat.le_sqrt]
    exact le_trans (by norm_num) hbig
  have hQp : (0:ℝ)<Q := Nat.cast_pos.mpr (by omega)
  have hQsq : Q^2≤Δ/r := by
    have h₁ : Q≤Nat.sqrt (Δ/r) := Nat.div_le_self _ _
    exact (Nat.pow_le_pow_left h₁ 2).trans (by simpa only [sq] using Nat.sqrt_le (Δ/r))
  have hQW : Q^2≤W := hQsq.trans (Nat.le_add_right _ _)
  have hQY : Q^2≤Y/r := hQsq.trans (Nat.div_le_div_right hΔY)
  have hlocal (x : ℝ) : (∑ j ∈ coprimeClasses r, localizedArcMass (U j) W x)/(r.totient:ℝ) ≤ A := by
    change (∑ j ∈ coprimeClasses r, ∫ α in x-1/(W:ℝ)..x+1/(W:ℝ), ‖U j α‖^2)/(r.totient:ℝ) ≤ A
    rw [← intervalIntegral_finset_sum (fun j _ => short_norm_sq_intervalIntegrable (U j) _ _),
      div_eq_inv_mul,← one_div,← intervalIntegral.integral_const_mul]
    exact hmean hr hrY hY hQ3 hQW hQY x
  have hs : (coprimeClasses r).Nonempty := Finset.card_pos.mp (by
    rw [card_coprimeClasses]; exact Nat.totient_pos.mpr hr)
  have hBe := averaged_localized_product_bessel (coprimeClasses r) ({()} : Finset Unit)
    hs (Finset.singleton_nonempty ()) U (fun _ => P b.1) (X/r-2) W hw (A := A) (fun x => by
      rw [card_coprimeClasses]; exact hlocal x)
  simp only [Finset.sum_singleton,Finset.card_singleton,Nat.cast_one,card_coprimeClasses,mul_one,div_one] at hBe
  have hb := mem_coprimeClasses.mp b.2
  have hPrime : (∫ x in (0:ℝ)..1, ‖P b.1 x‖^2) ≤ Cb*κ*H*L :=
    hprime (X:=X) (Δ:=Δ) hr hX hrX hΔX hb.1 hb.2 hB
  have he := hBe.trans (mul_le_mul_of_nonneg_left hPrime (show 0≤32*(W:ℝ)*A by dsimp [A]; positivity))
  have hroot : 0≤Real.sqrt k := Real.sqrt_nonneg _
  have hk : 0≤k := by dsimp [k]; positivity
  have hfloor : ((Δ/r:ℕ):ℝ) ≤ k := (le_div_iff₀ hrp).2 (by exact_mod_cast Nat.div_mul_le_self Δ r)
  have hk₁ : 1≤k := by
    exact (show (1:ℝ)≤(Δ/r:ℕ) by exact_mod_cast (show 1≤Δ/r by omega)).trans hfloor
  have hWk : (W:ℝ)≤4*k := by dsimp only [W]; push_cast; linarith only [hfloor,hk₁]
  obtain ⟨_,hQlo,_,_⟩ := routeAQ_bounds hr (le_trans (by norm_num : 2^26≤2^72) hbig)
  have hratio : (W:ℝ)/(Q:ℝ)≤(2:ℝ)^16*Real.sqrt k := by
    change 1/(2:ℝ)^14*Real.sqrt k ≤ (Q:ℝ) at hQlo
    apply (div_le_iff₀ hQp).2
    have hmul := mul_le_mul_of_nonneg_right hQlo hroot
    nlinarith only [hmul,Real.sq_sqrt hk,hWk]
  have hlogs : L^3≤8*L₀^3 := by
    have hy : (Y:ℝ)≤2*(X:ℝ) := by exact_mod_cast (show Y≤2*X by dsimp [Y]; omega)
    have hx : (1:ℝ)≤X := Nat.one_le_cast.mpr (by omega)
    have hl := Real.log_le_log (by positivity : 0<2*(Y:ℝ))
      (show 2*(Y:ℝ)≤(2*(X:ℝ))^2 by
        nlinarith only [hy,mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg (α:=ℝ) X)])
    rw [Real.log_pow] at hl
    have h' : L≤2*L₀ := hl
    have h'' := pow_le_pow_left₀ hL h' 3
    linarith only [h'']
  have hpe : 0≤32*Ca*Cb*κ^2*H^2 := by positivity
  change (∑ j ∈ coprimeClasses r, productWindowEnergy (U j) (P b.1) (X/r-2) W)/(r.totient:ℝ) ≤ _
  calc _ ≤ 32*(W:ℝ)*A*(Cb*κ*H*L) := he
    _ = (32*Ca*Cb*κ^2*H^2)*(((W:ℝ)/Q)*L^3) := by dsimp [A,κ,H]; field_simp
    _ ≤ (32*Ca*Cb*κ^2*H^2)*(((2:ℝ)^16*Real.sqrt k)*(8*L₀^3)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hratio hlogs (by positivity) (by positivity)) hpe
    _ = _ := by
      dsimp [C,T,shortDoubleAvgAnalyticCap,κ,H,k,L₀]
      field_simp

end FareyGoldbach
