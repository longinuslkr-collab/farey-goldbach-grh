import FareyGoldbach.ShortSingleAssembly
import FareyGoldbach.ShortDoubleAverageGoldbach

/-! # Optimization of the mixed Fourier energy on one translated window -/

open scoped BigOperators Classical

namespace FareyGoldbach

private theorem short_cutoff {H B : ℝ} (hH : 0≤H) (hB : 0<B) :
    ∃ D : ℕ, 1≤D ∧ B*Real.log (2*(D:ℝ))+H/(D:ℝ) ≤ 2*(B*(1+Real.log (2+H/B))) := by
  let u := H/B
  have hu : 0 ≤ u := div_nonneg hH hB.le
  let D := ⌈1+u⌉₊
  have hd : 1+u ≤ (D:ℝ) := Nat.le_ceil _
  have hd' : (1:ℝ) ≤ D := by linarith
  have hpos : 0 < (D:ℝ) := by linarith
  have hub := (Nat.ceil_lt_add_one (show 0 ≤ 1+u by linarith)).le
  have hle : (D:ℝ) ≤ 2+u := by dsimp [D]; linarith
  have hlog : Real.log (2*(D:ℝ)) ≤ 1+Real.log (2+u) := by
    rw [Real.log_mul (by norm_num) hpos.ne']
    linarith [Real.log_le_log hpos hle,Real.log_two_lt_d9]
  have htail : H/(D:ℝ) ≤ B := by
    apply (div_le_iff₀ hpos).2
    calc H = B*u := by dsimp [u]; field_simp
         _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hB.le
  have hlg : 0 ≤ Real.log (2+u) := Real.log_nonneg (by linarith)
  refine ⟨D,by exact_mod_cast hd',?_⟩
  change B*Real.log (2*(D:ℝ))+H/(D:ℝ) ≤ 2*(B*(1+Real.log (2+u)))
  nlinarith only [mul_le_mul_of_nonneg_left hlog hB.le,htail,mul_nonneg hB.le hlg]

/-- The split at D and the two all-denominator estimates give the minimum of the
window-dependent logarithm and the coarse bound. -/
theorem short_mixed_cap_optimize {X Δ r : ℕ} (hr : 0<r) (hX : 2≤X) (hΔX : Δ≤X)
    {E C : ℝ} (hC : 0<C) {Q : ℕ} (hQ : 0<Q) (hQK : (Q:ℝ)≤(Δ:ℝ)/r) :
    let Y := X+Δ
    let κ := (r:ℝ)/r.totient
    let H := (Y:ℝ)/r
    let L := Real.log (2*(Y:ℝ))
    let T := (1:ℝ)/262144*κ^2*H
    (∀ D : ℕ, 1≤D → E ≤ C*(κ^2*(Y:ℝ)*H*L^2*Real.log (2*(D:ℝ))+κ^4*H^3/(D:ℝ))) →
    E ≤ C*(κ^2*(Y:ℝ)*H*L^2*Real.log (2*(Q:ℝ))) →
    E ≤ C*(κ*(Y:ℝ)*H*L^3) →
    E ≤ (8*(262144:ℝ)^2*C)*T^2*shortSingleMixedCap X Δ r := by
  intro Y κ H L T hD hlow hco
  let a := (r.totient:ℝ)/r
  let K := (Δ:ℝ)/r
  let H₀ := (X:ℝ)/r
  let L₀ := Real.log (2*(X:ℝ))
  let B := shortSingleBase X r
  let G := κ^4*H^2
  have hr' : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have ht : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have ha : 0<a := div_pos ht hr'
  have hH : 0<H := div_pos (Nat.cast_pos.mpr (by dsimp [Y]; omega)) hr'
  have hH₀ : 0<H₀ := div_pos (Nat.cast_pos.mpr (by omega)) hr'
  have hκ : 0<κ := div_pos hr' ht
  have hG : 0<G := by dsimp [G]; positivity
  have hL₀ : 1≤L₀ := one_le_log_two_mul hX
  have hL : 1≤L := one_le_log_two_mul (show 2≤Y by dsimp [Y]; omega)
  have hB : 0<B := by dsimp [B,shortSingleBase]; positivity
  have hy : (Y:ℝ) ≤ 2*(X:ℝ) := by exact_mod_cast (show Y≤2*X by dsimp [Y]; omega)
  have hhh : H≤2*H₀ := (div_le_div_of_nonneg_right hy hr'.le).trans_eq (by dsimp [H₀]; ring)
  have hL2 : L ≤ 2*L₀ := by
    have hx : (2:ℝ)≤X := by exact_mod_cast hX
    have hh := Real.log_le_log (by positivity : 0<2*(Y:ℝ))
      (show 2*(Y:ℝ)≤(2*(X:ℝ))^2 by nlinarith [mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg (α:=ℝ) X)])
    rw [Real.log_pow] at hh; exact hh
  have hκa : κ*a=1 := by dsimp [κ,a]; field_simp
  have hYr : (Y:ℝ)=(r:ℝ)*H := by dsimp [H]; field_simp
  have hbase : κ^2*(Y:ℝ)*H*L^2 ≤ G*(4*B) := by
    have he : κ^2*(Y:ℝ)*H*L^2 = G*(a^2*(r:ℝ)*L^2) := by
      dsimp only [G]; rw [hYr]
      calc _ = κ^2*((r:ℝ)*H)*H*L^2*(κ*a)^2 := by rw [hκa]; ring
           _ = _ := by ring
    rw [he]
    apply mul_le_mul_of_nonneg_left _ hG.le
    change a^2*(r:ℝ)*L^2 ≤ 4*(a^2*(r:ℝ)*L₀^2)
    nlinarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith : 0≤L) hL2 2)
      (mul_nonneg (sq_nonneg a) hr'.le)]
  have hcore : κ*(Y:ℝ)*H*L^3 ≤ G*(8*(a^3*(r:ℝ)*L₀^3)) := by
    have he : κ*(Y:ℝ)*H*L^3 = G*(a^3*(r:ℝ)*L^3) := by
      dsimp only [G]; rw [hYr]
      calc _ = κ*((r:ℝ)*H)*H*L^3*(κ*a)^3 := by rw [hκa]; ring
           _ = _ := by ring
    rw [he]
    apply mul_le_mul_of_nonneg_left _ hG.le
    nlinarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith : 0≤L) hL2 3)
      (mul_nonneg (pow_nonneg ha.le 3) hr'.le)]
  have hedge : E ≤ (8*C*G)*(B*(1+Real.log (2+min K (H₀/B)))) := by
    by_cases hk : K≤H₀/B
    · rw [min_eq_left hk]
      have hq1 : (1:ℝ)≤Q := Nat.one_le_cast.mpr hQ
      have hlogq : 0≤Real.log (2*(Q:ℝ)) := Real.log_nonneg (by linarith)
      have hlogk : 0≤Real.log (2+K) := Real.log_nonneg (by linarith)
      have hl : Real.log (2*(Q:ℝ)) ≤ 1+Real.log (2+K) := by
        rw [Real.log_mul (by norm_num) (Nat.cast_pos.mpr hQ).ne']
        linarith only [Real.log_two_lt_d9,Real.log_le_log (Nat.cast_pos.mpr hQ) (by linarith : (Q:ℝ)≤2+K)]
      have hh := mul_le_mul hbase hl hlogq (mul_nonneg hG.le (by positivity))
      have hlarge : G*(4*B)*(1+Real.log (2+K)) ≤ 8*G*(B*(1+Real.log (2+K))) := by
        nlinarith only [mul_nonneg (mul_nonneg hG.le hB.le) (by linarith : 0≤1+Real.log (2+K))]
      exact hlow.trans ((mul_le_mul_of_nonneg_left (hh.trans hlarge) hC.le).trans_eq (by ring))
    · rw [min_eq_right (le_of_not_ge hk)]
      obtain ⟨D,hD1,hcut⟩ := short_cutoff hH₀.le hB
      have hd : (0:ℝ)<D := Nat.cast_pos.mpr hD1
      have hd1 : (1:ℝ)≤D := by exact_mod_cast hD1
      have hl : 0≤Real.log (2*(D:ℝ)) := Real.log_nonneg (by linarith only [hd1])
      have hlo := mul_le_mul_of_nonneg_right hbase hl
      have ht' : κ^4*H^3/(D:ℝ) ≤ G*(4*(H₀/(D:ℝ))) := by
        calc _ = G*(H/(D:ℝ)) := by dsimp [G]; ring
             _ ≤ _ := by
               apply mul_le_mul_of_nonneg_left _ hG.le
               rw [←mul_div_assoc]
               exact div_le_div_of_nonneg_right (by linarith only [hhh,hH₀]) hd.le
      have hsum := add_le_add hlo ht'
      have hnorm : κ^2*(Y:ℝ)*H*L^2*Real.log (2*(D:ℝ))+κ^4*H^3/(D:ℝ) ≤
          4*G*(B*Real.log (2*(D:ℝ))+H₀/(D:ℝ)) := hsum.trans_eq (by ring)
      exact (hD D hD1).trans (mul_le_mul_of_nonneg_left (hnorm.trans
        (mul_le_mul_of_nonneg_left hcut (by positivity))) hC.le |>.trans_eq (by ring))
  have heco : E≤(8*C*G)*(a^3*(r:ℝ)*L₀^3) :=
    hco.trans (mul_le_mul_of_nonneg_left hcore hC.le |>.trans_eq (by ring))
  have ht' : (8*(262144:ℝ)^2*C)*T^2 = 8*C*G := by dsimp [T,G]; ring
  rw [ht']
  change E ≤ (8*C*G)*min (B*(1+Real.log (2+min K (H₀/B)))) (a^3*(r:ℝ)*L₀^3)
  rw [mul_min_of_nonneg _ _ (by positivity)]
  exact le_min hedge heco

end FareyGoldbach

