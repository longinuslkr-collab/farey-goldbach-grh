import FareyGoldbach.SharpPerronEnvelope
import FareyGoldbach.SharpPerronKernel

/-! # Choice of the Perron ramp width at an integer endpoint -/

open scoped Topology

namespace FareyGoldbach

noncomputable def sharpPerronHeight (X : ℕ) : ℝ := 4*(X:ℝ)

noncomputable def sharpPerronWidth (X : ℕ) : ℝ := 1/sharpPerronHeight X

noncomputable def scaledSharpPerronKernel (X : ℕ) (s : ℂ) : ℂ :=
  ((X:ℝ):ℂ)^s * sharpPerronKernel (sharpPerronWidth X) s

theorem sharpPerronWidth_pos {X : ℕ} (hX : 2≤X) : 0<sharpPerronWidth X := by
  have hx : (0:ℝ)<X := Nat.cast_pos.mpr (by omega)
  unfold sharpPerronWidth sharpPerronHeight
  positivity

theorem sharpPerronWidth_le_quarter {X : ℕ} (hX : 2≤X) : sharpPerronWidth X≤1/4 := by
  have hx : (2:ℝ)≤X := Nat.cast_le.mpr hX
  unfold sharpPerronWidth sharpPerronHeight
  exact one_div_le_one_div_of_le (by norm_num) (by linarith only [hx])

/-- The scaled ramp contains no integer in its transition interval. -/
theorem sharpPerron_end_lt_succ {X : ℕ} (hX : 2≤X) :
    Real.exp (2*sharpPerronWidth X) * (X:ℝ) < (X:ℝ)+1 := by
  have hx : (2:ℝ)≤X := Nat.cast_le.mpr hX
  have hp := sharpPerronWidth_pos hX
  have hδ := sharpPerronWidth_le_quarter hX
  let t := 2*sharpPerronWidth X
  have ht : 0<t := by dsimp [t]; positivity
  have ht₂ : t<2 := by dsimp [t]; linarith only [hδ]
  have htx : t*(X:ℝ) = 1/2 := by
    dsimp [t,sharpPerronWidth,sharpPerronHeight]
    field_simp [show (X:ℝ)≠0 by linarith only [hx]]
    ring
  have hr : ((2+t)/(2-t))*(X:ℝ) < (X:ℝ)+1 := by
    rw [div_mul_eq_mul_div,div_lt_iff₀ (sub_pos.mpr ht₂)]
    linarith only [htx, show t≤1/2 by dsimp [t]; linarith only [hδ]]
  exact (mul_lt_mul_of_pos_right (Real.exp_lt_two_add_div_two_sub ht ht₂)
    (by linarith only [hx])).trans hr

theorem sharpPerron_log_ge_one {X d : ℕ} [NeZero d] (hX : 2≤X) :
    1≤Real.log (2*(d:ℝ)*(X:ℝ)) := by
  have hx : (2:ℝ)≤X := Nat.cast_le.mpr hX
  have hh := one_le_log_two_mul_d_mul d ((X:ℝ)-2)
  rw [abs_of_nonneg (sub_nonneg.mpr hx), show 2+((X:ℝ)-2)=(X:ℝ) by ring] at hh
  exact hh

private theorem sharpPerron_base_log_upper {X d : ℕ} [NeZero d] (hX : 2≤X) :
    Real.log (2*(d:ℝ)*(2+sharpPerronHeight X))≤3*Real.log (2*(d:ℝ)*(X:ℝ)) := by
  have hx : (2:ℝ)≤X := Nat.cast_le.mpr hX
  have hd : (1:ℝ)≤d := Nat.one_le_cast.mpr (NeZero.pos d)
  let u := 2*(d:ℝ)*(X:ℝ)
  have hu : 4≤u := by
    dsimp [u]
    nlinarith only [hx,hd,mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hx)]
  have hp : 0<2*(d:ℝ)*(2+sharpPerronHeight X) := by
    dsimp [sharpPerronHeight]
    positivity
  have hb : 2*(d:ℝ)*(2+sharpPerronHeight X)≤u^3 := by
    calc _ ≤ 2*(d:ℝ)*(5*(X:ℝ)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              dsimp [sharpPerronHeight]
              linarith only [hx]
      _ = 5*u := by dsimp [u]; ring
      _ ≤ u^2*u := mul_le_mul_of_nonneg_right
        (by nlinarith only [hu,sq_nonneg (u-4)]) (by linarith only [hu])
      _ = u^3 := by ring
  exact (Real.log_le_log hp hb).trans_eq (by rw [Real.log_pow]; norm_num [u])

/-- Split the logarithm before estimating the two Perron tails. -/
theorem sharpPerron_log_split {X d : ℕ} [NeZero d] (hX : 2≤X) {x : ℝ} (hx : 0≤x) :
    (x≤sharpPerronHeight X →
      Real.log (2*(d:ℝ)*(2+x))≤3*Real.log (2*(d:ℝ)*(X:ℝ))) ∧
    (sharpPerronHeight X≤x →
      Real.log (2*(d:ℝ)*(2+x)) ≤
        4*Real.log (2*(d:ℝ)*(X:ℝ))*((1+x)/sharpPerronHeight X)) := by
  let T := sharpPerronHeight X
  let L := Real.log (2*(d:ℝ)*(X:ℝ))
  have hX' : (2:ℝ)≤X := Nat.cast_le.mpr hX
  have hT : 0<T := by dsimp [T,sharpPerronHeight]; linarith only [hX']
  have hd : (0:ℝ)<d := Nat.cast_pos.mpr (NeZero.pos d)
  have hL : 1≤L := sharpPerron_log_ge_one hX
  have hlog := sharpPerron_base_log_upper (d:=d) hX
  have hp : 0<2*(d:ℝ)*(2+x) := by positivity
  refine ⟨fun h => (Real.log_le_log hp
    (mul_le_mul_of_nonneg_left (by linarith only [h]) (by positivity))).trans hlog,?_⟩
  intro hTx
  let y := (1+x)/T
  have hy : 1≤y := (one_le_div hT).mpr (by linarith only [hTx])
  have hratio : 2+x≤(2+T)*y := by
    dsimp only [y]
    rw [show (2+T)*((1+x)/T)=((2+T)*(1+x))/T by ring, le_div_iff₀ hT]
    nlinarith only [hTx,hx]
  have hy' : 0<y := by linarith only [hy]
  have h2d : 0<2*(d:ℝ)*(2+T) := by positivity
  calc Real.log (2*(d:ℝ)*(2+x)) ≤ Real.log ((2*(d:ℝ)*(2+T))*y) :=
        Real.log_le_log hp (by
          calc _ ≤ (2*(d:ℝ))*((2+T)*y) := mul_le_mul_of_nonneg_left hratio (by positivity)
            _ = _ := by ring)
    _ = Real.log (2*(d:ℝ)*(2+T))+Real.log y := Real.log_mul h2d.ne' hy'.ne'
    _ ≤ 3*L+(y-1) := add_le_add hlog (Real.log_le_sub_one_of_pos hy')
    _ ≤ 4*L*y := by nlinarith only [hL,hy,mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hy)]

theorem sharpPerronMajorant_mass_le {X d : ℕ} [NeZero d] (hX : 2≤X) :
    (∫ u : ℝ, sharpPerronMajorant (sharpPerronHeight X) u) ≤
      8*Real.log (2*(d:ℝ)*(X:ℝ)) ∧
    (∑' k : ℤ, sharpPerronMajorant (sharpPerronHeight X) (k:ℝ)) ≤
      9*Real.log (2*(d:ℝ)*(X:ℝ)) := by
  have hT : 0≤sharpPerronHeight X := by unfold sharpPerronHeight; positivity
  have hL := sharpPerron_log_ge_one (d:=d) hX
  have hlog := sharpPerron_base_log_upper (d:=d) hX
  have hd : (1:ℝ)≤d := Nat.one_le_cast.mpr (NeZero.pos d)
  have h₁ : Real.log (1+sharpPerronHeight X) ≤ 3*Real.log (2*(d:ℝ)*(X:ℝ)) := by
    apply le_trans _ hlog
    apply Real.log_le_log (by positivity)
    calc
      _ ≤ 2+sharpPerronHeight X := by linarith
      _ ≤ _ := le_mul_of_one_le_left (by positivity) (by linarith only [hd])
  constructor
  · rw [sharpPerronMajorant_integral hT]
    linarith only [h₁,hL]
  · exact (sharpPerronMajorant_int_tsum_le hT).trans (by linarith only [h₁,hL])

end FareyGoldbach
