import FareyGoldbach.ShortSingleAssembly

/-! # Scales for averaging the prescribed-class ternary Goldbach problem -/

open scoped BigOperators

namespace FareyGoldbach

noncomputable def ternaryCandidateScale (X r : ℕ) : ℝ :=
  (X:ℝ)/(64*(r.totient:ℝ)*Real.log (2*(X:ℝ)))

noncomputable def ternaryDoubleAverageBudget (X r : ℕ) : ℝ :=
  let H := (X:ℝ)/r
  let κ := (r:ℝ)/r.totient
  let L := Real.log (2*(X:ℝ))
  L^4/(κ^3*Real.sqrt H)

noncomputable def ternarySingleAverageBudget (X r : ℕ) : ℝ :=
  let κ := (r:ℝ)/r.totient
  let L := Real.log (2*(X:ℝ))
  let J := (X:ℝ)/((r.totient:ℝ)^2*L^2)
  ternaryDoubleAverageBudget X r + (L/κ)*(1+Real.log (2+J))/J

noncomputable def ternaryBinarySingleBudget (X r : ℕ) : ℝ :=
  let J := (X:ℝ)/((r.totient:ℝ)^2*Real.log (2*(X:ℝ))^2)
  shortDoubleAvgAnalyticCap X X r + shortSingleBase X r*(1+Real.log (2+J))

private theorem ternary_edge_scale {b B h H : ℝ} (hb : 0 < b) (hbB : b ≤ B) (hh : 0 ≤ h) (hhH : h ≤ H) :
    b*(1+Real.log (2+h/b)) ≤ B*(1+Real.log (2+H/B)) := by
  have hB := lt_of_lt_of_le hb hbB
  have hlog := Real.log_le_sub_one_of_pos (div_pos hB hb)
  have he : b * (B/b) = B := by field_simp
  have hk := mul_le_mul_of_nonneg_left hlog hb.le
  have harg : 2+h/b ≤ (B/b)*(2+H/B) := by
    field_simp [hb.ne',hB.ne']; nlinarith [mul_le_mul_of_nonneg_right hbB hB.le,
      mul_le_mul_of_nonneg_right hhH hB.le]
  have ht := Real.log_le_log (by positivity : 0 < 2+h/b) harg
  rw [Real.log_mul (div_pos hB hb).ne' (by have := div_nonneg (hh.trans hhH) hB.le; linarith : 2+H/B ≠ 0)] at ht
  have hlast := mul_le_mul_of_nonneg_right hbB (Real.log_nonneg
    (by have := div_nonneg (hh.trans hhH) hB.le; linarith : 1 ≤ 2+H/B))
  nlinarith only [he,hk,hlast,mul_le_mul_of_nonneg_left ht hb.le]


/-- The one-logarithm short binary bound is monotone after replacing its truncated
logarithm by the logarithm of the global ratio. -/
theorem ternary_binary_window_bound {X Y r : ℕ} (hr : 0<r) (hY : 2≤Y) (hYX : Y≤X) :
    shortSingleAvgBudget Y Y r ≤ ternaryBinarySingleBudget X r := by
  let a := (r.totient:ℝ)/r
  let H (y : ℕ) := (y:ℝ)/r
  let L (y : ℕ) := Real.log (2*(y:ℝ))
  let B (y : ℕ) := shortSingleBase y r
  have hr' : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have ht : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have ha : 0<a := div_pos ht hr'
  have hy : (0:ℝ)<Y := Nat.cast_pos.mpr (by omega)
  have hLY : 1≤L Y := one_le_log_two_mul hY
  have hLX : 1≤L X := one_le_log_two_mul (hY.trans hYX)
  have hl : L Y ≤ L X := Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hYX) (by norm_num))
  have hh : H Y ≤ H X := div_le_div_of_nonneg_right (Nat.cast_le.mpr hYX) hr'.le
  have hhy : 0<H Y := div_pos hy hr'
  have hby : 0<B Y := by change 0<a^2*(r:ℝ)*(L Y)^2; positivity
  have hb : B Y ≤ B X := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith : 0≤L Y) hl 2) (by positivity : 0≤a^2*(r:ℝ))
  have hJ : H X / B X = (X:ℝ)/((r.totient:ℝ)^2*(L X)^2) := by dsimp [H,B,shortSingleBase,L]; field_simp
  have hlog : 1+Real.log (2+min (H Y) (H Y/B Y)) ≤ 1+Real.log (2+H Y/B Y) := by
    have hz := le_min hhy.le (div_nonneg hhy.le hby.le)
    exact add_le_add (le_refl 1) (Real.log_le_log (by linarith) (add_le_add (le_refl 2) (min_le_right ..)))
  have he : shortSingleMixedCap Y Y r ≤ B X*(1+Real.log (2+H X/B X)) :=
    (min_le_left ..).trans ((mul_le_mul_of_nonneg_left hlog hby.le).trans (ternary_edge_scale hby hb hhy.le hh))
  rw [hJ] at he
  have hs : shortDoubleAvgAnalyticCap Y Y r ≤ shortDoubleAvgAnalyticCap X X r :=
    mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hh) (sq_nonneg a))
      (pow_le_pow_left₀ (by linarith : 0≤L Y) hl 3) (by positivity) (by positivity)
  exact (min_le_right ..).trans (add_le_add hs he)

theorem ternary_binary_double_scale {X r : ℕ} (hr : 0<r) (hX : 2≤X) :
    shortDoubleAvgAnalyticCap X X r / ternaryCandidateScale X r = 64*ternaryDoubleAverageBudget X r := by
  let H := (X:ℝ)/r
  let L := Real.log (2*(X:ℝ))
  have hr' : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have ht : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hx : (0:ℝ)<X := Nat.cast_pos.mpr (by omega)
  have hh : 0<H := div_pos hx hr'
  have hl : 0<L := zero_lt_one.trans_le (one_le_log_two_mul hX)
  have hs : 0<Real.sqrt H := Real.sqrt_pos.mpr hh
  have he : (r:ℝ)*(Real.sqrt H)^2 = (X:ℝ) := by rw [Real.sq_sqrt hh.le]; dsimp [H]; field_simp
  change (((r.totient:ℝ)/r)^2*Real.sqrt H*L^3)/((X:ℝ)/(64*(r.totient:ℝ)*L)) =
    64*(L^4/(((r:ℝ)/r.totient)^3*Real.sqrt H))
  field_simp
  exact he

theorem ternary_binary_single_scale {X r : ℕ} (hr : 0<r) (hX : 2≤X) :
    ternaryBinarySingleBudget X r / ternaryCandidateScale X r = 64*ternarySingleAverageBudget X r := by
  let L := Real.log (2*(X:ℝ))
  let J := (X:ℝ)/((r.totient:ℝ)^2*L^2)
  have hr' : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have ht : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hx : (0:ℝ)<X := Nat.cast_pos.mpr (by omega)
  have hl : 0<L := zero_lt_one.trans_le (one_le_log_two_mul hX)
  change (shortDoubleAvgAnalyticCap X X r + shortSingleBase X r*(1+Real.log (2+J)))/ternaryCandidateScale X r = _
  rw [add_div,ternary_binary_double_scale hr hX]
  change _ = 64*(ternaryDoubleAverageBudget X r+(L/((r:ℝ)/r.totient))*(1+Real.log (2+J))/J)
  conv_rhs => rw [mul_add]
  apply congrArg (fun t : ℝ => 64*ternaryDoubleAverageBudget X r+t)
  change (((r.totient:ℝ)/r)^2*(r:ℝ)*L^2*(1+Real.log (2+J)))/((X:ℝ)/(64*(r.totient:ℝ)*L)) =
    64*((L/((r:ℝ)/r.totient))*(1+Real.log (2+J))/J)
  generalize Real.log (2+J) = z
  dsimp only [J]
  field_simp

theorem ternary_candidate_active {X r : ℕ} (hr : 0<r) (hX : 2≤X) (hrX : r≤X)
    {c : ℝ} (_hc : 0<c) (hc' : c≤1/16)
    (hp : (r.totient:ℝ)≤c*Real.sqrt (X:ℝ)/Real.log (2*(X:ℝ))) : 16≤X ∧ r≤X/4 := by
  let L := Real.log (2*(X:ℝ))
  have hL : 1≤L := one_le_log_two_mul hX
  have hpos : 0<L := zero_lt_one.trans_le hL
  have ht : (1:ℝ)≤r.totient := Nat.one_le_cast.mpr (Nat.totient_pos.mpr hr)
  have ht' : (0:ℝ)<r.totient := zero_lt_one.trans_le ht
  have hs := (le_div_iff₀ hpos).mp hp
  have hcs := mul_le_mul_of_nonneg_right hc' (Real.sqrt_nonneg (X:ℝ))
  have h1 : 1≤(r.totient:ℝ)*L := one_le_mul_of_one_le_of_one_le ht hL
  have hs16 : 16≤Real.sqrt (X:ℝ) := by linarith only [h1,hs,hcs]
  have hx := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) X)
  have h16 : (16:ℝ)≤X := by nlinarith only [hs16,hx,sq_nonneg (Real.sqrt (X:ℝ)-16)]
  have hkr := div_totient_le_two_log hr
  have hlr : Real.log (2*(r:ℝ))≤L := Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hrX) (by norm_num))
  have hh := (div_le_iff₀ ht').mp (hkr.trans (mul_le_mul_of_nonneg_left hlr (by norm_num)))
  have hrem : (r:ℝ)*4≤X := by nlinarith only [hh,hs,hcs,hx,hs16,sq_nonneg (Real.sqrt (X:ℝ)-1)]
  exact ⟨by exact_mod_cast h16,(Nat.le_div_iff_mul_le (by decide : 0<4)).2 (by exact_mod_cast hrem)⟩

theorem ternary_single_inactive {X r : ℕ} (hr : 0<r) (hX : 2≤X) (hrX : r≤X)
    {c : ℝ} (hc : 0<c)
    (hp : ¬ (r.totient:ℝ)≤c*Real.sqrt (X:ℝ)/Real.log (2*(X:ℝ))) :
    1≤(2/c^2)*ternarySingleAverageBudget X r := by
  let L := Real.log (2*(X:ℝ))
  let κ := (r:ℝ)/r.totient
  let J := (X:ℝ)/((r.totient:ℝ)^2*L^2)
  have hL : 1≤L := one_le_log_two_mul hX
  have hpos : 0<L := zero_lt_one.trans_le hL
  have ht : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hr' : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have hx : (0:ℝ)<X := Nat.cast_pos.mpr (by omega)
  have hJ : 0<J := by dsimp [J]; positivity
  have hκ : 0<κ := div_pos hr' ht
  have hsx := (div_lt_iff₀ hpos).mp (lt_of_not_ge hp)
  have hs := pow_le_pow_left₀ (mul_nonneg hc.le (Real.sqrt_nonneg _)) hsx.le 2
  rw [mul_pow,Real.sq_sqrt hx.le,mul_pow] at hs
  have hj : c^2≤1/J := by
    dsimp only [J]
    rw [one_div,inv_div]
    exact (le_div_iff₀ hx).2 hs
  have ha : 1/2≤L/κ := (single_half_le_ratio_log hr hrX).trans_eq (by dsimp [L,κ]; field_simp)
  have hlog : 1≤1+Real.log (2+J) := le_add_of_nonneg_right (Real.log_nonneg (by linarith))
  have hz : 0≤ternaryDoubleAverageBudget X r := by unfold ternaryDoubleAverageBudget; positivity
  have hli : 1/2≤ (L/κ)*(1+Real.log (2+J)) := by
    have hh := mul_le_mul ha hlog (by norm_num : (0:ℝ)≤1) (div_nonneg hpos.le hκ.le)
    simpa only [mul_one] using hh
  have hh := mul_le_mul hli hj (sq_nonneg c) (by positivity : 0≤(L/κ)*(1+Real.log (2+J)))
  have hhe : c^2/2 ≤ ternarySingleAverageBudget X r := by
    change _ ≤ ternaryDoubleAverageBudget X r + (L/κ)*(1+Real.log (2+J))/J
    rw [←mul_div_assoc,mul_one] at hh
    linarith only [hh,hz]
  rw [div_mul_eq_mul_div,le_div_iff₀ (sq_pos_of_pos hc),one_mul]
  linarith

end FareyGoldbach



