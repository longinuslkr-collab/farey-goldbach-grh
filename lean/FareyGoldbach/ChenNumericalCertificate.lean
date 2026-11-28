module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # A rational upper bound for the switching integral in Chen's sieve -/

public section

open MeasureTheory Set

namespace FareyGoldbach

private def polyFour {K : Type*} [Field K] (v : K) : K := v-v^2/2+v^3/3-v^4/4
private def polyFive {K : Type*} [Field K] (v : K) : K := polyFour v+v^5/5

private theorem polyFour_deriv (x : ℝ) :
    HasDerivAt polyFour (1-x+x^2-x^3) x := by
  have h : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
  convert (((h.sub ((h.pow 2).div_const 2)).add ((h.pow 3).div_const 3)).sub
    ((h.pow 4).div_const 4)) using 1 <;> first | rfl | ring

private theorem zero_le_of_deriv {f g : ℝ → ℝ}
    (h : ∀ t, 0≤t → HasDerivAt f (g t) t) (hg : ∀ t, 0≤t → 0≤g t) (hf : f 0=0)
    {x : ℝ} (hx : 0≤x) : 0≤f x := by
  have hm : MonotoneOn f (Ici 0) := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (fun t ht => (h t ht).continuousAt.continuousWithinAt)
    (fun t ht => (h t (interior_subset ht)).hasDerivWithinAt)
    (fun t ht => hg t (interior_subset ht))
  simpa only [hf] using hm (show (0:ℝ)∈Ici 0 from le_rfl) hx hx

private theorem log_poly_bounds {v : ℝ} (hv : 0≤v) :
    polyFour v ≤ Real.log (1+v) ∧ Real.log (1+v) ≤ polyFive v := by
  have hd (t : ℝ) (ht : 0≤t) :
      HasDerivAt (fun s : ℝ => Real.log (1+s)) (1/(1+t)) t := by
    simpa only [zero_add,Pi.add_apply,id_eq] using (((hasDerivAt_const t (1:ℝ)).add
      (hasDerivAt_id t)).log (by dsimp; linarith))
  constructor
  · apply sub_nonneg.mp
    refine zero_le_of_deriv (f:=fun t => Real.log (1+t)-polyFour t) (g:=fun t => t^4/(1+t))
      (fun t ht => ?_) (fun t ht => by positivity) ?_ hv
    · convert (hd t ht).sub (polyFour_deriv t) using 1
      field_simp [show 1+t≠0 by linarith]
      ring
    · norm_num [polyFour]
  · apply sub_nonneg.mp
    refine zero_le_of_deriv (f:=fun t => polyFive t-Real.log (1+t)) (g:=fun t => t^5/(1+t))
      (fun t ht => ?_) (fun t ht => by positivity) ?_ hv
    · have hid : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
      convert ((polyFour_deriv t).add ((hid.pow 5).div_const 5)).sub (hd t ht) using 1 <;>
        first | rfl | (field_simp [show 1+t≠0 by linarith]; ring)
    · norm_num [polyFive,polyFour]

/-- The sixth alternating partial sum bounds the logarithm from below for nonnegative arguments. -/
theorem chen_log_lower_six {x : ℝ} (hx : 0≤x) :
    x-x^2/2+x^3/3-x^4/4+x^5/5-x^6/6 ≤ Real.log (1+x) := by
  apply sub_nonneg.mp
  apply zero_le_of_deriv (g:=fun t => t^6/(1+t)) _ (fun t ht => by positivity) _ hx
  · intro t ht
    have hid : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id _
    have hd : HasDerivAt (fun s : ℝ => Real.log (1+s)) (1/(1+t)) t := by
      simpa only [zero_add,Pi.add_apply,id_eq] using (((hasDerivAt_const t (1:ℝ)).add
        (hasDerivAt_id t)).log (by dsimp; linarith))
    convert hd.sub (((polyFour_deriv t).add ((hid.pow 5).div_const 5)).sub
      ((hid.pow 6).div_const 6)) using 1 <;>
      first | rfl | (field_simp [show 1+t≠0 by linarith]; ring)
  · norm_num

private def gridPoint (w : ℚ) (i : ℕ) : ℚ := 1/8+(i:ℚ)*w

private def gridArea (w : ℚ) (i : ℕ) : ℚ :=
  w*polyFive (1-3*gridPoint w i)/(gridPoint w i*(1-gridPoint w i))

/-- Rational rectangular area on the original 48-cell grid. -/
def chenGridArea (i : ℕ) : ℚ := gridArea (5/1152) i

/-- Rational rectangular area on the refined 192-cell grid. -/
def chenGridAreaRefined (i : ℕ) : ℚ := gridArea (5/4608) i

/-- Upper roundings to millionths, all computed using exact rational arithmetic. -/
theorem chen_grid_ceiling_sum :
    (∑ i ∈ Finset.range 48, ⌈(1000000:ℚ)*chenGridArea i⌉₊) = 374518 := by
  decide +kernel

theorem chen_grid_ceiling_sum_refined :
    (∑ i ∈ Finset.range 192, ⌈(1000000:ℚ)*chenGridAreaRefined i⌉₊) = 367226 := by
  decide +kernel

private noncomputable def grid (w : ℚ) (i : ℕ) : ℝ := 1/8+(i:ℝ)*(w:ℝ)
private noncomputable def integrand (u : ℝ) : ℝ := Real.log (2-3*u)/(u*(1-u))

/-- Chen's integral after doing the inner integration over the two larger prime factors. -/
@[expose] noncomputable def chenSwitchIntegral : ℝ :=
  ∫ u in (1/8:ℝ)..1/3, Real.log (2-3*u)/(u*(1-u))

private theorem grid_bounds {w : ℚ} {n i : ℕ} (hw : 0≤(w:ℝ)) (hend : (n:ℝ)*(w:ℝ)=5/24)
    (hi : i<n) : 1/8 ≤ grid w i ∧ grid w i ≤ grid w (i+1) ∧ grid w (i+1) ≤ 1/3 := by
  have hie : ((i+1:ℕ):ℝ) ≤ n := by exact_mod_cast hi
  have hle := mul_le_mul_of_nonneg_right hie hw
  have h₀ := mul_nonneg (Nat.cast_nonneg (α:=ℝ) i) hw
  dsimp only [grid]
  push_cast at *
  exact ⟨by linarith, by nlinarith, by linarith⟩

private theorem cell_integrable {w : ℚ} {n i : ℕ} (hw : 0≤(w:ℝ))
    (hend : (n:ℝ)*(w:ℝ)=5/24) (hi : i<n) :
    IntervalIntegrable integrand volume (grid w i) (grid w (i+1)) := by
  obtain ⟨ha,hab,hb⟩ := grid_bounds hw hend hi
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro t ht
  have ht₁ := ha.trans ht.1
  have ht₂ := ht.2.trans hb
  change ContinuousWithinAt (fun u : ℝ => Real.log (2-3*u)/(u*(1-u))) _ t
  fun_prop (disch := first | positivity | apply mul_ne_zero <;> linarith | linarith)

private theorem cell_le {w : ℚ} {n i : ℕ} (hw : 0≤(w:ℝ))
    (hend : (n:ℝ)*(w:ℝ)=5/24) (hi : i<n) :
    (∫ t in grid w i..grid w (i+1), integrand t) ≤ (gridArea w i:ℝ) := by
  let a := grid w i
  let v := 1-3*a
  let U := polyFive v/(a*(1-a))
  obtain ⟨ha,hab,hb⟩ := grid_bounds hw hend hi
  have hpos : 0<a := by dsimp [a]; linarith
  have hahi : a≤1/3 := hab.trans hb
  have hda : 0<a*(1-a) := mul_pos hpos (by linarith)
  have hlog : Real.log (2-3*a) ≤ polyFive v := by
    rw [show 2-3*a=1+v by dsimp [v]; ring]
    exact (log_poly_bounds (by dsimp [v]; linarith)).2
  have hpoly : 0≤polyFive v := (Real.log_nonneg (by linarith : 1≤2-3*a)).trans hlog
  have hm (t : ℝ) (ht : t∈Icc (grid w i) (grid w (i+1))) : integrand t ≤ U := by
    have hta : a≤t := ht.1
    have ht₃ := ht.2.trans hb
    have hd : a*(1-a) ≤ t*(1-t) := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hta) (show 0≤1-t-a by linarith)]
    have hn := Real.log_le_log (by linarith : 0<2-3*t) (show 2-3*t≤2-3*a by linarith)
    exact div_le_div₀ hpoly (hn.trans hlog) hda hd
  have huc : Continuous (fun _ : ℝ => U) := continuous_const
  have hcomp := intervalIntegral.integral_mono_on hab (cell_integrable hw hend hi)
    (huc.intervalIntegrable (grid w i) (grid w (i+1))) hm
  rw [intervalIntegral.integral_const,smul_eq_mul] at hcomp
  convert hcomp using 1
  dsimp [gridArea,gridPoint,grid,U,v,a,polyFive,polyFour]
  push_cast
  ring

private theorem integral_le_grid {w : ℚ} {n : ℕ} (hw : 0≤(w:ℝ))
    (hend : (n:ℝ)*(w:ℝ)=5/24) :
    chenSwitchIntegral ≤ ((∑ i ∈ Finset.range n, ⌈(1000000:ℚ)*gridArea w i⌉₊ : ℕ):ℝ)/1000000 := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a:=grid w) (n:=n)
    (fun _ hi => cell_integrable hw hend hi)
  have h0 : grid w 0=1/8 := by simp [grid]
  have hn : grid w n=1/3 := by dsimp only [grid]; rw [hend]; norm_num
  rw [h0,hn] at hsum
  calc
    chenSwitchIntegral = ∑ i ∈ Finset.range n, ∫ t in grid w i..grid w (i+1), integrand t := hsum.symm
    _ ≤ ∑ i ∈ Finset.range n, (((⌈(1000000:ℚ)*gridArea w i⌉₊:ℕ):ℝ)/1000000) := by
      apply Finset.sum_le_sum
      intro i hi
      refine (cell_le hw hend (Finset.mem_range.mp hi)).trans ?_
      have h := Nat.le_ceil ((1000000:ℚ)*gridArea w i)
      apply (le_div_iff₀ (by norm_num)).2
      rw [mul_comm]
      exact_mod_cast h
    _ = _ := by rw [←Finset.sum_div,←Nat.cast_sum]

theorem chenSwitchIntegral_le : chenSwitchIntegral ≤ 374518/1000000 := by
  have h := integral_le_grid (n:=48) (w:=5/1152) (by norm_num) (by norm_num)
  change chenSwitchIntegral ≤ ((∑ i ∈ Finset.range 48, ⌈(1000000:ℚ)*chenGridArea i⌉₊ : ℕ):ℝ)/1000000 at h
  simpa only [chen_grid_ceiling_sum,Nat.cast_ofNat] using h

theorem chenSwitchIntegral_le_refined : chenSwitchIntegral ≤ 367226/1000000 := by
  have h := integral_le_grid (n:=192) (w:=5/4608) (by norm_num) (by norm_num)
  change chenSwitchIntegral ≤ ((∑ i ∈ Finset.range 192, ⌈(1000000:ℚ)*chenGridAreaRefined i⌉₊ : ℕ):ℝ)/1000000 at h
  simpa only [chen_grid_ceiling_sum_refined,Nat.cast_ofNat] using h

/-- A simple strictly larger rational bound for Chen's switching integral. -/
theorem chenSwitchIntegral_lt_three_eighths : chenSwitchIntegral < 3/8 := by
  linarith only [chenSwitchIntegral_le]

/-- The first four alternating terms suffice for the lower logarithmic bound. -/
theorem chen_log_three_halves_gt_two_fifths : (2:ℝ)/5 < Real.log (3/2) := by
  have h := (log_poly_bounds (by norm_num : (0:ℝ)≤1/2)).1
  norm_num [polyFour] at h
  linarith only [h]

/-- The normalized sieve coefficient in its shorter logarithmic form. -/
theorem chen_main_coefficient_eq :
    4*Real.log 3-2*Real.log 6-2*chenSwitchIntegral =
      2*Real.log (3/2)-2*chenSwitchIntegral := by
  have h6 : Real.log 6=Real.log 3+Real.log 2 := by
    rw [←Real.log_mul (by norm_num : (3:ℝ)≠0) (by norm_num : (2:ℝ)≠0)]
    norm_num
  rw [h6,Real.log_div (by norm_num : (3:ℝ)≠0) (by norm_num : (2:ℝ)≠0)]
  ring

/-- The lower-sieve coefficient exceeds the switching loss by more than one twentieth. -/
theorem chen_numerical_margin :
    (1:ℝ)/20 < 4*Real.log 3-2*Real.log 6-2*chenSwitchIntegral := by
  rw [chen_main_coefficient_eq]
  linarith only [chen_log_three_halves_gt_two_fifths,chenSwitchIntegral_le]

end FareyGoldbach
