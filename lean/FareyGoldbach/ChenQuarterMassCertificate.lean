import FareyGoldbach.ChenSwitchingCell

/-! # Rational endpoint certificates for quarter-cutoff switching -/

open Filter Finset Set
open scoped Topology

namespace FareyGoldbach

private def oddLower {K : Type*} [Field K] (t : K) : K :=
  2 * (t + t^3/3 + t^5/5)

private def oddUpper {K : Type*} [Field K] (t : K) : K :=
  oddLower t + 2*(t^7/(7*(1-t^2)))

private theorem log_ratio_deriv (t : ℝ) (ht₀ : 0≤t) (ht₁ : t<1) :
    HasDerivAt (fun s : ℝ => Real.log ((1+s)/(1-s))) (2/(1-t^2)) t := by
  have hid : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have h₁ : 1-t ≠ 0 := by linarith
  have h₂ : 1+t ≠ 0 := by linarith
  have h₃ : 1-t^2 ≠ 0 := by
    rw [show 1-t^2=(1-t)*(1+t) by ring]
    exact mul_ne_zero h₁ h₂
  convert ((hid.const_add 1).div (hid.const_sub 1) h₁).log (div_ne_zero h₂ h₁) using 1
  dsimp
  field_simp [h₁,h₂,h₃]
  ring

private theorem odd_lower_deriv (t : ℝ) :
    HasDerivAt oddLower (2*(1+t^2+t^4)) t := by
  have hid : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  convert (((hid.add ((hid.pow 3).div_const 3)).add ((hid.pow 5).div_const 5)).const_mul 2)
    using 1 <;> first | rfl | ring

private theorem nonnegative_of_deriv {f g : ℝ → ℝ}
    (h : ∀ t, 0≤t → t<1 → HasDerivAt f (g t) t)
    (hg : ∀ t, 0≤t → t<1 → 0≤g t) (hf : f 0=0)
    {t : ℝ} (ht₀ : 0≤t) (ht₁ : t<1) : 0≤f t := by
  have hm : MonotoneOn f (Set.Ico 0 1) := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
    (fun s hs => (h s hs.1 hs.2).continuousAt.continuousWithinAt)
    (fun s hs => let hs' := interior_subset hs; (h s hs'.1 hs'.2).hasDerivWithinAt)
    (fun s hs => let hs' := interior_subset hs; hg s hs'.1 hs'.2)
  simpa only [hf] using hm (show (0:ℝ) ∈ Set.Ico 0 1 from ⟨le_rfl, zero_lt_one⟩) ⟨ht₀,ht₁⟩ ht₀

private theorem ratio_log_bounds {t : ℝ} (ht₀ : 0≤t) (ht₁ : t<1) :
    oddLower t ≤ Real.log ((1+t)/(1-t)) ∧ Real.log ((1+t)/(1-t)) ≤ oddUpper t := by
  have hden (s : ℝ) (hs₀ : 0≤s) (hs₁ : s<1) : 0 < 1-s^2 := by
    rw [show 1-s^2=(1-s)*(1+s) by ring]
    exact mul_pos (by linarith) (by linarith)
  constructor
  · apply sub_nonneg.mp
    refine nonnegative_of_deriv (f:=fun s => Real.log ((1+s)/(1-s)) - oddLower s)
      (g:=fun s => 2*s^6/(1-s^2)) (fun s hs₀ hs₁ => ?_)
      (fun s hs₀ hs₁ => div_nonneg (by positivity) (hden s hs₀ hs₁).le) ?_ ht₀ ht₁
    · convert (log_ratio_deriv s hs₀ hs₁).sub (odd_lower_deriv s) using 1
      field_simp [(hden s hs₀ hs₁).ne']
      ring
    · norm_num [oddLower]
  · apply sub_nonneg.mp
    refine nonnegative_of_deriv (f:=fun s => oddUpper s - Real.log ((1+s)/(1-s)))
      (g:=fun s => 4*s^8/(7*(1-s^2)^2)) (fun s hs₀ hs₁ => ?_)
      (fun s hs₀ _ => by positivity) ?_ ht₀ ht₁
    · have hid : HasDerivAt (fun x : ℝ => x) 1 s := hasDerivAt_id s
      have hd₀ := (hden s hs₀ hs₁).ne'
      have hd₁ : 7*(1-s^2) ≠ 0 := mul_ne_zero (by norm_num) hd₀
      have htail := (((hid.pow 7).div (((hid.pow 2).const_sub 1).const_mul 7) hd₁).const_mul 2)
      convert ((odd_lower_deriv s).add htail).sub (log_ratio_deriv s hs₀ hs₁) using 1 <;>
        first | rfl | (norm_num only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, mul_one]; field_simp [hd₀,hd₁]; ring)
    · norm_num [oddUpper,oddLower]

/-- Three odd terms and a geometric remainder bound for the real logarithm. -/
theorem chen_quarter_log_bounds {x : ℝ} (hx : 1≤x) :
    let t := (x-1)/(x+1)
    2*(t+t^3/3+t^5/5) ≤ Real.log x ∧
      Real.log x ≤ 2*(t+t^3/3+t^5/5) + 2*(t^7/(7*(1-t^2))) := by
  dsimp only
  let t := (x-1)/(x+1)
  have hx₀ : 0<x+1 := by linarith
  have ht₀ : 0≤t := div_nonneg (by linarith) hx₀.le
  have ht₁ : t<1 := (div_lt_iff₀ hx₀).mpr (by linarith)
  have h := ratio_log_bounds ht₀ ht₁
  have hr : (1+t)/(1-t)=x := by
    apply (div_eq_iff (by linarith : 1-t≠0)).mpr
    dsimp [t]
    field_simp
    ring
  simpa only [hr,oddLower,oddUpper] using h

/-- The fixed 128-cell rational grid between two first-prime exponent bounds. -/
def chenQuarterGrid (A B : ℚ) (i : ℕ) : ℚ :=
  A + (i:ℚ)*((B-A)/128)

private def boxUpper {K : Type*} [Field K] (a b c : K) : K :=
  let θ := 1-b
  let d := (1-a)/2+1/100000
  let x := (d/(θ-d))/(c/(θ-c))
  ((b-a)/a)*(oddUpper ((x-1)/(x+1))/θ)

/-- Round one exponent cell's mass coefficient upward to millionths. -/
def chenQuarterBoxUpperRounded (A B : ℚ) (c : ℚ → ℚ) (i : ℕ) : ℕ :=
  ⌈1000000*boxUpper (chenQuarterGrid A B i) (chenQuarterGrid A B (i+1)) (c (chenQuarterGrid A B i))⌉₊

theorem chen_quarter_box_sum_30 :
    (∑ i ∈ range 128, chenQuarterBoxUpperRounded (1/4) (1/3) id i) = 148754 := by
  decide +kernel

theorem chen_quarter_box_sum_31 :
    (∑ i ∈ range 128, chenQuarterBoxUpperRounded (4/25) (1/4) (fun _ => 1/4) i) = 439737 := by
  decide +kernel

/-- The logarithmic coefficient of one box is bounded by its rounded rational certificate. -/
theorem chen_quarter_box_coeff_le_rounded (A B : ℚ) (c : ℚ → ℚ) (i : ℕ)
    (ha : (0:ℝ) < (chenQuarterGrid A B i:ℝ))
    (hab : (chenQuarterGrid A B i:ℝ) ≤ (chenQuarterGrid A B (i+1):ℝ))
    (hb : (chenQuarterGrid A B (i+1):ℝ) ≤ 1/3)
    (hc : (0:ℝ) < (c (chenQuarterGrid A B i):ℝ))
    (hcd : (c (chenQuarterGrid A B i):ℝ) <
      chenSwitchCap (chenQuarterGrid A B i:ℝ) (1/100000)) :
    let a : ℝ := chenQuarterGrid A B i
    let b : ℝ := chenQuarterGrid A B (i+1)
    let c' : ℝ := c (chenQuarterGrid A B i)
    let θ := 1-b
    let d := chenSwitchCap a (1/100000)
    (Real.log b - Real.log a)*(Real.log ((d/(θ-d))/(c'/(θ-c'))) / θ)
      ≤ (chenQuarterBoxUpperRounded A B c i:ℝ)/1000000 := by
  let a : ℝ := chenQuarterGrid A B i
  let b : ℝ := chenQuarterGrid A B (i+1)
  let c' : ℝ := c (chenQuarterGrid A B i)
  let θ := 1-b
  let d := chenSwitchCap a (1/100000)
  let x := (d/(θ-d))/(c'/(θ-c'))
  have hθ : 0<θ := by dsimp [θ,b]; linarith
  have hdθ : d<θ := by dsimp [θ,d,chenSwitchCap,a,b]; linarith
  have hcd' : c'<d := hcd
  have hc' : 0<c' := hc
  have hx : 1≤x := by
    have hpos : 0<c'/(θ-c') := div_pos hc' (by linarith)
    apply (le_div_iff₀ hpos).mpr
    rw [one_mul]
    exact div_le_div₀ (hc'.le.trans hcd'.le) hcd'.le (by linarith) (by linarith)
  have hb' : 0<b := ha.trans_le hab
  have hlog := Real.log_le_sub_one_of_pos (div_pos hb' ha)
  rw [Real.log_div hb'.ne' ha.ne'] at hlog
  have hlog' : Real.log b - Real.log a ≤ (b-a)/a := by
    rw [sub_div,div_self ha.ne']
    exact hlog
  have hOdd := (chen_quarter_log_bounds hx).2
  have hcoeff : (Real.log b - Real.log a)*(Real.log x / θ) ≤ boxUpper a b c' :=
    mul_le_mul hlog' (div_le_div_of_nonneg_right hOdd hθ.le)
      (div_nonneg (Real.log_nonneg hx) hθ.le) (div_nonneg (sub_nonneg.mpr hab) ha.le)
  calc
    _ ≤ boxUpper a b c' := hcoeff
    _ ≤ _ := by
      apply (le_div_iff₀ (by norm_num : (0:ℝ)<1000000)).mpr
      rw [mul_comm]
      have h := Nat.le_ceil (1000000 * boxUpper (chenQuarterGrid A B i)
        (chenQuarterGrid A B (i+1)) (c (chenQuarterGrid A B i)))
      have h' : ((1000000 * boxUpper (chenQuarterGrid A B i)
            (chenQuarterGrid A B (i+1)) (c (chenQuarterGrid A B i)):ℚ):ℝ) ≤
          (chenQuarterBoxUpperRounded A B c i:ℝ) := by exact_mod_cast h
      simpa only [boxUpper, a, b, c', oddUpper, oddLower, Rat.cast_add, Rat.cast_sub, Rat.cast_mul,
        Rat.cast_div, Rat.cast_pow, Rat.cast_one, Rat.cast_ofNat] using h'

end FareyGoldbach
