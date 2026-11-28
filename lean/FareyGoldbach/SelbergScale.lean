import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Parameters in the finite sieve and absorption of four logarithmic weights -/

namespace FareyGoldbach

def sieveScaleK (J : ℕ) : ℕ := Nat.log 2 J / 320
def sieveScaleZ (J : ℕ) : ℕ := 2 ^ sieveScaleK J
def sieveScaleD (J : ℕ) : ℕ := (sieveScaleZ J)^32

set_option exponentiation.threshold 640 in
/-- Dyadic parameters, including a half power of saving on the boundary term. -/
theorem sieve_scale_bounds {J : ℕ} (hJ : 2^320 ≤ J) :
    1 ≤ sieveScaleK J ∧ (sieveScaleD J)^8 ≤ J ∧ (sieveScaleZ J)^2 ≤ J ∧
      Real.log J ≤ 640 * Real.log (sieveScaleZ J) := by
  have hjpos : 0 < J := lt_of_lt_of_le (pow_pos (by decide : 0 < 2) 320) hJ
  have hlog : 320 ≤ Nat.log 2 J := (Nat.le_log_iff_pow_le Nat.one_lt_two hjpos.ne').mpr hJ
  have hk : 1 ≤ sieveScaleK J := by unfold sieveScaleK; omega
  have hlower (n : ℕ) (hn : n ≤ Nat.log 2 J) : 2^n ≤ J :=
    (Nat.le_log_iff_pow_le (by decide) hjpos.ne').mp hn
  refine ⟨hk, ?_, ?_, ?_⟩
  · simp only [sieveScaleD, sieveScaleZ, sieveScaleK, ← pow_mul]
    apply hlower
    omega
  · simp only [sieveScaleZ, sieveScaleK, ← pow_mul]
    apply hlower
    omega
  · have hub : J ≤ (sieveScaleZ J)^640 := by
      have he : Nat.log 2 J + 1 ≤ sieveScaleK J * 640 := by
        unfold sieveScaleK at hk ⊢; omega
      calc
        _ ≤ 2^(Nat.log 2 J + 1) := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) J).le
        _ ≤ 2^(sieveScaleK J * 640) := Nat.pow_le_pow_right (by decide) he
        _ = _ := by rw [sieveScaleZ, pow_mul]
    have hr : (J : ℝ) ≤ (sieveScaleZ J : ℝ)^640 := by exact_mod_cast hub
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by exact_mod_cast hjpos) hr

/-- The error scale `D⁴` can absorb four logarithmic weights. -/
theorem sieve_scale_pow_four_le_sqrt {J : ℕ} (hJ : 2^320 ≤ J) :
    (sieveScaleD J : ℝ)^4 ≤ Real.sqrt J := by
  have h : (sieveScaleD J : ℝ)^8 ≤ J := by exact_mod_cast (sieve_scale_bounds hJ).2.1
  apply Real.le_sqrt_of_sq_le
  simpa only [← pow_mul] using h

theorem sieve_scale_pow_four_le {J : ℕ} (hJ : 2^320 ≤ J) : (sieveScaleD J)^4 ≤ J := by
  have hd : 0 < sieveScaleD J := by unfold sieveScaleD sieveScaleZ; positivity
  exact (Nat.pow_le_pow_right hd (by decide : 4 ≤ 8)).trans (sieve_scale_bounds hJ).2.1

theorem sieve_scale_z_le_sqrt {J : ℕ} (hJ : 2^320 ≤ J) :
    (sieveScaleZ J : ℝ) ≤ Real.sqrt J := by
  exact Real.le_sqrt_of_sq_le (by exact_mod_cast (sieve_scale_bounds hJ).2.2.1)

/-- On the scale `Y ≤ 4J²`, all four logarithmic weights are controlled by `log J`. -/
theorem sieve_log_two_mul_le {Y J : ℕ} (hJ : 2 ≤ J) (hY : Y ≤ 4 * J^2) :
    Real.log (2 * (Y : ℝ)) ≤ 5 * Real.log J := by
  have hj : (2 : ℝ) ≤ J := by exact_mod_cast hJ
  have hjpos : 0 < (J : ℝ) := by linarith
  have hjlog : Real.log (2 : ℝ) ≤ Real.log J := Real.log_le_log (by norm_num) hj
  by_cases h : Y = 0
  · subst Y
    simp only [Nat.cast_zero, mul_zero, Real.log_zero]
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith : 1 ≤ (J : ℝ)))
  have hyr : 0 < (Y : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
  have hy : (Y : ℝ) ≤ 4 * (J : ℝ)^2 := by exact_mod_cast hY
  have hlog := Real.log_le_log (show 0 < 2 * (Y : ℝ) by positivity)
    (show 2 * (Y : ℝ) ≤ (2 : ℝ)^3 * (J : ℝ)^2 by nlinarith)
  rw [Real.log_mul (x := (2 : ℝ)^3) (y := (J : ℝ)^2) (by positivity) (by positivity),
    Real.log_pow, Real.log_pow] at hlog
  norm_num at hlog
  linarith

/-- Explicit comparison against the fourth Taylor coefficient of the exponential. -/
theorem sieve_log_two_mul_pow_four_le {Y J : ℕ} (hJ : 2 ≤ J) (hY : Y ≤ 4 * J^2) :
    Real.log (2 * (Y : ℝ))^4 ≤ 240000 * Real.sqrt J := by
  have hj : (2 : ℝ) ≤ J := by exact_mod_cast hJ
  have hjpos : 0 < (J : ℝ) := by linarith
  have hlog : 0 ≤ Real.log (J : ℝ) := Real.log_nonneg (by linarith)
  have hpos : 0 ≤ Real.log (2 * (Y : ℝ)) := by
    by_cases h : Y = 0
    · simp [h]
    · have hy : 1 ≤ (Y : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
      exact Real.log_nonneg (by linarith)
  have h4 : Real.log (2 * (Y : ℝ))^4 ≤ (5 * Real.log (J : ℝ))^4 := by
    gcongr
    exact sieve_log_two_mul_le hJ hY
  have ht := Real.pow_div_factorial_le_exp (Real.log (J : ℝ) / 2) (by linarith) 4
  rw [Real.exp_half, Real.exp_log hjpos] at ht
  norm_num [Nat.factorial] at ht
  nlinarith

/-- Pass between the real class length and the integer side of the sieve cube. -/
theorem sieve_class_scales {Y r : ℕ} (hr : 0 < r) (hYr : r ≤ Y)
    (hbal : (r : ℝ) ≤ 4 * ((Y : ℝ) / r)) :
    2 ≤ Y / r + 1 ∧ ((Y / r + 1 : ℕ) : ℝ) ≤ 2 * ((Y : ℝ) / r) ∧
      Y ≤ 4 * (Y / r + 1)^2 := by
  let J := Y / r + 1
  have hrp : 0 < (r : ℝ) := by exact_mod_cast hr
  have hH : (1 : ℝ) ≤ (Y : ℝ) / r := (one_le_div hrp).mpr (by exact_mod_cast hYr)
  have hJH : (J : ℝ) ≤ 2 * ((Y : ℝ) / r) := by
    have hfloor : ((Y / r : ℕ) : ℝ) ≤ (Y : ℝ) / r := Nat.cast_div_le
    dsimp only [J]
    push_cast
    linarith
  have hHJ : (Y : ℝ) / r ≤ J := by
    apply (div_le_iff₀ hrp).mpr
    have hm := Nat.mod_add_div Y r
    have hrem := Nat.mod_lt Y hr
    rw [Nat.mul_comm r] at hm
    have hnum : Y ≤ J * r := by dsimp [J]; rw [Nat.add_mul, Nat.one_mul]; omega
    exact_mod_cast hnum
  refine ⟨by have := Nat.div_pos hYr hr; omega, hJH, ?_⟩
  change Y ≤ 4 * J^2
  exact_mod_cast (calc
    (Y : ℝ) = (Y / (r : ℝ)) * r := (div_mul_cancel₀ (Y : ℝ) hrp.ne').symm
    _ ≤ (J : ℝ) * (4 * J) := mul_le_mul hHJ (by linarith) hrp.le (Nat.cast_nonneg _)
    _ = 4 * (J : ℝ)^2 := by ring)

set_option exponentiation.threshold 320 in
/-- The entire range below the first full sieve scale has a uniform logarithmic cost. -/
theorem sieve_log_small_scale {Y J : ℕ} (hJ : 2 ≤ J) (hY : Y ≤ 4 * J^2)
    (hSmall : J < 2^320) : Real.log (2 * (Y : ℝ)) ≤ 1600 * Real.log 2 := by
  have hj : 0 < (J : ℝ) := by exact_mod_cast (show 0 < J by omega)
  have hcast : (J : ℝ) ≤ (2 : ℝ)^320 := by exact_mod_cast hSmall.le
  have hlog := Real.log_le_log hj hcast
  rw [Real.log_pow] at hlog
  norm_num at hlog
  linarith [sieve_log_two_mul_le hJ hY]

end FareyGoldbach
