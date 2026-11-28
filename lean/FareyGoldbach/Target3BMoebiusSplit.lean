import FareyGoldbach.Defs

open scoped BigOperators
open ArithmeticFunction

namespace Target3B

def moebiusAtMost (R : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n ≤ R then moebius n else 0, by simp⟩

def moebiusAbove (R : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if R < n then moebius n else 0, by simp⟩

@[simp] theorem moebiusAtMost_apply (R n : ℕ) :
    moebiusAtMost R n = if n ≤ R then moebius n else 0 := rfl

@[simp] theorem moebiusAbove_apply (R n : ℕ) :
    moebiusAbove R n = if R < n then moebius n else 0 := rfl

private theorem moebiusAbove_eq_sub (R : ℕ) :
    moebiusAbove R = moebius - moebiusAtMost R := by
  ext n
  by_cases h : n ≤ R
  · simp [h, Nat.not_lt.2 h]
  · simp [h, Nat.lt_of_not_ge h]

/-- Double-cutoff Möbius identity in the Dirichlet convolution ring. -/
theorem moebius_two_cutoffs (R S : ℕ) :
    moebius = moebiusAtMost R + moebiusAtMost S
      - (moebiusAtMost R * moebiusAtMost S) * (↑zeta : ArithmeticFunction ℤ)
      + (moebiusAbove R * moebiusAbove S) * (↑zeta : ArithmeticFunction ℤ) := by
  let u := moebiusAtMost R
  let v := moebiusAtMost S
  let z : ArithmeticFunction ℤ := ↑zeta
  have hz : moebius * z = 1 := moebius_mul_coe_zeta
  rw [moebiusAbove_eq_sub, moebiusAbove_eq_sub]
  change moebius = u + v - (u * v) * z + ((moebius - u) * (moebius - v)) * z
  calc
    moebius = u + v - moebius * z * (u + v) + moebius * z * moebius := by
      rw [hz]
      ring
    _ = u + v - (u * v) * z + ((moebius - u) * (moebius - v)) * z := by ring

/-- Exact finite Type I and Type II decomposition for inputs above both cutoffs. -/
theorem moebius_finite_split {n R S : ℕ} (hR : R < n) (hS : S < n) :
    moebius n =
      -(∑ d ∈ n.divisors, ∑ p ∈ d.divisorsAntidiagonal,
          moebiusAtMost R p.1 * moebiusAtMost S p.2)
      + ∑ p ∈ n.divisorsAntidiagonal,
          moebiusAbove R p.1 * ∑ d ∈ p.2.divisors, moebiusAbove S d := by
  have typeI :
      ((moebiusAtMost R * moebiusAtMost S) * (↑zeta : ArithmeticFunction ℤ)) n =
        ∑ d ∈ n.divisors, ∑ p ∈ d.divisorsAntidiagonal,
          moebiusAtMost R p.1 * moebiusAtMost S p.2 := by
    rw [coe_mul_zeta_apply]
    simp only [ArithmeticFunction.mul_apply]
  have typeII :
      ((moebiusAbove R * moebiusAbove S) * (↑zeta : ArithmeticFunction ℤ)) n =
        ∑ p ∈ n.divisorsAntidiagonal,
          moebiusAbove R p.1 * ∑ d ∈ p.2.divisors, moebiusAbove S d := by
    rw [mul_assoc, ArithmeticFunction.mul_apply]
    simp only [coe_mul_zeta_apply]
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) (moebius_two_cutoffs R S)
  have lowR : moebiusAtMost R n = 0 := by simp [Nat.not_le_of_lt hR]
  have lowS : moebiusAtMost S n = 0 := by simp [Nat.not_le_of_lt hS]
  simpa only [add_apply, sub_apply, lowR, lowS, zero_add, zero_sub, typeI, typeII] using h

theorem typeI_vanish_of_mul_cutoffs_lt {R S d : ℕ} (hd : R * S < d) :
    (moebiusAtMost R * moebiusAtMost S) d = 0 := by
  rw [ArithmeticFunction.mul_apply]
  refine Finset.sum_eq_zero fun p hp => ?_
  by_cases hR : p.1 ≤ R
  · have hS : ¬p.2 ≤ S := by
      intro hS
      apply Nat.not_le_of_lt hd
      rw [← (Nat.mem_divisorsAntidiagonal.mp hp).1]
      exact Nat.mul_le_mul hR hS
    simp [hS]
  · simp [hR]

theorem typeII_tail_vanish_of_le_cutoff {S n : ℕ} (hn : n ≤ S) :
    (∑ d ∈ n.divisors, moebiusAbove S d) = 0 := by
  refine Finset.sum_eq_zero fun d hd => ?_
  obtain ⟨hdvd, hn0⟩ := Nat.mem_divisors.mp hd
  have h : d ≤ S := (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd).trans hn
  simp [Nat.not_lt_of_ge h]

def truncation (x j : ℚ) : ℚ := (x - j) / 5
def transition (x j : ℚ) : ℚ := (x - j) / 3
def bottleneck (x j : ℚ) : ℚ := (10 * j - x) / 12

/-- Nine normalized branch exponents for the `9/19` elementary fourth-moment ledger. -/
def exponents (x j r t : ℚ) : Fin 9 → ℚ :=
  ![j - x, j + 2*r - x/2, (j-r)/2, j - x/2, j + t/2 - x/4,
    (3*j - x/2)/4, (3*j-t)/4, j - x/4, j - x/4]

theorem cuts_in_range {x j : ℚ} (hj : 0 ≤ j) (hx : 10*j < x) :
    0 < truncation x j ∧ truncation x j < transition x j ∧ transition x j < x/2 := by
  unfold truncation transition
  exact ⟨by linarith, by linarith, by linarith⟩

theorem typeI_scale {x j r d : ℚ} (hd : d ≤ 2*r) :
    j + d - x/2 ≤ exponents x j r 0 1 := by
  simp [exponents]
  linarith

theorem typeII_completion_scales {x j r t s : ℚ} (hr : r ≤ s) (ht : s ≤ t) :
    (j-s)/2 ≤ exponents x j r t 2 ∧
    j - x/2 = exponents x j r t 3 ∧
    j + s/2 - x/4 ≤ exponents x j r t 4 := by
  simp [exponents]
  exact ⟨by linarith, by linarith⟩

theorem typeII_fourth_scales {x j r t s : ℚ} (ht : t ≤ s) (hs : s ≤ x/2) :
    (3*j-(x-s))/4 ≤ exponents x j r t 5 ∧
    (3*j-s)/4 ≤ exponents x j r t 6 ∧
    (3*j-(x-s))/4 + (j+s-x)/4 ≤ exponents x j r t 7 ∧
    (3*j-s)/4 + (j+s-x)/4 = exponents x j r t 8 := by
  simp [exponents]
  exact ⟨by linarith, by linarith, by linarith, by ring⟩

theorem every_row_le_bottleneck {x jTop j : ℚ} (hj : 0 ≤ jTop) (hx : 10*jTop ≤ x)
    (hle : j ≤ jTop) (i : Fin 9) :
    exponents x j (truncation x jTop) (transition x jTop) i ≤ bottleneck x jTop := by
  fin_cases i <;> simp [exponents, truncation, transition, bottleneck] <;> linarith

theorem every_row_strict {x jTop j : ℚ} (hj : 0 ≤ jTop) (hx : 10*jTop < x)
    (hle : j ≤ jTop) (i : Fin 9) :
    exponents x j (truncation x jTop) (transition x jTop) i < 0 := by
  refine lt_of_le_of_lt (every_row_le_bottleneck hj hx.le hle i) ?_
  unfold bottleneck
  linarith

theorem sum_rows_strict {x jTop j : ℚ} (hj : 0 ≤ jTop) (hx : 10*jTop < x)
    (hle : j ≤ jTop) :
    (∑ i, exponents x j (truncation x jTop) (transition x jTop) i) < 0 := by
  calc
    (∑ i, exponents x j (truncation x jTop) (transition x jTop) i)
        ≤ ∑ _i : Fin 9, bottleneck x jTop :=
          Finset.sum_le_sum (fun i _ => every_row_le_bottleneck hj hx.le hle i)
    _ < 0 := by simp [bottleneck]; linarith

theorem transition_optimal (x j t : ℚ) :
    bottleneck x j ≤ max (j + t/2 - x/4) ((3*j-t)/4) := by
  have h1 := le_max_left (j + t/2 - x/4) ((3*j-t)/4)
  have h2 := le_max_right (j + t/2 - x/4) ((3*j-t)/4)
  unfold bottleneck
  linarith

theorem truncation_optimal (x j r : ℚ) :
    (6*j-x)/10 ≤ max (j + 2*r - x/2) ((j-r)/2) := by
  have h1 := le_max_left (j + 2*r - x/2) ((j-r)/2)
  have h2 := le_max_right (j + 2*r - x/2) ((j-r)/2)
  linarith

theorem truncation_attains (x j : ℚ) :
    j + 2 * truncation x j - x/2 = (6*j-x)/10 ∧
    (j-truncation x j)/2 = (6*j-x)/10 := by
  constructor <;> unfold truncation <;> ring

theorem transition_attains (x j : ℚ) :
    j + transition x j / 2 - x/4 = bottleneck x j ∧
    (3*j-transition x j)/4 = bottleneck x j := by
  constructor <;> unfold transition bottleneck <;> ring

theorem threshold (theta : ℚ) :
    10*(1-2*theta) < 1-theta ↔ 9/19 < theta := by
  constructor <;> intro h <;> linarith

theorem target_rows (i : Fin 9) :
    exponents (13/25) (1/25) (12/125) (4/25) i =
      ![-12/25, -7/250, -7/250, -11/50, -1/100, -7/200, -1/100, -9/100, -9/100] i := by
  fin_cases i <;> norm_num [exponents]

theorem below_target : bottleneck (21/40) (1/20) = -1/480 := by
  norm_num [bottleneck]

/-- Analytic interface for the `9/19` nine-branch power bound. -/
structure AnalyticEstimates (S N C slack : ℝ) (bound : Fin 9 → ℝ)
    (x j r t : ℚ) : Prop where
  const_nonneg : 0 ≤ C
  split : |S| ≤ ∑ i, bound i
  branches : ∀ i, bound i ≤ C * N ^ ((exponents x j r t i : ℝ) + slack)

theorem analytic_power_bound {S N C slack : ℝ} {bound : Fin 9 → ℝ} {x jTop j : ℚ}
    (hN : 1 ≤ N) (hj : 0 ≤ jTop) (hx : 10*jTop ≤ x) (hle : j ≤ jTop)
    (est : AnalyticEstimates S N C slack bound x j (truncation x jTop) (transition x jTop)) :
    |S| ≤ (9 * C) * N ^ ((bottleneck x jTop : ℝ) + slack) := by
  calc
    |S| ≤ ∑ i, bound i := est.split
    _ ≤ ∑ _i : Fin 9, C * N ^ ((bottleneck x jTop : ℝ) + slack) := by
      apply Finset.sum_le_sum
      intro i _
      refine (est.branches i).trans (mul_le_mul_of_nonneg_left ?_ est.const_nonneg)
      apply Real.rpow_le_rpow_of_exponent_le hN
      have hrow : (exponents x j (truncation x jTop) (transition x jTop) i : ℝ) ≤
          (bottleneck x jTop : ℝ) := by
        exact_mod_cast every_row_le_bottleneck hj hx hle i
      exact add_le_add hrow le_rfl
    _ = (9 * C) * N ^ ((bottleneck x jTop : ℝ) + slack) := by
      simp [Finset.sum_const, mul_assoc]

end Target3B
