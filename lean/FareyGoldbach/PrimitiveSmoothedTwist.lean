import FareyGoldbach.SmoothedExplicitFormula
import FareyGoldbach.PrimeSums
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Module A4: Single-Log Smoothed Twist Bound for Primitive Characters

Consuming Module A3 (`primitive_smoothed_explicit_formula`), Module A1 (`zeroCount_unit`,
`negLogDeriv_quarter`), Module A2 (`quarticKernel_norm_le_inv_sqrt`, `quarticKernel_norm_le_tail`),
and `PrimeSums.quarticBump_lipschitz`, this module proves the sharp single-logarithm bound
`primitive_smoothedTwist_bound` for every primitive Dirichlet character `χ mod d`, `Y ≥ 2`, and
`|t| ≤ 1/2`:
```
‖smoothedTiltedRemainder χ Y t‖ ≤ C_prim * √(Y * (1 + |t| * Y)) * log(2 * d * Y).
```
-/

open Real Complex Set Filter MeasureTheory Topology Metric
open scoped BigOperators Classical

namespace FareyGoldbach

section ElementaryHelpers

lemma norm_e_sub_e_le (t x y : ℝ) : ‖e (t * x) - e (t * y)‖ ≤ 2 * Real.pi * |t| * |x - y| := by
  let f : ℝ → ℂ := fun u => e (t * u)
  have hder : ∀ u : ℝ, HasDerivAt f ((2 * (Real.pi : ℂ) * (t : ℂ) * Complex.I) * f u) u := by
    intro u
    have hlin : HasDerivAt (fun v : ℝ => 2 * (Real.pi : ℂ) * ((t * v : ℝ) : ℂ) * Complex.I)
        (2 * (Real.pi : ℂ) * (t : ℂ) * Complex.I) u := by
      have h1 : HasDerivAt (fun v : ℝ => ((t * v : ℝ) : ℂ)) (t : ℂ) u := by
        simpa using ((hasDerivAt_id u).const_mul t).ofReal_comp
      simpa [mul_assoc] using (h1.const_mul (2 * (Real.pi : ℂ))).mul_const Complex.I
    have hexp : HasDerivAt f (f u * (2 * (Real.pi : ℂ) * (t : ℂ) * Complex.I)) u := hlin.cexp
    refine hexp.congr_deriv ?_
    ring
  have hbound : ∀ u ∈ (Set.univ : Set ℝ), ‖deriv f u‖ ≤ 2 * Real.pi * |t| := by
    intro u _
    rw [(hder u).deriv, norm_mul, norm_mul, norm_mul, norm_mul,
        Complex.norm_ofNat, Complex.norm_real, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hne : ‖f u‖ = 1 := norm_e (t * u)
    rw [hne, mul_one]
  have hmvt := convex_univ.norm_image_sub_le_of_norm_deriv_le
    (fun u _ => (hder u).differentiableAt) hbound (mem_univ y) (mem_univ x)
  simpa [f, Real.norm_eq_abs] using hmvt

/-- Principal Euler–Maclaurin-free comparison:
`‖∫_0^Y f(x) dx - ∑_{n=1}^Y f(n)‖ ≤ 8 * (1 + |t| * Y)`. -/
theorem principal_integral_sub_sum_le {Y : ℕ} (hY : 1 ≤ Y) (t : ℝ) :
    ‖mellin (scaledTiltedBump Y t) 1 -
        ∑ n ∈ Finset.Icc 1 Y, scaledTiltedBump Y t (n : ℝ)‖ ≤
      8 * (1 + |t| * (Y : ℝ)) := by
  rw [mellin_scaledTiltedBump_one hY t]
  have hY_pos : (0 : ℝ) < (Y : ℝ) := Nat.cast_pos.mpr (by omega)
  let f : ℝ → ℂ := scaledTiltedBump Y t
  have hf_cont : Continuous f := continuous_scaledTiltedBump Y t
  have hint_split : (∫ x in (0 : ℝ)..(Y : ℝ), f x) =
      ∑ k ∈ Finset.range Y, ∫ x in (k : ℝ)..((k + 1 : ℕ) : ℝ), f x := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := f)
      (a := fun k : ℕ => (k : ℝ)) (n := Y) fun k _ => hf_cont.intervalIntegrable (μ := volume) _ _
    simpa using h.symm
  have hsum_reindex : (∑ n ∈ Finset.Icc 1 Y, f (n : ℝ)) =
      ∑ k ∈ Finset.range Y, f ((k + 1 : ℕ) : ℝ) := by
    refine Finset.sum_bij (fun n _ => n - 1) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      exact Finset.mem_range.mpr (by omega)
    · intro n₁ hn₁ n₂ hn₂ heq
      simp only [Finset.mem_Icc] at hn₁ hn₂
      omega
    · intro k hk
      have hklt : k < Y := Finset.mem_range.mp hk
      exact ⟨k + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      have : n - 1 + 1 = n := by omega
      rw [this]
  have hsub_eq : (∫ x in (0 : ℝ)..(Y : ℝ), f x) - ∑ n ∈ Finset.Icc 1 Y, f (n : ℝ) =
      ∑ k ∈ Finset.range Y, ∫ x in (k : ℝ)..((k + 1 : ℕ) : ℝ), (f x - f ((k + 1 : ℕ) : ℝ)) := by
    rw [hint_split, hsum_reindex, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hconst : (∫ _x in (k : ℝ)..((k + 1 : ℕ) : ℝ), f ((k + 1 : ℕ) : ℝ)) = f ((k + 1 : ℕ) : ℝ) := by
      rw [intervalIntegral.integral_const]
      push_cast; simp
    rw [intervalIntegral.integral_sub (hf_cont.intervalIntegrable _ _) intervalIntegrable_const, hconst]
  rw [hsub_eq]
  have hstep : ∀ k ∈ Finset.range Y,
      ‖∫ x in (k : ℝ)..((k + 1 : ℕ) : ℝ), (f x - f ((k + 1 : ℕ) : ℝ))‖ ≤ 8 / (Y : ℝ) + 8 * |t| := by
    intro k _
    have hle_end : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
    have hpt : ∀ x ∈ uIoc (k : ℝ) ((k + 1 : ℕ) : ℝ),
        ‖f x - f ((k + 1 : ℕ) : ℝ)‖ ≤ 8 / (Y : ℝ) + 8 * |t| := by
      intro x hx
      rw [Set.uIoc_of_le hle_end] at hx
      have hdx : |x - ((k + 1 : ℕ) : ℝ)| ≤ 1 := by
        rw [abs_le]; push_cast at hx ⊢; constructor <;> linarith only [hx.1, hx.2]
      set y : ℝ := ((k + 1 : ℕ) : ℝ)
      have hdecomp : f x - f y =
          ((quarticBump (x / (Y : ℝ)) - quarticBump (y / (Y : ℝ)) : ℝ) : ℂ) * e (t * x) +
          (quarticBump (y / (Y : ℝ)) : ℂ) * (e (t * x) - e (t * y)) := by
        dsimp [f, scaledTiltedBump]; push_cast; ring
      rw [hdecomp]
      have hb1 : ‖((quarticBump (x / (Y : ℝ)) - quarticBump (y / (Y : ℝ)) : ℝ) : ℂ) * e (t * x)‖ ≤
          8 / (Y : ℝ) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_e, mul_one]
        calc |quarticBump (x / (Y : ℝ)) - quarticBump (y / (Y : ℝ))|
            ≤ 8 * |x / (Y : ℝ) - y / (Y : ℝ)| := quarticBump_lipschitz _ _
          _ = 8 * (|x - y| / (Y : ℝ)) := by rw [← sub_div, abs_div, abs_of_pos hY_pos]
          _ ≤ 8 * (1 / (Y : ℝ)) := mul_le_mul_of_nonneg_left
                (div_le_div_of_nonneg_right hdx hY_pos.le) (by norm_num)
          _ = 8 / (Y : ℝ) := by ring
      have hb2 : ‖(quarticBump (y / (Y : ℝ)) : ℂ) * (e (t * x) - e (t * y))‖ ≤ 8 * |t| := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (quarticBump_nonneg _)]
        have hpi : 2 * Real.pi ≤ 8 := by linarith only [Real.pi_lt_four]
        calc quarticBump (y / (Y : ℝ)) * ‖e (t * x) - e (t * y)‖
            ≤ 1 * (2 * Real.pi * |t| * |x - y|) :=
              mul_le_mul (quarticBump_le_one _) (norm_e_sub_e_le t x y) (norm_nonneg _) zero_le_one
          _ ≤ 1 * (2 * Real.pi * |t| * 1) := by
              have : 0 ≤ 2 * Real.pi * |t| := by positivity
              nlinarith only [hdx, this]
          _ ≤ 8 * |t| := by nlinarith only [hpi, abs_nonneg t]
      exact (norm_add_le _ _).trans (add_le_add hb1 hb2)
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    have hlen : |((k + 1 : ℕ) : ℝ) - (k : ℝ)| = 1 := by push_cast; norm_num
    rwa [hlen, mul_one] at hint
  calc ‖∑ k ∈ Finset.range Y, ∫ x in (k : ℝ)..((k + 1 : ℕ) : ℝ), (f x - f ((k + 1 : ℕ) : ℝ))‖
      ≤ ∑ k ∈ Finset.range Y, ‖∫ x in (k : ℝ)..((k + 1 : ℕ) : ℝ), (f x - f ((k + 1 : ℕ) : ℝ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range Y, (8 / (Y : ℝ) + 8 * |t|) := Finset.sum_le_sum hstep
    _ = (Y : ℝ) * (8 / (Y : ℝ) + 8 * |t|) := by simp; ring
    _ = 8 * (1 + |t| * (Y : ℝ)) := by field_simp [hY_pos.ne']

/-- Elementary telescoping bound `∑' n : ℕ, (1 + n)^(-(3/2)) ≤ 3`. -/
private lemma tsum_nat_one_add_rpow_neg_three_halves_le :
    (∑' n : ℕ, (1 + (n : ℝ)) ^ (-(3 / 2 : ℝ))) ≤ 3 := by
  have hstrong : ∀ m : ℕ,
      (∑ n ∈ Finset.range (m + 1), (1 + (n : ℝ)) ^ (-(3 / 2 : ℝ))) ≤
        3 - 2 / Real.sqrt ((m : ℝ) + 1) := by
    intro m
    induction m with
    | zero =>
      simp; norm_num
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hk2_pos : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      have hsq1 : 0 < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.mpr hk1_pos
      have hsq2 : 0 < Real.sqrt ((k : ℝ) + 2) := Real.sqrt_pos.mpr hk2_pos
      have hstep : (1 + ((k + 1 : ℕ) : ℝ)) ^ (-(3 / 2 : ℝ)) ≤
          2 / Real.sqrt ((k : ℝ) + 1) - 2 / Real.sqrt ((k : ℝ) + 2) := by
        have hbase : 1 + ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
        rw [hbase, Real.rpow_neg hk2_pos.le]
        have hpow : ((k : ℝ) + 2) ^ ((3 : ℝ) / 2) = ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hk2_pos.le (by norm_num)]; norm_num
        rw [hpow, ← one_div]
        have hdiff : 2 / Real.sqrt ((k : ℝ) + 1) - 2 / Real.sqrt ((k : ℝ) + 2) =
            2 / (Real.sqrt ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 2) *
              (Real.sqrt ((k : ℝ) + 2) + Real.sqrt ((k : ℝ) + 1))) := by
          have hsum_pos : 0 < Real.sqrt ((k : ℝ) + 2) + Real.sqrt ((k : ℝ) + 1) := by positivity
          have hsq : Real.sqrt ((k : ℝ) + 2) ^ 2 = (k : ℝ) + 2 := Real.sq_sqrt hk2_pos.le
          have hsq' : Real.sqrt ((k : ℝ) + 1) ^ 2 = (k : ℝ) + 1 := Real.sq_sqrt hk1_pos.le
          field_simp [hsq1.ne', hsq2.ne', hsum_pos.ne']
          nlinarith only [hsq, hsq']
        rw [hdiff]
        have hle_sq : Real.sqrt ((k : ℝ) + 1) ≤ Real.sqrt ((k : ℝ) + 2) :=
          Real.sqrt_le_sqrt (by linarith)
        have hden : Real.sqrt ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 2) *
            (Real.sqrt ((k : ℝ) + 2) + Real.sqrt ((k : ℝ) + 1)) ≤
            2 * (((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2)) := by
          have h1 : Real.sqrt ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 2) ≤ (k : ℝ) + 2 := by
            calc Real.sqrt ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 2)
                ≤ Real.sqrt ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2) :=
                  mul_le_mul_of_nonneg_right hle_sq hsq2.le
              _ = (k : ℝ) + 2 := Real.mul_self_sqrt hk2_pos.le
          have h2 : Real.sqrt ((k : ℝ) + 2) + Real.sqrt ((k : ℝ) + 1) ≤ 2 * Real.sqrt ((k : ℝ) + 2) := by
            linarith only [hle_sq]
          calc Real.sqrt ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 2) *
                (Real.sqrt ((k : ℝ) + 2) + Real.sqrt ((k : ℝ) + 1))
              ≤ ((k : ℝ) + 2) * (2 * Real.sqrt ((k : ℝ) + 2)) :=
                mul_le_mul h1 h2 (by positivity) hk2_pos.le
            _ = 2 * (((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2)) := by ring
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith only [hden]
      push_cast at hstep ⊢
      have hadd : (k : ℝ) + 1 + 1 = (k : ℝ) + 2 := by ring
      rw [hadd]
      linarith only [ih, hstep]
  refine Real.tsum_le_of_sum_range_le (fun _ => by positivity) fun N => ?_
  cases N with
  | zero => simp
  | succ m =>
    have h1 := hstrong m
    have hpos : 0 ≤ 2 / Real.sqrt ((m : ℝ) + 1) := by positivity
    linarith only [h1, hpos]

/-- Explicit bound `∑' k : ℤ, (1 + |(k : ℝ)|)^(-(3/2)) ≤ 6`. -/
lemma tsum_int_one_add_abs_rpow_neg_three_halves_le :
    (∑' k : ℤ, (1 + |(k : ℝ)|) ^ (-(3 / 2 : ℝ))) ≤ 6 := by
  have hnat_sum : Summable (fun n : ℕ => (1 + (n : ℝ)) ^ (-(3 / 2 : ℝ))) := by
    have h1 : Summable (fun n : ℕ => ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹) :=
      Real.summable_nat_rpow_inv.mpr (by norm_num)
    refine ((summable_nat_add_iff 1).mpr h1).congr fun n => ?_
    rw [Real.rpow_neg (by positivity), Nat.cast_add, Nat.cast_one, add_comm]
  have hint_sum : Summable (fun k : ℤ => (1 + |(k : ℝ)|) ^ (-(3 / 2 : ℝ))) := by
    rw [summable_int_iff_summable_nat_and_neg]
    exact ⟨hnat_sum.congr fun n => by simp [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)],
           hnat_sum.congr fun n => by simp [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]⟩
  refine hasSum_le_of_sum_le hint_sum.hasSum fun S => ?_
  let N : ℕ := S.sup (fun k => k.natAbs)
  have hsub : S ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro k hk
    have hle : k.natAbs ≤ N := Finset.le_sup (f := fun z : ℤ => z.natAbs) hk
    rw [Finset.mem_Icc]
    omega
  have hsplit : (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 + |(k : ℝ)|) ^ (-(3 / 2 : ℝ))) ≤
      (∑ n ∈ Finset.range (N + 1), (1 + (n : ℝ)) ^ (-(3 / 2 : ℝ))) +
      (∑ n ∈ Finset.range (N + 1), (1 + (n : ℝ)) ^ (-(3 / 2 : ℝ))) := by
    have hunion : Finset.Icc (-(N : ℤ)) (N : ℤ) ⊆
        ((Finset.range (N + 1)).image (fun n : ℕ => (n : ℤ))) ∪
        ((Finset.range (N + 1)).image (fun n : ℕ => -(n : ℤ))) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      rw [Finset.mem_union]
      by_cases h0 : 0 ≤ k
      · left
        exact Finset.mem_image.mpr ⟨k.toNat, Finset.mem_range.mpr (by omega), by omega⟩
      · right
        exact Finset.mem_image.mpr ⟨(-k).toNat, Finset.mem_range.mpr (by omega), by omega⟩
    calc ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 + |(k : ℝ)|) ^ (-(3 / 2 : ℝ))
        ≤ ∑ k ∈ ((Finset.range (N + 1)).image (fun n : ℕ => (n : ℤ))) ∪
                ((Finset.range (N + 1)).image (fun n : ℕ => -(n : ℤ))),
            (1 + |(k : ℝ)|) ^ (-(3 / 2 : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hunion fun _ _ _ => by positivity
      _ ≤ (∑ k ∈ (Finset.range (N + 1)).image (fun n : ℕ => (n : ℤ)), (1 + |(k : ℝ)|) ^ (-(3 / 2 : ℝ))) +
          (∑ k ∈ (Finset.range (N + 1)).image (fun n : ℕ => -(n : ℤ)), (1 + |(k : ℝ)|) ^ (-(3 / 2 : ℝ))) := by
          rw [← Finset.sum_union_inter]
          have hinter : 0 ≤ ∑ k ∈ ((Finset.range (N + 1)).image (fun n : ℕ => (n : ℤ))) ∩
              ((Finset.range (N + 1)).image (fun n : ℕ => -(n : ℤ))), (1 + |(k : ℝ)|) ^ (-(3 / 2 : ℝ)) :=
            Finset.sum_nonneg fun _ _ => by positivity
          linarith only [hinter]
      _ ≤ (∑ n ∈ Finset.range (N + 1), (1 + (n : ℝ)) ^ (-(3 / 2 : ℝ))) +
          (∑ n ∈ Finset.range (N + 1), (1 + (n : ℝ)) ^ (-(3 / 2 : ℝ))) := by
          refine add_le_add ?_ ?_
          · exact (Finset.sum_image_le_of_nonneg fun _ _ => by positivity).trans_eq
              (Finset.sum_congr rfl fun n _ => by simp [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)])
          · exact (Finset.sum_image_le_of_nonneg fun _ _ => by positivity).trans_eq
              (Finset.sum_congr rfl fun n _ => by simp [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)])
  have hnat_le := hnat_sum.sum_le_tsum (Finset.range (N + 1)) fun _ _ => by positivity
  calc ∑ k ∈ S, (1 + |(k : ℝ)|) ^ (-(3 / 2 : ℝ))
      ≤ ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 + |(k : ℝ)|) ^ (-(3 / 2 : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ (∑ n ∈ Finset.range (N + 1), (1 + (n : ℝ)) ^ (-(3 / 2 : ℝ))) +
        (∑ n ∈ Finset.range (N + 1), (1 + (n : ℝ)) ^ (-(3 / 2 : ℝ))) := hsplit
    _ ≤ 3 + 3 := add_le_add (hnat_le.trans tsum_nat_one_add_rpow_neg_three_halves_le)
        (hnat_le.trans tsum_nat_one_add_rpow_neg_three_halves_le)
    _ = 6 := by norm_num

/-- Explicit value `∫ u : ℝ, (1 + |u|)^(-(3/2)) = 4`. -/
lemma integral_one_add_abs_rpow_neg_three_halves_eq :
    (∫ u : ℝ, (1 + |u|) ^ (-(3 / 2 : ℝ))) = 4 := by
  have hder_pos : ∀ u ∈ Ici (0 : ℝ),
      HasDerivAt (fun x : ℝ => -2 * (1 + x) ^ (-(1 / 2 : ℝ))) ((1 + u) ^ (-(3 / 2 : ℝ))) u := by
    intro u hu
    have hpos : 0 < 1 + u := by linarith only [Set.mem_Ici.mp hu]
    have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 u := (hasDerivAt_id u).const_add 1
    have h2 := h1.rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hpos.ne')
    convert h2.const_mul (-2 : ℝ) using 1
    norm_num; ring
  have htend_pos : Tendsto (fun x : ℝ => -2 * (1 + x) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => 1 + x) atTop atTop := tendsto_atTop_add_const_left atTop 1 tendsto_id
    have h2 : Tendsto (fun x : ℝ => (1 + x) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp h1
    simpa using h2.const_mul (-2 : ℝ)
  have hpos_int : IntegrableOn (fun u : ℝ => (1 + u) ^ (-(3 / 2 : ℝ))) (Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' hder_pos
      (fun u hu => Real.rpow_nonneg (by linarith only [Set.mem_Ioi.mp hu]) _) htend_pos
  have hpos_val : (∫ u in Ioi (0 : ℝ), (1 + u) ^ (-(3 / 2 : ℝ))) = 2 := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' hder_pos hpos_int htend_pos]; norm_num
  have hIoi_int : IntegrableOn (fun u : ℝ => (1 + |u|) ^ (-(3 / 2 : ℝ))) (Ioi 0) :=
    hpos_int.congr_fun (fun u hu => by simp [abs_of_pos (Set.mem_Ioi.mp hu)]) measurableSet_Ioi
  have hIoi_eq : (∫ u in Ioi (0 : ℝ), (1 + |u|) ^ (-(3 / 2 : ℝ))) = 2 := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun u => (1 + u) ^ (-(3 / 2 : ℝ)))
        fun u hu => by simp [abs_of_pos (Set.mem_Ioi.mp hu)]]
    exact hpos_val
  have hder_neg : ∀ u ∈ Iic (0 : ℝ),
      HasDerivAt (fun x : ℝ => 2 * (1 - x) ^ (-(1 / 2 : ℝ))) ((1 - u) ^ (-(3 / 2 : ℝ))) u := by
    intro u hu
    have hpos : 0 < 1 - u := by linarith only [Set.mem_Iic.mp hu]
    have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) u := (hasDerivAt_id' u).const_sub (1 : ℝ)
    have h2 := h1.rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hpos.ne')
    convert h2.const_mul (2 : ℝ) using 1
    norm_num; ring
  have htend_neg : Tendsto (fun x : ℝ => 2 * (1 - x) ^ (-(1 / 2 : ℝ))) atBot (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => 1 - x) atBot atTop := by
      have := tendsto_atTop_add_const_left atBot (1 : ℝ) tendsto_neg_atBot_atTop
      simpa [sub_eq_add_neg] using this
    have h2 : Tendsto (fun x : ℝ => (1 - x) ^ (-(1 / 2 : ℝ))) atBot (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp h1
    simpa using h2.const_mul (2 : ℝ)
  have hIic_int : IntegrableOn (fun u : ℝ => (1 + |u|) ^ (-(3 / 2 : ℝ))) (Iic 0) := by
    have h1 : IntegrableOn (fun u : ℝ => (1 + |-u|) ^ (-(3 / 2 : ℝ))) (Iio 0) := by
      simpa using hIoi_int.comp_neg
    have h2 : IntegrableOn (fun u : ℝ => (1 + |u|) ^ (-(3 / 2 : ℝ))) (Iio 0) := by
      simpa [abs_neg] using h1
    exact h2.congr_set_ae Iio_ae_eq_Iic.symm
  have hneg_int : IntegrableOn (fun u : ℝ => (1 - u) ^ (-(3 / 2 : ℝ))) (Iic 0) :=
    hIic_int.congr_fun (fun u hu => by
      dsimp only; rw [abs_of_nonpos (Set.mem_Iic.mp hu), ← sub_eq_add_neg]) measurableSet_Iic
  have hIic_eq : (∫ u in Iic (0 : ℝ), (1 + |u|) ^ (-(3 / 2 : ℝ))) = 2 := by
    rw [setIntegral_congr_fun measurableSet_Iic (g := fun u => (1 - u) ^ (-(3 / 2 : ℝ))) fun u hu => by
      dsimp only; rw [abs_of_nonpos (Set.mem_Iic.mp hu), ← sub_eq_add_neg]]
    have hcont0 : ContinuousWithinAt (fun x : ℝ => 2 * (1 - x) ^ (-(1 / 2 : ℝ))) (Iic 0) 0 :=
      (hder_neg 0 self_mem_Iic).continuousAt.continuousWithinAt
    rw [integral_Iic_of_hasDerivAt_of_tendsto hcont0 (fun u hu => hder_neg u (Set.mem_Iio.mp hu).le) hneg_int htend_neg]
    norm_num
  have hunion : (Iic (0 : ℝ)) ∪ Ioi 0 = Set.univ := Iic_union_Ioi
  have hdisj : Disjoint (Iic (0 : ℝ)) (Ioi 0) := Set.Iic_disjoint_Ioi le_rfl
  rw [← setIntegral_univ, ← hunion,
      setIntegral_union hdisj measurableSet_Ioi hIic_int hIoi_int, hIic_eq, hIoi_eq]
  norm_num

/-- Shared logarithmic helper: for `d ≥ 1`, `Y ≥ 2`, `1 ≤ Real.log (2 * d * Y)`. -/
lemma one_le_log_two_d_Y {d Y : ℕ} [NeZero d] (hY : 2 ≤ Y) :
    1 ≤ Real.log (2 * (d : ℝ) * (Y : ℝ)) := by
  have hd : (1 : ℝ) ≤ d := Nat.one_le_cast.mpr (NeZero.pos d)
  have hY2 : (2 : ℝ) ≤ Y := Nat.ofNat_le_cast.mpr hY
  have he : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h4 : (4 : ℝ) ≤ 2 * (d : ℝ) * (Y : ℝ) := by nlinarith only [hd, hY2]
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (2 * (d : ℝ) * (Y : ℝ)) := Real.log_le_log (Real.exp_pos 1) (he.le.trans h4)

/-- Shared logarithmic helper: `log(2 * d * (2 + x)) ≤ 4 * log(2 * d * Y)` whenever `0 ≤ x ≤ 16 * Y`. -/
lemma log_two_d_add_le_four_log {d Y : ℕ} [NeZero d] (hY : 2 ≤ Y) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ 16 * (Y : ℝ)) :
    Real.log (2 * (d : ℝ) * (2 + x)) ≤ 4 * Real.log (2 * (d : ℝ) * (Y : ℝ)) := by
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hY2 : (2 : ℝ) ≤ Y := Nat.ofNat_le_cast.mpr hY
  have hlog1 := one_le_log_two_d_Y (d := d) hY
  have harg : 2 * (d : ℝ) * (2 + x) ≤ 17 * (2 * (d : ℝ) * (Y : ℝ)) := by
    nlinarith only [hd_pos, hY2, hx]
  have hlog17 : Real.log 17 ≤ 3 := by
    have h17 : (17 : ℝ) ≤ Real.exp 3 := by
      have he : (2.7 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) Real.exp_one_gt_d9.le
      calc (17 : ℝ) ≤ (2.7 : ℝ) ^ 3 := by norm_num
        _ ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) he 3
        _ = Real.exp 3 := by rw [← Real.exp_nat_mul]; norm_num
    calc Real.log 17 ≤ Real.log (Real.exp 3) := Real.log_le_log (by norm_num) h17
      _ = 3 := Real.log_exp 3
  calc Real.log (2 * (d : ℝ) * (2 + x))
      ≤ Real.log (17 * (2 * (d : ℝ) * (Y : ℝ))) := Real.log_le_log (by positivity) harg
    _ = Real.log 17 + Real.log (2 * (d : ℝ) * (Y : ℝ)) := Real.log_mul (by norm_num) (by positivity)
    _ ≤ 3 + Real.log (2 * (d : ℝ) * (Y : ℝ)) := by linarith only [hlog17]
    _ ≤ 4 * Real.log (2 * (d : ℝ) * (Y : ℝ)) := by linarith only [hlog1]

/-- Shared logarithmic helper for tails: `log(2 * d * (2 + x)) ≤ 5 * log(2 * d * Y) * √(1 + x)`
for all `0 ≤ x`. -/
lemma log_two_d_add_le_five_log_sqrt {d Y : ℕ} [NeZero d] (hY : 2 ≤ Y) {x : ℝ} (hx0 : 0 ≤ x) :
    Real.log (2 * (d : ℝ) * (2 + x)) ≤ 5 * Real.log (2 * (d : ℝ) * (Y : ℝ)) * Real.sqrt (1 + x) := by
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hY2 : (2 : ℝ) ≤ Y := Nat.ofNat_le_cast.mpr hY
  have hlog1 := one_le_log_two_d_Y (d := d) hY
  have hlog2d_le : Real.log (2 * (d : ℝ)) ≤ Real.log (2 * (d : ℝ) * (Y : ℝ)) :=
    Real.log_le_log (by positivity) (by nlinarith only [hd_pos, hY2])
  have hlog_x : Real.log (2 + x) ≤ 4 * Real.sqrt (1 + x) := by
    have hpos : 0 < 2 + x := by linarith only [hx0]
    have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hpos)
    rw [Real.log_sqrt hpos.le] at h1
    have hsqrt4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two]
    have h2 : Real.sqrt (2 + x) ≤ 2 * Real.sqrt (1 + x) := by
      calc Real.sqrt (2 + x) ≤ Real.sqrt (4 * (1 + x)) := Real.sqrt_le_sqrt (by linarith only [hx0])
        _ = 2 * Real.sqrt (1 + x) := by rw [Real.sqrt_mul (by norm_num), hsqrt4]
    linarith only [h1, h2]
  have hsq1 : (1 : ℝ) ≤ Real.sqrt (1 + x) := by
    rw [Real.le_sqrt zero_le_one (by positivity)]; linarith only [hx0]
  rw [Real.log_mul (by positivity) (by positivity)]
  nlinarith only [hlog2d_le, hlog_x, hsq1, hlog1]

end ElementaryHelpers

section ZeroSumAndQuarterBounds

/-- Bound on the critical-strip zero sum `‖∑' ρ, zeroTerm χ Y t ρ‖`. -/
theorem norm_tsum_zeroTerm_le (hGRH : DirichletGRH) {d Y : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) (hY : 2 ≤ Y) {t : ℝ} (ht : |t| ≤ 1 / 2) :
    ‖∑' ρ : ℂ, zeroTerm χ Y t ρ‖ ≤
      450000000 * Real.sqrt ((Y : ℝ) * (1 + |t| * (Y : ℝ))) * Real.log (2 * (d : ℝ) * (Y : ℝ)) := by
  have hY1 : 1 ≤ Y := by omega
  have hY2 : (2 : ℝ) ≤ Y := Nat.ofNat_le_cast.mpr hY
  set B : ℝ := 1 + |t| * (Y : ℝ)
  have hB1 : 1 ≤ B := by dsimp [B]; linarith [mul_nonneg (abs_nonneg t) (Nat.cast_nonneg (α := ℝ) Y)]
  have hB_le_Y : B ≤ (Y : ℝ) := by
    dsimp [B]; nlinarith only [ht, hY2]
  have hlam_abs : |t * (Y : ℝ)| = |t| * (Y : ℝ) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) Y)]
  have h1lam : 1 + |t * (Y : ℝ)| = B := by rw [hlam_abs]
  set R₀ : ℝ := 4 * Real.pi * |t * (Y : ℝ)| + 3
  have hR₀_le : R₀ ≤ 16 * B := by
    have h4pi : 4 * Real.pi ≤ 13 := by linarith only [Real.pi_lt_d2]
    dsimp [R₀]
    rw [hlam_abs]
    have : 0 ≤ |t| * (Y : ℝ) := by positivity
    dsimp [B]; nlinarith only [h4pi, this]
  let bandBound : ℤ → ℝ := fun k =>
    Real.sqrt (Y : ℝ) *
      (if R₀ ≤ |(k : ℝ)| then 60000 / (1 + |(k : ℝ)|) ^ 2 else 1792 / Real.sqrt B) *
      (217 * Real.log (2 * (d : ℝ) * (2 + |(k : ℝ)|)))
  have hband_sum : Summable bandBound := by
    simpa [bandBound, R₀, h1lam] using summable_band_zero_bound (d := d) hY1 t
  have hband_nn : ∀ k : ℤ, 0 ≤ bandBound k := fun k => by
    have := one_le_log_two_mul_d_mul d (k : ℝ)
    dsimp [bandBound]; split_ifs <;> positivity
  -- First show `‖∑' ρ, zeroTerm χ Y t ρ‖ ≤ ∑' k : ℤ, bandBound k`.
  have htsum_le_band : ‖∑' ρ : ℂ, zeroTerm χ Y t ρ‖ ≤ ∑' k : ℤ, bandBound k := by
    have hnorm_summ := summable_norm_zeroTerm hGRH hprim hY1 t
    refine (norm_tsum_le_tsum_norm hnorm_summ).trans ?_
    refine hasSum_le_of_sum_le hnorm_summ.hasSum fun S => ?_
    let K : Finset ℤ := S.image (fun ρ => ⌊ρ.im⌋)
    have hsub : S.filter (fun ρ => 0 < ρ.re ∧ entireL χ ρ = 0) ⊆ K.biUnion (bandZeros χ) := by
      intro ρ hρ
      obtain ⟨hρS, hre, h0⟩ := Finset.mem_filter.mp hρ
      refine Finset.mem_biUnion.mpr ⟨⌊ρ.im⌋, Finset.mem_image_of_mem _ hρS, ?_⟩
      exact (mem_bandZeros_iff hGRH hprim).mpr ⟨hre, h0, Int.floor_le ρ.im, Int.lt_floor_add_one ρ.im⟩
    have hfilt : (∑ ρ ∈ S, ‖zeroTerm χ Y t ρ‖) =
        ∑ ρ ∈ S.filter (fun ρ => 0 < ρ.re ∧ entireL χ ρ = 0), ‖zeroTerm χ Y t ρ‖ := by
      rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun ρ _ => by unfold zeroTerm; split_ifs <;> simp
    calc ∑ ρ ∈ S, ‖zeroTerm χ Y t ρ‖
        = ∑ ρ ∈ S.filter (fun ρ => 0 < ρ.re ∧ entireL χ ρ = 0), ‖zeroTerm χ Y t ρ‖ := hfilt
      _ ≤ ∑ ρ ∈ K.biUnion (bandZeros χ), ‖zeroTerm χ Y t ρ‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => norm_nonneg _
      _ = ∑ k ∈ K, ∑ ρ ∈ bandZeros χ k, ‖zeroTerm χ Y t ρ‖ :=
          Finset.sum_biUnion fun k₁ _ k₂ _ hne => bandZeros_disjoint χ hne
      _ ≤ ∑ k ∈ K, bandBound k :=
          Finset.sum_le_sum fun k _ => by
            simpa [bandBound, R₀, h1lam] using sum_norm_zeroTerm_band_le hGRH hprim hY1 t k
      _ ≤ ∑' k : ℤ, bandBound k := hband_sum.sum_le_tsum K fun k _ => hband_nn k
  -- Split `bandBound k ≤ g_in k + g_out k` cleanly!
  set L : ℝ := Real.log (2 * (d : ℝ) * (Y : ℝ))
  have hL1 : 1 ≤ L := one_le_log_two_d_Y (d := d) hY
  let M : ℕ := Nat.floor R₀
  let S_in : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ)
  let g_in : ℤ → ℝ := fun k =>
    if k ∈ S_in then Real.sqrt (Y : ℝ) * (1792 / Real.sqrt B) * (217 * (4 * L)) else 0
  let g_out : ℤ → ℝ := fun k =>
    Real.sqrt (Y : ℝ) * 60000 * (217 * (5 * L)) * (1 + |(k : ℝ)|) ^ (-(3 / 2 : ℝ))
  have hgin_sum : Summable g_in := summable_of_ne_finset_zero (s := S_in) fun k hk => by simp [g_in, hk]
  have hgout_sum : Summable g_out := by
    have hbase : Summable (fun k : ℤ => (1 + |(k : ℝ)|) ^ (-(3 / 2 : ℝ))) := by
      have hnat : Summable (fun n : ℕ => (1 + (n : ℝ)) ^ (-(3 / 2 : ℝ))) := by
        have h1 : Summable (fun n : ℕ => ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹) :=
          Real.summable_nat_rpow_inv.mpr (by norm_num)
        refine ((summable_nat_add_iff 1).mpr h1).congr fun n => ?_
        rw [Real.rpow_neg (by positivity), Nat.cast_add, Nat.cast_one, add_comm]
      rw [summable_int_iff_summable_nat_and_neg]
      exact ⟨hnat.congr fun n => by simp [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)],
             hnat.congr fun n => by simp [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]⟩
    exact hbase.mul_left _
  have hpt : ∀ k : ℤ, bandBound k ≤ g_in k + g_out k := by
    intro k
    have hgin_nn : 0 ≤ g_in k := by dsimp [g_in]; split_ifs <;> positivity
    have hgout_nn : 0 ≤ g_out k := by dsimp [g_out]; positivity
    dsimp [bandBound]
    split_ifs with htail
    · refine le_add_of_nonneg_of_le hgin_nn ?_
      have hlog := log_two_d_add_le_five_log_sqrt (d := d) hY (abs_nonneg (k : ℝ))
      have hrpow : Real.sqrt (1 + |(k : ℝ)|) / (1 + |(k : ℝ)|) ^ 2 = (1 + |(k : ℝ)|) ^ (-(3 / 2 : ℝ)) := by
        have hpos : 0 < 1 + |(k : ℝ)| := by positivity
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (1 + |(k : ℝ)|) 2, ← Real.rpow_sub hpos]; norm_num
      calc Real.sqrt (Y : ℝ) * (60000 / (1 + |(k : ℝ)|) ^ 2) *
            (217 * Real.log (2 * (d : ℝ) * (2 + |(k : ℝ)|)))
          ≤ Real.sqrt (Y : ℝ) * (60000 / (1 + |(k : ℝ)|) ^ 2) *
            (217 * (5 * L * Real.sqrt (1 + |(k : ℝ)|))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (by norm_num)) (by positivity)
        _ = Real.sqrt (Y : ℝ) * 60000 * (217 * (5 * L)) *
              (Real.sqrt (1 + |(k : ℝ)|) / (1 + |(k : ℝ)|) ^ 2) := by ring
        _ = g_out k := by rw [hrpow]
    · push Not at htail
      refine le_add_of_le_of_nonneg ?_ hgout_nn
      have hk_mem : k ∈ S_in := by
        have hk_le : k.natAbs ≤ M := Nat.le_floor (by simpa using htail.le)
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hk_le_16Y : |(k : ℝ)| ≤ 16 * (Y : ℝ) := by linarith only [htail, hR₀_le, hB_le_Y]
      have hlog := log_two_d_add_le_four_log (d := d) hY (abs_nonneg (k : ℝ)) hk_le_16Y
      dsimp [g_in]
      simp only [hk_mem, ↓reduceIte]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (by norm_num)) (by positivity)
  have htsum_gin : (∑' k : ℤ, g_in k) ≤ 52000000 * Real.sqrt ((Y : ℝ) * B) * L := by
    rw [tsum_eq_sum (s := S_in) fun k hk => by simp [g_in, hk]]
    have hsum_eq : (∑ k ∈ S_in, g_in k) =
        (S_in.card : ℝ) * (Real.sqrt (Y : ℝ) * (1792 / Real.sqrt B) * (217 * (4 * L))) := by
      have : ∀ k ∈ S_in, g_in k = Real.sqrt (Y : ℝ) * (1792 / Real.sqrt B) * (217 * (4 * L)) :=
        fun k hk => by simp [g_in, hk]
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
    rw [hsum_eq]
    have hcard_le : (S_in.card : ℝ) ≤ 33 * B := by
      have hcard : S_in.card = 2 * M + 1 := by
        dsimp [S_in]; rw [Int.card_Icc]; omega
      have hM_le : (M : ℝ) ≤ R₀ := Nat.floor_le (by dsimp [R₀]; positivity)
      rw [hcard]; push_cast; linarith only [hM_le, hR₀_le, hB1]
    have hsqrt_mul : B * (Real.sqrt (Y : ℝ) * (1792 / Real.sqrt B)) =
        1792 * Real.sqrt ((Y : ℝ) * B) := by
      have hB_pos : 0 < B := by linarith only [hB1]
      have hsqB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB_pos
      rw [Real.sqrt_mul (Nat.cast_nonneg Y)]
      field_simp [hsqB.ne']
      rw [Real.sq_sqrt hB_pos.le]
    calc (S_in.card : ℝ) * (Real.sqrt (Y : ℝ) * (1792 / Real.sqrt B) * (217 * (4 * L)))
        ≤ (33 * B) * (Real.sqrt (Y : ℝ) * (1792 / Real.sqrt B) * (217 * (4 * L))) :=
          mul_le_mul_of_nonneg_right hcard_le (by positivity)
      _ = 33 * (B * (Real.sqrt (Y : ℝ) * (1792 / Real.sqrt B))) * (217 * (4 * L)) := by ring
      _ = 33 * (1792 * Real.sqrt ((Y : ℝ) * B)) * (217 * (4 * L)) := by rw [hsqrt_mul]
      _ ≤ 52000000 * Real.sqrt ((Y : ℝ) * B) * L := by
          have hnn : 0 ≤ Real.sqrt ((Y : ℝ) * B) * L := by positivity
          nlinarith only [hnn]
  have htsum_gout : (∑' k : ℤ, g_out k) ≤ 391000000 * Real.sqrt ((Y : ℝ) * B) * L := by
    have hmul : (∑' k : ℤ, g_out k) =
        Real.sqrt (Y : ℝ) * 60000 * (217 * (5 * L)) * ∑' k : ℤ, (1 + |(k : ℝ)|) ^ (-(3 / 2 : ℝ)) :=
      tsum_mul_left
    rw [hmul]
    have hsq_le : Real.sqrt (Y : ℝ) ≤ Real.sqrt ((Y : ℝ) * B) :=
      Real.sqrt_le_sqrt (by nlinarith only [hB1, hY2])
    calc Real.sqrt (Y : ℝ) * 60000 * (217 * (5 * L)) * ∑' k : ℤ, (1 + |(k : ℝ)|) ^ (-(3 / 2 : ℝ))
        ≤ Real.sqrt ((Y : ℝ) * B) * 60000 * (217 * (5 * L)) * 6 :=
          mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq_le (by norm_num)) (by positivity))
            tsum_int_one_add_abs_rpow_neg_three_halves_le (tsum_nonneg fun _ => by positivity) (by positivity)
      _ ≤ 391000000 * Real.sqrt ((Y : ℝ) * B) * L := by
          have hnn : 0 ≤ Real.sqrt ((Y : ℝ) * B) * L := by positivity
          nlinarith only [hnn]
  have htsum_tot : (∑' k : ℤ, bandBound k) ≤ (∑' k : ℤ, g_in k) + (∑' k : ℤ, g_out k) := by
    rw [← (hgin_sum.tsum_add hgout_sum)]
    exact hband_sum.tsum_le_tsum hpt (hgin_sum.add hgout_sum)
  have hnn_tot : 0 ≤ Real.sqrt ((Y : ℝ) * B) * L := by positivity
  linarith only [htsum_le_band, htsum_tot, htsum_gin, htsum_gout, hnn_tot]

/-- Bound on the `Re(s) = 1/4` vertical line integral. -/
theorem norm_quarter_integral_le (hGRH : DirichletGRH) {d Y : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) (hY : 2 ≤ Y) {t : ℝ} (ht : |t| ≤ 1 / 2) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ u : ℝ, mellin (scaledTiltedBump Y t) ((1 / 4 : ℝ) + (u : ℂ) * Complex.I) *
          negLogDerivL χ ((1 / 4 : ℝ) + (u : ℂ) * Complex.I)‖ ≤
      500000000000 * Real.sqrt ((Y : ℝ) * (1 + |t| * (Y : ℝ))) * Real.log (2 * (d : ℝ) * (Y : ℝ)) := by
  have hY1 : 1 ≤ Y := by omega
  have hY2 : (2 : ℝ) ≤ Y := Nat.ofNat_le_cast.mpr hY
  have hY_pos : (0 : ℝ) < (Y : ℝ) := Nat.cast_pos.mpr (by omega)
  set B : ℝ := 1 + |t| * (Y : ℝ)
  have hB1 : 1 ≤ B := by dsimp [B]; linarith [mul_nonneg (abs_nonneg t) (Nat.cast_nonneg (α := ℝ) Y)]
  have hB_le_Y : B ≤ (Y : ℝ) := by dsimp [B]; nlinarith only [ht, hY2]
  have hlam_abs : |t * (Y : ℝ)| = |t| * (Y : ℝ) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) Y)]
  set R : ℝ := 4 * Real.pi * |t * (Y : ℝ)| + 2
  have hR_pos : 0 < R := by dsimp [R]; positivity
  have hR_le : R ≤ 16 * B := by
    have h4pi : 4 * Real.pi ≤ 13 := by linarith only [Real.pi_lt_d2]
    dsimp [R]; rw [hlam_abs]
    have : 0 ≤ |t| * (Y : ℝ) := by positivity
    dsimp [B]; nlinarith only [h4pi, this]
  set L : ℝ := Real.log (2 * (d : ℝ) * (Y : ℝ))
  have hL1 : 1 ≤ L := one_le_log_two_d_Y (d := d) hY
  have hY14_le : (Y : ℝ) ^ ((1 : ℝ) / 4) ≤ Real.sqrt (Y : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith only [hY2]) (by norm_num)
  set C_in : ℝ := (Y : ℝ) ^ ((1 : ℝ) / 4) * (1792 / Real.sqrt B) * (812870 * (4 * L))
  set C_out : ℝ := (Y : ℝ) ^ ((1 : ℝ) / 4) * 15000 * (812870 * (5 * L))
  let g_in : ℝ → ℝ := Set.indicator (Icc (-R) R) (fun _ => C_in)
  let g_out : ℝ → ℝ := fun u => C_out * (1 + |u|) ^ (-(3 / 2 : ℝ))
  have hgin_int : Integrable g_in :=
    (integrableOn_const (hs := measure_Icc_lt_top.ne)).integrable_indicator measurableSet_Icc
  have hgout_int : Integrable g_out := by
    have hbase : Integrable (fun u : ℝ => (1 + |u|) ^ (-(3 / 2 : ℝ))) := by
      have hcont : Continuous (fun u : ℝ => (1 + |u|) ^ (-(3 / 2 : ℝ))) :=
        Continuous.rpow (continuous_const.add continuous_abs) continuous_const fun _ => Or.inl (by positivity)
      have hIoc : IntegrableOn (fun u : ℝ => (1 + |u|) ^ (-(3 / 2 : ℝ))) (Ioc 0 1) :=
        (hcont.continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
      have hIoi1 : IntegrableOn (fun u : ℝ => (1 + |u|) ^ (-(3 / 2 : ℝ))) (Ioi 1) := by
        have hdom := integrableOn_Ioi_rpow_of_lt (a := -(3 / 2 : ℝ)) (c := (1 : ℝ)) (by norm_num) zero_lt_one
        refine hdom.mono' hcont.aestronglyMeasurable ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu0 : 0 < u := zero_lt_one.trans hu
        rw [Real.norm_of_nonneg (by positivity), abs_of_pos hu0]
        exact Real.rpow_le_rpow_of_nonpos hu0 (by linarith only [hu]) (by norm_num)
      have hpos : IntegrableOn (fun u : ℝ => (1 + |u|) ^ (-(3 / 2 : ℝ))) (Ioi 0) := by
        rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]; exact hIoc.union hIoi1
      have hneg : IntegrableOn (fun u : ℝ => (1 + |u|) ^ (-(3 / 2 : ℝ))) (Iic 0) := by
        have h1 : IntegrableOn (fun u : ℝ => (1 + |-u|) ^ (-(3 / 2 : ℝ))) (Iio 0) := by
          simpa using hpos.comp_neg
        have h2 : IntegrableOn (fun u : ℝ => (1 + |u|) ^ (-(3 / 2 : ℝ))) (Iio 0) := by
          simpa [abs_neg] using h1
        exact h2.congr_set_ae Iio_ae_eq_Iic.symm
      rw [← integrableOn_univ, ← Iic_union_Ioi]
      exact hneg.union hpos
    exact hbase.const_mul C_out
  have hpt : ∀ u : ℝ,
      ‖mellin (scaledTiltedBump Y t) ((1 / 4 : ℝ) + (u : ℂ) * Complex.I) *
        negLogDerivL χ ((1 / 4 : ℝ) + (u : ℂ) * Complex.I)‖ ≤ g_in u + g_out u := by
    intro u
    rw [norm_mul, mellin_scaledTiltedBump_eq hY1 t _, norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos hY_pos]
    have hre : (((1 / 4 : ℝ) : ℂ) + (u : ℂ) * Complex.I).re = 1 / 4 := by simp
    rw [hre]
    have hD := negLogDeriv_quarter hGRH hprim u
    have hgin_nn : 0 ≤ g_in u := Set.indicator_nonneg (fun _ _ => by dsimp [C_in]; positivity) u
    have hgout_nn : 0 ≤ g_out u := by dsimp [g_out, C_out]; positivity
    by_cases hu : R ≤ |u|
    · refine le_add_of_nonneg_of_le hgin_nn ?_
      have hker := quarticKernel_norm_le_tail (lam := t * (Y : ℝ)) (σ := 1 / 4) (γ := u)
        (by norm_num) (by norm_num) hu
      have hlog := log_two_d_add_le_five_log_sqrt (d := d) hY (abs_nonneg u)
      have hrpow : Real.sqrt (1 + |u|) / (1 + |u|) ^ 2 = (1 + |u|) ^ (-(3 / 2 : ℝ)) := by
        have hpos : 0 < 1 + |u| := by positivity
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (1 + |u|) 2, ← Real.rpow_sub hpos]; norm_num
      calc (Y : ℝ) ^ ((1 : ℝ) / 4) *
            ‖quarticKernel (t * (Y : ℝ)) ((1 / 4 : ℝ) + (u : ℂ) * Complex.I)‖ *
            ‖negLogDerivL χ ((1 / 4 : ℝ) + (u : ℂ) * Complex.I)‖
          ≤ (Y : ℝ) ^ ((1 : ℝ) / 4) * (15000 / (1 + |u|) ^ 2) *
            (812870 * (5 * L * Real.sqrt (1 + |u|))) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left hker (by positivity))
                (hD.trans (mul_le_mul_of_nonneg_left hlog (by norm_num)))
                (norm_nonneg _) (by positivity)
        _ = C_out * (Real.sqrt (1 + |u|) / (1 + |u|) ^ 2) := by dsimp [C_out]; ring
        _ = g_out u := by rw [hrpow]
    · push Not at hu
      refine le_add_of_le_of_nonneg ?_ hgout_nn
      have hmem : u ∈ Icc (-R) R := abs_le.mp hu.le
      have hker := quarticKernel_norm_le_inv_sqrt (lam := t * (Y : ℝ)) (σ := 1 / 4) (γ := u)
        (by norm_num) (by norm_num)
      rw [hlam_abs] at hker
      have hu_le : |u| ≤ 16 * (Y : ℝ) := by linarith only [hu, hR_le, hB_le_Y]
      have hlog := log_two_d_add_le_four_log (d := d) hY (abs_nonneg u) hu_le
      dsimp [g_in]
      rw [Set.indicator_of_mem hmem]
      calc (Y : ℝ) ^ ((1 : ℝ) / 4) *
            ‖quarticKernel (t * (Y : ℝ)) ((1 / 4 : ℝ) + (u : ℂ) * Complex.I)‖ *
            ‖negLogDerivL χ ((1 / 4 : ℝ) + (u : ℂ) * Complex.I)‖
          ≤ (Y : ℝ) ^ ((1 : ℝ) / 4) * (1792 / Real.sqrt B) * (812870 * (4 * L)) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left hker (by positivity))
                (hD.trans (mul_le_mul_of_nonneg_left hlog (by norm_num)))
                (norm_nonneg _) (by positivity)
        _ = C_in := rfl
  have hint_in : (∫ u : ℝ, g_in u) ≤ 200000000000 * Real.sqrt ((Y : ℝ) * B) * L := by
    have heval : (∫ u : ℝ, g_in u) = 2 * R * C_in := by
      dsimp [g_in]
      rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
          Real.volume_real_Icc_of_le (by linarith only [hR_pos])]
      ring
    rw [heval]
    have hsqrt_mul : B * (Real.sqrt (Y : ℝ) * (1792 / Real.sqrt B)) =
        1792 * Real.sqrt ((Y : ℝ) * B) := by
      have hB_pos : 0 < B := by linarith only [hB1]
      have hsqB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB_pos
      rw [Real.sqrt_mul (Nat.cast_nonneg Y)]
      field_simp [hsqB.ne']
      rw [Real.sq_sqrt hB_pos.le]
    have hCin_le : C_in ≤ Real.sqrt (Y : ℝ) * (1792 / Real.sqrt B) * (812870 * (4 * L)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hY14_le (by positivity)) (by positivity)
    calc 2 * R * C_in
        ≤ 2 * (16 * B) * (Real.sqrt (Y : ℝ) * (1792 / Real.sqrt B) * (812870 * (4 * L))) :=
          mul_le_mul (by linarith only [hR_le]) hCin_le (by dsimp [C_in]; positivity) (by positivity)
      _ = 32 * (B * (Real.sqrt (Y : ℝ) * (1792 / Real.sqrt B))) * (812870 * (4 * L)) := by ring
      _ = 32 * (1792 * Real.sqrt ((Y : ℝ) * B)) * (812870 * (4 * L)) := by rw [hsqrt_mul]
      _ ≤ 200000000000 * Real.sqrt ((Y : ℝ) * B) * L := by
          have hnn : 0 ≤ Real.sqrt ((Y : ℝ) * B) * L := by positivity
          nlinarith only [hnn]
  have hint_out : (∫ u : ℝ, g_out u) ≤ 300000000000 * Real.sqrt ((Y : ℝ) * B) * L := by
    have heval : (∫ u : ℝ, g_out u) = C_out * 4 := by
      dsimp [g_out]
      rw [integral_const_mul, integral_one_add_abs_rpow_neg_three_halves_eq]
    rw [heval]
    have hsq_le : (Y : ℝ) ^ ((1 : ℝ) / 4) ≤ Real.sqrt ((Y : ℝ) * B) :=
      hY14_le.trans (Real.sqrt_le_sqrt (by nlinarith only [hB1, hY2]))
    calc C_out * 4
        ≤ (Real.sqrt ((Y : ℝ) * B) * 15000 * (812870 * (5 * L))) * 4 := by
          dsimp [C_out]
          refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq_le (by norm_num)) (by positivity)
      _ ≤ 300000000000 * Real.sqrt ((Y : ℝ) * B) * L := by
          have hnn : 0 ≤ Real.sqrt ((Y : ℝ) * B) * L := by positivity
          nlinarith only [hnn]
  have h1_2pi : ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [div_le_one (by positivity)]
    linarith only [Real.pi_gt_three]
  have hint_q := integrable_quarter_line hGRH hprim hY1 t
  have hint_le : ‖∫ u : ℝ, mellin (scaledTiltedBump Y t) ((1 / 4 : ℝ) + (u : ℂ) * Complex.I) *
        negLogDerivL χ ((1 / 4 : ℝ) + (u : ℂ) * Complex.I)‖ ≤
      (∫ u : ℝ, g_in u) + (∫ u : ℝ, g_out u) := by
    calc ‖∫ u : ℝ, mellin (scaledTiltedBump Y t) ((1 / 4 : ℝ) + (u : ℂ) * Complex.I) *
            negLogDerivL χ ((1 / 4 : ℝ) + (u : ℂ) * Complex.I)‖
        ≤ ∫ u : ℝ, ‖mellin (scaledTiltedBump Y t) ((1 / 4 : ℝ) + (u : ℂ) * Complex.I) *
            negLogDerivL χ ((1 / 4 : ℝ) + (u : ℂ) * Complex.I)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ u : ℝ, (g_in u + g_out u) := integral_mono hint_q.norm (hgin_int.add hgout_int) hpt
      _ = (∫ u : ℝ, g_in u) + (∫ u : ℝ, g_out u) := integral_add hgin_int hgout_int
  rw [norm_mul]
  calc ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ *
        ‖∫ u : ℝ, mellin (scaledTiltedBump Y t) ((1 / 4 : ℝ) + (u : ℂ) * Complex.I) *
          negLogDerivL χ ((1 / 4 : ℝ) + (u : ℂ) * Complex.I)‖
      ≤ 1 * ((∫ u : ℝ, g_in u) + (∫ u : ℝ, g_out u)) :=
        mul_le_mul h1_2pi hint_le (norm_nonneg _) zero_le_one
    _ ≤ 500000000000 * Real.sqrt ((Y : ℝ) * B) * L := by linarith only [hint_in, hint_out]

/-- **Module A4 Main Theorem (`primitive_smoothedTwist_bound`)**:
Under `DirichletGRH`, every primitive Dirichlet character `χ mod d`, every `Y ≥ 2`, and every
`|t| ≤ 1/2` satisfies the sharp single-logarithm bound
`‖smoothedTiltedRemainder χ Y t‖ ≤ 600000000000 * √(Y * (1 + |t| * Y)) * log(2 * d * Y)`. -/
theorem primitive_smoothedTwist_bound (hGRH : DirichletGRH) {Y d : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) {t : ℝ}
    (hY : 2 ≤ Y) (ht : |t| ≤ 1 / 2) :
    ‖smoothedTiltedRemainder χ Y t‖ ≤
      600000000000 * Real.sqrt ((Y : ℝ) * (1 + |t| * (Y : ℝ))) * Real.log (2 * (d : ℝ) * (Y : ℝ)) := by
  have hY1 : 1 ≤ Y := by omega
  have hY2 : (2 : ℝ) ≤ Y := Nat.ofNat_le_cast.mpr hY
  set B : ℝ := 1 + |t| * (Y : ℝ)
  have hB1 : 1 ≤ B := by dsimp [B]; linarith [mul_nonneg (abs_nonneg t) (Nat.cast_nonneg (α := ℝ) Y)]
  have hB_le_Y : B ≤ (Y : ℝ) := by dsimp [B]; nlinarith only [ht, hY2]
  set L : ℝ := Real.log (2 * (d : ℝ) * (Y : ℝ))
  have hL1 : 1 ≤ L := one_le_log_two_d_Y (d := d) hY
  -- Rewrite `smoothedTiltedRemainder χ Y t` via Module A3's explicit formula.
  have hrem_eq : smoothedTiltedRemainder χ Y t =
      (if χ = 1 then
        mellin (scaledTiltedBump Y t) 1 - ∑ n ∈ Finset.Icc 1 Y, scaledTiltedBump Y t (n : ℝ)
      else 0) -
      (∑' ρ : ℂ, zeroTerm χ Y t ρ) +
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ u : ℝ, mellin (scaledTiltedBump Y t) ((1 / 4 : ℝ) + (u : ℂ) * Complex.I) *
          negLogDerivL χ ((1 / 4 : ℝ) + (u : ℂ) * Complex.I) := by
    have hsplit : smoothedTiltedRemainder χ Y t =
        (∑ n ∈ Finset.Icc 1 Y,
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod d) * scaledTiltedBump Y t (n : ℝ)) -
        (if χ = 1 then ∑ n ∈ Finset.Icc 1 Y, scaledTiltedBump Y t (n : ℝ) else 0) := by
      unfold smoothedTiltedRemainder scaledTiltedBump
      simp_rw [sub_mul, Finset.sum_sub_distrib]
      congr 1
      · refine Finset.sum_congr rfl fun n _ => by ring
      · split_ifs
        · refine Finset.sum_congr rfl fun n _ => by ring
        · simp
    rw [hsplit, primitive_smoothed_explicit_formula hGRH hprim hY t]
    split_ifs <;> ring
  rw [hrem_eq]
  have hb_princ : ‖if χ = 1 then
      mellin (scaledTiltedBump Y t) 1 - ∑ n ∈ Finset.Icc 1 Y, scaledTiltedBump Y t (n : ℝ)
      else 0‖ ≤ 8 * Real.sqrt ((Y : ℝ) * B) * L := by
    split_ifs
    · have h1 := principal_integral_sub_sum_le hY1 t
      have hB_le_sqrt : B ≤ Real.sqrt ((Y : ℝ) * B) := by
        rw [Real.le_sqrt (by linarith only [hB1]) (by positivity)]
        nlinarith only [hB_le_Y, hB1]
      have hnn : 0 ≤ Real.sqrt ((Y : ℝ) * B) := Real.sqrt_nonneg _
      nlinarith only [h1, hB_le_sqrt, hL1, hnn]
    · rw [norm_zero]; positivity
  have hb_zeros := norm_tsum_zeroTerm_le hGRH hprim hY ht
  have hb_quarter := norm_quarter_integral_le hGRH hprim hY ht
  have htri1 := norm_add_le
    ((if χ = 1 then
      mellin (scaledTiltedBump Y t) 1 - ∑ n ∈ Finset.Icc 1 Y, scaledTiltedBump Y t (n : ℝ)
    else 0) - (∑' ρ : ℂ, zeroTerm χ Y t ρ))
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ u : ℝ, mellin (scaledTiltedBump Y t) ((1 / 4 : ℝ) + (u : ℂ) * Complex.I) *
        negLogDerivL χ ((1 / 4 : ℝ) + (u : ℂ) * Complex.I))
  have htri2 := norm_sub_le
    (if χ = 1 then
      mellin (scaledTiltedBump Y t) 1 - ∑ n ∈ Finset.Icc 1 Y, scaledTiltedBump Y t (n : ℝ)
    else 0)
    (∑' ρ : ℂ, zeroTerm χ Y t ρ)
  have hnn : 0 ≤ Real.sqrt ((Y : ℝ) * B) * L := by positivity
  linarith only [htri1, htri2, hb_princ, hb_zeros, hb_quarter, hnn]

end ZeroSumAndQuarterBounds

end FareyGoldbach
