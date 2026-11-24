import FareyGoldbach.Defs
import FareyGoldbach.CharacterBound
import FareyGoldbach.VoronoiCells
import FareyGoldbach.SingularSeries
import FareyGoldbach.PrimeSums
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Modules B3 & C3: Piecewise Farey Model, Remainder Sup Bound, L² Bound, and Main-Term Lower Bound

This module defines the piecewise Farey model `modelSum` on the weighted Voronoi partition
`voronoiCell Q c` with cutoff `Q₀ = Q / 2^24`, and proves:

1. **Module B3a (`remainder_sup_le`)**: assuming `SmoothedTwistEstimate`, for every `α : ℝ`,
   `‖smoothedPrimeSum r b Y α - modelSum r b Y Q Q₀ α‖ ≤ C_rem * Y^(3/4) * r^(-1/4) * log(2Y)`.
2. **Module B3b (`modelSum_l2_le`)**:
   `∫ α in 0..1, ‖modelSum r b Y Q Q₀ α‖² ≤ 36 * (r / φ(r)) * (Y / r) * log(2Y)`.
3. **Module C3 (`modelSum_conv_re_lower`)**: for admissible even `n = r * k + b₁ + b₂ ∈ (Y/2, Y]`
   with `singularTrunc` lower bound active,
   `(∫ α in 0..1, modelSum₁ α * modelSum₂ α * e(-k * α)).re ≥ (1 / 262144) * (r / φ(r))² * (Y / r)`.
-/

open scoped BigOperators

namespace FareyGoldbach

section ModelDefinition

/-- Arithmetic coefficient at rational center `c = a / q` for progression `b mod r`. -/
noncomputable def modelCoeff (r b : ℕ) (c : RatCenter) : ℂ :=
  if Nat.Coprime c.q r then
    e (-((c.a : ℝ) * (rInv r c.q : ℝ) * (b : ℝ) / (c.q : ℝ))) *
      (((r : ℝ) / (r.totient : ℝ) : ℝ) : ℂ) *
      ((ArithmeticFunction.moebius c.q : ℂ) / (c.q.totient : ℂ))
  else 0

/-- Piecewise Farey model supported on Voronoi cells with denominator `c.q ≤ Q₀`. -/
noncomputable def modelSum (r b Y Q Q₀ : ℕ) (α : ℝ) : ℂ :=
  ∑ c ∈ (centers Q).filter (fun c => c.q ≤ Q₀),
    (voronoiCell Q c).indicator
      (fun x => modelCoeff r b c * smoothedKernel r b Y (wrap (x - c.val))) α

lemma smoothedKernel_wrap (r b Y : ℕ) (β : ℝ) :
    smoothedKernel r b Y (wrap β) = smoothedKernel r b Y β := by
  unfold smoothedKernel
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  unfold wrap
  apply e_eq_of_sub_int (k := -(round β * (j : ℤ)))
  push_cast; ring

lemma smoothedKernel_periodic (r b Y : ℕ) : Function.Periodic (smoothedKernel r b Y) 1 := by
  intro β
  unfold smoothedKernel
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have : (β + 1) * (j : ℝ) = β * (j : ℝ) + (j : ℤ) := by push_cast; ring
  rw [this, e_add_int]

/-- Helper: finite sum of continuous functions is continuous. -/
lemma continuous_sum_finset {ι X E : Type*} [TopologicalSpace X] [AddCommMonoid E]
    [TopologicalSpace E] [ContinuousAdd E] (s : Finset ι) {f : ι → X → E}
    (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [continuous_const]
  | @insert i t hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

lemma continuous_smoothedKernel (r b Y : ℕ) : Continuous (smoothedKernel r b Y) := by
  unfold smoothedKernel
  refine continuous_sum_finset _ fun j _ => ?_
  have h : (fun β : ℝ => (quarticBump ((r * j + b : ℝ) / (Y : ℝ)) : ℂ) * e (β * (j : ℝ))) =
      fun β : ℝ => (quarticBump ((r * j + b : ℝ) / (Y : ℝ)) : ℂ) * e ((j : ℝ) * β) := by
    funext β; rw [mul_comm β]
  rw [h]
  exact continuous_const.mul (continuous_e_mul (j : ℝ))

lemma continuous_smoothedPrimeSum (r b Y : ℕ) : Continuous (smoothedPrimeSum r b Y) := by
  unfold smoothedPrimeSum
  refine continuous_sum_finset _ fun j _ => ?_
  have h : (fun α : ℝ => ((quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * primeWeight (r * j + b) : ℝ) : ℂ) * e (α * (j : ℝ))) =
      fun α : ℝ => ((quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * primeWeight (r * j + b) : ℝ) : ℂ) * e ((j : ℝ) * α) := by
    funext α; rw [mul_comm α]
  rw [h]
  exact continuous_const.mul (continuous_e_mul (j : ℝ))

lemma modelSum_eq_on_cell_le {r b Y Q Q₀ : ℕ} {c : RatCenter} {α : ℝ}
    (hα : α ∈ voronoiCell Q c) (hc : c.q ≤ Q₀) :
    modelSum r b Y Q Q₀ α = modelCoeff r b c * smoothedKernel r b Y (wrap (α - c.val)) := by
  unfold modelSum
  have hc_mem : c ∈ (centers Q).filter (fun c' => c'.q ≤ Q₀) :=
    Finset.mem_filter.mpr ⟨hα.1, hc⟩
  rw [Finset.sum_eq_single c]
  · exact Set.indicator_of_mem hα _
  · intro c' _ hne
    have hnot : α ∉ voronoiCell Q c' :=
      Set.disjoint_left.mp (voronoiCell_disjoint hne.symm) hα
    exact Set.indicator_of_notMem hnot _
  · intro hnot; exact absurd hc_mem hnot

lemma modelSum_eq_zero_on_cell_gt {r b Y Q Q₀ : ℕ} {c : RatCenter} {α : ℝ}
    (hα : α ∈ voronoiCell Q c) (hc : Q₀ < c.q) :
    modelSum r b Y Q Q₀ α = 0 := by
  unfold modelSum
  apply Finset.sum_eq_zero
  intro c' hc'
  have hc'_le : c'.q ≤ Q₀ := (Finset.mem_filter.mp hc').2
  have hne : c ≠ c' := by intro h; subst h; omega
  have hnot : α ∉ voronoiCell Q c' :=
    Set.disjoint_left.mp (voronoiCell_disjoint hne) hα
  exact Set.indicator_of_notMem hnot _

lemma modelSum_periodic (r b Y Q Q₀ : ℕ) : Function.Periodic (modelSum r b Y Q Q₀) 1 := by
  intro α
  unfold modelSum
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hα : α ∈ voronoiCell Q c
  · have hα1 : α + 1 ∈ voronoiCell Q c := (voronoiCell_periodic Q c α).2 hα
    rw [Set.indicator_of_mem hα1, Set.indicator_of_mem hα]
    have hsub : α + 1 - c.val = (α - c.val) + 1 := by ring
    rw [hsub, wrap_add_one]
  · have hα1 : α + 1 ∉ voronoiCell Q c := fun h => hα ((voronoiCell_periodic Q c α).1 h)
    rw [Set.indicator_of_notMem hα1, Set.indicator_of_notMem hα]

lemma modelTerm_measurable (r b Y Q : ℕ) (c : RatCenter) :
    Measurable ((voronoiCell Q c).indicator
      (fun x => modelCoeff r b c * smoothedKernel r b Y (wrap (x - c.val)))) := by
  refine Measurable.indicator ?_ (voronoiCell_measurable Q c)
  exact measurable_const.mul
    ((continuous_smoothedKernel r b Y).measurable.comp
      (measurable_wrap.comp (measurable_id.sub measurable_const)))

lemma modelSum_measurable (r b Y Q Q₀ : ℕ) : Measurable (modelSum r b Y Q Q₀) := by
  unfold modelSum
  exact Finset.measurable_sum _ fun c _ => modelTerm_measurable r b Y Q c

lemma modelSum_norm_bounded (r b Y Q Q₀ : ℕ) :
    ∃ B : ℝ, ∀ α : ℝ, ‖modelSum r b Y Q Q₀ α‖ ≤ B := by
  refine ⟨∑ c ∈ (centers Q).filter (fun c => c.q ≤ Q₀),
    ‖modelCoeff r b c‖ * ((Y : ℝ) / (r : ℝ) + 1), fun α => ?_⟩
  unfold modelSum
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  by_cases hα : α ∈ voronoiCell Q c
  · rw [Set.indicator_of_mem hα, norm_mul]
    exact mul_le_mul_of_nonneg_left (smoothedKernel_bound_triv r b Y _) (norm_nonneg _)
  · rw [Set.indicator_of_notMem hα, norm_zero]
    exact mul_nonneg (norm_nonneg _) (by positivity)

lemma intervalIntegrable_of_measurable_bounded {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {f : ℝ → E} {a b B : ℝ} (hf : Measurable f) (hB : ∀ x, ‖f x‖ ≤ B) :
    IntervalIntegrable f MeasureTheory.volume a b := by
  have hfin : MeasureTheory.volume (Set.uIoc a b) ≠ ⊤ := by
    simp [Set.uIoc, Real.volume_Ioc]
  have h1 : MeasureTheory.IntegrableOn f (Set.uIoc a b) MeasureTheory.volume := by
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrableOn_const (hs := hfin) (C := B))
      hf.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall hB
  exact (intervalIntegrable_iff.mpr h1)

lemma modelSum_intervalIntegrable (r b Y Q Q₀ : ℕ) (a₁ a₂ : ℝ) :
    IntervalIntegrable (modelSum r b Y Q Q₀) MeasureTheory.volume a₁ a₂ := by
  obtain ⟨B, hB⟩ := modelSum_norm_bounded r b Y Q Q₀
  exact intervalIntegrable_of_measurable_bounded (modelSum_measurable r b Y Q Q₀) hB

end ModelDefinition

section PrincipalBlockApprox

/-- Comparing the un-restricted smoothed exponential sum `∑_{1 ≤ n ≤ Y} w(n/Y) e((β/r) n)`
with `r * smoothedKernel r b Y β` pays only `16 * r + 14 * Y * |β|`. -/
lemma principalSum_approx_smoothedKernel {r b Y : ℕ} (hr : 0 < r) (hb : b < r) (hrY : r ≤ Y)
    (β : ℝ) :
    ‖e (-((β * (b : ℝ)) / (r : ℝ))) *
        (∑ n ∈ Finset.Icc 1 Y,
          (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * e ((β / (r : ℝ)) * (n : ℝ))) -
      (r : ℂ) * smoothedKernel r b Y β‖ ≤
      16 * (r : ℝ) + 16 * (Y : ℝ) * |β| := by
  have hY_pos : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
  have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  -- Rewrite the `Icc 1 Y` sum as a double sum over `j ∈ range (Y / r + 1)` and `u ∈ range r`.
  have hdouble :
      e (-((β * (b : ℝ)) / (r : ℝ))) *
        (∑ n ∈ Finset.Icc 1 Y,
          (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * e ((β / (r : ℝ)) * (n : ℝ))) =
      ∑ j ∈ Finset.range (Y / r + 1), ∑ u ∈ Finset.range r,
        (quarticBump (((r * j + u : ℕ) : ℝ) / (Y : ℝ)) : ℂ) *
          e (β * (j : ℝ)) * e (β * ((u : ℝ) - (b : ℝ)) / (r : ℝ)) := by
    rw [Finset.mul_sum]
    -- Reindex `(j, u) ↦ r * j + u` and drop terms outside `Icc 1 Y` where `quarticBump = 0`.
    let S := ((Finset.range (Y / r + 1)).product (Finset.range r)).filter
      (fun ju => 1 ≤ r * ju.1 + ju.2 ∧ r * ju.1 + ju.2 ≤ Y)
    have hprod : ∑ j ∈ Finset.range (Y / r + 1), ∑ u ∈ Finset.range r,
          (quarticBump (((r * j + u : ℕ) : ℝ) / (Y : ℝ)) : ℂ) *
            e (β * (j : ℝ)) * e (β * ((u : ℝ) - (b : ℝ)) / (r : ℝ)) =
        ∑ ju ∈ S,
          (quarticBump (((r * ju.1 + ju.2 : ℕ) : ℝ) / (Y : ℝ)) : ℂ) *
            e (β * (ju.1 : ℝ)) * e (β * ((ju.2 : ℝ) - (b : ℝ)) / (r : ℝ)) := by
      rw [← Finset.sum_product']
      symm
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun ju _ => ?_
      split_ifs with h
      · rfl
      · have hw0 : quarticBump (((r * ju.1 + ju.2 : ℕ) : ℝ) / (Y : ℝ)) = 0 := by
          unfold quarticBump
          have hnot : ¬ (0 < ((r * ju.1 + ju.2 : ℕ) : ℝ) / (Y : ℝ) ∧
              ((r * ju.1 + ju.2 : ℕ) : ℝ) / (Y : ℝ) < 1) := by
            rintro ⟨h1, h2⟩
            have h1' : (0 : ℕ) < r * ju.1 + ju.2 := by
              exact_mod_cast (div_pos_iff_of_pos_right hY_pos).1 h1
            have h2' : r * ju.1 + ju.2 < Y := by
              exact_mod_cast (div_lt_one hY_pos).1 h2
            exact h ⟨by omega, by omega⟩
          exact ite_eq_right hnot
        rw [hw0]; simp
    rw [hprod]
    symm
    refine Finset.sum_bij (fun ju _ => r * ju.1 + ju.2) ?_ ?_ ?_ ?_
    · intro ju hju
      exact Finset.mem_Icc.mpr (Finset.mem_filter.mp hju).2
    · intro ju₁ hju₁ ju₂ hju₂ hEq
      have hu1 : ju₁.2 < r := Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_filter.mp hju₁).1).2
      have hu2 : ju₂.2 < r := Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_filter.mp hju₂).1).2
      have hdiv1 : (r * ju₁.1 + ju₁.2) / r = ju₁.1 := by
        rw [Nat.mul_add_div hr, Nat.div_eq_of_lt hu1, add_zero]
      have hdiv2 : (r * ju₂.1 + ju₂.2) / r = ju₂.1 := by
        rw [Nat.mul_add_div hr, Nat.div_eq_of_lt hu2, add_zero]
      have h1 : ju₁.1 = ju₂.1 := by rw [← hdiv1, ← hdiv2, hEq]
      have h2 : ju₁.2 = ju₂.2 := by rw [h1] at hEq; omega
      exact Prod.ext h1 h2
    · intro n hn
      have hn_Icc := Finset.mem_Icc.mp hn
      refine ⟨(n / r, n % r), ?_, Nat.div_add_mod n r⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hn_Icc.2))
      · exact Finset.mem_range.mpr (Nat.mod_lt n hr)
      · rw [Nat.div_add_mod n r]; exact hn_Icc
    · intro ju _
      have hexp : e (β * (ju.1 : ℝ)) * e (β * ((ju.2 : ℝ) - (b : ℝ)) / (r : ℝ)) =
          e (-((β * (b : ℝ)) / (r : ℝ))) * e ((β / (r : ℝ)) * ((r * ju.1 + ju.2 : ℕ) : ℝ)) := by
        rw [← e_add, ← e_add]
        congr 1
        push_cast
        field_simp [hr_pos.ne']
        ring
      calc (quarticBump (((r * ju.1 + ju.2 : ℕ) : ℝ) / (Y : ℝ)) : ℂ) *
              e (β * (ju.1 : ℝ)) * e (β * ((ju.2 : ℝ) - (b : ℝ)) / (r : ℝ))
          = (quarticBump (((r * ju.1 + ju.2 : ℕ) : ℝ) / (Y : ℝ)) : ℂ) *
              (e (β * (ju.1 : ℝ)) * e (β * ((ju.2 : ℝ) - (b : ℝ)) / (r : ℝ))) := by ring
        _ = (quarticBump (((r * ju.1 + ju.2 : ℕ) : ℝ) / (Y : ℝ)) : ℂ) *
              (e (-((β * (b : ℝ)) / (r : ℝ))) * e ((β / (r : ℝ)) * ((r * ju.1 + ju.2 : ℕ) : ℝ))) := by
            rw [hexp]
        _ = e (-((β * (b : ℝ)) / (r : ℝ))) *
              ((quarticBump (((r * ju.1 + ju.2 : ℕ) : ℝ) / (Y : ℝ)) : ℂ) *
                e ((β / (r : ℝ)) * ((r * ju.1 + ju.2 : ℕ) : ℝ))) := by ring
  have hrV : (r : ℂ) * smoothedKernel r b Y β =
      ∑ j ∈ Finset.range (Y / r + 1), ∑ _u ∈ Finset.range r,
        (quarticBump (((r * j + b : ℕ) : ℝ) / (Y : ℝ)) : ℂ) * e (β * (j : ℝ)) := by
    unfold smoothedKernel
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast; rfl
  rw [hdouble, hrV, ← Finset.sum_sub_distrib]
  have hterm : ∀ j ∈ Finset.range (Y / r + 1), ∀ u ∈ Finset.range r,
      ‖(quarticBump (((r * j + u : ℕ) : ℝ) / (Y : ℝ)) : ℂ) *
          e (β * (j : ℝ)) * e (β * ((u : ℝ) - (b : ℝ)) / (r : ℝ)) -
        (quarticBump (((r * j + b : ℕ) : ℝ) / (Y : ℝ)) : ℂ) * e (β * (j : ℝ))‖ ≤
        8 * (r : ℝ) / (Y : ℝ) + 8 * |β| := by
    intro j _ u hu
    have hu_lt : u < r := Finset.mem_range.mp hu
    have hsplit :
        (quarticBump (((r * j + u : ℕ) : ℝ) / (Y : ℝ)) : ℂ) *
          e (β * (j : ℝ)) * e (β * ((u : ℝ) - (b : ℝ)) / (r : ℝ)) -
        (quarticBump (((r * j + b : ℕ) : ℝ) / (Y : ℝ)) : ℂ) * e (β * (j : ℝ)) =
        (((quarticBump (((r * j + u : ℕ) : ℝ) / (Y : ℝ)) -
            quarticBump (((r * j + b : ℕ) : ℝ) / (Y : ℝ)) : ℝ) : ℂ) *
            e (β * ((u : ℝ) - (b : ℝ)) / (r : ℝ)) +
          (quarticBump (((r * j + b : ℕ) : ℝ) / (Y : ℝ)) : ℂ) *
            (e (β * ((u : ℝ) - (b : ℝ)) / (r : ℝ)) - 1)) * e (β * (j : ℝ)) := by
      push_cast; ring
    rw [hsplit, norm_mul, norm_e, mul_one]
    have h1 : ‖((quarticBump (((r * j + u : ℕ) : ℝ) / (Y : ℝ)) -
          quarticBump (((r * j + b : ℕ) : ℝ) / (Y : ℝ)) : ℝ) : ℂ) *
          e (β * ((u : ℝ) - (b : ℝ)) / (r : ℝ))‖ ≤ 8 * (r : ℝ) / (Y : ℝ) := by
      rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs]
      have hlip := quarticBump_lipschitz (((r * j + u : ℕ) : ℝ) / (Y : ℝ)) (((r * j + b : ℕ) : ℝ) / (Y : ℝ))
      have hdiff : |(((r * j + u : ℕ) : ℝ) / (Y : ℝ)) - (((r * j + b : ℕ) : ℝ) / (Y : ℝ))| ≤ (r : ℝ) / (Y : ℝ) := by
        rw [← sub_div, abs_div, abs_of_pos hY_pos]
        apply div_le_div_of_nonneg_right _ hY_pos.le
        have hsub : ((r * j + u : ℕ) : ℝ) - ((r * j + b : ℕ) : ℝ) = (u : ℝ) - (b : ℝ) := by
          push_cast; ring
        rw [hsub, abs_le]
        have huR : (u : ℝ) ≤ r := Nat.cast_le.mpr hu_lt.le
        have hbR : (b : ℝ) ≤ r := Nat.cast_le.mpr hb.le
        exact ⟨by linarith [Nat.cast_nonneg (α := ℝ) u], by linarith [Nat.cast_nonneg (α := ℝ) b]⟩
      calc |quarticBump (((r * j + u : ℕ) : ℝ) / (Y : ℝ)) - quarticBump (((r * j + b : ℕ) : ℝ) / (Y : ℝ))|
          ≤ 8 * |(((r * j + u : ℕ) : ℝ) / (Y : ℝ)) - (((r * j + b : ℕ) : ℝ) / (Y : ℝ))| := hlip
        _ ≤ 8 * ((r : ℝ) / (Y : ℝ)) := mul_le_mul_of_nonneg_left hdiff (by norm_num)
        _ = 8 * (r : ℝ) / (Y : ℝ) := by ring
    have h2 : ‖(quarticBump (((r * j + b : ℕ) : ℝ) / (Y : ℝ)) : ℂ) *
          (e (β * ((u : ℝ) - (b : ℝ)) / (r : ℝ)) - 1)‖ ≤ 8 * |β| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (quarticBump_nonneg _)]
      have hw1 : quarticBump (((r * j + b : ℕ) : ℝ) / (Y : ℝ)) ≤ 1 := quarticBump_le_one _
      have he1 := norm_e_sub_one_le (β * ((u : ℝ) - (b : ℝ)) / (r : ℝ))
      have habs_ub : |(u : ℝ) - (b : ℝ)| ≤ (r : ℝ) := by
        rw [abs_le]
        have huR : (u : ℝ) ≤ r := Nat.cast_le.mpr hu_lt.le
        have hbR : (b : ℝ) ≤ r := Nat.cast_le.mpr hb.le
        exact ⟨by linarith [Nat.cast_nonneg (α := ℝ) u], by linarith [Nat.cast_nonneg (α := ℝ) b]⟩
      have harg : |β * ((u : ℝ) - (b : ℝ)) / (r : ℝ)| ≤ |β| := by
        rw [abs_div, abs_mul, abs_of_pos hr_pos, div_le_iff₀ hr_pos]
        exact mul_le_mul_of_nonneg_left habs_ub (abs_nonneg β)
      have h2pi : 2 * Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
      calc quarticBump (((r * j + b : ℕ) : ℝ) / (Y : ℝ)) * ‖e (β * ((u : ℝ) - (b : ℝ)) / (r : ℝ)) - 1‖
          ≤ 1 * (2 * Real.pi * |β * ((u : ℝ) - (b : ℝ)) / (r : ℝ)|) :=
            mul_le_mul hw1 he1 (norm_nonneg _) zero_le_one
        _ ≤ 2 * Real.pi * |β| := by
            rw [one_mul]; exact mul_le_mul_of_nonneg_left harg (by positivity)
        _ ≤ 8 * |β| := mul_le_mul_of_nonneg_right h2pi (abs_nonneg β)
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  have hcard_j : ((Y / r + 1 : ℕ) : ℝ) ≤ 2 * ((Y : ℝ) / (r : ℝ)) := by
    have hdiv : ((Y / r : ℕ) : ℝ) ≤ (Y : ℝ) / (r : ℝ) := by
      rw [le_div_iff₀ hr_pos]; exact_mod_cast (by simpa [mul_comm] using Nat.mul_div_le Y r)
    have h1 : (1 : ℝ) ≤ (Y : ℝ) / (r : ℝ) := (one_le_div hr_pos).2 (Nat.cast_le.mpr hrY)
    push_cast; linarith
  calc ‖∑ j ∈ Finset.range (Y / r + 1),
          (∑ u ∈ Finset.range r,
            (quarticBump (((r * j + u : ℕ) : ℝ) / (Y : ℝ)) : ℂ) *
              e (β * (j : ℝ)) * e (β * ((u : ℝ) - (b : ℝ)) / (r : ℝ)) -
          ∑ _u ∈ Finset.range r,
            (quarticBump (((r * j + b : ℕ) : ℝ) / (Y : ℝ)) : ℂ) * e (β * (j : ℝ)))‖
      ≤ ∑ j ∈ Finset.range (Y / r + 1),
          ‖∑ u ∈ Finset.range r,
            ((quarticBump (((r * j + u : ℕ) : ℝ) / (Y : ℝ)) : ℂ) *
              e (β * (j : ℝ)) * e (β * ((u : ℝ) - (b : ℝ)) / (r : ℝ)) -
             (quarticBump (((r * j + b : ℕ) : ℝ) / (Y : ℝ)) : ℂ) * e (β * (j : ℝ)))‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [Finset.sum_sub_distrib]
    _ ≤ ∑ j ∈ Finset.range (Y / r + 1), ∑ _u ∈ Finset.range r, (8 * (r : ℝ) / (Y : ℝ) + 8 * |β|) := by
        refine Finset.sum_le_sum fun j hj => (norm_sum_le _ _).trans (Finset.sum_le_sum fun u hu => hterm j hj u hu)
    _ = ((Y / r + 1 : ℕ) : ℝ) * (r : ℝ) * (8 * (r : ℝ) / (Y : ℝ) + 8 * |β|) := by
        simp [nsmul_eq_mul, mul_assoc]; ring
    _ ≤ (2 * ((Y : ℝ) / (r : ℝ))) * (r : ℝ) * (8 * (r : ℝ) / (Y : ℝ) + 8 * |β|) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard_j hr_pos.le) (by positivity)
    _ = 16 * (r : ℝ) + 16 * (Y : ℝ) * |β| := by field_simp [hr_pos.ne', hY_pos.ne']; ring

end PrincipalBlockApprox

section RemainderSup

/-- Elementary `log(2Y) ≤ 4 * √Y` for `Y ≥ 1`. -/
lemma log_two_mul_le_four_sqrt {Y : ℕ} (hY : 1 ≤ Y) :
    Real.log (2 * (Y : ℝ)) ≤ 4 * Real.sqrt (Y : ℝ) := by
  have hY_pos : (0 : ℝ) < Y := Nat.cast_pos.mpr hY
  have hsq : Real.log (Real.sqrt (2 * (Y : ℝ))) ≤ Real.sqrt (2 * (Y : ℝ)) := by
    linarith [Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 2 * Y))]
  have hlog : Real.log (2 * (Y : ℝ)) = 2 * Real.log (Real.sqrt (2 * (Y : ℝ))) := by
    rw [Real.log_sqrt (by positivity)]; ring
  have hsq2 : Real.sqrt (2 * (Y : ℝ)) ≤ 2 * Real.sqrt (Y : ℝ) := by
    rw [Real.sqrt_mul (by norm_num)]
    have : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
    nlinarith [Real.sqrt_nonneg (Y : ℝ)]
  linarith

/-- Elementary `1 ≤ log(2Y)` for `Y ≥ 2`. -/
lemma one_le_log_two_mul {Y : ℕ} (hY : 2 ≤ Y) : (1 : ℝ) ≤ Real.log (2 * (Y : ℝ)) := by
  have h : Real.exp 1 ≤ 2 * (Y : ℝ) := by
    have hY2 : (2 : ℝ) ≤ Y := Nat.cast_le.mpr hY
    linarith [Real.exp_one_lt_d9]
  have := Real.log_le_log (Real.exp_pos 1) h
  rwa [Real.log_exp] at this

/-- Standalone `rpow` identity: `√(y * √(y / r)) = y^(3/4) * r^(-1/4)` for `y, r > 0`. -/
lemma sqrt_mul_sqrt_div {y r : ℝ} (hy : 0 < y) (hr : 0 < r) :
    Real.sqrt (y * Real.sqrt (y / r)) = y ^ ((3 : ℝ) / 4) * r ^ (-(1 : ℝ) / 4) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.div_rpow hy.le hr.le,
      mul_div_assoc', ← Real.rpow_one_add' hy.le (by norm_num),
      Real.div_rpow (by positivity) (by positivity), ← Real.rpow_mul hy.le,
      ← Real.rpow_mul hr.le, div_eq_mul_inv, ← Real.rpow_neg hr.le]
  norm_num

set_option maxHeartbeats 800000 in
/-- **Module B3a (Uniform remainder sup bound on `[0, 1]`):**
Assuming `SmoothedTwistEstimate` with constant `C > 0`, for `Q = Nat.sqrt (Y / r)`,
`Q₀ = Q / 2^24`, `1 ≤ r ≤ Y`, and `2^25 ≤ Q`, we have uniformly for all `α : ℝ`:
`‖smoothedPrimeSum r b Y α - modelSum r b Y Q Q₀ α‖ ≤ (C_rem) * Y^(3/4) * r^(-1/4) * log(2Y)`. -/
theorem remainder_sup_le {C : ℝ} (hC : 0 < C)
    (hTw : ∀ (Y d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (t : ℝ),
      2 ≤ Y → |t| ≤ 1 / 2 →
        ‖smoothedTiltedRemainder χ Y t‖ ≤
          C * Real.sqrt ((Y : ℝ) * (1 + |t| * Y)) * Real.log (2 * (d : ℝ) * Y))
    {r b Y : ℕ} (hr : 0 < r) (hrY : r ≤ Y) (hb : b < r) (hbr : Nat.Coprime b r)
    (hQ_ge : 2 ^ 25 ≤ Nat.sqrt (Y / r)) (α : ℝ) :
    ‖smoothedPrimeSum r b Y α - modelSum r b Y (Nat.sqrt (Y / r)) (Nat.sqrt (Y / r) / 2 ^ 24) α‖ ≤
      (6 * C + ((2 : ℝ) ^ 144) ^ 2) *
        (Y : ℝ) ^ ((3 : ℝ) / 4) * (r : ℝ) ^ (-(1 : ℝ) / 4) * Real.log (2 * (Y : ℝ)) := by
  classical
  set Q := Nat.sqrt (Y / r)
  set Q₀ := Q / 2 ^ 24
  have hQ_pos : 0 < Q := by omega
  have hQ0_pos : 0 < Q₀ := by dsimp [Q₀]; omega
  have hYr_ge : 2 ^ 50 ≤ Y / r := by
    have h1 : Q * Q ≤ Y / r := Nat.sqrt_le (Y / r)
    have h2 : 2 ^ 25 * 2 ^ 25 ≤ Q * Q := Nat.mul_le_mul hQ_ge hQ_ge
    have h3 : 2 ^ 50 = 2 ^ 25 * 2 ^ 25 := by norm_num
    omega
  have hY_ge2 : 2 ≤ Y := by
    have : 1 ≤ Y / r := by omega
    have := Nat.mul_div_le Y r
    nlinarith
  have hY_pos : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
  have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hlog1 : (1 : ℝ) ≤ Real.log (2 * (Y : ℝ)) := one_le_log_two_mul hY_ge2
  set M := (Y : ℝ) ^ ((3 : ℝ) / 4) * (r : ℝ) ^ (-(1 : ℝ) / 4)
  have hM_pos : 0 < M := by positivity
  have hsqrtY_le_M : Real.sqrt (Y : ℝ) ≤ M := by
    have hr_le : (r : ℝ) ≤ Y := Nat.cast_le.mpr hrY
    have hrpow : (Y : ℝ) ^ (-(1 : ℝ) / 4) ≤ (r : ℝ) ^ (-(1 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_nonpos hr_pos hr_le (by norm_num)
    calc Real.sqrt (Y : ℝ) = (Y : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
      _ = (Y : ℝ) ^ ((3 : ℝ) / 4) * (Y : ℝ) ^ (-(1 : ℝ) / 4) := by
          rw [← Real.rpow_add hY_pos]; norm_num
      _ ≤ M := mul_le_mul_of_nonneg_left hrpow (by positivity)
  have hQ_bounds : (1 / 2 : ℝ) * Real.sqrt ((Y : ℝ) / (r : ℝ)) ≤ (Q : ℝ) ∧
      (Q : ℝ) ≤ Real.sqrt ((Y : ℝ) / (r : ℝ)) := by
    constructor
    · have hsucc : Y / r < (Q + 1) * (Q + 1) := Nat.lt_succ_sqrt (Y / r)
      have hdiv : (Y : ℝ) / (r : ℝ) ≤ ((Y / r + 1 : ℕ) : ℝ) := by
        have h1 := Nat.div_add_mod Y r
        have h2 := Nat.mod_lt Y hr
        rw [div_le_iff₀ hr_pos]
        exact_mod_cast (by nlinarith : Y ≤ (Y / r + 1) * r)
      have hsq : (Y : ℝ) / (r : ℝ) ≤ ((2 * Q : ℕ) : ℝ) ^ 2 := by
        have hQ1 : Q + 1 ≤ 2 * Q := by omega
        have hnat : Y / r + 1 ≤ (2 * Q) ^ 2 := by nlinarith
        exact hdiv.trans (by exact_mod_cast hnat)
      have hrt := Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_sq (by positivity)] at hrt
      push_cast at hrt
      linarith
    · rw [Real.le_sqrt (Nat.cast_nonneg _) (by positivity)]
      have h1 : Q * Q ≤ Y / r := Nat.sqrt_le (Y / r)
      have h2 : ((Y / r : ℕ) : ℝ) ≤ (Y : ℝ) / (r : ℝ) := by
        rw [le_div_iff₀ hr_pos]; exact_mod_cast (by simpa [mul_comm] using Nat.mul_div_le Y r)
      have h3 : (Q : ℝ) ^ 2 ≤ ((Y / r : ℕ) : ℝ) := by exact_mod_cast (by simpa [sq] using h1)
      exact h3.trans h2
  -- Locate the unique Voronoi cell `c ∈ centers Q` containing `α`.
  obtain ⟨c, hc_mem, hα_cell⟩ := voronoiCell_cover Q hQ_pos α
  set q := c.q
  set a := c.a
  have hq_pos : 0 < q := c.q_pos
  have hq_le_Q : q ≤ Q := mem_centers_iff.mp hc_mem
  have ha_cop : Nat.Coprime a q := c.coprime
  have : NeZero (r * q) := ⟨Nat.mul_ne_zero hr.ne' hq_pos.ne'⟩
  set β := wrap (α - c.val)
  have hβ_half : |β| ≤ 1 / 2 := abs_wrap_le_half _
  have hβ_outer : |β| ≤ 1 / ((q : ℝ) * (Q : ℝ)) := voronoiCell_outer_radius hQ_pos hα_cell
  -- Step 1: Express `smoothedPrimeSum r b Y α` via `e(a*j/q) * e(β*j)` and compare `primeWeight` with `vonMangoldt`.
  let S_vm : ℂ := ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => n % r = b),
    (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      e ((a : ℝ) * (n : ℝ) / ((r * q : ℕ) : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ))
  let phase : ℂ := e (-((a : ℝ) * (b : ℝ) / ((r * q : ℕ) : ℝ))) * e (-((β * (b : ℝ)) / (r : ℝ)))
  have hphase_norm : ‖phase‖ = 1 := by simp [phase, norm_e]
  have hstep1 : ‖smoothedPrimeSum r b Y α - phase * S_vm‖ ≤ Real.sqrt (Y : ℝ) * Real.log (Y : ℝ) := by
    -- Reindex `smoothedPrimeSum` to `n ∈ (Icc 1 Y).filter (fun n => n % r = b)` with `phase`.
    have hreidx : smoothedPrimeSum r b Y α =
        phase * ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => n % r = b),
          (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
            e ((a : ℝ) * (n : ℝ) / ((r * q : ℕ) : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ)) := by
      unfold smoothedPrimeSum
      rw [Finset.mul_sum]
      let J0 := (Finset.range (Y / r + 1)).filter (fun j => 1 ≤ r * j + b ∧ r * j + b ≤ Y)
      have htrim : ∑ j ∈ Finset.range (Y / r + 1),
          ((quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * primeWeight (r * j + b) : ℝ) : ℂ) * e (α * (j : ℝ)) =
          ∑ j ∈ J0,
            ((quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * primeWeight (r * j + b) : ℝ) : ℂ) * e (α * (j : ℝ)) := by
        symm; rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs with h
        · rfl
        · have hw0 : quarticBump ((r * j + b : ℝ) / (Y : ℝ)) = 0 := by
            unfold quarticBump
            have hnot : ¬ (0 < (r * j + b : ℝ) / (Y : ℝ) ∧ (r * j + b : ℝ) / (Y : ℝ) < 1) := by
              rintro ⟨h1, h2⟩
              have hcast : ((r * j + b : ℕ) : ℝ) = (r * j + b : ℝ) := by push_cast; rfl
              have h1' : (0 : ℕ) < r * j + b := by
                have := (div_pos_iff_of_pos_right hY_pos).1 h1
                rw [← hcast] at this; exact_mod_cast this
              have h2' : r * j + b < Y := by
                have := (div_lt_one hY_pos).1 h2
                rw [← hcast] at this; exact_mod_cast this
              exact h ⟨by omega, by omega⟩
            simp [hnot]
          simp [hw0]
      rw [htrim]
      refine Finset.sum_bij (fun j _ => r * j + b) ?_ ?_ ?_ ?_
      · intro j hj
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (Finset.mem_filter.mp hj).2, ?_⟩
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
      · intro j₁ _ j₂ _ hEq; exact Nat.eq_of_mul_eq_mul_left hr (by omega)
      · intro n hn
        have hIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
        have hmod := (Finset.mem_filter.mp hn).2
        have hnj : r * (n / r) + b = n := by have := Nat.div_add_mod n r; omega
        refine ⟨n / r, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hIcc.2)),
          hnj.symm ▸ hIcc.1, hnj.symm ▸ hIcc.2⟩, hnj⟩
      · intro j _
        have hα_e : e (α * (j : ℝ)) =
            phase * (e ((a : ℝ) * ((r * j + b : ℕ) : ℝ) / ((r * q : ℕ) : ℝ)) *
              e ((β / (r : ℝ)) * ((r * j + b : ℕ) : ℝ))) := by
          have h1 : e (α * (j : ℝ)) = e (c.val * (j : ℝ)) * e (β * (j : ℝ)) := by
            rw [← e_add]
            apply e_eq_of_sub_int (k := round (α - c.val) * (j : ℤ))
            dsimp [β, wrap]; push_cast; ring
          rw [h1]
          dsimp [phase, RatCenter.val, a, q]
          rw [← e_add, ← e_add, ← e_add, ← e_add]
          congr 1
          have hr0 : (r : ℝ) ≠ 0 := hr_pos.ne'
          have hq0 : (c.q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq_pos.ne'
          push_cast; field_simp [hr0, hq0]; ring
        rw [hα_e]; push_cast; ring
    rw [hreidx, ← mul_sub, norm_mul, hphase_norm, one_mul, ← Finset.sum_sub_distrib]
    calc ‖∑ n ∈ (Finset.Icc 1 Y).filter (fun n => n % r = b),
            ((quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
                e ((a : ℝ) * (n : ℝ) / ((r * q : ℕ) : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ)) -
             (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                e ((a : ℝ) * (n : ℝ) / ((r * q : ℕ) : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ)))‖
        ≤ ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => n % r = b),
            |ArithmeticFunction.vonMangoldt n - primeWeight n| := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
          have hfac : (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
                e ((a : ℝ) * (n : ℝ) / ((r * q : ℕ) : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ)) -
              (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                e ((a : ℝ) * (n : ℝ) / ((r * q : ℕ) : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ)) =
              (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * (((primeWeight n - ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) *
                e ((a : ℝ) * (n : ℝ) / ((r * q : ℕ) : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ)) := by
            push_cast; ring
          rw [hfac, norm_mul, norm_mul, norm_mul, norm_e, norm_e, mul_one, mul_one,
              Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (quarticBump_nonneg _), abs_sub_comm]
          exact mul_le_of_le_one_left (abs_nonneg _) (quarticBump_le_one _)
      _ ≤ ∑ n ∈ Finset.Icc 1 Y, |ArithmeticFunction.vonMangoldt n - primeWeight n| :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => abs_nonneg _
      _ ≤ Real.sqrt (Y : ℝ) * Real.log (Y : ℝ) := primePowerMass_le Y (by omega)
  -- Step 2: Split `S_vm` into coprime `(n, r * q) = 1` and non-coprime `(n, r * q) > 1`.
  let S_cop : ℂ := ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => n % r = b ∧ Nat.Coprime n (r * q)),
    (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      e ((a : ℝ) * (n : ℝ) / ((r * q : ℕ) : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ))
  have hstep2 : ‖phase * S_vm - phase * S_cop‖ ≤ 4 * Real.log (2 * (Y : ℝ)) * Real.log (2 * (Y : ℝ)) := by
    rw [← mul_sub, norm_mul, hphase_norm, one_mul]
    have hdiff : S_vm - S_cop =
        ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => n % r = b ∧ ¬ Nat.Coprime n (r * q)),
          (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            e ((a : ℝ) * (n : ℝ) / ((r * q : ℕ) : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ)) := by
      have hsp := (Finset.sum_filter_add_sum_filter_not
        ((Finset.Icc 1 Y).filter (fun n => n % r = b))
        (fun n => Nat.Coprime n (r * q))
        (fun n => (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          e ((a : ℝ) * (n : ℝ) / ((r * q : ℕ) : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ)))).symm
      have hf1 : ((Finset.Icc 1 Y).filter (fun n => n % r = b)).filter (fun n => Nat.Coprime n (r * q)) =
          (Finset.Icc 1 Y).filter (fun n => n % r = b ∧ Nat.Coprime n (r * q)) := by
        ext n; simp [and_assoc]
      have hf2 : ((Finset.Icc 1 Y).filter (fun n => n % r = b)).filter (fun n => ¬ Nat.Coprime n (r * q)) =
          (Finset.Icc 1 Y).filter (fun n => n % r = b ∧ ¬ Nat.Coprime n (r * q)) := by
        ext n; simp [and_assoc]
      rw [hf1, hf2] at hsp
      exact (eq_sub_of_add_eq' hsp.symm).symm
    rw [hdiff]
    have hlog_rq : Real.log (2 * ((r * q : ℕ) : ℝ)) ≤ 2 * Real.log (2 * (Y : ℝ)) := by
      have hqY : q ≤ Y := hq_le_Q.trans (by
        have h1 : Q * Q ≤ Y / r := Nat.sqrt_le (Y / r)
        have h2 : Y / r ≤ Y := Nat.div_le_self Y r
        nlinarith)
      have h2rq : 2 * ((r * q : ℕ) : ℝ) ≤ (2 * (Y : ℝ)) ^ 2 := by
        have hrY' : (r : ℝ) ≤ Y := Nat.cast_le.mpr hrY
        have hqY' : (q : ℝ) ≤ Y := Nat.cast_le.mpr hqY
        push_cast; nlinarith
      calc Real.log (2 * ((r * q : ℕ) : ℝ)) ≤ Real.log ((2 * (Y : ℝ)) ^ 2) :=
            Real.log_le_log (by positivity) h2rq
        _ = 2 * Real.log (2 * (Y : ℝ)) := by rw [Real.log_pow]; norm_num
    have hlogY : Real.log (Y : ℝ) ≤ Real.log (2 * (Y : ℝ)) :=
      Real.log_le_log hY_pos (by linarith)
    calc ‖∑ n ∈ (Finset.Icc 1 Y).filter (fun n => n % r = b ∧ ¬ Nat.Coprime n (r * q)),
            (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              e ((a : ℝ) * (n : ℝ) / ((r * q : ℕ) : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ))‖
        ≤ ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => n % r = b ∧ ¬ Nat.Coprime n (r * q)),
            ArithmeticFunction.vonMangoldt n := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
          rw [norm_mul, norm_mul, norm_mul, norm_e, norm_e, mul_one, mul_one,
              Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (quarticBump_nonneg _), abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (quarticBump_le_one _)
      _ ≤ ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => ¬ Nat.Coprime n (r * q)),
            ArithmeticFunction.vonMangoldt n := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
          intro n hn; exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1, (Finset.mem_filter.mp hn).2.2⟩
      _ ≤ 2 * Real.log (2 * ((r * q : ℕ) : ℝ)) * Real.log (Y : ℝ) :=
          nonCoprimeVonMangoldt_le Y (r * q) (by omega) (Nat.mul_pos hr hq_pos)
      _ ≤ 2 * (2 * Real.log (2 * (Y : ℝ))) * Real.log (2 * (Y : ℝ)) := by
          have hlogY_nn : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Y))
          exact mul_le_mul (mul_le_mul_of_nonneg_left hlog_rq (by norm_num)) hlogY hlogY_nn (by positivity)
      _ = 4 * Real.log (2 * (Y : ℝ)) * Real.log (2 * (Y : ℝ)) := by ring
  -- Step 3: Character expansion of `S_cop` into twist error + principal term!
  let principalSum : ℂ :=
    ∑ n ∈ Finset.Icc 1 Y, (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * e ((β / (r : ℝ)) * (n : ℝ))
  let twistSum : ℂ :=
    ∑ χ : DirichletCharacter ℂ (r * q), charCoeff r q a b χ * smoothedTiltedRemainder χ Y (β / (r : ℝ))
  have hS_cop_eq : S_cop = twistSum + charCoeff r q a b 1 * principalSum := by
    have hpt : ∀ n ∈ Finset.Icc 1 Y,
        (if n % r = b ∧ Nat.Coprime n (r * q) then
          (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            e ((a : ℝ) * (n : ℝ) / ((r * q : ℕ) : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ))
        else 0) =
        ∑ χ : DirichletCharacter ℂ (r * q),
          charCoeff r q a b χ *
            (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod (r * q))) *
              (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * e ((β / (r : ℝ)) * (n : ℝ)) := by
      intro n _
      by_cases hcop : Nat.Coprime n (r * q)
      · have hu : IsUnit (n : ZMod (r * q)) := (ZMod.isUnit_iff_coprime n (r * q)).2 hcop
        have heval := charExpansion_eval r q a b hr hq_pos hu
        have hval_mod : ((n : ZMod (r * q)).val) % r = n % r := by
          rw [ZMod.val_natCast, Nat.mod_mul_right_mod]
        have hb_mod : b % r = b := Nat.mod_eq_of_lt hb
        have he_val : e ((a : ℝ) * ((n : ZMod (r * q)).val : ℝ) / ((r * q : ℕ) : ℝ)) =
            e ((a : ℝ) * (n : ℝ) / ((r * q : ℕ) : ℝ)) := by
          rw [ZMod.val_natCast]
          let t := n / (r * q)
          let rem := n % (r * q)
          have hdiv : r * q * t + rem = n := Nat.div_add_mod n (r * q)
          have hdivR : ((r * q : ℕ) : ℝ) * (t : ℝ) + (rem : ℝ) = (n : ℝ) := by exact_mod_cast hdiv
          apply e_eq_of_sub_int (k := -((a * t : ℕ) : ℤ))
          have hrq0 : ((r * q : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.mul_ne_zero hr.ne' hq_pos.ne')
          rw [Int.cast_neg, Int.cast_natCast, ← sub_div, div_eq_iff hrq0, Nat.cast_mul]
          change (a : ℝ) * (rem : ℝ) - (a : ℝ) * (n : ℝ) = -((a : ℝ) * (t : ℝ)) * ((r * q : ℕ) : ℝ)
          nlinarith only [hdivR]
        rw [hval_mod, hb_mod, he_val] at heval
        have h1 : (if n % r = b ∧ Nat.Coprime n (r * q) then
            (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              e ((a : ℝ) * (n : ℝ) / ((r * q : ℕ) : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ))
          else 0) =
          (if n % r = b then e ((a : ℝ) * (n : ℝ) / ((r * q : ℕ) : ℝ)) else 0) *
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * e ((β / (r : ℝ)) * (n : ℝ)) := by
          by_cases hmod : n % r = b
          · rw [ite_eq_left ⟨hmod, hcop⟩, ite_eq_left hmod]; ring
          · rw [ite_eq_right (fun h => hmod h.1), ite_eq_right hmod]; ring
        rw [h1, ← heval, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun χ _ => by ring
      · have hnu : ¬ IsUnit (n : ZMod (r * q)) := fun hu => hcop ((ZMod.isUnit_iff_coprime n (r * q)).1 hu)
        have hf : ¬ (n % r = b ∧ Nat.Coprime n (r * q)) := fun h => hcop h.2
        rw [ite_eq_right hf]
        symm
        apply Finset.sum_eq_zero
        intro χ _
        rw [MulChar.map_nonunit χ hnu]; ring
    dsimp [S_cop]
    rw [Finset.sum_filter]
    calc ∑ n ∈ Finset.Icc 1 Y,
          (if n % r = b ∧ Nat.Coprime n (r * q) then
            (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              e ((a : ℝ) * (n : ℝ) / ((r * q : ℕ) : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ))
          else 0)
        = ∑ n ∈ Finset.Icc 1 Y, ∑ χ : DirichletCharacter ℂ (r * q),
            charCoeff r q a b χ *
              (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod (r * q))) *
                (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * e ((β / (r : ℝ)) * (n : ℝ)) :=
          Finset.sum_congr rfl hpt
      _ = ∑ χ : DirichletCharacter ℂ (r * q), charCoeff r q a b χ *
            ∑ n ∈ Finset.Icc 1 Y,
              (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod (r * q))) *
                (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * e ((β / (r : ℝ)) * (n : ℝ)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun χ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => by ring
      _ = ∑ χ : DirichletCharacter ℂ (r * q), charCoeff r q a b χ *
            (smoothedTiltedRemainder χ Y (β / (r : ℝ)) +
              (if χ = 1 then (1 : ℂ) else 0) * principalSum) := by
          refine Finset.sum_congr rfl fun χ _ => ?_
          congr 1
          unfold smoothedTiltedRemainder
          dsimp [principalSum]
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun n _ => by ring
      _ = twistSum + charCoeff r q a b 1 * principalSum := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
          congr 1
          rw [Finset.sum_eq_single (1 : DirichletCharacter ℂ (r * q))]
          · simp
          · intro χ _ hχ; simp [hχ]
          · intro h; exact absurd (Finset.mem_univ _) h
  -- Step 4: Bound `‖phase * twistSum‖ ≤ 6 * C * M * log(2Y)`.
  have hstep3 : ‖phase * twistSum‖ ≤ 6 * C * M * Real.log (2 * (Y : ℝ)) := by
    rw [norm_mul, hphase_norm, one_mul]
    have htr : |β / (r : ℝ)| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos hr_pos]
      have hr1 : (1 : ℝ) ≤ r := Nat.one_le_cast.mpr hr
      calc |β| / (r : ℝ) ≤ |β| / 1 := div_le_div_of_nonneg_left (abs_nonneg β) zero_lt_one hr1
        _ = |β| := div_one _
        _ ≤ 1 / 2 := hβ_half
    have hlog_rqY : Real.log (2 * ((r * q : ℕ) : ℝ) * (Y : ℝ)) ≤ 3 * Real.log (2 * (Y : ℝ)) := by
      have hqY : q ≤ Y := hq_le_Q.trans ((Nat.sqrt_le_self (Y / r)).trans (Nat.div_le_self Y r))
      have hbound : 2 * ((r * q : ℕ) : ℝ) * (Y : ℝ) ≤ (2 * (Y : ℝ)) ^ 3 := by
        have hrY' : (r : ℝ) ≤ Y := Nat.cast_le.mpr hrY
        have hqY' : (q : ℝ) ≤ Y := Nat.cast_le.mpr hqY
        calc 2 * ((r * q : ℕ) : ℝ) * (Y : ℝ) = 2 * ((r : ℝ) * (q : ℝ)) * (Y : ℝ) := by push_cast; ring
          _ ≤ 2 * ((Y : ℝ) * (Y : ℝ)) * (Y : ℝ) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (mul_le_mul hrY' hqY' (Nat.cast_nonneg _) hY_pos.le) two_pos.le) hY_pos.le
          _ ≤ (2 * (Y : ℝ)) ^ 3 := by
              have hY3 : 0 ≤ (Y : ℝ) ^ 3 := by positivity
              have heq1 : 2 * ((Y : ℝ) * (Y : ℝ)) * (Y : ℝ) = 2 * (Y : ℝ) ^ 3 := by ring
              have heq2 : (2 * (Y : ℝ)) ^ 3 = 8 * (Y : ℝ) ^ 3 := by ring
              linarith
      calc Real.log (2 * ((r * q : ℕ) : ℝ) * (Y : ℝ)) ≤ Real.log ((2 * (Y : ℝ)) ^ 3) :=
            Real.log_le_log (by positivity) hbound
        _ = 3 * Real.log (2 * (Y : ℝ)) := by rw [Real.log_pow]; norm_num
    have hrad : Real.sqrt ((q : ℝ) / ((Nat.gcd r q : ℕ) : ℝ)) *
          Real.sqrt ((Y : ℝ) * (1 + |β / (r : ℝ)| * (Y : ℝ))) ≤ 2 * M := by
      have hgcd1 : (1 : ℝ) ≤ ((Nat.gcd r q : ℕ) : ℝ) := Nat.one_le_cast.mpr (Nat.gcd_pos_of_pos_left q hr)
      have hq_div : (q : ℝ) / ((Nat.gcd r q : ℕ) : ℝ) ≤ (q : ℝ) := div_le_self (Nat.cast_nonneg _) hgcd1
      have hprod_le : (q : ℝ) * (1 + |β / (r : ℝ)| * (Y : ℝ)) ≤ 3 * Real.sqrt ((Y : ℝ) / (r : ℝ)) := by
        have hqβ : (q : ℝ) * |β| ≤ 1 / (Q : ℝ) := by
          have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq_pos
          have hQR : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ_pos
          calc (q : ℝ) * |β| ≤ (q : ℝ) * (1 / ((q : ℝ) * (Q : ℝ))) :=
                mul_le_mul_of_nonneg_left hβ_outer hqR.le
            _ = 1 / (Q : ℝ) := by field_simp [hqR.ne', hQR.ne']
        have hQ_inv : (Y : ℝ) / ((r : ℝ) * (Q : ℝ)) ≤ 2 * Real.sqrt ((Y : ℝ) / (r : ℝ)) := by
          have hQR : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ_pos
          have hrt_pos : 0 < Real.sqrt ((Y : ℝ) / (r : ℝ)) := Real.sqrt_pos.mpr (div_pos hY_pos hr_pos)
          rw [div_le_iff₀ (mul_pos hr_pos hQR)]
          have h1 : (Y : ℝ) = (r : ℝ) * (Real.sqrt ((Y : ℝ) / (r : ℝ)) * Real.sqrt ((Y : ℝ) / (r : ℝ))) := by
            rw [Real.mul_self_sqrt (by positivity)]; field_simp [hr_pos.ne']
          have h2 : Real.sqrt ((Y : ℝ) / (r : ℝ)) ≤ 2 * (Q : ℝ) := by linarith [hQ_bounds.1]
          nlinarith
        have hq_le_rt : (q : ℝ) ≤ Real.sqrt ((Y : ℝ) / (r : ℝ)) :=
          (Nat.cast_le.mpr hq_le_Q).trans hQ_bounds.2
        have hterm2 : (q : ℝ) * (|β / (r : ℝ)| * (Y : ℝ)) ≤ (Y : ℝ) / ((r : ℝ) * (Q : ℝ)) := by
          rw [abs_div, abs_of_pos hr_pos]
          calc (q : ℝ) * (|β| / (r : ℝ) * (Y : ℝ)) = ((q : ℝ) * |β|) * ((Y : ℝ) / (r : ℝ)) := by ring
            _ ≤ (1 / (Q : ℝ)) * ((Y : ℝ) / (r : ℝ)) := mul_le_mul_of_nonneg_right hqβ (by positivity)
            _ = (Y : ℝ) / ((r : ℝ) * (Q : ℝ)) := by ring
        linarith
      rw [← Real.sqrt_mul (by positivity)]
      calc Real.sqrt ((q : ℝ) / ((Nat.gcd r q : ℕ) : ℝ) * ((Y : ℝ) * (1 + |β / (r : ℝ)| * (Y : ℝ))))
          ≤ Real.sqrt ((Y : ℝ) * ((q : ℝ) * (1 + |β / (r : ℝ)| * (Y : ℝ)))) := by
            apply Real.sqrt_le_sqrt
            have : (q : ℝ) / ((Nat.gcd r q : ℕ) : ℝ) * ((Y : ℝ) * (1 + |β / (r : ℝ)| * (Y : ℝ))) =
                (Y : ℝ) * (((q : ℝ) / ((Nat.gcd r q : ℕ) : ℝ)) * (1 + |β / (r : ℝ)| * (Y : ℝ))) := by ring
            rw [this]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hq_div (by positivity)) hY_pos.le
        _ ≤ Real.sqrt ((Y : ℝ) * (3 * Real.sqrt ((Y : ℝ) / (r : ℝ)))) :=
            Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hprod_le hY_pos.le)
        _ ≤ Real.sqrt (4 * ((Y : ℝ) * Real.sqrt ((Y : ℝ) / (r : ℝ)))) := by
            apply Real.sqrt_le_sqrt; nlinarith [Real.sqrt_nonneg ((Y : ℝ) / (r : ℝ))]
        _ = 2 * M := by
            have hsq4 : Real.sqrt 4 = 2 := by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two]
            rw [Real.sqrt_mul (by norm_num), hsq4, sqrt_mul_sqrt_div hY_pos hr_pos]
    calc ‖twistSum‖
        ≤ ∑ χ : DirichletCharacter ℂ (r * q),
            ‖charCoeff r q a b χ‖ * ‖smoothedTiltedRemainder χ Y (β / (r : ℝ))‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => (norm_mul _ _).le)
      _ ≤ ∑ χ : DirichletCharacter ℂ (r * q),
            ‖charCoeff r q a b χ‖ *
              (C * Real.sqrt ((Y : ℝ) * (1 + |β / (r : ℝ)| * (Y : ℝ))) * (3 * Real.log (2 * (Y : ℝ)))) := by
          refine Finset.sum_le_sum fun χ _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact (hTw Y (r * q) χ (β / (r : ℝ)) hY_ge2 htr).trans
            (mul_le_mul_of_nonneg_left hlog_rqY (by positivity))
      _ = (∑ χ : DirichletCharacter ℂ (r * q), ‖charCoeff r q a b χ‖) *
            (C * Real.sqrt ((Y : ℝ) * (1 + |β / (r : ℝ)| * (Y : ℝ))) * (3 * Real.log (2 * (Y : ℝ)))) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ Real.sqrt ((q : ℝ) / ((Nat.gcd r q : ℕ) : ℝ)) *
            (C * Real.sqrt ((Y : ℝ) * (1 + |β / (r : ℝ)| * (Y : ℝ))) * (3 * Real.log (2 * (Y : ℝ)))) :=
          mul_le_mul_of_nonneg_right (charCoeff_l1_le r q a b hr hq_pos hbr) (by positivity)
      _ = 3 * C * (Real.sqrt ((q : ℝ) / ((Nat.gcd r q : ℕ) : ℝ)) *
            Real.sqrt ((Y : ℝ) * (1 + |β / (r : ℝ)| * (Y : ℝ)))) * Real.log (2 * (Y : ℝ)) := by ring
      _ ≤ 3 * C * (2 * M) * Real.log (2 * (Y : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrad (by positivity)) (by linarith)
      _ = 6 * C * M * Real.log (2 * (Y : ℝ)) := by ring
  -- Step 5: Compare `phase * charCoeff r q a b 1 * principalSum` with `modelSum r b Y Q Q₀ α`.
  have hstep4 : ‖phase * (charCoeff r q a b 1 * principalSum) - modelSum r b Y Q Q₀ α‖ ≤
      ((2 : ℝ) ^ 143) ^ 2 * M := by
    by_cases hcop_qr : Nat.Coprime q r
    · -- First compare `phase * charCoeff 1 * principalSum` with `modelCoeff r b c * smoothedKernel r b Y β`.
      have hcc := charCoeff_one_coprime hr hq_pos hb ha_cop hbr hcop_qr
      have hrew : phase * (charCoeff r q a b 1 * principalSum) -
            modelCoeff r b c * smoothedKernel r b Y β =
          (e (-((a : ℝ) * (rInv r q : ℝ) * (b : ℝ) / (q : ℝ))) *
            (ArithmeticFunction.moebius q : ℂ) / ((r.totient : ℂ) * (q.totient : ℂ))) *
          (e (-((β * (b : ℝ)) / (r : ℝ))) * principalSum - (r : ℂ) * smoothedKernel r b Y β) := by
        have hmc : modelCoeff r b c =
            e (-((a : ℝ) * (rInv r q : ℝ) * (b : ℝ) / (q : ℝ))) *
              (((r : ℝ) / (r.totient : ℝ) : ℝ) : ℂ) *
              ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) := by
          unfold modelCoeff; exact ite_eq_left hcop_qr
        rw [hmc]
        have hph : phase * (charCoeff r q a b 1 * principalSum) =
            (e (-((a : ℝ) * (b : ℝ) / ((r * q : ℕ) : ℝ))) * charCoeff r q a b 1) *
              (e (-((β * (b : ℝ)) / (r : ℝ))) * principalSum) := by dsimp [phase]; ring
        rw [hph, hcc]
        have hr0 : (r.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hr).ne'
        have hq0 : (q.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hq_pos).ne'
        push_cast; field_simp [hr0, hq0]
      have hblock_err : ‖phase * (charCoeff r q a b 1 * principalSum) -
            modelCoeff r b c * smoothedKernel r b Y β‖ ≤ (2 : ℝ) ^ 22 * M := by
        rw [hrew, norm_mul]
        have hmu1 : ‖(ArithmeticFunction.moebius q : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_intCast]
          by_cases hsf : Squarefree q
          · rw [ArithmeticFunction.moebius_apply_of_squarefree hsf]
            simp
          · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
            simp
        have hcoeff_norm : ‖e (-((a : ℝ) * (rInv r q : ℝ) * (b : ℝ) / (q : ℝ))) *
            (ArithmeticFunction.moebius q : ℂ) / ((r.totient : ℂ) * (q.totient : ℂ))‖ ≤
            1 / ((r.totient : ℝ) * (q.totient : ℝ)) := by
          rw [norm_div, norm_mul, norm_e, one_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
          exact div_le_div_of_nonneg_right hmu1 (by positivity)
        have happrox := principalSum_approx_smoothedKernel hr hb hrY β
        have htot_r : (r : ℝ) / (r.totient : ℝ) ≤ (2 : ℝ) ^ 16 * (r : ℝ) ^ ((1 : ℝ) / 4) :=
          div_totient_le_rpow_quarter r hr
        have hqtot1 : (1 : ℝ) ≤ q.totient := Nat.one_le_cast.mpr (Nat.totient_pos.mpr hq_pos)
        have hpart1 : (16 * (r : ℝ)) / ((r.totient : ℝ) * (q.totient : ℝ)) ≤ (2 : ℝ) ^ 20 * M := by
          have hr14 : (r : ℝ) ^ ((1 : ℝ) / 4) ≤ M := by
            have h1 : (r : ℝ) ^ ((1 : ℝ) / 4) ≤ Real.sqrt (Y : ℝ) := by
              rw [Real.sqrt_eq_rpow]
              calc (r : ℝ) ^ ((1 : ℝ) / 4) ≤ (Y : ℝ) ^ ((1 : ℝ) / 4) :=
                    Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hrY) (by norm_num)
                _ ≤ (Y : ℝ) ^ ((1 : ℝ) / 2) :=
                    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ Y)) (by norm_num)
            exact h1.trans hsqrtY_le_M
          have h1 : (16 * (r : ℝ)) / ((r.totient : ℝ) * (q.totient : ℝ)) ≤ 16 * ((r : ℝ) / (r.totient : ℝ)) := by
            rw [div_mul_eq_div_div, mul_div_assoc]
            exact div_le_self (by positivity) hqtot1
          calc (16 * (r : ℝ)) / ((r.totient : ℝ) * (q.totient : ℝ))
              ≤ 16 * ((2 : ℝ) ^ 16 * (r : ℝ) ^ ((1 : ℝ) / 4)) := h1.trans (mul_le_mul_of_nonneg_left htot_r (by norm_num))
            _ = (2 : ℝ) ^ 20 * (r : ℝ) ^ ((1 : ℝ) / 4) := by norm_num; ring
            _ ≤ (2 : ℝ) ^ 20 * M := mul_le_mul_of_nonneg_left hr14 (by positivity)
        have hpart2 : (16 * (Y : ℝ) * |β|) / ((r.totient : ℝ) * (q.totient : ℝ)) ≤ (2 : ℝ) ^ 21 * M := by
          have hQ_inv : (Y : ℝ) / ((r : ℝ) * (Q : ℝ)) ≤ 2 * Real.sqrt ((Y : ℝ) / (r : ℝ)) := by
            have hQR : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ_pos
            rw [div_le_iff₀ (mul_pos hr_pos hQR)]
            have h1 : (Y : ℝ) = (r : ℝ) * (Real.sqrt ((Y : ℝ) / (r : ℝ)) * Real.sqrt ((Y : ℝ) / (r : ℝ))) := by
              rw [Real.mul_self_sqrt (by positivity)]; field_simp [hr_pos.ne']
            have h2 : Real.sqrt ((Y : ℝ) / (r : ℝ)) ≤ 2 * (Q : ℝ) := by linarith only [hQ_bounds.1]
            calc (Y : ℝ) = (r : ℝ) * Real.sqrt ((Y : ℝ) / (r : ℝ)) * Real.sqrt ((Y : ℝ) / (r : ℝ)) := by linarith only [h1]
              _ ≤ (r : ℝ) * Real.sqrt ((Y : ℝ) / (r : ℝ)) * (2 * (Q : ℝ)) :=
                  mul_le_mul_of_nonneg_left h2 (by positivity)
              _ = 2 * Real.sqrt ((Y : ℝ) / (r : ℝ)) * ((r : ℝ) * (Q : ℝ)) := by ring
          have hβ1 : |β| ≤ 1 / (Q : ℝ) := hβ_outer.trans (one_div_le_one_div_of_le (Nat.cast_pos.mpr hQ_pos) (by
            have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr hq_pos
            have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
            nlinarith only [hq1, hQ0]))
          have hrt_r14 : Real.sqrt ((Y : ℝ) / (r : ℝ)) * (r : ℝ) ^ ((1 : ℝ) / 4) ≤ M := by
            have heq : Real.sqrt ((Y : ℝ) / (r : ℝ)) * (r : ℝ) ^ ((1 : ℝ) / 4) =
                (Y : ℝ) ^ ((1 : ℝ) / 2) * (r : ℝ) ^ (-(1 : ℝ) / 4) := by
              rw [Real.sqrt_eq_rpow, Real.div_rpow hY_pos.le hr_pos.le, div_eq_mul_inv,
                  ← Real.rpow_neg hr_pos.le, mul_assoc, ← Real.rpow_add hr_pos]
              norm_num
            rw [heq]
            exact mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ Y)) (by norm_num))
              (by positivity)
          have h1 : (16 * (Y : ℝ) * |β|) / ((r.totient : ℝ) * (q.totient : ℝ)) ≤
              16 * ((Y : ℝ) / ((r : ℝ) * (Q : ℝ))) * ((r : ℝ) / (r.totient : ℝ)) := by
            have hrt_pos : (0 : ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
            have h2 : (16 * (Y : ℝ) * |β|) / ((r.totient : ℝ) * (q.totient : ℝ)) ≤
                (16 * (Y : ℝ) * (1 / (Q : ℝ))) / (r.totient : ℝ) := by
              calc (16 * (Y : ℝ) * |β|) / ((r.totient : ℝ) * (q.totient : ℝ))
                  = ((16 * (Y : ℝ) * |β|) / (r.totient : ℝ)) / (q.totient : ℝ) := by rw [div_mul_eq_div_div]
                _ ≤ (16 * (Y : ℝ) * |β|) / (r.totient : ℝ) := div_le_self (by positivity) hqtot1
                _ ≤ (16 * (Y : ℝ) * (1 / (Q : ℝ))) / (r.totient : ℝ) :=
                    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hβ1 (by positivity)) hrt_pos.le
            have h3 : (16 * (Y : ℝ) * (1 / (Q : ℝ))) / (r.totient : ℝ) =
                16 * ((Y : ℝ) / ((r : ℝ) * (Q : ℝ))) * ((r : ℝ) / (r.totient : ℝ)) := by
              field_simp [hr_pos.ne', hrt_pos.ne', (Nat.cast_pos.mpr hQ_pos).ne']
            exact h2.trans h3.le
          calc (16 * (Y : ℝ) * |β|) / ((r.totient : ℝ) * (q.totient : ℝ))
              ≤ 16 * (2 * Real.sqrt ((Y : ℝ) / (r : ℝ))) * ((2 : ℝ) ^ 16 * (r : ℝ) ^ ((1 : ℝ) / 4)) :=
                h1.trans (mul_le_mul (mul_le_mul_of_nonneg_left hQ_inv (by norm_num)) htot_r (by positivity) (by positivity))
            _ = 32 * (2 : ℝ) ^ 16 * (Real.sqrt ((Y : ℝ) / (r : ℝ)) * (r : ℝ) ^ ((1 : ℝ) / 4)) := by ring
            _ ≤ (2 : ℝ) ^ 21 * M := by
                have h32 : 32 * (2 : ℝ) ^ 16 ≤ (2 : ℝ) ^ 21 := by norm_num
                exact mul_le_mul h32 hrt_r14 (by positivity) (by positivity)
        calc ‖e (-((a : ℝ) * (rInv r q : ℝ) * (b : ℝ) / (q : ℝ))) *
              (ArithmeticFunction.moebius q : ℂ) / ((r.totient : ℂ) * (q.totient : ℂ))‖ *
            ‖e (-((β * (b : ℝ)) / (r : ℝ))) * principalSum - (r : ℂ) * smoothedKernel r b Y β‖
            ≤ (1 / ((r.totient : ℝ) * (q.totient : ℝ))) * (16 * (r : ℝ) + 16 * (Y : ℝ) * |β|) :=
              mul_le_mul hcoeff_norm happrox (norm_nonneg _) (by positivity)
          _ = (16 * (r : ℝ)) / ((r.totient : ℝ) * (q.totient : ℝ)) +
              (16 * (Y : ℝ) * |β|) / ((r.totient : ℝ) * (q.totient : ℝ)) := by ring
          _ ≤ (2 : ℝ) ^ 20 * M + (2 : ℝ) ^ 21 * M := add_le_add hpart1 hpart2
          _ ≤ (2 : ℝ) ^ 22 * M := by nlinarith only [hM_pos]
      by_cases hq_le : q ≤ Q₀
      · rw [modelSum_eq_on_cell_le hα_cell hq_le]
        have hc22 : (2 : ℝ) ^ 22 ≤ ((2 : ℝ) ^ 143) ^ 2 := by
          have h1 : (2 : ℝ) ^ 22 ≤ (2 : ℝ) ^ 143 := pow_le_pow_right₀ (by norm_num) (by norm_num)
          have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ 143 := one_le_pow₀ (by norm_num)
          nlinarith only [h1, h2]
        exact hblock_err.trans (mul_le_mul_of_nonneg_right hc22 hM_pos.le)
      · have hq_gt : Q₀ < q := not_le.mp hq_le
        rw [modelSum_eq_zero_on_cell_gt hα_cell hq_gt, sub_zero]
        -- Bound `‖modelCoeff r b c * smoothedKernel r b Y β‖` for `Q₀ < q ≤ Q`.
        have hdisc : ‖modelCoeff r b c * smoothedKernel r b Y β‖ ≤ ((2 : ℝ) ^ 142) ^ 2 * M := by
          have hmc_norm : ‖modelCoeff r b c‖ ≤ ((r : ℝ) / (r.totient : ℝ)) * (1 / (q.totient : ℝ)) := by
            unfold modelCoeff
            rw [ite_eq_left hcop_qr, norm_mul, norm_mul, norm_e, one_mul, norm_div,
                Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), Complex.norm_natCast]
            have hmu1 : ‖(ArithmeticFunction.moebius q : ℂ)‖ ≤ 1 := by
              rw [Complex.norm_intCast]
              by_cases hsf : Squarefree q
              · rw [ArithmeticFunction.moebius_apply_of_squarefree hsf]; simp
              · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; simp
            exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hmu1 (by positivity)) (by positivity)
          have hV_le : ‖smoothedKernel r b Y β‖ ≤ 2 * ((Y : ℝ) / (r : ℝ)) := by
            have h1 : (1 : ℝ) ≤ (Y : ℝ) / (r : ℝ) := (one_le_div hr_pos).2 (Nat.cast_le.mpr hrY)
            linarith [smoothedKernel_bound_triv r b Y β]
          have hq_ge_rt : (1 / (2 : ℝ) ^ 26) * Real.sqrt ((Y : ℝ) / (r : ℝ)) ≤ (q : ℝ) := by
            have h1 : Q ≤ 2 ^ 24 * (Q₀ + 1) := by
              have := Nat.div_add_mod Q (2 ^ 24)
              have := Nat.mod_lt Q (by norm_num : 0 < 2 ^ 24)
              dsimp [Q₀]; omega
            have h2 : Q₀ + 1 ≤ q := hq_gt
            have h3 : (Q : ℝ) ≤ (2 : ℝ) ^ 24 * (q : ℝ) := by
              have : Q ≤ 2 ^ 24 * q := h1.trans (Nat.mul_le_mul_left _ h2)
              exact_mod_cast this
            linarith [hQ_bounds.1]
          have hYq : 2 * ((Y : ℝ) / ((r : ℝ) * (q : ℝ))) ≤ (2 : ℝ) ^ 27 * Real.sqrt ((Y : ℝ) / (r : ℝ)) := by
            have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq_pos
            rw [mul_div_assoc', div_le_iff₀ (mul_pos hr_pos hqR)]
            have h1 : (Y : ℝ) = (r : ℝ) * (Real.sqrt ((Y : ℝ) / (r : ℝ)) * Real.sqrt ((Y : ℝ) / (r : ℝ))) := by
              rw [Real.mul_self_sqrt (by positivity)]; field_simp [hr_pos.ne']
            have hq26 : Real.sqrt ((Y : ℝ) / (r : ℝ)) ≤ (2 : ℝ) ^ 26 * (q : ℝ) := by linarith only [hq_ge_rt]
            calc 2 * (Y : ℝ) = 2 * (r : ℝ) * Real.sqrt ((Y : ℝ) / (r : ℝ)) * Real.sqrt ((Y : ℝ) / (r : ℝ)) := by linarith only [h1]
              _ ≤ 2 * (r : ℝ) * Real.sqrt ((Y : ℝ) / (r : ℝ)) * ((2 : ℝ) ^ 26 * (q : ℝ)) :=
                  mul_le_mul_of_nonneg_left hq26 (by positivity)
              _ = (2 : ℝ) ^ 27 * Real.sqrt ((Y : ℝ) / (r : ℝ)) * ((r : ℝ) * (q : ℝ)) := by ring
          have htot_r := div_totient_le_rpow_eighth r hr
          have htot_q := div_totient_le_rpow_eighth q hq_pos
          have hqY : (q : ℝ) ≤ Y := Nat.cast_le.mpr (hq_le_Q.trans ((Nat.sqrt_le_self (Y / r)).trans (Nat.div_le_self Y r)))
          have hpow_le : Real.sqrt ((Y : ℝ) / (r : ℝ)) * (r : ℝ) ^ ((1 : ℝ) / 8) * (q : ℝ) ^ ((1 : ℝ) / 8) ≤ M := by
            have hq18 : (q : ℝ) ^ ((1 : ℝ) / 8) ≤ (Y : ℝ) ^ ((1 : ℝ) / 8) :=
              Real.rpow_le_rpow (Nat.cast_nonneg _) hqY (by norm_num)
            have h1 : Real.sqrt ((Y : ℝ) / (r : ℝ)) * (r : ℝ) ^ ((1 : ℝ) / 8) * (Y : ℝ) ^ ((1 : ℝ) / 8) =
                (Y : ℝ) ^ ((5 : ℝ) / 8) * (r : ℝ) ^ (-(3 : ℝ) / 8) := by
              rw [Real.sqrt_eq_rpow, Real.div_rpow hY_pos.le hr_pos.le, div_eq_mul_inv,
                  ← Real.rpow_neg hr_pos.le]
              calc (Y : ℝ) ^ ((1 : ℝ) / 2) * (r : ℝ) ^ (-((1 : ℝ) / 2)) * (r : ℝ) ^ ((1 : ℝ) / 8) * (Y : ℝ) ^ ((1 : ℝ) / 8)
                  = ((Y : ℝ) ^ ((1 : ℝ) / 2) * (Y : ℝ) ^ ((1 : ℝ) / 8)) *
                      ((r : ℝ) ^ (-((1 : ℝ) / 2)) * (r : ℝ) ^ ((1 : ℝ) / 8)) := by ring
                _ = (Y : ℝ) ^ ((5 : ℝ) / 8) * (r : ℝ) ^ (-(3 : ℝ) / 8) := by
                    rw [← Real.rpow_add hY_pos, ← Real.rpow_add hr_pos]; norm_num
            have hY58 : (Y : ℝ) ^ ((5 : ℝ) / 8) ≤ (Y : ℝ) ^ ((3 : ℝ) / 4) :=
              Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ Y)) (by norm_num)
            have hr38 : (r : ℝ) ^ (-(3 : ℝ) / 8) ≤ (r : ℝ) ^ (-(1 : ℝ) / 4) :=
              Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hr) (by norm_num)
            calc Real.sqrt ((Y : ℝ) / (r : ℝ)) * (r : ℝ) ^ ((1 : ℝ) / 8) * (q : ℝ) ^ ((1 : ℝ) / 8)
                ≤ Real.sqrt ((Y : ℝ) / (r : ℝ)) * (r : ℝ) ^ ((1 : ℝ) / 8) * (Y : ℝ) ^ ((1 : ℝ) / 8) :=
                  mul_le_mul_of_nonneg_left hq18 (by positivity)
              _ = (Y : ℝ) ^ ((5 : ℝ) / 8) * (r : ℝ) ^ (-(3 : ℝ) / 8) := h1
              _ ≤ M := mul_le_mul hY58 hr38 (by positivity) (by positivity)
          have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq_pos.ne'
          calc ‖modelCoeff r b c * smoothedKernel r b Y β‖
              = ‖modelCoeff r b c‖ * ‖smoothedKernel r b Y β‖ := norm_mul _ _
            _ ≤ (((r : ℝ) / (r.totient : ℝ)) * (1 / (q.totient : ℝ))) * (2 * ((Y : ℝ) / (r : ℝ))) :=
                mul_le_mul hmc_norm hV_le (norm_nonneg _) (by positivity)
            _ = (2 * ((Y : ℝ) / ((r : ℝ) * (q : ℝ)))) * ((r : ℝ) / (r.totient : ℝ)) * ((q : ℝ) / (q.totient : ℝ)) := by
                field_simp [hqR, hr_pos.ne', (Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)).ne',
                  (Nat.cast_pos.mpr (Nat.totient_pos.mpr hq_pos)).ne']
            _ ≤ ((2 : ℝ) ^ 27 * Real.sqrt ((Y : ℝ) / (r : ℝ))) *
                (((2 : ℝ) ^ 64) ^ 2 * (r : ℝ) ^ ((1 : ℝ) / 8)) *
                (((2 : ℝ) ^ 64) ^ 2 * (q : ℝ) ^ ((1 : ℝ) / 8)) := by
                refine mul_le_mul (mul_le_mul hYq htot_r (by positivity) (by positivity)) htot_q (by positivity) (by positivity)
            _ = (2 : ℝ) ^ 27 * (((2 : ℝ) ^ 64) ^ 2 * ((2 : ℝ) ^ 64) ^ 2) *
                (Real.sqrt ((Y : ℝ) / (r : ℝ)) * (r : ℝ) ^ ((1 : ℝ) / 8) * (q : ℝ) ^ ((1 : ℝ) / 8)) := by ring
            _ ≤ ((2 : ℝ) ^ 142) ^ 2 * M := by
                have hconst : (2 : ℝ) ^ 27 * (((2 : ℝ) ^ 64) ^ 2 * ((2 : ℝ) ^ 64) ^ 2) ≤ ((2 : ℝ) ^ 142) ^ 2 := by
                  have h1 : (2 : ℝ) ^ 27 * (((2 : ℝ) ^ 64) ^ 2 * ((2 : ℝ) ^ 64) ^ 2) =
                      (2 : ℝ) ^ 27 * ((2 : ℝ) ^ 128) ^ 2 := by ring
                  have h2 : ((2 : ℝ) ^ 142) ^ 2 = (2 : ℝ) ^ 28 * ((2 : ℝ) ^ 128) ^ 2 := by ring
                  rw [h1, h2]
                  exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
                exact mul_le_mul hconst hpow_le (by positivity) (by positivity)
        have htri : ‖phase * (charCoeff r q a b 1 * principalSum)‖ ≤
            ‖phase * (charCoeff r q a b 1 * principalSum) - modelCoeff r b c * smoothedKernel r b Y β‖ +
              ‖modelCoeff r b c * smoothedKernel r b Y β‖ := by
          have heq : phase * (charCoeff r q a b 1 * principalSum) =
              (phase * (charCoeff r q a b 1 * principalSum) - modelCoeff r b c * smoothedKernel r b Y β) +
                modelCoeff r b c * smoothedKernel r b Y β := (sub_add_cancel _ _).symm
          conv_lhs => rw [heq]
          exact norm_add_le _ _
        calc ‖phase * (charCoeff r q a b 1 * principalSum)‖
            ≤ (2 : ℝ) ^ 22 * M + ((2 : ℝ) ^ 142) ^ 2 * M := htri.trans (add_le_add hblock_err hdisc)
          _ ≤ ((2 : ℝ) ^ 143) ^ 2 * M := by
              have hpow : ((2 : ℝ) ^ 143) ^ 2 = 4 * ((2 : ℝ) ^ 142) ^ 2 := by ring
              have hle : (2 : ℝ) ^ 22 ≤ ((2 : ℝ) ^ 142) ^ 2 := by
                have h1 : (2 : ℝ) ^ 22 ≤ (2 : ℝ) ^ 142 := pow_le_pow_right₀ (by norm_num) (by norm_num)
                have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ 142 := one_le_pow₀ (by norm_num)
                nlinarith only [h1, h2]
              have hnn : 0 ≤ ((2 : ℝ) ^ 142) ^ 2 := sq_nonneg _
              have hcoef : (2 : ℝ) ^ 22 + ((2 : ℝ) ^ 142) ^ 2 ≤ ((2 : ℝ) ^ 143) ^ 2 := by linarith only [hpow, hle, hnn]
              have hlin := mul_le_mul_of_nonneg_right hcoef hM_pos.le
              linarith only [hlin]
    · -- `¬ Nat.Coprime q r`: BOTH `charCoeff r q a b 1` AND `modelCoeff r b c` vanish!
      have hg : 1 < Nat.gcd r q := by
        have hpos := Nat.gcd_pos_of_pos_left q hr
        have hne : Nat.gcd r q ≠ 1 := fun h => hcop_qr (by rwa [Nat.Coprime, Nat.gcd_comm])
        omega
      have hcc0 : charCoeff r q a b 1 = 0 :=
        charCoeff_one_eq_zero_of_one_lt_gcd r q a b hr hq_pos ha_cop hbr hg
      have hmod0 : modelSum r b Y Q Q₀ α = 0 := by
        by_cases hq_le : q ≤ Q₀
        · rw [modelSum_eq_on_cell_le hα_cell hq_le]
          unfold modelCoeff
          rw [ite_eq_right hcop_qr, zero_mul]
        · exact modelSum_eq_zero_on_cell_gt hα_cell (not_le.mp hq_le)
      rw [hcc0, zero_mul, mul_zero, hmod0, sub_zero, norm_zero]
      positivity
  -- Combine Steps 1–5!
  have hlogY : Real.log (Y : ℝ) ≤ Real.log (2 * (Y : ℝ)) := Real.log_le_log hY_pos (by linarith)
  have hcomb : smoothedPrimeSum r b Y α - modelSum r b Y Q Q₀ α =
      (smoothedPrimeSum r b Y α - phase * S_vm) +
      (phase * S_vm - phase * S_cop) +
      (phase * twistSum) +
      (phase * (charCoeff r q a b 1 * principalSum) - modelSum r b Y Q Q₀ α) := by
    rw [hS_cop_eq]; ring
  rw [hcomb]
  have h1 : ‖smoothedPrimeSum r b Y α - phase * S_vm‖ ≤ M * Real.log (2 * (Y : ℝ)) := by
    calc ‖smoothedPrimeSum r b Y α - phase * S_vm‖
        ≤ Real.sqrt (Y : ℝ) * Real.log (Y : ℝ) := hstep1
      _ ≤ M * Real.log (2 * (Y : ℝ)) :=
          mul_le_mul hsqrtY_le_M hlogY (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Y))) hM_pos.le
  have h2 : ‖phase * S_vm - phase * S_cop‖ ≤ 16 * M * Real.log (2 * (Y : ℝ)) := by
    have hlog_sq := log_two_mul_le_four_sqrt (by omega : 1 ≤ Y)
    calc ‖phase * S_vm - phase * S_cop‖
        ≤ 4 * Real.log (2 * (Y : ℝ)) * Real.log (2 * (Y : ℝ)) := hstep2
      _ ≤ 4 * (4 * Real.sqrt (Y : ℝ)) * Real.log (2 * (Y : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog_sq (by norm_num)) (by linarith)
      _ = 16 * Real.sqrt (Y : ℝ) * Real.log (2 * (Y : ℝ)) := by ring
      _ ≤ 16 * M * Real.log (2 * (Y : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrtY_le_M (by norm_num)) (by linarith)
  have h4 : ‖phase * (charCoeff r q a b 1 * principalSum) - modelSum r b Y Q Q₀ α‖ ≤
      ((2 : ℝ) ^ 143) ^ 2 * M * Real.log (2 * (Y : ℝ)) :=
    hstep4.trans (le_mul_of_one_le_right (by positivity) hlog1)
  have htri : ‖smoothedPrimeSum r b Y α - phase * S_vm + (phase * S_vm - phase * S_cop) +
      phase * twistSum + (phase * (charCoeff r q a b 1 * principalSum) - modelSum r b Y Q Q₀ α)‖ ≤
      ‖smoothedPrimeSum r b Y α - phase * S_vm‖ + ‖phase * S_vm - phase * S_cop‖ +
      ‖phase * twistSum‖ + ‖phase * (charCoeff r q a b 1 * principalSum) - modelSum r b Y Q Q₀ α‖ :=
    (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
  have hconst_sum : 1 + 16 + ((2 : ℝ) ^ 143) ^ 2 ≤ ((2 : ℝ) ^ 144) ^ 2 := by
    have hpow : ((2 : ℝ) ^ 144) ^ 2 = 4 * ((2 : ℝ) ^ 143) ^ 2 := by ring
    have hge1 : (17 : ℝ) ≤ ((2 : ℝ) ^ 143) ^ 2 := by
      have h1 : (2 : ℝ) ^ 5 ≤ (2 : ℝ) ^ 143 := pow_le_pow_right₀ (by norm_num) (by norm_num)
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ 143 := one_le_pow₀ (by norm_num)
      nlinarith only [h1, h2]
    linarith only [hpow, hge1]
  have htot_le : ‖smoothedPrimeSum r b Y α - phase * S_vm‖ + ‖phase * S_vm - phase * S_cop‖ +
      ‖phase * twistSum‖ + ‖phase * (charCoeff r q a b 1 * principalSum) - modelSum r b Y Q Q₀ α‖ ≤
      (6 * C + ((2 : ℝ) ^ 144) ^ 2) * M * Real.log (2 * (Y : ℝ)) := by
    have hlin : (1 + 16 + ((2 : ℝ) ^ 143) ^ 2) * (M * Real.log (2 * (Y : ℝ))) ≤
        ((2 : ℝ) ^ 144) ^ 2 * (M * Real.log (2 * (Y : ℝ))) :=
      mul_le_mul_of_nonneg_right hconst_sum (by positivity)
    linarith [h1, h2, hstep3, h4, hlin]
  exact (htri.trans htot_le).trans_eq (by dsimp [M]; ring)

end RemainderSup

section ModelL2AndConv

/-- Helper: `1`-periodic shift of an integral on `[0, 1]` to `[-1/2, 1/2]` around `c`. -/
lemma intervalIntegral_shift_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (hper : Function.Periodic g 1) (c : ℝ) :
    (∫ α in (0 : ℝ)..1, g α) = ∫ β in (-(1 / 2) : ℝ)..(1 / 2), g (c + β) := by
  have h1 := hper.intervalIntegral_add_eq (c - 1 / 2) 0
  have h2 : (0 : ℝ) + 1 = 1 := by norm_num
  have h3 : c - 1 / 2 + 1 = c + 1 / 2 := by ring
  rw [h2, h3] at h1
  rw [← h1]
  have hcomp := intervalIntegral.integral_comp_add_left g c (a := -(1 / 2 : ℝ)) (b := 1 / 2)
  have ha : c + -(1 / 2 : ℝ) = c - 1 / 2 := by ring
  rw [ha] at hcomp
  exact hcomp.symm

/-- Helper: sum of disjoint indicators squared norm equals sum of squared norms. -/
lemma norm_sq_sum_disjoint_indicator {ι : Type*} (S : Finset ι) (A : ι → Set ℝ)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (A i) (A j))
    (f : ι → ℝ → ℂ) (x : ℝ) :
    ‖∑ i ∈ S, (A i).indicator (f i) x‖ ^ 2 = ∑ i ∈ S, (A i).indicator (fun y => ‖f i y‖ ^ 2) x := by
  by_cases hex : ∃ i ∈ S, x ∈ A i
  · obtain ⟨i₀, hi₀, hx⟩ := hex
    rw [Finset.sum_eq_single i₀, Finset.sum_eq_single i₀]
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · intro j hj hne
      have hnot : x ∉ A j := Set.disjoint_left.mp (hdisj i₀ hi₀ j hj hne.symm) hx
      exact Set.indicator_of_notMem hnot _
    · intro h; exact absurd hi₀ h
    · intro j hj hne
      have hnot : x ∉ A j := Set.disjoint_left.mp (hdisj i₀ hi₀ j hj hne.symm) hx
      exact Set.indicator_of_notMem hnot _
    · intro h; exact absurd hi₀ h
  · push Not at hex
    have h1 : ∑ i ∈ S, (A i).indicator (f i) x = 0 :=
      Finset.sum_eq_zero fun i hi => Set.indicator_of_notMem (hex i hi) _
    have h2 : ∑ i ∈ S, (A i).indicator (fun y => ‖f i y‖ ^ 2) x = 0 :=
      Finset.sum_eq_zero fun i hi => Set.indicator_of_notMem (hex i hi) _
    rw [h1, h2, norm_zero, zero_pow two_ne_zero]

/-- **Module B3b (Model L² bound):**
For `1 ≤ r ≤ Y`, `Q₀ ≤ Y`, and `2^72 ≤ Y`:
`∫ α in 0..1, ‖modelSum r b Y Q Q₀ α‖² ≤ 36 * (r / φ(r)) * (Y / r) * log(2Y)`. -/
theorem modelSum_l2_le {r b Y Q Q₀ : ℕ} (hr : 0 < r) (hrY : r ≤ Y) (hQ0Y : Q₀ ≤ Y)
    (hY_large : 2 ^ 72 ≤ Y) :
    (∫ α in (0 : ℝ)..1, ‖modelSum r b Y Q Q₀ α‖ ^ 2) ≤
      36 * ((r : ℝ) / (r.totient : ℝ)) * ((Y : ℝ) / (r : ℝ)) * Real.log (2 * (Y : ℝ)) := by
  classical
  let Cset := (centers Q).filter (fun c => c.q ≤ Q₀)
  have hpt : ∀ α : ℝ, ‖modelSum r b Y Q Q₀ α‖ ^ 2 =
      ∑ c ∈ Cset, (voronoiCell Q c).indicator
        (fun x => ‖modelCoeff r b c * smoothedKernel r b Y (wrap (x - c.val))‖ ^ 2) α := by
    intro α
    unfold modelSum
    exact norm_sq_sum_disjoint_indicator Cset (voronoiCell Q)
      (fun c₁ _ c₂ _ hne => voronoiCell_disjoint hne)
      (fun c x => modelCoeff r b c * smoothedKernel r b Y (wrap (x - c.val))) α
  simp_rw [hpt]
  have hint_c : ∀ c ∈ Cset,
      IntervalIntegrable
        ((voronoiCell Q c).indicator (fun x => ‖modelCoeff r b c * smoothedKernel r b Y (wrap (x - c.val))‖ ^ 2))
        MeasureTheory.volume 0 1 := by
    intro c _
    have hmeas : Measurable ((voronoiCell Q c).indicator
        (fun x => ‖modelCoeff r b c * smoothedKernel r b Y (wrap (x - c.val))‖ ^ 2)) := by
      refine Measurable.indicator ?_ (voronoiCell_measurable Q c)
      exact ((continuous_norm.measurable.comp
        (measurable_const.mul ((continuous_smoothedKernel r b Y).measurable.comp
          (measurable_wrap.comp (measurable_id.sub measurable_const))))).pow_const 2)
    refine intervalIntegrable_of_measurable_bounded (B := (‖modelCoeff r b c‖ * ((Y : ℝ) / (r : ℝ) + 1)) ^ 2) hmeas ?_
    intro x
    rw [Real.norm_eq_abs]
    by_cases hx : x ∈ voronoiCell Q c
    · rw [Set.indicator_of_mem hx, abs_of_nonneg (sq_nonneg _), norm_mul]
      exact pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_left (smoothedKernel_bound_triv r b Y _) (norm_nonneg _)) 2
    · rw [Set.indicator_of_notMem hx, abs_zero]; positivity
  rw [intervalIntegral_finset_sum hint_c]
  have hterm_le : ∀ c ∈ Cset,
      (∫ α in (0 : ℝ)..1,
        (voronoiCell Q c).indicator
          (fun x => ‖modelCoeff r b c * smoothedKernel r b Y (wrap (x - c.val))‖ ^ 2) α) ≤
        ‖modelCoeff r b c‖ ^ 2 * ((Y : ℝ) / (r : ℝ) + 1) := by
    intro c _
    have hper : Function.Periodic ((voronoiCell Q c).indicator
        (fun x => ‖modelCoeff r b c * smoothedKernel r b Y (wrap (x - c.val))‖ ^ 2)) 1 := by
      intro x
      by_cases hx : x ∈ voronoiCell Q c
      · rw [Set.indicator_of_mem ((voronoiCell_periodic Q c x).2 hx), Set.indicator_of_mem hx]
        have : x + 1 - c.val = (x - c.val) + 1 := by ring
        rw [this, wrap_add_one]
      · rw [Set.indicator_of_notMem (fun h => hx ((voronoiCell_periodic Q c x).1 h)), Set.indicator_of_notMem hx]
    rw [intervalIntegral_shift_symm hper c.val]
    have hmono : (∫ β in (-(1 / 2) : ℝ)..(1 / 2),
          (voronoiCell Q c).indicator
            (fun x => ‖modelCoeff r b c * smoothedKernel r b Y (wrap (x - c.val))‖ ^ 2) (c.val + β)) ≤
        ∫ β in (-(1 / 2) : ℝ)..(1 / 2), ‖modelCoeff r b c‖ ^ 2 * ‖smoothedKernel r b Y β‖ ^ 2 := by
      apply intervalIntegral.integral_mono_on (by norm_num)
      · have hmeas : Measurable (fun β : ℝ => (voronoiCell Q c).indicator
            (fun x => ‖modelCoeff r b c * smoothedKernel r b Y (wrap (x - c.val))‖ ^ 2) (c.val + β)) := by
          have hm0 : Measurable ((voronoiCell Q c).indicator
              (fun x => ‖modelCoeff r b c * smoothedKernel r b Y (wrap (x - c.val))‖ ^ 2)) :=
            Measurable.indicator
              ((continuous_norm.measurable.comp
                (measurable_const.mul ((continuous_smoothedKernel r b Y).measurable.comp
                  (measurable_wrap.comp (measurable_id.sub measurable_const))))).pow_const 2)
              (voronoiCell_measurable Q c)
          exact hm0.comp (measurable_const.add measurable_id)
        refine intervalIntegrable_of_measurable_bounded (B := (‖modelCoeff r b c‖ * ((Y : ℝ) / (r : ℝ) + 1)) ^ 2) hmeas ?_
        intro β
        rw [Real.norm_eq_abs]
        by_cases hmem : c.val + β ∈ voronoiCell Q c
        · rw [Set.indicator_of_mem hmem, abs_of_nonneg (sq_nonneg _), norm_mul]
          exact pow_le_pow_left₀ (by positivity)
            (mul_le_mul_of_nonneg_left (smoothedKernel_bound_triv r b Y _) (norm_nonneg _)) 2
        · rw [Set.indicator_of_notMem hmem, abs_zero]; positivity
      · exact (continuous_const.mul ((continuous_norm.comp (continuous_smoothedKernel r b Y)).pow 2)).intervalIntegrable _ _
      · intro β _
        by_cases hmem : c.val + β ∈ voronoiCell Q c
        · rw [Set.indicator_of_mem hmem]
          have hsub : c.val + β - c.val = β := by ring
          rw [hsub, smoothedKernel_wrap, norm_mul, mul_pow]
        · rw [Set.indicator_of_notMem hmem]; positivity
    rw [intervalIntegral.integral_const_mul] at hmono
    exact hmono.trans (mul_le_mul_of_nonneg_left (smoothedKernel_l2_le r b Y) (sq_nonneg _))
  -- Group `∑_{c ∈ Cset} ‖modelCoeff r b c‖²` by denominator `q` and numerator `a`!
  have hsum_coeff : ∑ c ∈ Cset, ‖modelCoeff r b c‖ ^ 2 ≤
      ((r : ℝ) / (r.totient : ℝ)) ^ 2 *
        ∑ q ∈ ((Finset.Icc 1 Q₀).filter (fun q => Nat.Coprime q r)).filter Squarefree,
          (1 : ℝ) / (q.totient : ℝ) := by
    let Qset := ((Finset.Icc 1 Q₀).filter (fun q => Nat.Coprime q r)).filter Squarefree
    -- Every `c ∈ Cset` with `modelCoeff r b c ≠ 0` has `c.q ∈ Qset`.
    let Cgood := Cset.filter (fun c => c.q ∈ Qset)
    have htrim : ∑ c ∈ Cset, ‖modelCoeff r b c‖ ^ 2 = ∑ c ∈ Cgood, ‖modelCoeff r b c‖ ^ 2 := by
      symm; rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun c hc => ?_
      split_ifs with h
      · rfl
      · have h0 : modelCoeff r b c = 0 := by
          unfold modelCoeff
          by_cases hcop : Nat.Coprime c.q r
          · rw [ite_eq_left hcop]
            have hnot_sf : ¬ Squarefree c.q := by
              intro hsf
              exact h (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
                ⟨Finset.mem_Icc.mpr ⟨c.q_pos, (Finset.mem_filter.mp hc).2⟩, hcop⟩, hsf⟩)
            rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnot_sf]; simp
          · exact ite_eq_right hcop
        simp [h0]
    rw [htrim]
    -- Fiber over `q ∈ Qset`: at most `φ(q)` centers `c ∈ Cgood` have `c.q = q`.
    have hfiber : ∑ c ∈ Cgood, ‖modelCoeff r b c‖ ^ 2 =
        ∑ q ∈ Qset, ∑ c ∈ Cgood.filter (fun c => c.q = q), ‖modelCoeff r b c‖ ^ 2 :=
      (Finset.sum_fiberwise_of_maps_to (s := Cgood) (t := Qset) (g := fun c : RatCenter => c.q)
        (fun c hc => (Finset.mem_filter.mp hc).2) (fun c => ‖modelCoeff r b c‖ ^ 2)).symm
    rw [hfiber, Finset.mul_sum]
    refine Finset.sum_le_sum fun q hq => ?_
    have hq_pos : 0 < q := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).1
    have hq_cop : Nat.Coprime q r := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
    have hq_sf : Squarefree q := (Finset.mem_filter.mp hq).2
    have hcard_a : (Cgood.filter (fun c => c.q = q)).card ≤ q.totient := by
      have hsub : (Cgood.filter (fun c => c.q = q)).image (fun c => c.a) ⊆
          (Finset.range q).filter (fun a => Nat.Coprime a q) := by
        intro a ha
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ha
        have hcq : c.q = q := (Finset.mem_filter.mp hc).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hcq ▸ c.a_lt), hcq ▸ c.coprime⟩
      have hinj : Set.InjOn (fun c : RatCenter => c.a) (Cgood.filter (fun c => c.q = q) : Set RatCenter) := by
        intro c₁ h1 c₂ h2 hEq
        have hq1 : c₁.q = q := (Finset.mem_filter.mp h1).2
        have hq2 : c₂.q = q := (Finset.mem_filter.mp h2).2
        exact RatCenter.ext hEq (hq1.trans hq2.symm)
      rw [← Finset.card_image_of_injOn hinj]
      calc ((Cgood.filter (fun c => c.q = q)).image (fun c => c.a)).card
          ≤ ((Finset.range q).filter (fun a => Nat.Coprime a q)).card := Finset.card_le_card hsub
        _ = q.totient := by
            rw [Nat.totient_eq_card_coprime]
            congr 1; ext a; simp [Nat.coprime_comm]
    have hnorm_eq : ∀ c ∈ Cgood.filter (fun c => c.q = q),
        ‖modelCoeff r b c‖ ^ 2 = ((r : ℝ) / (r.totient : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2 := by
      intro c hc
      have hcq : c.q = q := (Finset.mem_filter.mp hc).2
      unfold modelCoeff
      rw [hcq, ite_eq_left hq_cop, norm_mul, norm_mul, norm_e, one_mul, norm_div,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
          Complex.norm_intCast, Complex.norm_natCast,
          ArithmeticFunction.moebius_apply_of_squarefree hq_sf]
      simp [mul_pow, div_pow]; ring
    calc ∑ c ∈ Cgood.filter (fun c => c.q = q), ‖modelCoeff r b c‖ ^ 2
        = ((Cgood.filter (fun c => c.q = q)).card : ℝ) *
            (((r : ℝ) / (r.totient : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2) := by
          rw [Finset.sum_congr rfl hnorm_eq, Finset.sum_const, nsmul_eq_mul]
      _ ≤ (q.totient : ℝ) * (((r : ℝ) / (r.totient : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard_a) (by positivity)
      _ = ((r : ℝ) / (r.totient : ℝ)) ^ 2 * (1 / (q.totient : ℝ)) := by
          have hqt0 : (q.totient : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hq_pos).ne'
          field_simp [hqt0]
  have hY_plus : (Y : ℝ) / (r : ℝ) + 1 ≤ 2 * ((Y : ℝ) / (r : ℝ)) := by
    have h1 : (1 : ℝ) ≤ (Y : ℝ) / (r : ℝ) := (one_le_div (Nat.cast_pos.mpr hr)).2 (Nat.cast_le.mpr hrY)
    linarith
  have hlog_nn : 0 ≤ Real.log (2 * (Y : ℝ)) := Real.log_nonneg (by
    have : 2 ≤ 2 ^ 72 := by norm_num
    have hY2 : (2 : ℝ) ≤ Y := Nat.cast_le.mpr (this.trans hY_large)
    linarith)
  calc ∑ c ∈ Cset, (∫ α in (0 : ℝ)..1,
          (voronoiCell Q c).indicator
            (fun x => ‖modelCoeff r b c * smoothedKernel r b Y (wrap (x - c.val))‖ ^ 2) α)
      ≤ ∑ c ∈ Cset, ‖modelCoeff r b c‖ ^ 2 * ((Y : ℝ) / (r : ℝ) + 1) := Finset.sum_le_sum hterm_le
    _ = (∑ c ∈ Cset, ‖modelCoeff r b c‖ ^ 2) * ((Y : ℝ) / (r : ℝ) + 1) := (Finset.sum_mul _ _ _).symm
    _ ≤ (((r : ℝ) / (r.totient : ℝ)) ^ 2 * (18 * ((r.totient : ℝ) / (r : ℝ)) * Real.log (2 * (Y : ℝ)))) *
          (2 * ((Y : ℝ) / (r : ℝ))) := by
        refine mul_le_mul ?_ hY_plus (by positivity) (by positivity)
        exact hsum_coeff.trans (mul_le_mul_of_nonneg_left (sum_coprime_inv_totient_le hr hrY hQ0Y hY_large) (by positivity))
    _ = 36 * ((r : ℝ) / (r.totient : ℝ)) * ((Y : ℝ) / (r : ℝ)) * Real.log (2 * (Y : ℝ)) := by
        have hr0 : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
        have hrt0 : (r.totient : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hr).ne'
        field_simp [hr0, hrt0]; ring

/-- Helper: product of two disjoint indicator sums is a single indicator sum of products. -/
lemma mul_sum_disjoint_indicator {ι : Type*} (S : Finset ι) (A : ι → Set ℝ)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (A i) (A j))
    (f g : ι → ℝ → ℂ) (x : ℝ) :
    (∑ i ∈ S, (A i).indicator (f i) x) * (∑ j ∈ S, (A j).indicator (g j) x) =
      ∑ i ∈ S, (A i).indicator (fun y => f i y * g i y) x := by
  by_cases hex : ∃ i ∈ S, x ∈ A i
  · obtain ⟨i₀, hi₀, hx⟩ := hex
    rw [Finset.sum_eq_single i₀, Finset.sum_eq_single i₀, Finset.sum_eq_single i₀]
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · intro j hj hne; exact Set.indicator_of_notMem (Set.disjoint_left.mp (hdisj i₀ hi₀ j hj hne.symm) hx) _
    · intro h; exact absurd hi₀ h
    · intro j hj hne; exact Set.indicator_of_notMem (Set.disjoint_left.mp (hdisj i₀ hi₀ j hj hne.symm) hx) _
    · intro h; exact absurd hi₀ h
    · intro j hj hne; exact Set.indicator_of_notMem (Set.disjoint_left.mp (hdisj i₀ hi₀ j hj hne.symm) hx) _
    · intro h; exact absurd hi₀ h
  · push Not at hex
    have h1 : ∑ i ∈ S, (A i).indicator (f i) x = 0 :=
      Finset.sum_eq_zero fun i hi => Set.indicator_of_notMem (hex i hi) _
    have h2 : ∑ i ∈ S, (A i).indicator (fun y => f i y * g i y) x = 0 :=
      Finset.sum_eq_zero fun i hi => Set.indicator_of_notMem (hex i hi) _
    rw [h1, zero_mul, h2]

/-- Exact integral of `smoothedKernel₁ * smoothedKernel₂ * e(-k * β)` on `[-1/2, 1/2]`. -/
lemma integral_smoothedKernel_mul_e {r b₁ b₂ Y k : ℕ} (hk : k ≤ Y / r) :
    (∫ β in (-(1 / 2) : ℝ)..(1 / 2),
      smoothedKernel r b₁ Y β * smoothedKernel r b₂ Y β * e (-((k : ℝ) * β))) =
      ((∑ j₁ ∈ Finset.range (k + 1),
        quarticBump (((r * j₁ + b₁ : ℕ) : ℝ) / (Y : ℝ)) *
          quarticBump (((r * (k - j₁) + b₂ : ℕ) : ℝ) / (Y : ℝ)) : ℝ) : ℂ) := by
  have hpt : ∀ β : ℝ,
      smoothedKernel r b₁ Y β * smoothedKernel r b₂ Y β * e (-((k : ℝ) * β)) =
      ∑ j₁ ∈ Finset.range (Y / r + 1), ∑ j₂ ∈ Finset.range (Y / r + 1),
        ((quarticBump (((r * j₁ + b₁ : ℕ) : ℝ) / (Y : ℝ)) *
          quarticBump (((r * j₂ + b₂ : ℕ) : ℝ) / (Y : ℝ)) : ℝ) : ℂ) *
          e ((((j₁ : ℤ) + (j₂ : ℤ) - (k : ℤ) : ℤ) : ℝ) * β) := by
    intro β
    unfold smoothedKernel
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j₁ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j₂ _ => ?_
    have hexp : e (β * (j₁ : ℝ)) * e (β * (j₂ : ℝ)) * e (-((k : ℝ) * β)) =
        e ((((j₁ : ℤ) + (j₂ : ℤ) - (k : ℤ) : ℤ) : ℝ) * β) := by
      rw [← e_add, ← e_add]; congr 1; push_cast; ring
    calc (quarticBump ((r * j₁ + b₁ : ℝ) / (Y : ℝ)) : ℂ) * e (β * (j₁ : ℝ)) *
            ((quarticBump ((r * j₂ + b₂ : ℝ) / (Y : ℝ)) : ℂ) * e (β * (j₂ : ℝ))) * e (-((k : ℝ) * β))
        = ((quarticBump (((r * j₁ + b₁ : ℕ) : ℝ) / (Y : ℝ)) *
            quarticBump (((r * j₂ + b₂ : ℕ) : ℝ) / (Y : ℝ)) : ℝ) : ℂ) *
            (e (β * (j₁ : ℝ)) * e (β * (j₂ : ℝ)) * e (-((k : ℝ) * β))) := by push_cast; ring
      _ = _ := by rw [hexp]
  simp_rw [hpt]
  rw [intervalIntegral_finset_sum]
  · have hinner : ∀ j₁ ∈ Finset.range (Y / r + 1),
        (∫ β in (-(1 / 2) : ℝ)..(1 / 2), ∑ j₂ ∈ Finset.range (Y / r + 1),
          ((quarticBump (((r * j₁ + b₁ : ℕ) : ℝ) / (Y : ℝ)) *
            quarticBump (((r * j₂ + b₂ : ℕ) : ℝ) / (Y : ℝ)) : ℝ) : ℂ) *
            e ((((j₁ : ℤ) + (j₂ : ℤ) - (k : ℤ) : ℤ) : ℝ) * β)) =
        ∑ j₂ ∈ Finset.range (Y / r + 1), ∫ β in (-(1 / 2) : ℝ)..(1 / 2),
          ((quarticBump (((r * j₁ + b₁ : ℕ) : ℝ) / (Y : ℝ)) *
            quarticBump (((r * j₂ + b₂ : ℕ) : ℝ) / (Y : ℝ)) : ℝ) : ℂ) *
            e ((((j₁ : ℤ) + (j₂ : ℤ) - (k : ℤ) : ℤ) : ℝ) * β) :=
      fun j₁ _ => intervalIntegral_finset_sum fun j₂ _ =>
        (continuous_const.mul (continuous_e_mul _)).intervalIntegrable _ _
    rw [Finset.sum_congr rfl hinner]
    simp_rw [intervalIntegral.integral_const_mul, integral_e_int_symm]
    rw [Complex.ofReal_sum]
    -- Collapse `j₂` to `k - j₁` for `j₁ ≤ k`, and `0` for `j₁ > k`.
    have hsplit : ∑ j₁ ∈ Finset.range (Y / r + 1),
        ∑ j₂ ∈ Finset.range (Y / r + 1),
          ((quarticBump (((r * j₁ + b₁ : ℕ) : ℝ) / (Y : ℝ)) *
            quarticBump (((r * j₂ + b₂ : ℕ) : ℝ) / (Y : ℝ)) : ℝ) : ℂ) *
            (if (j₁ : ℤ) + (j₂ : ℤ) - (k : ℤ) = 0 then (1 : ℂ) else 0) =
        ∑ j₁ ∈ Finset.range (k + 1),
          ((quarticBump (((r * j₁ + b₁ : ℕ) : ℝ) / (Y : ℝ)) *
            quarticBump (((r * (k - j₁) + b₂ : ℕ) : ℝ) / (Y : ℝ)) : ℝ) : ℂ) := by
      have hsub : Finset.range (k + 1) ⊆ Finset.range (Y / r + 1) :=
        Finset.range_mono (by omega)
      rw [← Finset.sum_subset hsub]
      · refine Finset.sum_congr rfl fun j₁ hj₁ => ?_
        have hj₁_le : j₁ ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj₁)
        have hkj : k - j₁ ∈ Finset.range (Y / r + 1) := Finset.mem_range.mpr (by omega)
        rw [Finset.sum_eq_single (k - j₁)]
        · have hz : (j₁ : ℤ) + ((k - j₁ : ℕ) : ℤ) - (k : ℤ) = 0 := by omega
          simp [hz]
        · intro j₂ _ hne
          have hnz : (j₁ : ℤ) + (j₂ : ℤ) - (k : ℤ) ≠ 0 := by omega
          simp [hnz]
        · intro h; exact absurd hkj h
      · intro j₁ _ hj₁_not
        have hj₁_gt : k < j₁ := by simpa [Finset.mem_range] using hj₁_not
        apply Finset.sum_eq_zero
        intro j₂ _
        have hnz : (j₁ : ℤ) + (j₂ : ℤ) - (k : ℤ) ≠ 0 := by omega
        simp [hnz]
    exact hsplit
  · intro j₁ _
    exact intervalIntegrable_finset_sum (Finset.range (Y / r + 1)) fun j₂ _ =>
      (continuous_const.mul (continuous_e_mul _)).intervalIntegrable _ _

/-- Summing the product of arithmetic phases over reduced numerators `a mod q` yields `ramanujanSum q n`. -/
lemma sum_modelCoeff_mul_e_eq_ramanujan {r b₁ b₂ k q : ℕ} (hq : 0 < q) (hqr : Nat.Coprime q r) :
    ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      e (-((a : ℝ) * (rInv r q : ℝ) * (b₁ : ℝ) / (q : ℝ))) *
      e (-((a : ℝ) * (rInv r q : ℝ) * (b₂ : ℝ) / (q : ℝ))) *
      e (-((k : ℝ) * ((a : ℝ) / (q : ℝ)))) =
    ramanujanSum q (r * k + b₁ + b₂) := by
  have : NeZero q := ⟨hq.ne'⟩
  set n := r * k + b₁ + b₂
  unfold ramanujanSum
  refine Finset.sum_bij (fun a _ => ((-((a : ZMod q) * (rInv r q : ZMod q))).val)) ?_ ?_ ?_ ?_
  · intro a ha
    have ha_cop := (Finset.mem_filter.mp ha).2
    have hu_a : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 ha_cop
    have hu_ri : IsUnit (rInv r q : ZMod q) := (ZMod.isUnit_iff_coprime _ q).2 (rInv_coprime hq hqr)
    have hu : IsUnit (-((a : ZMod q) * (rInv r q : ZMod q))) := (hu_a.mul hu_ri).neg
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
    rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
    exact hu
  · intro a₁ ha₁ a₂ ha₂ hEq
    have hlt1 := Finset.mem_range.mp (Finset.mem_filter.mp ha₁).1
    have hlt2 := Finset.mem_range.mp (Finset.mem_filter.mp ha₂).1
    have hz : -((a₁ : ZMod q) * (rInv r q : ZMod q)) = -((a₂ : ZMod q) * (rInv r q : ZMod q)) := by
      have h := congrArg (fun m : ℕ => (m : ZMod q)) hEq
      simpa only [ZMod.natCast_zmod_val] using h
    have hu_ri : IsUnit (rInv r q : ZMod q) := (ZMod.isUnit_iff_coprime _ q).2 (rInv_coprime hq hqr)
    have hz2 : (a₁ : ZMod q) = (a₂ : ZMod q) := hu_ri.mul_right_cancel (neg_inj.mp hz)
    have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).1 hz2
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hmod
  · intro u hu
    have hu_lt := Finset.mem_range.mp (Finset.mem_filter.mp hu).1
    have hu_cop := (Finset.mem_filter.mp hu).2
    let z : ZMod q := -((u : ZMod q) * (r : ZMod q))
    have hu_u : IsUnit (u : ZMod q) := (ZMod.isUnit_iff_coprime u q).2 hu_cop
    have hu_r : IsUnit (r : ZMod q) := (ZMod.isUnit_iff_coprime r q).2 hqr.symm
    have hz_unit : IsUnit z := (hu_u.mul hu_r).neg
    have hrr : (r : ZMod q) * (rInv r q : ZMod q) = 1 := by
      have := (ZMod.natCast_eq_natCast_iff _ _ _).2 (mul_rInv_modEq hq hqr)
      simpa [Nat.cast_mul] using this
    refine ⟨z.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr z.val_lt, ?_⟩, ?_⟩
    · rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]; exact hz_unit
    · rw [ZMod.natCast_zmod_val]
      have hcalc : -(z * (rInv r q : ZMod q)) = (u : ZMod q) := by
        dsimp [z]
        calc -(-((u : ZMod q) * (r : ZMod q)) * (rInv r q : ZMod q))
            = (u : ZMod q) * ((r : ZMod q) * (rInv r q : ZMod q)) := by ring
          _ = (u : ZMod q) := by rw [hrr, mul_one]
      rw [hcalc, ZMod.val_natCast_of_lt hu_lt]
  · intro a _
    rw [← e_add, ← e_add]
    let u := (-((a : ZMod q) * (rInv r q : ZMod q))).val
    have hmod_u : (u : ZMod q) + (a : ZMod q) * (rInv r q : ZMod q) = 0 := by
      dsimp [u]; rw [ZMod.natCast_zmod_val]; ring
    have hrr : (r : ZMod q) * (rInv r q : ZMod q) = 1 := by
      have := (ZMod.natCast_eq_natCast_iff _ _ _).2 (mul_rInv_modEq hq hqr)
      simpa [Nat.cast_mul] using this
    have hzero : ((a * rInv r q * b₁ + a * rInv r q * b₂ + k * a + u * n : ℕ) : ZMod q) = 0 := by
      push_cast
      have h1 : (a : ZMod q) * (rInv r q : ZMod q) * (b₁ : ZMod q) +
          (a : ZMod q) * (rInv r q : ZMod q) * (b₂ : ZMod q) + (k : ZMod q) * (a : ZMod q) =
          (a : ZMod q) * (rInv r q : ZMod q) * ((n : ℕ) : ZMod q) := by
        dsimp [n]; push_cast
        calc (a : ZMod q) * (rInv r q : ZMod q) * (b₁ : ZMod q) +
              (a : ZMod q) * (rInv r q : ZMod q) * (b₂ : ZMod q) + (k : ZMod q) * (a : ZMod q)
            = (a : ZMod q) * (rInv r q : ZMod q) * (b₁ : ZMod q) +
              (a : ZMod q) * (rInv r q : ZMod q) * (b₂ : ZMod q) + (k : ZMod q) * (a : ZMod q) * 1 := by ring
          _ = (a : ZMod q) * (rInv r q : ZMod q) * (b₁ : ZMod q) +
              (a : ZMod q) * (rInv r q : ZMod q) * (b₂ : ZMod q) +
              (k : ZMod q) * (a : ZMod q) * ((r : ZMod q) * (rInv r q : ZMod q)) := by rw [hrr]
          _ = (a : ZMod q) * (rInv r q : ZMod q) * ((r : ZMod q) * (k : ZMod q) + (b₁ : ZMod q) + (b₂ : ZMod q)) := by ring
      calc (a : ZMod q) * (rInv r q : ZMod q) * (b₁ : ZMod q) +
            (a : ZMod q) * (rInv r q : ZMod q) * (b₂ : ZMod q) + (k : ZMod q) * (a : ZMod q) +
            (u : ZMod q) * ((n : ℕ) : ZMod q)
          = ((u : ZMod q) + (a : ZMod q) * (rInv r q : ZMod q)) * ((n : ℕ) : ZMod q) := by
            rw [h1]; ring
        _ = 0 := by rw [hmod_u, zero_mul]
    have hdvd : q ∣ a * rInv r q * b₁ + a * rInv r q * b₂ + k * a + u * n :=
      (ZMod.natCast_eq_zero_iff _ _).1 hzero
    obtain ⟨m, hm⟩ := hdvd
    apply e_eq_of_sub_int (k := -(m : ℤ))
    have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
    have hmR : (a : ℝ) * (rInv r q : ℝ) * (b₁ : ℝ) + (a : ℝ) * (rInv r q : ℝ) * (b₂ : ℝ) +
        (k : ℝ) * (a : ℝ) + (u : ℝ) * (n : ℝ) = (q : ℝ) * (m : ℝ) := by
      exact_mod_cast hm
    change -((a : ℝ) * (rInv r q : ℝ) * (b₁ : ℝ) / (q : ℝ)) +
        -((a : ℝ) * (rInv r q : ℝ) * (b₂ : ℝ) / (q : ℝ)) +
        -((k : ℝ) * ((a : ℝ) / (q : ℝ))) - (u : ℝ) * (n : ℝ) / (q : ℝ) = (-(m : ℤ) : ℝ)
    push_cast; field_simp [hq0]; linarith

/-- Helper: tail integral `∫_{δ ≤ |β| ≤ 1/2} 4 / β² ≤ 16 * q * Q` for `δ = 1 / (2 * q * Q)`. -/
lemma tail_integral_four_div_sq {q Q : ℕ} (hq : 0 < q) (hQ : 2 ≤ Q) :
    (∫ β in (-(1 / 2) : ℝ)..(1 / 2),
      if |β| < 1 / (2 * (q : ℝ) * (Q : ℝ)) then (0 : ℝ) else 4 / β ^ 2) ≤
      16 * (q : ℝ) * (Q : ℝ) := by
  set δ : ℝ := 1 / (2 * (q : ℝ) * (Q : ℝ))
  have hq_pos : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hQ_ge2 : (2 : ℝ) ≤ Q := Nat.cast_le.mpr hQ
  have hδ_pos : 0 < δ := by positivity
  have hδ_lt : δ < 1 / 2 := by
    dsimp [δ]
    rw [div_lt_div_iff₀ (by positivity) two_pos]
    have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr hq
    nlinarith
  let g : ℝ → ℝ := fun β => if |β| < δ then 0 else 4 / β ^ 2
  have hg_int : ∀ a b : ℝ, -(1 / 2) ≤ a → b ≤ 1 / 2 → IntervalIntegrable g MeasureTheory.volume a b := by
    intro a b _ _
    have hmeas : Measurable g :=
      Measurable.ite (measurableSet_lt continuous_abs.measurable measurable_const)
        measurable_const (measurable_const.div (measurable_id.pow_const 2))
    refine intervalIntegrable_of_measurable_bounded (B := 4 / δ ^ 2) hmeas ?_
    intro β
    rw [Real.norm_eq_abs]
    dsimp [g]
    split_ifs with h
    · rw [abs_zero]; positivity
    · rw [abs_of_nonneg (by positivity)]
      have hge : δ ≤ |β| := not_lt.mp h
      have hsq : δ ^ 2 ≤ β ^ 2 := by rw [← sq_abs β]; exact pow_le_pow_left₀ hδ_pos.le hge 2
      exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hδ_pos 2) hsq
  -- Split `[-1/2, 1/2]` at `-δ` and `δ`.
  have hsp1 := (intervalIntegral.integral_add_adjacent_intervals
    (hg_int (-(1 / 2)) (-δ) le_rfl (by linarith))
    (hg_int (-δ) (1 / 2) (by linarith) le_rfl)).symm
  have hsp2 := (intervalIntegral.integral_add_adjacent_intervals
    (hg_int (-δ) δ (by linarith) (by linarith))
    (hg_int δ (1 / 2) (by linarith) le_rfl)).symm
  have hmid : (∫ β in (-δ)..δ, g β) = 0 := by
    have hzero : ∫ β in (-δ)..δ, (0 : ℝ) = 0 := by simp
    rw [← hzero]
    apply intervalIntegral.integral_congr_ae
    have hne : ∀ᵐ β ∂MeasureTheory.volume, β ≠ -δ ∧ β ≠ δ := by
      have h1 : ∀ᵐ β ∂MeasureTheory.volume, β ≠ -δ := by
        rw [MeasureTheory.ae_iff]; simp
      have h2 : ∀ᵐ β ∂MeasureTheory.volume, β ≠ δ := by
        rw [MeasureTheory.ae_iff]; simp
      exact h1.and h2
    filter_upwards [hne] with β ⟨h1, h2⟩ hmem
    rw [Set.uIoc_of_le (by linarith)] at hmem
    have habs : |β| < δ := abs_lt.mpr ⟨lt_of_le_of_ne hmem.1.le (Ne.symm h1), lt_of_le_of_ne hmem.2 h2⟩
    simp [g, habs]
  have hright : (∫ β in δ..(1 / 2), g β) ≤ 8 * (q : ℝ) * (Q : ℝ) := by
    have heq : (∫ β in δ..(1 / 2), g β) = ∫ β in δ..(1 / 2), 4 / β ^ 2 := by
      apply intervalIntegral.integral_congr
      intro β hβ
      rw [Set.uIcc_of_le hδ_lt.le] at hβ
      have hge : ¬ (|β| < δ) := by rw [abs_of_pos (by linarith [hβ.1])]; linarith [hβ.1]
      simp [g, hge]
    rw [heq]
    have hderiv : ∀ β ∈ Set.uIcc δ (1 / 2 : ℝ), HasDerivAt (fun x : ℝ => -(4 / x)) (4 / β ^ 2) β := by
      intro β hβ
      rw [Set.uIcc_of_le hδ_lt.le] at hβ
      have hβ0 : β ≠ 0 := by linarith [hβ.1]
      have hd := (hasDerivAt_inv hβ0).const_mul (-4 : ℝ)
      have hfun : (fun x : ℝ => -(4 / x)) = fun x : ℝ => (-4 : ℝ) * x⁻¹ := by funext x; ring
      have hval : (-4 : ℝ) * -(β ^ 2)⁻¹ = 4 / β ^ 2 := by ring
      rw [hfun, ← hval]; exact hd
    have hcont : ContinuousOn (fun β : ℝ => 4 / β ^ 2) (Set.uIcc δ (1 / 2)) := by
      refine continuousOn_const.div (continuousOn_pow 2) fun β hβ => ?_
      rw [Set.uIcc_of_le hδ_lt.le] at hβ
      exact pow_ne_zero 2 (by linarith [hβ.1])
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
    have h4δ : 4 / δ = 8 * (q : ℝ) * (Q : ℝ) := by dsimp [δ]; field_simp [hq_pos.ne', (by linarith : (Q : ℝ) ≠ 0)]; ring
    linarith
  have hleft : (∫ β in (-(1 / 2))..(-δ), g β) ≤ 8 * (q : ℝ) * (Q : ℝ) := by
    have heq : (∫ β in (-(1 / 2))..(-δ), g β) = ∫ β in (-(1 / 2))..(-δ), 4 / β ^ 2 := by
      apply intervalIntegral.integral_congr
      intro β hβ
      rw [Set.uIcc_of_le (by linarith)] at hβ
      have hge : ¬ (|β| < δ) := by rw [abs_of_neg (by linarith [hβ.2])]; linarith [hβ.2]
      simp [g, hge]
    rw [heq]
    have hderiv : ∀ β ∈ Set.uIcc (-(1 / 2) : ℝ) (-δ), HasDerivAt (fun x : ℝ => -(4 / x)) (4 / β ^ 2) β := by
      intro β hβ
      rw [Set.uIcc_of_le (by linarith)] at hβ
      have hβ0 : β ≠ 0 := by linarith [hβ.2]
      have hd := (hasDerivAt_inv hβ0).const_mul (-4 : ℝ)
      have hfun : (fun x : ℝ => -(4 / x)) = fun x : ℝ => (-4 : ℝ) * x⁻¹ := by funext x; ring
      have hval : (-4 : ℝ) * -(β ^ 2)⁻¹ = 4 / β ^ 2 := by ring
      rw [hfun, ← hval]; exact hd
    have hcont : ContinuousOn (fun β : ℝ => 4 / β ^ 2) (Set.uIcc (-(1 / 2)) (-δ)) := by
      refine continuousOn_const.div (continuousOn_pow 2) fun β hβ => ?_
      rw [Set.uIcc_of_le (by linarith)] at hβ
      exact pow_ne_zero 2 (by linarith [hβ.2])
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
    have h4δ : 4 / δ = 8 * (q : ℝ) * (Q : ℝ) := by dsimp [δ]; field_simp [hq_pos.ne', (by linarith : (Q : ℝ) ≠ 0)]; ring
    have hneg : -(4 / (-δ)) = 4 / δ := by ring
    linarith
  change (∫ β in (-(1 / 2) : ℝ)..(1 / 2), g β) ≤ 16 * (q : ℝ) * (Q : ℝ)
  linarith [hsp1, hsp2, hmid, hleft, hright]

/-- **Module C3 (Model convolution real-part lower bound):**
For admissible even `n = r * k + b₁ + b₂ ∈ (Y/2, Y]` with `Q = Nat.sqrt (Y / r)`, `Q₀ = Q / 2^24`,
`2^25 ≤ Q`, and `rankinConst * n^(1/16) ≤ (1/4) * √Q₀`:
`(∫ α in 0..1, modelSum₁ α * modelSum₂ α * e(-k * α)).re ≥ (1 / 262144) * (r / φ(r))² * (Y / r)`. -/
theorem modelSum_conv_re_lower {r b₁ b₂ Y k : ℕ} (hr : 0 < r) (hb₁ : b₁ < r) (hb₂ : b₂ < r)
    (hn_lo : Y / 2 < r * k + b₁ + b₂) (hn_hi : r * k + b₁ + b₂ ≤ Y)
    (hn_even : Even (r * k + b₁ + b₂))
    (hQ_ge : 2 ^ 25 ≤ Nat.sqrt (Y / r))
    (hRankin : rankinConst * ((r * k + b₁ + b₂ : ℕ) : ℝ) ^ ((1 : ℝ) / 16) ≤
      (1 / 4 : ℝ) * Real.sqrt ((Nat.sqrt (Y / r) / 2 ^ 24 : ℕ) : ℝ)) :
    ((1 : ℝ) / 262144) * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * ((Y : ℝ) / (r : ℝ)) ≤
      (∫ α in (0 : ℝ)..1,
        modelSum r b₁ Y (Nat.sqrt (Y / r)) (Nat.sqrt (Y / r) / 2 ^ 24) α *
        modelSum r b₂ Y (Nat.sqrt (Y / r)) (Nat.sqrt (Y / r) / 2 ^ 24) α *
        e (-((k : ℝ) * α))).re := by
  classical
  set Q := Nat.sqrt (Y / r)
  set Q₀ := Q / 2 ^ 24
  set n := r * k + b₁ + b₂
  have hQ_pos : 0 < Q := by omega
  have hQ_ge2 : 2 ≤ Q := by omega
  have hQ0_ge2 : 2 ≤ Q₀ := by dsimp [Q₀]; omega
  have hYr_ge : 2 ^ 50 ≤ Y / r := by
    have h1 : Q * Q ≤ Y / r := Nat.sqrt_le (Y / r)
    have h2 : 2 ^ 25 * 2 ^ 25 ≤ Q * Q := Nat.mul_le_mul hQ_ge hQ_ge
    have h3 : 2 ^ 50 = 2 ^ 25 * 2 ^ 25 := by norm_num
    omega
  have h16rY : 16 * r ≤ Y := by
    calc 16 * r = r * 16 := mul_comm _ _
      _ ≤ r * (Y / r) := Nat.mul_le_mul_left r (by omega)
      _ ≤ Y := Nat.mul_div_le Y r
  have hk_le : k ≤ Y / r := by
    rw [Nat.le_div_iff_mul_le hr]
    calc k * r = r * k := mul_comm _ _
      _ ≤ Y := by omega
  have hn_pos : 1 ≤ n := by omega
  let Cset := (centers Q).filter (fun c => c.q ≤ Q₀)
  -- Step 1: Decompose integral over `Cset` using disjointness of Voronoi cells.
  have hpt : ∀ α : ℝ,
      modelSum r b₁ Y Q Q₀ α * modelSum r b₂ Y Q Q₀ α * e (-((k : ℝ) * α)) =
      ∑ c ∈ Cset, (voronoiCell Q c).indicator
        (fun x => modelCoeff r b₁ c * modelCoeff r b₂ c *
          smoothedKernel r b₁ Y (wrap (x - c.val)) *
          smoothedKernel r b₂ Y (wrap (x - c.val)) * e (-((k : ℝ) * x))) α := by
    intro α
    unfold modelSum
    rw [mul_sum_disjoint_indicator Cset (voronoiCell Q) (fun c₁ _ c₂ _ hne => voronoiCell_disjoint hne)]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hα : α ∈ voronoiCell Q c
    · rw [Set.indicator_of_mem hα, Set.indicator_of_mem hα]; ring
    · rw [Set.indicator_of_notMem hα, Set.indicator_of_notMem hα, zero_mul]
  simp_rw [hpt]
  have hint_c : ∀ c ∈ Cset,
      IntervalIntegrable
        ((voronoiCell Q c).indicator
          (fun x => modelCoeff r b₁ c * modelCoeff r b₂ c *
            smoothedKernel r b₁ Y (wrap (x - c.val)) *
            smoothedKernel r b₂ Y (wrap (x - c.val)) * e (-((k : ℝ) * x))))
        MeasureTheory.volume 0 1 := by
    intro c _
    have hmeas : Measurable ((voronoiCell Q c).indicator
        (fun x => modelCoeff r b₁ c * modelCoeff r b₂ c *
          smoothedKernel r b₁ Y (wrap (x - c.val)) *
          smoothedKernel r b₂ Y (wrap (x - c.val)) * e (-((k : ℝ) * x)))) := by
      have he_meas : Measurable (fun x : ℝ => e (-((k : ℝ) * x))) := by
        have h : (fun x : ℝ => e (-((k : ℝ) * x))) = fun x : ℝ => e (-(k : ℝ) * x) := by funext x; ring_nf
        rw [h]; exact (continuous_e_mul (-(k : ℝ))).measurable
      refine Measurable.indicator ?_ (voronoiCell_measurable Q c)
      exact (((measurable_const.mul
        ((continuous_smoothedKernel r b₁ Y).measurable.comp (measurable_wrap.comp (measurable_id.sub measurable_const)))).mul
        ((continuous_smoothedKernel r b₂ Y).measurable.comp (measurable_wrap.comp (measurable_id.sub measurable_const)))).mul
        he_meas)
    refine intervalIntegrable_of_measurable_bounded
      (B := ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ * ((Y : ℝ) / (r : ℝ) + 1) ^ 2) hmeas ?_
    intro x
    by_cases hx : x ∈ voronoiCell Q c
    · rw [Set.indicator_of_mem hx, norm_mul, norm_mul, norm_mul, norm_mul, norm_e, mul_one]
      have h1 := smoothedKernel_bound_triv r b₁ Y (wrap (x - c.val))
      have h2 := smoothedKernel_bound_triv r b₂ Y (wrap (x - c.val))
      have hprod : ‖smoothedKernel r b₁ Y (wrap (x - c.val))‖ * ‖smoothedKernel r b₂ Y (wrap (x - c.val))‖ ≤
          ((Y : ℝ) / (r : ℝ) + 1) ^ 2 := by
        rw [sq]; exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      calc ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ *
            ‖smoothedKernel r b₁ Y (wrap (x - c.val))‖ * ‖smoothedKernel r b₂ Y (wrap (x - c.val))‖
          = ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ *
            (‖smoothedKernel r b₁ Y (wrap (x - c.val))‖ * ‖smoothedKernel r b₂ Y (wrap (x - c.val))‖) := by ring
        _ ≤ ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ * ((Y : ℝ) / (r : ℝ) + 1) ^ 2 :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
    · rw [Set.indicator_of_notMem hx, norm_zero]; positivity
  rw [intervalIntegral_finset_sum hint_c]
  -- Step 2: Shift each cell integral to `[-1/2, 1/2]` around `c.val`, and compare with the completed integral!
  let fullConv : ℂ :=
    ∫ β in (-(1 / 2) : ℝ)..(1 / 2),
      smoothedKernel r b₁ Y β * smoothedKernel r b₂ Y β * e (-((k : ℝ) * β))
  let completed : ℂ :=
    ∑ c ∈ Cset, modelCoeff r b₁ c * modelCoeff r b₂ c * e (-((k : ℝ) * c.val)) * fullConv
  -- Bound the completion error `‖(∑ cell) - completed‖ ≤ 48 * (r / φ(r))² * Q * Q₀`.
  have hcomp_err :
      ‖(∑ c ∈ Cset, ∫ α in (0 : ℝ)..1,
          (voronoiCell Q c).indicator
            (fun x => modelCoeff r b₁ c * modelCoeff r b₂ c *
              smoothedKernel r b₁ Y (wrap (x - c.val)) *
              smoothedKernel r b₂ Y (wrap (x - c.val)) * e (-((k : ℝ) * x))) α) - completed‖ ≤
      48 * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * (Q : ℝ) * (Q₀ : ℝ) := by
    dsimp [completed]
    rw [← Finset.sum_sub_distrib]
    have hcell_err : ∀ c ∈ Cset,
        ‖(∫ α in (0 : ℝ)..1,
            (voronoiCell Q c).indicator
              (fun x => modelCoeff r b₁ c * modelCoeff r b₂ c *
                smoothedKernel r b₁ Y (wrap (x - c.val)) *
                smoothedKernel r b₂ Y (wrap (x - c.val)) * e (-((k : ℝ) * x))) α) -
          modelCoeff r b₁ c * modelCoeff r b₂ c * e (-((k : ℝ) * c.val)) * fullConv‖ ≤
        ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ * (16 * (c.q : ℝ) * (Q : ℝ)) := by
      intro c hc
      have hc_mem : c ∈ centers Q := (Finset.mem_filter.mp hc).1
      have hper : Function.Periodic ((voronoiCell Q c).indicator
          (fun x => modelCoeff r b₁ c * modelCoeff r b₂ c *
            smoothedKernel r b₁ Y (wrap (x - c.val)) *
            smoothedKernel r b₂ Y (wrap (x - c.val)) * e (-((k : ℝ) * x)))) 1 := by
        intro x
        by_cases hx : x ∈ voronoiCell Q c
        · rw [Set.indicator_of_mem ((voronoiCell_periodic Q c x).2 hx), Set.indicator_of_mem hx]
          have h1 : x + 1 - c.val = (x - c.val) + 1 := by ring
          have h2 : -((k : ℝ) * (x + 1)) = -((k : ℝ) * x) + ((-(k : ℤ) : ℤ) : ℝ) := by
            rw [Int.cast_neg, Int.cast_natCast]; ring
          rw [h1, wrap_add_one, h2, e_add_int]
        · rw [Set.indicator_of_notMem (fun h => hx ((voronoiCell_periodic Q c x).1 h)), Set.indicator_of_notMem hx]
      rw [intervalIntegral_shift_symm hper c.val]
      dsimp [fullConv]
      rw [← intervalIntegral.integral_const_mul]
      -- Combine both integrals into one over `[-1/2, 1/2]`.
      let f_cell : ℝ → ℂ := fun β =>
        (voronoiCell Q c).indicator
          (fun x => modelCoeff r b₁ c * modelCoeff r b₂ c *
            smoothedKernel r b₁ Y (wrap (x - c.val)) *
            smoothedKernel r b₂ Y (wrap (x - c.val)) * e (-((k : ℝ) * x))) (c.val + β)
      let f_full : ℝ → ℂ := fun β =>
        modelCoeff r b₁ c * modelCoeff r b₂ c * e (-((k : ℝ) * c.val)) *
          (smoothedKernel r b₁ Y β * smoothedKernel r b₂ Y β * e (-((k : ℝ) * β)))
      have hf_cell_int : IntervalIntegrable f_cell MeasureTheory.volume (-(1 / 2)) (1 / 2) := by
        have he_meas : Measurable (fun x : ℝ => e (-((k : ℝ) * x))) := by
          have h : (fun x : ℝ => e (-((k : ℝ) * x))) = fun x : ℝ => e (-(k : ℝ) * x) := by funext x; ring_nf
          rw [h]; exact (continuous_e_mul (-(k : ℝ))).measurable
        have hm0 : Measurable ((voronoiCell Q c).indicator
            (fun x => modelCoeff r b₁ c * modelCoeff r b₂ c *
              smoothedKernel r b₁ Y (wrap (x - c.val)) *
              smoothedKernel r b₂ Y (wrap (x - c.val)) * e (-((k : ℝ) * x)))) :=
          Measurable.indicator
            (((measurable_const.mul
              ((continuous_smoothedKernel r b₁ Y).measurable.comp (measurable_wrap.comp (measurable_id.sub measurable_const)))).mul
              ((continuous_smoothedKernel r b₂ Y).measurable.comp (measurable_wrap.comp (measurable_id.sub measurable_const)))).mul
              he_meas)
            (voronoiCell_measurable Q c)
        refine intervalIntegrable_of_measurable_bounded
          (B := ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ * ((Y : ℝ) / (r : ℝ) + 1) ^ 2)
          (hm0.comp (measurable_const.add measurable_id)) ?_
        intro β
        dsimp [f_cell]
        by_cases hx : c.val + β ∈ voronoiCell Q c
        · rw [Set.indicator_of_mem hx, norm_mul, norm_mul, norm_mul, norm_mul, norm_e, mul_one]
          have h1 := smoothedKernel_bound_triv r b₁ Y (wrap (c.val + β - c.val))
          have h2 := smoothedKernel_bound_triv r b₂ Y (wrap (c.val + β - c.val))
          have hprod : ‖smoothedKernel r b₁ Y (wrap (c.val + β - c.val))‖ *
              ‖smoothedKernel r b₂ Y (wrap (c.val + β - c.val))‖ ≤ ((Y : ℝ) / (r : ℝ) + 1) ^ 2 := by
            rw [sq]; exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
          calc ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ *
                ‖smoothedKernel r b₁ Y (wrap (c.val + β - c.val))‖ *
                ‖smoothedKernel r b₂ Y (wrap (c.val + β - c.val))‖
              = ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ *
                (‖smoothedKernel r b₁ Y (wrap (c.val + β - c.val))‖ *
                 ‖smoothedKernel r b₂ Y (wrap (c.val + β - c.val))‖) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by positivity)
        · rw [Set.indicator_of_notMem hx, norm_zero]; positivity
      have hf_full_int : IntervalIntegrable f_full MeasureTheory.volume (-(1 / 2)) (1 / 2) := by
        have hcont : Continuous f_full := by
          dsimp [f_full]
          refine continuous_const.mul (((continuous_smoothedKernel r b₁ Y).mul (continuous_smoothedKernel r b₂ Y)).mul ?_)
          have h : (fun β : ℝ => e (-((k : ℝ) * β))) = fun β : ℝ => e (-(k : ℝ) * β) := by funext β; ring_nf
          rw [h]; exact continuous_e_mul (-(k : ℝ))
        exact hcont.intervalIntegrable _ _
      change ‖(∫ β in (-(1 / 2) : ℝ)..(1 / 2), f_cell β) - (∫ β in (-(1 / 2) : ℝ)..(1 / 2), f_full β)‖ ≤ _
      rw [← intervalIntegral.integral_sub hf_cell_int hf_full_int]
      -- Bound `‖f_cell β - f_full β‖` pointwise on `[-1/2, 1/2]`.
      set δ := 1 / (2 * (c.q : ℝ) * (Q : ℝ))
      let maj : ℝ → ℝ := fun β =>
        (‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖) * (if |β| < δ then 0 else 4 / β ^ 2)
      have hmaj_int : IntervalIntegrable maj MeasureTheory.volume (-(1 / 2)) (1 / 2) := by
        have hδ_pos : 0 < δ := by
          dsimp [δ]; have : (0 : ℝ) < c.q := Nat.cast_pos.mpr c.q_pos; positivity
        have hmeas : Measurable maj :=
          measurable_const.mul (Measurable.ite (measurableSet_lt continuous_abs.measurable measurable_const)
            measurable_const (measurable_const.div (measurable_id.pow_const 2)))
        refine intervalIntegrable_of_measurable_bounded
          (B := ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ * (4 / δ ^ 2)) hmeas ?_
        intro β
        rw [Real.norm_eq_abs]
        dsimp [maj]
        split_ifs with h
        · rw [mul_zero, abs_zero]; positivity
        · rw [abs_of_nonneg (by positivity)]
          have hge : δ ≤ |β| := not_lt.mp h
          have hsq : δ ^ 2 ≤ β ^ 2 := by rw [← sq_abs β]; exact pow_le_pow_left₀ hδ_pos.le hge 2
          exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by norm_num) (pow_pos hδ_pos 2) hsq) (by positivity)
      have hnorm_le : ‖∫ β in (-(1 / 2) : ℝ)..(1 / 2), (f_cell β - f_full β)‖ ≤
          ∫ β in (-(1 / 2) : ℝ)..(1 / 2), maj β := by
        refine intervalIntegral.norm_integral_le_of_norm_le (by norm_num) ?_ hmaj_int
        filter_upwards with β hβ
        have hβ_half : |β| ≤ 1 / 2 := abs_le.mpr ⟨hβ.1.le, hβ.2⟩
        by_cases hlt : |β| < δ
        · have hmem : c.val + β ∈ voronoiCell Q c := voronoiCell_inner_subset_beta hQ_pos hc_mem hlt
          have hsub0 : f_cell β - f_full β = 0 := by
            dsimp [f_cell, f_full]
            rw [Set.indicator_of_mem hmem]
            have hs : c.val + β - c.val = β := by ring
            have he : e (-((k : ℝ) * (c.val + β))) = e (-((k : ℝ) * c.val)) * e (-((k : ℝ) * β)) := by
              rw [← e_add]; congr 1; ring
            rw [hs, smoothedKernel_wrap, smoothedKernel_wrap, he]; ring
          rw [hsub0, norm_zero]
          dsimp [maj]; rw [ite_eq_left hlt, mul_zero]
        · have hβ0 : β ≠ 0 := by
            intro hz; subst hz; rw [abs_zero] at hlt
            have hδ_pos : 0 < δ := by
              dsimp [δ]; have : (0 : ℝ) < c.q := Nat.cast_pos.mpr c.q_pos; positivity
            exact hlt hδ_pos
          have hpt_le : ‖f_cell β - f_full β‖ ≤ ‖f_full β‖ := by
            by_cases hmem : c.val + β ∈ voronoiCell Q c
            · have hsub0 : f_cell β - f_full β = 0 := by
                dsimp [f_cell, f_full]
                rw [Set.indicator_of_mem hmem]
                have hs : c.val + β - c.val = β := by ring
                have he : e (-((k : ℝ) * (c.val + β))) = e (-((k : ℝ) * c.val)) * e (-((k : ℝ) * β)) := by
                  rw [← e_add]; congr 1; ring
                rw [hs, smoothedKernel_wrap, smoothedKernel_wrap, he]; ring
              rw [hsub0, norm_zero]; exact norm_nonneg _
            · dsimp [f_cell]
              rw [Set.indicator_of_notMem hmem, zero_sub, norm_neg]
          dsimp [maj]
          rw [ite_eq_right hlt]
          refine hpt_le.trans ?_
          dsimp [f_full]
          rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_e, norm_e, mul_one, mul_one]
          have hd1 := smoothedKernel_bound_decay r b₁ Y hβ0 hβ_half
          have hd2 := smoothedKernel_bound_decay r b₂ Y hβ0 hβ_half
          have hprod : ‖smoothedKernel r b₁ Y β‖ * ‖smoothedKernel r b₂ Y β‖ ≤ 4 / β ^ 2 := by
            calc ‖smoothedKernel r b₁ Y β‖ * ‖smoothedKernel r b₂ Y β‖
                ≤ (2 / |β|) * (2 / |β|) := mul_le_mul hd1 hd2 (norm_nonneg _) (by positivity)
              _ = 4 / β ^ 2 := by rw [div_mul_div_comm, ← sq, ← sq, sq_abs]; norm_num
          exact mul_le_mul_of_nonneg_left hprod (by positivity)
      calc ‖∫ β in (-(1 / 2) : ℝ)..(1 / 2), (f_cell β - f_full β)‖
          ≤ ∫ β in (-(1 / 2) : ℝ)..(1 / 2), maj β := hnorm_le
        _ = (‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖) *
              ∫ β in (-(1 / 2) : ℝ)..(1 / 2), (if |β| < δ then (0 : ℝ) else 4 / β ^ 2) :=
            intervalIntegral.integral_const_mul _ _
        _ ≤ (‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖) * (16 * (c.q : ℝ) * (Q : ℝ)) :=
            mul_le_mul_of_nonneg_left (tail_integral_four_div_sq c.q_pos hQ_ge2) (by positivity)
    -- Sum `hcell_err` over `c ∈ Cset`, grouping by squarefree `q ∈ Icc 1 Q₀`!
    calc ‖∑ c ∈ Cset, ((∫ α in (0 : ℝ)..1,
            (voronoiCell Q c).indicator
              (fun x => modelCoeff r b₁ c * modelCoeff r b₂ c *
                smoothedKernel r b₁ Y (wrap (x - c.val)) *
                smoothedKernel r b₂ Y (wrap (x - c.val)) * e (-((k : ℝ) * x))) α) -
            modelCoeff r b₁ c * modelCoeff r b₂ c * e (-((k : ℝ) * c.val)) * fullConv)‖
        ≤ ∑ c ∈ Cset, ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ * (16 * (c.q : ℝ) * (Q : ℝ)) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum hcell_err)
      _ ≤ 16 * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * (Q : ℝ) *
            ∑ q ∈ (Finset.Icc 1 Q₀).filter Squarefree, ((q : ℝ) / (q.totient : ℝ)) := by
          let Qsf := (Finset.Icc 1 Q₀).filter Squarefree
          let Cgood := Cset.filter (fun c => c.q ∈ Qsf)
          have htrim : ∑ c ∈ Cset, ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ * (16 * (c.q : ℝ) * (Q : ℝ)) =
              ∑ c ∈ Cgood, ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ * (16 * (c.q : ℝ) * (Q : ℝ)) := by
            symm; rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun c hc => ?_
            split_ifs with h
            · rfl
            · have h0 : modelCoeff r b₁ c = 0 := by
                unfold modelCoeff
                by_cases hcop : Nat.Coprime c.q r
                · rw [ite_eq_left hcop]
                  have hnsf : ¬ Squarefree c.q := fun hsf =>
                    h (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨c.q_pos, (Finset.mem_filter.mp hc).2⟩, hsf⟩)
                  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsf]; simp
                · exact ite_eq_right hcop
              simp [h0]
          rw [htrim,
              ← Finset.sum_fiberwise_of_maps_to (s := Cgood) (t := Qsf) (g := fun c : RatCenter => c.q)
                (fun c hc => (Finset.mem_filter.mp hc).2),
              Finset.mul_sum]
          refine Finset.sum_le_sum fun q hq => ?_
          have hq_pos : 0 < q := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
          have hq_sf : Squarefree q := (Finset.mem_filter.mp hq).2
          have hcard_a : (Cgood.filter (fun c => c.q = q)).card ≤ q.totient := by
            have hsub : (Cgood.filter (fun c => c.q = q)).image (fun c => c.a) ⊆
                (Finset.range q).filter (fun a => Nat.Coprime a q) := by
              intro a ha
              obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ha
              have hcq : c.q = q := (Finset.mem_filter.mp hc).2
              exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hcq ▸ c.a_lt), hcq ▸ c.coprime⟩
            have hinj : Set.InjOn (fun c : RatCenter => c.a) (Cgood.filter (fun c => c.q = q) : Set RatCenter) := by
              intro c₁ h1 c₂ h2 hEq
              exact RatCenter.ext hEq ((Finset.mem_filter.mp h1).2.trans (Finset.mem_filter.mp h2).2.symm)
            rw [← Finset.card_image_of_injOn hinj]
            calc ((Cgood.filter (fun c => c.q = q)).image (fun c => c.a)).card
                ≤ ((Finset.range q).filter (fun a => Nat.Coprime a q)).card := Finset.card_le_card hsub
              _ = q.totient := by rw [Nat.totient_eq_card_coprime]; congr 1; ext a; simp [Nat.coprime_comm]
          have hterm_le : ∀ c ∈ Cgood.filter (fun c => c.q = q),
              ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ * (16 * (c.q : ℝ) * (Q : ℝ)) ≤
                (((r : ℝ) / (r.totient : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2) * (16 * (q : ℝ) * (Q : ℝ)) := by
            intro c hc
            have hcq : c.q = q := (Finset.mem_filter.mp hc).2
            rw [hcq]
            have hm_le : ∀ b', ‖modelCoeff r b' c‖ ≤ ((r : ℝ) / (r.totient : ℝ)) / (q.totient : ℝ) := fun b' => by
              unfold modelCoeff
              rw [hcq]
              split_ifs with hcop
              · rw [norm_mul, norm_mul, norm_e, one_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
                    abs_of_nonneg (by positivity), Complex.norm_intCast, Complex.norm_natCast,
                    ArithmeticFunction.moebius_apply_of_squarefree hq_sf]
                simp [div_eq_mul_inv]
              · rw [norm_zero]; positivity
            have hmul := mul_le_mul (hm_le b₁) (hm_le b₂) (norm_nonneg _) (by positivity)
            have hsq : (((r : ℝ) / (r.totient : ℝ)) / (q.totient : ℝ)) *
                (((r : ℝ) / (r.totient : ℝ)) / (q.totient : ℝ)) =
                ((r : ℝ) / (r.totient : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2 := by ring
            rw [hsq] at hmul
            exact mul_le_mul_of_nonneg_right hmul (by positivity)
          calc ∑ c ∈ Cgood.filter (fun c => c.q = q),
                ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ * (16 * (c.q : ℝ) * (Q : ℝ))
              ≤ ∑ _c ∈ Cgood.filter (fun c => c.q = q),
                  ((((r : ℝ) / (r.totient : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2) * (16 * (q : ℝ) * (Q : ℝ))) :=
                Finset.sum_le_sum hterm_le
            _ = ((Cgood.filter (fun c => c.q = q)).card : ℝ) *
                  ((((r : ℝ) / (r.totient : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2) * (16 * (q : ℝ) * (Q : ℝ))) := by
                simp [nsmul_eq_mul]
            _ ≤ (q.totient : ℝ) *
                  ((((r : ℝ) / (r.totient : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2) * (16 * (q : ℝ) * (Q : ℝ))) :=
                mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard_a) (by positivity)
            _ = 16 * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * (Q : ℝ) * ((q : ℝ) / (q.totient : ℝ)) := by
                have hqt0 : (q.totient : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hq_pos).ne'
                field_simp [hqt0]
      _ ≤ 16 * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * (Q : ℝ) * (3 * (Q₀ : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_sqfree_div_totient_le Q₀) (by positivity)
      _ = 48 * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * (Q : ℝ) * (Q₀ : ℝ) := by ring
  -- Step 3: Evaluate `completed` exactly as `(r / φ(r))² * singularTrunc r n Q₀ * quarticConv`!
  have hcomp_eq : completed =
      ((((r : ℝ) / (r.totient : ℝ)) ^ 2 : ℝ) : ℂ) * singularTrunc r n Q₀ *
      ((∑ j₁ ∈ Finset.range (k + 1),
        quarticBump (((r * j₁ + b₁ : ℕ) : ℝ) / (Y : ℝ)) *
          quarticBump (((r * (k - j₁) + b₂ : ℕ) : ℝ) / (Y : ℝ)) : ℝ) : ℂ) := by
    dsimp [completed, fullConv]
    rw [integral_smoothedKernel_mul_e hk_le, ← Finset.sum_mul]
    congr 1
    unfold singularTrunc
    rw [Finset.mul_sum]
    -- Group `Cset` by `q ∈ (Icc 1 Q₀).filter (Coprime · r)`!
    let Qcop := (Finset.Icc 1 Q₀).filter (fun q => Nat.Coprime q r)
    let Ccop := Cset.filter (fun c => c.q ∈ Qcop)
    have htrim : ∑ c ∈ Cset, modelCoeff r b₁ c * modelCoeff r b₂ c * e (-((k : ℝ) * c.val)) =
        ∑ c ∈ Ccop, modelCoeff r b₁ c * modelCoeff r b₂ c * e (-((k : ℝ) * c.val)) := by
      symm; rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun c hc => ?_
      split_ifs with h
      · rfl
      · have hncop : ¬ Nat.Coprime c.q r := fun hcop =>
          h (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨c.q_pos, (Finset.mem_filter.mp hc).2⟩, hcop⟩)
        unfold modelCoeff
        rw [ite_eq_right hncop, zero_mul, zero_mul]
    rw [htrim,
        ← Finset.sum_fiberwise_of_maps_to (s := Ccop) (t := Qcop) (g := fun c : RatCenter => c.q)
          (fun c hc => (Finset.mem_filter.mp hc).2)]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
    have hq_pos : 0 < q := hq_Icc.1
    have hq_le_Q0 : q ≤ Q₀ := hq_Icc.2
    have hq_le_Q : q ≤ Q := hq_le_Q0.trans (Nat.div_le_self Q (2 ^ 24))
    have hq_cop : Nat.Coprime q r := (Finset.mem_filter.mp hq).2
    -- Biject `Ccop.filter (c.q = q)` with `(range q).filter (Coprime · q)` via `c ↦ c.a`!
    have hbij : ∑ c ∈ Ccop.filter (fun c => c.q = q),
          modelCoeff r b₁ c * modelCoeff r b₂ c * e (-((k : ℝ) * c.val)) =
        ((((r : ℝ) / (r.totient : ℝ)) ^ 2 : ℝ) : ℂ) *
          ((ArithmeticFunction.moebius q : ℂ) ^ 2 / (q.totient : ℂ) ^ 2) *
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            e (-((a : ℝ) * (rInv r q : ℝ) * (b₁ : ℝ) / (q : ℝ))) *
            e (-((a : ℝ) * (rInv r q : ℝ) * (b₂ : ℝ) / (q : ℝ))) *
            e (-((k : ℝ) * ((a : ℝ) / (q : ℝ)))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun c _ => c.a) ?_ ?_ ?_ ?_
      · intro c hc
        have hcq : c.q = q := (Finset.mem_filter.mp hc).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hcq ▸ c.a_lt), hcq ▸ c.coprime⟩
      · intro c₁ h1 c₂ h2 hEq
        exact RatCenter.ext hEq ((Finset.mem_filter.mp h1).2.trans (Finset.mem_filter.mp h2).2.symm)
      · intro a ha
        have ha_lt := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
        have ha_cop := (Finset.mem_filter.mp ha).2
        let c : RatCenter := ⟨a, q, hq_pos, ha_lt, ha_cop⟩
        refine ⟨c, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨mem_centers_iff.mpr hq_le_Q, hq_le_Q0⟩, hq⟩, rfl⟩
      · intro c hc
        have hcq : c.q = q := (Finset.mem_filter.mp hc).2
        unfold modelCoeff RatCenter.val
        rw [hcq, ite_eq_left hq_cop, ite_eq_left hq_cop]
        push_cast; ring
    rw [hbij, sum_modelCoeff_mul_e_eq_ramanujan hq_pos hq_cop]
    ring
  -- Step 4: Combine main-term lower bound (`singularTrunc_re_lower` * `quarticBump_conv_lower`) with `hcomp_err`!
  have hmain_re : ((1 : ℝ) / 131072) * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * ((Y : ℝ) / (r : ℝ)) ≤
      completed.re := by
    rw [hcomp_eq]
    have hre : (((((r : ℝ) / (r.totient : ℝ)) ^ 2 : ℝ) : ℂ) * singularTrunc r n Q₀ *
        ((∑ j₁ ∈ Finset.range (k + 1),
          quarticBump (((r * j₁ + b₁ : ℕ) : ℝ) / (Y : ℝ)) *
            quarticBump (((r * (k - j₁) + b₂ : ℕ) : ℝ) / (Y : ℝ)) : ℝ) : ℂ)).re =
        ((r : ℝ) / (r.totient : ℝ)) ^ 2 * (singularTrunc r n Q₀).re *
          (∑ j₁ ∈ Finset.range (k + 1),
            quarticBump (((r * j₁ + b₁ : ℕ) : ℝ) / (Y : ℝ)) *
              quarticBump (((r * (k - j₁) + b₂ : ℕ) : ℝ) / (Y : ℝ))) := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_mul]
    rw [hre]
    have hsing := singularTrunc_re_lower r n Q₀ hn_pos hn_even hQ0_ge2 hRankin
    have hconv := quarticBump_conv_lower hr hb₁ hb₂ h16rY hn_lo hn_hi
    have hmul : (1 / 4 : ℝ) * (((1 : ℝ) / 32768) * ((Y : ℝ) / (r : ℝ))) ≤
        (singularTrunc r n Q₀).re *
          (∑ j₁ ∈ Finset.range (k + 1),
            quarticBump (((r * j₁ + b₁ : ℕ) : ℝ) / (Y : ℝ)) *
              quarticBump (((r * (k - j₁) + b₂ : ℕ) : ℝ) / (Y : ℝ))) :=
      mul_le_mul hsing hconv (by positivity) (by linarith)
    have hmul2 := mul_le_mul_of_nonneg_left hmul (sq_nonneg ((r : ℝ) / (r.totient : ℝ)))
    linarith
  have herr_small : 48 * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * (Q : ℝ) * (Q₀ : ℝ) ≤
      ((1 : ℝ) / 262144) * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * ((Y : ℝ) / (r : ℝ)) := by
    have hQQ0 : (Q : ℝ) * (Q₀ : ℝ) ≤ ((Y : ℝ) / (r : ℝ)) / ((2 : ℝ) ^ 24) := by
      have h1 : Q₀ * 2 ^ 24 ≤ Q := by rw [mul_comm]; exact Nat.mul_div_le Q (2 ^ 24)
      have h2 : Q * Q ≤ Y / r := Nat.sqrt_le (Y / r)
      have h3 : (Q : ℝ) * (Q : ℝ) ≤ (Y : ℝ) / (r : ℝ) := by
        have hdiv : ((Y / r : ℕ) : ℝ) ≤ (Y : ℝ) / (r : ℝ) := by
          rw [le_div_iff₀ (Nat.cast_pos.mpr hr)]
          exact_mod_cast (by simpa [mul_comm] using Nat.mul_div_le Y r)
        exact (by exact_mod_cast h2 : (Q : ℝ) * (Q : ℝ) ≤ ((Y / r : ℕ) : ℝ)).trans hdiv
      have h4 : (Q₀ : ℝ) ≤ (Q : ℝ) / ((2 : ℝ) ^ 24) := by
        rw [le_div_iff₀ (by positivity)]
        exact_mod_cast h1
      calc (Q : ℝ) * (Q₀ : ℝ) ≤ (Q : ℝ) * ((Q : ℝ) / ((2 : ℝ) ^ 24)) :=
            mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg _)
        _ = ((Q : ℝ) * (Q : ℝ)) / ((2 : ℝ) ^ 24) := by ring
        _ ≤ ((Y : ℝ) / (r : ℝ)) / ((2 : ℝ) ^ 24) := div_le_div_of_nonneg_right h3 (by positivity)
    have hcoeff : (48 : ℝ) / ((2 : ℝ) ^ 24) ≤ (1 : ℝ) / 262144 := by norm_num
    calc 48 * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * (Q : ℝ) * (Q₀ : ℝ)
        = 48 * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * ((Q : ℝ) * (Q₀ : ℝ)) := by ring
      _ ≤ 48 * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * (((Y : ℝ) / (r : ℝ)) / ((2 : ℝ) ^ 24)) :=
          mul_le_mul_of_nonneg_left hQQ0 (by positivity)
      _ = ((48 : ℝ) / ((2 : ℝ) ^ 24)) * (((r : ℝ) / (r.totient : ℝ)) ^ 2 * ((Y : ℝ) / (r : ℝ))) := by ring
      _ ≤ ((1 : ℝ) / 262144) * (((r : ℝ) / (r.totient : ℝ)) ^ 2 * ((Y : ℝ) / (r : ℝ))) :=
          mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = ((1 : ℝ) / 262144) * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * ((Y : ℝ) / (r : ℝ)) := by ring
  have hre_diff : |(∑ c ∈ Cset, ∫ α in (0 : ℝ)..1,
      (voronoiCell Q c).indicator
        (fun x => modelCoeff r b₁ c * modelCoeff r b₂ c *
          smoothedKernel r b₁ Y (wrap (x - c.val)) *
          smoothedKernel r b₂ Y (wrap (x - c.val)) * e (-((k : ℝ) * x))) α).re - completed.re| ≤
      48 * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * (Q : ℝ) * (Q₀ : ℝ) := by
    have h1 := Complex.abs_re_le_norm ((∑ c ∈ Cset, ∫ α in (0 : ℝ)..1,
      (voronoiCell Q c).indicator
        (fun x => modelCoeff r b₁ c * modelCoeff r b₂ c *
          smoothedKernel r b₁ Y (wrap (x - c.val)) *
          smoothedKernel r b₂ Y (wrap (x - c.val)) * e (-((k : ℝ) * x))) α) - completed)
    rw [Complex.sub_re] at h1
    exact h1.trans hcomp_err
  have hre_lo := (abs_le.mp hre_diff).1
  linarith

end ModelL2AndConv

end FareyGoldbach
