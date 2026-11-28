import FareyGoldbach.Defs
import FareyGoldbach.CharacterBound
import FareyGoldbach.VoronoiCells
import FareyGoldbach.SingularSeries
import FareyGoldbach.PrimeSums
import FareyGoldbach.ModelAndRemainder
import FareyGoldbach.DyadicAssembly
import FareyGoldbach.SmoothedTwistOfGRH
import FareyGoldbach.SharpRankin
import FareyGoldbach.AveragedRemainder

/-!
# Module F3: Double-Averaged Binary Goldbach Across All Moduli `1 ≤ r ≤ X`

This module proves **Theorem (D)** of Route A with zero `sorry` and zero custom axioms:
assuming `DirichletGRH` (via `SmoothedTwistEstimate`), there exists an absolute constant `C > 0`
such that for **EVERY** `X ≥ 2` and **EVERY** positive integer modulus `1 ≤ r ≤ X`,
```
(1 / φ(r)²) * ∑_{b₁, b₂ ∈ U_r} E_r(X; b₁, b₂)
  ≤ C * min (X / r) ((φ(r) / r)² * √(X / r) * log³(2 * X)).
```
In particular, density-one representation holds uniformly for all `r ≤ X / log(2X)^(6 + ε)`
(with no subexponential cutoff restriction, thanks to `singularTrunc_re_ge_quarter` in Module F1).
-/

open Real Complex Set
open Filter
open scoped BigOperators Classical Topology

namespace FareyGoldbach

section DoubleAverageDefs

/-- Normalized double average `E_{b₁, b₂ ∈ U_r} E_r(X; b₁, b₂)` over all coprime residue pairs. -/
noncomputable def doubleAvgExceptions (X r : ℕ) (hr : 0 < r) : ℝ :=
  (1 / ((r.totient : ℝ) ^ 2)) *
    ∑ b₁ ∈ (coprimeClasses r).attach, ∑ b₂ ∈ (coprimeClasses r).attach,
      ((exceptions ⟨r, hr, b₁.1, b₂.1,
        (mem_coprimeClasses.mp b₁.2).1, (mem_coprimeClasses.mp b₂.2).1,
        (mem_coprimeClasses.mp b₁.2).2, (mem_coprimeClasses.mp b₂.2).2⟩ X).card : ℝ)

/-- Normalized double average of dyadic exceptions in `(Y/2, Y]` over all coprime residue pairs. -/
noncomputable def doubleAvgDyadicExceptions (Y r : ℕ) (hr : 0 < r) : ℝ :=
  (1 / ((r.totient : ℝ) ^ 2)) *
    ∑ b₁ ∈ (coprimeClasses r).attach, ∑ b₂ ∈ (coprimeClasses r).attach,
      ((dyadicExceptions ⟨r, hr, b₁.1, b₂.1,
        (mem_coprimeClasses.mp b₁.2).1, (mem_coprimeClasses.mp b₂.2).1,
        (mem_coprimeClasses.mp b₁.2).2, (mem_coprimeClasses.mp b₂.2).2⟩ Y).card : ℝ)

end DoubleAverageDefs

section MainTermAndAvgL2

/-- **All-cutoff Route-A model convolution lower bound `(9)`:**
Using `Q₀ = Q = routeAQ Y r` and Module F1's `singularTrunc_re_ge_quarter` (no Rankin tail!),
for EVERY `0 < r`, `2 ^ 26 ≤ Y / r`, `b₁, b₂ < r`, and even `n = r * k + b₁ + b₂ ∈ (Y / 2, Y]`:
`(∫_0^1 M₁ α * M₂ α * e(-k * α)).re ≥ (1 / 262144) * (r / φ(r))² * (Y / r)`. -/
theorem modelSum_routeA_conv_re_lower {r b₁ b₂ Y k : ℕ} (hr : 0 < r) (hb₁ : b₁ < r) (hb₂ : b₂ < r)
    (hn_lo : Y / 2 < r * k + b₁ + b₂) (hn_hi : r * k + b₁ + b₂ ≤ Y)
    (hn_even : Even (r * k + b₁ + b₂)) (hH : 2 ^ 26 ≤ Y / r) :
    ((1 : ℝ) / 262144) * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * ((Y : ℝ) / (r : ℝ)) ≤
      (∫ α in (0 : ℝ)..1,
        modelSum r b₁ Y (routeAQ Y r) (routeAQ Y r) α *
        modelSum r b₂ Y (routeAQ Y r) (routeAQ Y r) α *
        e (-((k : ℝ) * α))).re := by
  set Q := routeAQ Y r
  set n := r * k + b₁ + b₂
  obtain ⟨hQ_ge2, _, hQ_hi, _⟩ := routeAQ_bounds hr hH
  have hQ_pos : 0 < Q := by omega
  have h16rY : 16 * r ≤ Y := by
    calc 16 * r = r * 16 := mul_comm _ _
      _ ≤ r * (Y / r) := Nat.mul_le_mul_left r (by omega)
      _ ≤ Y := Nat.mul_div_le Y r
  have hk_le : k ≤ Y / r := by
    rw [Nat.le_div_iff_mul_le hr]
    calc k * r = r * k := mul_comm _ _
      _ ≤ Y := by omega
  have hn_pos : 0 < n := by omega
  let Cset := (centers Q).filter (fun c => c.q ≤ Q)
  -- Step 1: Decompose integral over `Cset` using disjointness of Voronoi cells.
  have hpt : ∀ α : ℝ,
      modelSum r b₁ Y Q Q α * modelSum r b₂ Y Q Q α * e (-((k : ℝ) * α)) =
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
        _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by positivity)
    · rw [Set.indicator_of_notMem hx, norm_zero]; positivity
  rw [intervalIntegral_finset_sum hint_c]
  -- Step 2: Compare cell integrals with completed `[-1/2, 1/2]` integrals.
  let fullConv : ℂ :=
    ∫ β in (-(1 / 2) : ℝ)..(1 / 2),
      smoothedKernel r b₁ Y β * smoothedKernel r b₂ Y β * e (-((k : ℝ) * β))
  let completed : ℂ :=
    ∑ c ∈ Cset, modelCoeff r b₁ c * modelCoeff r b₂ c * e (-((k : ℝ) * c.val)) * fullConv
  have hcomp_err :
      ‖(∑ c ∈ Cset, ∫ α in (0 : ℝ)..1,
          (voronoiCell Q c).indicator
            (fun x => modelCoeff r b₁ c * modelCoeff r b₂ c *
              smoothedKernel r b₁ Y (wrap (x - c.val)) *
              smoothedKernel r b₂ Y (wrap (x - c.val)) * e (-((k : ℝ) * x))) α) - completed‖ ≤
      48 * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * (Q : ℝ) * (Q : ℝ) := by
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
        intro β; dsimp [f_cell]
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
        intro β; rw [Real.norm_eq_abs]; dsimp [maj]
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
            dsimp [f_cell, f_full]; rw [Set.indicator_of_mem hmem]
            have hs : c.val + β - c.val = β := by ring
            have he : e (-((k : ℝ) * (c.val + β))) = e (-((k : ℝ) * c.val)) * e (-((k : ℝ) * β)) := by
              rw [← e_add]; congr 1; ring
            rw [hs, smoothedKernel_wrap, smoothedKernel_wrap, he]; ring
          rw [hsub0, norm_zero]; dsimp [maj]; rw [ite_eq_left hlt, mul_zero]
        · have hβ0 : β ≠ 0 := by
            intro hz; subst hz; rw [abs_zero] at hlt
            have hδ_pos : 0 < δ := by
              dsimp [δ]; have : (0 : ℝ) < c.q := Nat.cast_pos.mpr c.q_pos; positivity
            exact hlt hδ_pos
          have hpt_le : ‖f_cell β - f_full β‖ ≤ ‖f_full β‖ := by
            by_cases hmem : c.val + β ∈ voronoiCell Q c
            · have hsub0 : f_cell β - f_full β = 0 := by
                dsimp [f_cell, f_full]; rw [Set.indicator_of_mem hmem]
                have hs : c.val + β - c.val = β := by ring
                have he : e (-((k : ℝ) * (c.val + β))) = e (-((k : ℝ) * c.val)) * e (-((k : ℝ) * β)) := by
                  rw [← e_add]; congr 1; ring
                rw [hs, smoothedKernel_wrap, smoothedKernel_wrap, he]; ring
              rw [hsub0, norm_zero]; exact norm_nonneg _
            · dsimp [f_cell]; rw [Set.indicator_of_notMem hmem, zero_sub, norm_neg]
          dsimp [maj]; rw [ite_eq_right hlt]
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
    calc ‖∑ c ∈ Cset, ((∫ α in (0 : ℝ)..1,
            (voronoiCell Q c).indicator
              (fun x => modelCoeff r b₁ c * modelCoeff r b₂ c *
                smoothedKernel r b₁ Y (wrap (x - c.val)) *
                smoothedKernel r b₂ Y (wrap (x - c.val)) * e (-((k : ℝ) * x))) α) -
            modelCoeff r b₁ c * modelCoeff r b₂ c * e (-((k : ℝ) * c.val)) * fullConv)‖
        ≤ ∑ c ∈ Cset, ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ * (16 * (c.q : ℝ) * (Q : ℝ)) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum hcell_err)
      _ ≤ 16 * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * (Q : ℝ) *
            ∑ q ∈ (Finset.Icc 1 Q).filter Squarefree, ((q : ℝ) / (q.totient : ℝ)) := by
          let Qsf := (Finset.Icc 1 Q).filter Squarefree
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
            have hsub : (Cgood.filter (fun c => c.q = q)).image (fun c => c.a) ⊆ coprimeClasses q := by
              intro a ha
              obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ha
              have hcq : c.q = q := (Finset.mem_filter.mp hc).2
              exact mem_coprimeClasses.mpr ⟨hcq ▸ c.a_lt, hcq ▸ c.coprime⟩
            have hinj : Set.InjOn (fun c : RatCenter => c.a) (Cgood.filter (fun c => c.q = q) : Set RatCenter) := by
              intro c₁ h1 c₂ h2 hEq
              exact RatCenter.ext hEq ((Finset.mem_filter.mp h1).2.trans (Finset.mem_filter.mp h2).2.symm)
            rw [← Finset.card_image_of_injOn hinj]
            exact (Finset.card_le_card hsub).trans (le_of_eq (card_coprimeClasses q))
          have hterm_le : ∀ c ∈ Cgood.filter (fun c => c.q = q),
              ‖modelCoeff r b₁ c‖ * ‖modelCoeff r b₂ c‖ * (16 * (c.q : ℝ) * (Q : ℝ)) ≤
                (((r : ℝ) / (r.totient : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2) * (16 * (q : ℝ) * (Q : ℝ)) := by
            intro c hc
            have hcq : c.q = q := (Finset.mem_filter.mp hc).2
            rw [hcq]
            have hm_le : ∀ b', ‖modelCoeff r b' c‖ ≤ ((r : ℝ) / (r.totient : ℝ)) / (q.totient : ℝ) := fun b' => by
              unfold modelCoeff; rw [hcq]
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
      _ ≤ 16 * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * (Q : ℝ) * (3 * (Q : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_sqfree_div_totient_le Q) (by positivity)
      _ = 48 * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * (Q : ℝ) * (Q : ℝ) := by ring
  -- Step 3: Evaluate `completed` as `(r / φ(r))² * singularTrunc r n Q * quarticConv`.
  have hcomp_eq : completed =
      ((((r : ℝ) / (r.totient : ℝ)) ^ 2 : ℝ) : ℂ) * singularTrunc r n Q *
      ((∑ j₁ ∈ Finset.range (k + 1),
        quarticBump (((r * j₁ + b₁ : ℕ) : ℝ) / (Y : ℝ)) *
          quarticBump (((r * (k - j₁) + b₂ : ℕ) : ℝ) / (Y : ℝ)) : ℝ) : ℂ) := by
    dsimp [completed, fullConv]
    rw [integral_smoothedKernel_mul_e hk_le, ← Finset.sum_mul]
    congr 1
    unfold singularTrunc
    rw [Finset.mul_sum]
    let Qcop := (Finset.Icc 1 Q).filter (fun q => Nat.Coprime q r)
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
    have hq_le_Q : q ≤ Q := hq_Icc.2
    have hq_cop : Nat.Coprime q r := (Finset.mem_filter.mp hq).2
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
          ⟨Finset.mem_filter.mpr ⟨mem_centers_iff.mpr hq_le_Q, hq_le_Q⟩, hq⟩, rfl⟩
      · intro c hc
        have hcq : c.q = q := (Finset.mem_filter.mp hc).2
        unfold modelCoeff RatCenter.val
        rw [hcq, ite_eq_left hq_cop, ite_eq_left hq_cop]
        push_cast; ring
    rw [hbij, sum_modelCoeff_mul_e_eq_ramanujan hq_pos hq_cop]
    ring
  -- Step 4: Use Module F1's ALL-CUTOFF positivity `singularTrunc_re_ge_quarter`!
  have hmain_re : ((1 : ℝ) / 131072) * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * ((Y : ℝ) / (r : ℝ)) ≤
      completed.re := by
    rw [hcomp_eq]
    have hre : (((((r : ℝ) / (r.totient : ℝ)) ^ 2 : ℝ) : ℂ) * singularTrunc r n Q *
        ((∑ j₁ ∈ Finset.range (k + 1),
          quarticBump (((r * j₁ + b₁ : ℕ) : ℝ) / (Y : ℝ)) *
            quarticBump (((r * (k - j₁) + b₂ : ℕ) : ℝ) / (Y : ℝ)) : ℝ) : ℂ)).re =
        ((r : ℝ) / (r.totient : ℝ)) ^ 2 * (singularTrunc r n Q).re *
          (∑ j₁ ∈ Finset.range (k + 1),
            quarticBump (((r * j₁ + b₁ : ℕ) : ℝ) / (Y : ℝ)) *
              quarticBump (((r * (k - j₁) + b₂ : ℕ) : ℝ) / (Y : ℝ))) := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_mul]
    rw [hre]
    have hsing := singularTrunc_re_ge_quarter hr hn_pos hn_even (by omega : 1 ≤ Q)
    have hconv := quarticBump_conv_lower hr hb₁ hb₂ h16rY hn_lo hn_hi
    have hmul : (1 / 4 : ℝ) * (((1 : ℝ) / 32768) * ((Y : ℝ) / (r : ℝ))) ≤
        (singularTrunc r n Q).re *
          (∑ j₁ ∈ Finset.range (k + 1),
            quarticBump (((r * j₁ + b₁ : ℕ) : ℝ) / (Y : ℝ)) *
              quarticBump (((r * (k - j₁) + b₂ : ℕ) : ℝ) / (Y : ℝ))) :=
      mul_le_mul hsing hconv (by positivity) (by linarith)
    have hmul2 := mul_le_mul_of_nonneg_left hmul (sq_nonneg ((r : ℝ) / (r.totient : ℝ)))
    linarith
  -- Step 5: Completion error `48 * κ² * Q² ≤ (1 / 262144) * κ² * (Y / r)` since `Q ≤ √(Y / r) / 2^12`!
  have herr_small : 48 * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * (Q : ℝ) * (Q : ℝ) ≤
      ((1 : ℝ) / 262144) * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * ((Y : ℝ) / (r : ℝ)) := by
    have hQ2 : (Q : ℝ) * (Q : ℝ) ≤ ((Y : ℝ) / (r : ℝ)) / ((2 : ℝ) ^ 24) := by
      calc (Q : ℝ) * (Q : ℝ) = (Q : ℝ) ^ 2 := (sq _).symm
        _ ≤ (1 / (2 : ℝ) ^ 12 * Real.sqrt ((Y : ℝ) / (r : ℝ))) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg Q) hQ_hi 2
        _ = ((Y : ℝ) / (r : ℝ)) / ((2 : ℝ) ^ 24) := by
            rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
    have hcoeff : (48 : ℝ) / ((2 : ℝ) ^ 24) ≤ (1 : ℝ) / 262144 := by norm_num
    calc 48 * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * (Q : ℝ) * (Q : ℝ)
        = 48 * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * ((Q : ℝ) * (Q : ℝ)) := by ring
      _ ≤ 48 * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * (((Y : ℝ) / (r : ℝ)) / ((2 : ℝ) ^ 24)) :=
          mul_le_mul_of_nonneg_left hQ2 (by positivity)
      _ = ((48 : ℝ) / ((2 : ℝ) ^ 24)) * (((r : ℝ) / (r.totient : ℝ)) ^ 2 * ((Y : ℝ) / (r : ℝ))) := by ring
      _ ≤ ((1 : ℝ) / 262144) * (((r : ℝ) / (r.totient : ℝ)) ^ 2 * ((Y : ℝ) / (r : ℝ))) :=
          mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = ((1 : ℝ) / 262144) * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * ((Y : ℝ) / (r : ℝ)) := by ring
  have hre_diff : |(∑ c ∈ Cset, ∫ α in (0 : ℝ)..1,
      (voronoiCell Q c).indicator
        (fun x => modelCoeff r b₁ c * modelCoeff r b₂ c *
          smoothedKernel r b₁ Y (wrap (x - c.val)) *
          smoothedKernel r b₂ Y (wrap (x - c.val)) * e (-((k : ℝ) * x))) α).re - completed.re| ≤
      48 * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * (Q : ℝ) * (Q : ℝ) := by
    have h1 := Complex.abs_re_le_norm ((∑ c ∈ Cset, ∫ α in (0 : ℝ)..1,
      (voronoiCell Q c).indicator
        (fun x => modelCoeff r b₁ c * modelCoeff r b₂ c *
          smoothedKernel r b₁ Y (wrap (x - c.val)) *
          smoothedKernel r b₂ Y (wrap (x - c.val)) * e (-((k : ℝ) * x))) α) - completed)
    rw [Complex.sub_re] at h1
    exact h1.trans hcomp_err
  have hre_lo := (abs_le.mp hre_diff).1
  linarith

/-- **Unconditional averaged L² prime-sum bound `(10a)`:**
For ALL `0 < r ≤ Y` and `2 ≤ Y`:
`(1 / φ(r)) * ∑_{b ∈ U_r} ∫_0^1 ‖S_b(α)‖² ≤ 2 * (r / φ(r)) * (Y / r) * log(2 * Y)`. -/
theorem avg_smoothedPrimeSum_l2_le {r Y : ℕ} (hr : 0 < r) (_hrY : r ≤ Y) (hY : 2 ≤ Y) :
    (1 / (r.totient : ℝ)) *
        ∑ b ∈ coprimeClasses r, ∫ α in (0 : ℝ)..1, ‖smoothedPrimeSum r b Y α‖ ^ 2 ≤
      2 * ((r : ℝ) / (r.totient : ℝ)) * ((Y : ℝ) / (r : ℝ)) * Real.log (2 * (Y : ℝ)) := by
  have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hY_pos : (0 : ℝ) < Y := Nat.cast_pos.mpr (by omega)
  have hφr_pos : (0 : ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hlog_nn : 0 ≤ Real.log (2 * (Y : ℝ)) := Real.log_nonneg (by
    have : (2 : ℝ) ≤ Y := Nat.cast_le.mpr hY; linarith)
  -- Per-class Parseval bound: `∫_0^1 ‖S_b‖² ≤ log(2Y) * ∑_{n ∈ Icc 1 Y, n % r = b} primeWeight n`.
  have hper : ∀ b ∈ coprimeClasses r,
      (∫ α in (0 : ℝ)..1, ‖smoothedPrimeSum r b Y α‖ ^ 2) ≤
        Real.log (2 * (Y : ℝ)) *
          ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => n % r = b), primeWeight n := by
    intro b hb
    have hb_lt : b < r := (mem_coprimeClasses.mp hb).1
    have hL2 : (∫ α in (0 : ℝ)..1, ‖smoothedPrimeSum r b Y α‖ ^ 2) =
        ∑ j ∈ Finset.range (Y / r + 1),
          (quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * primeWeight (r * j + b)) ^ 2 := by
      unfold smoothedPrimeSum
      rw [integral_norm_sq_trigPoly]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hL2, Finset.mul_sum]
    -- First drop terms outside `1 ≤ r * j + b ≤ Y`, then reindex to `(Icc 1 Y).filter (· % r = b)`.
    let J0 := (Finset.range (Y / r + 1)).filter (fun j => 1 ≤ r * j + b ∧ r * j + b ≤ Y)
    have htrim : ∑ j ∈ Finset.range (Y / r + 1),
          (quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * primeWeight (r * j + b)) ^ 2 =
        ∑ j ∈ J0, (quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * primeWeight (r * j + b)) ^ 2 := by
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
              have := (div_pos_iff_of_pos_right hY_pos).1 h1; rw [← hcast] at this; exact_mod_cast this
            have h2' : r * j + b < Y := by
              have := (div_lt_one hY_pos).1 h2; rw [← hcast] at this; exact_mod_cast this
            exact h ⟨by omega, by omega⟩
          simp [hnot]
        simp [hw0]
    have hstep1 : ∑ j ∈ J0, (quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * primeWeight (r * j + b)) ^ 2 ≤
        ∑ j ∈ J0, Real.log (2 * (Y : ℝ)) * primeWeight (r * j + b) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hleY : r * j + b ≤ Y := (Finset.mem_filter.mp hj).2.2
      have hw_nn : 0 ≤ quarticBump ((r * j + b : ℝ) / (Y : ℝ)) := quarticBump_nonneg _
      have hw_le : quarticBump ((r * j + b : ℝ) / (Y : ℝ)) ≤ 1 := quarticBump_le_one _
      have hp_nn : 0 ≤ primeWeight (r * j + b) := primeWeight_nonneg _
      have hp_le : primeWeight (r * j + b) ≤ Real.log (2 * (Y : ℝ)) :=
        (primeWeight_le_log hleY).trans (Real.log_le_log hY_pos (by linarith))
      rw [sq]
      calc (quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * primeWeight (r * j + b)) *
            (quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * primeWeight (r * j + b))
          ≤ (1 * Real.log (2 * (Y : ℝ))) * (1 * primeWeight (r * j + b)) :=
            mul_le_mul (mul_le_mul hw_le hp_le hp_nn zero_le_one)
              (mul_le_mul_of_nonneg_right hw_le hp_nn) (mul_nonneg hw_nn hp_nn) (by positivity)
        _ = Real.log (2 * (Y : ℝ)) * primeWeight (r * j + b) := by ring
    have hreidx : ∑ j ∈ J0, Real.log (2 * (Y : ℝ)) * primeWeight (r * j + b) =
        ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => n % r = b), Real.log (2 * (Y : ℝ)) * primeWeight n := by
      refine Finset.sum_bij (fun j _ => r * j + b) ?_ ?_ ?_ ?_
      · intro j hj
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (Finset.mem_filter.mp hj).2, ?_⟩
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hb_lt]
      · intro j₁ _ j₂ _ hEq; exact Nat.eq_of_mul_eq_mul_left hr (by omega)
      · intro n hn
        have hIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
        have hmod := (Finset.mem_filter.mp hn).2
        have hnj : r * (n / r) + b = n := by have := Nat.div_add_mod n r; omega
        refine ⟨n / r, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
          (Nat.lt_succ_of_le (Nat.div_le_div_right hIcc.2)), hnj.symm ▸ hIcc.1, hnj.symm ▸ hIcc.2⟩, hnj⟩
      · intro j _; rfl
    rw [htrim, ← hreidx]; exact hstep1
  -- Disjoint union over `b ∈ coprimeClasses r` is contained in `Finset.Icc 1 Y`.
  have hdisj : Set.PairwiseDisjoint (coprimeClasses r : Set ℕ)
      (fun b => (Finset.Icc 1 Y).filter (fun n => n % r = b)) := by
    intro b₁ _ b₂ _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro n hn₁ hn₂
    exact hne ((Finset.mem_filter.mp hn₁).2.symm.trans (Finset.mem_filter.mp hn₂).2)
  have hsub : (coprimeClasses r).biUnion (fun b => (Finset.Icc 1 Y).filter (fun n => n % r = b)) ⊆
      Finset.Icc 1 Y := by
    intro n hn
    obtain ⟨_, _, h2⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp h2).1
  have hsum_pw : ∑ b ∈ coprimeClasses r,
        ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => n % r = b), primeWeight n ≤ 2 * (Y : ℝ) := by
    rw [← Finset.sum_biUnion hdisj]
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => primeWeight_nonneg _).trans
      (sum_primeWeight_le_two_mul Y)
  calc (1 / (r.totient : ℝ)) *
          ∑ b ∈ coprimeClasses r, ∫ α in (0 : ℝ)..1, ‖smoothedPrimeSum r b Y α‖ ^ 2
      ≤ (1 / (r.totient : ℝ)) *
          ∑ b ∈ coprimeClasses r, Real.log (2 * (Y : ℝ)) *
            ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => n % r = b), primeWeight n :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper) (by positivity)
    _ = (1 / (r.totient : ℝ)) * Real.log (2 * (Y : ℝ)) *
          ∑ b ∈ coprimeClasses r, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => n % r = b), primeWeight n := by
        rw [← Finset.mul_sum]; ring
    _ ≤ (1 / (r.totient : ℝ)) * Real.log (2 * (Y : ℝ)) * (2 * (Y : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum_pw (by positivity)
    _ = 2 * ((r : ℝ) / (r.totient : ℝ)) * ((Y : ℝ) / (r : ℝ)) * Real.log (2 * (Y : ℝ)) := by
        field_simp [hr_pos.ne', hφr_pos.ne']

end MainTermAndAvgL2

section DyadicAndGlobalDoubleAverage

/-- Bessel's inequality on the dyadic exceptions for a fixed pair of reduced residue classes. -/
theorem routeA_dyadic_pair_bessel {r Y : ℕ} (hr : 0 < r) (hH26 : 2^26 ≤ Y / r)
    (b₁ b₂ : {b // b ∈ coprimeClasses r}) :
    let Q := routeAQ Y r
    let thresh : ℝ := (1 / 262144) * ((r : ℝ) / (r.totient : ℝ))^2 * ((Y : ℝ) / (r : ℝ))
    ((dyadicExceptions ⟨r, hr, b₁.1, b₂.1,
      (mem_coprimeClasses.mp b₁.2).1, (mem_coprimeClasses.mp b₂.2).1,
      (mem_coprimeClasses.mp b₁.2).2, (mem_coprimeClasses.mp b₂.2).2⟩ Y).card : ℝ) * thresh ^ 2 ≤
    ∫ α in (0 : ℝ)..1,
      ‖smoothedPrimeSum r b₁.1 Y α * smoothedPrimeSum r b₂.1 Y α -
        modelSum r b₁.1 Y Q Q α * modelSum r b₂.1 Y Q Q α‖ ^ 2 := by
  dsimp only
  set Q := routeAQ Y r
  have h4rY : 4 * r ≤ Y := by
    calc 4 * r = r * 4 := mul_comm _ _
      _ ≤ r * (Y / r) := Nat.mul_le_mul_left r (by omega)
      _ ≤ Y := Nat.mul_div_le Y r
  set thresh : ℝ := (1 / 262144) * ((r : ℝ) / (r.totient : ℝ))^2 * ((Y : ℝ) / (r : ℝ))
  have hrY : r ≤ Y := by omega
  have hthresh_pos : 0 < thresh := by
    have hr' : (0 : ℝ) < r := Nat.cast_pos.mpr hr
    have hY' : (0 : ℝ) < Y := Nat.cast_pos.mpr (hr.trans_le hrY)
    have ht' : (0 : ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
    dsimp [thresh]
    positivity
  let P : Progressions := ⟨r, hr, b₁.1, b₂.1,
    (mem_coprimeClasses.mp b₁.2).1, (mem_coprimeClasses.mp b₂.2).1,
    (mem_coprimeClasses.mp b₁.2).2, (mem_coprimeClasses.mp b₂.2).2⟩
  let badK : Finset ℕ := (dyadicExceptions P Y).image (fun n => (n - (P.b₁ + P.b₂)) / r)
  have hcard_eq : (dyadicExceptions P Y).card = badK.card := by
    symm
    refine Finset.card_image_of_injOn fun n₁ h1 n₂ h2 hEq => ?_
    have hrec : ∀ n ∈ dyadicExceptions P Y, r * ((n - (P.b₁ + P.b₂)) / r) + P.b₁ + P.b₂ = n := by
      intro n hn
      have hlo : Y / 2 < n := (Finset.mem_filter.mp hn).2
      have hmod : n % r = (P.b₁ + P.b₂) % r := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2.2.1
      have hge_b : P.b₁ + P.b₂ ≤ n := by have h1 : P.b₁ < r := P.b₁_lt; have h2 : P.b₂ < r := P.b₂_lt; omega
      have hdvd : r ∣ n - (P.b₁ + P.b₂) := (Nat.modEq_iff_dvd' hge_b).1 hmod.symm
      have hmul := Nat.mul_div_cancel' hdvd; omega
    rw [← hrec n₁ h1, ← hrec n₂ h2, hEq]
  have hbadK_sub : badK ⊆ Finset.range (Y / r + 1) := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    have hnY : n ≤ Y := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right ((Nat.sub_le n _).trans hnY)))
  let F : ℝ → ℂ := fun α =>
    smoothedPrimeSum r b₁.1 Y α * smoothedPrimeSum r b₂.1 Y α -
      modelSum r b₁.1 Y Q Q α * modelSum r b₂.1 Y Q Q α
  let err : ℕ → ℂ := fun k => ∫ α in (0 : ℝ)..1, F α * e (-((k : ℝ) * α))
  have hbad_thresh : ∀ k ∈ badK, thresh ≤ ‖err k‖ := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    have hlo : Y / 2 < n := (Finset.mem_filter.mp hn).2
    have hmem_exc := Finset.mem_filter.mp (Finset.mem_filter.mp hn).1
    have hn_hi : n ≤ Y := (Finset.mem_Icc.mp hmem_exc.1).2
    have hn_even : Even n := hmem_exc.2.1
    have hmod : n % r = (P.b₁ + P.b₂) % r := hmem_exc.2.2.1
    have hexc0 : (primeRepresentations P n).card = 0 := hmem_exc.2.2.2
    have hge_b : P.b₁ + P.b₂ ≤ n := by have h1 : P.b₁ < r := P.b₁_lt; have h2 : P.b₂ < r := P.b₂_lt; omega
    have hdvd : r ∣ n - (P.b₁ + P.b₂) := (Nat.modEq_iff_dvd' hge_b).1 hmod.symm
    set k' := (n - (P.b₁ + P.b₂)) / r
    have hnk : r * k' + P.b₁ + P.b₂ = n := by
      have hmul : r * k' = n - (P.b₁ + P.b₂) := Nat.mul_div_cancel' hdvd; omega
    have hk'_le : k' ≤ Y / r := Nat.div_le_div_right ((Nat.sub_le n _).trans hn_hi)
    have hS_int : IntervalIntegrable
        (fun α => smoothedPrimeSum r b₁.1 Y α * smoothedPrimeSum r b₂.1 Y α * e (-((k' : ℝ) * α)))
        MeasureTheory.volume 0 1 := by
      have hcont : Continuous (fun α => smoothedPrimeSum r b₁.1 Y α * smoothedPrimeSum r b₂.1 Y α * e (-((k' : ℝ) * α))) := by
        refine ((continuous_smoothedPrimeSum r b₁.1 Y).mul (continuous_smoothedPrimeSum r b₂.1 Y)).mul ?_
        have h : (fun α : ℝ => e (-((k' : ℝ) * α))) = fun α : ℝ => e (-(k' : ℝ) * α) := by funext α; ring_nf
        rw [h]; exact continuous_e_mul (-(k' : ℝ))
      exact hcont.intervalIntegrable 0 1
    have hM_int : IntervalIntegrable
        (fun α => modelSum r b₁.1 Y Q Q α * modelSum r b₂.1 Y Q Q α * e (-((k' : ℝ) * α)))
        MeasureTheory.volume 0 1 := by
      obtain ⟨B1, hB1⟩ := modelSum_norm_bounded r b₁.1 Y Q Q
      obtain ⟨B2, hB2⟩ := modelSum_norm_bounded r b₂.1 Y Q Q
      have hB1_nn : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
      have he_meas : Measurable (fun α : ℝ => e (-((k' : ℝ) * α))) := by
        have h : (fun α : ℝ => e (-((k' : ℝ) * α))) = fun α : ℝ => e (-(k' : ℝ) * α) := by funext α; ring_nf
        rw [h]; exact (continuous_e_mul (-(k' : ℝ))).measurable
      refine intervalIntegrable_of_measurable_bounded (B := B1 * B2)
        (((modelSum_measurable r b₁.1 Y Q Q).mul (modelSum_measurable r b₂.1 Y Q Q)).mul he_meas) fun α => ?_
      rw [norm_mul, norm_mul, norm_e, mul_one]
      exact mul_le_mul (hB1 α) (hB2 α) (norm_nonneg _) hB1_nn
    have herr_eq : err k' = -(∫ α in (0 : ℝ)..1,
        modelSum r b₁.1 Y Q Q α * modelSum r b₂.1 Y Q Q α * e (-((k' : ℝ) * α))) := by
      dsimp [err, F]
      have hfun : (fun α => (smoothedPrimeSum r b₁.1 Y α * smoothedPrimeSum r b₂.1 Y α -
            modelSum r b₁.1 Y Q Q α * modelSum r b₂.1 Y Q Q α) * e (-((k' : ℝ) * α))) =
          fun α => smoothedPrimeSum r b₁.1 Y α * smoothedPrimeSum r b₂.1 Y α * e (-((k' : ℝ) * α)) -
            modelSum r b₁.1 Y Q Q α * modelSum r b₂.1 Y Q Q α * e (-((k' : ℝ) * α)) := by
        funext α; ring
      rw [hfun, intervalIntegral.integral_sub hS_int hM_int,
          primeConvolution_eq_zero_of_exception P hk'_le (hnk.symm ▸ hexc0), zero_sub]
    rw [herr_eq, norm_neg]
    exact (modelSum_routeA_conv_re_lower hr P.b₁_lt P.b₂_lt (hnk.symm ▸ hlo) (hnk.symm ▸ hn_hi)
      (hnk.symm ▸ hn_even) hH26).trans (Complex.re_le_norm _)
  have hF_meas : Measurable F :=
    ((continuous_smoothedPrimeSum r b₁.1 Y).measurable.mul (continuous_smoothedPrimeSum r b₂.1 Y).measurable).sub
      ((modelSum_measurable r b₁.1 Y Q Q).mul (modelSum_measurable r b₂.1 Y Q Q))
  have hF_bound : ∃ BF : ℝ, ∀ α, ‖F α‖ ≤ BF := by
    obtain ⟨B1, hB1⟩ := modelSum_norm_bounded r b₁.1 Y Q Q
    obtain ⟨B2, hB2⟩ := modelSum_norm_bounded r b₂.1 Y Q Q
    have hS_bd : ∀ b, ∃ BS : ℝ, ∀ α, ‖smoothedPrimeSum r b Y α‖ ≤ BS := fun b =>
      ⟨∑ j ∈ Finset.range (Y / r + 1), |quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * primeWeight (r * j + b)|,
        fun α => by
          unfold smoothedPrimeSum
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs]⟩
    obtain ⟨BS1, hBS1⟩ := hS_bd b₁.1
    obtain ⟨BS2, hBS2⟩ := hS_bd b₂.1
    refine ⟨BS1 * BS2 + B1 * B2, fun α => ?_⟩
    have hBS1_nn : 0 ≤ BS1 := (norm_nonneg _).trans (hBS1 0)
    have hB1_nn : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
    calc ‖F α‖ ≤ ‖smoothedPrimeSum r b₁.1 Y α * smoothedPrimeSum r b₂.1 Y α‖ +
            ‖modelSum r b₁.1 Y Q Q α * modelSum r b₂.1 Y Q Q α‖ := norm_sub_le _ _
      _ = ‖smoothedPrimeSum r b₁.1 Y α‖ * ‖smoothedPrimeSum r b₂.1 Y α‖ +
            ‖modelSum r b₁.1 Y Q Q α‖ * ‖modelSum r b₂.1 Y Q Q α‖ := by rw [norm_mul, norm_mul]
      _ ≤ BS1 * BS2 + B1 * B2 := add_le_add
          (mul_le_mul (hBS1 α) (hBS2 α) (norm_nonneg _) hBS1_nn)
          (mul_le_mul (hB1 α) (hB2 α) (norm_nonneg _) hB1_nn)
  obtain ⟨BF, hBF⟩ := hF_bound
  rw [hcard_eq]
  exact (card_mul_sq_le_sum hbadK_sub err hthresh_pos.le hbad_thresh).trans
    (bessel_intervalIntegral hF_meas hBF (Y / r + 1))

/-- **Dyadic Double-Average Theorem (Main Regime `2 ^ 72 ≤ Y / r`):**
Under `SmoothedTwistEstimate` with constant `C > 0`, for ALL `0 < r` and `2 ^ 72 ≤ Y / r`:
`doubleAvgDyadicExceptions Y r hr ≤ C_dyad * (φ(r)/r)² * √(Y/r) * log³(2Y)`. -/
lemma dyadic_double_average_large {C : ℝ} (hC : 0 < C)
    (hTw : ∀ (Y d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (t : ℝ),
      2 ≤ Y → |t| ≤ 1 / 2 →
        ‖smoothedTiltedRemainder χ Y t‖ ≤
          C * Real.sqrt ((Y : ℝ) * (1 + |t| * Y)) * Real.log (2 * (d : ℝ) * Y))
    {r Y : ℕ} (hr : 0 < r) (hH : 2 ^ 72 ≤ Y / r) :
    doubleAvgDyadicExceptions Y r hr ≤
      (76 * (262144 : ℝ) ^ 2 * (3 * (3 * C + 1) ^ 2 * (2 : ℝ) ^ 15 + 3 + 3 * (2 : ℝ) ^ 39)) *
        ((r.totient : ℝ) / (r : ℝ)) ^ 2 * Real.sqrt ((Y : ℝ) / (r : ℝ)) *
        (Real.log (2 * (Y : ℝ))) ^ 3 := by
  set Q := routeAQ Y r
  have hH26 : 2 ^ 26 ≤ Y / r := le_trans (by norm_num : 2 ^ 26 ≤ 2 ^ 72) hH
  have hrY : r ≤ Y := by
    calc r = r * 1 := (mul_one r).symm
      _ ≤ r * (Y / r) := Nat.mul_le_mul_left r (by omega)
      _ ≤ Y := Nat.mul_div_le Y r
  have hY72 : 2 ^ 72 ≤ Y := by
    calc 2 ^ 72 = 1 * 2 ^ 72 := (one_mul _).symm
      _ ≤ r * (Y / r) := Nat.mul_le_mul hr hH
      _ ≤ Y := Nat.mul_div_le Y r
  have hY2 : 2 ≤ Y := le_trans (by norm_num : 2 ≤ 2 ^ 72) hY72
  obtain ⟨_, _, _, hQ_le_Y⟩ := routeAQ_bounds hr hH26
  have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hφr_pos : (0 : ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  set H : ℝ := (Y : ℝ) / (r : ℝ)
  set L : ℝ := Real.log (2 * (Y : ℝ))
  set κ : ℝ := (r : ℝ) / (r.totient : ℝ)
  set thresh : ℝ := ((1 : ℝ) / 262144) * κ ^ 2 * H
  have hthresh_pos : 0 < thresh := by dsimp [thresh, κ, H]; positivity
  -- Step 1: Per-pair Bessel inequality: `E_dyad(b₁, b₂) * thresh² ≤ ∫_0^1 ‖S₁ S₂ - M₁ M₂‖²`.
  have hpair : ∀ (b₁ b₂ : {b // b ∈ coprimeClasses r}),
      ((dyadicExceptions ⟨r, hr, b₁.1, b₂.1,
        (mem_coprimeClasses.mp b₁.2).1, (mem_coprimeClasses.mp b₂.2).1,
        (mem_coprimeClasses.mp b₁.2).2, (mem_coprimeClasses.mp b₂.2).2⟩ Y).card : ℝ) * thresh ^ 2 ≤
      ∫ α in (0 : ℝ)..1,
        ‖smoothedPrimeSum r b₁.1 Y α * smoothedPrimeSum r b₂.1 Y α -
          modelSum r b₁.1 Y Q Q α * modelSum r b₂.1 Y Q Q α‖ ^ 2 := by
    exact routeA_dyadic_pair_bessel hr hH26
  -- Step 2: Pointwise splitting `S₁ S₂ - M₁ M₂ = R₁ S₂ + M₁ R₂`, then average over `b₁, b₂`!
  let R : ℕ → ℝ → ℂ := fun b α => smoothedPrimeSum r b Y α - modelSum r b Y Q Q α
  have hS_int : ∀ b, IntervalIntegrable (fun α => ‖smoothedPrimeSum r b Y α‖ ^ 2) MeasureTheory.volume 0 1 := fun b =>
    ((continuous_norm.comp (continuous_smoothedPrimeSum r b Y)).pow 2).intervalIntegrable 0 1
  have hM_int : ∀ b, IntervalIntegrable (fun α => ‖modelSum r b Y Q Q α‖ ^ 2) MeasureTheory.volume 0 1 := fun b => by
    obtain ⟨B, hB⟩ := modelSum_norm_bounded r b Y Q Q
    refine intervalIntegrable_of_measurable_bounded (B := B ^ 2)
      ((continuous_norm.measurable.comp (modelSum_measurable r b Y Q Q)).pow_const 2) fun α => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB α) 2
  have hR_meas : ∀ b, Measurable (R b) := fun b =>
    (continuous_smoothedPrimeSum r b Y).measurable.sub (modelSum_measurable r b Y Q Q)
  have hR_bd : ∀ b, ∃ BR : ℝ, ∀ α, ‖R b α‖ ≤ BR := fun b => by
    obtain ⟨BM, hBM⟩ := modelSum_norm_bounded r b Y Q Q
    let BS := ∑ j ∈ Finset.range (Y / r + 1), |quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * primeWeight (r * j + b)|
    refine ⟨BS + BM, fun α => ?_⟩
    have hS : ‖smoothedPrimeSum r b Y α‖ ≤ BS := by
      unfold smoothedPrimeSum
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact (norm_sub_le _ _).trans (add_le_add hS (hBM α))
  have hRS_int : ∀ b₁ b₂,
      IntervalIntegrable (fun α => ‖R b₁ α‖ ^ 2 * ‖smoothedPrimeSum r b₂ Y α‖ ^ 2) MeasureTheory.volume 0 1 := by
    intro b₁ b₂
    obtain ⟨BR, hBR⟩ := hR_bd b₁
    let BS := ∑ j ∈ Finset.range (Y / r + 1), |quarticBump ((r * j + b₂ : ℝ) / (Y : ℝ)) * primeWeight (r * j + b₂)|
    have hBS : ∀ α, ‖smoothedPrimeSum r b₂ Y α‖ ≤ BS := fun α => by
      unfold smoothedPrimeSum
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs]
    refine intervalIntegrable_of_measurable_bounded (B := BR ^ 2 * BS ^ 2)
      (((continuous_norm.measurable.comp (hR_meas b₁)).pow_const 2).mul
        ((continuous_norm.measurable.comp (continuous_smoothedPrimeSum r b₂ Y).measurable).pow_const 2)) fun α => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hBR α) 2)
      (pow_le_pow_left₀ (norm_nonneg _) (hBS α) 2) (sq_nonneg _) (sq_nonneg _)
  have hMR_int : ∀ b₁ b₂,
      IntervalIntegrable (fun α => ‖modelSum r b₁ Y Q Q α‖ ^ 2 * ‖R b₂ α‖ ^ 2) MeasureTheory.volume 0 1 := by
    intro b₁ b₂
    obtain ⟨BM, hBM⟩ := modelSum_norm_bounded r b₁ Y Q Q
    obtain ⟨BR, hBR⟩ := hR_bd b₂
    refine intervalIntegrable_of_measurable_bounded (B := BM ^ 2 * BR ^ 2)
      (((continuous_norm.measurable.comp (modelSum_measurable r b₁ Y Q Q)).pow_const 2).mul
        ((continuous_norm.measurable.comp (hR_meas b₂)).pow_const 2)) fun α => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hBM α) 2)
      (pow_le_pow_left₀ (norm_nonneg _) (hBR α) 2) (sq_nonneg _) (sq_nonneg _)
  have hF2_int : ∀ b₁ b₂,
      IntervalIntegrable (fun α => ‖smoothedPrimeSum r b₁ Y α * smoothedPrimeSum r b₂ Y α -
        modelSum r b₁ Y Q Q α * modelSum r b₂ Y Q Q α‖ ^ 2) MeasureTheory.volume 0 1 := by
    intro b₁ b₂
    obtain ⟨BM1, hBM1⟩ := modelSum_norm_bounded r b₁ Y Q Q
    obtain ⟨BM2, hBM2⟩ := modelSum_norm_bounded r b₂ Y Q Q
    let BS1 := ∑ j ∈ Finset.range (Y / r + 1), |quarticBump ((r * j + b₁ : ℝ) / (Y : ℝ)) * primeWeight (r * j + b₁)|
    let BS2 := ∑ j ∈ Finset.range (Y / r + 1), |quarticBump ((r * j + b₂ : ℝ) / (Y : ℝ)) * primeWeight (r * j + b₂)|
    have hBS : ∀ b α, ‖smoothedPrimeSum r b Y α‖ ≤
        ∑ j ∈ Finset.range (Y / r + 1), |quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * primeWeight (r * j + b)| := fun b α => by
      unfold smoothedPrimeSum
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hmeas : Measurable (fun α => ‖smoothedPrimeSum r b₁ Y α * smoothedPrimeSum r b₂ Y α -
        modelSum r b₁ Y Q Q α * modelSum r b₂ Y Q Q α‖ ^ 2) :=
      (continuous_norm.measurable.comp
        (((continuous_smoothedPrimeSum r b₁ Y).measurable.mul (continuous_smoothedPrimeSum r b₂ Y).measurable).sub
          ((modelSum_measurable r b₁ Y Q Q).mul (modelSum_measurable r b₂ Y Q Q)))).pow_const 2
    refine intervalIntegrable_of_measurable_bounded (B := (BS1 * BS2 + BM1 * BM2) ^ 2) hmeas fun α => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : ‖smoothedPrimeSum r b₁ Y α * smoothedPrimeSum r b₂ Y α -
        modelSum r b₁ Y Q Q α * modelSum r b₂ Y Q Q α‖ ≤ BS1 * BS2 + BM1 * BM2 := by
      have hBS1_nn : 0 ≤ BS1 := (norm_nonneg _).trans (hBS b₁ 0)
      have hBM1_nn : 0 ≤ BM1 := (norm_nonneg _).trans (hBM1 0)
      calc _ ≤ ‖smoothedPrimeSum r b₁ Y α‖ * ‖smoothedPrimeSum r b₂ Y α‖ +
              ‖modelSum r b₁ Y Q Q α‖ * ‖modelSum r b₂ Y Q Q α‖ :=
            (norm_sub_le _ _).trans_eq (by rw [norm_mul, norm_mul])
        _ ≤ BS1 * BS2 + BM1 * BM2 := add_le_add
            (mul_le_mul (hBS b₁ α) (hBS b₂ α) (norm_nonneg _) hBS1_nn)
            (mul_le_mul (hBM1 α) (hBM2 α) (norm_nonneg _) hBM1_nn)
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  -- Per-pair integral bound `∫ ‖S₁S₂ - M₁M₂‖² ≤ 2 * (∫ ‖R₁‖² ‖S₂‖² + ∫ ‖M₁‖² ‖R₂‖²)`.
  have hpair_split : ∀ b₁ b₂ : ℕ,
      (∫ α in (0 : ℝ)..1,
          ‖smoothedPrimeSum r b₁ Y α * smoothedPrimeSum r b₂ Y α -
            modelSum r b₁ Y Q Q α * modelSum r b₂ Y Q Q α‖ ^ 2) ≤
        2 * (∫ α in (0 : ℝ)..1, ‖R b₁ α‖ ^ 2 * ‖smoothedPrimeSum r b₂ Y α‖ ^ 2) +
        2 * (∫ α in (0 : ℝ)..1, ‖modelSum r b₁ Y Q Q α‖ ^ 2 * ‖R b₂ α‖ ^ 2) := by
    intro b₁ b₂
    have hmono := intervalIntegral.integral_mono_on zero_le_one (hF2_int b₁ b₂)
      (((hRS_int b₁ b₂).const_mul 2).add ((hMR_int b₁ b₂).const_mul 2)) fun α _ => by
      have hid : smoothedPrimeSum r b₁ Y α * smoothedPrimeSum r b₂ Y α -
            modelSum r b₁ Y Q Q α * modelSum r b₂ Y Q Q α =
          R b₁ α * smoothedPrimeSum r b₂ Y α + modelSum r b₁ Y Q Q α * R b₂ α := by dsimp [R]; ring
      rw [hid]
      have htri : ‖R b₁ α * smoothedPrimeSum r b₂ Y α + modelSum r b₁ Y Q Q α * R b₂ α‖ ≤
          ‖R b₁ α‖ * ‖smoothedPrimeSum r b₂ Y α‖ + ‖modelSum r b₁ Y Q Q α‖ * ‖R b₂ α‖ :=
        (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul])
      have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
      have h2ab : (‖R b₁ α‖ * ‖smoothedPrimeSum r b₂ Y α‖ + ‖modelSum r b₁ Y Q Q α‖ * ‖R b₂ α‖) ^ 2 ≤
          2 * (‖R b₁ α‖ ^ 2 * ‖smoothedPrimeSum r b₂ Y α‖ ^ 2) +
          2 * (‖modelSum r b₁ Y Q Q α‖ ^ 2 * ‖R b₂ α‖ ^ 2) := by
        nlinarith [sq_nonneg (‖R b₁ α‖ * ‖smoothedPrimeSum r b₂ Y α‖ - ‖modelSum r b₁ Y Q Q α‖ * ‖R b₂ α‖)]
      linarith
    rw [intervalIntegral.integral_add ((hRS_int b₁ b₂).const_mul 2) ((hMR_int b₁ b₂).const_mul 2),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
    exact hmono
  -- Step 3: Bound the two double-averaged integral terms using `avg_remainder_sq`!
  set C_avg : ℝ := 3 * (3 * C + 1) ^ 2 * (2 : ℝ) ^ 15 + 3 + 3 * (2 : ℝ) ^ 39
  set R_avg : ℝ := C_avg * κ * H * Real.sqrt H * L ^ 2
  have hterm1 : (1 / ((r.totient : ℝ) ^ 2)) *
        ∑ b₁ ∈ coprimeClasses r, ∑ b₂ ∈ coprimeClasses r,
          ∫ α in (0 : ℝ)..1, ‖R b₁ α‖ ^ 2 * ‖smoothedPrimeSum r b₂ Y α‖ ^ 2 ≤
      R_avg * (2 * κ * H * L) := by
    have hpull : ∑ b₁ ∈ coprimeClasses r, ∑ b₂ ∈ coprimeClasses r,
          ∫ α in (0 : ℝ)..1, ‖R b₁ α‖ ^ 2 * ‖smoothedPrimeSum r b₂ Y α‖ ^ 2 =
        ∫ α in (0 : ℝ)..1,
          (∑ b₁ ∈ coprimeClasses r, ‖R b₁ α‖ ^ 2) *
            (∑ b₂ ∈ coprimeClasses r, ‖smoothedPrimeSum r b₂ Y α‖ ^ 2) := by
      have h1 : ∀ b₁ ∈ coprimeClasses r,
          ∑ b₂ ∈ coprimeClasses r, ∫ α in (0 : ℝ)..1, ‖R b₁ α‖ ^ 2 * ‖smoothedPrimeSum r b₂ Y α‖ ^ 2 =
          ∫ α in (0 : ℝ)..1, ∑ b₂ ∈ coprimeClasses r, ‖R b₁ α‖ ^ 2 * ‖smoothedPrimeSum r b₂ Y α‖ ^ 2 :=
        fun b₁ _ => (intervalIntegral_finset_sum fun b₂ _ => hRS_int b₁ b₂).symm
      rw [Finset.sum_congr rfl h1, ← intervalIntegral_finset_sum (fun b₁ _ =>
        intervalIntegrable_finset_sum _ fun b₂ _ => hRS_int b₁ b₂)]
      refine intervalIntegral.integral_congr fun α _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b₁ _ => (Finset.mul_sum _ _ _).symm
    rw [hpull, ← intervalIntegral.integral_const_mul]
    have hpt_avg : ∀ α : ℝ,
        (1 / ((r.totient : ℝ) ^ 2)) *
          ((∑ b₁ ∈ coprimeClasses r, ‖R b₁ α‖ ^ 2) *
            (∑ b₂ ∈ coprimeClasses r, ‖smoothedPrimeSum r b₂ Y α‖ ^ 2)) ≤
        R_avg * ((1 / (r.totient : ℝ)) * ∑ b₂ ∈ coprimeClasses r, ‖smoothedPrimeSum r b₂ Y α‖ ^ 2) := by
      intro α
      have hR := avg_remainder_sq hC hTw hr hrY hH26 α
      have hrew : (1 / ((r.totient : ℝ) ^ 2)) *
            ((∑ b₁ ∈ coprimeClasses r, ‖R b₁ α‖ ^ 2) *
              (∑ b₂ ∈ coprimeClasses r, ‖smoothedPrimeSum r b₂ Y α‖ ^ 2)) =
          ((1 / (r.totient : ℝ)) * ∑ b₁ ∈ coprimeClasses r, ‖R b₁ α‖ ^ 2) *
            ((1 / (r.totient : ℝ)) * ∑ b₂ ∈ coprimeClasses r, ‖smoothedPrimeSum r b₂ Y α‖ ^ 2) := by
        ring
      rw [hrew]
      exact mul_le_mul_of_nonneg_right hR (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _))
    have hL_int : IntervalIntegrable (fun α => (1 / ((r.totient : ℝ) ^ 2)) *
        ((∑ b₁ ∈ coprimeClasses r, ‖R b₁ α‖ ^ 2) *
          (∑ b₂ ∈ coprimeClasses r, ‖smoothedPrimeSum r b₂ Y α‖ ^ 2))) MeasureTheory.volume 0 1 := by
      have heq : (fun α => (1 / ((r.totient : ℝ) ^ 2)) *
            ((∑ b₁ ∈ coprimeClasses r, ‖R b₁ α‖ ^ 2) *
              (∑ b₂ ∈ coprimeClasses r, ‖smoothedPrimeSum r b₂ Y α‖ ^ 2))) =
          fun α => (1 / ((r.totient : ℝ) ^ 2)) * ∑ b₁ ∈ coprimeClasses r, ∑ b₂ ∈ coprimeClasses r,
            ‖R b₁ α‖ ^ 2 * ‖smoothedPrimeSum r b₂ Y α‖ ^ 2 := by
        funext α; congr 1; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => Finset.mul_sum _ _ _
      rw [heq]
      exact (intervalIntegrable_finset_sum _ fun b₁ _ =>
        intervalIntegrable_finset_sum _ fun b₂ _ => hRS_int b₁ b₂).const_mul _
    have hR_int : IntervalIntegrable (fun α => R_avg *
        ((1 / (r.totient : ℝ)) * ∑ b₂ ∈ coprimeClasses r, ‖smoothedPrimeSum r b₂ Y α‖ ^ 2))
        MeasureTheory.volume 0 1 :=
      ((intervalIntegrable_finset_sum _ fun b₂ _ => hS_int b₂).const_mul _).const_mul _
    calc (∫ α in (0 : ℝ)..1, (1 / ((r.totient : ℝ) ^ 2)) *
            ((∑ b₁ ∈ coprimeClasses r, ‖R b₁ α‖ ^ 2) *
              (∑ b₂ ∈ coprimeClasses r, ‖smoothedPrimeSum r b₂ Y α‖ ^ 2)))
        ≤ ∫ α in (0 : ℝ)..1, R_avg *
            ((1 / (r.totient : ℝ)) * ∑ b₂ ∈ coprimeClasses r, ‖smoothedPrimeSum r b₂ Y α‖ ^ 2) :=
          intervalIntegral.integral_mono_on zero_le_one hL_int hR_int fun α _ => hpt_avg α
      _ = R_avg * ((1 / (r.totient : ℝ)) *
            ∑ b₂ ∈ coprimeClasses r, ∫ α in (0 : ℝ)..1, ‖smoothedPrimeSum r b₂ Y α‖ ^ 2) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
              intervalIntegral_finset_sum fun b₂ _ => hS_int b₂]
      _ ≤ R_avg * (2 * κ * H * L) :=
          mul_le_mul_of_nonneg_left (avg_smoothedPrimeSum_l2_le hr hrY hY2) (by dsimp [R_avg, C_avg, κ, H, L]; positivity)
  have hterm2 : (1 / ((r.totient : ℝ) ^ 2)) *
        ∑ b₁ ∈ coprimeClasses r, ∑ b₂ ∈ coprimeClasses r,
          ∫ α in (0 : ℝ)..1, ‖modelSum r b₁ Y Q Q α‖ ^ 2 * ‖R b₂ α‖ ^ 2 ≤
      R_avg * (36 * κ * H * L) := by
    have hpull : ∑ b₁ ∈ coprimeClasses r, ∑ b₂ ∈ coprimeClasses r,
          ∫ α in (0 : ℝ)..1, ‖modelSum r b₁ Y Q Q α‖ ^ 2 * ‖R b₂ α‖ ^ 2 =
        ∫ α in (0 : ℝ)..1,
          (∑ b₁ ∈ coprimeClasses r, ‖modelSum r b₁ Y Q Q α‖ ^ 2) *
            (∑ b₂ ∈ coprimeClasses r, ‖R b₂ α‖ ^ 2) := by
      have h1 : ∀ b₁ ∈ coprimeClasses r,
          ∑ b₂ ∈ coprimeClasses r, ∫ α in (0 : ℝ)..1, ‖modelSum r b₁ Y Q Q α‖ ^ 2 * ‖R b₂ α‖ ^ 2 =
          ∫ α in (0 : ℝ)..1, ∑ b₂ ∈ coprimeClasses r, ‖modelSum r b₁ Y Q Q α‖ ^ 2 * ‖R b₂ α‖ ^ 2 :=
        fun b₁ _ => (intervalIntegral_finset_sum fun b₂ _ => hMR_int b₁ b₂).symm
      rw [Finset.sum_congr rfl h1, ← intervalIntegral_finset_sum (fun b₁ _ =>
        intervalIntegrable_finset_sum _ fun b₂ _ => hMR_int b₁ b₂)]
      refine intervalIntegral.integral_congr fun α _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b₁ _ => (Finset.mul_sum _ _ _).symm
    rw [hpull, ← intervalIntegral.integral_const_mul]
    have hpt_avg : ∀ α : ℝ,
        (1 / ((r.totient : ℝ) ^ 2)) *
          ((∑ b₁ ∈ coprimeClasses r, ‖modelSum r b₁ Y Q Q α‖ ^ 2) *
            (∑ b₂ ∈ coprimeClasses r, ‖R b₂ α‖ ^ 2)) ≤
        R_avg * ((1 / (r.totient : ℝ)) * ∑ b₁ ∈ coprimeClasses r, ‖modelSum r b₁ Y Q Q α‖ ^ 2) := by
      intro α
      have hR := avg_remainder_sq hC hTw hr hrY hH26 α
      have hrew : (1 / ((r.totient : ℝ) ^ 2)) *
            ((∑ b₁ ∈ coprimeClasses r, ‖modelSum r b₁ Y Q Q α‖ ^ 2) *
              (∑ b₂ ∈ coprimeClasses r, ‖R b₂ α‖ ^ 2)) =
          ((1 / (r.totient : ℝ)) * ∑ b₂ ∈ coprimeClasses r, ‖R b₂ α‖ ^ 2) *
            ((1 / (r.totient : ℝ)) * ∑ b₁ ∈ coprimeClasses r, ‖modelSum r b₁ Y Q Q α‖ ^ 2) := by
        ring
      rw [hrew]
      exact mul_le_mul_of_nonneg_right hR (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _))
    have hL_int : IntervalIntegrable (fun α => (1 / ((r.totient : ℝ) ^ 2)) *
        ((∑ b₁ ∈ coprimeClasses r, ‖modelSum r b₁ Y Q Q α‖ ^ 2) *
          (∑ b₂ ∈ coprimeClasses r, ‖R b₂ α‖ ^ 2))) MeasureTheory.volume 0 1 := by
      have heq : (fun α => (1 / ((r.totient : ℝ) ^ 2)) *
            ((∑ b₁ ∈ coprimeClasses r, ‖modelSum r b₁ Y Q Q α‖ ^ 2) *
              (∑ b₂ ∈ coprimeClasses r, ‖R b₂ α‖ ^ 2))) =
          fun α => (1 / ((r.totient : ℝ) ^ 2)) * ∑ b₁ ∈ coprimeClasses r, ∑ b₂ ∈ coprimeClasses r,
            ‖modelSum r b₁ Y Q Q α‖ ^ 2 * ‖R b₂ α‖ ^ 2 := by
        funext α; congr 1; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => Finset.mul_sum _ _ _
      rw [heq]
      exact (intervalIntegrable_finset_sum _ fun b₁ _ =>
        intervalIntegrable_finset_sum _ fun b₂ _ => hMR_int b₁ b₂).const_mul _
    have hR_int : IntervalIntegrable (fun α => R_avg *
        ((1 / (r.totient : ℝ)) * ∑ b₁ ∈ coprimeClasses r, ‖modelSum r b₁ Y Q Q α‖ ^ 2))
        MeasureTheory.volume 0 1 :=
      ((intervalIntegrable_finset_sum _ fun b₁ _ => hM_int b₁).const_mul _).const_mul _
    have hM_avg : (1 / (r.totient : ℝ)) *
          ∑ b₁ ∈ coprimeClasses r, ∫ α in (0 : ℝ)..1, ‖modelSum r b₁ Y Q Q α‖ ^ 2 ≤
        36 * κ * H * L := by
      have hcard : ((coprimeClasses r).card : ℝ) = (r.totient : ℝ) := by rw [card_coprimeClasses]
      calc (1 / (r.totient : ℝ)) *
              ∑ b₁ ∈ coprimeClasses r, ∫ α in (0 : ℝ)..1, ‖modelSum r b₁ Y Q Q α‖ ^ 2
          ≤ (1 / (r.totient : ℝ)) * ∑ _b₁ ∈ coprimeClasses r, (36 * κ * H * L) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b₁ _ =>
              modelSum_l2_le hr hrY hQ_le_Y hY72) (by positivity)
        _ = (1 / (r.totient : ℝ)) * ((r.totient : ℝ) * (36 * κ * H * L)) := by
            simp [nsmul_eq_mul, hcard]
        _ = 36 * κ * H * L := by field_simp [hφr_pos.ne']
    calc (∫ α in (0 : ℝ)..1, (1 / ((r.totient : ℝ) ^ 2)) *
            ((∑ b₁ ∈ coprimeClasses r, ‖modelSum r b₁ Y Q Q α‖ ^ 2) *
              (∑ b₂ ∈ coprimeClasses r, ‖R b₂ α‖ ^ 2)))
        ≤ ∫ α in (0 : ℝ)..1, R_avg *
            ((1 / (r.totient : ℝ)) * ∑ b₁ ∈ coprimeClasses r, ‖modelSum r b₁ Y Q Q α‖ ^ 2) :=
          intervalIntegral.integral_mono_on zero_le_one hL_int hR_int fun α _ => hpt_avg α
      _ = R_avg * ((1 / (r.totient : ℝ)) *
            ∑ b₁ ∈ coprimeClasses r, ∫ α in (0 : ℝ)..1, ‖modelSum r b₁ Y Q Q α‖ ^ 2) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
              intervalIntegral_finset_sum fun b₁ _ => hM_int b₁]
      _ ≤ R_avg * (36 * κ * H * L) :=
          mul_le_mul_of_nonneg_left hM_avg (by dsimp [R_avg, C_avg, κ, H, L]; positivity)
  -- Step 4: Combine and divide by `thresh²`!
  have htotal : doubleAvgDyadicExceptions Y r hr * thresh ^ 2 ≤ 76 * R_avg * κ * H * L := by
    unfold doubleAvgDyadicExceptions
    have hmul_in :
        ((1 / ((r.totient : ℝ) ^ 2)) *
          ∑ b₁ ∈ (coprimeClasses r).attach, ∑ b₂ ∈ (coprimeClasses r).attach,
            ((dyadicExceptions ⟨r, hr, b₁.1, b₂.1,
              (mem_coprimeClasses.mp b₁.2).1, (mem_coprimeClasses.mp b₂.2).1,
              (mem_coprimeClasses.mp b₁.2).2, (mem_coprimeClasses.mp b₂.2).2⟩ Y).card : ℝ)) * thresh ^ 2 =
        (1 / ((r.totient : ℝ) ^ 2)) *
          ∑ b₁ ∈ (coprimeClasses r).attach, ∑ b₂ ∈ (coprimeClasses r).attach,
            ((dyadicExceptions ⟨r, hr, b₁.1, b₂.1,
              (mem_coprimeClasses.mp b₁.2).1, (mem_coprimeClasses.mp b₂.2).1,
              (mem_coprimeClasses.mp b₁.2).2, (mem_coprimeClasses.mp b₂.2).2⟩ Y).card : ℝ) * thresh ^ 2 := by
      rw [mul_assoc, Finset.sum_mul]
      congr 1; refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_mul _ _ _
    rw [hmul_in]
    have hstep1 : (1 / ((r.totient : ℝ) ^ 2)) *
          ∑ b₁ ∈ (coprimeClasses r).attach, ∑ b₂ ∈ (coprimeClasses r).attach,
            ((dyadicExceptions ⟨r, hr, b₁.1, b₂.1,
              (mem_coprimeClasses.mp b₁.2).1, (mem_coprimeClasses.mp b₂.2).1,
              (mem_coprimeClasses.mp b₁.2).2, (mem_coprimeClasses.mp b₂.2).2⟩ Y).card : ℝ) * thresh ^ 2 ≤
        (1 / ((r.totient : ℝ) ^ 2)) *
          ∑ b₁ ∈ coprimeClasses r, ∑ b₂ ∈ coprimeClasses r,
            (2 * (∫ α in (0 : ℝ)..1, ‖R b₁ α‖ ^ 2 * ‖smoothedPrimeSum r b₂ Y α‖ ^ 2) +
             2 * (∫ α in (0 : ℝ)..1, ‖modelSum r b₁ Y Q Q α‖ ^ 2 * ‖R b₂ α‖ ^ 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc ∑ b₁ ∈ (coprimeClasses r).attach, ∑ b₂ ∈ (coprimeClasses r).attach,
              ((dyadicExceptions ⟨r, hr, b₁.1, b₂.1,
                (mem_coprimeClasses.mp b₁.2).1, (mem_coprimeClasses.mp b₂.2).1,
                (mem_coprimeClasses.mp b₁.2).2, (mem_coprimeClasses.mp b₂.2).2⟩ Y).card : ℝ) * thresh ^ 2
          ≤ ∑ b₁ ∈ (coprimeClasses r).attach, ∑ b₂ ∈ (coprimeClasses r).attach,
              (2 * (∫ α in (0 : ℝ)..1, ‖R b₁.1 α‖ ^ 2 * ‖smoothedPrimeSum r b₂.1 Y α‖ ^ 2) +
               2 * (∫ α in (0 : ℝ)..1, ‖modelSum r b₁.1 Y Q Q α‖ ^ 2 * ‖R b₂.1 α‖ ^ 2)) :=
            Finset.sum_le_sum fun b₁ _ => Finset.sum_le_sum fun b₂ _ =>
              (hpair b₁ b₂).trans (hpair_split b₁.1 b₂.1)
        _ = ∑ b₁ ∈ (coprimeClasses r).attach, ∑ b₂ ∈ coprimeClasses r,
              (2 * (∫ α in (0 : ℝ)..1, ‖R b₁.1 α‖ ^ 2 * ‖smoothedPrimeSum r b₂ Y α‖ ^ 2) +
               2 * (∫ α in (0 : ℝ)..1, ‖modelSum r b₁.1 Y Q Q α‖ ^ 2 * ‖R b₂ α‖ ^ 2)) :=
            Finset.sum_congr rfl fun b₁ _ =>
              Finset.sum_attach (coprimeClasses r) (fun b₂ =>
                2 * (∫ α in (0 : ℝ)..1, ‖R b₁.1 α‖ ^ 2 * ‖smoothedPrimeSum r b₂ Y α‖ ^ 2) +
                2 * (∫ α in (0 : ℝ)..1, ‖modelSum r b₁.1 Y Q Q α‖ ^ 2 * ‖R b₂ α‖ ^ 2))
        _ = ∑ b₁ ∈ coprimeClasses r, ∑ b₂ ∈ coprimeClasses r,
              (2 * (∫ α in (0 : ℝ)..1, ‖R b₁ α‖ ^ 2 * ‖smoothedPrimeSum r b₂ Y α‖ ^ 2) +
               2 * (∫ α in (0 : ℝ)..1, ‖modelSum r b₁ Y Q Q α‖ ^ 2 * ‖R b₂ α‖ ^ 2)) :=
            Finset.sum_attach (coprimeClasses r) (fun b₁ => ∑ b₂ ∈ coprimeClasses r,
              (2 * (∫ α in (0 : ℝ)..1, ‖R b₁ α‖ ^ 2 * ‖smoothedPrimeSum r b₂ Y α‖ ^ 2) +
               2 * (∫ α in (0 : ℝ)..1, ‖modelSum r b₁ Y Q Q α‖ ^ 2 * ‖R b₂ α‖ ^ 2)))
    have hstep2 : (1 / ((r.totient : ℝ) ^ 2)) *
          ∑ b₁ ∈ coprimeClasses r, ∑ b₂ ∈ coprimeClasses r,
            (2 * (∫ α in (0 : ℝ)..1, ‖R b₁ α‖ ^ 2 * ‖smoothedPrimeSum r b₂ Y α‖ ^ 2) +
             2 * (∫ α in (0 : ℝ)..1, ‖modelSum r b₁ Y Q Q α‖ ^ 2 * ‖R b₂ α‖ ^ 2)) =
        2 * ((1 / ((r.totient : ℝ) ^ 2)) *
          ∑ b₁ ∈ coprimeClasses r, ∑ b₂ ∈ coprimeClasses r,
            ∫ α in (0 : ℝ)..1, ‖R b₁ α‖ ^ 2 * ‖smoothedPrimeSum r b₂ Y α‖ ^ 2) +
        2 * ((1 / ((r.totient : ℝ) ^ 2)) *
          ∑ b₁ ∈ coprimeClasses r, ∑ b₂ ∈ coprimeClasses r,
            ∫ α in (0 : ℝ)..1, ‖modelSum r b₁ Y Q Q α‖ ^ 2 * ‖R b₂ α‖ ^ 2) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]; ring
    linarith [hstep1, hstep2, hterm1, hterm2]
  have hdiv := (le_div_iff₀ (sq_pos_of_pos hthresh_pos)).2 htotal
  have hrhs_eq : 76 * R_avg * κ * H * L / thresh ^ 2 =
      (76 * (262144 : ℝ) ^ 2 * C_avg) * ((r.totient : ℝ) / (r : ℝ)) ^ 2 * Real.sqrt H * L ^ 3 := by
    have hH_ne : H ≠ 0 := (div_pos (Nat.cast_pos.mpr (by omega)) hr_pos).ne'
    dsimp [R_avg, thresh, κ]
    field_simp [hr_pos.ne', hφr_pos.ne', hH_ne]
  linarith [hdiv, hrhs_eq]

/-- **All-scales Dyadic Double-Average Bound:**
For EVERY `0 < r ≤ Y`, `doubleAvgDyadicExceptions Y r hr ≤ C_D * (φ(r)/r)² * √(Y/r) * log³(2Y)`. -/
lemma dyadic_double_average_all {C : ℝ} (hC : 0 < C)
    (hTw : ∀ (Y d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (t : ℝ),
      2 ≤ Y → |t| ≤ 1 / 2 →
        ‖smoothedTiltedRemainder χ Y t‖ ≤
          C * Real.sqrt ((Y : ℝ) * (1 + |t| * Y)) * Real.log (2 * (d : ℝ) * Y))
    {r Y : ℕ} (hr : 0 < r) (hrY : r ≤ Y) :
    doubleAvgDyadicExceptions Y r hr ≤
      (76 * (262144 : ℝ) ^ 2 * (3 * (3 * C + 1) ^ 2 * (2 : ℝ) ^ 15 + 3 + 3 * (2 : ℝ) ^ 39) +
        4 * ((2 : ℝ) ^ 72 + 1)) *
        ((r.totient : ℝ) / (r : ℝ)) ^ 2 * Real.sqrt ((Y : ℝ) / (r : ℝ)) *
        (Real.log (2 * (Y : ℝ))) ^ 3 := by
  set C1 : ℝ := 76 * (262144 : ℝ) ^ 2 * (3 * (3 * C + 1) ^ 2 * (2 : ℝ) ^ 15 + 3 + 3 * (2 : ℝ) ^ 39)
  set C2 : ℝ := 4 * ((2 : ℝ) ^ 72 + 1)
  have hC1_nn : 0 ≤ C1 := by dsimp [C1]; positivity
  have hC2_nn : 0 ≤ C2 := by dsimp [C2]; positivity
  have hlog_nn : 0 ≤ Real.log (2 * (Y : ℝ)) := Real.log_nonneg (by
    have hY1 : (1 : ℝ) ≤ Y := Nat.one_le_cast.mpr (lt_of_lt_of_le hr hrY); linarith)
  by_cases hH : 2 ^ 72 ≤ Y / r
  · have hbig := dyadic_double_average_large hC hTw hr hH
    have hterm_nn : 0 ≤ ((r.totient : ℝ) / (r : ℝ)) ^ 2 * Real.sqrt ((Y : ℝ) / (r : ℝ)) *
        (Real.log (2 * (Y : ℝ))) ^ 3 := by positivity
    nlinarith only [hbig, hterm_nn, hC2_nn]
  · push Not at hH
    -- When `Y = 1` (and `r = 1`), `dyadicExceptions` is empty since `n = 1` is odd!
    by_cases hY1 : Y = 1
    · subst hY1
      have h0 : doubleAvgDyadicExceptions 1 r hr = 0 := by
        unfold doubleAvgDyadicExceptions
        suffices hs : ∑ b₁ ∈ (coprimeClasses r).attach, ∑ b₂ ∈ (coprimeClasses r).attach,
            ((dyadicExceptions ⟨r, hr, b₁.1, b₂.1,
              (mem_coprimeClasses.mp b₁.2).1, (mem_coprimeClasses.mp b₂.2).1,
              (mem_coprimeClasses.mp b₁.2).2, (mem_coprimeClasses.mp b₂.2).2⟩ 1).card : ℝ) = 0 by
          rw [hs, mul_zero]
        apply Finset.sum_eq_zero; intro b₁ _
        apply Finset.sum_eq_zero; intro b₂ _
        have hemp : dyadicExceptions ⟨r, hr, b₁.1, b₂.1,
            (mem_coprimeClasses.mp b₁.2).1, (mem_coprimeClasses.mp b₂.2).1,
            (mem_coprimeClasses.mp b₁.2).2, (mem_coprimeClasses.mp b₂.2).2⟩ 1 = ∅ := by
          ext n; simp only [dyadicExceptions, exceptions, Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty,
            iff_false, not_and]
          intro h1 _
          have hn1 : n = 1 := by omega
          subst hn1; exact (by decide : ¬ Even (1 : ℕ)) h1.2.1
        rw [hemp]; simp
      rw [h0]; positivity
    · have hY2 : 2 ≤ Y := by omega
      have hL1 : 1 ≤ Real.log (2 * (Y : ℝ)) := one_le_log_two_mul hY2
      have hκ_le : (r : ℝ) / (r.totient : ℝ) ≤ 2 * Real.log (2 * (Y : ℝ)) :=
        (div_totient_le_two_log hr).trans
          (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by
            have : (r : ℝ) ≤ Y := Nat.cast_le.mpr hrY; linarith)) (by norm_num))
      have hφr_pos : (0 : ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
      have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
      have hinvκ : (1 / 4 : ℝ) ≤ ((r.totient : ℝ) / (r : ℝ)) ^ 2 * (Real.log (2 * (Y : ℝ))) ^ 3 := by
        have h1 : (1 / (2 * Real.log (2 * (Y : ℝ)))) ≤ (r.totient : ℝ) / (r : ℝ) := by
          rw [div_le_div_iff₀ (by positivity) hr_pos, one_mul]
          have hmul := mul_le_mul_of_nonneg_left hκ_le hφr_pos.le
          have hcancel : (r.totient : ℝ) * ((r : ℝ) / (r.totient : ℝ)) = (r : ℝ) := by field_simp [hφr_pos.ne']
          linarith
        have hsq := pow_le_pow_left₀ (by positivity) h1 2
        have h2 : (1 / (4 * (Real.log (2 * (Y : ℝ))) ^ 2)) ≤ ((r.totient : ℝ) / (r : ℝ)) ^ 2 := by
          have heq : (1 / (4 * (Real.log (2 * (Y : ℝ))) ^ 2)) = (1 / (2 * Real.log (2 * (Y : ℝ)))) ^ 2 := by ring
          rw [heq]; exact hsq
        have hmul := mul_le_mul_of_nonneg_right h2 (pow_nonneg hlog_nn 3)
        have hL_ne : Real.log (2 * (Y : ℝ)) ≠ 0 := by linarith
        have hsimp : 1 / (4 * (Real.log (2 * (Y : ℝ))) ^ 2) * (Real.log (2 * (Y : ℝ))) ^ 3 =
            Real.log (2 * (Y : ℝ)) / 4 := by field_simp [hL_ne]
        linarith
      have hrt_ge1 : 1 ≤ Real.sqrt ((Y : ℝ) / (r : ℝ)) := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt ((one_le_div hr_pos).2 (Nat.cast_le.mpr hrY))
      have htriv : doubleAvgDyadicExceptions Y r hr ≤ (2 : ℝ) ^ 72 + 1 := by
        unfold doubleAvgDyadicExceptions
        have hper : ∀ (b₁ b₂ : {b // b ∈ coprimeClasses r}),
            ((dyadicExceptions ⟨r, hr, b₁.1, b₂.1,
              (mem_coprimeClasses.mp b₁.2).1, (mem_coprimeClasses.mp b₂.2).1,
              (mem_coprimeClasses.mp b₁.2).2, (mem_coprimeClasses.mp b₂.2).2⟩ Y).card : ℝ) ≤
            (2 : ℝ) ^ 72 + 1 := by
          intro b₁ b₂
          have hsub : dyadicExceptions ⟨r, hr, b₁.1, b₂.1,
              (mem_coprimeClasses.mp b₁.2).1, (mem_coprimeClasses.mp b₂.2).1,
              (mem_coprimeClasses.mp b₁.2).2, (mem_coprimeClasses.mp b₂.2).2⟩ Y ⊆
              (Finset.Icc 1 Y).filter (fun n => n % r = (b₁.1 + b₂.1) % r) := fun n hn =>
            Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1,
              (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2.2.1⟩
          have hcard := (Finset.card_le_card hsub).trans (card_congruence_Icc_le Y r _ hr)
          have hle : Y / r + 1 ≤ 2 ^ 72 + 1 := by omega
          exact_mod_cast hcard.trans hle
        have hcard_att : ((coprimeClasses r).attach.card : ℝ) = (r.totient : ℝ) := by
          rw [Finset.card_attach, card_coprimeClasses]
        calc (1 / ((r.totient : ℝ) ^ 2)) *
                ∑ b₁ ∈ (coprimeClasses r).attach, ∑ b₂ ∈ (coprimeClasses r).attach,
                  ((dyadicExceptions ⟨r, hr, b₁.1, b₂.1,
                    (mem_coprimeClasses.mp b₁.2).1, (mem_coprimeClasses.mp b₂.2).1,
                    (mem_coprimeClasses.mp b₁.2).2, (mem_coprimeClasses.mp b₂.2).2⟩ Y).card : ℝ)
            ≤ (1 / ((r.totient : ℝ) ^ 2)) *
                ∑ _b₁ ∈ (coprimeClasses r).attach, ∑ _b₂ ∈ (coprimeClasses r).attach, ((2 : ℝ) ^ 72 + 1) :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b₁ _ => Finset.sum_le_sum fun b₂ _ => hper b₁ b₂)
                (by positivity)
          _ = (1 / ((r.totient : ℝ) ^ 2)) * (((r.totient : ℝ) ^ 2) * ((2 : ℝ) ^ 72 + 1)) := by
              simp only [Finset.sum_const, nsmul_eq_mul, hcard_att]; ring
          _ = (2 : ℝ) ^ 72 + 1 := by field_simp [hφr_pos.ne']
      have hterm_ge : (1 / 4 : ℝ) ≤ ((r.totient : ℝ) / (r : ℝ)) ^ 2 * Real.sqrt ((Y : ℝ) / (r : ℝ)) *
          (Real.log (2 * (Y : ℝ))) ^ 3 := by
        have h1 : ((r.totient : ℝ) / (r : ℝ)) ^ 2 * (Real.log (2 * (Y : ℝ))) ^ 3 ≤
            ((r.totient : ℝ) / (r : ℝ)) ^ 2 * Real.sqrt ((Y : ℝ) / (r : ℝ)) * (Real.log (2 * (Y : ℝ))) ^ 3 := by
          have hnn : 0 ≤ ((r.totient : ℝ) / (r : ℝ)) ^ 2 * (Real.log (2 * (Y : ℝ))) ^ 3 := by positivity
          nlinarith only [hnn, hrt_ge1]
        linarith only [hinvκ, h1]
      have hC2_eq : C2 = 4 * ((2 : ℝ) ^ 72 + 1) := rfl
      nlinarith only [htriv, hterm_ge, hC1_nn, hC2_eq]

/-- **Module F3 Main Theorem (`SmoothedTwistEstimate → Theorem (D)`):**
For EVERY `2 ≤ X` and EVERY `0 < r ≤ X`:
`doubleAvgExceptions X r hr ≤ C_D * min (X / r) ((φ(r)/r)² * √(X/r) * log³(2X))`. -/
theorem double_average_of_smoothedTwist :
    SmoothedTwistEstimate →
    ∃ C : ℝ, 0 < C ∧ ∀ (X r : ℕ) (hr : 0 < r), 2 ≤ X → r ≤ X →
      doubleAvgExceptions X r hr ≤
        C * min ((X : ℝ) / (r : ℝ))
          (((r.totient : ℝ) / (r : ℝ)) ^ 2 * Real.sqrt ((X : ℝ) / (r : ℝ)) *
            (Real.log (2 * (X : ℝ))) ^ 3) := by
  rintro ⟨C₀, hC₀, hTw⟩
  obtain ⟨C_dyad, hCdyad_pos, hdyad_all⟩ :
      ∃ C_dyad : ℝ, 0 < C_dyad ∧ ∀ {r Y : ℕ} (hr : 0 < r), r ≤ Y →
        doubleAvgDyadicExceptions Y r hr ≤
          C_dyad * ((r.totient : ℝ) / (r : ℝ)) ^ 2 * Real.sqrt ((Y : ℝ) / (r : ℝ)) *
            (Real.log (2 * (Y : ℝ))) ^ 3 :=
    ⟨76 * (262144 : ℝ) ^ 2 * (3 * (3 * C₀ + 1) ^ 2 * (2 : ℝ) ^ 15 + 3 + 3 * (2 : ℝ) ^ 39) +
        4 * ((2 : ℝ) ^ 72 + 1),
      by positivity, fun hr hrY => dyadic_double_average_all hC₀ hTw hr hrY⟩
  refine ⟨4 * C_dyad + 8, by linarith, fun X r hr hX2 hrX => ?_⟩
  have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hX_pos : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
  have hφr_pos : (0 : ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  -- Bound 1: Trivial congruence bound `doubleAvgExceptions X r hr ≤ 2 * (X / r)`.
  have htriv : doubleAvgExceptions X r hr ≤ (4 * C_dyad + 8) * ((X : ℝ) / (r : ℝ)) := by
    have hcard_att : ((coprimeClasses r).attach.card : ℝ) = (r.totient : ℝ) := by
      rw [Finset.card_attach, card_coprimeClasses]
    have hper : ∀ (b₁ b₂ : {b // b ∈ coprimeClasses r}),
        ((exceptions ⟨r, hr, b₁.1, b₂.1,
          (mem_coprimeClasses.mp b₁.2).1, (mem_coprimeClasses.mp b₂.2).1,
          (mem_coprimeClasses.mp b₁.2).2, (mem_coprimeClasses.mp b₂.2).2⟩ X).card : ℝ) ≤
        2 * ((X : ℝ) / (r : ℝ)) := by
      intro b₁ b₂
      have hsub : exceptions ⟨r, hr, b₁.1, b₂.1,
          (mem_coprimeClasses.mp b₁.2).1, (mem_coprimeClasses.mp b₂.2).1,
          (mem_coprimeClasses.mp b₁.2).2, (mem_coprimeClasses.mp b₂.2).2⟩ X ⊆
          (Finset.Icc 1 X).filter (fun n => n % r = (b₁.1 + b₂.1) % r) := fun n hn =>
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1, (Finset.mem_filter.mp hn).2.2.1⟩
      have hcard := (Finset.card_le_card hsub).trans (card_congruence_Icc_le X r _ hr)
      have hdiv : ((X / r : ℕ) : ℝ) ≤ (X : ℝ) / (r : ℝ) := by
        rw [le_div_iff₀ hr_pos]; exact_mod_cast (by simpa [mul_comm] using Nat.mul_div_le X r)
      have h1 : (1 : ℝ) ≤ (X : ℝ) / (r : ℝ) := (one_le_div hr_pos).2 (Nat.cast_le.mpr hrX)
      have hR : ((X / r + 1 : ℕ) : ℝ) ≤ 2 * ((X : ℝ) / (r : ℝ)) := by push_cast; linarith
      exact (Nat.cast_le.mpr hcard).trans hR
    have h2 : doubleAvgExceptions X r hr ≤ 2 * ((X : ℝ) / (r : ℝ)) := by
      unfold doubleAvgExceptions
      calc (1 / ((r.totient : ℝ) ^ 2)) *
              ∑ b₁ ∈ (coprimeClasses r).attach, ∑ b₂ ∈ (coprimeClasses r).attach,
                ((exceptions ⟨r, hr, b₁.1, b₂.1,
                  (mem_coprimeClasses.mp b₁.2).1, (mem_coprimeClasses.mp b₂.2).1,
                  (mem_coprimeClasses.mp b₁.2).2, (mem_coprimeClasses.mp b₂.2).2⟩ X).card : ℝ)
          ≤ (1 / ((r.totient : ℝ) ^ 2)) *
              ∑ _b₁ ∈ (coprimeClasses r).attach, ∑ _b₂ ∈ (coprimeClasses r).attach, (2 * ((X : ℝ) / (r : ℝ))) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b₁ _ => Finset.sum_le_sum fun b₂ _ => hper b₁ b₂)
              (by positivity)
        _ = (1 / ((r.totient : ℝ) ^ 2)) * (((r.totient : ℝ) ^ 2) * (2 * ((X : ℝ) / (r : ℝ)))) := by
            simp only [Finset.sum_const, nsmul_eq_mul, hcard_att]; ring
        _ = 2 * ((X : ℝ) / (r : ℝ)) := by field_simp [hφr_pos.ne']
    nlinarith only [h2, hCdyad_pos, div_pos hX_pos hr_pos]
  -- Bound 2: Dyadic decomposition from `X` down to `r`, plus at most 2 exceptions in `[1, r]`.
  have hdyad : doubleAvgExceptions X r hr ≤
      (4 * C_dyad + 8) *
        (((r.totient : ℝ) / (r : ℝ)) ^ 2 * Real.sqrt ((X : ℝ) / (r : ℝ)) *
          (Real.log (2 * (X : ℝ))) ^ 3) := by
    let K : ℕ := Nat.log 2 (X / r) + 1
    let Yseq : ℕ → ℕ := fun j => X / 2 ^ j
    have hYseq_ge : ∀ j < K, r ≤ Yseq j := by
      intro j hj
      have hj_le : j ≤ Nat.log 2 (X / r) := Nat.lt_succ_iff.mp hj
      have h2j : 2 ^ j ≤ X / r :=
        (Nat.pow_le_pow_right (by norm_num) hj_le).trans
          (Nat.pow_log_le_self 2 (Nat.div_pos hrX hr).ne')
      exact (Nat.le_div_iff_mul_le (Nat.pow_pos two_pos)).2
        ((Nat.mul_le_mul_left r h2j).trans (Nat.mul_div_le X r))
    have hYseq_end : Yseq K < r := by
      dsimp [Yseq, K]
      have hlt : X / r < 2 ^ (Nat.log 2 (X / r) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos two_pos)]
      have hd := Nat.div_add_mod X r; have hm := Nat.mod_lt X hr
      have h1 : X < r * (X / r + 1) := by nlinarith only [hd, hm]
      have h2 : X / r + 1 ≤ 2 ^ (Nat.log 2 (X / r) + 1) := hlt
      calc X < r * (X / r + 1) := h1
        _ ≤ r * 2 ^ (Nat.log 2 (X / r) + 1) := Nat.mul_le_mul_left r h2
    -- Every `n ∈ exceptions P X` lies either in `Icc 1 r` or in `dyadicExceptions P (Yseq j)` for some `j < K`.
    have hcover : ∀ (P : Progressions), P.r = r →
        ((exceptions P X).card : ℝ) ≤
          2 + ∑ j ∈ Finset.range K, ((dyadicExceptions P (Yseq j)).card : ℝ) := by
      intro P hPr
      have hsub : exceptions P X ⊆
          ((Finset.Icc 1 r).filter (fun n => n % r = (P.b₁ + P.b₂) % r)) ∪
          (Finset.range K).biUnion (fun j => dyadicExceptions P (Yseq j)) := by
        intro n hn
        have hn_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
        have hn_mod := (Finset.mem_filter.mp hn).2.2.1
        by_cases hnr : n ≤ r
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn_Icc.1, hnr⟩, hPr ▸ hn_mod⟩)
        · push Not at hnr
          refine Finset.mem_union_right _ ?_
          -- Find the largest `j < K` with `n ≤ Yseq j`.
          let Jset := (Finset.range K).filter (fun j => n ≤ Yseq j)
          have h0_mem : 0 ∈ Jset := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by dsimp [K]; omega), by
            dsimp [Yseq]; simpa using hn_Icc.2⟩
          let j := Jset.max' ⟨0, h0_mem⟩
          have hj_mem : j ∈ Jset := Finset.max'_mem Jset ⟨0, h0_mem⟩
          have hj_lt : j < K := Finset.mem_range.mp (Finset.mem_filter.mp hj_mem).1
          have hnj : n ≤ Yseq j := (Finset.mem_filter.mp hj_mem).2
          have hgt : Yseq j / 2 < n := by
            have hnext : Yseq (j + 1) = Yseq j / 2 := by
              dsimp [Yseq]; rw [pow_succ, Nat.div_div_eq_div_mul]
            by_cases hj1 : j + 1 < K
            · by_contra hle; push Not at hle
              have hmem1 : j + 1 ∈ Jset :=
                Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj1, hnext.symm ▸ hle⟩
              have := Finset.le_max' Jset (j + 1) hmem1; omega
            · have hjK : j + 1 = K := by omega
              rw [← hnext, hjK]; omega
          refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj_lt,
            Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn_Icc.1, hnj⟩,
              (Finset.mem_filter.mp hn).2⟩, hgt⟩⟩
      have hcard_le : (exceptions P X).card ≤
          2 + ∑ j ∈ Finset.range K, (dyadicExceptions P (Yseq j)).card := by
        calc (exceptions P X).card
            ≤ (((Finset.Icc 1 r).filter (fun n => n % r = (P.b₁ + P.b₂) % r)) ∪
                (Finset.range K).biUnion (fun j => dyadicExceptions P (Yseq j))).card :=
              Finset.card_le_card hsub
          _ ≤ ((Finset.Icc 1 r).filter (fun n => n % r = (P.b₁ + P.b₂) % r)).card +
                ((Finset.range K).biUnion (fun j => dyadicExceptions P (Yseq j))).card :=
              Finset.card_union_le _ _
          _ ≤ (r / r + 1) + ∑ j ∈ Finset.range K, (dyadicExceptions P (Yseq j)).card :=
              Nat.add_le_add (card_congruence_Icc_le r r _ hr) Finset.card_biUnion_le
          _ = 2 + ∑ j ∈ Finset.range K, (dyadicExceptions P (Yseq j)).card := by
              rw [Nat.div_self hr]
      exact_mod_cast hcard_le
    -- Average `hcover` over `b₁, b₂`!
    have hcard_att : ((coprimeClasses r).attach.card : ℝ) = (r.totient : ℝ) := by
      rw [Finset.card_attach, card_coprimeClasses]
    have havg_sum : doubleAvgExceptions X r hr ≤
        2 + ∑ j ∈ Finset.range K, doubleAvgDyadicExceptions (Yseq j) r hr := by
      unfold doubleAvgExceptions doubleAvgDyadicExceptions
      have hrhs : 2 + ∑ j ∈ Finset.range K,
            (1 / ((r.totient : ℝ) ^ 2)) *
              ∑ b₁ ∈ (coprimeClasses r).attach, ∑ b₂ ∈ (coprimeClasses r).attach,
                ((dyadicExceptions ⟨r, hr, b₁.1, b₂.1,
                  (mem_coprimeClasses.mp b₁.2).1, (mem_coprimeClasses.mp b₂.2).1,
                  (mem_coprimeClasses.mp b₁.2).2, (mem_coprimeClasses.mp b₂.2).2⟩ (Yseq j)).card : ℝ) =
          (1 / ((r.totient : ℝ) ^ 2)) *
            ∑ b₁ ∈ (coprimeClasses r).attach, ∑ b₂ ∈ (coprimeClasses r).attach,
              (2 + ∑ j ∈ Finset.range K,
                ((dyadicExceptions ⟨r, hr, b₁.1, b₂.1,
                  (mem_coprimeClasses.mp b₁.2).1, (mem_coprimeClasses.mp b₂.2).1,
                  (mem_coprimeClasses.mp b₁.2).2, (mem_coprimeClasses.mp b₂.2).2⟩ (Yseq j)).card : ℝ)) := by
        have hswap_all :
            ∑ b₁ ∈ (coprimeClasses r).attach, ∑ b₂ ∈ (coprimeClasses r).attach, ∑ j ∈ Finset.range K,
                ((dyadicExceptions ⟨r, hr, b₁.1, b₂.1,
                  (mem_coprimeClasses.mp b₁.2).1, (mem_coprimeClasses.mp b₂.2).1,
                  (mem_coprimeClasses.mp b₁.2).2, (mem_coprimeClasses.mp b₂.2).2⟩ (Yseq j)).card : ℝ) =
            ∑ j ∈ Finset.range K, ∑ b₁ ∈ (coprimeClasses r).attach, ∑ b₂ ∈ (coprimeClasses r).attach,
                ((dyadicExceptions ⟨r, hr, b₁.1, b₂.1,
                  (mem_coprimeClasses.mp b₁.2).1, (mem_coprimeClasses.mp b₂.2).1,
                  (mem_coprimeClasses.mp b₁.2).2, (mem_coprimeClasses.mp b₂.2).2⟩ (Yseq j)).card : ℝ) := by
          calc ∑ b₁ ∈ (coprimeClasses r).attach, ∑ b₂ ∈ (coprimeClasses r).attach, ∑ j ∈ Finset.range K,
                  ((dyadicExceptions ⟨r, hr, b₁.1, b₂.1,
                    (mem_coprimeClasses.mp b₁.2).1, (mem_coprimeClasses.mp b₂.2).1,
                    (mem_coprimeClasses.mp b₁.2).2, (mem_coprimeClasses.mp b₂.2).2⟩ (Yseq j)).card : ℝ)
              = ∑ b₁ ∈ (coprimeClasses r).attach, ∑ j ∈ Finset.range K, ∑ b₂ ∈ (coprimeClasses r).attach,
                  ((dyadicExceptions ⟨r, hr, b₁.1, b₂.1,
                    (mem_coprimeClasses.mp b₁.2).1, (mem_coprimeClasses.mp b₂.2).1,
                    (mem_coprimeClasses.mp b₁.2).2, (mem_coprimeClasses.mp b₂.2).2⟩ (Yseq j)).card : ℝ) :=
                Finset.sum_congr rfl fun _ _ => Finset.sum_comm
            _ = _ := Finset.sum_comm
        simp_rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard_att]
        rw [← Finset.mul_sum, hswap_all, mul_add]
        congr 1
        calc (2 : ℝ) = (((r.totient : ℝ) ^ 2) / ((r.totient : ℝ) ^ 2)) * 2 := by
              rw [div_self (pow_ne_zero 2 hφr_pos.ne'), one_mul]
          _ = (1 / ((r.totient : ℝ) ^ 2)) * ((r.totient : ℝ) * ((r.totient : ℝ) * 2)) := by ring
      rw [hrhs]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact Finset.sum_le_sum fun b₁ _ => Finset.sum_le_sum fun b₂ _ => hcover _ rfl
    -- Bound each dyadic term by `C_dyad * (φ(r)/r)² * √(X/r) * log³(2X) * (1 / √2)^j`.
    have hblock : ∀ j ∈ Finset.range K,
        doubleAvgDyadicExceptions (Yseq j) r hr ≤
          (C_dyad * ((r.totient : ℝ) / (r : ℝ)) ^ 2 * Real.sqrt ((X : ℝ) / (r : ℝ)) *
            (Real.log (2 * (X : ℝ))) ^ 3) * ((1 / Real.sqrt 2) ^ j) := by
      intro j hj
      have hj_lt : j < K := Finset.mem_range.mp hj
      have hge := hYseq_ge j hj_lt
      have hbd := hdyad_all hr hge
      have hYle : (Yseq j : ℝ) ≤ (X : ℝ) / ((2 : ℝ) ^ j) := by
        dsimp [Yseq]
        rw [le_div_iff₀ (by positivity)]
        exact_mod_cast (by simpa [mul_comm] using Nat.mul_div_le X (2 ^ j))
      have hrt : Real.sqrt ((Yseq j : ℝ) / (r : ℝ)) ≤ Real.sqrt ((X : ℝ) / (r : ℝ)) * (1 / Real.sqrt 2) ^ j := by
        have h1 : (Yseq j : ℝ) / (r : ℝ) ≤ ((X : ℝ) / (r : ℝ)) / ((2 : ℝ) ^ j) := by
          rw [div_div, mul_comm (r : ℝ), ← div_div]
          exact div_le_div_of_nonneg_right hYle hr_pos.le
        have hsqrt2j : Real.sqrt ((2 : ℝ) ^ j) = (Real.sqrt 2) ^ j := by
          rw [← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg 2) j)]
          congr 1; rw [← pow_mul, mul_comm j 2, pow_mul, Real.sq_sqrt (by norm_num)]
        calc Real.sqrt ((Yseq j : ℝ) / (r : ℝ))
            ≤ Real.sqrt (((X : ℝ) / (r : ℝ)) / ((2 : ℝ) ^ j)) := Real.sqrt_le_sqrt h1
          _ = Real.sqrt ((X : ℝ) / (r : ℝ)) / Real.sqrt ((2 : ℝ) ^ j) := Real.sqrt_div (by positivity) _
          _ = Real.sqrt ((X : ℝ) / (r : ℝ)) * (1 / Real.sqrt 2) ^ j := by
              rw [hsqrt2j, div_eq_mul_inv, ← one_div, one_div_pow]
      have hlog_le : Real.log (2 * (Yseq j : ℝ)) ≤ Real.log (2 * (X : ℝ)) := by
        have hpos : (0 : ℝ) < 2 * (Yseq j : ℝ) := by
          have : 0 < Yseq j := lt_of_lt_of_le hr hge; positivity
        exact Real.log_le_log hpos (by
          have : Yseq j ≤ X := Nat.div_le_self X (2 ^ j)
          have : (Yseq j : ℝ) ≤ X := Nat.cast_le.mpr this; linarith)
      have hlog_nn : 0 ≤ Real.log (2 * (Yseq j : ℝ)) := Real.log_nonneg (by
        have : (1 : ℝ) ≤ Yseq j := Nat.one_le_cast.mpr (lt_of_lt_of_le hr hge); linarith)
      have hlog3 : (Real.log (2 * (Yseq j : ℝ))) ^ 3 ≤ (Real.log (2 * (X : ℝ))) ^ 3 :=
        pow_le_pow_left₀ hlog_nn hlog_le 3
      calc doubleAvgDyadicExceptions (Yseq j) r hr
          ≤ C_dyad * ((r.totient : ℝ) / (r : ℝ)) ^ 2 * Real.sqrt ((Yseq j : ℝ) / (r : ℝ)) *
              (Real.log (2 * (Yseq j : ℝ))) ^ 3 := hbd
        _ ≤ C_dyad * ((r.totient : ℝ) / (r : ℝ)) ^ 2 *
              (Real.sqrt ((X : ℝ) / (r : ℝ)) * (1 / Real.sqrt 2) ^ j) *
              (Real.log (2 * (X : ℝ))) ^ 3 := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hrt (by positivity)) hlog3 (pow_nonneg hlog_nn 3) (by positivity)
        _ = (C_dyad * ((r.totient : ℝ) / (r : ℝ)) ^ 2 * Real.sqrt ((X : ℝ) / (r : ℝ)) *
              (Real.log (2 * (X : ℝ))) ^ 3) * ((1 / Real.sqrt 2) ^ j) := by ring
    have hgeom : ∑ j ∈ Finset.range K, ((1 / Real.sqrt 2) ^ j) ≤ 4 := by
      have hrt2_gt1 : (1 : ℝ) < Real.sqrt 2 := by
        rw [← Real.sqrt_one]; exact Real.sqrt_lt_sqrt zero_le_one (by norm_num)
      have hrt2_lt : Real.sqrt 2 < 3 / 2 := by
        rw [Real.sqrt_lt' (by norm_num)]; norm_num
      have hratio_lt : 1 / Real.sqrt 2 < 1 := (div_lt_one (by positivity)).2 hrt2_gt1
      rw [geom_sum_eq hratio_lt.ne]
      have hnum : (1 / Real.sqrt 2) ^ K - 1 ≥ -1 := by
        have : (0 : ℝ) ≤ (1 / Real.sqrt 2) ^ K := by positivity
        linarith
      have hden_neg : 1 / Real.sqrt 2 - 1 < 0 := by linarith
      have h1 : ((1 / Real.sqrt 2) ^ K - 1) / (1 / Real.sqrt 2 - 1) ≤ 1 / (1 - 1 / Real.sqrt 2) := by
        have heq : ((1 / Real.sqrt 2) ^ K - 1) / (1 / Real.sqrt 2 - 1) =
            (1 - (1 / Real.sqrt 2) ^ K) / (1 - 1 / Real.sqrt 2) := by
          rw [← neg_div_neg_eq, neg_sub, neg_sub]
        rw [heq]
        exact div_le_div_of_nonneg_right (by linarith [show (0 : ℝ) ≤ (1 / Real.sqrt 2) ^ K by positivity])
          (by linarith)
      have h2 : 1 / (1 - 1 / Real.sqrt 2) ≤ 4 := by
        rw [div_le_iff₀ (by linarith)]
        have hrt2_ge : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
          rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
        have hinv : 1 / Real.sqrt 2 ≤ 3 / 4 := by
          rw [div_le_iff₀ (by positivity)]; linarith
        linarith
      linarith
    -- Bound the constant `2 ≤ 8 * (φ(r)/r)² * √(X/r) * log³(2X)`.
    have h2_le : (2 : ℝ) ≤ 8 * (((r.totient : ℝ) / (r : ℝ)) ^ 2 * Real.sqrt ((X : ℝ) / (r : ℝ)) *
        (Real.log (2 * (X : ℝ))) ^ 3) := by
      have hL1 : 1 ≤ Real.log (2 * (X : ℝ)) := one_le_log_two_mul hX2
      have hκ_le : (r : ℝ) / (r.totient : ℝ) ≤ 2 * Real.log (2 * (X : ℝ)) :=
        (div_totient_le_two_log hr).trans
          (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by
            have : (r : ℝ) ≤ X := Nat.cast_le.mpr hrX; linarith)) (by norm_num))
      have h1 : (1 / (2 * Real.log (2 * (X : ℝ)))) ≤ (r.totient : ℝ) / (r : ℝ) := by
        rw [div_le_div_iff₀ (by positivity) hr_pos, one_mul]
        have hmul := mul_le_mul_of_nonneg_left hκ_le hφr_pos.le
        have hcancel : (r.totient : ℝ) * ((r : ℝ) / (r.totient : ℝ)) = (r : ℝ) := by field_simp [hφr_pos.ne']
        linarith
      have hsq := pow_le_pow_left₀ (by positivity) h1 2
      have h2 : (1 / (4 * (Real.log (2 * (X : ℝ))) ^ 2)) ≤ ((r.totient : ℝ) / (r : ℝ)) ^ 2 := by
        have heq : (1 / (4 * (Real.log (2 * (X : ℝ))) ^ 2)) = (1 / (2 * Real.log (2 * (X : ℝ)))) ^ 2 := by ring
        rw [heq]; exact hsq
      have hL_nn : 0 ≤ Real.log (2 * (X : ℝ)) := by linarith
      have hmul := mul_le_mul_of_nonneg_right h2 (pow_nonneg hL_nn 3)
      have hL_ne : Real.log (2 * (X : ℝ)) ≠ 0 := by linarith
      have hsimp : 1 / (4 * (Real.log (2 * (X : ℝ))) ^ 2) * (Real.log (2 * (X : ℝ))) ^ 3 =
          Real.log (2 * (X : ℝ)) / 4 := by field_simp [hL_ne]
      have hrt1 : 1 ≤ Real.sqrt ((X : ℝ) / (r : ℝ)) := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt ((one_le_div hr_pos).2 (Nat.cast_le.mpr hrX))
      have hprod : (1 / 4 : ℝ) ≤ ((r.totient : ℝ) / (r : ℝ)) ^ 2 * Real.sqrt ((X : ℝ) / (r : ℝ)) *
          (Real.log (2 * (X : ℝ))) ^ 3 := by
        have hA : (1 / 4 : ℝ) ≤ ((r.totient : ℝ) / (r : ℝ)) ^ 2 * (Real.log (2 * (X : ℝ))) ^ 3 := by linarith
        nlinarith only [hA, hrt1]
      linarith
    have hcoeff_nn : 0 ≤ C_dyad * ((r.totient : ℝ) / (r : ℝ)) ^ 2 * Real.sqrt ((X : ℝ) / (r : ℝ)) *
        (Real.log (2 * (X : ℝ))) ^ 3 := by
      have hL_nn : 0 ≤ Real.log (2 * (X : ℝ)) :=
        Real.log_nonneg (by have : (2 : ℝ) ≤ X := Nat.cast_le.mpr hX2; linarith)
      positivity
    calc doubleAvgExceptions X r hr
        ≤ 2 + ∑ j ∈ Finset.range K, doubleAvgDyadicExceptions (Yseq j) r hr := havg_sum
      _ ≤ 2 + ∑ j ∈ Finset.range K,
            (C_dyad * ((r.totient : ℝ) / (r : ℝ)) ^ 2 * Real.sqrt ((X : ℝ) / (r : ℝ)) *
              (Real.log (2 * (X : ℝ))) ^ 3) * ((1 / Real.sqrt 2) ^ j) :=
          add_le_add le_rfl (Finset.sum_le_sum hblock)
      _ = 2 + (C_dyad * ((r.totient : ℝ) / (r : ℝ)) ^ 2 * Real.sqrt ((X : ℝ) / (r : ℝ)) *
            (Real.log (2 * (X : ℝ))) ^ 3) * ∑ j ∈ Finset.range K, ((1 / Real.sqrt 2) ^ j) := by
          rw [← Finset.mul_sum]
      _ ≤ 2 + (C_dyad * ((r.totient : ℝ) / (r : ℝ)) ^ 2 * Real.sqrt ((X : ℝ) / (r : ℝ)) *
            (Real.log (2 * (X : ℝ))) ^ 3) * 4 :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hgeom hcoeff_nn)
      _ ≤ (4 * C_dyad + 8) *
            (((r.totient : ℝ) / (r : ℝ)) ^ 2 * Real.sqrt ((X : ℝ) / (r : ℝ)) *
              (Real.log (2 * (X : ℝ))) ^ 3) := by linarith
  rw [mul_min_of_nonneg _ _ (by linarith : (0 : ℝ) ≤ 4 * C_dyad + 8)]
  exact le_min htriv hdyad

/-- **End-to-End Theorem (D) (`DirichletGRH → Double-Averaged Binary Goldbach`):**
Under Dirichlet GRH, there exists an absolute constant `C > 0` such that for EVERY `X ≥ 2`
and EVERY positive integer modulus `1 ≤ r ≤ X`,
```
(1 / φ(r)²) * ∑_{b₁, b₂ ∈ U_r} E_r(X; b₁, b₂)
  ≤ C * min (X / r) ((φ(r) / r)² * √(X / r) * log³(2 * X)).
``` -/
theorem double_average_of_dirichletGRH :
    DirichletGRH →
    ∃ C : ℝ, 0 < C ∧ ∀ (X r : ℕ) (hr : 0 < r), 2 ≤ X → r ≤ X →
      doubleAvgExceptions X r hr ≤
        C * min ((X : ℝ) / (r : ℝ))
          (((r.totient : ℝ) / (r : ℝ)) ^ 2 * Real.sqrt ((X : ℝ) / (r : ℝ)) *
            (Real.log (2 * (X : ℝ))) ^ 3) :=
  fun hGRH => double_average_of_smoothedTwist (smoothedTwistEstimate_of_dirichletGRH hGRH)

end DyadicAndGlobalDoubleAverage

/-- The squared reciprocal of the normalized analytic term in the double-average bound. -/
noncomputable def doubleAvgParameter (X r : ℕ) : ℝ :=
  ((r : ℝ) / r.totient) ^ 4 * ((X : ℝ) / r) / Real.log (2 * (X : ℝ)) ^ 6

private theorem doubleAvg_normalized_term {X r : ℕ} (hr : 0 < r) (hX : 2 ≤ X) :
    (((r.totient : ℝ) / r) ^ 2 * Real.sqrt ((X : ℝ) / r) * Real.log (2 * (X : ℝ)) ^ 3) /
      ((X : ℝ) / r) = (Real.sqrt (doubleAvgParameter X r))⁻¹ := by
  have hr' : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have ht : (0 : ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hX' : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
  let H : ℝ := (X : ℝ) / r
  let L := Real.log (2 * (X : ℝ))
  let κ : ℝ := (r : ℝ) / r.totient
  let a : ℝ := (r.totient : ℝ) / r
  have hH : 0 < H := div_pos hX' hr'
  have hL : 0 < L := Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * X))
  have hκ : 0 < κ := div_pos hr' ht
  have haκ : a * κ = 1 := by dsimp [a, κ]; field_simp
  have hs : Real.sqrt (doubleAvgParameter X r) = κ ^ 2 * Real.sqrt H / L ^ 3 := by
    change Real.sqrt (κ ^ 4 * H / L ^ 6) = _
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity)]
    have hκ4 : κ ^ 4 = (κ ^ 2) ^ 2 := by ring
    have hL6 : L ^ 6 = (L ^ 3) ^ 2 := by ring
    rw [hκ4, hL6, Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)]
  have hs' : 0 < Real.sqrt (doubleAvgParameter X r) := by rw [hs]; positivity
  change (a ^ 2 * Real.sqrt H * L ^ 3) / H = _
  rw [← one_div]
  symm
  apply (div_eq_iff hs'.ne').2
  symm
  rw [hs]
  calc a ^ 2 * Real.sqrt H * L ^ 3 / H * (κ ^ 2 * Real.sqrt H / L ^ 3) =
      (a * κ) ^ 2 * (Real.sqrt H) ^ 2 / H := by field_simp
    _ = 1 := by rw [haκ, Real.sq_sqrt hH.le]; simp [hH.ne']

/-- The double-averaged exceptional proportion tends to zero whenever
`(r/φ(r))⁴ (X/r) / log⁶(2X)` tends to infinity along the chosen sequence. -/
theorem double_average_density_one_of_dirichletGRH (h : DirichletGRH)
    (X r : ℕ → ℕ) (hr : ∀ n, 0 < r n) (hX : ∀ n, 2 ≤ X n) (hrX : ∀ n, r n ≤ X n)
    (hP : Tendsto (fun n => doubleAvgParameter (X n) (r n)) atTop atTop) :
    Tendsto (fun n => doubleAvgExceptions (X n) (r n) (hr n) / ((X n : ℝ) / r n))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := double_average_of_dirichletGRH h
  have hs : Tendsto (fun n => (Real.sqrt (doubleAvgParameter (X n) (r n)))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hP)
  have hsC : Tendsto (fun n => C * (Real.sqrt (doubleAvgParameter (X n) (r n)))⁻¹)
      atTop (𝓝 0) := by simpa using hs.const_mul C
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsC
    (Filter.Eventually.of_forall ?_) (Filter.Eventually.of_forall ?_)
  · intro n
    unfold doubleAvgExceptions
    positivity
  · intro n
    have hn := (hbound (X n) (r n) (hr n) (hX n) (hrX n)).trans
      (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)
    refine (div_le_div_of_nonneg_right hn (by positivity)).trans_eq ?_
    rw [mul_div_assoc, doubleAvg_normalized_term (hr n) (hX n)]

end FareyGoldbach
