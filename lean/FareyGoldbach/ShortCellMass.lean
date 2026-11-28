import FareyGoldbach.ModelAndRemainder

/-! # Restricting a periodic cell mass to an arbitrary short arc -/

open Set MeasureTheory
open scoped Classical

namespace FareyGoldbach

noncomputable def shortCellMassDensity (Q : ℕ) (c : RatCenter) (f : ℝ → ℝ) : ℝ → ℝ :=
  (voronoiCell Q c).indicator (fun α => f (wrap (α - c.val)))

theorem shortCellMassDensity_intervalIntegrable (Q : ℕ) (c : RatCenter) {f : ℝ → ℝ}
    (hf : Continuous f) (hf₀ : ∀ t, 0 ≤ f t) (a b : ℝ) :
    IntervalIntegrable (shortCellMassDensity Q c f) volume a b := by
  have hmeas : Measurable (shortCellMassDensity Q c f) := by
    unfold shortCellMassDensity
    exact (hf.measurable.comp (measurable_wrap.comp (measurable_id.sub measurable_const))).indicator
      (voronoiCell_measurable Q c)
  obtain ⟨m, hm, hmax⟩ := (isCompact_Icc (a := -(1/2:ℝ)) (b := (1/2:ℝ))).exists_isMaxOn
    ⟨0, by norm_num⟩ hf.continuousOn
  refine intervalIntegrable_of_measurable_bounded (B := f m) hmeas fun x => ?_
  by_cases h : x ∈ voronoiCell Q c
  · rw [shortCellMassDensity, Set.indicator_of_mem h, Real.norm_of_nonneg (hf₀ _)]
    exact hmax (abs_le.mp (abs_wrap_le_half _))
  · rw [shortCellMassDensity, Set.indicator_of_notMem h, norm_zero]
    exact hf₀ m

set_option maxHeartbeats 1000000 in
/-- The integral over any arc of length at most one of the cell-restricted
lift is bounded by the integral of the local density over a centered rational arc. -/
theorem shortCellMassDensity_arc_le {Q : ℕ} (hQ : 3 ≤ Q) (c : RatCenter)
    {f : ℝ → ℝ} (hf : Continuous f) (hf₀ : ∀ β, 0 ≤ f β)
    {a b : ℝ} (hab : a ≤ b) (hb : b ≤ a+1) :
    (∫ α in a..b, shortCellMassDensity Q c f α) ≤
      ∫ β in -(3/(2*((c.q:ℝ)*Q)))..(3/(2*((c.q:ℝ)*Q))), f β := by
  let g := shortCellMassDensity Q c f
  let η : ℝ := 3/(2*((c.q:ℝ)*Q))
  have hqQ : 3 ≤ (c.q:ℝ)*Q := by
    have hq : 1 ≤ (c.q:ℝ) := Nat.one_le_cast.mpr c.q_pos
    have hQ' : (3:ℝ) ≤ Q := by exact_mod_cast hQ
    calc (3:ℝ) ≤ 1 * (Q:ℝ) := by simpa using hQ'
      _ ≤ _ := mul_le_mul_of_nonneg_right hq (by positivity)
  have hqQ' : 0 < (c.q:ℝ)*Q := by linarith
  have hη : 0 < η := by dsimp [η]; positivity
  have hη₂ : η ≤ 1/2 := (div_le_iff₀ (by positivity : 0 < 2*((c.q:ℝ)*Q))).2 (by linarith)
  have hper : Function.Periodic g 1 := by
    intro x
    simp only [g, shortCellMassDensity, Set.indicator_apply, voronoiCell_periodic,
      show x+1-c.val=x-c.val+1 by ring, wrap_add_one]
  have hg₀ (x : ℝ) : 0 ≤ g x := by
    simp only [g, shortCellMassDensity, Set.indicator_apply]
    split_ifs <;> [exact hf₀ _; exact le_rfl]
  have hgint (a b : ℝ) : IntervalIntegrable g volume a b :=
    shortCellMassDensity_intervalIntegrable Q c hf hf₀ a b
  calc (∫ α in a..b, g α) ≤ ∫ α in a..a+1, g α :=
      intervalIntegral.integral_mono_interval le_rfl hab hb
        (Filter.Eventually.of_forall hg₀) (hgint _ _)
    _ = ∫ α in (0:ℝ)..1, g α := by simpa using hper.intervalIntegral_add_eq a 0
    _ = ∫ β in (-(1/2):ℝ)..1/2, g (c.val+β) :=
      intervalIntegral_shift_symm hper c.val
    _ ≤ ∫ β in (-(1/2):ℝ)..1/2, (Ioc (-η) η).indicator f β := by
      have hi : IntervalIntegrable ((Ioc (-η) η).indicator f)
          volume (-(1/2):ℝ) (1/2:ℝ) := by
        rw [intervalIntegrable_iff]
        exact (hf.intervalIntegrable _ _).def'.indicator measurableSet_Ioc
      have hgshift : IntervalIntegrable (fun β ↦ g (c.val+β)) volume (-(1/2):ℝ) (1/2:ℝ) := by
        simpa only [add_sub_cancel_right] using
          (hgint (-(1/2)+c.val) (1/2+c.val)).comp_add_left c.val
      refine intervalIntegral.integral_mono_on (by norm_num) hgshift hi fun β hβ => ?_
      by_cases h : c.val+β ∈ voronoiCell Q c
      · have hβ₀ : |β| ≤ 1/2 := abs_le.mpr hβ
        have hbound := voronoiCell_outer_radius (show 0 < Q by omega) h
        rw [add_sub_cancel_left, abs_wrap_eq_abs_of_abs_le_half hβ₀] at hbound
        have hlt : |β| < η := hbound.trans_lt
          ((div_lt_div_iff_of_pos_right hqQ').2 (by norm_num : (1:ℝ) < 3/2) |>.trans_eq (by
            dsimp [η]; ring))
        have hi' : β ∈ Ioc (-η) η := ⟨(abs_lt.mp hlt).1, (abs_lt.mp hlt).2.le⟩
        dsimp only [g, shortCellMassDensity]
        rw [Set.indicator_of_mem h, Set.indicator_of_mem hi',
          add_sub_cancel_left, wrap_eq_self_of_abs_lt_half (hlt.trans_le hη₂)]
      · dsimp only [g, shortCellMassDensity]
        rw [Set.indicator_of_notMem h]
        exact Set.indicator_nonneg (fun β _ => hf₀ β) _
    _ = ∫ β in -η..η, f β := by
      rw [intervalIntegral.integral_of_le (by norm_num : -(1/2:ℝ) ≤ 1/2),
        intervalIntegral.integral_of_le (by linarith : -η ≤ η), MeasureTheory.setIntegral_indicator measurableSet_Ioc]
      rw [Set.inter_eq_right.mpr (Ioc_subset_Ioc (by linarith) hη₂)]

end FareyGoldbach
