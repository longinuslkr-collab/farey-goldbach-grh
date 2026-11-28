import FareyGoldbach.VoronoiCells

/-! # Local multiplicity of weighted Farey cells -/

namespace FareyGoldbach

/-- Centers whose assigned cell intersects the real interval, including both endpoints. -/
noncomputable def shortWindowCenters (Q : ℕ) (x δ : ℝ) : Finset RatCenter := by
  classical
  exact (centers Q).filter fun c => (Set.Icc (x-δ) (x+δ) ∩ voronoiCell Q c).Nonempty

private theorem window_center_radius {Q : ℕ} (hQ : 0<Q) {x δ : ℝ} {c : RatCenter}
    (hc : c ∈ shortWindowCenters Q x δ) : |wrap (c.val-x)| ≤ 1/((c.q:ℝ)*Q)+δ := by
  classical
  obtain ⟨y, hy, hyc⟩ := (Finset.mem_filter.mp hc).2
  have hcy := voronoiCell_outer_radius hQ hyc
  have hwrap := abs_wrap_le_abs_sub_int (y-x) 0
  simp only [Int.cast_zero,sub_zero] at hwrap
  have hyabs : |y-x| ≤ δ := abs_le.mpr ⟨by linarith [hy.1],by linarith [hy.2]⟩
  have htr := abs_wrap_triangle c.val y x
  rw [abs_wrap_sub_comm c.val y] at htr
  linarith only [htr,hcy,hwrap,hyabs]

/-- On the chosen lifts, ordinary distance is at least circular distance. -/
private theorem window_center_separation {a b : RatCenter} (hne : a ≠ b) (x : ℝ) :
    1/((a.q:ℝ)*b.q) ≤ |wrap (a.val-x)-wrap (b.val-x)| := by
  refine (ratCenter_separation hne).trans ?_
  have h := abs_wrap_le_abs_sub_int (a.val-b.val) (round (a.val-x)-round (b.val-x))
  have he : wrap (a.val-x)-wrap (b.val-x) = a.val-b.val-((round (a.val-x)-round (b.val-x):ℤ):ℝ) := by
    unfold wrap; push_cast; ring
  rw [he]; exact h

/-- At most nine distinct cells meet any closed interval of radius `δ ≤ Q⁻²`.
    At most one denominator is `≤ 7Q/20`. The other centers have scaled offsets in
    an interval of length `54/7 < 8`, with distance at least one between any two. -/
theorem shortWindowCenters_card_le_nine {Q : ℕ} (hQ : 2 ≤ Q) (x δ : ℝ)
    (hδQ : δ*(Q:ℝ)^2 ≤ 1) : (shortWindowCenters Q x δ).card ≤ 9 := by
  classical
  let S := shortWindowCenters Q x δ
  let isSmall := fun c : RatCenter => 20*(c.q:ℝ) ≤ 7*(Q:ℝ)
  let small := S.filter isSmall
  let large := S.filter fun c => ¬ isSmall c
  have hQ₀ : 0<Q := by omega
  have hQ' : (0:ℝ)<Q := Nat.cast_pos.mpr hQ₀
  have hcq (c : RatCenter) : (0:ℝ) < c.q := Nat.cast_pos.mpr c.q_pos
  have hsmall : small.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    by_contra hn
    obtain ⟨haS,haq⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbS,hbq⟩ := Finset.mem_filter.mp hb
    change 20*(a.q:ℝ) ≤ 7*(Q:ℝ) at haq
    change 20*(b.q:ℝ) ≤ 7*(Q:ℝ) at hbq
    have hsep := window_center_separation hn x
    have hax := window_center_radius hQ₀ haS
    have hbx := window_center_radius hQ₀ hbS
    have hfrac : 1/((a.q:ℝ)*b.q) ≤ 1/((a.q:ℝ)*Q)+1/((b.q:ℝ)*Q)+2*δ := by
      linarith only [hsep,hax,hbx,abs_sub (wrap (a.val-x)) (wrap (b.val-x))]
    have ha' := hcq a; have hb' := hcq b
    field_simp [ha'.ne',hb'.ne',hQ'.ne'] at hfrac
    have hmul := mul_le_mul haq hbq (by positivity) (by positivity)
    have hd := mul_le_mul_of_nonneg_left hδQ (mul_nonneg ha'.le hb'.le)
    have haQ := mul_le_mul_of_nonneg_right haq hQ'.le
    have hbQ := mul_le_mul_of_nonneg_right hbq hQ'.le
    have hfrac' := mul_le_mul_of_nonneg_right hfrac hQ'.le
    nlinarith only [hfrac',hmul,hd,haQ,hbQ,sq_pos_of_pos hQ']
  let pos := fun c : RatCenter => (Q:ℝ)^2*wrap (c.val-x) + 27/7
  have hrange (c : RatCenter) (hc : c ∈ large) : 0 ≤ pos c ∧ pos c < 8 := by
    obtain ⟨hcS,hcl⟩ := Finset.mem_filter.mp hc
    change ¬ 20*(c.q:ℝ) ≤ 7*(Q:ℝ) at hcl
    have hq := hcq c
    have hrat : (Q:ℝ)/c.q ≤ 20/7 := (div_le_div_iff₀ hq (by norm_num)).2 (by linarith)
    have hs := mul_le_mul_of_nonneg_left (window_center_radius hQ₀ hcS) (sq_nonneg (Q:ℝ))
    have he : (Q:ℝ)^2 * (1/((c.q:ℝ)*Q)) = (Q:ℝ)/c.q := by field_simp
    rw [mul_add,he] at hs
    have habs : |(Q:ℝ)^2 * wrap (c.val-x)| ≤ 27/7 := by
      rw [abs_mul,abs_of_nonneg (sq_nonneg (Q:ℝ))]; linarith
    dsimp [pos]; constructor <;> linarith only [(abs_le.mp habs).1,(abs_le.mp habs).2]
  let bin := fun c : RatCenter => ⌊pos c⌋₊
  have hinj : Set.InjOn bin large := by
    intro a ha b hb he
    by_contra hn
    have haS := (Finset.mem_filter.mp ha).1; have hbS := (Finset.mem_filter.mp hb).1
    have haQ : (a.q:ℝ) ≤ Q := Nat.cast_le.mpr (mem_centers_iff.mp (Finset.mem_filter.mp haS).1)
    have hbQ : (b.q:ℝ) ≤ Q := Nat.cast_le.mpr (mem_centers_iff.mp (Finset.mem_filter.mp hbS).1)
    have hden := mul_le_mul haQ hbQ (hcq b).le hQ'.le
    have hsep := window_center_separation hn x
    have hscaled : 1 ≤ (Q:ℝ)^2 * |wrap (a.val-x)-wrap (b.val-x)| := by
      have e := (div_le_iff₀ (mul_pos (hcq a) (hcq b))).1 hsep
      nlinarith only [e,mul_le_mul_of_nonneg_right hden (abs_nonneg (wrap (a.val-x)-wrap (b.val-x)))]
    have hposabs : 1 ≤ |pos a - pos b| := by
      have heq : pos a - pos b = (Q:ℝ)^2*(wrap (a.val-x)-wrap (b.val-x)) := by dsimp [pos]; ring
      rw [heq,abs_mul,abs_of_nonneg (sq_nonneg (Q:ℝ))]; exact hscaled
    have hloA := Nat.floor_le (hrange a ha).1; have hloB := Nat.floor_le (hrange b hb).1
    have hhiA := Nat.lt_floor_add_one (pos a); have hhiB := Nat.lt_floor_add_one (pos b)
    change ⌊pos a⌋₊ = ⌊pos b⌋₊ at he
    rw [he] at hloA hhiA
    exact (not_lt_of_ge hposabs) (abs_lt.mpr ⟨by linarith only [hloA,hhiB],by linarith only [hloB,hhiA]⟩)
  have hsub : large.image bin ⊆ Finset.range 8 := by
    intro i hi
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hi
    apply Finset.mem_range.mpr
    exact (Nat.floor_lt (hrange c hc).1).2 (by exact_mod_cast (hrange c hc).2)
  have hlarge : large.card ≤ 8 := by
    rw [←Finset.card_image_of_injOn hinj]; exact (Finset.card_le_card hsub).trans (by simp)
  have heq : small ∪ large = S := Finset.filter_union_filter_not_eq ..
  change S.card ≤ 9
  rw [←heq]; exact (Finset.card_union_le _ _).trans (by omega)

end FareyGoldbach
