import FareyGoldbach.Defs
import FareyGoldbach.CharacterBound
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Function.Floor

/-!
# Module B2: Weighted Voronoi Cells (Bypassing Farey Mediant Combinatorics)

For a cutoff `Q ≥ 1`, we partition `ℝ` (1-periodically) into measurable cells `voronoiCell Q c`
indexed by reduced fractions `c = a / q` with `0 ≤ a < q ≤ Q`, assigning each `α : ℝ` to the
center minimizing `q * |wrap (α - a / q)|` (tie-broken lexicographically by `(q, a)`).

Key results (all proved with zero `sorry`):
- `voronoiCell_measurable`: every cell is Borel measurable.
- `voronoiCell_pairwiseDisjoint` & `voronoiCell_cover`: exact partition of `ℝ`.
- `voronoiCell_outer_radius`: `α ∈ voronoiCell Q c → |wrap (α - c.val)| ≤ 1 / (c.q * Q)`.
- `voronoiCell_inner_radius`: `|wrap (α - c.val)| < 1 / (2 * c.q * Q) → α ∈ voronoiCell Q c`.
- `voronoiCell_periodic`: `α + 1 ∈ voronoiCell Q c ↔ α ∈ voronoiCell Q c`.
- `voronoiCell_beta_subset_outer` & `voronoiCell_inner_subset_beta`: exact `β`-coordinate
  sandwich on `[-1/2, 1/2]`.
-/

open scoped BigOperators

namespace FareyGoldbach

section WrapModOne

/-- Signed distance to the nearest integer: `wrap t = t - round t ∈ [-1/2, 1/2]`. -/
noncomputable def wrap (t : ℝ) : ℝ := t - (round t : ℝ)

lemma abs_wrap_le_half (t : ℝ) : |wrap t| ≤ 1 / 2 :=
  abs_sub_round t

lemma abs_wrap_le_abs_sub_int (t : ℝ) (k : ℤ) : |wrap t| ≤ |t - (k : ℝ)| :=
  round_le t k

lemma wrap_add_int (t : ℝ) (k : ℤ) : wrap (t + (k : ℝ)) = wrap t := by
  unfold wrap
  rw [round_add_intCast]
  push_cast
  ring

lemma wrap_sub_int (t : ℝ) (k : ℤ) : wrap (t - (k : ℝ)) = wrap t := by
  simpa [sub_eq_add_neg] using wrap_add_int t (-k)

lemma wrap_add_one (t : ℝ) : wrap (t + 1) = wrap t := by
  simpa using wrap_add_int t 1

lemma abs_wrap_neg (t : ℝ) : |wrap (-t)| = |wrap t| := by
  apply le_antisymm
  · have h := abs_wrap_le_abs_sub_int (-t) (-(round t))
    calc |wrap (-t)| ≤ |-t - (-(round t : ℤ) : ℝ)| := h
      _ = |-(t - (round t : ℝ))| := by ring_nf
      _ = |wrap t| := by rw [abs_neg]; rfl
  · have h := abs_wrap_le_abs_sub_int t (-(round (-t)))
    calc |wrap t| ≤ |t - (-(round (-t) : ℤ) : ℝ)| := h
      _ = |-((-t) - (round (-t) : ℝ))| := by ring_nf
      _ = |wrap (-t)| := by rw [abs_neg]; rfl

lemma abs_wrap_sub_comm (x y : ℝ) : |wrap (x - y)| = |wrap (y - x)| := by
  rw [← abs_wrap_neg (x - y), neg_sub]

lemma abs_wrap_add_le (x y : ℝ) : |wrap (x + y)| ≤ |wrap x| + |wrap y| := by
  have h := abs_wrap_le_abs_sub_int (x + y) (round x + round y)
  calc |wrap (x + y)| ≤ |x + y - ((round x + round y : ℤ) : ℝ)| := h
    _ = |wrap x + wrap y| := by unfold wrap; push_cast; ring_nf
    _ ≤ |wrap x| + |wrap y| := abs_add_le _ _

lemma abs_wrap_triangle (x y z : ℝ) : |wrap (x - z)| ≤ |wrap (x - y)| + |wrap (y - z)| := by
  have h : x - z = (x - y) + (y - z) := by ring
  rw [h]
  exact abs_wrap_add_le (x - y) (y - z)

lemma e_wrap (t : ℝ) : e (wrap t) = e t := by
  unfold wrap
  exact (e_eq_of_sub_int (k := -(round t)) (by push_cast; ring))

lemma wrap_eq_self_of_abs_lt_half {t : ℝ} (ht : |t| < 1 / 2) : wrap t = t := by
  unfold wrap
  have hr : round t = 0 := by
    rw [round_eq_zero_iff]
    exact ⟨by linarith [(abs_lt.mp ht).1], (abs_lt.mp ht).2⟩
  simp [hr]

lemma abs_wrap_eq_abs_of_abs_le_half {t : ℝ} (ht : |t| ≤ 1 / 2) : |wrap t| = |t| := by
  rcases lt_or_eq_of_le ht with hlt | heq
  · rw [wrap_eq_self_of_abs_lt_half hlt]
  · rcases eq_or_eq_neg_of_abs_eq heq with rfl | rfl
    · have hr : round (1 / 2 : ℝ) = 1 := by
        rw [round_eq]
        norm_num
      unfold wrap
      rw [hr]
      norm_num
    · have hr : round (-(1 / 2 : ℝ)) = 0 := by
        rw [round_eq]
        norm_num
      unfold wrap
      rw [hr]
      norm_num

lemma measurable_wrap : Measurable wrap := by
  unfold wrap
  have hfloor : Measurable (fun t : ℝ => (⌊t + 1 / 2⌋ : ℤ)) :=
    Int.measurable_floor.comp (measurable_id.add measurable_const)
  have hround : Measurable (fun t : ℝ => (round t : ℝ)) := by
    have heq : (fun t : ℝ => (round t : ℝ)) = fun t : ℝ => ((⌊t + 1 / 2⌋ : ℤ) : ℝ) := by
      funext t
      rw [round_eq]
    rw [heq]
    exact measurable_from_top.comp hfloor
  exact measurable_id.sub hround

end WrapModOne

section RatCenters

/-- Reduced rational center `a / q` in `[0, 1)` with `0 ≤ a < q` and `gcd(a, q) = 1`. -/
@[ext]
structure RatCenter where
  a : ℕ
  q : ℕ
  q_pos : 0 < q
  a_lt : a < q
  coprime : Nat.Coprime a q
  deriving DecidableEq

/-- Value of a rational center as a real number in `[0, 1)`. -/
noncomputable def RatCenter.val (c : RatCenter) : ℝ := (c.a : ℝ) / (c.q : ℝ)

/-- Canonical `0 / 1` center. -/
def RatCenter.zero : RatCenter :=
  ⟨0, 1, one_pos, one_pos, (Nat.coprime_zero_left 1).2 rfl⟩

/-- Lexicographic total order on `RatCenter` via `(q, a)` for deterministic tie-breaking. -/
instance : LinearOrder RatCenter :=
  LinearOrder.lift' (fun c : RatCenter => toLex (c.q, c.a)) fun c₁ c₂ h => by
    have hp : (c₁.q, c₁.a) = (c₂.q, c₂.a) := by simpa using h
    exact RatCenter.ext (congrArg Prod.snd hp) (congrArg Prod.fst hp)

/-- Finite set of all reduced rational centers with denominator `1 ≤ q ≤ Q`. -/
def centers (Q : ℕ) : Finset RatCenter :=
  ((Finset.Icc 1 Q).biUnion fun q =>
    ((Finset.range q).filter fun a => Nat.Coprime a q).attach.image fun ⟨a, ha⟩ =>
      { a := a
        q := q
        q_pos := by
          have h := (Finset.mem_filter.mp ha).1
          exact Nat.pos_of_ne_zero (by intro hq; simp [hq] at h)
        a_lt := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
        coprime := (Finset.mem_filter.mp ha).2 })

lemma mem_centers_iff {Q : ℕ} {c : RatCenter} : c ∈ centers Q ↔ c.q ≤ Q := by
  unfold centers
  simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image, Finset.mem_attach, true_and,
    Subtype.exists, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨q, ⟨_, hqQ⟩, a, ⟨_, _⟩, rfl⟩
    exact hqQ
  · intro hcQ
    exact ⟨c.q, ⟨c.q_pos, hcQ⟩, c.a, ⟨c.a_lt, c.coprime⟩, rfl⟩

lemma zero_mem_centers {Q : ℕ} (hQ : 0 < Q) : RatCenter.zero ∈ centers Q := by
  rw [mem_centers_iff]
  exact hQ

lemma centers_nonempty {Q : ℕ} (hQ : 0 < Q) : (centers Q).Nonempty :=
  ⟨RatCenter.zero, zero_mem_centers hQ⟩

/-- Distinct reduced centers in `[0, 1)` are separated mod 1 by at least `1 / (q₁ * q₂)`. -/
lemma ratCenter_separation {c₁ c₂ : RatCenter} (hne : c₁ ≠ c₂) :
    1 / ((c₁.q : ℝ) * (c₂.q : ℝ)) ≤ |wrap (c₁.val - c₂.val)| := by
  unfold wrap RatCenter.val
  set k : ℤ := round ((c₁.a : ℝ) / (c₁.q : ℝ) - (c₂.a : ℝ) / (c₂.q : ℝ))
  have hq1 : (0 : ℝ) < c₁.q := Nat.cast_pos.mpr c₁.q_pos
  have hq2 : (0 : ℝ) < c₂.q := Nat.cast_pos.mpr c₂.q_pos
  set num : ℤ := (c₁.a : ℤ) * (c₂.q : ℤ) - (c₂.a : ℤ) * (c₁.q : ℤ) - k * ((c₁.q : ℤ) * (c₂.q : ℤ))
  have hfrac : (c₁.a : ℝ) / (c₁.q : ℝ) - (c₂.a : ℝ) / (c₂.q : ℝ) - (k : ℝ) =
      (num : ℝ) / ((c₁.q : ℝ) * (c₂.q : ℝ)) := by
    simp only [num]
    push_cast
    field_simp [hq1.ne', hq2.ne']
  have hnum_ne : num ≠ 0 := by
    intro hzero
    -- If `num = 0`, then `c₁.a / c₁.q - c₂.a / c₂.q = k ∈ ℤ`.
    have hdiff : (c₁.a : ℝ) / (c₁.q : ℝ) - (c₂.a : ℝ) / (c₂.q : ℝ) = (k : ℝ) := by
      have h0 : (num : ℝ) / ((c₁.q : ℝ) * (c₂.q : ℝ)) = 0 := by simp [hzero]
      linarith [hfrac.trans h0]
    have h1lt : (c₁.a : ℝ) / (c₁.q : ℝ) < 1 := (div_lt_one hq1).2 (Nat.cast_lt.mpr c₁.a_lt)
    have h2lt : (c₂.a : ℝ) / (c₂.q : ℝ) < 1 := (div_lt_one hq2).2 (Nat.cast_lt.mpr c₂.a_lt)
    have h1nn : 0 ≤ (c₁.a : ℝ) / (c₁.q : ℝ) := div_nonneg (Nat.cast_nonneg _) hq1.le
    have h2nn : 0 ≤ (c₂.a : ℝ) / (c₂.q : ℝ) := div_nonneg (Nat.cast_nonneg _) hq2.le
    have hk_lt : (k : ℝ) < 1 := by linarith
    have hk_gt : (-1 : ℝ) < (k : ℝ) := by linarith
    have hk_zero : k = 0 := by
      have hk1 : k < 1 := by exact_mod_cast hk_lt
      have hk2 : -1 < k := by exact_mod_cast hk_gt
      omega
    have hcross_real : (c₁.a : ℝ) * (c₂.q : ℝ) = (c₂.a : ℝ) * (c₁.q : ℝ) := by
      have h0 : (c₁.a : ℝ) / (c₁.q : ℝ) = (c₂.a : ℝ) / (c₂.q : ℝ) := by
        rw [hk_zero] at hdiff; simp at hdiff; linarith
      exact (div_eq_div_iff hq1.ne' hq2.ne').1 h0
    have hcross : c₁.a * c₂.q = c₂.a * c₁.q := by exact_mod_cast hcross_real
    have hq1_dvd : c₁.q ∣ c₂.q := by
      have h : c₁.q ∣ c₁.a * c₂.q := ⟨c₂.a, by linarith⟩
      exact c₁.coprime.symm.dvd_of_dvd_mul_left h
    have hq2_dvd : c₂.q ∣ c₁.q := by
      have h : c₂.q ∣ c₂.a * c₁.q := ⟨c₁.a, by linarith⟩
      exact c₂.coprime.symm.dvd_of_dvd_mul_left h
    have hq_eq : c₁.q = c₂.q := Nat.dvd_antisymm hq1_dvd hq2_dvd
    have ha_eq : c₁.a = c₂.a := by
      rw [hq_eq] at hcross
      exact Nat.eq_of_mul_eq_mul_right c₂.q_pos hcross
    exact hne (RatCenter.ext ha_eq hq_eq)
  have hnum_ge : (1 : ℝ) ≤ |(num : ℝ)| := by
    have : (1 : ℤ) ≤ |num| := Int.one_le_abs hnum_ne
    exact_mod_cast this
  rw [hfrac, abs_div, abs_of_pos (mul_pos hq1 hq2)]
  exact div_le_div_of_nonneg_right hnum_ge (mul_pos hq1 hq2).le

/-- Dirichlet's approximation theorem into `centers Q`. -/
lemma exists_center_weighted_le (Q : ℕ) (hQ : 0 < Q) (α : ℝ) :
    ∃ c ∈ centers Q, (c.q : ℝ) * |wrap (α - c.val)| ≤ 1 / (Q : ℝ) := by
  obtain ⟨r, hr_dist, hr_den⟩ := Real.exists_rat_abs_sub_le_and_den_le α hQ
  let q : ℕ := r.den
  have hq_pos : 0 < q := r.pos
  let a : ℕ := Int.toNat (r.num % (q : ℤ))
  have ha_lt : a < q := by
    have h1 : 0 ≤ r.num % (q : ℤ) := Int.emod_nonneg _ (Int.ofNat_ne_zero.mpr hq_pos.ne')
    have h2 : r.num % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos _ (Int.natCast_pos.mpr hq_pos)
    omega
  have ha_cast : (a : ℤ) = r.num % (q : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.ofNat_ne_zero.mpr hq_pos.ne'))
  have ha_cop : Nat.Coprime a q := by
    have hred : Nat.Coprime r.num.natAbs q := r.reduced
    have hg : Int.gcd (r.num % (q : ℤ)) (q : ℤ) = Int.gcd r.num (q : ℤ) := by
      rw [Int.gcd_emod]
    have h1 : Nat.gcd a q = Int.gcd (a : ℤ) (q : ℤ) := rfl
    rw [Nat.Coprime, h1, ha_cast, hg]
    simpa [Int.gcd] using hred
  let c : RatCenter := ⟨a, q, hq_pos, ha_lt, ha_cop⟩
  refine ⟨c, mem_centers_iff.mpr hr_den, ?_⟩
  -- Compare `α - c.val` with `α - r`: they differ by an integer `r.num / q`!
  let k : ℤ := r.num / (q : ℤ)
  have hnum_split : r.num = (q : ℤ) * k + (a : ℤ) := by
    rw [ha_cast]
    exact (Int.mul_ediv_add_emod r.num (q : ℤ)).symm
  have hrat_eq : (r : ℝ) = c.val + (k : ℝ) := by
    have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq_pos.ne'
    rw [Rat.cast_def]
    change (r.num : ℝ) / (q : ℝ) = (a : ℝ) / (q : ℝ) + (k : ℝ)
    have hnumR : (r.num : ℝ) = (q : ℝ) * (k : ℝ) + (a : ℝ) := by exact_mod_cast hnum_split
    rw [hnumR]
    field_simp [hqR]
    ring
  have hwrap_le : |wrap (α - c.val)| ≤ |α - (r : ℝ)| := by
    have hsub : α - c.val - (k : ℝ) = α - (r : ℝ) := by linarith [hrat_eq]
    rw [← hsub]
    exact abs_wrap_le_abs_sub_int (α - c.val) k
  have hQ_pos : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have hq_posR : (0 : ℝ) < q := Nat.cast_pos.mpr hq_pos
  calc (c.q : ℝ) * |wrap (α - c.val)|
      ≤ (q : ℝ) * |α - (r : ℝ)| := mul_le_mul_of_nonneg_left hwrap_le hq_posR.le
    _ ≤ (q : ℝ) * (1 / (((Q : ℝ) + 1) * (q : ℝ))) :=
        mul_le_mul_of_nonneg_left hr_dist hq_posR.le
    _ = 1 / ((Q : ℝ) + 1) := by field_simp [hq_posR.ne', (by linarith : (Q : ℝ) + 1 ≠ 0)]
    _ ≤ 1 / (Q : ℝ) := by
        exact one_div_le_one_div_of_le hQ_pos (by linarith)

end RatCenters

section VoronoiPartition

/-- Weighted distance from `α` to center `c`: `q * |wrap (α - a / q)|`. -/
noncomputable def weightedDist (c : RatCenter) (α : ℝ) : ℝ :=
  (c.q : ℝ) * |wrap (α - c.val)|

lemma measurable_weightedDist (c : RatCenter) : Measurable (weightedDist c) := by
  unfold weightedDist
  exact measurable_const.mul
    (continuous_abs.measurable.comp (measurable_wrap.comp (measurable_id.sub measurable_const)))

/-- The weighted Voronoi cell of center `c` at level `Q`:
`α ∈ voronoiCell Q c` iff `c ∈ centers Q` minimizes `weightedDist c α` with lexicographic
tie-breaking by `c ≤ c'`. -/
def voronoiCell (Q : ℕ) (c : RatCenter) : Set ℝ :=
  {α : ℝ | c ∈ centers Q ∧ ∀ c' ∈ centers Q,
    weightedDist c α < weightedDist c' α ∨ (weightedDist c α = weightedDist c' α ∧ c ≤ c')}

lemma voronoiCell_measurable (Q : ℕ) (c : RatCenter) : MeasurableSet (voronoiCell Q c) := by
  unfold voronoiCell
  by_cases hc : c ∈ centers Q
  · have hEq : {α : ℝ | c ∈ centers Q ∧ ∀ c' ∈ centers Q,
        weightedDist c α < weightedDist c' α ∨ (weightedDist c α = weightedDist c' α ∧ c ≤ c')} =
        ⋂ c' ∈ centers Q,
          ({α : ℝ | weightedDist c α < weightedDist c' α} ∪
            ({α : ℝ | weightedDist c α = weightedDist c' α} ∩ {α : ℝ | c ≤ c'})) := by
      ext α
      simp [hc]
    rw [hEq]
    refine MeasurableSet.biInter (centers Q).countable_toSet fun c' _ => ?_
    refine MeasurableSet.union ?_ (MeasurableSet.inter ?_ ?_)
    · exact measurableSet_lt (measurable_weightedDist c) (measurable_weightedDist c')
    · exact measurableSet_eq_fun (measurable_weightedDist c) (measurable_weightedDist c')
    · by_cases hle : c ≤ c' <;> simp [hle]
  · have hEq : {α : ℝ | c ∈ centers Q ∧ ∀ c' ∈ centers Q,
        weightedDist c α < weightedDist c' α ∨ (weightedDist c α = weightedDist c' α ∧ c ≤ c')} = ∅ := by
      ext α; simp [hc]
    rw [hEq]
    exact MeasurableSet.empty

lemma voronoiCell_periodic (Q : ℕ) (c : RatCenter) (α : ℝ) :
    α + 1 ∈ voronoiCell Q c ↔ α ∈ voronoiCell Q c := by
  have hwd : ∀ c' : RatCenter, weightedDist c' (α + 1) = weightedDist c' α := by
    intro c'
    unfold weightedDist
    have h : α + 1 - c'.val = (α - c'.val) + 1 := by ring
    rw [h, wrap_add_one]
  simp only [voronoiCell, Set.mem_ofPred_eq, hwd]

lemma voronoiCell_disjoint {Q : ℕ} {c₁ c₂ : RatCenter} (hne : c₁ ≠ c₂) :
    Disjoint (voronoiCell Q c₁) (voronoiCell Q c₂) := by
  rw [Set.disjoint_left]
  intro α h1 h2
  have h12 := h1.2 c₂ h2.1
  have h21 := h2.2 c₁ h1.1
  rcases h12 with hlt | ⟨heq, hle12⟩
  · rcases h21 with hlt' | ⟨heq', _⟩
    · linarith
    · linarith
  · rcases h21 with hlt' | ⟨_, hle21⟩
    · linarith
    · exact hne (le_antisymm hle12 hle21)

lemma voronoiCell_cover (Q : ℕ) (hQ : 0 < Q) (α : ℝ) :
    ∃ c ∈ centers Q, α ∈ voronoiCell Q c := by
  -- First pick the minimum weighted distance on the finite nonempty set `centers Q`.
  obtain ⟨c₀, hc₀, hmin⟩ := (centers Q).exists_min_image (fun c => weightedDist c α)
    (centers_nonempty hQ)
  -- Among all minimizers, pick the lexicographically smallest center `c`.
  let ties : Finset RatCenter :=
    (centers Q).filter fun c => weightedDist c α = weightedDist c₀ α
  have hties_ne : ties.Nonempty := ⟨c₀, Finset.mem_filter.mpr ⟨hc₀, rfl⟩⟩
  let c : RatCenter := ties.min' hties_ne
  have hc_mem_ties : c ∈ ties := Finset.min'_mem ties hties_ne
  have hc_mem : c ∈ centers Q := (Finset.mem_filter.mp hc_mem_ties).1
  have hc_val : weightedDist c α = weightedDist c₀ α := (Finset.mem_filter.mp hc_mem_ties).2
  refine ⟨c, hc_mem, hc_mem, ?_⟩
  intro c' hc'
  have hle : weightedDist c α ≤ weightedDist c' α := by
    rw [hc_val]; exact hmin c' hc'
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr ⟨heq, ?_⟩
    have hc'_ties : c' ∈ ties := Finset.mem_filter.mpr ⟨hc', heq.symm.trans hc_val⟩
    exact Finset.min'_le ties c' hc'_ties

/-- **Theorem B2.1 (Outer radius):** Every `α ∈ voronoiCell Q c` satisfies
`|wrap (α - c.val)| ≤ 1 / (c.q * Q)`. -/
theorem voronoiCell_outer_radius {Q : ℕ} (hQ : 0 < Q) {c : RatCenter} {α : ℝ}
    (hα : α ∈ voronoiCell Q c) :
    |wrap (α - c.val)| ≤ 1 / ((c.q : ℝ) * (Q : ℝ)) := by
  obtain ⟨c₀, hc₀, hdir⟩ := exists_center_weighted_le Q hQ α
  have hle : weightedDist c α ≤ weightedDist c₀ α := by
    rcases hα.2 c₀ hc₀ with hlt | ⟨heq, _⟩ <;> linarith
  have hq : (0 : ℝ) < c.q := Nat.cast_pos.mpr c.q_pos
  have h1 : (c.q : ℝ) * |wrap (α - c.val)| ≤ 1 / (Q : ℝ) := hle.trans hdir
  rw [le_div_iff₀ (mul_pos hq (Nat.cast_pos.mpr hQ))]
  have hQpos : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have h2 := (le_div_iff₀ hQpos).1 h1
  nlinarith

/-- **Theorem B2.2 (Inner radius):** If `|wrap (α - c.val)| < 1 / (2 * c.q * Q)` and `c ∈ centers Q`,
then `α ∈ voronoiCell Q c`. -/
theorem voronoiCell_inner_radius {Q : ℕ} (hQ : 0 < Q) {c : RatCenter} (hc : c ∈ centers Q)
    {α : ℝ} (hdist : |wrap (α - c.val)| < 1 / (2 * (c.q : ℝ) * (Q : ℝ))) :
    α ∈ voronoiCell Q c := by
  refine ⟨hc, fun c' hc' => ?_⟩
  by_cases hEq : c = c'
  · subst hEq; exact Or.inr ⟨rfl, le_refl _⟩
  · left
    have hq : (0 : ℝ) < c.q := Nat.cast_pos.mpr c.q_pos
    have hq' : (0 : ℝ) < c'.q := Nat.cast_pos.mpr c'.q_pos
    have hQpos : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
    have hcq : (c.q : ℝ) ≤ Q := Nat.cast_le.mpr (mem_centers_iff.mp hc)
    have hcq' : (c'.q : ℝ) ≤ Q := Nat.cast_le.mpr (mem_centers_iff.mp hc')
    -- Home weighted distance `< 1 / (2 * Q)`.
    have hhome : weightedDist c α < 1 / (2 * (Q : ℝ)) := by
      unfold weightedDist
      calc (c.q : ℝ) * |wrap (α - c.val)|
          < (c.q : ℝ) * (1 / (2 * (c.q : ℝ) * (Q : ℝ))) := mul_lt_mul_of_pos_left hdist hq
        _ = 1 / (2 * (Q : ℝ)) := by field_simp [hq.ne', hQpos.ne']
    -- Rival distance via separation `|wrap (c.val - c'.val)| ≥ 1 / (c.q * c'.q)`.
    have hsep := ratCenter_separation hEq
    have htri := abs_wrap_triangle c.val α c'.val
    rw [abs_wrap_sub_comm c.val α] at htri
    have hrival_dist : 1 / ((c.q : ℝ) * (c'.q : ℝ)) - 1 / (2 * (c.q : ℝ) * (Q : ℝ)) <
        |wrap (α - c'.val)| := by
      linarith
    have hrival : 1 / (2 * (Q : ℝ)) < weightedDist c' α := by
      unfold weightedDist
      have h1 : (c'.q : ℝ) * (1 / ((c.q : ℝ) * (c'.q : ℝ)) - 1 / (2 * (c.q : ℝ) * (Q : ℝ))) <
          (c'.q : ℝ) * |wrap (α - c'.val)| := mul_lt_mul_of_pos_left hrival_dist hq'
      have h2 : (c'.q : ℝ) * (1 / ((c.q : ℝ) * (c'.q : ℝ)) - 1 / (2 * (c.q : ℝ) * (Q : ℝ))) =
          (1 / (c.q : ℝ)) * (1 - (c'.q : ℝ) / (2 * (Q : ℝ))) := by
        field_simp [hq.ne', hq'.ne', hQpos.ne']
      have h3 : (1 : ℝ) / 2 ≤ 1 - (c'.q : ℝ) / (2 * (Q : ℝ)) := by
        have : (c'.q : ℝ) / (2 * (Q : ℝ)) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by positivity) two_pos]
          linarith
        linarith
      have h4 : 1 / (2 * (Q : ℝ)) ≤ (1 / (c.q : ℝ)) * (1 / 2) := by
        have hinv : (1 : ℝ) / (Q : ℝ) ≤ 1 / (c.q : ℝ) := one_div_le_one_div_of_le hq hcq
        have heq : (1 : ℝ) / (2 * (Q : ℝ)) = (1 / (Q : ℝ)) * (1 / 2) := by ring
        rw [heq]
        linarith
      have h5 : (1 / (c.q : ℝ)) * (1 / 2) ≤ (1 / (c.q : ℝ)) * (1 - (c'.q : ℝ) / (2 * (Q : ℝ))) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      linarith
    exact hhome.trans hrival

/-- Coordinate sandwich on `β ∈ [-1/2, 1/2]`: inner arc lies inside cell, cell lies inside outer arc. -/
lemma voronoiCell_beta_subset_outer {Q : ℕ} (hQ : 0 < Q) {c : RatCenter} {β : ℝ}
    (hβ : |β| ≤ 1 / 2) (hmem : c.val + β ∈ voronoiCell Q c) :
    |β| ≤ 1 / ((c.q : ℝ) * (Q : ℝ)) := by
  have hout := voronoiCell_outer_radius hQ hmem
  have hsub : c.val + β - c.val = β := by ring
  rw [hsub, abs_wrap_eq_abs_of_abs_le_half hβ] at hout
  exact hout

lemma voronoiCell_inner_subset_beta {Q : ℕ} (hQ : 0 < Q) {c : RatCenter} (hc : c ∈ centers Q)
    {β : ℝ} (hβ : |β| < 1 / (2 * (c.q : ℝ) * (Q : ℝ))) :
    c.val + β ∈ voronoiCell Q c := by
  apply voronoiCell_inner_radius hQ hc
  have hsub : c.val + β - c.val = β := by ring
  rw [hsub]
  have hq : (1 : ℝ) ≤ c.q := Nat.one_le_cast.mpr c.q_pos
  have hQ1 : (1 : ℝ) ≤ Q := Nat.one_le_cast.mpr hQ
  have hhalf : |β| ≤ 1 / 2 := by
    have : 1 / (2 * (c.q : ℝ) * (Q : ℝ)) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le two_pos
      nlinarith
    linarith
  rw [abs_wrap_eq_abs_of_abs_le_half hhalf]
  exact hβ

end VoronoiPartition

end FareyGoldbach
