import FareyGoldbach.DoubleAverageGoldbach

/-! # Single-average dyadic estimates and their global summation -/

open scoped BigOperators Classical
open Real

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

namespace FareyGoldbach

abbrev ReducedClass (r : ℕ) := {b // b ∈ coprimeClasses r}

private def classPair {r : ℕ} (hr : 0 < r) (b₁ b₂ : ReducedClass r) : Progressions :=
  ⟨r, hr, b₁.1, b₂.1, (mem_coprimeClasses.mp b₁.2).1, (mem_coprimeClasses.mp b₂.2).1,
    (mem_coprimeClasses.mp b₁.2).2, (mem_coprimeClasses.mp b₂.2).2⟩

noncomputable def singleAvgExceptions (X r : ℕ) (hr : 0 < r) (b₁ : ReducedClass r) : ℝ :=
  (1 / (r.totient : ℝ)) * ∑ b₂ ∈ (coprimeClasses r).attach,
    ((exceptions (classPair hr b₁ b₂) X).card : ℝ)

noncomputable def singleAvgDyadicExceptions (Y r : ℕ) (hr : 0 < r) (b₁ : ReducedClass r) : ℝ :=
  (1 / (r.totient : ℝ)) * ∑ b₂ ∈ (coprimeClasses r).attach,
    ((dyadicExceptions (classPair hr b₁ b₂) Y).card : ℝ)

/-- The analytic input is needed only on active dyadic blocks. -/
def SingleAverageDyadicBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ {r Y : ℕ} (hr : 0 < r) (b₁ : ReducedClass r),
      2 ^ 72 ≤ Y / r →
      ((r.totient : ℝ) / (r : ℝ)) ^ 2 * (r : ℝ) * Real.log (2 * (Y : ℝ)) ^ 2 ≤ (Y : ℝ) / (r : ℝ) →
      ∀ D : ℕ, 1 ≤ D →
      let H := (Y : ℝ) / (r : ℝ)
      let L := Real.log (2 * (Y : ℝ))
      let a := (r.totient : ℝ) / (r : ℝ)
      singleAvgDyadicExceptions Y r hr b₁ ≤ C * (a ^ 2 * Real.sqrt H * L ^ 3 +
        min (a ^ 2 * r * L ^ 2 * Real.log (2 * (D : ℝ)) + a * H * L / (D : ℝ) ^ 2)
          (a ^ 3 * r * L ^ 3))

private theorem exceptions_card_le {r : ℕ} (hr : 0 < r) (b₁ b₂ : ReducedClass r) (X : ℕ) :
    ((exceptions (classPair hr b₁ b₂) X).card : ℝ) ≤ (X : ℝ) / r + 1 := by
  let P := classPair hr b₁ b₂
  have hs : exceptions P X ⊆ (Finset.Icc 1 X).filter (fun n => n % r = (P.b₁ + P.b₂) % r) :=
    fun _ hn => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1, (Finset.mem_filter.mp hn).2.2.1⟩
  have hc := (Finset.card_le_card hs).trans (card_congruence_Icc_le X r _ hr)
  have hd : ((X / r : ℕ) : ℝ) ≤ (X : ℝ) / r := by
    rw [le_div_iff₀ (Nat.cast_pos.mpr hr)]; exact_mod_cast (by simpa [mul_comm] using Nat.mul_div_le X r)
  have hc' : ((exceptions P X).card : ℝ) ≤ ((X / r : ℕ) : ℝ) + 1 := by exact_mod_cast hc
  exact hc'.trans (by linarith)

theorem singleAvgExceptions_trivial {r : ℕ} (hr : 0 < r) (b₁ : ReducedClass r) (X : ℕ) :
    singleAvgExceptions X r hr b₁ ≤ (X : ℝ) / r + 1 := by
  have hp : (0 : ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  unfold singleAvgExceptions
  calc _ ≤ (1 / (r.totient : ℝ)) * ∑ _b₂ ∈ (coprimeClasses r).attach, ((X : ℝ) / r + 1) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b₂ _ => exceptions_card_le hr b₁ b₂ X) (by positivity)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_attach, card_coprimeClasses]; field_simp

private theorem singleAvg_step {r : ℕ} (hr : 0 < r) (b₁ : ReducedClass r) (Y : ℕ) :
    singleAvgExceptions Y r hr b₁ ≤ singleAvgExceptions (Y / 2) r hr b₁ + singleAvgDyadicExceptions Y r hr b₁ := by
  unfold singleAvgExceptions singleAvgDyadicExceptions
  rw [← mul_add, ← Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b₂ _ => ?_) (by positivity)
  let P := classPair hr b₁ b₂
  have hsub : exceptions P Y ⊆ exceptions P (Y / 2) ∪ dyadicExceptions P Y := by
    intro n hn
    by_cases h : n ≤ Y / 2
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1, h⟩, (Finset.mem_filter.mp hn).2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn, by omega⟩)
  exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

private theorem singleAvg_cover {r : ℕ} (hr : 0 < r) (b₁ : ReducedClass r) (X k : ℕ) :
    singleAvgExceptions X r hr b₁ ≤ singleAvgExceptions (X / 2 ^ k) r hr b₁ +
      ∑ j ∈ Finset.range k, singleAvgDyadicExceptions (X / 2 ^ j) r hr b₁ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := singleAvg_step hr b₁ (X / 2 ^ k)
    rw [Nat.div_div_eq_div_mul, ← pow_succ] at h
    rw [Finset.sum_range_succ]
    linarith



/-- A generic dyadic summation with an arbitrary real stopping threshold. The square-root
    component sums geometrically; the constant component costs one logarithm. -/
private theorem singleAvg_sum_threshold {X r : ℕ} (hr : 0 < r) (b₁ : ReducedClass r)
    {T U V : ℝ} (hT : 0 < T) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hblock : ∀ Y ≤ X, T ≤ (Y : ℝ) / r →
      singleAvgDyadicExceptions Y r hr b₁ ≤ U * Real.sqrt ((Y : ℝ) / r) + V) :
    singleAvgExceptions X r hr b₁ ≤ T + 1 + 4 * U * Real.sqrt ((X : ℝ) / r) +
      V * (1 + 2 * Real.log (2 + ((X : ℝ) / r) / T)) := by
  classical
  let Y : ℕ → ℕ := fun j => X / 2 ^ j
  let H := (X : ℝ) / r
  have hr' : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hex : ∃ j, ((Y j : ℕ) : ℝ) / r < T :=
    ⟨X, by simpa [Y, Nat.div_eq_of_lt (Nat.lt_two_pow_self (n := X))] using hT⟩
  let k := Nat.find hex
  have hlast : (Y k : ℝ) / r < T := Nat.find_spec hex
  have hact : ∀ j < k, T ≤ (Y j : ℝ) / r := fun j hj => le_of_not_gt (Nat.find_min hex hj)
  have hscale (j : ℕ) : (Y j : ℝ) / r ≤ H / (2 : ℝ)^j := by
    have hfloor : (Y j : ℝ) * (2 : ℝ)^j ≤ X := by
      dsimp [Y]; exact_mod_cast (by simpa [mul_comm] using Nat.mul_div_le X (2^j))
    dsimp [H]; rw [div_le_div_iff₀ hr' (by positivity)]
    calc (Y j : ℝ) * 2 ^ j ≤ X := hfloor
      _ = ((X : ℝ) / r) * r := by field_simp
  have hlog : 0 ≤ Real.log (2 + H/T) := Real.log_nonneg (by linarith [div_nonneg hH hT.le])
  have hcount : (k : ℝ) ≤ 1 + 2 * Real.log (2 + H/T) := by
    cases hk : k with
    | zero => simp; linarith
    | succ j =>
      have ht := (hact j (by omega)).trans (hscale j)
      have hp : (2 : ℝ)^j ≤ H/T := by
        rw [le_div_iff₀ hT]; rw [le_div_iff₀ (by positivity)] at ht; linarith
      have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ j) (hp.trans (by linarith : H/T ≤ 2+H/T))
      rw [Real.log_pow] at hl
      have hh : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hh' := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
      push_cast; linarith
  have hroot (j : ℕ) : Real.sqrt ((Y j : ℝ) / r) ≤ Real.sqrt H * (1 / Real.sqrt 2)^j := by
    apply (Real.sqrt_le_sqrt (hscale j)).trans (le_of_eq ?_)
    have hp : Real.sqrt ((2 : ℝ) ^ j) = (Real.sqrt 2) ^ j := by
      rw [← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg 2) j)]; congr 1
      rw [← pow_mul, mul_comm j 2, pow_mul, Real.sq_sqrt (by norm_num)]
    rw [Real.sqrt_div hH, hp, one_div_pow, div_eq_mul_one_div]
  have hsum : ∑ j ∈ Finset.range k, (1 / Real.sqrt 2 : ℝ)^j ≤ 4 := by
    have hrho : (1 / Real.sqrt 2 : ℝ) ≤ 3 / 4 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have hgeom := geom_sum_mul (1 / Real.sqrt 2 : ℝ) k
    have hpos : (0 : ℝ) ≤ ∑ j ∈ Finset.range k, (1 / Real.sqrt 2 : ℝ)^j := by positivity
    have hp : (0 : ℝ) ≤ (1 / Real.sqrt 2 : ℝ)^k := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hrho hpos]
  have hblocks (j : ℕ) (hj : j ∈ Finset.range k) : singleAvgDyadicExceptions (Y j) r hr b₁ ≤
      (U * Real.sqrt H) * (1 / Real.sqrt 2)^j + V := by
    refine (hblock (Y j) (Nat.div_le_self ..) (hact j (Finset.mem_range.mp hj))).trans ?_
    have hm := mul_le_mul_of_nonneg_left (hroot j) hU; linarith
  have hend := (singleAvgExceptions_trivial hr b₁ (Y k)).trans (by linarith : (Y k : ℝ) / r + 1 ≤ T + 1)
  calc singleAvgExceptions X r hr b₁ ≤ singleAvgExceptions (Y k) r hr b₁ +
        ∑ j ∈ Finset.range k, singleAvgDyadicExceptions (Y j) r hr b₁ := singleAvg_cover hr b₁ X k
    _ ≤ (T+1) + ∑ j ∈ Finset.range k, ((U * Real.sqrt H) * (1/Real.sqrt 2)^j + V) :=
        add_le_add hend (Finset.sum_le_sum hblocks)
    _ = (T+1) + ((U * Real.sqrt H) * (∑ j ∈ Finset.range k, (1/Real.sqrt 2)^j) + k*V) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp
    _ ≤ _ := by
        have h₁ := mul_le_mul_of_nonneg_left hsum (mul_nonneg hU (Real.sqrt_nonneg H))
        have h₂ := mul_le_mul_of_nonneg_right hcount hV
        change _ ≤ T + 1 + 4 * U * Real.sqrt H + V * (1 + 2 * Real.log (2 + H/T)); linarith




/-- The global right-hand side `(S*)`, with `a = φ(r)/r`. -/
noncomputable def singleAvgSharpBudget (X r : ℕ) : ℝ :=
  let H := (X : ℝ) / r
  let L := Real.log (2 * (X : ℝ))
  let a := (r.totient : ℝ) / r
  let B := a^2 * r * L^2
  min H (a^2 * Real.sqrt H * L^3 +
    min (B * (1 + Real.log (2 + H/B)) * (1 + Real.log (2 + H/(a*r*L)))) (a^3 * r * L^4))

/-- Real cutoff optimization with integer denominator cutoff. -/
private theorem exists_single_cutoff {u : ℝ} (hu : 0 ≤ u) :
    ∃ D : ℕ, 1 ≤ D ∧ u ≤ (D : ℝ)^2 ∧ Real.log (2 * (D : ℝ)) ≤ 1 + Real.log (2+u) := by
  let D := ⌈1+u⌉₊
  have hd : 1 + u ≤ (D : ℝ) := Nat.le_ceil _
  have hd' : (1 : ℝ) ≤ D := by linarith
  have hub := (Nat.ceil_lt_add_one (show 0 ≤ 1+u by linarith)).le
  have hle : (D : ℝ) ≤ 2+u := by dsimp [D]; linarith
  refine ⟨D, by exact_mod_cast hd', by nlinarith, ?_⟩
  have hlg := Real.log_le_log (by linarith : (0 : ℝ) < D) hle
  rw [Real.log_mul (by norm_num) (by linarith : (D : ℝ) ≠ 0)]
  linarith [Real.log_two_lt_d9]

/-- Sum the active dyadic estimates down to the first inactive block and optimize the
    denominator cutoff simultaneously for all blocks. -/
theorem singleAvgSharp_of_dyadic (input : SingleAverageDyadicBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X r : ℕ) (hr : 0 < r) (b₁ : ReducedClass r), 2 ≤ X → r ≤ X →
      singleAvgExceptions X r hr b₁ ≤ C * singleAvgSharpBudget X r := by
  obtain ⟨C, hC, hdy⟩ := input
  let c : ℝ := 2^75 + 16
  have hc : 4 ≤ c := by norm_num [c]
  refine ⟨4*C + 4*c, by linarith, fun X r hr b₁ hX hrX => ?_⟩
  let R : ℝ := r
  let H := (X : ℝ) / r
  let L := Real.log (2 * (X : ℝ))
  let a := (r.totient : ℝ) / r
  let B := a^2 * R * L^2
  let T := B + (2:ℝ)^72 + 1
  let u := H/(a*R*L)
  let K := H/B
  let f := 1 + Real.log (2+K)
  let g := 1 + Real.log (2+u)
  let A := a^2 * Real.sqrt H * L^3
  let W := a^3 * R * L^4
  have hr' : 0 < R := Nat.cast_pos.mpr hr
  have hR : 1 ≤ R := Nat.one_le_cast.mpr hr
  have hφ : (0 : ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hH : 1 ≤ H := (one_le_div hr').2 (Nat.cast_le.mpr hrX)
  have hL : 1 ≤ L := one_le_log_two_mul hX
  have ha : 0 < a := div_pos hφ hr'
  have hL' : 0 < L := by linarith
  have hB : 0 < B := by dsimp [B]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hu : 0 ≤ u := div_nonneg (by linarith) (by positivity)
  have hK : 0 ≤ K := div_nonneg (by linarith) hB.le
  have hf : 1 ≤ f := by dsimp [f]; linarith [Real.log_nonneg (by linarith : 1 ≤ 2+K)]
  have hg : 1 ≤ g := by dsimp [g]; linarith [Real.log_nonneg (by linarith : 1 ≤ 2+u)]
  have haL : 1/2 ≤ a*L := by
    have hk := (div_totient_le_two_log hr).trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log (by positivity : (0 : ℝ) < 2*(r:ℝ))
      (by have : (r:ℝ) ≤ X := Nat.cast_le.mpr hrX; linarith : 2*(r:ℝ) ≤ 2*(X:ℝ))) (by norm_num : (0:ℝ) ≤ 2))
    change (1/2 : ℝ) ≤ (r.totient : ℝ)/(r:ℝ)*L
    change (r:ℝ)/(r.totient:ℝ) ≤ 2*L at hk
    rw [div_le_iff₀ hφ] at hk
    have hn : (r:ℝ) ≠ 0 := hr'.ne'
    field_simp [hn]; linarith
  have hB₀ : 1/4 ≤ B := by
    have ht : (1/2 : ℝ)^2 ≤ (a*L)^2 := pow_le_pow_left₀ (by norm_num) haL 2
    have hm := mul_le_mul_of_nonneg_right hR (sq_nonneg (a*L))
    dsimp [B]; nlinarith
  have hTle : T+1 ≤ c*B := by dsimp [T,c]; linarith
  have hW : B ≤ 2*W := by
    have hz := mul_le_mul_of_nonneg_right haL (by positivity : 0 ≤ B*L)
    have hb := mul_le_mul_of_nonneg_left hL hB.le
    dsimp [B, W] at *; nlinarith only [hz, hb]
  have hBT : B ≤ T := by dsimp [T]; linarith
  have hT₁ : 1 ≤ T := by dsimp [T]; linarith
  obtain ⟨D,hD,hDu,hDlog⟩ := exists_single_cutoff hu
  let V := min (B*(g+1)) (a^3 * R * L^3)
  have hV : 0 ≤ V := le_min (by positivity) (by positivity)
  have hdpos : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hhigh : a*H*L/(D:ℝ)^2 ≤ B := by
    rw [div_le_iff₀ (by positivity)]
    have heq : a*H*L = B*u := by dsimp [B,u]; field_simp [ha.ne', hr'.ne', hL'.ne']
    rw [heq]; exact mul_le_mul_of_nonneg_left hDu hB.le
  have hblock (Y : ℕ) (hYX : Y ≤ X) (hact : T ≤ (Y:ℝ)/r) :
      singleAvgDyadicExceptions Y r hr b₁ ≤ (C*(a^2*L^3)) * Real.sqrt ((Y:ℝ)/r) + C*V := by
    have hy0 : 0 < Y := by
      by_contra! hy
      have he : Y = 0 := by omega
      rw [he, Nat.cast_zero, zero_div] at hact
      exact (not_le_of_gt hT) hact
    let l := Real.log (2*(Y:ℝ))
    let h := (Y:ℝ)/r
    have hl : 0 ≤ l := Real.log_nonneg (by have : (1:ℝ) ≤ Y := Nat.one_le_cast.mpr hy0; linarith)
    have hlL : l ≤ L := Real.log_le_log (by positivity) (by have : (Y:ℝ) ≤ X := Nat.cast_le.mpr hYX; linarith)
    have hhH : h ≤ H := div_le_div_of_nonneg_right (Nat.cast_le.mpr hYX) hr'.le
    have hnat : 2^72 ≤ Y/r := by
      apply (Nat.le_div_iff_mul_le hr).2
      have hreal : (2:ℝ)^72 ≤ (Y:ℝ)/r := (by dsimp [T]; linarith : (2:ℝ)^72 ≤ T).trans hact
      rw [le_div_iff₀ hr'] at hreal; dsimp [R] at hreal; exact_mod_cast hreal
    have hbY : a^2 * R * l^2 ≤ B := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl hlL 2) (by positivity)
    have hy := hdy hr b₁ hnat (hbY.trans (hBT.trans hact)) D hD
    change _ ≤ C * (a^2 * Real.sqrt h * l^3 + min (a^2*R*l^2*Real.log (2*(D:ℝ)) + a*h*l/(D:ℝ)^2) (a^3*R*l^3)) at hy
    have hlg0 : 0 ≤ Real.log (2*(D:ℝ)) := Real.log_nonneg (by have : (1:ℝ) ≤ D := Nat.one_le_cast.mpr hD; linarith)
    have hlo := mul_le_mul hbY hDlog hlg0 hB.le
    have hvhi : a*h*l/(D:ℝ)^2 ≤ B := by
      apply le_trans _ hhigh; gcongr
    have hfro : min (a^2*R*l^2*Real.log (2*(D:ℝ)) + a*h*l/(D:ℝ)^2) (a^3*R*l^3) ≤ V := by
      apply min_le_min
      · change _ ≤ B*(g+1); change _ ≤ B*g at hlo; linarith
      · gcongr
    have haY : a^2 * Real.sqrt h * l^3 ≤ a^2 * Real.sqrt h * L^3 := by gcongr
    have hres := hy.trans (mul_le_mul_of_nonneg_left (add_le_add haY hfro) hC.le)
    convert hres using 1; ring
  have hsum := singleAvg_sum_threshold hr b₁ hT (show 0 ≤ C*(a^2*L^3) by positivity)
    (mul_nonneg hC.le hV) hblock
  let G := 1 + 2 * Real.log (2+H/T)
  change _ ≤ T+1 + 4*(C*(a^2*L^3))*Real.sqrt H + (C*V)*G at hsum
  have hG₀ : 0 ≤ G := by
    have hq : 0 ≤ H/T := div_nonneg (by linarith) hT.le
    dsimp [G]; linarith [Real.log_nonneg (by linarith : 1 ≤ 2+H/T)]
  have hGf : G ≤ 2*f := by
    have hq : H/T ≤ K := div_le_div_of_nonneg_left (by linarith) hB hBT
    have ht := Real.log_le_log (by have := div_nonneg (show 0 ≤ H by linarith) hT.le; linarith : 0 < 2+H/T)
      (by linarith : 2+H/T ≤ 2+K)
    dsimp [G,f]; linarith
  have hGL : G ≤ 3*L := by
    have hq : H/T ≤ H := div_le_self (by linarith) hT₁
    have hx : H ≤ X := div_le_self (by positivity) hR
    have ht := Real.log_le_log (by have := div_nonneg (show 0 ≤ H by linarith) hT.le; linarith : 0 < 2+H/T)
      (by
        have hhx : (2:ℝ) ≤ X := by exact_mod_cast hX
        linarith : 2+H/T ≤ 2*(X:ℝ))
    change Real.log (2+H/T) ≤ L at ht; dsimp [G]; linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hAeq : 4*(C*(a^2*L^3))*Real.sqrt H = 4*C*A := by dsimp [A]; ring
  rw [hAeq] at hsum
  let Z := B*f*g
  have hzB : B ≤ Z := by
    have h₁ := mul_le_mul_of_nonneg_left hf hB.le
    have h₂ := mul_le_mul_of_nonneg_left hg (mul_nonneg hB.le (by linarith : 0 ≤ f))
    dsimp [Z]; linarith
  have hprodZ : V*G ≤ 4*Z := by
    have hv : V ≤ B*(g+1) := min_le_left ..
    have hv' : V ≤ 2*(B*g) := hv.trans (by nlinarith [mul_le_mul_of_nonneg_left hg hB.le])
    have hm := mul_le_mul hv' hGf hG₀ (by positivity : 0 ≤ 2*(B*g))
    dsimp [Z]; nlinarith only [hm]
  have hprodW : V*G ≤ 3*W := by
    have hm := mul_le_mul (show V ≤ a^3*R*L^3 from min_le_right ..) hGL hG₀ (by positivity)
    dsimp [W]; nlinarith only [hm]
  have hZ : singleAvgExceptions X r hr b₁ ≤ (4*C+4*c)*(A+Z) := by
    have hm := mul_le_mul_of_nonneg_left hprodZ hC.le
    have ht := mul_le_mul_of_nonneg_left hzB (by linarith : 0 ≤ c)
    nlinarith only [hsum,hm,ht,hTle, mul_nonneg (show 0 ≤ c by linarith) hA,
      mul_nonneg (show 0 ≤ c by linarith) (hB.le.trans hzB)]
  have hW' : singleAvgExceptions X r hr b₁ ≤ (4*C+4*c)*(A+W) := by
    have hm := mul_le_mul_of_nonneg_left hprodW hC.le
    have ht := mul_le_mul_of_nonneg_left hW (by linarith : 0 ≤ c)
    have hw' : 0 ≤ W := by dsimp [W]; positivity
    nlinarith only [hsum,hm,ht,hTle,mul_nonneg (show 0 ≤ c by linarith) hA,
      mul_nonneg (show 0 ≤ c by linarith) hw', mul_nonneg hC.le hw']
  have htr : singleAvgExceptions X r hr b₁ ≤ (4*C+4*c)*H := by
    have hh := singleAvgExceptions_trivial hr b₁ X
    change _ ≤ H+1 at hh
    nlinarith only [hh,hH,mul_le_mul_of_nonneg_right (show 2 ≤ 4*C+4*c by linarith) (show 0 ≤ H by linarith)]
  change _ ≤ (4*C+4*c) * min H (A + min Z W)
  rw [← min_add_add_left, mul_min_of_nonneg _ _ (by linarith : 0 ≤ 4*C+4*c),
    mul_min_of_nonneg _ _ (by linarith : 0 ≤ 4*C+4*c)]
  exact le_min htr (le_min hZ hW')

/-- The sixth term of the exponential series absorbs the two logarithms after cubing. -/
private theorem log_product_cube {K u : ℝ} (hu : 1/2 ≤ u) (hK : 0 ≤ K) (hKu : K ≤ 2*u) :
    ((1+Real.log (2+K)) * (1+Real.log (2+u)))^3 ≤ 200^3*u := by
  let t := Real.log (2 + 2*u)
  have ht : 1/2 ≤ t := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ 2+2*u)
    dsimp [t]; linarith [Real.log_two_gt_d9]
  have hlg1 := Real.log_le_log (by linarith : 0 < 2+K) (by linarith : 2+K ≤ 2+2*u)
  have hlg2 := Real.log_le_log (by linarith : 0 < 2+u) (by linarith : 2+u ≤ 2+2*u)
  have h1 : 1+Real.log (2+K) ≤ 3*t := by change _ ≤ t at hlg1; linarith
  have h2 : 1+Real.log (2+u) ≤ 3*t := by change _ ≤ t at hlg2; linarith
  have h3 : 0 ≤ 1+Real.log (2+u) := by linarith [Real.log_nonneg (by linarith : 1 ≤ 2+u)]
  have h4 : 0 ≤ 1+Real.log (2+K) := by linarith [Real.log_nonneg (by linarith : 1 ≤ 2+K)]
  have hmul := mul_le_mul h1 h2 h3 (by linarith : 0 ≤ 3*t)
  have hpow := pow_le_pow_left₀ (mul_nonneg h4 h3) hmul 3
  have he := Real.pow_div_factorial_le_exp t (by linarith : 0 ≤ t) 6
  change t^6 / (Nat.factorial 6 : ℝ) ≤ Real.exp (Real.log (2+2*u)) at he
  rw [Real.exp_log (by linarith)] at he
  norm_num [Nat.factorial] at he; nlinarith only [hpow, he,hu]

/-- Sharp and power-form right-hand sides use the same full-denominator fallback. -/
noncomputable def singleAvgPowerBudget (X r : ℕ) : ℝ :=
  let H := (X : ℝ) / r
  let L := Real.log (2 * (X : ℝ))
  let a := (r.totient : ℝ) / r
  min H (a^2 * Real.sqrt H * L^3 + min
    (a ^ (5/3:ℝ) * ((X:ℝ)*r) ^ (1/3:ℝ) * L ^ (5/3:ℝ)) (a^3 * r * L^4))

private theorem single_power_cube {a x r L : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (hr : 0 < r) (hL : 0 < L) :
    (a^(5/3:ℝ) * (x*r)^(1/3:ℝ) * L^(5/3:ℝ))^3 =
    (a^2*r*L^2)^3 * ((x/r)/(a*r*L)) := by
  rw [mul_pow,mul_pow,← Real.rpow_mul_natCast ha.le,← Real.rpow_mul_natCast (mul_nonneg hx hr.le),
    ← Real.rpow_mul_natCast hL.le]
  norm_num
  field_simp [ha.ne', hr.ne', hL.ne']




private theorem single_budget_compare {H B K u A F W : ℝ} (hH : 0 ≤ H) (hB : 0 < B)
    (hK : 0 ≤ K) (hu : 0 ≤ u) (hA : 0 ≤ A) (hF : 0 ≤ F) (hW : 0 ≤ W)
    (hKu : K ≤ 2*u) (hHB : H = B*K) (hWcube : W^3 = B^3*u) :
    min H (A + min (B*(1+Real.log (2+K))*(1+Real.log (2+u))) F) ≤
      200 * min H (A+min W F) := by
  let e := min H (A + min (B*(1+Real.log (2+K))*(1+Real.log (2+u))) F)
  have h1 : e ≤ H := min_le_left ..
  have h2 : e ≤ A+F := (min_le_right ..).trans (add_le_add le_rfl (min_le_right ..))
  have h3 : e ≤ 200*(A+W) := by
    by_cases hub : 1/2 ≤ u
    · have hprod := log_product_cube hub hK hKu
      have hp := mul_le_mul_of_nonneg_left hprod (pow_nonneg hB.le 3)
      have hc : (B*(1+Real.log (2+K))*(1+Real.log (2+u)))^3 ≤ (200*W)^3 := by
        rw [mul_pow (200:ℝ), hWcube]; nlinarith only [hp]
      have hq := (Odd.strictMono_pow (show Odd (3:ℕ) from ⟨1, by norm_num⟩)).le_iff_le.mp hc
      have hb : e ≤ A + B*(1+Real.log (2+K))*(1+Real.log (2+u)) :=
        (min_le_right ..).trans (add_le_add le_rfl (min_le_left ..))
      linarith
    · have hb : H ≤ 2*B*u := by rw [hHB]; nlinarith [mul_le_mul_of_nonneg_left hKu hB.le]
      have hpow := pow_le_pow_left₀ hH hb 3
      have hu1 : u ≤ 1 := by linarith
      have hu3 : u^3 ≤ u := by
        have hm := mul_le_mul_of_nonneg_left hu1 hu
        have hm' := mul_le_mul_of_nonneg_left hm hu
        nlinarith only [hm,hm']
      have hm := mul_le_mul_of_nonneg_left hu3 (pow_nonneg hB.le 3)
      have hc : H^3 ≤ (2*W)^3 := by rw [mul_pow (2:ℝ), hWcube]; nlinarith only [hpow,hm]
      have hq := (Odd.strictMono_pow (show Odd (3:ℕ) from ⟨1, by norm_num⟩)).le_iff_le.mp hc
      linarith
  change e ≤ _
  rw [← min_add_add_left, mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 200),
    mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 200)]
  exact le_min (by linarith) (le_min h3 (by linarith))

/-- The sharp global estimate implies the original single-average estimate, with the
    exponent `5/3` on both `φ(r)/r` and `log(2X)`. -/
theorem singleAvgSharpBudget_le_power {X r : ℕ} (hr : 0 < r) (hX : 2 ≤ X) (hrX : r ≤ X) :
    singleAvgSharpBudget X r ≤ 200 * singleAvgPowerBudget X r := by
  let R : ℝ := r
  let H := (X : ℝ)/r
  let L := Real.log (2*(X:ℝ))
  let a := (r.totient:ℝ)/r
  let B := a^2*R*L^2
  let K := H/B
  let u := H/(a*R*L)
  have hr' : 0 < R := Nat.cast_pos.mpr hr
  have hφ : (0:ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have ha : 0 < a := div_pos hφ hr'
  have hL : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (one_le_log_two_mul hX)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hK : 0 ≤ K := div_nonneg hH hB.le
  have hu : 0 ≤ u := div_nonneg hH (by positivity)
  have haL : 1/2 ≤ a*L := by
    have hk := (div_totient_le_two_log hr).trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log (by positivity : (0 : ℝ) < 2*(r:ℝ))
        (by have : (r:ℝ) ≤ X := Nat.cast_le.mpr hrX; linarith : 2*(r:ℝ) ≤ 2*(X:ℝ))) (by norm_num : (0:ℝ) ≤ 2))
    change (r:ℝ)/(r.totient:ℝ) ≤ 2*L at hk
    rw [div_le_iff₀ hφ] at hk
    dsimp [a]; field_simp [show (r:ℝ) ≠ 0 from hr'.ne']; linarith
  have hKu : K ≤ 2*u := by
    have hrel : K*(a*L) = u := by dsimp [K,B,u]; field_simp [ha.ne',hr'.ne',hL.ne']
    nlinarith only [hrel, mul_le_mul_of_nonneg_left haL hK]
  have hHB : H = B*K := by dsimp [K]; field_simp [hB.ne']
  unfold singleAvgSharpBudget singleAvgPowerBudget
  exact single_budget_compare hH hB hK hu (by positivity) (by positivity) (by positivity) hKu hHB
    (single_power_cube ha (Nat.cast_nonneg X) hr' hL)

theorem singleAvgPower_of_dyadic (input : SingleAverageDyadicBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X r : ℕ) (hr : 0 < r) (b₁ : ReducedClass r), 2 ≤ X → r ≤ X →
      singleAvgExceptions X r hr b₁ ≤ C * singleAvgPowerBudget X r := by
  obtain ⟨C, hC, h⟩ := singleAvgSharp_of_dyadic input
  refine ⟨C*200, by positivity, fun X r hr b₁ hX hrX => ?_⟩
  have hrhs := mul_le_mul_of_nonneg_left (singleAvgSharpBudget_le_power hr hX hrX) hC.le
  exact (h X r hr b₁ hX hrX).trans (by linarith)

/-- Dyadic input after the fourth-moment estimate of the high-denominator term. -/
def SingleAverageLogEdgeDyadicBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ {r Y : ℕ} (hr : 0 < r) (b₁ : ReducedClass r),
      2 ^ 72 ≤ Y / r →
      ((r.totient : ℝ) / (r : ℝ)) ^ 2 * (r : ℝ) * Real.log (2 * (Y : ℝ)) ^ 2 ≤ (Y : ℝ) / (r : ℝ) →
      let H := (Y : ℝ) / r
      let L := Real.log (2 * (Y : ℝ))
      let a := (r.totient : ℝ) / r
      let B := a^2 * r * L^2
      singleAvgDyadicExceptions Y r hr b₁ ≤ C * (a^2 * Real.sqrt H * L^3 + B*(1+Real.log (2+H/B)))

noncomputable def singleAvgLogEdgeBudget (X r : ℕ) : ℝ :=
  let H := (X:ℝ)/r
  let L := Real.log (2*(X:ℝ))
  let a := (r.totient:ℝ)/r
  let B := a^2*r*L^2
  min H (a^2*Real.sqrt H*L^3 + B*(1+Real.log (2+H/B))^2)

/-- Freezing both positive scales at their global values preserves the logarithmic budget. -/
private theorem single_edge_scale {b B h H : ℝ} (hb : 0 < b) (hbB : b ≤ B) (hh : 0 ≤ h) (hhH : h ≤ H) :
    b*(1+Real.log (2+h/b)) ≤ B*(1+Real.log (2+H/B)) := by
  have hB := lt_of_lt_of_le hb hbB
  have hlog := Real.log_le_sub_one_of_pos (div_pos hB hb)
  have he : b * (B/b) = B := by field_simp
  have hk := mul_le_mul_of_nonneg_left hlog hb.le
  have harg : 2+h/b ≤ (B/b)*(2+H/B) := by
    field_simp [hb.ne',hB.ne']; nlinarith [mul_le_mul_of_nonneg_right hbB hB.le,
      mul_le_mul_of_nonneg_right hhH hB.le]
  have ht := Real.log_le_log (by positivity : 0 < 2+h/b) harg
  rw [Real.log_mul (div_pos hB hb).ne' (by have := div_nonneg (hh.trans hhH) hB.le; linarith : 2+H/B ≠ 0)] at ht
  have hlast := mul_le_mul_of_nonneg_right hbB (Real.log_nonneg
    (by have := div_nonneg (hh.trans hhH) hB.le; linarith : 1 ≤ 2+H/B))
  nlinarith only [he,hk,hlast,mul_le_mul_of_nonneg_left ht hb.le]

theorem single_half_le_ratio_log {X r : ℕ} (hr : 0 < r) (hrX : r ≤ X) :
    (1/2 : ℝ) ≤ ((r.totient:ℝ)/r)*Real.log (2*(X:ℝ)) := by
  have hφ : (0:ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hR : (0:ℝ) < r := Nat.cast_pos.mpr hr
  have h := (div_totient_le_two_log hr).trans (mul_le_mul_of_nonneg_left
    (Real.log_le_log (by positivity : (0:ℝ) < 2*(r:ℝ))
      (by have : (r:ℝ) ≤ X := Nat.cast_le.mpr hrX; linarith : 2*(r:ℝ) ≤ 2*(X:ℝ))) (by norm_num : (0:ℝ) ≤ 2))
  rw [div_le_iff₀ hφ] at h; field_simp [hR.ne']; linarith

theorem singleAvgLogEdge_of_dyadic (input : SingleAverageLogEdgeDyadicBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X r : ℕ) (hr : 0 < r) (b₁ : ReducedClass r), 2 ≤ X → r ≤ X →
      singleAvgExceptions X r hr b₁ ≤ C * singleAvgLogEdgeBudget X r := by
  obtain ⟨C,hC,hd⟩ := input
  let c : ℝ := 2^75+16
  have hc : 4 ≤ c := by norm_num [c]
  refine ⟨4*C+c, by linarith, fun X r hr b₁ hX hrX => ?_⟩
  let R : ℝ := r
  let H := (X:ℝ)/r
  let a := (r.totient:ℝ)/r
  let L := Real.log (2*(X:ℝ))
  let B := a^2*R*L^2
  let T := B+(2:ℝ)^72+1
  let f := 1+Real.log (2+H/B)
  let A := a^2*Real.sqrt H*L^3
  have hR : 0 < R := Nat.cast_pos.mpr hr
  have hR1 : 1 ≤ R := Nat.one_le_cast.mpr hr
  have hH : 1 ≤ H := (one_le_div hR).2 (Nat.cast_le.mpr hrX)
  have ha : 0 < a := div_pos (Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)) hR
  have hL : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (one_le_log_two_mul hX)
  have hB : 0 < B := by dsimp [B]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hBT : B ≤ T := by dsimp [T]; linarith
  have hf : 1 ≤ f := by
    have := div_nonneg (show 0 ≤ H by linarith) hB.le; dsimp [f]; linarith [Real.log_nonneg (by linarith : 1 ≤ 2+H/B)]
  have hB₀ : 1/4 ≤ B := by
    have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) (single_half_le_ratio_log hr hrX) 2
    change (1/2:ℝ)^2 ≤ (a*L)^2 at hsq
    have := mul_le_mul_of_nonneg_right hR1 (sq_nonneg (a*L)); dsimp [B]; nlinarith
  have htail : T+1 ≤ c*B := by dsimp [T,c]; linarith only [hB₀]
  have hact (Y : ℕ) (hYX : Y ≤ X) (ht : T ≤ (Y:ℝ)/r) :
      singleAvgDyadicExceptions Y r hr b₁ ≤ (C*(a^2*L^3))*Real.sqrt ((Y:ℝ)/r) + C*(B*f) := by
    have hy : 0 < Y := by
      by_contra! hu; have he : Y=0 := by omega
      rw [he, Nat.cast_zero, zero_div] at ht; linarith
    let l := Real.log (2*(Y:ℝ))
    let h := (Y:ℝ)/r
    let b := a^2*R*l^2
    have hpos : 0 < l := Real.log_pos (by have : (1:ℝ) ≤ Y := Nat.one_le_cast.mpr hy; linarith)
    have hb : 0 < b := by dsimp [b]; positivity
    have hl : l ≤ L := Real.log_le_log (by positivity) (by have : (Y:ℝ) ≤ X := Nat.cast_le.mpr hYX; linarith)
    have hbB : b ≤ B := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpos.le hl 2) (by positivity)
    have hhH : h ≤ H := div_le_div_of_nonneg_right (Nat.cast_le.mpr hYX) hR.le
    have hnat : 2^72 ≤ Y/r := by
      apply (Nat.le_div_iff_mul_le hr).2
      have hh := (show (2:ℝ)^72 ≤ T by dsimp [T]; linarith).trans ht
      rw [le_div_iff₀ hR] at hh; dsimp [R] at hh; exact_mod_cast hh
    have hest := hd hr b₁ hnat (hbB.trans (hBT.trans ht))
    change _ ≤ C*(a^2*Real.sqrt h*l^3 + b*(1+Real.log (2+h/b))) at hest
    have hz := single_edge_scale hb hbB (show 0 ≤ h by dsimp [h]; positivity) hhH
    have hmain : a^2*Real.sqrt h*l^3 ≤ a^2*Real.sqrt h*L^3 := by gcongr
    have hh := hest.trans (mul_le_mul_of_nonneg_left (add_le_add hmain hz) hC.le)
    change _ ≤ C*(a^2*Real.sqrt h*L^3+B*f) at hh
    convert hh using 1; ring
  have hf₀ : 0 ≤ f := by linarith
  have hs := singleAvg_sum_threshold hr b₁ hT (show 0 ≤ C*(a^2*L^3) by positivity)
    (show 0 ≤ C*(B*f) by positivity) hact
  have hlogs : 1+2*Real.log (2+H/T) ≤ 2*f := by
    have hh := div_le_div_of_nonneg_left (show 0 ≤ H by linarith) hB hBT
    have hl := Real.log_le_log (by have := div_nonneg (show 0 ≤ H by linarith) hT.le; linarith : 0 < 2+H/T)
      (by linarith : 2+H/T ≤ 2+H/B)
    dsimp [f]; linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hBf : B ≤ B*f^2 := by
    have ht := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hf 2
    nlinarith only [mul_le_mul_of_nonneg_left ht hB.le]
  have hnonneg : 0 ≤ C*(B*f) := by positivity
  have hcmp := mul_le_mul_of_nonneg_left hlogs hnonneg
  change _ ≤ T+1+4*(C*(a^2*L^3))*Real.sqrt H + C*(B*f)*(1+2*Real.log (2+H/T)) at hs
  have he : 4*(C*(a^2*L^3))*Real.sqrt H = 4*C*A := by dsimp [A]; ring
  rw [he] at hs
  have hmain : singleAvgExceptions X r hr b₁ ≤ (4*C+c)*(A + B*f^2) := by
    nlinarith only [hs,htail,hcmp,mul_le_mul_of_nonneg_left hBf (by linarith : 0 ≤ c),
      mul_nonneg (by linarith : 0 ≤ c) hA, mul_nonneg hnonneg (by linarith : 0 ≤ f)]
  have htr : singleAvgExceptions X r hr b₁ ≤ (4*C+c)*H := by
    have hh := singleAvgExceptions_trivial hr b₁ X
    change _ ≤ H+1 at hh
    nlinarith only [hh,hH,mul_le_mul_of_nonneg_right (show 2 ≤ 4*C+c by linarith) (show 0 ≤ H by linarith)]
  change _ ≤ (4*C+c)*min H (A+B*f^2)
  rw [mul_min_of_nonneg _ _ (by linarith : 0 ≤ 4*C+c)]; exact le_min htr hmain

open Filter
open scoped Topology

/-- Dimensionless cutoff parameter for the density-one statement. -/
noncomputable def singleAvgLogEdgeParameter (X r : ℕ) : ℝ :=
  (X:ℝ) / ((r.totient:ℝ)^2 * Real.log (2*(X:ℝ))^2)

theorem edge_basics {X r : ℕ} (hr : 0 < r) (hX : 2 ≤ X) (hrX : r ≤ X) :
    let H := (X:ℝ)/r
    let L := Real.log (2*(X:ℝ))
    let a := (r.totient:ℝ)/r
    let B := a^2*r*L^2
    let K := singleAvgLogEdgeParameter X r
    (r:ℝ) ≤ 4*B ∧ K = H/B ∧ K/4 ≤ H := by
  dsimp only
  let H := (X:ℝ)/r
  let L := Real.log (2*(X:ℝ))
  let a := (r.totient:ℝ)/r
  let B := a^2*r*L^2
  let K := singleAvgLogEdgeParameter X r
  have hr' : (0:ℝ) < r := Nat.cast_pos.mpr hr
  have hφ : (0:ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have ha : 0 < a := div_pos hφ hr'
  have hL : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (one_le_log_two_mul hX)
  have hB : 0 < B := by dsimp [B]; positivity
  have hR : 1 ≤ (r:ℝ) := Nat.one_le_cast.mpr hr
  have haL : (1/2:ℝ) ≤ a*L := single_half_le_ratio_log hr hrX
  have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) haL 2
  have hrB : (r:ℝ) ≤ 4*B := by dsimp [B]; nlinarith only [mul_le_mul_of_nonneg_left hsq hr'.le]
  have hKB : K = H/B := by
    change (X:ℝ)/((r.totient:ℝ)^2*L^2) = ((X:ℝ)/r)/(((r.totient:ℝ)/r)^2*r*L^2)
    field_simp [hφ.ne',hr'.ne',hL.ne']
  have hK : 0 ≤ K := by rw [hKB]; dsimp [H]; positivity
  have hHB : B*K = H := by rw [hKB]; field_simp [hB.ne']
  refine ⟨hrB,hKB,?_⟩
  change K/4 ≤ H
  nlinarith only [hHB, mul_le_mul_of_nonneg_right (hR.trans hrB) hK]

private theorem edge_normalized_budget {X r : ℕ} (hr : 0 < r) (hX : 2 ≤ X) (hrX : r ≤ X)
    (hH₄ : 4 ≤ (X:ℝ)/r) (hK₄ : 4 ≤ singleAvgLogEdgeParameter X r) :
    let H := (X:ℝ)/r
    let K := singleAvgLogEdgeParameter X r
    singleAvgLogEdgeBudget X r / H ≤ 64 * (Real.log H ^ 3 / Real.sqrt H) + 16 * (Real.log K ^ 2 / K) := by
  let H := (X:ℝ)/r
  let K := singleAvgLogEdgeParameter X r
  let L := Real.log (2*(X:ℝ))
  let a := (r.totient:ℝ)/r
  let B := a^2*r*L^2
  change 4 ≤ H at hH₄; change 4 ≤ K at hK₄
  have hr' : (0:ℝ) < r := Nat.cast_pos.mpr hr
  have hH : 0 < H := by linarith
  have hK : 0 < K := by linarith
  have hL : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (one_le_log_two_mul hX)
  have ha : 0 < a := div_pos (Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)) hr'
  have ha1 : a ≤ 1 := (div_le_one hr').2 (Nat.cast_le.mpr (Nat.totient_le r))
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨hrB, hKB, _⟩ := edge_basics hr hX hrX
  change (r:ℝ) ≤ 4*B at hrB; change K = H/B at hKB
  have hHB : B*K = H := by rw [hKB]; field_simp [hB.ne']
  have hbH : B ≤ H := by nlinarith only [hHB, mul_le_mul_of_nonneg_left (show 1 ≤ K by linarith) hB.le]
  have hrH : (r:ℝ) ≤ 4*H := by linarith only [hrB,hbH]
  have hx : (X:ℝ) = H*r := by dsimp [H]; field_simp [hr'.ne']
  have hsq : 8 ≤ H^2 := by nlinarith only [hH₄, sq_nonneg (H-4)]
  have hdom : 2*(X:ℝ) ≤ H^4 := by
    nlinarith only [hx, mul_le_mul_of_nonneg_left hrH hH.le, mul_le_mul_of_nonneg_right hsq (sq_nonneg H)]
  have hlog := Real.log_le_log (by have : (0:ℝ) < X := Nat.cast_pos.mpr (by omega); positivity : 0 < 2*(X:ℝ)) hdom
  rw [Real.log_pow] at hlog
  change L ≤ 4*Real.log H at hlog
  have hlgK := Real.log_le_log (by linarith : 0 < 2+K) (by nlinarith only [hK₄,sq_nonneg (K-2)] : 2+K ≤ K^2)
  rw [Real.log_pow] at hlgK
  have hlow := Real.log_le_log (by norm_num : (0:ℝ)<2) (by linarith : 2 ≤ K)
  have hlogK : 1+Real.log (2+K) ≤ 4*Real.log K := by push_cast at hlgK; linarith [Real.log_two_gt_d9]
  have hposlog : 0 ≤ 1+Real.log (2+K) := by linarith [Real.log_nonneg (by linarith : 1 ≤ 2+K)]
  have hroot := Real.sqrt_pos.2 hH
  have ha2 := pow_le_pow_left₀ ha.le ha1 2
  have hmajor : a^2*Real.sqrt H*L^3/H ≤ 64*(Real.log H^3 / Real.sqrt H) := by
    have hh : a^2*Real.sqrt H*L^3/H = a^2*L^3 / Real.sqrt H := by
      field_simp [hH.ne',hroot.ne']; exact Real.sq_sqrt hH.le
    rw [hh, ← mul_div_assoc]; apply div_le_div_of_nonneg_right _ hroot.le
    have hp := pow_le_pow_left₀ hL.le hlog 3
    nlinarith only [hp,mul_le_mul_of_nonneg_right ha2 (pow_nonneg hL.le 3)]
  have hminor : B*(1+Real.log (2+K))^2/H ≤ 16*(Real.log K^2/K) := by
    rw [← hHB, mul_div_mul_left _ _ hB.ne', ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hK.le
    nlinarith only [pow_le_pow_left₀ hposlog hlogK 2]
  change singleAvgLogEdgeBudget X r / H ≤ _
  have hb : singleAvgLogEdgeBudget X r ≤ a^2*Real.sqrt H*L^3 + B*(1+Real.log (2+K))^2 := by
    rw [hKB]; exact min_le_right ..
  exact (div_le_div_of_nonneg_right hb hH.le).trans (by rw [add_div]; exact add_le_add hmajor hminor)

private theorem edge_log_cube_div_sqrt : Tendsto (fun x : ℝ => Real.log x^3/Real.sqrt x) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => Real.log (Real.sqrt x)^3/Real.sqrt x) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 3 one_ne_zero).comp Real.tendsto_sqrt_atTop
  have h' : Tendsto (fun x : ℝ => 8*(Real.log (Real.sqrt x)^3/Real.sqrt x)) atTop (𝓝 0) := by
    simpa using h.const_mul (8:ℝ)
  apply h'.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
  have hs := Real.log_pow (Real.sqrt x) 2
  rw [Real.sq_sqrt hx] at hs
  push_cast at hs; rw [hs]; ring

/-- Along arbitrary sequences of moduli and fixed first classes, `X/(φ(r)^2 log²(2X)) → ∞`
    suffices for the single-averaged density of exceptions to tend to zero. -/
theorem singleAvgDensity_of_logEdgeDyadic (input : SingleAverageLogEdgeDyadicBound)
    (X r : ℕ → ℕ) (hr : ∀ n, 0 < r n) (b₁ : ∀ n, ReducedClass (r n)) (hX : ∀ n, 2 ≤ X n)
    (hrX : ∀ n, r n ≤ X n) (hK : Tendsto (fun n => singleAvgLogEdgeParameter (X n) (r n)) atTop atTop) :
    Tendsto (fun n => singleAvgExceptions (X n) (r n) (hr n) (b₁ n) / ((X n:ℝ)/r n)) atTop (𝓝 0) := by
  let H := fun n => (X n:ℝ)/r n
  let K := fun n => singleAvgLogEdgeParameter (X n) (r n)
  have hH : Tendsto H atTop atTop := by
    refine Filter.tendsto_atTop.2 fun t => ?_
    filter_upwards [hK.eventually_ge_atTop (4*t)] with n hn
    have hh := (edge_basics (hr n) (hX n) (hrX n)).2.2
    change (4*t) ≤ K n at hn; change K n/4 ≤ H n at hh; linarith
  obtain ⟨C,hC,hbound⟩ := singleAvgLogEdge_of_dyadic input
  have h1 : Tendsto (fun n => Real.log (H n)^3 / Real.sqrt (H n)) atTop (𝓝 0) := edge_log_cube_div_sqrt.comp hH
  have h2 : Tendsto (fun n => Real.log (K n)^2 / K n) atTop (𝓝 0) := by
    simpa [Function.comp_def,K] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp hK
  have ht : Tendsto (fun n => C*(64*(Real.log (H n)^3 / Real.sqrt (H n)) + 16*(Real.log (K n)^2 / K n))) atTop (𝓝 0) := by
    simpa using ((h1.const_mul (64:ℝ)).add (h2.const_mul (16:ℝ))).const_mul C
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht (Filter.Eventually.of_forall ?_) ?_
  · intro n
    have he : 0 ≤ singleAvgExceptions (X n) (r n) (hr n) (b₁ n) := by unfold singleAvgExceptions; positivity
    exact div_nonneg he (by positivity)
  · filter_upwards [hH.eventually_ge_atTop 4, hK.eventually_ge_atTop 4] with n hn hn'
    have he := hbound (X n) (r n) (hr n) (b₁ n) (hX n) (hrX n)
    have hh := edge_normalized_budget (hr n) (hX n) (hrX n) hn hn'
    have hpositive : 0 ≤ H n := by dsimp [H]; positivity
    calc singleAvgExceptions (X n) (r n) (hr n) (b₁ n) / H n ≤ C*singleAvgLogEdgeBudget (X n) (r n)/H n :=
          div_le_div_of_nonneg_right he hpositive
      _ = C*(singleAvgLogEdgeBudget (X n) (r n)/H n) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hh hC.le

end FareyGoldbach



