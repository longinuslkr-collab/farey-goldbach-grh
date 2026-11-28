import FareyGoldbach.Defs
import FareyGoldbach.CharacterBound
import FareyGoldbach.VoronoiCells
import FareyGoldbach.PrimeSums
import FareyGoldbach.ModelAndRemainder
import FareyGoldbach.SharpRankin

/-!
# Module F2: Finite-Group Parseval Bounds, Local/Global Remainders, and Second-Difference Kernel Decay

This module supplies the harmonic-analysis core for Route A (double- and single-averaged binary
Goldbach in arithmetic progressions across arbitrary positive integer moduli `1 ≤ r ≤ X`):

1. **Two finite-group Parseval lemmas on `ZMod (r * q)`**:
   - `mul_parseval_units` (multiplicative Parseval `(4)` on `U_{rq}`).
   - `fiber_sq_le` (fiber Cauchy–Schwarz `(5)` over `b ∈ U_r`).
   - `fixed_fiber_additive_parseval` (fixed-fiber numerator Parseval `(6)` over `a mod q`).
2. **Explicit local/global remainder separation**:
   - `localModelTerm` and `localRemainder` at `(a, q, β)`.
   - `localRemainder_eq_global_on_cell`: exact agreement with `smoothedPrimeSum - modelSum Q Q`
     on every `voronoiCell Q c`.
   - `avg_remainder_sq` (`(7)`): uniform sup-in-`α` mean-square remainder over `b ∈ U_r`:
     `(1 / φ(r)) * ∑_b* ‖R_b(α)‖² ≪ κ * H * √H * L²`.
   - `fixed_num_remainder_sq` (`(8)`): fixed-class numerator Parseval over `a ∈ U_q`:
     `∑_a* ‖Rloc_{b,a,q}(β)‖² ≪ q * Y * (1 + H * |β|) * L²`.
3. **Second-difference smooth kernel decay `(11)`**:
   - `smoothedKernel_second_diff_decay`: `‖V_b(β)‖ ≤ 64 * H / (1 + H * |β|)²`.
   - `integral_one_add_mul_norm_smoothedKernel_sq_le`:
     `∫_{-1/2}^{1/2} (1 + H * |β|) * ‖V_b(β)‖² dβ ≤ 4096 * H`.
-/

open Real Complex Set
open scoped BigOperators Classical

namespace FareyGoldbach

section ReducedClassesAndCanonicalLevel

/-- Reduced residue classes modulo `m`: `{a ∈ range m | Nat.Coprime a m}`.
For `m = 1`, this is `{0}` with cardinality `1 = φ(1)`. -/
def coprimeClasses (m : ℕ) : Finset ℕ :=
  (Finset.range m).filter (fun a => Nat.Coprime a m)

lemma card_coprimeClasses (m : ℕ) : (coprimeClasses m).card = m.totient := by
  unfold coprimeClasses
  rw [Nat.totient_eq_card_coprime]
  congr 1; ext a; simp [Nat.coprime_comm]

lemma mem_coprimeClasses {m a : ℕ} : a ∈ coprimeClasses m ↔ a < m ∧ Nat.Coprime a m := by
  simp [coprimeClasses]

/-- Canonical Route-A Farey denominator cutoff `Q = ⌊√(Y / r)⌋ / 2^12`. -/
def routeAQ (Y r : ℕ) : ℕ := Nat.sqrt (Y / r) / 2 ^ 12

/-- Lower and upper bounds for `Q = routeAQ Y r` when `2 ^ 26 ≤ Y / r`. -/
lemma routeAQ_bounds {r Y : ℕ} (hr : 0 < r) (hH : 2 ^ 26 ≤ Y / r) :
    2 ≤ routeAQ Y r ∧
    (1 / (2 : ℝ) ^ 14) * Real.sqrt ((Y : ℝ) / (r : ℝ)) ≤ (routeAQ Y r : ℝ) ∧
    (routeAQ Y r : ℝ) ≤ (1 / (2 : ℝ) ^ 12) * Real.sqrt ((Y : ℝ) / (r : ℝ)) ∧
    routeAQ Y r ≤ Y := by
  set S := Nat.sqrt (Y / r)
  set Q := routeAQ Y r
  have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hS_ge : 2 ^ 13 ≤ S := by
    dsimp [S]
    rw [Nat.le_sqrt]
    have : 2 ^ 13 * 2 ^ 13 = 2 ^ 26 := by norm_num
    omega
  have hQ_ge2 : 2 ≤ Q := by
    dsimp [Q, routeAQ]
    have : 2 * 2 ^ 12 ≤ S := by omega
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2 ^ 12)).2 this
  have hS_le_rt : (S : ℝ) ≤ Real.sqrt ((Y : ℝ) / (r : ℝ)) := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (by positivity)]
    have h1 : S * S ≤ Y / r := Nat.sqrt_le (Y / r)
    have h2 : ((Y / r : ℕ) : ℝ) ≤ (Y : ℝ) / (r : ℝ) := by
      rw [le_div_iff₀ hr_pos]; exact_mod_cast (by simpa [mul_comm] using Nat.mul_div_le Y r)
    exact (by exact_mod_cast (by simpa [sq] using h1) : (S : ℝ) ^ 2 ≤ ((Y / r : ℕ) : ℝ)).trans h2
  have hrt_le_2S : Real.sqrt ((Y : ℝ) / (r : ℝ)) ≤ 2 * (S : ℝ) := by
    have hsucc : Y / r < (S + 1) * (S + 1) := Nat.lt_succ_sqrt (Y / r)
    have hdiv : (Y : ℝ) / (r : ℝ) ≤ ((Y / r + 1 : ℕ) : ℝ) := by
      have hd := Nat.div_add_mod Y r; have hm := Nat.mod_lt Y hr
      rw [div_le_iff₀ hr_pos]
      exact_mod_cast (by nlinarith : Y ≤ (Y / r + 1) * r)
    have hS1 : S + 1 ≤ 2 * S := by omega
    have hnat : Y / r + 1 ≤ (2 * S) ^ 2 := by nlinarith
    have hsq : (Y : ℝ) / (r : ℝ) ≤ ((2 * S : ℕ) : ℝ) ^ 2 := hdiv.trans (by exact_mod_cast hnat)
    have hrt := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (by positivity)] at hrt
    push_cast at hrt; exact hrt
  have hQ_upper : (Q : ℝ) ≤ (1 / (2 : ℝ) ^ 12) * Real.sqrt ((Y : ℝ) / (r : ℝ)) := by
    have h1 : Q * 2 ^ 12 ≤ S := by
      dsimp [Q, routeAQ]; rw [mul_comm]; exact Nat.mul_div_le S (2 ^ 12)
    have h1R : (Q : ℝ) * (2 : ℝ) ^ 12 ≤ (S : ℝ) := by exact_mod_cast h1
    have h12_pos : (0 : ℝ) < (2 : ℝ) ^ 12 := by positivity
    calc (Q : ℝ) = (1 / (2 : ℝ) ^ 12) * ((Q : ℝ) * (2 : ℝ) ^ 12) := by field_simp [h12_pos.ne']
      _ ≤ (1 / (2 : ℝ) ^ 12) * (S : ℝ) := mul_le_mul_of_nonneg_left h1R (by positivity)
      _ ≤ (1 / (2 : ℝ) ^ 12) * Real.sqrt ((Y : ℝ) / (r : ℝ)) :=
          mul_le_mul_of_nonneg_left hS_le_rt (by positivity)
  have hQ_lower : (1 / (2 : ℝ) ^ 14) * Real.sqrt ((Y : ℝ) / (r : ℝ)) ≤ (Q : ℝ) := by
    have h1 : S ≤ 2 ^ 12 * (Q + 1) := by
      have := Nat.div_add_mod S (2 ^ 12)
      have := Nat.mod_lt S (by norm_num : 0 < 2 ^ 12)
      dsimp [Q, routeAQ]; omega
    have h2 : S ≤ 2 ^ 13 * Q := by
      have : Q + 1 ≤ 2 * Q := by omega
      have : 2 ^ 12 * (Q + 1) ≤ 2 ^ 12 * (2 * Q) := Nat.mul_le_mul_left _ this
      have : 2 ^ 12 * (2 * Q) = 2 ^ 13 * Q := by ring
      omega
    have h2R : (S : ℝ) ≤ (2 : ℝ) ^ 13 * (Q : ℝ) := by exact_mod_cast h2
    have h14 : (2 : ℝ) ^ 14 = 2 * (2 : ℝ) ^ 13 := by norm_num
    have hpos14 : (0 : ℝ) < (2 : ℝ) ^ 14 := by positivity
    rw [one_div_mul_eq_div, div_le_iff₀ hpos14]
    linarith [hrt_le_2S, h2R, h14]
  have hQ_le_Y : Q ≤ Y :=
    (Nat.div_le_self S (2 ^ 12)).trans ((Nat.sqrt_le_self (Y / r)).trans (Nat.div_le_self Y r))
  exact ⟨hQ_ge2, hQ_lower, hQ_upper, hQ_le_Y⟩

end ReducedClassesAndCanonicalLevel

section FiniteGroupParseval

/-- Unit group subset of `ZMod m`. -/
noncomputable def zmodUnitsFinset (m : ℕ) [NeZero m] : Finset (ZMod m) :=
  Finset.univ.filter IsUnit

lemma card_zmodUnitsFinset (m : ℕ) [NeZero m] : (zmodUnitsFinset m).card = m.totient := by
  have hbij : (zmodUnitsFinset m).card = Fintype.card (ZMod m)ˣ := by
    change (zmodUnitsFinset m).card = (Finset.univ : Finset (ZMod m)ˣ).card
    refine Finset.card_bij (fun u hu => (Finset.mem_filter.mp hu).2.unit) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro u₁ _ u₂ _ hEq; simpa using congrArg Units.val hEq
    · intro u _
      exact ⟨(u : ZMod m), Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.isUnit⟩, by ext; rfl⟩
  rw [hbij, ZMod.card_units_eq_totient]

/-- Sum of `1` over all Dirichlet characters mod `m` equals `φ(m)`. -/
lemma sum_one_dirichletChar (m : ℕ) [NeZero m] :
    ∑ _χ : DirichletCharacter ℂ m, (1 : ℝ) = (m.totient : ℝ) := by
  have h := DirichletCharacter.sum_char_inv_mul_char_eq ℂ (isUnit_one : IsUnit (1 : ZMod m)) (1 : ZMod m)
  simp only [map_one, mul_one, ↓reduceIte] at h
  have hre := congrArg Complex.re h
  rw [Complex.re_sum] at hre
  simpa using hre

/-- Character orthogonality over the unit subset of `ZMod m`. -/
lemma sum_dirichletChar_over_units {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) :
    ∑ u ∈ zmodUnitsFinset m, χ u = if χ = 1 then (m.totient : ℂ) else 0 := by
  by_cases h1 : χ = 1
  · subst h1
    rw [ite_eq_left rfl]
    calc ∑ u ∈ zmodUnitsFinset m, (1 : DirichletCharacter ℂ m) u
        = ∑ _u ∈ zmodUnitsFinset m, (1 : ℂ) :=
          Finset.sum_congr rfl fun u hu => MulChar.one_apply (Finset.mem_filter.mp hu).2
      _ = ((zmodUnitsFinset m).card : ℂ) := by simp
      _ = (m.totient : ℂ) := by rw [card_zmodUnitsFinset]
  · rw [ite_eq_right h1]
    -- Find a unit `u₀` with `χ u₀ ≠ 1`.
    have hex : ∃ u₀ : ZMod m, IsUnit u₀ ∧ χ u₀ ≠ 1 := by
      by_contra hall
      push Not at hall
      apply h1
      ext u
      rw [MulChar.one_apply u.isUnit]
      exact hall (u : ZMod m) u.isUnit
    obtain ⟨u₀, hu₀, hne⟩ := hex
    have hshift : ∑ u ∈ zmodUnitsFinset m, χ u = χ u₀ * ∑ u ∈ zmodUnitsFinset m, χ u := by
      have hbij : ∑ u ∈ zmodUnitsFinset m, χ u = ∑ u ∈ zmodUnitsFinset m, χ (u * u₀) := by
        symm
        refine Finset.sum_bij (fun u _ => u * u₀) ?_ ?_ ?_ ?_
        · intro u hu
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2.mul hu₀⟩
        · intro u₁ _ u₂ _ hEq; exact hu₀.mul_right_cancel hEq
        · intro v hv
          have hv_unit := (Finset.mem_filter.mp hv).2
          let u₀inv : ZMod m := ↑(hu₀.unit⁻¹)
          have hmul : u₀inv * u₀ = 1 := by
            change (↑(hu₀.unit⁻¹) : ZMod m) * (↑hu₀.unit : ZMod m) = 1
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
          exact ⟨v * u₀inv, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv_unit.mul hu₀.unit⁻¹.isUnit⟩,
            by rw [mul_assoc, hmul, mul_one]⟩
        · intro _ _; rfl
      conv_lhs => rw [hbij]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => by rw [map_mul, mul_comm]
    have hmul0 : (χ u₀ - 1) * ∑ u ∈ zmodUnitsFinset m, χ u = 0 := by
      calc (χ u₀ - 1) * ∑ u ∈ zmodUnitsFinset m, χ u
          = χ u₀ * ∑ u ∈ zmodUnitsFinset m, χ u - ∑ u ∈ zmodUnitsFinset m, χ u := by ring
        _ = 0 := by rw [← hshift, sub_self]
    exact (mul_eq_zero.mp hmul0).resolve_left (sub_ne_zero.mpr hne)

/-- **Multiplicative Parseval `(4)` on `(ZMod m)ˣ`:**
`∑_{u ∈ U_m} ‖f u‖² = (1 / φ(m)) * ∑_{χ mod m} ‖∑_{u ∈ U_m} f u * χ u‖²`. -/
theorem mul_parseval_units {m : ℕ} (hm : 0 < m) [NeZero m] (f : ZMod m → ℂ) :
    ∑ u ∈ zmodUnitsFinset m, ‖f u‖ ^ 2 =
      (1 / (m.totient : ℝ)) *
        ∑ χ : DirichletCharacter ℂ m, ‖∑ u ∈ zmodUnitsFinset m, f u * χ u‖ ^ 2 := by
  have hφ_pos : 0 < m.totient := Nat.totient_pos.mpr hm
  have hφR : (m.totient : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hφ_pos.ne'
  have hC : ∑ χ : DirichletCharacter ℂ m,
        (∑ u ∈ zmodUnitsFinset m, f u * χ u) * star (∑ v ∈ zmodUnitsFinset m, f v * χ v) =
      (m.totient : ℂ) * ∑ u ∈ zmodUnitsFinset m, f u * star (f u) := by
    have hterm : ∀ χ : DirichletCharacter ℂ m,
        (∑ u ∈ zmodUnitsFinset m, f u * χ u) * star (∑ v ∈ zmodUnitsFinset m, f v * χ v) =
        ∑ u ∈ zmodUnitsFinset m, ∑ v ∈ zmodUnitsFinset m,
          (f u * star (f v)) * (χ v⁻¹ * χ u) := by
      intro χ
      rw [star_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [star_mul', star_char_apply_eq_inv χ (Finset.mem_filter.mp hv).2]; ring
    calc ∑ χ : DirichletCharacter ℂ m,
            (∑ u ∈ zmodUnitsFinset m, f u * χ u) * star (∑ v ∈ zmodUnitsFinset m, f v * χ v)
        = ∑ χ : DirichletCharacter ℂ m, ∑ u ∈ zmodUnitsFinset m, ∑ v ∈ zmodUnitsFinset m,
            (f u * star (f v)) * (χ v⁻¹ * χ u) := Finset.sum_congr rfl fun χ _ => hterm χ
      _ = ∑ u ∈ zmodUnitsFinset m, ∑ v ∈ zmodUnitsFinset m,
            (f u * star (f v)) * ∑ χ : DirichletCharacter ℂ m, χ v⁻¹ * χ u := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ u ∈ zmodUnitsFinset m, ∑ v ∈ zmodUnitsFinset m,
            (f u * star (f v)) * (if v = u then (m.totient : ℂ) else 0) := by
          refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v hv => ?_
          rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ (Finset.mem_filter.mp hv).2 u]
      _ = ∑ u ∈ zmodUnitsFinset m, (f u * star (f u)) * (m.totient : ℂ) := by
          refine Finset.sum_congr rfl fun u hu => ?_
          simp only [mul_ite, mul_zero, Finset.sum_ite_eq', hu, ↓reduceIte]
      _ = (m.totient : ℂ) * ∑ u ∈ zmodUnitsFinset m, f u * star (f u) := by
          rw [← Finset.sum_mul, mul_comm]
  have hRe := congrArg Complex.re hC
  rw [Complex.re_sum, Complex.mul_re] at hRe
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, Complex.re_sum] at hRe
  have hnorm_sq : ∀ z : ℂ, (z * star z).re = ‖z‖ ^ 2 := fun z => by
    rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  simp_rw [hnorm_sq] at hRe
  rw [one_div_mul_eq_div, eq_div_iff hφR, mul_comm]
  exact hRe.symm

/-- **Fiber Cauchy–Schwarz Lemma `(5)`:**
For any `r, q ≥ 1`, any function `Δ : ZMod (r * q) → ℂ`, and any unimodular weights `‖η u‖ ≤ 1`,
`(1 / φ(r)) * ∑_{b ∈ U_r} ‖∑_{u ∈ charSupp r q b} η u * Δ u‖² ≤ (φ(rq) / φ(r)²) * ∑_{u ∈ U_{rq}} ‖Δ u‖²`. -/
theorem fiber_sq_le {r q : ℕ} (hr : 0 < r) (hq : 0 < q) [NeZero (r * q)]
    (Δ : ZMod (r * q) → ℂ) (η : ℕ → ZMod (r * q) → ℂ)
    (hη : ∀ b ∈ coprimeClasses r, ∀ u ∈ charSupp r q b, ‖η b u‖ ≤ 1) :
    (1 / (r.totient : ℝ)) *
        ∑ b ∈ coprimeClasses r, ‖∑ u ∈ charSupp r q b, η b u * Δ u‖ ^ 2 ≤
      (((r * q).totient : ℝ) / ((r.totient : ℝ) ^ 2)) *
        ∑ u ∈ zmodUnitsFinset (r * q), ‖Δ u‖ ^ 2 := by
  have hφr_pos : (0 : ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  -- Per-fiber Cauchy–Schwarz: `‖∑_{u ∈ fiber b} η b u * Δ u‖² ≤ (φ(rq)/φ(r)) * ∑_{u ∈ fiber b} ‖Δ u‖²`.
  have hper : ∀ b ∈ coprimeClasses r,
      ‖∑ u ∈ charSupp r q b, η b u * Δ u‖ ^ 2 ≤
        (((r * q).totient : ℝ) / (r.totient : ℝ)) *
          ∑ u ∈ charSupp r q b, ‖Δ u‖ ^ 2 := by
    intro b hb
    have hbr : Nat.Coprime b r := (mem_coprimeClasses.mp hb).2
    have htri : ‖∑ u ∈ charSupp r q b, η b u * Δ u‖ ≤ ∑ u ∈ charSupp r q b, ‖Δ u‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u hu => ?_)
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hη b hb u hu)
    have hcs := sq_sum_le_card_mul_sum_sq_real (charSupp r q b) (fun u => ‖Δ u‖)
    calc ‖∑ u ∈ charSupp r q b, η b u * Δ u‖ ^ 2
        ≤ (∑ u ∈ charSupp r q b, ‖Δ u‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) htri 2
      _ ≤ ((charSupp r q b).card : ℝ) * ∑ u ∈ charSupp r q b, ‖Δ u‖ ^ 2 := hcs
      _ = (((r * q).totient : ℝ) / (r.totient : ℝ)) * ∑ u ∈ charSupp r q b, ‖Δ u‖ ^ 2 := by
          rw [card_charSupp_eq r q b hr hbr]
  -- Pairwise disjointness of fibers `charSupp r q b` inside `zmodUnitsFinset (r * q)`.
  have hdisj : Set.PairwiseDisjoint (coprimeClasses r : Set ℕ) (fun b => charSupp r q b) := by
    intro b₁ hb₁ b₂ hb₂ hne
    change Disjoint (charSupp r q b₁) (charSupp r q b₂)
    rw [Finset.disjoint_left]
    intro u hu₁ hu₂
    have hm1 : u.val % r = b₁ % r := (Finset.mem_filter.mp hu₁).2.2
    have hm2 : u.val % r = b₂ % r := (Finset.mem_filter.mp hu₂).2.2
    have hb1_lt : b₁ < r := (mem_coprimeClasses.mp hb₁).1
    have hb2_lt : b₂ < r := (mem_coprimeClasses.mp hb₂).1
    rw [Nat.mod_eq_of_lt hb1_lt] at hm1
    rw [Nat.mod_eq_of_lt hb2_lt] at hm2
    exact hne (hm1.symm.trans hm2)
  have hsub : (coprimeClasses r).biUnion (fun b => charSupp r q b) ⊆ zmodUnitsFinset (r * q) := by
    intro u hu
    obtain ⟨b, _, hub⟩ := Finset.mem_biUnion.mp hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hub).2.1⟩
  have hsum_fibers : ∑ b ∈ coprimeClasses r, ∑ u ∈ charSupp r q b, ‖Δ u‖ ^ 2 ≤
      ∑ u ∈ zmodUnitsFinset (r * q), ‖Δ u‖ ^ 2 := by
    rw [← Finset.sum_biUnion hdisj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
  calc (1 / (r.totient : ℝ)) * ∑ b ∈ coprimeClasses r, ‖∑ u ∈ charSupp r q b, η b u * Δ u‖ ^ 2
      ≤ (1 / (r.totient : ℝ)) *
          ∑ b ∈ coprimeClasses r,
            (((r * q).totient : ℝ) / (r.totient : ℝ)) * ∑ u ∈ charSupp r q b, ‖Δ u‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper) (by positivity)
    _ = (((r * q).totient : ℝ) / ((r.totient : ℝ) ^ 2)) *
          ∑ b ∈ coprimeClasses r, ∑ u ∈ charSupp r q b, ‖Δ u‖ ^ 2 := by
        rw [← Finset.mul_sum]; ring
    _ ≤ (((r * q).totient : ℝ) / ((r.totient : ℝ) ^ 2)) *
          ∑ u ∈ zmodUnitsFinset (r * q), ‖Δ u‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsum_fibers (by positivity)

/-- **Fixed-Fiber Additive Parseval Lemma `(6)`:**
For fixed `b ∈ coprimeClasses r` and any `Δ : ZMod (r * q) → ℂ`,
`∑_{a < q} ‖∑_{u ∈ charSupp r q b} e(a * (u.val / r) / q) * Δ u‖² = q * ∑_{u ∈ charSupp r q b} ‖Δ u‖²`. -/
theorem fixed_fiber_additive_parseval {r q b : ℕ} (_hr : 0 < r) (hq : 0 < q) (hb : b < r)
    [NeZero (r * q)] (Δ : ZMod (r * q) → ℂ) :
    ∑ a ∈ Finset.range q,
        ‖∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) * Δ u‖ ^ 2 =
      (q : ℝ) * ∑ u ∈ charSupp r q b, ‖Δ u‖ ^ 2 := by
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  -- Injectivity of `u ↦ u.val / r` on `charSupp r q b` into `{0, ..., q - 1}`.
  have hinj_div : ∀ u ∈ charSupp r q b, ∀ v ∈ charSupp r q b,
      u.val / r = v.val / r → u = v := by
    intro u hu v hv hEq
    have hmu : u.val % r = b := by
      rw [(Finset.mem_filter.mp hu).2.2, Nat.mod_eq_of_lt hb]
    have hmv : v.val % r = b := by
      rw [(Finset.mem_filter.mp hv).2.2, Nat.mod_eq_of_lt hb]
    have hval : u.val = v.val := by
      have h1 := Nat.div_add_mod u.val r
      have h2 := Nat.div_add_mod v.val r
      rw [hEq, hmu] at h1; rw [hmv] at h2; omega
    have hcast : ((u.val : ℕ) : ZMod (r * q)) = ((v.val : ℕ) : ZMod (r * q)) := by rw [hval]
    simpa [ZMod.natCast_zmod_val] using hcast
  -- Orthogonality of `a ↦ e(a * (j₁ - j₂) / q)` over `a ∈ range q` for `j₁, j₂ < q`.
  have horth : ∀ u ∈ charSupp r q b, ∀ v ∈ charSupp r q b,
      ∑ a ∈ Finset.range q,
        e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) *
          star (e ((a : ℝ) * ((v.val / r : ℕ) : ℝ) / (q : ℝ))) =
        if u = v then (q : ℂ) else 0 := by
    intro u hu v hv
    let j₁ : ℕ := u.val / r
    let j₂ : ℕ := v.val / r
    let d : ℤ := (j₁ : ℤ) - (j₂ : ℤ)
    let z : ℂ := e ((d : ℝ) / (q : ℝ))
    have hpow : ∀ a : ℕ,
        e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) *
          star (e ((a : ℝ) * ((v.val / r : ℕ) : ℝ) / (q : ℝ))) = z ^ a := by
      intro a
      have hstar : star (e ((a : ℝ) * ((v.val / r : ℕ) : ℝ) / (q : ℝ))) =
          e (-((a : ℝ) * ((v.val / r : ℕ) : ℝ) / (q : ℝ))) := by
        apply mul_left_cancel₀ (show e ((a : ℝ) * ((v.val / r : ℕ) : ℝ) / (q : ℝ)) ≠ 0 from by
          unfold e; exact Complex.exp_ne_zero _)
        rw [e_mul_star_e, ← e_add, add_neg_cancel, e_zero]
      rw [hstar, ← e_add, ← e_nat_mul]
      congr 1
      change (a : ℝ) * (j₁ : ℝ) / (q : ℝ) + -((a : ℝ) * (j₂ : ℝ) / (q : ℝ)) =
        (a : ℝ) * ((((j₁ : ℤ) - (j₂ : ℤ) : ℤ) : ℝ) / (q : ℝ))
      rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast]; ring
    simp_rw [hpow]
    by_cases huv : u = v
    · subst huv
      rw [ite_eq_left rfl]
      have hz1 : z = 1 := by simp [z, d, j₁, j₂, e_zero]
      simp [hz1]
    · rw [ite_eq_right huv]
      have hd_ne : d ≠ 0 := fun h0 => huv (hinj_div u hu v hv (by dsimp [d, j₁, j₂] at h0; omega))
      have hu_lt : j₁ < q := Nat.div_lt_of_lt_mul u.val_lt
      have hv_lt : j₂ < q := Nat.div_lt_of_lt_mul v.val_lt
      have hz_ne : z ≠ 1 := by
        intro h1
        obtain ⟨k, hk⟩ := (e_eq_one_iff _).1 h1
        have hdR : (d : ℝ) = (k : ℝ) * (q : ℝ) := (div_eq_iff hqR).1 hk
        have hdZ : d = k * (q : ℤ) := by exact_mod_cast hdR
        have hj1_lt : (j₁ : ℤ) < (q : ℤ) := Int.ofNat_lt.mpr hu_lt
        have hj2_lt : (j₂ : ℤ) < (q : ℤ) := Int.ofNat_lt.mpr hv_lt
        have hj1_nn : (0 : ℤ) ≤ (j₁ : ℤ) := Int.natCast_nonneg _
        have hj2_nn : (0 : ℤ) ≤ (j₂ : ℤ) := Int.natCast_nonneg _
        have habs : |d| < (q : ℤ) := abs_lt.mpr ⟨by dsimp [d]; linarith, by dsimp [d]; linarith⟩
        have hk0 : k = 0 := by
          by_contra hk_ne
          have h1k : (1 : ℤ) ≤ |k| := Int.one_le_abs hk_ne
          have hmul : (q : ℤ) ≤ |d| := by
            rw [hdZ, abs_mul, abs_of_pos (Int.natCast_pos.mpr hq)]
            nlinarith
          omega
        exact hd_ne (by rw [hdZ, hk0, zero_mul])
      have hz_pow : z ^ q = 1 := by
        dsimp [z]
        rw [← e_nat_mul]
        have : (q : ℝ) * ((d : ℝ) / (q : ℝ)) = (d : ℝ) := mul_div_cancel₀ _ hqR
        rw [this, e_int]
      have hmul : (z - 1) * ∑ a ∈ Finset.range q, z ^ a = 0 := by
        rw [mul_comm, geom_sum_mul, hz_pow, sub_self]
      exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hz_ne)
  have hC : ∑ a ∈ Finset.range q,
        (∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) * Δ u) *
          star (∑ v ∈ charSupp r q b, e ((a : ℝ) * ((v.val / r : ℕ) : ℝ) / (q : ℝ)) * Δ v) =
      (q : ℂ) * ∑ u ∈ charSupp r q b, Δ u * star (Δ u) := by
    have hterm : ∀ a ∈ Finset.range q,
        (∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) * Δ u) *
          star (∑ v ∈ charSupp r q b, e ((a : ℝ) * ((v.val / r : ℕ) : ℝ) / (q : ℝ)) * Δ v) =
        ∑ u ∈ charSupp r q b, ∑ v ∈ charSupp r q b,
          (Δ u * star (Δ v)) *
            (e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) *
              star (e ((a : ℝ) * ((v.val / r : ℕ) : ℝ) / (q : ℝ)))) := by
      intro a _
      rw [star_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [star_mul']; ring
    calc ∑ a ∈ Finset.range q,
            (∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) * Δ u) *
              star (∑ v ∈ charSupp r q b, e ((a : ℝ) * ((v.val / r : ℕ) : ℝ) / (q : ℝ)) * Δ v)
        = ∑ a ∈ Finset.range q, ∑ u ∈ charSupp r q b, ∑ v ∈ charSupp r q b,
            (Δ u * star (Δ v)) *
              (e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) *
                star (e ((a : ℝ) * ((v.val / r : ℕ) : ℝ) / (q : ℝ)))) := Finset.sum_congr rfl hterm
      _ = ∑ u ∈ charSupp r q b, ∑ v ∈ charSupp r q b,
            (Δ u * star (Δ v)) *
              ∑ a ∈ Finset.range q,
                e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) *
                  star (e ((a : ℝ) * ((v.val / r : ℕ) : ℝ) / (q : ℝ))) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ u ∈ charSupp r q b, ∑ v ∈ charSupp r q b,
            (Δ u * star (Δ v)) * (if u = v then (q : ℂ) else 0) := by
          refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => ?_
          rw [horth u hu v hv]
      _ = ∑ u ∈ charSupp r q b, (Δ u * star (Δ u)) * (q : ℂ) := by
          refine Finset.sum_congr rfl fun u hu => ?_
          simp only [mul_ite, mul_zero, Finset.sum_ite_eq, hu, ↓reduceIte]
      _ = (q : ℂ) * ∑ u ∈ charSupp r q b, Δ u * star (Δ u) := by
          rw [← Finset.sum_mul, mul_comm]
  have hRe := congrArg Complex.re hC
  rw [Complex.re_sum, Complex.mul_re] at hRe
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, Complex.re_sum] at hRe
  have hnorm_sq : ∀ z : ℂ, (z * star z).re = ‖z‖ ^ 2 := fun z => by
    rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  simp_rw [hnorm_sq] at hRe
  exact hRe

end FiniteGroupParseval

section LocalAndGlobalRemainder

/-- Local Farey model term at fraction `a / q` and offset `β` (zero when `¬ Coprime q r`). -/
noncomputable def localModelTerm (r b Y a q : ℕ) (β : ℝ) : ℂ :=
  if Nat.Coprime q r then
    e (-((a : ℝ) * (rInv r q : ℝ) * (b : ℝ) / (q : ℝ))) *
      (((r : ℝ) / (r.totient : ℝ) : ℝ) : ℂ) *
      ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) *
      smoothedKernel r b Y β
  else 0

/-- Local Farey remainder `Rloc_{b, a, q}(β) = S_b(a/q + β) - M_{b, a, q}(β)`. -/
noncomputable def localRemainder (r b Y a q : ℕ) (β : ℝ) : ℂ :=
  smoothedPrimeSum r b Y ((a : ℝ) / (q : ℝ) + β) - localModelTerm r b Y a q β

/-- Exact agreement between global remainder (with `Q₀ = Q`) and `localRemainder` on `voronoiCell Q c`. -/
lemma localRemainder_eq_global_on_cell {r b Y Q : ℕ} {c : RatCenter} {α : ℝ}
    (hα : α ∈ voronoiCell Q c) :
    smoothedPrimeSum r b Y α - modelSum r b Y Q Q α =
      localRemainder r b Y c.a c.q (wrap (α - c.val)) := by
  have hc_le : c.q ≤ Q := mem_centers_iff.mp hα.1
  rw [modelSum_eq_on_cell_le hα hc_le]
  unfold localRemainder localModelTerm modelCoeff
  have hS : smoothedPrimeSum r b Y α = smoothedPrimeSum r b Y ((c.a : ℝ) / (c.q : ℝ) + wrap (α - c.val)) := by
    unfold smoothedPrimeSum RatCenter.val
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    apply e_eq_of_sub_int (k := round (α - (c.a : ℝ) / (c.q : ℝ)) * (j : ℤ))
    unfold wrap; push_cast; ring
  rw [hS]
  split_ifs <;> simp

/-- Discrepancy of the `primeWeight`-weighted smoothed sum in residue class `u mod (r * q)`. -/
noncomputable def unitClassDiscrepancy (r q Y : ℕ) [NeZero (r * q)] (β : ℝ) (u : ZMod (r * q)) : ℂ :=
  (∑ n ∈ (Finset.Icc 1 Y).filter (fun n : ℕ => (n : ZMod (r * q)) = u),
      (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
        e ((β / (r : ℝ)) * (n : ℝ))) -
    ((1 : ℂ) / ((r * q).totient : ℂ)) *
      (∑ n ∈ Finset.Icc 1 Y,
        (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * e ((β / (r : ℝ)) * (n : ℝ)))

/-- **Multiplicative Parseval budget `(4)` for `unitClassDiscrepancy`:**
Assuming `SmoothedTwistEstimate` with constant `C > 0`, for `1 ≤ r ≤ Y`, `2 ≤ Y`, `1 ≤ q ≤ Y`, `|β| ≤ 1/2`:
`∑_{u ∈ U_{rq}} ‖Δ_u‖² ≤ (3 * C + 1)² * Y * (1 + (Y / r) * |β|) * log²(2Y)`. -/
lemma sum_norm_sq_unitClassDiscrepancy_le {C : ℝ} (hC : 0 < C)
    (hTw : ∀ (Y d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (t : ℝ),
      2 ≤ Y → |t| ≤ 1 / 2 →
        ‖smoothedTiltedRemainder χ Y t‖ ≤
          C * Real.sqrt ((Y : ℝ) * (1 + |t| * Y)) * Real.log (2 * (d : ℝ) * Y))
    {r q Y : ℕ} (hr : 0 < r) (hq : 0 < q) (hrY : r ≤ Y) (hqY : q ≤ Y) (hY : 2 ≤ Y)
    {β : ℝ} (hβ : |β| ≤ 1 / 2) [NeZero (r * q)] :
    ∑ u ∈ zmodUnitsFinset (r * q), ‖unitClassDiscrepancy r q Y β u‖ ^ 2 ≤
      (3 * C + 1) ^ 2 * (Y : ℝ) * (1 + ((Y : ℝ) / (r : ℝ)) * |β|) * (Real.log (2 * (Y : ℝ))) ^ 2 := by
  have hrq_pos : 0 < r * q := Nat.mul_pos hr hq
  have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hY_pos : (0 : ℝ) < Y := Nat.cast_pos.mpr (by omega)
  have hlog_nn : 0 ≤ Real.log (2 * (Y : ℝ)) := Real.log_nonneg (by
    have : (2 : ℝ) ≤ Y := Nat.cast_le.mpr hY; linarith)
  rw [mul_parseval_units hrq_pos]
  let U_sum : ℂ := ∑ n ∈ Finset.Icc 1 Y,
    (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * e ((β / (r : ℝ)) * (n : ℝ))
  -- For every character `χ mod (r*q)`, compute `∑ u ∈ U_{rq}, Δ_u * χ u` and bound its norm.
  have hchar_bd : ∀ χ : DirichletCharacter ℂ (r * q),
      ‖∑ u ∈ zmodUnitsFinset (r * q), unitClassDiscrepancy r q Y β u * χ u‖ ≤
        (3 * C + 1) * Real.sqrt ((Y : ℝ) * (1 + ((Y : ℝ) / (r : ℝ)) * |β|)) * Real.log (2 * (Y : ℝ)) := by
    intro χ
    have hhat : ∑ u ∈ zmodUnitsFinset (r * q), unitClassDiscrepancy r q Y β u * χ u =
        smoothedTiltedRemainder χ Y (β / (r : ℝ)) +
        ∑ n ∈ Finset.Icc 1 Y,
          (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) *
            (((primeWeight n - ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) *
            χ (n : ZMod (r * q)) * e ((β / (r : ℝ)) * (n : ℝ)) := by
      unfold unitClassDiscrepancy
      simp_rw [sub_mul, Finset.sum_sub_distrib]
      have hfirst : ∑ u ∈ zmodUnitsFinset (r * q),
            (∑ n ∈ (Finset.Icc 1 Y).filter (fun n : ℕ => (n : ZMod (r * q)) = u),
              (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
                e ((β / (r : ℝ)) * (n : ℝ))) * χ u =
          ∑ n ∈ Finset.Icc 1 Y,
            (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
              χ (n : ZMod (r * q)) * e ((β / (r : ℝ)) * (n : ℝ)) := by
        have hstep1 : ∀ u ∈ zmodUnitsFinset (r * q),
            (∑ n ∈ (Finset.Icc 1 Y).filter (fun n : ℕ => (n : ZMod (r * q)) = u),
              (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
                e ((β / (r : ℝ)) * (n : ℝ))) * χ u =
            ∑ n ∈ (Finset.Icc 1 Y).filter (fun n : ℕ => (n : ZMod (r * q)) = u),
              (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
                χ (n : ZMod (r * q)) * e ((β / (r : ℝ)) * (n : ℝ)) := by
          intro u _
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [(Finset.mem_filter.mp hn).2]; ring
        rw [Finset.sum_congr rfl hstep1]
        have hfib := Finset.sum_fiberwise_of_maps_to
          (s := (Finset.Icc 1 Y).filter (fun n : ℕ => IsUnit (n : ZMod (r * q))))
          (t := zmodUnitsFinset (r * q))
          (g := fun n : ℕ => (n : ZMod (r * q)))
          (fun n hn => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hn).2⟩)
          (fun n => (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
            χ (n : ZMod (r * q)) * e ((β / (r : ℝ)) * (n : ℝ)))
        have hcong : ∑ u ∈ zmodUnitsFinset (r * q),
              ∑ n ∈ (Finset.Icc 1 Y).filter (fun n : ℕ => (n : ZMod (r * q)) = u),
                (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
                  χ (n : ZMod (r * q)) * e ((β / (r : ℝ)) * (n : ℝ)) =
            ∑ u ∈ zmodUnitsFinset (r * q),
              ∑ n ∈ ((Finset.Icc 1 Y).filter (fun n : ℕ => IsUnit (n : ZMod (r * q)))).filter
                  (fun n : ℕ => (n : ZMod (r * q)) = u),
                (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
                  χ (n : ZMod (r * q)) * e ((β / (r : ℝ)) * (n : ℝ)) := by
          refine Finset.sum_congr rfl fun u hu => Finset.sum_congr ?_ fun _ _ => rfl
          ext n; simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hn1, hn2⟩; exact ⟨⟨hn1, hn2.symm ▸ (Finset.mem_filter.mp hu).2⟩, hn2⟩
          · rintro ⟨⟨hn1, _⟩, hn2⟩; exact ⟨hn1, hn2⟩
        rw [hcong, hfib, Finset.sum_filter]
        refine Finset.sum_congr rfl fun n _ => ?_
        by_cases hu : IsUnit (n : ZMod (r * q))
        · simp [hu]
        · rw [ite_eq_right hu, MulChar.map_nonunit χ hu]; ring
      have hsecond : ∑ u ∈ zmodUnitsFinset (r * q),
            ((1 : ℂ) / ((r * q).totient : ℂ)) * U_sum * χ u =
          (if χ = 1 then (1 : ℂ) else 0) * U_sum := by
        have hpull : ∑ u ∈ zmodUnitsFinset (r * q),
              ((1 : ℂ) / ((r * q).totient : ℂ)) * U_sum * χ u =
            ((1 : ℂ) / ((r * q).totient : ℂ)) * U_sum * ∑ u ∈ zmodUnitsFinset (r * q), χ u := by
          exact (Finset.mul_sum _ _ _).symm
        rw [hpull, sum_dirichletChar_over_units]
        have hφC : ((r * q).totient : ℂ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hrq_pos).ne'
        split_ifs
        · field_simp [hφC]
        · ring
      rw [hfirst]
      change (∑ n ∈ Finset.Icc 1 Y,
          (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
            χ (n : ZMod (r * q)) * e ((β / (r : ℝ)) * (n : ℝ))) -
        ∑ u ∈ zmodUnitsFinset (r * q),
          ((1 : ℂ) / ((r * q).totient : ℂ)) * U_sum * χ u = _
      rw [hsecond]
      unfold smoothedTiltedRemainder
      dsimp [U_sum]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => by push_cast; ring
    rw [hhat]
    have htr : |β / (r : ℝ)| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos hr_pos]
      have hr1 : (1 : ℝ) ≤ r := Nat.one_le_cast.mpr hr
      calc |β| / (r : ℝ) ≤ |β| / 1 := div_le_div_of_nonneg_left (abs_nonneg β) zero_lt_one hr1
        _ = |β| := div_one _
        _ ≤ 1 / 2 := hβ
    have harg_eq : |β / (r : ℝ)| * (Y : ℝ) = ((Y : ℝ) / (r : ℝ)) * |β| := by
      rw [abs_div, abs_of_pos hr_pos]; ring
    have hlog_rqY : Real.log (2 * ((r * q : ℕ) : ℝ) * (Y : ℝ)) ≤ 3 * Real.log (2 * (Y : ℝ)) := by
      have h2rqY : 2 * ((r * q : ℕ) : ℝ) * (Y : ℝ) ≤ (2 * (Y : ℝ)) ^ 3 := by
        have hrY' : (r : ℝ) ≤ Y := Nat.cast_le.mpr hrY
        have hqY' : (q : ℝ) ≤ Y := Nat.cast_le.mpr hqY
        push_cast
        have h1 : (r : ℝ) * (q : ℝ) ≤ (Y : ℝ) * (Y : ℝ) :=
          mul_le_mul hrY' hqY' (Nat.cast_nonneg _) hY_pos.le
        have h2 : 2 * ((r : ℝ) * (q : ℝ)) * (Y : ℝ) ≤ 2 * ((Y : ℝ) * (Y : ℝ)) * (Y : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 two_pos.le) hY_pos.le
        nlinarith [pow_nonneg hY_pos.le 3]
      calc Real.log (2 * ((r * q : ℕ) : ℝ) * (Y : ℝ))
          ≤ Real.log ((2 * (Y : ℝ)) ^ 3) := Real.log_le_log (by positivity) h2rqY
        _ = 3 * Real.log (2 * (Y : ℝ)) := by rw [Real.log_pow]; norm_num
    have h1 : ‖smoothedTiltedRemainder χ Y (β / (r : ℝ))‖ ≤
        3 * C * Real.sqrt ((Y : ℝ) * (1 + ((Y : ℝ) / (r : ℝ)) * |β|)) * Real.log (2 * (Y : ℝ)) := by
      have htw := hTw Y (r * q) χ (β / (r : ℝ)) hY htr
      rw [harg_eq] at htw
      calc ‖smoothedTiltedRemainder χ Y (β / (r : ℝ))‖
          ≤ C * Real.sqrt ((Y : ℝ) * (1 + ((Y : ℝ) / (r : ℝ)) * |β|)) *
              Real.log (2 * ((r * q : ℕ) : ℝ) * (Y : ℝ)) := htw
        _ ≤ C * Real.sqrt ((Y : ℝ) * (1 + ((Y : ℝ) / (r : ℝ)) * |β|)) *
              (3 * Real.log (2 * (Y : ℝ))) :=
            mul_le_mul_of_nonneg_left hlog_rqY (by positivity)
        _ = 3 * C * Real.sqrt ((Y : ℝ) * (1 + ((Y : ℝ) / (r : ℝ)) * |β|)) * Real.log (2 * (Y : ℝ)) := by ring
    have h2 : ‖∑ n ∈ Finset.Icc 1 Y,
          (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) *
            (((primeWeight n - ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) *
            χ (n : ZMod (r * q)) * e ((β / (r : ℝ)) * (n : ℝ))‖ ≤
        Real.sqrt ((Y : ℝ) * (1 + ((Y : ℝ) / (r : ℝ)) * |β|)) * Real.log (2 * (Y : ℝ)) := by
      have hsum : ‖∑ n ∈ Finset.Icc 1 Y,
            (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) *
              (((primeWeight n - ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) *
              χ (n : ZMod (r * q)) * e ((β / (r : ℝ)) * (n : ℝ))‖ ≤
          Real.sqrt (Y : ℝ) * Real.log (Y : ℝ) := by
        calc ‖∑ n ∈ Finset.Icc 1 Y,
                (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) *
                  (((primeWeight n - ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) *
                  χ (n : ZMod (r * q)) * e ((β / (r : ℝ)) * (n : ℝ))‖
            ≤ ∑ n ∈ Finset.Icc 1 Y, |ArithmeticFunction.vonMangoldt n - primeWeight n| := by
              refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
              rw [norm_mul, norm_mul, norm_mul, norm_e, mul_one, Complex.norm_real, Complex.norm_real,
                  Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (quarticBump_nonneg _), abs_sub_comm]
              have hχ1 : ‖χ (n : ZMod (r * q))‖ ≤ 1 := by
                by_cases hu : IsUnit (n : ZMod (r * q))
                · have hpow : (hu.unit : (ZMod (r * q))ˣ) ^ Fintype.card (ZMod (r * q))ˣ = 1 :=
                    pow_card_eq_one
                  have hval : ((n : ZMod (r * q)) ^ Fintype.card (ZMod (r * q))ˣ) = 1 := by
                    have h1 := congrArg Units.val hpow
                    rw [Units.val_pow_eq_pow_val, Units.val_one] at h1
                    exact h1
                  have hnorm_pow : ‖χ (n : ZMod (r * q))‖ ^ Fintype.card (ZMod (r * q))ˣ = 1 := by
                    rw [← norm_pow, ← map_pow, hval, map_one, norm_one]
                  have hcard_pos : 0 < Fintype.card (ZMod (r * q))ˣ := Fintype.card_pos
                  by_contra hgt; push Not at hgt
                  have h1lt : 1 < ‖χ (n : ZMod (r * q))‖ ^ Fintype.card (ZMod (r * q))ˣ :=
                    one_lt_pow₀ hgt hcard_pos.ne'
                  linarith
                · rw [MulChar.map_nonunit χ hu, norm_zero]; exact zero_le_one
              calc quarticBump ((n : ℝ) / (Y : ℝ)) * |ArithmeticFunction.vonMangoldt n - primeWeight n| *
                    ‖χ (n : ZMod (r * q))‖
                  ≤ 1 * |ArithmeticFunction.vonMangoldt n - primeWeight n| * 1 :=
                    mul_le_mul (mul_le_mul_of_nonneg_right (quarticBump_le_one _) (abs_nonneg _))
                      hχ1 (norm_nonneg _) (by positivity)
                _ = |ArithmeticFunction.vonMangoldt n - primeWeight n| := by ring
          _ ≤ Real.sqrt (Y : ℝ) * Real.log (Y : ℝ) := primePowerMass_le Y (by omega)
      have hrt_le : Real.sqrt (Y : ℝ) ≤ Real.sqrt ((Y : ℝ) * (1 + ((Y : ℝ) / (r : ℝ)) * |β|)) :=
        Real.sqrt_le_sqrt (by nlinarith [show (0 : ℝ) ≤ ((Y : ℝ) / (r : ℝ)) * |β| by positivity])
      have hlogY_le : Real.log (Y : ℝ) ≤ Real.log (2 * (Y : ℝ)) :=
        Real.log_le_log hY_pos (by linarith)
      have hlogY_nn : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Y))
      exact hsum.trans (mul_le_mul hrt_le hlogY_le hlogY_nn (Real.sqrt_nonneg _))
    exact (norm_add_le _ _).trans (by linarith)
  set B : ℝ := (3 * C + 1) ^ 2 * (Y : ℝ) * (1 + ((Y : ℝ) / (r : ℝ)) * |β|) * (Real.log (2 * (Y : ℝ))) ^ 2
  have hsq_bd : ∀ χ : DirichletCharacter ℂ (r * q),
      ‖∑ u ∈ zmodUnitsFinset (r * q), unitClassDiscrepancy r q Y β u * χ u‖ ^ 2 ≤ B := by
    intro χ
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (hchar_bd χ) 2
    have hsq : ((3 * C + 1) * Real.sqrt ((Y : ℝ) * (1 + ((Y : ℝ) / (r : ℝ)) * |β|)) *
        Real.log (2 * (Y : ℝ))) ^ 2 = B := by
      dsimp [B]
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
    linarith
  have hφ_pos : (0 : ℝ) < (r * q).totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hrq_pos)
  calc (1 / ((r * q).totient : ℝ)) *
          ∑ χ : DirichletCharacter ℂ (r * q),
            ‖∑ u ∈ zmodUnitsFinset (r * q), unitClassDiscrepancy r q Y β u * χ u‖ ^ 2
      ≤ (1 / ((r * q).totient : ℝ)) * ∑ _χ : DirichletCharacter ℂ (r * q), B :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun χ _ => hsq_bd χ) (by positivity)
    _ = (1 / ((r * q).totient : ℝ)) * (B * ∑ _χ : DirichletCharacter ℂ (r * q), (1 : ℝ)) := by
        congr 1; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => (mul_one B).symm
    _ = B := by
        rw [sum_one_dirichletChar (r * q)]; field_simp [hφ_pos.ne']

/-- Exact three-term decomposition of `localRemainder r b Y a q β` for `a ∈ coprimeClasses q`,
`b ∈ coprimeClasses r`: fiber discrepancy sum + non-coprime primes + principal discretization error. -/
lemma localRemainder_decomp {r q a b Y : ℕ} (hr : 0 < r) (hq : 0 < q) (hrY : r ≤ Y) (hqY : q ≤ Y)
    (hY : 2 ≤ Y) (ha : Nat.Coprime a q) (hb : b < r) (hbr : Nat.Coprime b r) [NeZero (r * q)]
    (β : ℝ) :
    ‖localRemainder r b Y a q β‖ ≤
      ‖∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) *
          unitClassDiscrepancy r q Y β u‖ +
      Real.log (2 * (Y : ℝ)) +
      (16 * (r : ℝ) + 16 * (Y : ℝ) * |β|) / ((r.totient : ℝ) * (q.totient : ℝ)) := by
  have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hq_pos : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hY_pos : (0 : ℝ) < Y := Nat.cast_pos.mpr (by omega)
  let U_sum : ℂ := ∑ n ∈ Finset.Icc 1 Y,
    (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * e ((β / (r : ℝ)) * (n : ℝ))
  let F_sum : ℂ := e (-((β * (b : ℝ)) / (r : ℝ))) *
    ∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) *
      unitClassDiscrepancy r q Y β u
  let NC_sum : ℂ := e (-((β * (b : ℝ)) / (r : ℝ))) *
    ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => n % r = b ∧ ¬ Nat.Coprime n (r * q)),
      (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
        e ((a : ℝ) * (((n - b) / r : ℕ) : ℝ) / (q : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ))
  let M_main : ℂ := e (-((β * (b : ℝ)) / (r : ℝ))) *
    (((1 : ℂ) / ((r * q).totient : ℂ)) * U_sum *
      ∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)))
  -- Step 1: Exact identity `smoothedPrimeSum r b Y (a / q + β) = F_sum + NC_sum + M_main`.
  have hS_eq : smoothedPrimeSum r b Y ((a : ℝ) / (q : ℝ) + β) = F_sum + NC_sum + M_main := by
    -- Reindex `smoothedPrimeSum` to `n ∈ (Icc 1 Y).filter (fun n => n % r = b)`.
    have hreidx : smoothedPrimeSum r b Y ((a : ℝ) / (q : ℝ) + β) =
        e (-((β * (b : ℝ)) / (r : ℝ))) *
          ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => n % r = b),
            (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
              e ((a : ℝ) * (((n - b) / r : ℕ) : ℝ) / (q : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ)) := by
      unfold smoothedPrimeSum
      rw [Finset.mul_sum]
      let J0 := (Finset.range (Y / r + 1)).filter (fun j => 1 ≤ r * j + b ∧ r * j + b ≤ Y)
      have htrim : ∑ j ∈ Finset.range (Y / r + 1),
            ((quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * primeWeight (r * j + b) : ℝ) : ℂ) *
              e (((a : ℝ) / (q : ℝ) + β) * (j : ℝ)) =
          ∑ j ∈ J0,
            ((quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * primeWeight (r * j + b) : ℝ) : ℂ) *
              e (((a : ℝ) / (q : ℝ) + β) * (j : ℝ)) := by
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
        refine ⟨n / r, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
          (Nat.lt_succ_of_le (Nat.div_le_div_right hIcc.2)), hnj.symm ▸ hIcc.1, hnj.symm ▸ hIcc.2⟩, hnj⟩
      · intro j _
        have hsub_div : (r * j + b - b) / r = j := by rw [Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hr]
        rw [hsub_div]
        have hexp : e (((a : ℝ) / (q : ℝ) + β) * (j : ℝ)) =
            e (-((β * (b : ℝ)) / (r : ℝ))) *
              (e ((a : ℝ) * (j : ℝ) / (q : ℝ)) * e ((β / (r : ℝ)) * ((r * j + b : ℕ) : ℝ))) := by
          rw [← e_add, ← e_add]; congr 1; push_cast; field_simp [hr_pos.ne', hq_pos.ne']; ring
        rw [hexp]; push_cast; ring
    rw [hreidx]
    -- Split `n` into `Nat.Coprime n (r * q)` and `¬ Nat.Coprime n (r * q)`.
    have hsplit_cop :
        ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => n % r = b),
            (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
              e ((a : ℝ) * (((n - b) / r : ℕ) : ℝ) / (q : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ)) =
        (∑ n ∈ (Finset.Icc 1 Y).filter (fun n => n % r = b ∧ Nat.Coprime n (r * q)),
            (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
              e ((a : ℝ) * (((n - b) / r : ℕ) : ℝ) / (q : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ))) +
        (∑ n ∈ (Finset.Icc 1 Y).filter (fun n => n % r = b ∧ ¬ Nat.Coprime n (r * q)),
            (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
              e ((a : ℝ) * (((n - b) / r : ℕ) : ℝ) / (q : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ))) := by
      have h := (Finset.sum_filter_add_sum_filter_not
        ((Finset.Icc 1 Y).filter (fun n => n % r = b)) (fun n => Nat.Coprime n (r * q))
        (fun n => (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
          e ((a : ℝ) * (((n - b) / r : ℕ) : ℝ) / (q : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ)))).symm
      have hf1 : ((Finset.Icc 1 Y).filter (fun n => n % r = b)).filter (fun n => Nat.Coprime n (r * q)) =
          (Finset.Icc 1 Y).filter (fun n => n % r = b ∧ Nat.Coprime n (r * q)) := by ext n; simp [and_assoc]
      have hf2 : ((Finset.Icc 1 Y).filter (fun n => n % r = b)).filter (fun n => ¬ Nat.Coprime n (r * q)) =
          (Finset.Icc 1 Y).filter (fun n => n % r = b ∧ ¬ Nat.Coprime n (r * q)) := by ext n; simp [and_assoc]
      rwa [hf1, hf2] at h
    -- Partition the coprime sum by `u = (n : ZMod (r * q)) ∈ charSupp r q b`.
    have hcop_fiber :
        ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => n % r = b ∧ Nat.Coprime n (r * q)),
            (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
              e ((a : ℝ) * (((n - b) / r : ℕ) : ℝ) / (q : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ)) =
        ∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) *
          ∑ n ∈ (Finset.Icc 1 Y).filter (fun n : ℕ => (n : ZMod (r * q)) = u),
            (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
              e ((β / (r : ℝ)) * (n : ℝ)) := by
      have hfib := (Finset.sum_fiberwise_of_maps_to
        (s := (Finset.Icc 1 Y).filter (fun n => n % r = b ∧ Nat.Coprime n (r * q)))
        (t := charSupp r q b)
        (g := fun n : ℕ => (n : ZMod (r * q)))
        (fun n hn => by
          have h2 := (Finset.mem_filter.mp hn).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (ZMod.isUnit_iff_coprime n (r * q)).2 h2.2, ?_⟩
          rw [ZMod.val_natCast, Nat.mod_mul_right_mod, h2.1, Nat.mod_eq_of_lt hb])
        (fun n => (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
          e ((a : ℝ) * (((n - b) / r : ℕ) : ℝ) / (q : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ)))).symm
      rw [hfib]
      refine Finset.sum_congr rfl fun u hu => ?_
      have hset : ((Finset.Icc 1 Y).filter (fun n => n % r = b ∧ Nat.Coprime n (r * q))).filter
            (fun n : ℕ => (n : ZMod (r * q)) = u) =
          (Finset.Icc 1 Y).filter (fun n : ℕ => (n : ZMod (r * q)) = u) := by
        ext n; simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨hn1, _⟩, hn2⟩; exact ⟨hn1, hn2⟩
        · rintro ⟨hn1, hn2⟩
          have hu' := (Finset.mem_filter.mp hu).2
          have hmod : n % r = b := by
            have h1 := congrArg ZMod.val hn2
            rw [ZMod.val_natCast] at h1
            have h2 : n % r = u.val % r := by rw [← h1, Nat.mod_mul_right_mod]
            rw [h2, hu'.2, Nat.mod_eq_of_lt hb]
          have hcop : Nat.Coprime n (r * q) := (ZMod.isUnit_iff_coprime n (r * q)).1 (hn2.symm ▸ hu'.1)
          exact ⟨⟨hn1, hmod, hcop⟩, hn2⟩
      rw [hset, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hnu : (n : ZMod (r * q)) = u := (Finset.mem_filter.mp hn).2
      have hmod_rq : n % (r * q) = u.val := by
        have := congrArg ZMod.val hnu; rwa [ZMod.val_natCast] at this
      have hmod_r : n % r = b := by
        have h1 : n % r = u.val % r := by rw [← hmod_rq, Nat.mod_mul_right_mod]
        rw [h1, (Finset.mem_filter.mp hu).2.2, Nat.mod_eq_of_lt hb]
      -- Show `(n - b) / r ≡ u.val / r [MOD q]`.
      have he_eq : e ((a : ℝ) * (((n - b) / r : ℕ) : ℝ) / (q : ℝ)) =
          e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) := by
        have hnb : (n - b) / r = n / r := by
          conv_lhs => rw [← Nat.div_add_mod n r, hmod_r]
          rw [Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hr]
        have hdiv_n : r * ((n - b) / r) + b = n := by
          rw [hnb, ← hmod_r]; exact Nat.div_add_mod n r
        have hdiv_u : r * (u.val / r) + b = u.val := by
          have hd := Nat.div_add_mod u.val r
          have hmu : u.val % r = b := by rw [(Finset.mem_filter.mp hu).2.2, Nat.mod_eq_of_lt hb]
          omega
        let t := n / (r * q)
        have hdiv_rq : r * q * t + u.val = n := by
          dsimp [t]; rw [← hmod_rq]; exact Nat.div_add_mod n (r * q)
        have hq_diff : (n - b) / r = q * t + u.val / r := by
          apply Nat.eq_of_mul_eq_mul_left hr
          nlinarith
        apply e_eq_of_sub_int (k := ((a * t : ℕ) : ℤ))
        have hcast : (((n - b) / r : ℕ) : ℝ) = (q : ℝ) * (t : ℝ) + ((u.val / r : ℕ) : ℝ) := by
          exact_mod_cast hq_diff
        rw [hcast, Int.cast_natCast, Nat.cast_mul]; field_simp [hq_pos.ne']; ring
      rw [he_eq]; ring
    rw [hsplit_cop, hcop_fiber, mul_add]
    have hsplit_u :
        e (-((β * (b : ℝ)) / (r : ℝ))) *
          ∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) *
            ∑ n ∈ (Finset.Icc 1 Y).filter (fun n : ℕ => (n : ZMod (r * q)) = u),
              (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
                e ((β / (r : ℝ)) * (n : ℝ)) = F_sum + M_main := by
      dsimp only [F_sum, M_main]
      rw [← mul_add]
      congr 1
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      dsimp only [unitClassDiscrepancy, U_sum]
      ring
    rw [hsplit_u]; ring
  -- Step 2: Bound `‖NC_sum‖ ≤ log(2 * Y)`.
  have hNC_le : ‖NC_sum‖ ≤ Real.log (2 * (Y : ℝ)) := by
    dsimp [NC_sum]
    rw [norm_mul, norm_e, one_mul]
    let Snc := (Finset.Icc 1 Y).filter (fun n => n % r = b ∧ ¬ Nat.Coprime n (r * q))
    have hsub_pf : Snc.filter Nat.Prime ⊆ q.primeFactors := by
      intro p hp
      have hmem := Finset.mem_filter.mp hp
      have hpr : p.Prime := hmem.2
      have h1 := (Finset.mem_filter.mp hmem.1).2
      have hcop_r : Nat.Coprime p r := by
        rw [Nat.Coprime, Nat.ModEq.gcd_eq (show p ≡ b [MOD r] by rw [Nat.ModEq, h1.1, Nat.mod_eq_of_lt hb])]
        exact hbr.gcd_eq_one
      have hncop_q : ¬ Nat.Coprime p q := fun hcq => h1.2 (hcop_r.mul_right hcq)
      have hpdvd : p ∣ q := by
        by_contra hnd; exact hncop_q (hpr.coprime_iff_not_dvd.2 hnd)
      exact Nat.mem_primeFactors.mpr ⟨hpr, hpdvd, hq.ne'⟩
    calc ‖∑ n ∈ Snc,
            (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
              e ((a : ℝ) * (((n - b) / r : ℕ) : ℝ) / (q : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ))‖
        ≤ ∑ n ∈ Snc, primeWeight n := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
          rw [norm_mul, norm_mul, norm_mul, norm_e, norm_e, mul_one, mul_one,
              Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (quarticBump_nonneg _), abs_of_nonneg (primeWeight_nonneg _)]
          exact mul_le_of_le_one_left (primeWeight_nonneg _) (quarticBump_le_one _)
      _ = ∑ p ∈ Snc.filter Nat.Prime, Real.log (p : ℝ) := by
          symm
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun n _ => ?_
          unfold primeWeight; split_ifs <;> rfl
      _ ≤ ∑ p ∈ q.primeFactors, Real.log (p : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_pf fun p hp _ =>
            Real.log_nonneg (Nat.one_le_cast.mpr (Nat.prime_of_mem_primeFactors hp).pos)
      _ = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) :=
          (Real.log_prod fun p hp => Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).pos.ne').symm
      _ ≤ Real.log (q : ℝ) := by
          apply Real.log_le_log (Finset.prod_pos fun p hp => Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos)
          rw [← Nat.cast_prod]
          exact Nat.cast_le.mpr (Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q))
      _ ≤ Real.log (2 * (Y : ℝ)) := Real.log_le_log hq_pos (by
          have : (q : ℝ) ≤ Y := Nat.cast_le.mpr hqY; linarith)
  -- Step 3: Bound `‖M_main - localModelTerm r b Y a q β‖ ≤ (16 * r + 16 * Y * |β|) / (φ(r) * φ(q))`.
  have hM_le : ‖M_main - localModelTerm r b Y a q β‖ ≤
      (16 * (r : ℝ) + 16 * (Y : ℝ) * |β|) / ((r.totient : ℝ) * (q.totient : ℝ)) := by
    -- Relate `∑ u ∈ charSupp r q b, e(a * (u.val / r) / q)` to `charCoeff r q a b 1`!
    have hcc_eq : ((1 : ℂ) / ((r * q).totient : ℂ)) *
          ∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) =
        e (-((a : ℝ) * (b : ℝ) / ((r * q : ℕ) : ℝ))) *
          charCoeff r q a b (1 : DirichletCharacter ℂ (r * q)) := by
      unfold charCoeff
      have h1 : charCoeff r q a b (1 : DirichletCharacter ℂ (r * q)) =
          ((1 : ℂ) / ((r * q).totient : ℂ)) *
            ∑ u ∈ charSupp r q b, e ((a : ℝ) * (u.val : ℝ) / ((r * q : ℕ) : ℝ)) := by
        unfold charCoeff charSupp
        congr 1; refine Finset.sum_congr rfl fun u hu => ?_
        rw [MulChar.one_apply (Finset.mem_filter.mp hu).2.1, star_one, mul_one]
      change ((1 : ℂ) / ((r * q).totient : ℂ)) *
          ∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) = _
      have h2 : e (-((a : ℝ) * (b : ℝ) / ((r * q : ℕ) : ℝ))) *
            (((1 : ℂ) / ((r * q).totient : ℂ)) *
              ∑ u ∈ charSupp r q b, e ((a : ℝ) * (u.val : ℝ) / ((r * q : ℕ) : ℝ))) =
          ((1 : ℂ) / ((r * q).totient : ℂ)) *
            ∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) := by
        rw [mul_left_comm, Finset.mul_sum]
        congr 1; refine Finset.sum_congr rfl fun u hu => ?_
        have hmu : u.val % r = b := by rw [(Finset.mem_filter.mp hu).2.2, Nat.mod_eq_of_lt hb]
        have hdiv : r * (u.val / r) + b = u.val := by have := Nat.div_add_mod u.val r; omega
        rw [← e_add]; congr 1
        have hdivR : (r : ℝ) * ((u.val / r : ℕ) : ℝ) + (b : ℝ) = (u.val : ℝ) := by exact_mod_cast hdiv
        push_cast; field_simp [hr_pos.ne', hq_pos.ne']; nlinarith
      exact h2.symm.trans (by
        unfold charSupp
        congr 2; refine Finset.sum_congr rfl fun u hu => ?_
        rw [MulChar.one_apply (Finset.mem_filter.mp hu).2.1, star_one, mul_one])
    have hM_rew : M_main =
        (e (-((a : ℝ) * (b : ℝ) / ((r * q : ℕ) : ℝ))) *
          charCoeff r q a b (1 : DirichletCharacter ℂ (r * q))) *
        (e (-((β * (b : ℝ)) / (r : ℝ))) * U_sum) := by
      dsimp [M_main]
      rw [← hcc_eq]; ring
    rw [hM_rew]
    by_cases hcop_qr : Nat.Coprime q r
    · have hcc := charCoeff_one_coprime hr hq hb ha hbr hcop_qr
      rw [hcc]
      unfold localModelTerm
      rw [ite_eq_left hcop_qr]
      have hfactor :
          e (-((a : ℝ) * (rInv r q : ℝ) * (b : ℝ) / (q : ℝ))) *
              (ArithmeticFunction.moebius q : ℂ) / ((r.totient : ℂ) * (q.totient : ℂ)) *
              (e (-((β * (b : ℝ)) / (r : ℝ))) * U_sum) -
            e (-((a : ℝ) * (rInv r q : ℝ) * (b : ℝ) / (q : ℝ))) *
              (((r : ℝ) / (r.totient : ℝ) : ℝ) : ℂ) *
              ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) *
              smoothedKernel r b Y β =
          (e (-((a : ℝ) * (rInv r q : ℝ) * (b : ℝ) / (q : ℝ))) *
              (ArithmeticFunction.moebius q : ℂ) / ((r.totient : ℂ) * (q.totient : ℂ))) *
            (e (-((β * (b : ℝ)) / (r : ℝ))) * U_sum - (r : ℂ) * smoothedKernel r b Y β) := by
        have hr0 : (r.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hr).ne'
        have hq0 : (q.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hq).ne'
        push_cast; field_simp [hr0, hq0]
      rw [hfactor, norm_mul]
      have hmu1 : ‖(ArithmeticFunction.moebius q : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        by_cases hsf : Squarefree q
        · rw [ArithmeticFunction.moebius_apply_of_squarefree hsf]; simp
        · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; simp
      have hcoeff : ‖e (-((a : ℝ) * (rInv r q : ℝ) * (b : ℝ) / (q : ℝ))) *
            (ArithmeticFunction.moebius q : ℂ) / ((r.totient : ℂ) * (q.totient : ℂ))‖ ≤
          1 / ((r.totient : ℝ) * (q.totient : ℝ)) := by
        rw [norm_div, norm_mul, norm_e, one_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
        exact div_le_div_of_nonneg_right hmu1 (by positivity)
      have happrox := principalSum_approx_smoothedKernel hr hb hrY β
      calc ‖e (-((a : ℝ) * (rInv r q : ℝ) * (b : ℝ) / (q : ℝ))) *
              (ArithmeticFunction.moebius q : ℂ) / ((r.totient : ℂ) * (q.totient : ℂ))‖ *
            ‖e (-((β * (b : ℝ)) / (r : ℝ))) * U_sum - (r : ℂ) * smoothedKernel r b Y β‖
          ≤ (1 / ((r.totient : ℝ) * (q.totient : ℝ))) * (16 * (r : ℝ) + 16 * (Y : ℝ) * |β|) :=
            mul_le_mul hcoeff happrox (norm_nonneg _) (by positivity)
        _ = (16 * (r : ℝ) + 16 * (Y : ℝ) * |β|) / ((r.totient : ℝ) * (q.totient : ℝ)) := by ring
    · have hg : 1 < Nat.gcd r q := by
        have hpos := Nat.gcd_pos_of_pos_left q hr
        have hne : Nat.gcd r q ≠ 1 := fun h => hcop_qr (by rwa [Nat.Coprime, Nat.gcd_comm])
        omega
      rw [charCoeff_one_eq_zero_of_one_lt_gcd r q a b hr hq ha hbr hg]
      unfold localModelTerm
      rw [ite_eq_right hcop_qr]
      simp only [mul_zero, zero_mul, sub_zero, norm_zero]
      positivity
  -- Combine Steps 1–3 via triangle inequality.
  unfold localRemainder
  rw [hS_eq]
  have hcomb : F_sum + NC_sum + M_main - localModelTerm r b Y a q β =
      F_sum + NC_sum + (M_main - localModelTerm r b Y a q β) := by ring
  rw [hcomb]
  have hF_norm : ‖F_sum‖ =
      ‖∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) *
        unitClassDiscrepancy r q Y β u‖ := by
    dsimp [F_sum]; rw [norm_mul, norm_e, one_mul]
  have htri : ‖F_sum + NC_sum + (M_main - localModelTerm r b Y a q β)‖ ≤
      ‖F_sum‖ + ‖NC_sum‖ + ‖M_main - localModelTerm r b Y a q β‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  linarith [htri, hF_norm, hNC_le, hM_le]

/-- **Module F2 Main Theorem 1 (`avg_remainder_sq`, inequality `(7)`):**
Under `SmoothedTwistEstimate` with constant `C > 0`, for `Q = routeAQ Y r`, `1 ≤ r ≤ Y`, `2^26 ≤ Y / r`,
uniformly for ALL `α : ℝ`:
`(1 / φ(r)) * ∑_{b ∈ U_r} ‖S_b(α) - M_b(α)‖² ≤ C_avg * (r / φ(r)) * (Y / r) * √(Y / r) * log²(2Y)`. -/
theorem avg_remainder_sq {C : ℝ} (hC : 0 < C)
    (hTw : ∀ (Y d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (t : ℝ),
      2 ≤ Y → |t| ≤ 1 / 2 →
        ‖smoothedTiltedRemainder χ Y t‖ ≤
          C * Real.sqrt ((Y : ℝ) * (1 + |t| * Y)) * Real.log (2 * (d : ℝ) * Y))
    {r Y : ℕ} (hr : 0 < r) (hrY : r ≤ Y) (hH : 2 ^ 26 ≤ Y / r) (α : ℝ) :
    (1 / (r.totient : ℝ)) *
        ∑ b ∈ coprimeClasses r,
          ‖smoothedPrimeSum r b Y α - modelSum r b Y (routeAQ Y r) (routeAQ Y r) α‖ ^ 2 ≤
      (3 * (3 * C + 1) ^ 2 * (2 : ℝ) ^ 15 + 3 + 3 * (2 : ℝ) ^ 39) *
        ((r : ℝ) / (r.totient : ℝ)) *
        ((Y : ℝ) / (r : ℝ)) * Real.sqrt ((Y : ℝ) / (r : ℝ)) * (Real.log (2 * (Y : ℝ))) ^ 2 := by
  set Q := routeAQ Y r
  obtain ⟨hQ_ge2, hQ_lo, hQ_hi, hQ_le_Y⟩ := routeAQ_bounds hr hH
  have hQ_pos : 0 < Q := by omega
  have hY_ge2 : 2 ≤ Y := by
    have : 2 ≤ Y / r := by omega
    have := Nat.mul_div_le Y r; nlinarith
  have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hY_pos : (0 : ℝ) < Y := Nat.cast_pos.mpr (by omega)
  have hφr_pos : (0 : ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  set H : ℝ := (Y : ℝ) / (r : ℝ)
  set L : ℝ := Real.log (2 * (Y : ℝ))
  set κ : ℝ := (r : ℝ) / (r.totient : ℝ)
  have hH_ge1 : 1 ≤ H := (one_le_div hr_pos).2 (Nat.cast_le.mpr hrY)
  have hrtH_ge1 : 1 ≤ Real.sqrt H := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hH_ge1
  have hL_ge1 : 1 ≤ L := one_le_log_two_mul hY_ge2
  have hκ_ge1 : 1 ≤ κ := (one_le_div hφr_pos).2 (Nat.cast_le.mpr (Nat.totient_le r))
  have hκ_le : κ ≤ 2 * L :=
    (div_totient_le_two_log hr).trans
      (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by
        have : (r : ℝ) ≤ Y := Nat.cast_le.mpr hrY; linarith)) (by norm_num))
  -- Locate the Voronoi cell `c ∈ centers Q` containing `α`.
  obtain ⟨c, hc_mem, hα_cell⟩ := voronoiCell_cover Q hQ_pos α
  set q := c.q
  set a := c.a
  have hq_pos : 0 < q := c.q_pos
  have hq_le_Q : q ≤ Q := mem_centers_iff.mp hc_mem
  have hq_le_Y : q ≤ Y := hq_le_Q.trans hQ_le_Y
  have : NeZero (r * q) := ⟨Nat.mul_ne_zero hr.ne' hq_pos.ne'⟩
  set β := wrap (α - c.val)
  have hβ_half : |β| ≤ 1 / 2 := abs_wrap_le_half _
  have hβ_outer : |β| ≤ 1 / ((q : ℝ) * (Q : ℝ)) := voronoiCell_outer_radius hQ_pos hα_cell
  -- Key Farey budget: `q * (1 + H * |β|) ≤ 2^15 * √H` and `1 + H * |β| ≤ 2^15 * √H`.
  have hqJ_le : (q : ℝ) * (1 + H * |β|) ≤ (2 : ℝ) ^ 15 * Real.sqrt H := by
    have hq_le_rt : (q : ℝ) ≤ Real.sqrt H :=
      (Nat.cast_le.mpr hq_le_Q).trans (hQ_hi.trans (by
        have h12 : (1 / (2 : ℝ) ^ 12) ≤ 1 := by norm_num
        nlinarith [Real.sqrt_nonneg H]))
    have hqβ : (q : ℝ) * |β| ≤ 1 / (Q : ℝ) := by
      have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq_pos
      have hQR : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ_pos
      calc (q : ℝ) * |β| ≤ (q : ℝ) * (1 / ((q : ℝ) * (Q : ℝ))) :=
            mul_le_mul_of_nonneg_left hβ_outer hqR.le
        _ = 1 / (Q : ℝ) := by field_simp [hqR.ne', hQR.ne']
    have hHQ : H / (Q : ℝ) ≤ (2 : ℝ) ^ 14 * Real.sqrt H := by
      have hQR : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ_pos
      rw [div_le_iff₀ hQR]
      have hsq : H = Real.sqrt H * Real.sqrt H := (Real.mul_self_sqrt (by positivity)).symm
      have h14 : Real.sqrt H ≤ (2 : ℝ) ^ 14 * (Q : ℝ) := by
        have hpos14 : (0 : ℝ) < (2 : ℝ) ^ 14 := by positivity
        have hmul := mul_le_mul_of_nonneg_left hQ_lo hpos14.le
        have hcancel : (2 : ℝ) ^ 14 * ((1 / (2 : ℝ) ^ 14) * Real.sqrt H) = Real.sqrt H := by
          field_simp [hpos14.ne']
        linarith
      nlinarith [Real.sqrt_nonneg H]
    have h2 : (q : ℝ) * (H * |β|) ≤ (2 : ℝ) ^ 14 * Real.sqrt H := by
      calc (q : ℝ) * (H * |β|) = H * ((q : ℝ) * |β|) := by ring
        _ ≤ H * (1 / (Q : ℝ)) := mul_le_mul_of_nonneg_left hqβ (by positivity)
        _ = H / (Q : ℝ) := by ring
        _ ≤ (2 : ℝ) ^ 14 * Real.sqrt H := hHQ
    have hpow15 : (1 : ℝ) + (2 : ℝ) ^ 14 ≤ (2 : ℝ) ^ 15 := by norm_num
    nlinarith [Real.sqrt_nonneg H]
  have hJ_le : 1 + H * |β| ≤ (2 : ℝ) ^ 15 * Real.sqrt H := by
    have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr hq_pos
    nlinarith [show (0 : ℝ) ≤ 1 + H * |β| by positivity]
  -- Pointwise squared decomposition via `(x + y + z)² ≤ 3 * (x² + y² + z²)`.
  have h3sq : ∀ x y z : ℝ, (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := fun x y z => by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have hpt : ∀ b ∈ coprimeClasses r,
      ‖smoothedPrimeSum r b Y α - modelSum r b Y Q Q α‖ ^ 2 ≤
        3 * ‖∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) *
              unitClassDiscrepancy r q Y β u‖ ^ 2 +
        3 * L ^ 2 +
        3 * ((16 * (r : ℝ) + 16 * (Y : ℝ) * |β|) / ((r.totient : ℝ) * (q.totient : ℝ))) ^ 2 := by
    intro b hb
    rw [localRemainder_eq_global_on_cell hα_cell]
    have hdec := localRemainder_decomp hr hq_pos hrY hq_le_Y hY_ge2 c.coprime
      (mem_coprimeClasses.mp hb).1 (mem_coprimeClasses.mp hb).2 β
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hdec 2
    linarith [h3sq ‖∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) *
          unitClassDiscrepancy r q Y β u‖ L
        ((16 * (r : ℝ) + 16 * (Y : ℝ) * |β|) / ((r.totient : ℝ) * (q.totient : ℝ)))]
  -- Average each of the 3 pieces over `coprimeClasses r`.
  have hcard : ((coprimeClasses r).card : ℝ) = (r.totient : ℝ) := by
    rw [card_coprimeClasses]
  have havg1 : (1 / (r.totient : ℝ)) *
        ∑ b ∈ coprimeClasses r,
          ‖∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) *
            unitClassDiscrepancy r q Y β u‖ ^ 2 ≤
      (3 * C + 1) ^ 2 * (2 : ℝ) ^ 15 * κ * H * Real.sqrt H * L ^ 2 := by
    have hfib := fiber_sq_le hr hq_pos (unitClassDiscrepancy r q Y β)
      (fun _ u => e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)))
      (fun _ _ _ _ => le_of_eq (norm_e _))
    have htot_mul : ((r * q).totient : ℝ) ≤ (q : ℝ) * (r.totient : ℝ) := by
      exact_mod_cast totient_mul_le_mul_totient r q hr hq_pos
    have hratio : ((r * q).totient : ℝ) / ((r.totient : ℝ) ^ 2) ≤ (q : ℝ) / (r.totient : ℝ) := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hφr_pos) hφr_pos]
      nlinarith
    have hmp := sum_norm_sq_unitClassDiscrepancy_le hC hTw hr hq_pos hrY hq_le_Y hY_ge2 hβ_half
    calc (1 / (r.totient : ℝ)) *
            ∑ b ∈ coprimeClasses r,
              ‖∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) *
                unitClassDiscrepancy r q Y β u‖ ^ 2
        ≤ (((r * q).totient : ℝ) / ((r.totient : ℝ) ^ 2)) *
            ∑ u ∈ zmodUnitsFinset (r * q), ‖unitClassDiscrepancy r q Y β u‖ ^ 2 := hfib
      _ ≤ ((q : ℝ) / (r.totient : ℝ)) *
            ((3 * C + 1) ^ 2 * (Y : ℝ) * (1 + H * |β|) * L ^ 2) :=
          mul_le_mul hratio hmp (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      _ = (3 * C + 1) ^ 2 * κ * H * ((q : ℝ) * (1 + H * |β|)) * L ^ 2 := by
          dsimp [κ, H]; field_simp [hr_pos.ne', hφr_pos.ne']
      _ ≤ (3 * C + 1) ^ 2 * κ * H * ((2 : ℝ) ^ 15 * Real.sqrt H) * L ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hqJ_le (by positivity)) (sq_nonneg L)
      _ = (3 * C + 1) ^ 2 * (2 : ℝ) ^ 15 * κ * H * Real.sqrt H * L ^ 2 := by ring
  have havg2 : L ^ 2 ≤ κ * H * Real.sqrt H * L ^ 2 := by
    have h1 : (1 : ℝ) ≤ κ * H := by nlinarith only [hκ_ge1, hH_ge1]
    have h2 : (1 : ℝ) ≤ κ * H * Real.sqrt H := by nlinarith only [h1, hrtH_ge1]
    nlinarith only [h2, sq_nonneg L]
  have havg3 : ((16 * (r : ℝ) + 16 * (Y : ℝ) * |β|) / ((r.totient : ℝ) * (q.totient : ℝ))) ^ 2 ≤
      (2 : ℝ) ^ 39 * κ * H * Real.sqrt H * L ^ 2 := by
    have hqt1 : (1 : ℝ) ≤ q.totient := Nat.one_le_cast.mpr (Nat.totient_pos.mpr hq_pos)
    have hrew : (16 * (r : ℝ) + 16 * (Y : ℝ) * |β|) / ((r.totient : ℝ) * (q.totient : ℝ)) =
        (16 * κ * (1 + H * |β|)) / (q.totient : ℝ) := by
      dsimp [κ, H]; field_simp [hr_pos.ne', hφr_pos.ne', (by linarith only [hqt1] : (q.totient : ℝ) ≠ 0)]
    rw [hrew]
    have hle1 : (16 * κ * (1 + H * |β|)) / (q.totient : ℝ) ≤ 16 * κ * ((2 : ℝ) ^ 15 * Real.sqrt H) := by
      calc (16 * κ * (1 + H * |β|)) / (q.totient : ℝ)
          ≤ 16 * κ * (1 + H * |β|) := div_le_self (by positivity) hqt1
        _ ≤ 16 * κ * ((2 : ℝ) ^ 15 * Real.sqrt H) := mul_le_mul_of_nonneg_left hJ_le (by positivity)
    have hsq := pow_le_pow_left₀ (by positivity) hle1 2
    have hκsq : κ ^ 2 ≤ 2 * κ * L ^ 2 := by
      have h1 : κ * κ ≤ κ * (2 * L) := mul_le_mul_of_nonneg_left hκ_le (by positivity)
      have hLL : L ≤ L * L := by nlinarith only [hL_ge1]
      have h2 : 2 * κ * L ≤ 2 * κ * (L * L) := mul_le_mul_of_nonneg_left hLL (by positivity)
      calc κ ^ 2 = κ * κ := sq κ
        _ ≤ κ * (2 * L) := h1
        _ = 2 * κ * L := by ring
        _ ≤ 2 * κ * (L * L) := h2
        _ = 2 * κ * L ^ 2 := by ring
    have h38 : (16 : ℝ) ^ 2 * ((2 : ℝ) ^ 15) ^ 2 = (2 : ℝ) ^ 38 := by
      rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num, ← pow_mul, ← pow_mul, ← pow_add]
    have h39 : (2 : ℝ) ^ 38 * 2 = (2 : ℝ) ^ 39 := by rw [← pow_succ]
    calc ((16 * κ * (1 + H * |β|)) / (q.totient : ℝ)) ^ 2
        ≤ (16 * κ * ((2 : ℝ) ^ 15 * Real.sqrt H)) ^ 2 := hsq
      _ = (2 : ℝ) ^ 38 * κ ^ 2 * H := by
          rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
          calc (16 : ℝ) ^ 2 * κ ^ 2 * (((2 : ℝ) ^ 15) ^ 2 * H)
              = ((16 : ℝ) ^ 2 * ((2 : ℝ) ^ 15) ^ 2) * κ ^ 2 * H := by ring
            _ = (2 : ℝ) ^ 38 * κ ^ 2 * H := by rw [h38]
      _ ≤ (2 : ℝ) ^ 38 * (2 * κ * L ^ 2) * H :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκsq (by positivity)) (by positivity)
      _ = (2 : ℝ) ^ 39 * κ * H * L ^ 2 := by
          calc (2 : ℝ) ^ 38 * (2 * κ * L ^ 2) * H
              = ((2 : ℝ) ^ 38 * 2) * κ * H * L ^ 2 := by ring
            _ = (2 : ℝ) ^ 39 * κ * H * L ^ 2 := by rw [h39]
      _ ≤ (2 : ℝ) ^ 39 * κ * H * Real.sqrt H * L ^ 2 := by
          have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ 39 * κ * H * L ^ 2 := by positivity
          nlinarith only [hnn, hrtH_ge1]
  -- Sum `hpt` over `b ∈ coprimeClasses r` and divide by `φ(r)`.
  have hsum := Finset.sum_le_sum hpt
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hcard] at hsum
  have hdiv := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 1 / (r.totient : ℝ))
  have hcancel : (1 / (r.totient : ℝ)) *
      (3 * ∑ b ∈ coprimeClasses r,
          ‖∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) *
            unitClassDiscrepancy r q Y β u‖ ^ 2 +
        (r.totient : ℝ) * (3 * L ^ 2) +
        (r.totient : ℝ) *
          (3 * ((16 * (r : ℝ) + 16 * (Y : ℝ) * |β|) / ((r.totient : ℝ) * (q.totient : ℝ))) ^ 2)) =
      3 * ((1 / (r.totient : ℝ)) *
        ∑ b ∈ coprimeClasses r,
          ‖∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) *
            unitClassDiscrepancy r q Y β u‖ ^ 2) +
      3 * L ^ 2 +
      3 * ((16 * (r : ℝ) + 16 * (Y : ℝ) * |β|) / ((r.totient : ℝ) * (q.totient : ℝ))) ^ 2 := by
    field_simp [hφr_pos.ne']
  linarith [hdiv, hcancel, havg1, havg2, havg3]

/-- **Module F2 Main Theorem 2 (`fixed_num_remainder_sq`, inequality `(8)`):**
Under `SmoothedTwistEstimate` with constant `C > 0`, for EVERY fixed `b ∈ coprimeClasses r`,
EVERY `1 ≤ q ≤ Y`, and EVERY `|β| ≤ 1/2`:
`∑_{a ∈ U_q} ‖localRemainder r b Y a q β‖² ≤ (3*(3*C+1)² + 3075) * q * Y * (1 + (Y/r)*|β|) * log²(2Y)`. -/
theorem fixed_num_remainder_sq {C : ℝ} (hC : 0 < C)
    (hTw : ∀ (Y d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (t : ℝ),
      2 ≤ Y → |t| ≤ 1 / 2 →
        ‖smoothedTiltedRemainder χ Y t‖ ≤
          C * Real.sqrt ((Y : ℝ) * (1 + |t| * Y)) * Real.log (2 * (d : ℝ) * Y))
    {r b Y q : ℕ} (hr : 0 < r) (hrY : r ≤ Y) (hY : 2 ≤ Y) (hq : 0 < q) (hqY : q ≤ Y)
    (hb : b < r) (hbr : Nat.Coprime b r) {β : ℝ} (hβ : |β| ≤ 1 / 2) :
    ∑ a ∈ coprimeClasses q, ‖localRemainder r b Y a q β‖ ^ 2 ≤
      (3 * (3 * C + 1) ^ 2 + 3075) *
        (q : ℝ) * (Y : ℝ) * (1 + ((Y : ℝ) / (r : ℝ)) * |β|) * (Real.log (2 * (Y : ℝ))) ^ 2 := by
  have : NeZero (r * q) := ⟨Nat.mul_ne_zero hr.ne' hq.ne'⟩
  have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hq_pos : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hY_pos : (0 : ℝ) < Y := Nat.cast_pos.mpr (by omega)
  have hφr_pos : (0 : ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hφq_pos : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  set H : ℝ := (Y : ℝ) / (r : ℝ)
  set L : ℝ := Real.log (2 * (Y : ℝ))
  set κ : ℝ := (r : ℝ) / (r.totient : ℝ)
  have hκ_le : κ ≤ 2 * L :=
    (div_totient_le_two_log hr).trans
      (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by
        have : (r : ℝ) ≤ Y := Nat.cast_le.mpr hrY; linarith)) (by norm_num))
  have h3sq : ∀ x y z : ℝ, (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := fun x y z => by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have hpt : ∀ a ∈ coprimeClasses q,
      ‖localRemainder r b Y a q β‖ ^ 2 ≤
        3 * ‖∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) *
              unitClassDiscrepancy r q Y β u‖ ^ 2 +
        3 * L ^ 2 +
        3 * ((16 * (r : ℝ) + 16 * (Y : ℝ) * |β|) / ((r.totient : ℝ) * (q.totient : ℝ))) ^ 2 := by
    intro a ha
    have hdec := localRemainder_decomp hr hq hrY hqY hY (mem_coprimeClasses.mp ha).2 hb hbr β
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hdec 2
    linarith [h3sq ‖∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) *
          unitClassDiscrepancy r q Y β u‖ L
        ((16 * (r : ℝ) + 16 * (Y : ℝ) * |β|) / ((r.totient : ℝ) * (q.totient : ℝ)))]
  -- Piece 1: Fixed-fiber additive Parseval `(6)` + multiplicative Parseval `(4)`.
  have hsum1 : ∑ a ∈ coprimeClasses q,
        ‖∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) *
          unitClassDiscrepancy r q Y β u‖ ^ 2 ≤
      (3 * C + 1) ^ 2 * (q : ℝ) * (Y : ℝ) * (1 + H * |β|) * L ^ 2 := by
    have hsub_a : coprimeClasses q ⊆ Finset.range q := Finset.filter_subset _ _
    have hsub_u : charSupp r q b ⊆ zmodUnitsFinset (r * q) := fun u hu =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2.1⟩
    calc ∑ a ∈ coprimeClasses q,
            ‖∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) *
              unitClassDiscrepancy r q Y β u‖ ^ 2
        ≤ ∑ a ∈ Finset.range q,
            ‖∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) *
              unitClassDiscrepancy r q Y β u‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_a fun _ _ _ => sq_nonneg _
      _ = (q : ℝ) * ∑ u ∈ charSupp r q b, ‖unitClassDiscrepancy r q Y β u‖ ^ 2 :=
          fixed_fiber_additive_parseval hr hq hb (unitClassDiscrepancy r q Y β)
      _ ≤ (q : ℝ) * ∑ u ∈ zmodUnitsFinset (r * q), ‖unitClassDiscrepancy r q Y β u‖ ^ 2 :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg hsub_u fun _ _ _ => sq_nonneg _) hq_pos.le
      _ ≤ (q : ℝ) * ((3 * C + 1) ^ 2 * (Y : ℝ) * (1 + H * |β|) * L ^ 2) :=
          mul_le_mul_of_nonneg_left
            (sum_norm_sq_unitClassDiscrepancy_le hC hTw hr hq hrY hqY hY hβ) hq_pos.le
      _ = (3 * C + 1) ^ 2 * (q : ℝ) * (Y : ℝ) * (1 + H * |β|) * L ^ 2 := by ring
  -- Piece 2: `φ(q) * L² ≤ q * Y * (1 + H * |β|) * L²`.
  have hsum2 : (q.totient : ℝ) * L ^ 2 ≤ (q : ℝ) * (Y : ℝ) * (1 + H * |β|) * L ^ 2 := by
    have hqtot : (q.totient : ℝ) ≤ (q : ℝ) := Nat.cast_le.mpr (Nat.totient_le q)
    have hY1 : (1 : ℝ) ≤ Y := Nat.one_le_cast.mpr (by omega)
    have hJ1 : (1 : ℝ) ≤ 1 + H * |β| := by linarith [show (0 : ℝ) ≤ H * |β| by positivity]
    have hqY1 : (q : ℝ) ≤ (q : ℝ) * (Y : ℝ) := by nlinarith
    have h1 : (q.totient : ℝ) ≤ (q : ℝ) * (Y : ℝ) * (1 + H * |β|) := by nlinarith
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg L)
  -- Piece 3: `φ(q) * ((16*r + 16*Y*|β|) / (φ(r)*φ(q)))² ≤ 1024 * q * Y * (1 + H * |β|) * L²`.
  have hsum3 : (q.totient : ℝ) *
        ((16 * (r : ℝ) + 16 * (Y : ℝ) * |β|) / ((r.totient : ℝ) * (q.totient : ℝ))) ^ 2 ≤
      1024 * (q : ℝ) * (Y : ℝ) * (1 + H * |β|) * L ^ 2 := by
    have hrew : (q.totient : ℝ) *
          ((16 * (r : ℝ) + 16 * (Y : ℝ) * |β|) / ((r.totient : ℝ) * (q.totient : ℝ))) ^ 2 =
        256 * κ ^ 2 * (1 + H * |β|) ^ 2 / (q.totient : ℝ) := by
      dsimp [κ, H]; field_simp [hr_pos.ne', hφr_pos.ne', hφq_pos.ne']; ring
    rw [hrew]
    have hqt1 : (1 : ℝ) ≤ q.totient := Nat.one_le_cast.mpr (Nat.totient_pos.mpr hq)
    have hJ_le_Y : 1 + H * |β| ≤ (Y : ℝ) := by
      have hr1 : (1 : ℝ) ≤ r := Nat.one_le_cast.mpr hr
      have hH_le_Y : H ≤ (Y : ℝ) := by
        dsimp [H]; exact div_le_self hY_pos.le hr1
      have hY2 : (2 : ℝ) ≤ Y := Nat.cast_le.mpr hY
      have h1 : H * |β| ≤ (Y : ℝ) * (1 / 2) :=
        mul_le_mul hH_le_Y hβ (abs_nonneg _) hY_pos.le
      linarith
    have hκsq : κ ^ 2 ≤ 4 * L ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hκ_le 2
      linarith
    have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr hq
    calc 256 * κ ^ 2 * (1 + H * |β|) ^ 2 / (q.totient : ℝ)
        ≤ 256 * κ ^ 2 * (1 + H * |β|) ^ 2 := div_le_self (by positivity) hqt1
      _ = 256 * κ ^ 2 * (1 + H * |β|) * (1 + H * |β|) := by ring
      _ ≤ 256 * (4 * L ^ 2) * (1 + H * |β|) * (Y : ℝ) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hκsq (by norm_num)) (by positivity))
            hJ_le_Y (by positivity) (by positivity)
      _ = 1024 * (Y : ℝ) * (1 + H * |β|) * L ^ 2 := by ring
      _ ≤ 1024 * (q : ℝ) * (Y : ℝ) * (1 + H * |β|) * L ^ 2 := by
          have hnn : (0 : ℝ) ≤ 1024 * (Y : ℝ) * (1 + H * |β|) * L ^ 2 := by positivity
          nlinarith
  have hsum := Finset.sum_le_sum hpt
  have hcard : ((coprimeClasses q).card : ℝ) = (q.totient : ℝ) := by rw [card_coprimeClasses]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hcard] at hsum
  linarith [hsum, hsum1, hsum2, hsum3]

end LocalAndGlobalRemainder

section SecondDifferenceKernelDecay

/-- First derivative of `quarticBump`: continuous on all of `ℝ` and `32`-Lipschitz. -/
noncomputable def quarticBumpDeriv (x : ℝ) : ℝ :=
  if 0 < x ∧ x < 1 then 16 * (2 * x - 6 * x ^ 2 + 4 * x ^ 3) else 0

lemma quarticBumpDeriv_eq_poly_on_Icc {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    quarticBumpDeriv x = 16 * (2 * x - 6 * x ^ 2 + 4 * x ^ 3) := by
  unfold quarticBumpDeriv
  rcases eq_or_lt_of_le hx0 with rfl | h0
  · simp
  · rcases eq_or_lt_of_le hx1 with rfl | h1
    · norm_num
    · rw [ite_eq_left ⟨h0, h1⟩]

lemma quarticBumpDeriv_lipschitz (x y : ℝ) :
    |quarticBumpDeriv x - quarticBumpDeriv y| ≤ 32 * |x - y| := by
  let clamp : ℝ → ℝ := fun t => max 0 (min 1 t)
  have hclamp_mem : ∀ t, 0 ≤ clamp t ∧ clamp t ≤ 1 := fun t =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hclamp_eq : ∀ t, quarticBumpDeriv t = quarticBumpDeriv (clamp t) := fun t => by
    unfold quarticBumpDeriv clamp
    by_cases h0 : t ≤ 0
    · have h1 : min 1 t = t := min_eq_right (by linarith)
      have h2 : max 0 t = 0 := max_eq_left h0
      rw [h1, h2]; simp [not_lt.mpr h0]
    · push Not at h0
      by_cases h1 : 1 ≤ t
      · have hm1 : min 1 t = 1 := min_eq_left h1
        have hm2 : max 0 (1 : ℝ) = 1 := max_eq_right zero_le_one
        rw [hm1, hm2]; simp [not_lt.mpr h1]
      · push Not at h1
        rw [min_eq_right h1.le, max_eq_right h0.le]
  have hclamp_lip : |clamp x - clamp y| ≤ |x - y| := by
    have hsub : ∀ u v : ℝ, clamp u - clamp v ≤ |u - v| := fun u v => by
      have huv : u ≤ v + |u - v| := by linarith [le_abs_self (u - v)]
      have h1 : min (1 : ℝ) u ≤ min (1 : ℝ) v + |u - v| := by
        rcases le_total (1 : ℝ) v with hv | hv
        · rw [min_eq_left hv]
          exact (min_le_left (1 : ℝ) u).trans (by linarith [abs_nonneg (u - v)])
        · rw [min_eq_right hv]
          exact (min_le_right (1 : ℝ) u).trans huv
      have h2 : clamp u ≤ clamp v + |u - v| := by
        dsimp [clamp]
        refine max_le ?_ ?_
        · exact (le_max_left (0 : ℝ) (min (1 : ℝ) v)).trans (by linarith [abs_nonneg (u - v)])
        · exact h1.trans (add_le_add (le_max_right (0 : ℝ) (min (1 : ℝ) v)) le_rfl)
      linarith
    exact abs_le.mpr ⟨by linarith [hsub y x, abs_sub_comm x y], hsub x y⟩
  rw [hclamp_eq x, hclamp_eq y]
  set a := clamp x
  set b := clamp y
  obtain ⟨ha0, ha1⟩ := hclamp_mem x
  obtain ⟨hb0, hb1⟩ := hclamp_mem y
  rw [quarticBumpDeriv_eq_poly_on_Icc ha0 ha1, quarticBumpDeriv_eq_poly_on_Icc hb0 hb1]
  have hfac : 16 * (2 * a - 6 * a ^ 2 + 4 * a ^ 3) - 16 * (2 * b - 6 * b ^ 2 + 4 * b ^ 3) =
      (a - b) * (16 * (2 - 6 * (a + b) + 4 * (a ^ 2 + a * b + b ^ 2))) := by ring
  rw [hfac, abs_mul]
  have hmid : |16 * (2 - 6 * (a + b) + 4 * (a ^ 2 + a * b + b ^ 2))| ≤ 32 := by
    rw [abs_le]
    have hhi : 4 * (a ^ 2 + a * b + b ^ 2) - 6 * (a + b) ≤ 0 := by
      have : 4 * (a ^ 2 + a * b + b ^ 2) - 6 * (a + b) =
          4 * a * (a - 1) + 4 * b * (b - 1) + 2 * a * (b - 1) + 2 * b * (a - 1) := by ring
      nlinarith
    have hlo : 0 ≤ 4 * (a ^ 2 + a * b + b ^ 2) - 6 * (a + b) + 4 := by
      have : 4 * (a ^ 2 + a * b + b ^ 2) - 6 * (a + b) + 4 =
          3 * (a + b - 1) ^ 2 + (a - b) ^ 2 + 1 := by ring
      nlinarith [sq_nonneg (a + b - 1), sq_nonneg (a - b)]
    constructor <;> linarith
  calc |a - b| * |16 * (2 - 6 * (a + b) + 4 * (a ^ 2 + a * b + b ^ 2))|
      ≤ |a - b| * 32 := mul_le_mul_of_nonneg_left hmid (abs_nonneg _)
    _ = 32 * |a - b| := mul_comm _ _
    _ ≤ 32 * |x - y| := mul_le_mul_of_nonneg_left hclamp_lip (by norm_num)

/-- `quarticBump` is everywhere differentiable on `ℝ` with derivative `quarticBumpDeriv`. -/
lemma hasDerivAt_quarticBump (x : ℝ) : HasDerivAt quarticBump (quarticBumpDeriv x) x := by
  by_cases hx_lt0 : x < 0
  · have hev : quarticBump =ᶠ[nhds x] fun _ => (0 : ℝ) := by
      filter_upwards [eventually_lt_nhds hx_lt0] with y hy
      unfold quarticBump; simp [not_lt.mpr hy.le]
    have h0 : quarticBumpDeriv x = 0 := by unfold quarticBumpDeriv; simp [not_lt.mpr hx_lt0.le]
    rw [h0]
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
  · by_cases hx_gt1 : 1 < x
    · have hev : quarticBump =ᶠ[nhds x] fun _ => (0 : ℝ) := by
        filter_upwards [eventually_gt_nhds hx_gt1] with y hy
        unfold quarticBump; simp [not_lt.mpr hy.le]
      have h0 : quarticBumpDeriv x = 0 := by unfold quarticBumpDeriv; simp [not_lt.mpr hx_gt1.le]
      rw [h0]
      exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
    · push Not at hx_lt0 hx_gt1
      rcases eq_or_lt_of_le hx_lt0 with rfl | h0
      · -- `x = 0`: `|quarticBump y| ≤ 16 * y^2`.
        have h0' : quarticBumpDeriv 0 = 0 := by simp [quarticBumpDeriv]
        rw [h0', hasDerivAt_iff_isLittleO]
        rw [Asymptotics.isLittleO_iff]
        intro c hc
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (show (0 : ℝ) < min 1 (c / 16) by positivity)] with y hy
        rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy
        have hwb0 : quarticBump 0 = 0 := by simp [quarticBump]
        simp only [hwb0, smul_zero, sub_zero, Real.norm_eq_abs]
        have hbound : |quarticBump y| ≤ 16 * y ^ 2 := by
          unfold quarticBump
          split_ifs with h
          · rw [abs_of_nonneg (by positivity)]
            have h1y : (1 - y) ^ 2 ≤ 1 := by nlinarith [h.1, h.2]
            nlinarith [sq_nonneg y]
          · simp; positivity
        have hyc : 16 * |y| ≤ c := by
          have : |y| < c / 16 := lt_of_lt_of_le hy (min_le_right _ _)
          linarith
        calc |quarticBump y| ≤ 16 * y ^ 2 := hbound
          _ = (16 * |y|) * |y| := by rw [← sq_abs y]; ring
          _ ≤ c * |y| := mul_le_mul_of_nonneg_right hyc (abs_nonneg y)
      · rcases eq_or_lt_of_le hx_gt1 with rfl | h1
        · -- `x = 1`: `|quarticBump y| ≤ 16 * (y - 1)^2`.
          have h1' : quarticBumpDeriv 1 = 0 := by simp [quarticBumpDeriv]
          rw [h1', hasDerivAt_iff_isLittleO]
          rw [Asymptotics.isLittleO_iff]
          intro c hc
          filter_upwards [Metric.ball_mem_nhds (1 : ℝ) (show (0 : ℝ) < min 1 (c / 16) by positivity)] with y hy
          rw [Metric.mem_ball, Real.dist_eq] at hy
          have hwb1 : quarticBump 1 = 0 := by simp [quarticBump]
          simp only [hwb1, smul_zero, sub_zero, Real.norm_eq_abs]
          have hbound : |quarticBump y| ≤ 16 * (y - 1) ^ 2 := by
            unfold quarticBump
            split_ifs with h
            · rw [abs_of_nonneg (by positivity)]
              have hy2 : y ^ 2 ≤ 1 := by nlinarith [h.1, h.2]
              have hsq : (1 - y) ^ 2 = (y - 1) ^ 2 := by ring
              rw [hsq]; nlinarith [sq_nonneg (y - 1)]
            · simp; positivity
          have hyc : 16 * |y - 1| ≤ c := by
            have : |y - 1| < c / 16 := lt_of_lt_of_le hy (min_le_right _ _)
            linarith
          calc |quarticBump y| ≤ 16 * (y - 1) ^ 2 := hbound
            _ = (16 * |y - 1|) * |y - 1| := by rw [← sq_abs (y - 1)]; ring
            _ ≤ c * |y - 1| := mul_le_mul_of_nonneg_right hyc (abs_nonneg _)
        · -- `0 < x < 1`: locally agrees with polynomial `16 * x^2 * (1 - x)^2`.
          have hev : quarticBump =ᶠ[nhds x] fun y => 16 * y ^ 2 * (1 - y) ^ 2 := by
            filter_upwards [eventually_gt_nhds h0, eventually_lt_nhds h1] with y hy0 hy1
            unfold quarticBump; rw [ite_eq_left ⟨hy0, hy1⟩]
          have hpoly : HasDerivAt (fun y : ℝ => 16 * y ^ 2 * (1 - y) ^ 2)
              (16 * (2 * x - 6 * x ^ 2 + 4 * x ^ 3)) x := by
            have hd1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
              simpa using hasDerivAt_pow 2 x
            have hd2 : HasDerivAt (fun y : ℝ => (1 - y) ^ 2) (2 * (1 - x) * (-1)) x := by
              have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
                simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
              have hc := HasDerivAt.comp x (hasDerivAt_pow 2 (1 - x)) hsub
              simpa [Function.comp_def, pow_one] using hc
            have hmul := (hd1.const_mul 16).mul hd2
            convert hmul using 1; ring
          rw [quarticBumpDeriv_eq_poly_on_Icc h0.le h1.le]
          exact hpoly.congr_of_eventuallyEq hev

/-- Second-difference bound for `quarticBump`:
`|w(x + h) - 2 * w(x) + w(x - h)| ≤ 64 * h²` for all `x ∈ ℝ` and `h ≥ 0`. -/
lemma quarticBump_second_diff_le (x : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    |quarticBump (x + h) - 2 * quarticBump x + quarticBump (x - h)| ≤ 64 * h ^ 2 := by
  rcases eq_or_lt_of_le hh with rfl | hh_pos
  · simp; ring
  · have hcont : Continuous quarticBump :=
      continuous_iff_continuousAt.mpr fun t => (hasDerivAt_quarticBump t).continuousAt
    obtain ⟨ξ₁, hξ₁_mem, hξ₁_eq⟩ := exists_hasDerivAt_eq_slope quarticBump quarticBumpDeriv
      (by linarith : x < x + h) hcont.continuousOn (fun t _ => hasDerivAt_quarticBump t)
    obtain ⟨ξ₂, hξ₂_mem, hξ₂_eq⟩ := exists_hasDerivAt_eq_slope quarticBump quarticBumpDeriv
      (by linarith : x - h < x) hcont.continuousOn (fun t _ => hasDerivAt_quarticBump t)
    have hdiff1 : quarticBump (x + h) - quarticBump x = quarticBumpDeriv ξ₁ * h := by
      have hden : x + h - x = h := by ring
      rw [hden, eq_div_iff hh_pos.ne'] at hξ₁_eq; exact hξ₁_eq.symm
    have hdiff2 : quarticBump x - quarticBump (x - h) = quarticBumpDeriv ξ₂ * h := by
      have hden : x - (x - h) = h := by ring
      rw [hden, eq_div_iff hh_pos.ne'] at hξ₂_eq; exact hξ₂_eq.symm
    have hrew : quarticBump (x + h) - 2 * quarticBump x + quarticBump (x - h) =
        (quarticBumpDeriv ξ₁ - quarticBumpDeriv ξ₂) * h := by linarith
    have hξ_dist : |ξ₁ - ξ₂| ≤ 2 * h := by
      rw [abs_le]
      exact ⟨by linarith [hξ₁_mem.1, hξ₂_mem.2], by linarith [hξ₁_mem.2, hξ₂_mem.1]⟩
    rw [hrew, abs_mul, abs_of_pos hh_pos]
    calc |quarticBumpDeriv ξ₁ - quarticBumpDeriv ξ₂| * h
        ≤ (32 * |ξ₁ - ξ₂|) * h := mul_le_mul_of_nonneg_right (quarticBumpDeriv_lipschitz ξ₁ ξ₂) hh_pos.le
      _ ≤ (32 * (2 * h)) * h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hξ_dist (by norm_num)) hh_pos.le
      _ = 64 * h ^ 2 := by ring

/-- **Second-difference decay `(11a)` for `smoothedKernel`:**
For `0 < r ≤ Y`, `b < r`, and `|β| ≤ 1 / 2`:
`‖smoothedKernel r b Y β‖ ≤ 64 * (Y / r) / (1 + (Y / r) * |β|)²`. -/
theorem smoothedKernel_second_diff_decay {r b Y : ℕ} (hr : 0 < r) (hrY : r ≤ Y) (hb : b < r)
    {β : ℝ} (hβ : |β| ≤ 1 / 2) :
    ‖smoothedKernel r b Y β‖ ≤
      64 * ((Y : ℝ) / (r : ℝ)) / (1 + ((Y : ℝ) / (r : ℝ)) * |β|) ^ 2 := by
  have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hY_pos : (0 : ℝ) < Y := Nat.cast_pos.mpr (lt_of_lt_of_le hr hrY)
  set H : ℝ := (Y : ℝ) / (r : ℝ)
  have hH_ge1 : 1 ≤ H := (one_le_div hr_pos).2 (Nat.cast_le.mpr hrY)
  have hH_pos : 0 < H := by linarith
  -- Case 1: `H * |β| ≤ 1` (trivial bound `‖V_b(β)‖ ≤ 2 * H`).
  by_cases hsmall : H * |β| ≤ 1
  · have htriv : ‖smoothedKernel r b Y β‖ ≤ 2 * H := by
      linarith [smoothedKernel_bound_triv r b Y β]
    rw [le_div_iff₀ (sq_pos_of_pos (by positivity))]
    have h1 : (1 + H * |β|) ^ 2 ≤ 4 := by nlinarith [show (0 : ℝ) ≤ H * |β| by positivity]
    calc ‖smoothedKernel r b Y β‖ * (1 + H * |β|) ^ 2
        ≤ (2 * H) * 4 := mul_le_mul htriv h1 (sq_nonneg _) (by positivity)
      _ ≤ 64 * H := by linarith
  · -- Case 2: `1 < H * |β|` (double summation by parts!).
    push Not at hsmall
    have hβ_pos : 0 < |β| := by nlinarith
    set M : ℕ := Y / r
    let c : ℤ → ℝ := fun j => quarticBump (((r : ℝ) * (j : ℝ) + (b : ℝ)) / (Y : ℝ))
    have hc_neg : ∀ j : ℤ, j ≤ -1 → c j = 0 := fun j hj => by
      dsimp [c]; unfold quarticBump
      have hle : (r : ℝ) * (j : ℝ) + (b : ℝ) ≤ 0 := by
        have hj1 : (j : ℝ) ≤ -1 := by exact_mod_cast hj
        have hbR : (b : ℝ) < (r : ℝ) := Nat.cast_lt.mpr hb
        nlinarith
      have hdiv : ((r : ℝ) * (j : ℝ) + (b : ℝ)) / (Y : ℝ) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hle hY_pos.le
      simp [not_lt.mpr hdiv]
    have hc_hi : ∀ j : ℤ, (M : ℤ) + 1 ≤ j → c j = 0 := fun j hj => by
      dsimp [c]; unfold quarticBump
      have hge : (Y : ℝ) ≤ (r : ℝ) * (j : ℝ) + (b : ℝ) := by
        have hjM : ((M + 1 : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : (M + 1 : ℤ) ≤ j)
        have hY_lt : Y < r * (M + 1) := by
          have hd := Nat.div_add_mod Y r; have hm := Nat.mod_lt Y hr; dsimp [M]; nlinarith
        have hYR : (Y : ℝ) < (r : ℝ) * ((M + 1 : ℕ) : ℝ) := by exact_mod_cast hY_lt
        nlinarith [Nat.cast_nonneg (α := ℝ) b]
      have hdiv : 1 ≤ ((r : ℝ) * (j : ℝ) + (b : ℝ)) / (Y : ℝ) := (one_le_div hY_pos).2 hge
      simp [not_lt.mpr hdiv]
    -- Double difference identity: `(e β - 1)^2 * smoothedKernel = ∑_{k=0}^{M+2} (Δ² c_k) * e(β*k)`.
    have hV_eq : smoothedKernel r b Y β =
        ∑ k ∈ Finset.range (M + 1), (c (k : ℤ) : ℂ) * e (β * (k : ℝ)) := by
      unfold smoothedKernel
      refine Finset.sum_congr rfl fun k _ => by dsimp [c]; push_cast; rfl
    have hsbp2 : (e β - 1) ^ 2 * smoothedKernel r b Y β =
        ∑ k ∈ Finset.range (M + 3),
          ((c ((k : ℤ) - 2) - 2 * c ((k : ℤ) - 1) + c (k : ℤ) : ℝ) : ℂ) * e (β * (k : ℝ)) := by
      have hexp : (e β - 1) ^ 2 = e (2 * β) - 2 * e β + 1 := by
        have h2 : (e β) ^ 2 = e (2 * β) := by rw [← e_nat_mul]; push_cast; rfl
        calc (e β - 1) ^ 2 = (e β) ^ 2 - 2 * e β + 1 := by ring
          _ = e (2 * β) - 2 * e β + 1 := by rw [h2]
      rw [hexp, hV_eq, add_mul, sub_mul, one_mul]
      have hshift2 : e (2 * β) * ∑ j ∈ Finset.range (M + 1), (c (j : ℤ) : ℂ) * e (β * (j : ℝ)) =
          ∑ k ∈ Finset.range (M + 3), (c ((k : ℤ) - 2) : ℂ) * e (β * (k : ℝ)) := by
        rw [Finset.mul_sum]
        have hdrop : ∑ k ∈ Finset.range (M + 3), (c ((k : ℤ) - 2) : ℂ) * e (β * (k : ℝ)) =
            ∑ k ∈ Finset.Icc 2 (M + 2), (c ((k : ℤ) - 2) : ℂ) * e (β * (k : ℝ)) := by
          symm
          refine Finset.sum_subset (fun k hk => Finset.mem_range.mpr (by have := Finset.mem_Icc.mp hk; omega))
            fun k hk hnot => ?_
          have hklt : k < 2 := by
            have := Finset.mem_range.mp hk
            by_contra hge; exact hnot (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
          rw [hc_neg ((k : ℤ) - 2) (by omega)]; simp
        rw [hdrop]
        refine Finset.sum_bij (fun j _ => j + 2) ?_ ?_ ?_ ?_
        · intro j hj; exact Finset.mem_Icc.mpr ⟨by omega, by have := Finset.mem_range.mp hj; omega⟩
        · intro j₁ _ j₂ _ hEq; omega
        · intro k hk; have := Finset.mem_Icc.mp hk; exact ⟨k - 2, Finset.mem_range.mpr (by omega), by omega⟩
        · intro j _
          have he : e (2 * β) * e (β * (j : ℝ)) = e (β * ((j + 2 : ℕ) : ℝ)) := by
            rw [← e_add]; congr 1; push_cast; ring
          have hj2 : ((j + 2 : ℕ) : ℤ) - 2 = (j : ℤ) := by omega
          rw [hj2, ← he]; ring
      have hshift1 : (2 * e β) * ∑ j ∈ Finset.range (M + 1), (c (j : ℤ) : ℂ) * e (β * (j : ℝ)) =
          ∑ k ∈ Finset.range (M + 3), (2 * c ((k : ℤ) - 1) : ℂ) * e (β * (k : ℝ)) := by
        rw [Finset.mul_sum]
        have hdrop : ∑ k ∈ Finset.range (M + 3), (2 * c ((k : ℤ) - 1) : ℂ) * e (β * (k : ℝ)) =
            ∑ k ∈ Finset.Icc 1 (M + 1), (2 * c ((k : ℤ) - 1) : ℂ) * e (β * (k : ℝ)) := by
          symm
          refine Finset.sum_subset (fun k hk => Finset.mem_range.mpr (by have := Finset.mem_Icc.mp hk; omega))
            fun k hk hnot => ?_
          have hlt := Finset.mem_range.mp hk
          by_cases hk0 : k = 0
          · subst hk0; simp only [Nat.cast_zero, zero_sub]; rw [hc_neg (-1) le_rfl]; simp
          · have hkhi : M + 2 ≤ k := by
              by_contra hlt2; exact hnot (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
            rw [hc_hi ((k : ℤ) - 1) (by omega)]; simp
        rw [hdrop]
        refine Finset.sum_bij (fun j _ => j + 1) ?_ ?_ ?_ ?_
        · intro j hj; exact Finset.mem_Icc.mpr ⟨by omega, by have := Finset.mem_range.mp hj; omega⟩
        · intro j₁ _ j₂ _ hEq; omega
        · intro k hk; have := Finset.mem_Icc.mp hk; exact ⟨k - 1, Finset.mem_range.mpr (by omega), by omega⟩
        · intro j _
          have he : e β * e (β * (j : ℝ)) = e (β * ((j + 1 : ℕ) : ℝ)) := by
            rw [← e_add]; congr 1; push_cast; ring
          have hj1 : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
          rw [hj1, ← he]; ring
      have hshift0 : ∑ j ∈ Finset.range (M + 1), (c (j : ℤ) : ℂ) * e (β * (j : ℝ)) =
          ∑ k ∈ Finset.range (M + 3), (c (k : ℤ) : ℂ) * e (β * (k : ℝ)) := by
        refine Finset.sum_subset (Finset.range_mono (by omega)) fun k hk hnot => ?_
        have hge : M + 1 ≤ k := by simpa [Finset.mem_range] using hnot
        rw [hc_hi (k : ℤ) (by omega)]; simp
      rw [hshift2, hshift1, hshift0, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => by push_cast; ring
    have hnorm_lhs : 16 * β ^ 2 * ‖smoothedKernel r b Y β‖ ≤
        ‖(e β - 1) ^ 2 * smoothedKernel r b Y β‖ := by
      rw [norm_mul, norm_pow]
      have hge := four_mul_abs_le_norm_e_sub_one hβ
      have hsq : 16 * β ^ 2 ≤ ‖e β - 1‖ ^ 2 := by
        have h1 := pow_le_pow_left₀ (by positivity) hge 2
        rw [mul_pow, sq_abs] at h1; linarith
      exact mul_le_mul_of_nonneg_right hsq (norm_nonneg _)
    have hnorm_rhs : ‖∑ k ∈ Finset.range (M + 3),
          ((c ((k : ℤ) - 2) - 2 * c ((k : ℤ) - 1) + c (k : ℤ) : ℝ) : ℂ) * e (β * (k : ℝ))‖ ≤
        256 / H := by
      have hterm : ∀ k ∈ Finset.range (M + 3),
          ‖((c ((k : ℤ) - 2) - 2 * c ((k : ℤ) - 1) + c (k : ℤ) : ℝ) : ℂ) * e (β * (k : ℝ))‖ ≤
            64 / H ^ 2 := by
        intro k _
        rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs]
        set x0 : ℝ := ((r : ℝ) * (((k : ℤ) - 1 : ℤ) : ℝ) + (b : ℝ)) / (Y : ℝ)
        set step : ℝ := (r : ℝ) / (Y : ℝ)
        have hstep_eq : step = 1 / H := by dsimp [step, H]; field_simp [hr_pos.ne', hY_pos.ne']
        have h1 : c (k : ℤ) = quarticBump (x0 + step) := by
          dsimp [c, x0, step]; congr 1; push_cast; ring
        have h2 : c ((k : ℤ) - 1) = quarticBump x0 := rfl
        have h3 : c ((k : ℤ) - 2) = quarticBump (x0 - step) := by
          dsimp [c, x0, step]; congr 1; push_cast; ring
        rw [h1, h2, h3]
        have hcomm : quarticBump (x0 - step) - 2 * quarticBump x0 + quarticBump (x0 + step) =
            quarticBump (x0 + step) - 2 * quarticBump x0 + quarticBump (x0 - step) := by ring
        rw [hcomm]
        have hbd := quarticBump_second_diff_le x0 (by positivity : 0 ≤ step)
        have hstep_sq : 64 * step ^ 2 = 64 / H ^ 2 := by rw [hstep_eq]; ring
        linarith
      have hM3 : ((M + 3 : ℕ) : ℝ) ≤ 4 * H := by
        have hdiv : ((M : ℕ) : ℝ) ≤ H := by
          dsimp [M, H]; rw [le_div_iff₀ hr_pos]
          exact_mod_cast (by simpa [mul_comm] using Nat.mul_div_le Y r)
        push_cast; linarith
      calc ‖∑ k ∈ Finset.range (M + 3),
              ((c ((k : ℤ) - 2) - 2 * c ((k : ℤ) - 1) + c (k : ℤ) : ℝ) : ℂ) * e (β * (k : ℝ))‖
          ≤ ∑ _k ∈ Finset.range (M + 3), (64 / H ^ 2) := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
        _ = ((M + 3 : ℕ) : ℝ) * (64 / H ^ 2) := by simp [nsmul_eq_mul]
        _ ≤ (4 * H) * (64 / H ^ 2) := mul_le_mul_of_nonneg_right hM3 (by positivity)
        _ = 256 / H := by field_simp [hH_pos.ne']; ring
    have hV_bd : ‖smoothedKernel r b Y β‖ ≤ 16 / (H * β ^ 2) := by
      have hβ2_pos : 0 < β ^ 2 := sq_pos_of_ne_zero (abs_pos.mp hβ_pos)
      rw [le_div_iff₀ (mul_pos hH_pos hβ2_pos)]
      have hcomb : 16 * β ^ 2 * ‖smoothedKernel r b Y β‖ ≤ 256 / H := by
        rw [← hsbp2] at hnorm_rhs; exact hnorm_lhs.trans hnorm_rhs
      have hmul := mul_le_mul_of_nonneg_left hcomb hH_pos.le
      have hR : H * (256 / H) = 256 := mul_div_cancel₀ _ hH_pos.ne'
      linarith
    rw [le_div_iff₀ (sq_pos_of_pos (by positivity))]
    have hden : (1 + H * |β|) ^ 2 ≤ 4 * H ^ 2 * β ^ 2 := by
      have h1 : 1 + H * |β| ≤ 2 * (H * |β|) := by linarith
      have hsq := pow_le_pow_left₀ (by positivity) h1 2
      rw [mul_pow, mul_pow, sq_abs] at hsq; linarith
    calc ‖smoothedKernel r b Y β‖ * (1 + H * |β|) ^ 2
        ≤ (16 / (H * β ^ 2)) * (4 * H ^ 2 * β ^ 2) :=
          mul_le_mul hV_bd hden (sq_nonneg _) (by positivity)
      _ = 64 * H := by
          have hβ_ne : β ≠ 0 := abs_pos.mp hβ_pos
          field_simp [hH_pos.ne', hβ_ne]; ring

/-- **Weighted kernel L² integral `(11b)`:**
For `0 < r ≤ Y` and `b < r`:
`∫ β in (-1/2)..(1/2), (1 + (Y / r) * |β|) * ‖smoothedKernel r b Y β‖² ≤ 4096 * (Y / r)`. -/
theorem integral_one_add_mul_norm_smoothedKernel_sq_le {r b Y : ℕ} (hr : 0 < r) (hrY : r ≤ Y)
    (hb : b < r) :
    (∫ β in (-(1 / 2) : ℝ)..(1 / 2),
        (1 + ((Y : ℝ) / (r : ℝ)) * |β|) * ‖smoothedKernel r b Y β‖ ^ 2) ≤
      4096 * ((Y : ℝ) / (r : ℝ)) := by
  have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hY_pos : (0 : ℝ) < Y := Nat.cast_pos.mpr (lt_of_lt_of_le hr hrY)
  set H : ℝ := (Y : ℝ) / (r : ℝ)
  have hH_pos : 0 < H := div_pos hY_pos hr_pos
  let f : ℝ → ℝ := fun β => (1 + H * |β|) * ‖smoothedKernel r b Y β‖ ^ 2
  let g : ℝ → ℝ := fun β => 4096 * H ^ 2 / (1 + H * |β|) ^ 3
  have hf_cont : Continuous f :=
    (continuous_const.add (continuous_const.mul continuous_abs)).mul
      ((continuous_norm.comp (continuous_smoothedKernel r b Y)).pow 2)
  have hg_cont : Continuous g := by
    refine continuous_const.div ((continuous_const.add (continuous_const.mul continuous_abs)).pow 3) ?_
    intro β
    have hpos : 0 < 1 + H * |β| := by nlinarith [hH_pos, abs_nonneg β]
    exact pow_ne_zero 3 hpos.ne'
  have hmono : (∫ β in (-(1 / 2) : ℝ)..(1 / 2), f β) ≤ ∫ β in (-(1 / 2) : ℝ)..(1 / 2), g β := by
    apply intervalIntegral.integral_mono_on (by norm_num) (hf_cont.intervalIntegrable _ _)
      (hg_cont.intervalIntegrable _ _)
    intro β hβ
    have hβ_half : |β| ≤ 1 / 2 := abs_le.mpr hβ
    have hdec := smoothedKernel_second_diff_decay hr hrY hb hβ_half
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hdec 2
    have hden_pos : 0 < 1 + H * |β| := by positivity
    calc (1 + H * |β|) * ‖smoothedKernel r b Y β‖ ^ 2
        ≤ (1 + H * |β|) * (64 * H / (1 + H * |β|) ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hden_pos.le
      _ = 4096 * H ^ 2 / (1 + H * |β|) ^ 3 := by
          field_simp [hden_pos.ne']; ring
  -- Split `∫_{-1/2}^{1/2} g` at `0` and integrate explicitly via FTC!
  have hsp := (intervalIntegral.integral_add_adjacent_intervals
    (hg_cont.intervalIntegrable (μ := MeasureTheory.volume) (-(1 / 2)) 0)
    (hg_cont.intervalIntegrable (μ := MeasureTheory.volume) 0 (1 / 2))).symm
  have hright : (∫ β in (0 : ℝ)..(1 / 2), g β) ≤ 2048 * H := by
    have heq : (∫ β in (0 : ℝ)..(1 / 2), g β) =
        ∫ β in (0 : ℝ)..(1 / 2), 4096 * H ^ 2 / (1 + H * β) ^ 3 := by
      refine intervalIntegral.integral_congr fun β hβ => ?_
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hβ
      simp only [g, abs_of_nonneg hβ.1]
    rw [heq]
    have hderiv : ∀ β ∈ Set.uIcc (0 : ℝ) (1 / 2),
        HasDerivAt (fun x : ℝ => -(2048 * H) / (1 + H * x) ^ 2)
          (4096 * H ^ 2 / (1 + H * β) ^ 3) β := by
      intro β hβ
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hβ
      have hden_pos : 0 < 1 + H * β := by nlinarith [hβ.1]
      have hd1 : HasDerivAt (fun x : ℝ => 1 + H * x) H β := by
        have h := ((hasDerivAt_id β).const_mul H).const_add (1 : ℝ)
        rwa [mul_one] at h
      have hd2 : HasDerivAt (fun x : ℝ => (1 + H * x) ^ 2) (2 * (1 + H * β) * H) β := by
        convert hd1.pow 2 using 1; ring
      have hd3 := (hasDerivAt_const β (-(2048 * H))).div hd2 (pow_ne_zero 2 hden_pos.ne')
      convert hd3 using 1
      field_simp [hden_pos.ne']; ring
    have hcont_r : ContinuousOn (fun β : ℝ => 4096 * H ^ 2 / (1 + H * β) ^ 3) (Set.uIcc 0 (1 / 2)) := by
      refine continuousOn_const.div ((continuousOn_const.add (continuousOn_const.mul continuousOn_id)).pow 3) ?_
      intro β hβ
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hβ
      have hpos : 0 < 1 + H * β := by nlinarith [hβ.1, hH_pos]
      exact pow_ne_zero 3 hpos.ne'
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont_r.intervalIntegrable]
    have hterm_nn : 0 ≤ 2048 * H / (1 + H * (1 / 2)) ^ 2 := by positivity
    simp only [mul_zero, add_zero, one_pow, div_one, neg_div]; linarith
  have hleft : (∫ β in (-(1 / 2) : ℝ)..0, g β) ≤ 2048 * H := by
    have heq : (∫ β in (-(1 / 2) : ℝ)..0, g β) =
        ∫ β in (-(1 / 2) : ℝ)..0, 4096 * H ^ 2 / (1 - H * β) ^ 3 := by
      refine intervalIntegral.integral_congr fun β hβ => ?_
      rw [Set.uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 0)] at hβ
      simp only [g, abs_of_nonpos hβ.2]; ring_nf
    rw [heq]
    have hderiv : ∀ β ∈ Set.uIcc (-(1 / 2) : ℝ) 0,
        HasDerivAt (fun x : ℝ => (2048 * H) / (1 - H * x) ^ 2)
          (4096 * H ^ 2 / (1 - H * β) ^ 3) β := by
      intro β hβ
      rw [Set.uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 0)] at hβ
      have hden_pos : 0 < 1 - H * β := by nlinarith [hβ.2]
      have hd1 : HasDerivAt (fun x : ℝ => 1 - H * x) (-H) β := by
        have h := ((hasDerivAt_id β).const_mul (-H)).const_add (1 : ℝ)
        rw [mul_one] at h
        convert h using 1; ext x; dsimp only [id]; ring
      have hd2 : HasDerivAt (fun x : ℝ => (1 - H * x) ^ 2) (2 * (1 - H * β) * (-H)) β := by
        convert hd1.pow 2 using 1; ring
      have hd3 := (hasDerivAt_const β (2048 * H)).div hd2 (pow_ne_zero 2 hden_pos.ne')
      convert hd3 using 1
      field_simp [hden_pos.ne']; ring
    have hcont_l : ContinuousOn (fun β : ℝ => 4096 * H ^ 2 / (1 - H * β) ^ 3) (Set.uIcc (-(1 / 2)) 0) := by
      refine continuousOn_const.div ((continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).pow 3) ?_
      intro β hβ
      rw [Set.uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 0)] at hβ
      have hpos : 0 < 1 - H * β := by nlinarith [hβ.2, hH_pos]
      exact pow_ne_zero 3 hpos.ne'
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont_l.intervalIntegrable]
    have hterm_nn : 0 ≤ 2048 * H / (1 - H * -(1 / 2)) ^ 2 := by positivity
    simp only [mul_zero, sub_zero, one_pow, div_one]; linarith
  linarith [hmono, hsp, hleft, hright]

end SecondDifferenceKernelDecay

end FareyGoldbach
