import FareyGoldbach.LocalLogDerivative
import FareyGoldbach.QuarticMellin
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Module A3: Smoothed Explicit Formula via Right-Half-Plane Contour Shift

Combining Module A1 (`LocalLogDerivative`) and Module A2 (`QuarticMellin`), this module proves
under `DirichletGRH`, for every primitive Dirichlet character `χ mod d`, every `Y ≥ 2`, and every
`t : ℝ`:

1. `rectIntegral_eq_sum_simple_poles`: self-contained rectangular residue theorem for finitely
   many simple poles, proved directly from Mathlib's
   `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` and an explicit 1-pole evaluation.
2. `smoothedPrimeSum_eq_verticalIntegral`: Mellin-inversion representation of the smoothed twisted
   von Mangoldt sum on the vertical line `Re(s) = 2`.
3. `summable_norm_zeroTerm` & `integrable_quarter_line`: absolute summability of the critical-strip
   zero sum and integrability of the `Re(s) = 1/4` contour integral.
4. `primitive_smoothed_explicit_formula`:
   `∑_{n=1}^Y Λ(n) χ(n) w(n/Y) e(t n) = 1_{χ=1} f̃(1) - ∑'_ρ m_ρ f̃(ρ) + (1/(2π)) ∫_ℝ f̃(1/4+iu) (-L'/L)(1/4+iu, χ) du`.
-/

open Real Complex Set Filter MeasureTheory Topology Metric
open scoped BigOperators Classical Interval

namespace FareyGoldbach

section RectangleResidues

/-- Counterclockwise boundary integral of `f : ℂ → ℂ` around the rectangle `[x₁, x₂] × [y₁, y₂]`. -/
noncomputable def rectIntegral (f : ℂ → ℂ) (x₁ x₂ y₁ y₂ : ℝ) : ℂ :=
  (∫ x in x₁..x₂, f ((x : ℂ) + (y₁ : ℂ) * Complex.I)) -
  (∫ x in x₁..x₂, f ((x : ℂ) + (y₂ : ℂ) * Complex.I)) +
  Complex.I * (∫ y in y₁..y₂, f ((x₂ : ℂ) + (y : ℂ) * Complex.I)) -
  Complex.I * (∫ y in y₁..y₂, f ((x₁ : ℂ) + (y : ℂ) * Complex.I))

lemma rectIntegral_eq_zero_of_differentiableOn {f : ℂ → ℂ} {x₁ x₂ y₁ y₂ : ℝ}
    (hf : DifferentiableOn ℂ f ([[x₁, x₂]] ×ℂ [[y₁, y₂]])) :
    rectIntegral f x₁ x₂ y₁ y₂ = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((x₁ : ℂ) + (y₁ : ℂ) * Complex.I) ((x₂ : ℂ) + (y₂ : ℂ) * Complex.I) (by simpa using hf)
  simpa [rectIntegral, smul_eq_mul] using h

/-- Horizontal antiderivative of `u ↦ (u + b * I)⁻¹` for `b ≠ 0`. -/
private lemma hasDerivAt_horiz_inv {b : ℝ} (hb : b ≠ 0) (u : ℝ) :
    HasDerivAt
      (fun x : ℝ => (((1 / 2 : ℝ) * Real.log (x ^ 2 + b ^ 2) : ℝ) : ℂ) -
        Complex.I * ((Real.arctan (x / b) : ℝ) : ℂ))
      (((u : ℂ) + (b : ℂ) * Complex.I)⁻¹) u := by
  have hden_pos : 0 < u ^ 2 + b ^ 2 := by positivity
  have h1 : HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * Real.log (x ^ 2 + b ^ 2))
      (u / (u ^ 2 + b ^ 2)) u := by
    have hsq : HasDerivAt (fun x : ℝ => x ^ 2 + b ^ 2) (2 * u) u := by
      simpa using ((hasDerivAt_id u).fun_pow 2).add_const (b ^ 2)
    have hlog := (hsq.log hden_pos.ne').const_mul (1 / 2 : ℝ)
    convert hlog using 1
    field_simp [hden_pos.ne']
  have h2 : HasDerivAt (fun x : ℝ => Real.arctan (x / b)) (b / (u ^ 2 + b ^ 2)) u := by
    have hdiv : HasDerivAt (fun x : ℝ => x / b) (1 / b) u := (hasDerivAt_id u).div_const b
    have harc := (Real.hasDerivAt_arctan (u / b)).comp u hdiv
    refine harc.congr_deriv ?_
    have h1 : 1 + (u / b) ^ 2 ≠ 0 := by positivity
    field_simp [hb, hden_pos.ne', h1]
    ring
  have hcomb : HasDerivAt
      (fun x : ℝ => (((1 / 2 : ℝ) * Real.log (x ^ 2 + b ^ 2) : ℝ) : ℂ) -
        Complex.I * ((Real.arctan (x / b) : ℝ) : ℂ))
      (((u / (u ^ 2 + b ^ 2) : ℝ) : ℂ) - Complex.I * ((b / (u ^ 2 + b ^ 2) : ℝ) : ℂ)) u :=
    h1.ofReal_comp.sub (h2.ofReal_comp.const_mul Complex.I)
  refine hcomb.congr_deriv ?_
  have hdenC : ((u : ℂ) ^ 2 + (b : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hden_pos.ne'
  refine eq_inv_of_mul_eq_one_left ?_
  push_cast
  field_simp [hdenC]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Vertical antiderivative of `v ↦ I * (a + v * I)⁻¹` for `a ≠ 0`. -/
private lemma hasDerivAt_vert_inv {a : ℝ} (ha : a ≠ 0) (v : ℝ) :
    HasDerivAt
      (fun y : ℝ => (((1 / 2 : ℝ) * Real.log (a ^ 2 + y ^ 2) : ℝ) : ℂ) +
        Complex.I * ((Real.arctan (y / a) : ℝ) : ℂ))
      (Complex.I * ((a : ℂ) + (v : ℂ) * Complex.I)⁻¹) v := by
  have hden_pos : 0 < a ^ 2 + v ^ 2 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => (1 / 2 : ℝ) * Real.log (a ^ 2 + y ^ 2))
      (v / (a ^ 2 + v ^ 2)) v := by
    have hsq : HasDerivAt (fun y : ℝ => a ^ 2 + y ^ 2) (2 * v) v := by
      simpa using ((hasDerivAt_id v).fun_pow 2).const_add (a ^ 2)
    have hlog := (hsq.log hden_pos.ne').const_mul (1 / 2 : ℝ)
    convert hlog using 1
    field_simp [hden_pos.ne']
  have h2 : HasDerivAt (fun y : ℝ => Real.arctan (y / a)) (a / (a ^ 2 + v ^ 2)) v := by
    have hdiv : HasDerivAt (fun y : ℝ => y / a) (1 / a) v := (hasDerivAt_id v).div_const a
    have harc := (Real.hasDerivAt_arctan (v / a)).comp v hdiv
    refine harc.congr_deriv ?_
    have h1 : 1 + (v / a) ^ 2 ≠ 0 := by positivity
    field_simp [ha, hden_pos.ne', h1]
  have hcomb : HasDerivAt
      (fun y : ℝ => (((1 / 2 : ℝ) * Real.log (a ^ 2 + y ^ 2) : ℝ) : ℂ) +
        Complex.I * ((Real.arctan (y / a) : ℝ) : ℂ))
      (((v / (a ^ 2 + v ^ 2) : ℝ) : ℂ) + Complex.I * ((a / (a ^ 2 + v ^ 2) : ℝ) : ℂ)) v :=
    h1.ofReal_comp.add (h2.ofReal_comp.const_mul Complex.I)
  refine hcomb.congr_deriv ?_
  have hne : ((a : ℂ) + (v : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact ha this
  have hdenC : ((a : ℂ) ^ 2 + (v : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hden_pos.ne'
  rw [eq_comm, mul_comm, inv_mul_eq_iff_eq_mul₀ hne]
  push_cast
  field_simp [hdenC]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Exact 1-pole rectangular integral: `∮_{∂([x₁, x₂] × [y₁, y₂])} (s - p)⁻¹ ds = 2πi`
for any `p` strictly inside the open rectangle. -/
theorem rectIntegral_inv_sub {x₁ x₂ y₁ y₂ : ℝ} {p : ℂ}
    (hx₁ : x₁ < p.re) (hx₂ : p.re < x₂) (hy₁ : y₁ < p.im) (hy₂ : p.im < y₂) :
    rectIntegral (fun s => (s - p)⁻¹) x₁ x₂ y₁ y₂ = 2 * (Real.pi : ℂ) * Complex.I := by
  set a₁ : ℝ := x₁ - p.re
  set a₂ : ℝ := x₂ - p.re
  set b₁ : ℝ := y₁ - p.im
  set b₂ : ℝ := y₂ - p.im
  have ha₁ : a₁ < 0 := sub_neg.mpr hx₁
  have ha₂ : 0 < a₂ := sub_pos.mpr hx₂
  have hb₁ : b₁ < 0 := sub_neg.mpr hy₁
  have hb₂ : 0 < b₂ := sub_pos.mpr hy₂
  have eval_horiz : ∀ b : ℝ, b ≠ 0 →
      (∫ x in x₁..x₂, (((x : ℂ) + ((b + p.im : ℝ) : ℂ) * Complex.I) - p)⁻¹) =
        (((1 / 2 : ℝ) * Real.log (a₂ ^ 2 + b ^ 2) : ℝ) : ℂ) -
        Complex.I * ((Real.arctan (a₂ / b) : ℝ) : ℂ) -
        ((((1 / 2 : ℝ) * Real.log (a₁ ^ 2 + b ^ 2) : ℝ) : ℂ) -
        Complex.I * ((Real.arctan (a₁ / b) : ℝ) : ℂ)) := by
    intro b hb
    have hshift : ∀ x : ℝ,
        (((x : ℂ) + ((b + p.im : ℝ) : ℂ) * Complex.I) - p)⁻¹ =
          (((x - p.re : ℝ) : ℂ) + (b : ℂ) * Complex.I)⁻¹ := by
      intro x
      congr 1
      apply Complex.ext <;> simp
    simp_rw [hshift]
    have hder : ∀ x ∈ uIcc x₁ x₂,
        HasDerivAt (fun t : ℝ => (((1 / 2 : ℝ) * Real.log ((t - p.re) ^ 2 + b ^ 2) : ℝ) : ℂ) -
          Complex.I * ((Real.arctan ((t - p.re) / b) : ℝ) : ℂ))
          ((((x - p.re : ℝ) : ℂ) + (b : ℂ) * Complex.I)⁻¹) x := by
      intro x _
      have hc := (hasDerivAt_horiz_inv hb (x - p.re)).scomp x ((hasDerivAt_id' x).sub_const p.re)
      simpa only [Function.comp_def, one_smul] using hc
    have hcont : Continuous (fun x : ℝ => (((x - p.re : ℝ) : ℂ) + (b : ℂ) * Complex.I)⁻¹) := by
      refine Continuous.inv₀ (by fun_prop) fun x h => ?_
      have := congrArg Complex.im h; simp at this; exact hb this
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hcont.intervalIntegrable _ _)
  have eval_vert : ∀ a : ℝ, a ≠ 0 →
      Complex.I * (∫ y in y₁..y₂, ((((a + p.re : ℝ) : ℂ) + (y : ℂ) * Complex.I) - p)⁻¹) =
        (((1 / 2 : ℝ) * Real.log (a ^ 2 + b₂ ^ 2) : ℝ) : ℂ) +
        Complex.I * ((Real.arctan (b₂ / a) : ℝ) : ℂ) -
        ((((1 / 2 : ℝ) * Real.log (a ^ 2 + b₁ ^ 2) : ℝ) : ℂ) +
        Complex.I * ((Real.arctan (b₁ / a) : ℝ) : ℂ)) := by
    intro a ha
    rw [← intervalIntegral.integral_const_mul]
    have hshift : ∀ y : ℝ,
        Complex.I * ((((a + p.re : ℝ) : ℂ) + (y : ℂ) * Complex.I) - p)⁻¹ =
          Complex.I * ((a : ℂ) + ((y - p.im : ℝ) : ℂ) * Complex.I)⁻¹ := by
      intro y
      congr 2
      apply Complex.ext <;> simp
    simp_rw [hshift]
    have hder : ∀ y ∈ uIcc y₁ y₂,
        HasDerivAt (fun t : ℝ => (((1 / 2 : ℝ) * Real.log (a ^ 2 + (t - p.im) ^ 2) : ℝ) : ℂ) +
          Complex.I * ((Real.arctan ((t - p.im) / a) : ℝ) : ℂ))
          (Complex.I * ((a : ℂ) + ((y - p.im : ℝ) : ℂ) * Complex.I)⁻¹) y := by
      intro y _
      have hc := (hasDerivAt_vert_inv ha (y - p.im)).scomp y ((hasDerivAt_id' y).sub_const p.im)
      simpa only [Function.comp_def, one_smul] using hc
    have hcont : Continuous (fun y : ℝ => Complex.I * ((a : ℂ) + ((y - p.im : ℝ) : ℂ) * Complex.I)⁻¹) := by
      refine continuous_const.mul (Continuous.inv₀ (by fun_prop) fun y h => ?_)
      have := congrArg Complex.re h; simp at this; exact ha this
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hcont.intervalIntegrable _ _)
  have h1 := eval_horiz b₁ hb₁.ne
  have h2 := eval_horiz b₂ hb₂.ne'
  have h3 := eval_vert a₂ ha₂.ne'
  have h4 := eval_vert a₁ ha₁.ne
  have hy₁_eq : b₁ + p.im = y₁ := by dsimp [b₁]; ring
  have hy₂_eq : b₂ + p.im = y₂ := by dsimp [b₂]; ring
  have hx₂_eq : a₂ + p.re = x₂ := by dsimp [a₂]; ring
  have hx₁_eq : a₁ + p.re = x₁ := by dsimp [a₁]; ring
  rw [hy₁_eq] at h1
  rw [hy₂_eq] at h2
  rw [hx₂_eq] at h3
  rw [hx₁_eq] at h4
  unfold rectIntegral
  rw [h1, h2, h3, h4]
  -- Four corner arctan identities: each corner contributes `π / 2`.
  have hc1 : Real.arctan (a₂ / b₂) + Real.arctan (b₂ / a₂) = Real.pi / 2 := by
    have hinv : b₂ / a₂ = (a₂ / b₂)⁻¹ := by rw [inv_div]
    rw [hinv, Real.arctan_inv_of_pos (div_pos ha₂ hb₂)]; ring
  have hc2 : Real.arctan (a₁ / b₁) + Real.arctan (b₁ / a₁) = Real.pi / 2 := by
    have hinv : b₁ / a₁ = (a₁ / b₁)⁻¹ := by rw [inv_div]
    rw [hinv, Real.arctan_inv_of_pos (div_pos_of_neg_of_neg ha₁ hb₁)]; ring
  have hc3 : Real.arctan (a₁ / b₂) + Real.arctan (b₂ / a₁) = -(Real.pi / 2) := by
    have hinv : b₂ / a₁ = (a₁ / b₂)⁻¹ := by rw [inv_div]
    rw [hinv, Real.arctan_inv_of_neg (div_neg_of_neg_of_pos ha₁ hb₂)]; ring
  have hc4 : Real.arctan (a₂ / b₁) + Real.arctan (b₁ / a₂) = -(Real.pi / 2) := by
    have hinv : b₁ / a₂ = (a₂ / b₁)⁻¹ := by rw [inv_div]
    rw [hinv, Real.arctan_inv_of_neg (div_neg_of_pos_of_neg ha₂ hb₁)]; ring
  have hsum_arc :
      -(Real.arctan (a₂ / b₁)) + Real.arctan (a₁ / b₁) + Real.arctan (a₂ / b₂) -
        Real.arctan (a₁ / b₂) + Real.arctan (b₂ / a₂) - Real.arctan (b₁ / a₂) -
        Real.arctan (b₂ / a₁) + Real.arctan (b₁ / a₁) = 2 * Real.pi := by
    linarith only [hc1, hc2, hc3, hc4]
  have hsum_arcC :
      (-((Real.arctan (a₂ / b₁) : ℝ) : ℂ) + ((Real.arctan (a₁ / b₁) : ℝ) : ℂ) +
        ((Real.arctan (a₂ / b₂) : ℝ) : ℂ) - ((Real.arctan (a₁ / b₂) : ℝ) : ℂ) +
        ((Real.arctan (b₂ / a₂) : ℝ) : ℂ) - ((Real.arctan (b₁ / a₂) : ℝ) : ℂ) -
        ((Real.arctan (b₂ / a₁) : ℝ) : ℂ) + ((Real.arctan (b₁ / a₁) : ℝ) : ℂ)) =
        2 * (Real.pi : ℂ) := by
    exact_mod_cast hsum_arc
  calc (((1 / 2 : ℝ) * Real.log (a₂ ^ 2 + b₁ ^ 2) : ℝ) : ℂ) -
        Complex.I * ((Real.arctan (a₂ / b₁) : ℝ) : ℂ) -
        ((((1 / 2 : ℝ) * Real.log (a₁ ^ 2 + b₁ ^ 2) : ℝ) : ℂ) -
          Complex.I * ((Real.arctan (a₁ / b₁) : ℝ) : ℂ)) -
        ((((1 / 2 : ℝ) * Real.log (a₂ ^ 2 + b₂ ^ 2) : ℝ) : ℂ) -
          Complex.I * ((Real.arctan (a₂ / b₂) : ℝ) : ℂ) -
          ((((1 / 2 : ℝ) * Real.log (a₁ ^ 2 + b₂ ^ 2) : ℝ) : ℂ) -
            Complex.I * ((Real.arctan (a₁ / b₂) : ℝ) : ℂ))) +
        ((((1 / 2 : ℝ) * Real.log (a₂ ^ 2 + b₂ ^ 2) : ℝ) : ℂ) +
          Complex.I * ((Real.arctan (b₂ / a₂) : ℝ) : ℂ) -
          ((((1 / 2 : ℝ) * Real.log (a₂ ^ 2 + b₁ ^ 2) : ℝ) : ℂ) +
            Complex.I * ((Real.arctan (b₁ / a₂) : ℝ) : ℂ))) -
        ((((1 / 2 : ℝ) * Real.log (a₁ ^ 2 + b₂ ^ 2) : ℝ) : ℂ) +
          Complex.I * ((Real.arctan (b₂ / a₁) : ℝ) : ℂ) -
          ((((1 / 2 : ℝ) * Real.log (a₁ ^ 2 + b₁ ^ 2) : ℝ) : ℂ) +
            Complex.I * ((Real.arctan (b₁ / a₁) : ℝ) : ℂ)))
      = Complex.I *
        (-((Real.arctan (a₂ / b₁) : ℝ) : ℂ) + ((Real.arctan (a₁ / b₁) : ℝ) : ℂ) +
          ((Real.arctan (a₂ / b₂) : ℝ) : ℂ) - ((Real.arctan (a₁ / b₂) : ℝ) : ℂ) +
          ((Real.arctan (b₂ / a₂) : ℝ) : ℂ) - ((Real.arctan (b₁ / a₂) : ℝ) : ℂ) -
          ((Real.arctan (b₂ / a₁) : ℝ) : ℂ) + ((Real.arctan (b₁ / a₁) : ℝ) : ℂ)) := by ring
    _ = Complex.I * (2 * (Real.pi : ℂ)) := by rw [hsum_arcC]
    _ = 2 * (Real.pi : ℂ) * Complex.I := by ring

/-- Rectangular residue theorem for finitely many simple poles strictly inside `[x₁, x₂] × [y₁, y₂]`. -/
theorem rectIntegral_eq_sum_simple_poles {G H : ℂ → ℂ} {x₁ x₂ y₁ y₂ : ℝ}
    (hx : x₁ < x₂) (hy : y₁ < y₂) (P : Finset ℂ) (res : ℂ → ℂ)
    (hP : ∀ p ∈ P, x₁ < p.re ∧ p.re < x₂ ∧ y₁ < p.im ∧ p.im < y₂)
    (hH : DifferentiableOn ℂ H (Icc x₁ x₂ ×ℂ Icc y₁ y₂))
    (hEdge_bot : ∀ x ∈ Icc x₁ x₂,
      G ((x : ℂ) + (y₁ : ℂ) * Complex.I) = H ((x : ℂ) + (y₁ : ℂ) * Complex.I) +
        ∑ p ∈ P, res p * (((x : ℂ) + (y₁ : ℂ) * Complex.I) - p)⁻¹)
    (hEdge_top : ∀ x ∈ Icc x₁ x₂,
      G ((x : ℂ) + (y₂ : ℂ) * Complex.I) = H ((x : ℂ) + (y₂ : ℂ) * Complex.I) +
        ∑ p ∈ P, res p * (((x : ℂ) + (y₂ : ℂ) * Complex.I) - p)⁻¹)
    (hEdge_right : ∀ y ∈ Icc y₁ y₂,
      G ((x₂ : ℂ) + (y : ℂ) * Complex.I) = H ((x₂ : ℂ) + (y : ℂ) * Complex.I) +
        ∑ p ∈ P, res p * (((x₂ : ℂ) + (y : ℂ) * Complex.I) - p)⁻¹)
    (hEdge_left : ∀ y ∈ Icc y₁ y₂,
      G ((x₁ : ℂ) + (y : ℂ) * Complex.I) = H ((x₁ : ℂ) + (y : ℂ) * Complex.I) +
        ∑ p ∈ P, res p * (((x₁ : ℂ) + (y : ℂ) * Complex.I) - p)⁻¹) :
    rectIntegral G x₁ x₂ y₁ y₂ = 2 * (Real.pi : ℂ) * Complex.I * ∑ p ∈ P, res p := by
  have hH_zero : rectIntegral H x₁ x₂ y₁ y₂ = 0 := by
    refine rectIntegral_eq_zero_of_differentiableOn ?_
    rwa [Set.uIcc_of_le hx.le, Set.uIcc_of_le hy.le]
  have hH_cont := hH.continuousOn
  have hH_bot_int : IntervalIntegrable (fun x : ℝ => H ((x : ℂ) + (y₁ : ℂ) * Complex.I)) volume x₁ x₂ := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hx.le]
    exact hH_cont.comp (by fun_prop) fun x hx' =>
      Complex.mem_reProdIm.mpr ⟨by simpa using hx', by simpa using left_mem_Icc.mpr hy.le⟩
  have hH_top_int : IntervalIntegrable (fun x : ℝ => H ((x : ℂ) + (y₂ : ℂ) * Complex.I)) volume x₁ x₂ := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hx.le]
    exact hH_cont.comp (by fun_prop) fun x hx' =>
      Complex.mem_reProdIm.mpr ⟨by simpa using hx', by simpa using right_mem_Icc.mpr hy.le⟩
  have hH_right_int : IntervalIntegrable (fun y : ℝ => H ((x₂ : ℂ) + (y : ℂ) * Complex.I)) volume y₁ y₂ := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hy.le]
    exact hH_cont.comp (by fun_prop) fun y hy' =>
      Complex.mem_reProdIm.mpr ⟨by simpa using right_mem_Icc.mpr hx.le, by simpa using hy'⟩
  have hH_left_int : IntervalIntegrable (fun y : ℝ => H ((x₁ : ℂ) + (y : ℂ) * Complex.I)) volume y₁ y₂ := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hy.le]
    exact hH_cont.comp (by fun_prop) fun y hy' =>
      Complex.mem_reProdIm.mpr ⟨by simpa using left_mem_Icc.mpr hx.le, by simpa using hy'⟩
  have hp_bot_cont : ∀ p ∈ P, Continuous (fun x : ℝ => res p * (((x : ℂ) + (y₁ : ℂ) * Complex.I) - p)⁻¹) := by
    intro p hp
    refine continuous_const.mul (Continuous.inv₀ (by fun_prop) fun x h => ?_)
    have := congrArg Complex.im h; simp at this; linarith only [this, (hP p hp).2.2.1]
  have hp_top_cont : ∀ p ∈ P, Continuous (fun x : ℝ => res p * (((x : ℂ) + (y₂ : ℂ) * Complex.I) - p)⁻¹) := by
    intro p hp
    refine continuous_const.mul (Continuous.inv₀ (by fun_prop) fun x h => ?_)
    have := congrArg Complex.im h; simp at this; linarith only [this, (hP p hp).2.2.2]
  have hp_right_cont : ∀ p ∈ P, Continuous (fun y : ℝ => res p * (((x₂ : ℂ) + (y : ℂ) * Complex.I) - p)⁻¹) := by
    intro p hp
    refine continuous_const.mul (Continuous.inv₀ (by fun_prop) fun y h => ?_)
    have := congrArg Complex.re h; simp at this; linarith only [this, (hP p hp).2.1]
  have hp_left_cont : ∀ p ∈ P, Continuous (fun y : ℝ => res p * (((x₁ : ℂ) + (y : ℂ) * Complex.I) - p)⁻¹) := by
    intro p hp
    refine continuous_const.mul (Continuous.inv₀ (by fun_prop) fun y h => ?_)
    have := congrArg Complex.re h; simp at this; linarith only [this, (hP p hp).1]
  have hp_bot_int : ∀ p ∈ P, IntervalIntegrable
      (fun x : ℝ => res p * (((x : ℂ) + (y₁ : ℂ) * Complex.I) - p)⁻¹) volume x₁ x₂ :=
    fun p hp => (hp_bot_cont p hp).intervalIntegrable _ _
  have hp_top_int : ∀ p ∈ P, IntervalIntegrable
      (fun x : ℝ => res p * (((x : ℂ) + (y₂ : ℂ) * Complex.I) - p)⁻¹) volume x₁ x₂ :=
    fun p hp => (hp_top_cont p hp).intervalIntegrable _ _
  have hp_right_int : ∀ p ∈ P, IntervalIntegrable
      (fun y : ℝ => res p * (((x₂ : ℂ) + (y : ℂ) * Complex.I) - p)⁻¹) volume y₁ y₂ :=
    fun p hp => (hp_right_cont p hp).intervalIntegrable _ _
  have hp_left_int : ∀ p ∈ P, IntervalIntegrable
      (fun y : ℝ => res p * (((x₁ : ℂ) + (y : ℂ) * Complex.I) - p)⁻¹) volume y₁ y₂ :=
    fun p hp => (hp_left_cont p hp).intervalIntegrable _ _
  have hcont_sum : ∀ (s : Finset ℂ) (F : ℂ → ℝ → ℂ),
      (∀ i ∈ s, Continuous (F i)) → Continuous (fun x : ℝ => ∑ i ∈ s, F i x) := by
    intro s F hF
    induction s using Finset.cons_induction with
    | empty => simpa using continuous_const
    | cons a t ha ih =>
      simp_rw [Finset.sum_cons ha]
      exact (hF a (Finset.mem_cons_self a t)).add
        (ih fun i hi => hF i (Finset.mem_cons_of_mem hi))
  have hp_bot_sum : IntervalIntegrable
      (fun x : ℝ => ∑ p ∈ P, res p * (((x : ℂ) + (y₁ : ℂ) * Complex.I) - p)⁻¹) volume x₁ x₂ :=
    (hcont_sum P _ hp_bot_cont).intervalIntegrable _ _
  have hp_top_sum : IntervalIntegrable
      (fun x : ℝ => ∑ p ∈ P, res p * (((x : ℂ) + (y₂ : ℂ) * Complex.I) - p)⁻¹) volume x₁ x₂ :=
    (hcont_sum P _ hp_top_cont).intervalIntegrable _ _
  have hp_right_sum : IntervalIntegrable
      (fun y : ℝ => ∑ p ∈ P, res p * (((x₂ : ℂ) + (y : ℂ) * Complex.I) - p)⁻¹) volume y₁ y₂ :=
    (hcont_sum P _ hp_right_cont).intervalIntegrable _ _
  have hp_left_sum : IntervalIntegrable
      (fun y : ℝ => ∑ p ∈ P, res p * (((x₁ : ℂ) + (y : ℂ) * Complex.I) - p)⁻¹) volume y₁ y₂ :=
    (hcont_sum P _ hp_left_cont).intervalIntegrable _ _
  have hb_eq : (∫ x in x₁..x₂, G ((x : ℂ) + (y₁ : ℂ) * Complex.I)) =
      (∫ x in x₁..x₂, H ((x : ℂ) + (y₁ : ℂ) * Complex.I)) +
      ∑ p ∈ P, res p * ∫ x in x₁..x₂, (((x : ℂ) + (y₁ : ℂ) * Complex.I) - p)⁻¹ := by
    rw [intervalIntegral.integral_congr (fun x hx' => hEdge_bot x (by rwa [Set.uIcc_of_le hx.le] at hx')),
        intervalIntegral.integral_add hH_bot_int hp_bot_sum,
        intervalIntegral.integral_finsetSum hp_bot_int]
    congr 1; exact Finset.sum_congr rfl fun p _ => intervalIntegral.integral_const_mul _ _
  have ht_eq : (∫ x in x₁..x₂, G ((x : ℂ) + (y₂ : ℂ) * Complex.I)) =
      (∫ x in x₁..x₂, H ((x : ℂ) + (y₂ : ℂ) * Complex.I)) +
      ∑ p ∈ P, res p * ∫ x in x₁..x₂, (((x : ℂ) + (y₂ : ℂ) * Complex.I) - p)⁻¹ := by
    rw [intervalIntegral.integral_congr (fun x hx' => hEdge_top x (by rwa [Set.uIcc_of_le hx.le] at hx')),
        intervalIntegral.integral_add hH_top_int hp_top_sum,
        intervalIntegral.integral_finsetSum hp_top_int]
    congr 1; exact Finset.sum_congr rfl fun p _ => intervalIntegral.integral_const_mul _ _
  have hr_eq : (∫ y in y₁..y₂, G ((x₂ : ℂ) + (y : ℂ) * Complex.I)) =
      (∫ y in y₁..y₂, H ((x₂ : ℂ) + (y : ℂ) * Complex.I)) +
      ∑ p ∈ P, res p * ∫ y in y₁..y₂, (((x₂ : ℂ) + (y : ℂ) * Complex.I) - p)⁻¹ := by
    rw [intervalIntegral.integral_congr (fun y hy' => hEdge_right y (by rwa [Set.uIcc_of_le hy.le] at hy')),
        intervalIntegral.integral_add hH_right_int hp_right_sum,
        intervalIntegral.integral_finsetSum hp_right_int]
    congr 1; exact Finset.sum_congr rfl fun p _ => intervalIntegral.integral_const_mul _ _
  have hl_eq : (∫ y in y₁..y₂, G ((x₁ : ℂ) + (y : ℂ) * Complex.I)) =
      (∫ y in y₁..y₂, H ((x₁ : ℂ) + (y : ℂ) * Complex.I)) +
      ∑ p ∈ P, res p * ∫ y in y₁..y₂, (((x₁ : ℂ) + (y : ℂ) * Complex.I) - p)⁻¹ := by
    rw [intervalIntegral.integral_congr (fun y hy' => hEdge_left y (by rwa [Set.uIcc_of_le hy.le] at hy')),
        intervalIntegral.integral_add hH_left_int hp_left_sum,
        intervalIntegral.integral_finsetSum hp_left_int]
    congr 1; exact Finset.sum_congr rfl fun p _ => intervalIntegral.integral_const_mul _ _
  have hrect : rectIntegral G x₁ x₂ y₁ y₂ =
      rectIntegral H x₁ x₂ y₁ y₂ + ∑ p ∈ P, res p * rectIntegral (fun s => (s - p)⁻¹) x₁ x₂ y₁ y₂ := by
    unfold rectIntegral
    rw [hb_eq, ht_eq, hr_eq, hl_eq]
    simp only [mul_add, mul_sub, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hcomm : ∀ p : ℂ,
        res p * (Complex.I * ∫ y in y₁..y₂, ((x₂ : ℂ) + (y : ℂ) * Complex.I - p)⁻¹) =
          Complex.I * (res p * ∫ y in y₁..y₂, ((x₂ : ℂ) + (y : ℂ) * Complex.I - p)⁻¹) :=
      fun p => by ring
    have hcomm2 : ∀ p : ℂ,
        res p * (Complex.I * ∫ y in y₁..y₂, ((x₁ : ℂ) + (y : ℂ) * Complex.I - p)⁻¹) =
          Complex.I * (res p * ∫ y in y₁..y₂, ((x₁ : ℂ) + (y : ℂ) * Complex.I - p)⁻¹) :=
      fun p => by ring
    simp only [hcomm, hcomm2]
    ring
  rw [hrect, hH_zero, zero_add]
  calc ∑ p ∈ P, res p * rectIntegral (fun s => (s - p)⁻¹) x₁ x₂ y₁ y₂
      = ∑ p ∈ P, res p * (2 * (Real.pi : ℂ) * Complex.I) := by
          refine Finset.sum_congr rfl fun p hp => ?_
          obtain ⟨h1, h2, h3, h4⟩ := hP p hp
          rw [rectIntegral_inv_sub h1 h2 h3 h4]
    _ = 2 * (Real.pi : ℂ) * Complex.I * ∑ p ∈ P, res p := by
          rw [← Finset.sum_mul, mul_comm]

end RectangleResidues

section RightVerticalLineIdentity

/-- Elementary bound `Λ(n) / n² ≤ 2 / n^(3/2)` for `n ≥ 1`. -/
private lemma vonMangoldt_div_sq_le (n : ℕ) :
    (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ 2 ≤ 2 / (n : ℝ) ^ ((3 : ℝ) / 2) := by
  by_cases hn : n = 0
  · subst hn; simp
  · have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hlog : Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
      have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hn_pos)
      rw [Real.log_sqrt hn_pos.le] at h1
      linarith only [h1]
    have hlam : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) :=
      ArithmeticFunction.vonMangoldt_le_log.trans hlog
    have hpow : (n : ℝ) ^ (2 : ℕ) = Real.sqrt (n : ℝ) * (n : ℝ) ^ ((3 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn_pos, show (1 : ℝ) / 2 + 3 / 2 = (2 : ℕ) by norm_num,
          Real.rpow_natCast]
    rw [hpow]
    have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
    have h32_pos : 0 < (n : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hn_pos _
    rw [div_le_div_iff₀ (mul_pos hsq_pos h32_pos) h32_pos]
    nlinarith only [hlam, h32_pos]

/-- Uniform bound on `‖negLogDerivL χ (2 + u * I)‖` on the right vertical line `Re(s) = 2`. -/
lemma norm_negLogDerivL_two_le {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (u : ℝ) :
    ‖negLogDerivL χ (2 + (u : ℂ) * Complex.I)‖ ≤ ∑' n : ℕ, 2 / (n : ℝ) ^ ((3 : ℝ) / 2) := by
  set s : ℂ := 2 + (u : ℂ) * Complex.I
  have hs : 1 < s.re := by simp [s]
  rw [← LSeries_twist_vonMangoldt_eq_negLogDerivL χ hs]
  unfold LSeries
  have hsum_dom : Summable (fun n : ℕ => 2 / (n : ℝ) ^ ((3 : ℝ) / 2)) := by
    have h1 : Summable (fun n : ℕ => ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹) :=
      Real.summable_nat_rpow_inv.mpr (by norm_num)
    simpa [div_eq_mul_inv] using h1.mul_left 2
  have hpt : ∀ n : ℕ,
      ‖LSeries.term (fun k => χ (k : ZMod d) * (ArithmeticFunction.vonMangoldt k : ℂ)) s n‖ ≤
        2 / (n : ℝ) ^ ((3 : ℝ) / 2) := by
    intro n
    by_cases hn : n = 0
    · subst hn; simp [LSeries.term]
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      rw [LSeries.term_of_ne_zero hn, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          Complex.norm_natCast_cpow_of_pos hn_pos]
      have hs_re : s.re = 2 := by simp [s]
      rw [hs_re, Real.rpow_two]
      have h1 : ‖χ (n : ZMod d)‖ * (ArithmeticFunction.vonMangoldt n : ℝ) ≤
          (ArithmeticFunction.vonMangoldt n : ℝ) := by
        have hχ := norm_dirichletChar_le_one χ (n : ZMod d)
        nlinarith only [hχ, ArithmeticFunction.vonMangoldt_nonneg (n := n)]
      exact (div_le_div_of_nonneg_right h1 (by positivity)).trans (vonMangoldt_div_sq_le n)
  have hsumm : Summable (fun n : ℕ =>
      ‖LSeries.term (fun k => χ (k : ZMod d) * (ArithmeticFunction.vonMangoldt k : ℂ)) s n‖) :=
    hsum_dom.of_nonneg_of_le (fun _ => norm_nonneg _) hpt
  exact (norm_tsum_le_tsum_norm hsumm).trans (hsumm.tsum_le_tsum hpt hsum_dom)

/-- Continuity of `negLogDerivL χ` at any `s ≠ 1` where `entireL χ s ≠ 0`. -/
lemma continuousAt_negLogDerivL {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d)
    {s : ℂ} (hs1 : s ≠ 1) (hF : entireL χ s ≠ 0) :
    ContinuousAt (negLogDerivL χ) s := by
  have hF_diff : Differentiable ℂ (entireL χ) := differentiable_entireL χ
  have hF'_cont : ContinuousAt (deriv (entireL χ)) s := (hF_diff.deriv s).continuousAt
  have hF_cont : ContinuousAt (entireL χ) s := (hF_diff s).continuousAt
  have hopen1 : IsOpen {z : ℂ | z ≠ 1} := isOpen_ne
  have hopen2 : IsOpen {z : ℂ | entireL χ z ≠ 0} := isOpen_ne.preimage hF_diff.continuous
  have hlogd_cont : ContinuousAt (fun z : ℂ => deriv (entireL χ) z / entireL χ z) s :=
    hF'_cont.div hF_cont hF
  by_cases hχ : χ = 1
  · have heq : negLogDerivL χ =ᶠ[𝓝 s]
        fun z : ℂ => (1 : ℂ) / (z - 1) - deriv (entireL χ) z / entireL χ z := by
      filter_upwards [hopen1.mem_nhds hs1, hopen2.mem_nhds hF] with z hz1 hzF
      have hzL : χ.LFunction z ≠ 0 := fun h0 => by
        apply hzF; rw [entireL_apply_of_ne_one χ hz1, h0]; simp only [hχ, ↓reduceIte, mul_zero]
      have h := negLogDerivL_eq_of_ne_one χ hz1 hzL
      simpa only [hχ, ↓reduceIte] using h
    have hpole : ContinuousAt (fun z : ℂ => (1 : ℂ) / (z - 1)) s :=
      ContinuousAt.div (f := fun _ : ℂ => (1 : ℂ)) (g := fun z : ℂ => z - 1)
        continuousAt_const ((continuousAt_id (x := s)).sub continuousAt_const) (sub_ne_zero.mpr hs1)
    exact (hpole.sub hlogd_cont).congr heq.symm
  · have heq : negLogDerivL χ =ᶠ[𝓝 s]
        fun z : ℂ => -(deriv (entireL χ) z / entireL χ z) := by
      filter_upwards [hopen1.mem_nhds hs1, hopen2.mem_nhds hF] with z hz1 hzF
      have hzL : χ.LFunction z ≠ 0 := fun h0 => by
        apply hzF; rw [entireL_apply_of_ne_one χ hz1, h0]; simp only [hχ, ↓reduceIte]
      have h := negLogDerivL_eq_of_ne_one χ hz1 hzL
      simpa only [hχ, ↓reduceIte, zero_sub] using h
    exact hlogd_cont.neg.congr heq.symm

/-- Integrability of `mellin (scaledTiltedBump Y t) * negLogDerivL χ` on `Re(s) = 2`. -/
lemma integrable_two_line {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d)
    {Y : ℕ} (hY : 1 ≤ Y) (t : ℝ) :
    Integrable (fun u : ℝ =>
      mellin (scaledTiltedBump Y t) (2 + (u : ℂ) * Complex.I) *
        negLogDerivL χ (2 + (u : ℂ) * Complex.I)) := by
  set C₂ : ℝ := ∑' n : ℕ, 2 / (n : ℝ) ^ ((3 : ℝ) / 2)
  have hker := verticalIntegrable_mellin_scaledTiltedBump hY t (σ := 2) (by norm_num) le_rfl
  have hcont_D : Continuous (fun u : ℝ => negLogDerivL χ (2 + (u : ℂ) * Complex.I)) := by
    refine continuous_iff_continuousAt.mpr fun u => ?_
    set s : ℂ := 2 + (u : ℂ) * Complex.I
    have hs1 : s ≠ 1 := fun h => by have := congrArg Complex.re h; simp [s] at this
    have hL_ne : χ.LFunction s ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hs1) (by simp [s])
    have hF_ne : entireL χ s ≠ 0 := by
      rw [entireL_apply_of_ne_one χ hs1]; split_ifs
      · exact mul_ne_zero (sub_ne_zero.mpr hs1) hL_ne
      · exact hL_ne
    have hmap : ContinuousAt (fun v : ℝ => (2 : ℂ) + (v : ℂ) * Complex.I) u :=
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
    exact ContinuousAt.comp (f := fun v : ℝ => (2 : ℂ) + (v : ℂ) * Complex.I) (g := negLogDerivL χ)
      (continuousAt_negLogDerivL χ hs1 hF_ne) hmap
  refine (hker.norm.mul_const C₂).mono' (hker.aestronglyMeasurable.mul hcont_D.aestronglyMeasurable)
    (Eventually.of_forall fun u => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_negLogDerivL_two_le χ u) (norm_nonneg _)

/-- Inversion on any line of absolute convergence, with the absolute series
on the real axis providing the dominating Dirichlet sum. -/
theorem weightedVonMangoldt_eq_verticalIntegral_of_one_lt {d : ℕ} [NeZero d]
    (χ : DirichletCharacter ℂ d) (K : ℂ → ℂ) (w : ℝ → ℂ) (Y : ℕ)
    {σ : ℝ} (hσ : 1 < σ)
    (hker : Integrable (fun u : ℝ => K ((σ : ℂ) + (u : ℂ) * Complex.I)))
    (hInv : ∀ x : ℝ, 0 < x → mellinInv σ K x = w x)
    (hSupp : ∀ n : ℕ, Y < n → w (n : ℝ) = 0) :
    (∑ n ∈ Finset.Icc 1 Y, (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod d) * w n) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ u : ℝ, K ((σ : ℂ) + (u : ℂ) * Complex.I) *
          negLogDerivL χ ((σ : ℂ) + (u : ℂ) * Complex.I) := by
  let a : ℕ → ℂ := fun n => χ (n : ZMod d) * (ArithmeticFunction.vonMangoldt n : ℂ)
  let m (n : ℕ) := ‖LSeries.term a (σ:ℂ) n‖
  let F : ℕ → ℝ → ℂ := fun n u =>
    K ((σ : ℂ) + (u : ℂ) * Complex.I) *
      LSeries.term a ((σ : ℂ) + (u : ℂ) * Complex.I) n
  have hm : Summable m := by
    have h : LSeriesSummable a (σ:ℂ) :=
      χ.LSeriesSummable_twist_vonMangoldt (by simpa only [Complex.ofReal_re] using hσ)
    exact (summable_norm_iff).mpr h
  have hF_norm : ∀ n u, ‖F n u‖ ≤ ‖K ((σ : ℂ) + (u : ℂ) * Complex.I)‖ * m n := by
    intro n u
    dsimp only [F,m]
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    by_cases hn : n = 0
    · simp [LSeries.term,hn]
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      rw [LSeries.term_of_ne_zero hn,LSeries.term_of_ne_zero hn,norm_div,norm_div,
        Complex.norm_natCast_cpow_of_pos hn_pos,Complex.norm_natCast_cpow_of_pos hn_pos,
        show ((σ:ℂ)+(u:ℂ)*Complex.I).re=σ by simp,Complex.ofReal_re]
  have hF_int : ∀ n : ℕ, Integrable (F n) := by
    intro n
    have hcont_term : Continuous (fun u : ℝ => LSeries.term a ((σ : ℂ) + (u : ℂ) * Complex.I) n) := by
      by_cases hn : n = 0
      · subst hn; simp [LSeries.term]; exact continuous_const
      · simp only [LSeries.term_of_ne_zero hn]
        have hnC : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
        have hcp : Continuous (fun u : ℝ => ((n : ℕ) : ℂ) ^ ((σ : ℂ) + (u : ℂ) * Complex.I)) :=
          Continuous.const_cpow (by fun_prop) (Or.inl hnC)
        exact continuous_const.div hcp fun u => Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
    refine (hker.norm.mul_const (m n)).mono'
      (hker.aestronglyMeasurable.mul hcont_term.aestronglyMeasurable)
      (Eventually.of_forall (hF_norm n))
  have hF_sum : Summable fun n : ℕ => ∫ u : ℝ, ‖F n u‖ := by
    have hsum_dom : Summable fun n : ℕ =>
        (∫ u : ℝ, ‖K ((σ : ℂ) + (u : ℂ) * Complex.I)‖) *
          (m n) := by
      exact hm.mul_left _
    refine hsum_dom.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) fun n => ?_
    calc ∫ u : ℝ, ‖F n u‖
        ≤ ∫ u : ℝ, ‖K ((σ : ℂ) + (u : ℂ) * Complex.I)‖ *
            (m n) :=
          integral_mono (hF_int n).norm (hker.norm.mul_const _) (hF_norm n)
      _ = (∫ u : ℝ, ‖K ((σ : ℂ) + (u : ℂ) * Complex.I)‖) *
            (m n) := integral_mul_const _ _
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm hF_int hF_sum
  have htsum_eq : ∀ u : ℝ,
      (∑' n : ℕ, F n u) = K ((σ : ℂ) + (u : ℂ) * Complex.I) *
        negLogDerivL χ ((σ : ℂ) + (u : ℂ) * Complex.I) := by
    intro u
    have hs : 1 < ((σ : ℂ) + (u : ℂ) * Complex.I).re := by simpa using hσ
    rw [← LSeries_twist_vonMangoldt_eq_negLogDerivL χ hs]
    unfold LSeries
    change (∑' n : ℕ, K ((σ : ℂ) + (u : ℂ) * Complex.I) *
      LSeries.term a ((σ : ℂ) + (u : ℂ) * Complex.I) n) = _
    rw [tsum_mul_left]
  simp_rw [htsum_eq] at hswap
  have hterm_eval : ∀ n : ℕ,
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ u : ℝ, F n u) =
        (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod d) * w (n : ℝ) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp [F, LSeries.term]
    · have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have hF_rw : ∀ u : ℝ, F n u = a n * (((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (u : ℂ) * Complex.I)) *
          K ((σ : ℂ) + (u : ℂ) * Complex.I)) := by
        intro u
        dsimp [F]
        rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]
        ring
      simp_rw [hF_rw]
      rw [integral_const_mul]
      have hinv := hInv (n : ℝ) hn_pos
      unfold mellinInv at hinv
      simp only [smul_eq_mul, Complex.real_smul] at hinv
      calc ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (a n * ∫ u : ℝ, ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (u : ℂ) * Complex.I)) *
              K ((σ : ℂ) + (u : ℂ) * Complex.I))
          = a n * (((1 / (2 * Real.pi) : ℝ) : ℂ) *
              ∫ u : ℝ, ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (u : ℂ) * Complex.I)) *
                K ((σ : ℂ) + (u : ℂ) * Complex.I)) := by ring
        _ = a n * w (n : ℝ) := by rw [hinv]
        _ = (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod d) * w (n : ℝ) := by
            dsimp [a]; ring
  have hsum_collapse : (∑' n : ℕ, ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ u : ℝ, F n u) =
      ∑ n ∈ Finset.Icc 1 Y,
        (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod d) * w n := by
    simp_rw [hterm_eval]
    refine tsum_eq_sum fun n hn => ?_
    by_cases hn0 : n = 0
    · subst n; simp
    · rw [hSupp n (by simpa [Finset.mem_Icc, Nat.one_le_iff_ne_zero, hn0] using hn), mul_zero]
  rw [← hsum_collapse, tsum_mul_left, hswap]

/-- Mellin inversion on the line of real part two. -/
theorem weightedVonMangoldt_eq_verticalIntegral {d : ℕ} [NeZero d]
    (χ : DirichletCharacter ℂ d) (K : ℂ → ℂ) (w : ℝ → ℂ) (Y : ℕ)
    (hker : Integrable (fun u : ℝ => K (2 + (u : ℂ) * Complex.I)))
    (hInv : ∀ x : ℝ, 0 < x → mellinInv 2 K x = w x)
    (hSupp : ∀ n : ℕ, Y < n → w (n : ℝ) = 0) :
    (∑ n ∈ Finset.Icc 1 Y, (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod d) * w n) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ u : ℝ, K (2 + (u : ℂ) * Complex.I) *
          negLogDerivL χ (2 + (u : ℂ) * Complex.I) := by
  simpa only [Complex.ofReal_ofNat] using
    weightedVonMangoldt_eq_verticalIntegral_of_one_lt χ K w Y (σ:=2) (by norm_num)
      (by simpa only [Complex.ofReal_ofNat] using hker) hInv hSupp

/-- Mellin inversion for the quartic weight on the right side of the contour. -/
theorem smoothedPrimeSum_eq_verticalIntegral {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d)
    {Y : ℕ} (hY : 1 ≤ Y) (t : ℝ) :
    (∑ n ∈ Finset.Icc 1 Y,
      (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod d) *
        scaledTiltedBump Y t (n : ℝ)) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ u : ℝ, mellin (scaledTiltedBump Y t) (2 + (u : ℂ) * Complex.I) *
          negLogDerivL χ (2 + (u : ℂ) * Complex.I) := by
  apply weightedVonMangoldt_eq_verticalIntegral _ _ _ _
    (verticalIntegrable_mellin_scaledTiltedBump hY t (σ := 2) (by norm_num) le_rfl)
    (fun x hx => mellinInv_scaledTiltedBump_eq hY t (σ := 2) (by norm_num) le_rfl hx)
  intro n hn
  have hY_pos : (0 : ℝ) < (Y : ℝ) := Nat.cast_pos.mpr (by omega)
  have hgt1 : 1 < (n : ℝ) / (Y : ℝ) := (one_lt_div hY_pos).mpr (Nat.cast_lt.mpr hn)
  have hnot : ¬(0 < (n : ℝ) / (Y : ℝ) ∧ (n : ℝ) / (Y : ℝ) < 1) :=
    fun h => not_lt.mpr h.2.le hgt1
  simp [scaledTiltedBump, quarticBump_eq_zero_of_not_mem hnot]

end RightVerticalLineIdentity

section ZeroSummabilityAndQuarterIntegrability

/-- Critical-strip zeros of `entireL χ` in the half-open unit vertical band `k ≤ Im(ρ) < k + 1`. -/
noncomputable def bandZeros {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (k : ℤ) : Finset ℂ :=
  (diskZeros χ (2 + ((k : ℝ) : ℂ) * Complex.I) ((15 : ℝ) / 8)).filter
    fun ρ => 0 < ρ.re ∧ (k : ℝ) ≤ ρ.im ∧ ρ.im < (k : ℝ) + 1

/-- A kernel's contribution at a zero of the primitive Dirichlet L-function. -/
noncomputable def kernelZeroTerm {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d)
    (K : ℂ → ℂ) (ρ : ℂ) : ℂ :=
  if 0 < ρ.re ∧ entireL χ ρ = 0 then (zeroMult χ ρ : ℂ) * K ρ else 0

/-- Individual zero contribution `m_ρ * f̃(ρ)` supported on `0 < ρ.re ∧ entireL χ ρ = 0`. -/
noncomputable def zeroTerm {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (Y : ℕ) (t : ℝ) (ρ : ℂ) : ℂ :=
  if 0 < ρ.re ∧ entireL χ ρ = 0 then
    (zeroMult χ ρ : ℂ) * mellin (scaledTiltedBump Y t) ρ
  else 0

lemma mem_bandZeros_iff (hGRH : DirichletGRH) {d : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) {k : ℤ} {ρ : ℂ} :
    ρ ∈ bandZeros χ k ↔ 0 < ρ.re ∧ entireL χ ρ = 0 ∧ (k : ℝ) ≤ ρ.im ∧ ρ.im < (k : ℝ) + 1 := by
  unfold bandZeros
  rw [Finset.mem_filter, mem_diskZeros_iff]
  constructor
  · rintro ⟨⟨_, h0⟩, hre, hlo, hhi⟩
    exact ⟨hre, h0, hlo, hhi⟩
  · rintro ⟨hre, h0, hlo, hhi⟩
    have him : |ρ.im - (k : ℝ)| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith only [hlo, hhi]
    have hmem := (mem_diskZeros_iff χ).mp (mem_diskZeros_of_im_sub_le_one hGRH hprim (k : ℝ) hre h0 him)
    exact ⟨hmem, hre, hlo, hhi⟩

lemma bandZeros_disjoint {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) {k₁ k₂ : ℤ} (hne : k₁ ≠ k₂) :
    Disjoint (bandZeros χ k₁) (bandZeros χ k₂) := by
  rw [Finset.disjoint_left]
  intro ρ h1 h2
  have hb1 := (Finset.mem_filter.mp h1).2
  have hb2 := (Finset.mem_filter.mp h2).2
  have hlt1 : (k₁ : ℝ) < (k₂ : ℝ) + 1 := lt_of_le_of_lt hb1.2.1 hb2.2.2
  have hlt2 : (k₂ : ℝ) < (k₁ : ℝ) + 1 := lt_of_le_of_lt hb2.2.1 hb1.2.2
  have hlt1' : k₁ < k₂ + 1 := by exact_mod_cast hlt1
  have hlt2' : k₂ < k₁ + 1 := by exact_mod_cast hlt2
  omega

/-- Elementary inequality: `log(2 + x) ≤ 2 * √(2 + x)` for `0 ≤ x`. -/
private lemma log_two_add_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) :
    Real.log (2 + x) ≤ 2 * Real.sqrt (2 + x) := by
  have hpos : 0 < 2 + x := by linarith only [hx]
  have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hpos)
  rw [Real.log_sqrt hpos.le] at h1
  linarith only [h1]

/-- Elementary integrability: `u ↦ (1 + |u|)^(-(3/2))` is integrable on `ℝ`. -/
private lemma integrable_one_add_abs_rpow_neg_three_halves :
    Integrable (fun u : ℝ => (1 + |u|) ^ (-(3 / 2 : ℝ))) := by
  have hcont : Continuous (fun u : ℝ => (1 + |u|) ^ (-(3 / 2 : ℝ))) :=
    Continuous.rpow (continuous_const.add continuous_abs) continuous_const fun u =>
      Or.inl (by positivity)
  have hIoc : IntegrableOn (fun u : ℝ => (1 + |u|) ^ (-(3 / 2 : ℝ))) (Ioc 0 1) :=
    (hcont.continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hIoi1 : IntegrableOn (fun u : ℝ => (1 + |u|) ^ (-(3 / 2 : ℝ))) (Ioi 1) := by
    have hdom := integrableOn_Ioi_rpow_of_lt (a := -(3 / 2 : ℝ)) (c := (1 : ℝ)) (by norm_num) zero_lt_one
    refine hdom.mono' hcont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : 1 < u := hu
    have hu0 : 0 < u := zero_lt_one.trans hu1
    rw [Real.norm_of_nonneg (by positivity), abs_of_pos hu0]
    exact Real.rpow_le_rpow_of_nonpos hu0 (by linarith only [hu1]) (by norm_num)
  have hpos_int : IntegrableOn (fun u : ℝ => (1 + |u|) ^ (-(3 / 2 : ℝ))) (Ioi 0) := by
    have hunion : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := Ioc_union_Ioi_eq_Ioi zero_le_one
    rw [← hunion]
    exact hIoc.union hIoi1
  have hneg_int : IntegrableOn (fun u : ℝ => (1 + |u|) ^ (-(3 / 2 : ℝ))) (Iic 0) := by
    have h1 : IntegrableOn (fun u : ℝ => (1 + |-u|) ^ (-(3 / 2 : ℝ))) (Iio 0) := by
      have := hpos_int.comp_neg
      simpa using this
    have h2 : IntegrableOn (fun u : ℝ => (1 + |u|) ^ (-(3 / 2 : ℝ))) (Iio 0) := by
      simpa [abs_neg] using h1
    exact h2.congr_set_ae Iio_ae_eq_Iic.symm
  have hunion : (Iic (0 : ℝ)) ∪ (Ioi 0) = Set.univ := Iic_union_Ioi
  rw [← integrableOn_univ, ← hunion]
  exact hneg_int.union hpos_int

/-- Summability of `k : ℤ ↦ (1 + |(k : ℝ)|)^(-(3/2))`. -/
private lemma summable_int_one_add_abs_rpow_neg_three_halves :
    Summable (fun k : ℤ => (1 + |(k : ℝ)|) ^ (-(3 / 2 : ℝ))) := by
  have hnat : Summable (fun n : ℕ => ((1 + (n : ℝ)) ^ (-(3 / 2 : ℝ)))) := by
    have h1 : Summable (fun n : ℕ => ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹) :=
      Real.summable_nat_rpow_inv.mpr (by norm_num)
    have hshift : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2))⁻¹) :=
      (summable_nat_add_iff 1).mpr h1
    refine hshift.congr fun n => ?_
    rw [Real.rpow_neg (by positivity), Nat.cast_add, Nat.cast_one, add_comm]
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · refine hnat.congr fun n => ?_
    simp [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
  · refine hnat.congr fun n => ?_
    simp [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]

/-- Band-by-band bound on `zeroTerm` in `bandZeros χ k`, reusable in both A3 and A4. -/
theorem sum_norm_zeroTerm_band_le (hGRH : DirichletGRH) {d : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) {Y : ℕ} (hY : 1 ≤ Y) (t : ℝ) (k : ℤ) :
    (∑ ρ ∈ bandZeros χ k, ‖zeroTerm χ Y t ρ‖) ≤
      Real.sqrt (Y : ℝ) *
        (if 4 * Real.pi * |t * (Y : ℝ)| + 3 ≤ |(k : ℝ)| then
          60000 / (1 + |(k : ℝ)|) ^ 2
        else
          1792 / Real.sqrt (1 + |t * (Y : ℝ)|)) *
        (217 * Real.log (2 * (d : ℝ) * (2 + |(k : ℝ)|))) := by
  have hY_pos : (0 : ℝ) < (Y : ℝ) := Nat.cast_pos.mpr (by omega)
  have hcnt : (∑ ρ ∈ bandZeros χ k, (zeroMult χ ρ : ℝ)) ≤
      217 * Real.log (2 * (d : ℝ) * (2 + |(k : ℝ)|)) := by
    refine zeroCount_unit hGRH hprim (k : ℝ) (bandZeros χ k) fun ρ hρ => ?_
    obtain ⟨hre, h0, hlo, hhi⟩ := (mem_bandZeros_iff hGRH hprim).mp hρ
    exact ⟨hre, h0, by rw [abs_le]; constructor <;> linarith only [hlo, hhi]⟩
  set Kbound : ℝ :=
    if 4 * Real.pi * |t * (Y : ℝ)| + 3 ≤ |(k : ℝ)| then
      60000 / (1 + |(k : ℝ)|) ^ 2
    else
      1792 / Real.sqrt (1 + |t * (Y : ℝ)|)
  have hK_nn : 0 ≤ Kbound := by dsimp [Kbound]; split_ifs <;> positivity
  have hpt : ∀ ρ ∈ bandZeros χ k,
      ‖zeroTerm χ Y t ρ‖ ≤ (Real.sqrt (Y : ℝ) * Kbound) * (zeroMult χ ρ : ℝ) := by
    intro ρ hρ
    obtain ⟨hre, h0, hlo, hhi⟩ := (mem_bandZeros_iff hGRH hprim).mp hρ
    have hhalf : ρ.re = 1 / 2 := entireL_re_eq_half_of_eq_zero hGRH hprim hre h0
    have hρ_eq : ρ = ((1 / 2 : ℝ) : ℂ) + (ρ.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hhalf]
    unfold zeroTerm
    simp only [hre, h0, and_self, ↓reduceIte]
    rw [mellin_scaledTiltedBump_eq hY t ρ, norm_mul, norm_mul, Complex.norm_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos hY_pos, hhalf, ← Real.sqrt_eq_rpow]
    have hker_le : ‖quarticKernel (t * (Y : ℝ)) ρ‖ ≤ Kbound := by
      rw [hρ_eq]
      dsimp [Kbound]
      split_ifs with htail
      · have hρ_im_ge : |(k : ℝ)| - 1 ≤ |ρ.im| := by
          have hsub : |ρ.im - (k : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> linarith only [hlo, hhi]
          have htri := abs_sub_abs_le_abs_sub (k : ℝ) ρ.im
          rw [abs_sub_comm] at htri
          linarith only [htri, hsub]
        have hγ : 4 * Real.pi * |t * (Y : ℝ)| + 2 ≤ |ρ.im| := by linarith only [htail, hρ_im_ge]
        have h1 := quarticKernel_norm_le_tail (lam := t * (Y : ℝ)) (σ := 1 / 2) (γ := ρ.im)
          (by norm_num) (by norm_num) hγ
        have hk_ge3 : 3 ≤ |(k : ℝ)| := by
          have : 0 ≤ 4 * Real.pi * |t * (Y : ℝ)| := by positivity
          linarith only [htail, this]
        have h2 : (1 + |(k : ℝ)|) / 2 ≤ 1 + |ρ.im| := by linarith only [hρ_im_ge, hk_ge3]
        have hsq : (1 + |(k : ℝ)|) ^ 2 / 4 ≤ (1 + |ρ.im|) ^ 2 := by
          have hnn : 0 ≤ (1 + |(k : ℝ)|) / 2 := by positivity
          nlinarith only [h2, hnn]
        have hcmp : 15000 / (1 + |ρ.im|) ^ 2 ≤ 60000 / (1 + |(k : ℝ)|) ^ 2 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith only [hsq]
        exact h1.trans hcmp
      · exact quarticKernel_norm_le_inv_sqrt (lam := t * (Y : ℝ)) (σ := 1 / 2) (γ := ρ.im)
          (by norm_num) (by norm_num)
    calc (zeroMult χ ρ : ℝ) * (Real.sqrt (Y : ℝ) * ‖quarticKernel (t * (Y : ℝ)) ρ‖)
        ≤ (zeroMult χ ρ : ℝ) * (Real.sqrt (Y : ℝ) * Kbound) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hker_le (Real.sqrt_nonneg _))
            (Nat.cast_nonneg _)
      _ = (Real.sqrt (Y : ℝ) * Kbound) * (zeroMult χ ρ : ℝ) := mul_comm _ _
  calc ∑ ρ ∈ bandZeros χ k, ‖zeroTerm χ Y t ρ‖
      ≤ ∑ ρ ∈ bandZeros χ k, (Real.sqrt (Y : ℝ) * Kbound) * (zeroMult χ ρ : ℝ) :=
        Finset.sum_le_sum hpt
    _ = (Real.sqrt (Y : ℝ) * Kbound) * ∑ ρ ∈ bandZeros χ k, (zeroMult χ ρ : ℝ) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (Real.sqrt (Y : ℝ) * Kbound) * (217 * Real.log (2 * (d : ℝ) * (2 + |(k : ℝ)|))) :=
        mul_le_mul_of_nonneg_left hcnt (by positivity)

/-- Summability of the band upper bounds over `k : ℤ`. -/
lemma summable_band_zero_bound {d : ℕ} [NeZero d] {Y : ℕ} (hY : 1 ≤ Y) (t : ℝ) :
    Summable fun k : ℤ =>
      Real.sqrt (Y : ℝ) *
        (if 4 * Real.pi * |t * (Y : ℝ)| + 3 ≤ |(k : ℝ)| then
          60000 / (1 + |(k : ℝ)|) ^ 2
        else
          1792 / Real.sqrt (1 + |t * (Y : ℝ)|)) *
        (217 * Real.log (2 * (d : ℝ) * (2 + |(k : ℝ)|))) := by
  set R : ℝ := 4 * Real.pi * |t * (Y : ℝ)| + 3
  have hR_pos : 0 < R := by dsimp [R]; positivity
  set Clog : ℝ := Real.log (2 * (d : ℝ)) + 4
  have hClog_pos : 0 < Clog := by
    have hd : (1 : ℝ) ≤ d := Nat.one_le_cast.mpr (NeZero.pos d)
    have : 0 ≤ Real.log (2 * (d : ℝ)) := Real.log_nonneg (by linarith only [hd])
    dsimp [Clog]; linarith only [this]
  set Cbig : ℝ := Real.sqrt (Y : ℝ) * max 60000 (1792 * (1 + R) ^ 2) * (217 * Clog)
  refine (summable_int_one_add_abs_rpow_neg_three_halves.mul_left Cbig).of_nonneg_of_le
    (fun k => by
      have := one_le_log_two_mul_d_mul d (k : ℝ)
      split_ifs <;> positivity)
    fun k => ?_
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hlog_le : Real.log (2 * (d : ℝ) * (2 + |(k : ℝ)|)) ≤ Clog * Real.sqrt (1 + |(k : ℝ)|) := by
    rw [Real.log_mul (by positivity) (by positivity)]
    have h1 := log_two_add_le_two_sqrt (abs_nonneg (k : ℝ))
    have hsqrt4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two]
    have h2 : Real.sqrt (2 + |(k : ℝ)|) ≤ 2 * Real.sqrt (1 + |(k : ℝ)|) := by
      have hsq : 2 + |(k : ℝ)| ≤ 4 * (1 + |(k : ℝ)|) := by linarith only [abs_nonneg (k : ℝ)]
      calc Real.sqrt (2 + |(k : ℝ)|) ≤ Real.sqrt (4 * (1 + |(k : ℝ)|)) := Real.sqrt_le_sqrt hsq
        _ = 2 * Real.sqrt (1 + |(k : ℝ)|) := by rw [Real.sqrt_mul (by norm_num), hsqrt4]
    have hsq1 : (1 : ℝ) ≤ Real.sqrt (1 + |(k : ℝ)|) := by
      rw [Real.le_sqrt zero_le_one (by positivity)]; linarith only [abs_nonneg (k : ℝ)]
    have hlog2d : 0 ≤ Real.log (2 * (d : ℝ)) := Real.log_nonneg (by
      have hd : (1 : ℝ) ≤ d := Nat.one_le_cast.mpr (NeZero.pos d); linarith only [hd])
    dsimp [Clog]
    nlinarith only [h1, h2, hsq1, hlog2d]
  have hker_le :
      (if R ≤ |(k : ℝ)| then 60000 / (1 + |(k : ℝ)|) ^ 2 else 1792 / Real.sqrt (1 + |t * (Y : ℝ)|)) ≤
        max 60000 (1792 * (1 + R) ^ 2) / (1 + |(k : ℝ)|) ^ 2 := by
    split_ifs with hk
    · exact div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
    · push Not at hk
      have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (1 + |t * (Y : ℝ)|) := by
        rw [Real.le_sqrt zero_le_one (by positivity)]; linarith only [abs_nonneg (t * (Y : ℝ))]
      have h1 : 1792 / Real.sqrt (1 + |t * (Y : ℝ)|) ≤ 1792 := div_le_self (by norm_num) hsqrt1
      have h2 : 1 + |(k : ℝ)| ≤ 1 + R := by linarith only [hk]
      have h3 : (1 + |(k : ℝ)|) ^ 2 ≤ (1 + R) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h2 2
      have h4 : (1792 : ℝ) ≤ 1792 * (1 + R) ^ 2 / (1 + |(k : ℝ)|) ^ 2 := by
        rw [le_div_iff₀ (by positivity)]; nlinarith only [h3]
      exact h1.trans (h4.trans (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)))
  have hrpow : Real.sqrt (1 + |(k : ℝ)|) / (1 + |(k : ℝ)|) ^ 2 = (1 + |(k : ℝ)|) ^ (-(3 / 2 : ℝ)) := by
    have hpos : 0 < 1 + |(k : ℝ)| := by positivity
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (1 + |(k : ℝ)|) 2, ← Real.rpow_sub hpos]
    norm_num
  have hlog_nn : 0 ≤ Real.log (2 * (d : ℝ) * (2 + |(k : ℝ)|)) := by
    linarith only [one_le_log_two_mul_d_mul d (k : ℝ)]
  calc Real.sqrt (Y : ℝ) *
        (if R ≤ |(k : ℝ)| then 60000 / (1 + |(k : ℝ)|) ^ 2 else 1792 / Real.sqrt (1 + |t * (Y : ℝ)|)) *
        (217 * Real.log (2 * (d : ℝ) * (2 + |(k : ℝ)|)))
      ≤ Real.sqrt (Y : ℝ) *
        (max 60000 (1792 * (1 + R) ^ 2) / (1 + |(k : ℝ)|) ^ 2) *
        (217 * (Clog * Real.sqrt (1 + |(k : ℝ)|))) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hker_le (Real.sqrt_nonneg _))
            (mul_le_mul_of_nonneg_left hlog_le (by norm_num))
            (by positivity) (by positivity)
    _ = Cbig * (Real.sqrt (1 + |(k : ℝ)|) / (1 + |(k : ℝ)|) ^ 2) := by dsimp [Cbig]; ring
    _ = Cbig * (1 + |(k : ℝ)|) ^ (-(3 / 2 : ℝ)) := by rw [hrpow]

/-- Absolute summability of the critical-strip zero sum `∑'_ρ m_ρ f̃(ρ)`. -/
theorem summable_norm_zeroTerm (hGRH : DirichletGRH) {d : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) {Y : ℕ} (hY : 1 ≤ Y) (t : ℝ) :
    Summable (fun ρ : ℂ => ‖zeroTerm χ Y t ρ‖) := by
  let B : ℤ → ℝ := fun k =>
    Real.sqrt (Y : ℝ) *
      (if 4 * Real.pi * |t * (Y : ℝ)| + 3 ≤ |(k : ℝ)| then
        60000 / (1 + |(k : ℝ)|) ^ 2
      else
        1792 / Real.sqrt (1 + |t * (Y : ℝ)|)) *
      (217 * Real.log (2 * (d : ℝ) * (2 + |(k : ℝ)|)))
  have hB_sum : Summable B := summable_band_zero_bound (d := d) hY t
  have hB_nn : ∀ k : ℤ, 0 ≤ B k := fun k => by
    have := one_le_log_two_mul_d_mul d (k : ℝ)
    dsimp [B]; split_ifs <;> positivity
  refine summable_of_sum_le (fun _ => norm_nonneg _) (c := ∑' k : ℤ, B k) fun S => ?_
  let K : Finset ℤ := S.image (fun ρ => ⌊ρ.im⌋)
  have hsub : S.filter (fun ρ => 0 < ρ.re ∧ entireL χ ρ = 0) ⊆ K.biUnion (bandZeros χ) := by
    intro ρ hρ
    obtain ⟨hρS, hre, h0⟩ := Finset.mem_filter.mp hρ
    refine Finset.mem_biUnion.mpr ⟨⌊ρ.im⌋, Finset.mem_image_of_mem _ hρS, ?_⟩
    exact (mem_bandZeros_iff hGRH hprim).mpr ⟨hre, h0, Int.floor_le ρ.im, Int.lt_floor_add_one ρ.im⟩
  have hfilt : (∑ ρ ∈ S, ‖zeroTerm χ Y t ρ‖) =
      ∑ ρ ∈ S.filter (fun ρ => 0 < ρ.re ∧ entireL χ ρ = 0), ‖zeroTerm χ Y t ρ‖ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    unfold zeroTerm; split_ifs <;> simp
  calc ∑ ρ ∈ S, ‖zeroTerm χ Y t ρ‖
      = ∑ ρ ∈ S.filter (fun ρ => 0 < ρ.re ∧ entireL χ ρ = 0), ‖zeroTerm χ Y t ρ‖ := hfilt
    _ ≤ ∑ ρ ∈ K.biUnion (bandZeros χ), ‖zeroTerm χ Y t ρ‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => norm_nonneg _
    _ = ∑ k ∈ K, ∑ ρ ∈ bandZeros χ k, ‖zeroTerm χ Y t ρ‖ :=
        Finset.sum_biUnion fun k₁ _ k₂ _ hne => bandZeros_disjoint χ hne
    _ ≤ ∑ k ∈ K, B k := Finset.sum_le_sum fun k _ => sum_norm_zeroTerm_band_le hGRH hprim hY t k
    _ ≤ ∑' k : ℤ, B k := hB_sum.sum_le_tsum K fun k _ => hB_nn k

theorem summable_zeroTerm (hGRH : DirichletGRH) {d : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) {Y : ℕ} (hY : 1 ≤ Y) (t : ℝ) :
    Summable (zeroTerm χ Y t) :=
  (summable_norm_zeroTerm hGRH hprim hY t).of_norm

/-- Integrability of `u ↦ f̃(1/4 + iu) * (-L'/L)(1/4 + iu, χ)` on `ℝ`. -/
theorem integrable_quarter_line (hGRH : DirichletGRH) {d : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) {Y : ℕ} (hY : 1 ≤ Y) (t : ℝ) :
    Integrable (fun u : ℝ =>
      mellin (scaledTiltedBump Y t) ((1 / 4 : ℝ) + (u : ℂ) * Complex.I) *
        negLogDerivL χ ((1 / 4 : ℝ) + (u : ℂ) * Complex.I)) := by
  have hY_pos : (0 : ℝ) < (Y : ℝ) := Nat.cast_pos.mpr (by omega)
  have hcont_M : Continuous (fun u : ℝ => mellin (scaledTiltedBump Y t) ((1 / 4 : ℝ) + (u : ℂ) * Complex.I)) := by
    refine continuous_iff_continuousAt.mpr fun u => ?_
    have hdiff := differentiableAt_mellin_scaledTiltedBump hY (t := t)
      (s := ((1 / 4 : ℝ) : ℂ) + (u : ℂ) * Complex.I) (by simp; norm_num)
    exact ContinuousAt.comp (f := fun v : ℝ => ((1 / 4 : ℝ) : ℂ) + (v : ℂ) * Complex.I)
      (g := mellin (scaledTiltedBump Y t)) hdiff.continuousAt (by fun_prop)
  have hcont_D : Continuous (fun u : ℝ => negLogDerivL χ ((1 / 4 : ℝ) + (u : ℂ) * Complex.I)) := by
    refine continuous_iff_continuousAt.mpr fun u => ?_
    set s : ℂ := ((1 / 4 : ℝ) : ℂ) + (u : ℂ) * Complex.I
    have hs_re : s.re = 1 / 4 := by simp [s]
    have hs1 : s ≠ 1 := fun h => by rw [h] at hs_re; norm_num at hs_re
    have hF_ne : entireL χ s ≠ 0 := fun h0 => by
      have := entireL_re_eq_half_of_eq_zero hGRH hprim (by linarith : 0 < s.re) h0
      linarith only [hs_re, this]
    have hmap : ContinuousAt (fun v : ℝ => ((1 / 4 : ℝ) : ℂ) + (v : ℂ) * Complex.I) u :=
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
    exact ContinuousAt.comp (f := fun v : ℝ => ((1 / 4 : ℝ) : ℂ) + (v : ℂ) * Complex.I)
      (g := negLogDerivL χ) (continuousAt_negLogDerivL χ hs1 hF_ne) hmap
  set R : ℝ := 4 * Real.pi * |t * (Y : ℝ)| + 2
  set Clog : ℝ := Real.log (2 * (d : ℝ)) + 4
  have hClog_pos : 0 < Clog := by
    have hd : (1 : ℝ) ≤ d := Nat.one_le_cast.mpr (NeZero.pos d)
    have : 0 ≤ Real.log (2 * (d : ℝ)) := Real.log_nonneg (by linarith only [hd])
    dsimp [Clog]; linarith only [this]
  set Cdom : ℝ := (Y : ℝ) ^ ((1 : ℝ) / 4) * max 15000 (1792 * (1 + R) ^ 2) * (812870 * Clog)
  refine (integrable_one_add_abs_rpow_neg_three_halves.const_mul Cdom).mono'
    (hcont_M.aestronglyMeasurable.mul hcont_D.aestronglyMeasurable) (Eventually.of_forall fun u => ?_)
  rw [norm_mul, mellin_scaledTiltedBump_eq hY t _, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hY_pos]
  have hre : (((1 / 4 : ℝ) : ℂ) + (u : ℂ) * Complex.I).re = 1 / 4 := by simp
  rw [hre]
  have hD := negLogDeriv_quarter hGRH hprim u
  have hker : ‖quarticKernel (t * (Y : ℝ)) ((1 / 4 : ℝ) + (u : ℂ) * Complex.I)‖ ≤
      max 15000 (1792 * (1 + R) ^ 2) / (1 + |u|) ^ 2 := by
    by_cases hu : R ≤ |u|
    · exact (quarticKernel_norm_le_tail (by norm_num) (by norm_num) hu).trans
        (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
    · push Not at hu
      have h1 := quarticKernel_norm_le_inv_sqrt (lam := t * (Y : ℝ)) (σ := 1 / 4) (γ := u)
        (by norm_num) (by norm_num)
      have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (1 + |t * (Y : ℝ)|) := by
        rw [Real.le_sqrt zero_le_one (by positivity)]; linarith only [abs_nonneg (t * (Y : ℝ))]
      have hle1 : 1792 / Real.sqrt (1 + |t * (Y : ℝ)|) ≤ 1792 := div_le_self (by norm_num) hsqrt1
      have h2 : (1 + |u|) ^ 2 ≤ (1 + R) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith only [hu]) 2
      have h3 : (1792 : ℝ) ≤ 1792 * (1 + R) ^ 2 / (1 + |u|) ^ 2 := by
        rw [le_div_iff₀ (by positivity)]; nlinarith only [h2]
      exact h1.trans (hle1.trans (h3.trans (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity))))
  have hlog : Real.log (2 * (d : ℝ) * (2 + |u|)) ≤ Clog * Real.sqrt (1 + |u|) := by
    have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
    rw [Real.log_mul (by positivity) (by positivity)]
    have h1 := log_two_add_le_two_sqrt (abs_nonneg u)
    have hsqrt4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two]
    have h2 : Real.sqrt (2 + |u|) ≤ 2 * Real.sqrt (1 + |u|) := by
      calc Real.sqrt (2 + |u|) ≤ Real.sqrt (4 * (1 + |u|)) :=
            Real.sqrt_le_sqrt (by linarith only [abs_nonneg u])
        _ = 2 * Real.sqrt (1 + |u|) := by rw [Real.sqrt_mul (by norm_num), hsqrt4]
    have hsq1 : (1 : ℝ) ≤ Real.sqrt (1 + |u|) := by
      rw [Real.le_sqrt zero_le_one (by positivity)]; linarith only [abs_nonneg u]
    have hlog2d : 0 ≤ Real.log (2 * (d : ℝ)) := Real.log_nonneg (by
      have hd : (1 : ℝ) ≤ d := Nat.one_le_cast.mpr (NeZero.pos d); linarith only [hd])
    dsimp [Clog]
    nlinarith only [h1, h2, hsq1, hlog2d]
  have hrpow : Real.sqrt (1 + |u|) / (1 + |u|) ^ 2 = (1 + |u|) ^ (-(3 / 2 : ℝ)) := by
    have hpos : 0 < 1 + |u| := by positivity
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (1 + |u|) 2, ← Real.rpow_sub hpos]
    norm_num
  calc (Y : ℝ) ^ ((1 : ℝ) / 4) * ‖quarticKernel (t * (Y : ℝ)) ((1 / 4 : ℝ) + (u : ℂ) * Complex.I)‖ *
        ‖negLogDerivL χ ((1 / 4 : ℝ) + (u : ℂ) * Complex.I)‖
      ≤ (Y : ℝ) ^ ((1 : ℝ) / 4) * (max 15000 (1792 * (1 + R) ^ 2) / (1 + |u|) ^ 2) *
        (812870 * (Clog * Real.sqrt (1 + |u|))) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hker (by positivity))
            (hD.trans (mul_le_mul_of_nonneg_left hlog (by norm_num)))
            (norm_nonneg _) (by positivity)
    _ = Cdom * (Real.sqrt (1 + |u|) / (1 + |u|) ^ 2) := by dsimp [Cdom]; ring
    _ = Cdom * (1 + |u|) ^ (-(3 / 2 : ℝ)) := by rw [hrpow]

end ZeroSummabilityAndQuarterIntegrability

section ContourShiftAndExplicitFormula

/-- Exhaustion limit for a summable series: if `Z j` eventually contains every finite subset
of the support of `f`, then `∑ x ∈ Z j, f x → ∑' x, f x`. -/
private lemma tendsto_sum_of_exhaustion {α : Type*} {f : α → ℂ} (hf : Summable f)
    {Z : ℕ → Finset α}
    (hexh : ∀ s : Finset α, ∀ᶠ j in atTop, ∀ x ∈ s, f x ≠ 0 → x ∈ Z j) :
    Tendsto (fun j => ∑ x ∈ Z j, f x) atTop (𝓝 (∑' x, f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hhas : Tendsto (fun s : Finset α => ∑ b ∈ s, f b) atTop (𝓝 (∑' x, f x)) := hf.hasSum
  rw [Metric.tendsto_atTop] at hhas
  obtain ⟨s₀, hs₀⟩ := hhas ε hε
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hexh s₀)
  refine ⟨J, fun j hj => ?_⟩
  let s₁ : Finset α := Z j ∪ s₀
  have hs₁_eq : ∑ x ∈ s₁, f x = ∑ x ∈ Z j, f x :=
    (Finset.sum_subset Finset.subset_union_left fun x hx hnot => by
      have hxs₀ : x ∈ s₀ := (Finset.mem_union.mp hx).resolve_left hnot
      by_contra hne
      exact hnot (hJ j hj x hxs₀ hne)).symm
  rw [← hs₁_eq]
  exact hs₀ s₁ Finset.subset_union_right

/-- Logarithmic derivative of a finite product `∏ ρ ∈ Z, (z - ρ) ^ m ρ` (local copy). -/
private lemma hasDerivAt_prod_sub_pow (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ)
    (hs : ∀ ρ ∈ Z, s ≠ ρ) :
    HasDerivAt (fun z : ℂ => ∏ ρ ∈ Z, (z - ρ) ^ m ρ)
      ((∏ ρ ∈ Z, (s - ρ) ^ m ρ) * ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)) s := by
  induction Z using Finset.cons_induction with
  | empty =>
    simpa using hasDerivAt_const s (1 : ℂ)
  | cons a S ha ih =>
    have hsa : s ≠ a := hs a (Finset.mem_cons_self a S)
    have ih' := ih fun ρ hρ => hs ρ (Finset.mem_cons_of_mem hρ)
    have hfac : HasDerivAt (fun z : ℂ => (z - a) ^ m a) ((m a : ℂ) * (s - a) ^ (m a - 1)) s := by
      simpa using ((hasDerivAt_id s).sub_const a).fun_pow (m a)
    have hmul := hfac.fun_mul ih'
    have hfun : (fun z : ℂ => ∏ ρ ∈ Finset.cons a S ha, (z - ρ) ^ m ρ) =
        fun z => (z - a) ^ m a * ∏ ρ ∈ S, (z - ρ) ^ m ρ := by
      ext z; exact Finset.prod_cons ha
    rw [hfun]
    refine hmul.congr_deriv ?_
    rw [Finset.prod_cons ha, Finset.sum_cons ha]
    have hsa0 : s - a ≠ 0 := sub_ne_zero.mpr hsa
    cases m a with
    | zero => simp
    | succ k => simp only [Nat.add_sub_cancel, pow_succ]; field_simp [hsa0]

/-- Finite-rectangle contour identity at a good height `T ≥ 2`. -/
private lemma rect_kernel_contour_identity (hGRH : DirichletGRH) {d : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) (F : ℂ → ℂ)
    (hF_diff_U : DifferentiableOn ℂ F {s : ℂ | 0 < s.re})
    {T : ℝ} (hT : 2 ≤ T)
    (hno_zero : ∀ s : ℂ, 0 < s.re → (s.im = T ∨ s.im = -T) → entireL χ s ≠ 0) :
    rectIntegral (fun s => F s * negLogDerivL χ s)
      ((1 : ℝ) / 4) 2 (-T) T =
    2 * (Real.pi : ℂ) * Complex.I *
      ((if χ = 1 then F 1 else 0) -
        ∑ ρ ∈ (diskZeros χ 2 (T + 2)).filter
          (fun ρ => 0 < ρ.re ∧ -T < ρ.im ∧ ρ.im < T),
          kernelZeroTerm χ F ρ) := by
  set Z_big : Finset ℂ := diskZeros χ 2 (T + 2)
  set Z_in : Finset ℂ := Z_big.filter fun ρ => 0 < ρ.re ∧ -T < ρ.im ∧ ρ.im < T
  set Z_out : Finset ℂ := Z_big.filter fun ρ => ¬(0 < ρ.re ∧ -T < ρ.im ∧ ρ.im < T)
  set Rbox : Set ℂ := Icc ((1 : ℝ) / 4) 2 ×ℂ Icc (-T) T
  have hR_sub_ball : Rbox ⊆ closedBall (2 : ℂ) (T + 2) := by
    intro s hs
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hre : |s.re - 2| ≤ 7 / 4 := by rw [abs_le]; constructor <;> linarith only [hs.1.1, hs.1.2]
    have him : |s.im| ≤ T := abs_le.mpr hs.2
    have hsq : ‖s - 2‖ ^ 2 ≤ (T + 2) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have h1 : (s - 2).re = s.re - 2 := by simp
      have h2 : (s - 2).im = s.im := by simp
      rw [h1, h2]
      have ha : (s.re - 2) ^ 2 ≤ (7 / 4 : ℝ) ^ 2 := by nlinarith only [(abs_le.mp hre).1, (abs_le.mp hre).2]
      have hb : s.im ^ 2 ≤ T ^ 2 := by nlinarith only [(abs_le.mp him).1, (abs_le.mp him).2]
      nlinarith only [ha, hb, hT]
    have hnn : 0 ≤ ‖s - 2‖ := norm_nonneg _
    nlinarith only [hsq, hnn, hT]
  obtain ⟨g, hg_diff, hg_ne, hfac⟩ := extract_zeros_on_closedBall χ 2 (T + 2)
  -- Check that every `ρ ∈ Z_in` lies strictly inside `(1/4, 2) × (-T, T)` and `ρ ≠ 1`.
  have hZin_strict : ∀ ρ ∈ Z_in,
      (1 : ℝ) / 4 < ρ.re ∧ ρ.re < 2 ∧ -T < ρ.im ∧ ρ.im < T := by
    intro ρ hρ
    obtain ⟨hbig, hre, hlo, hhi⟩ := Finset.mem_filter.mp hρ
    have h0 := ((mem_diskZeros_iff χ).mp hbig).2
    have hhalf := entireL_re_eq_half_of_eq_zero hGRH hprim hre h0
    exact ⟨by linarith only [hhalf], by linarith only [hhalf], hlo, hhi⟩
  have h1_not_Zin : (1 : ℂ) ∉ Z_in := by
    intro hmem
    have hbig := (Finset.mem_filter.mp hmem).1
    have h0 := ((mem_diskZeros_iff χ).mp hbig).2
    have hhalf := entireL_re_eq_half_of_eq_zero hGRH hprim (by simp) h0
    norm_num at hhalf
  -- Check that every `ρ ∈ Z_out` lies outside `Rbox`.
  have hZout_disj : ∀ ρ ∈ Z_out, ρ ∉ Rbox := by
    intro ρ hρ hmem
    obtain ⟨hbig, hnot⟩ := Finset.mem_filter.mp hρ
    have h0 := ((mem_diskZeros_iff χ).mp hbig).2
    have hre_pos : 0 < ρ.re := by linarith only [hmem.1.1]
    have hne_top : ρ.im ≠ T := fun h => hno_zero ρ hre_pos (Or.inl h) h0
    have hne_bot : ρ.im ≠ -T := fun h => hno_zero ρ hre_pos (Or.inr h) h0
    have hlo : -T < ρ.im := lt_of_le_of_ne hmem.2.1 hne_bot.symm
    have hhi : ρ.im < T := lt_of_le_of_ne hmem.2.2 hne_top
    exact hnot ⟨hre_pos, hlo, hhi⟩
  -- Define pole set `P` and residues `res`.
  let P : Finset ℂ := if χ = 1 then insert (1 : ℂ) Z_in else Z_in
  let res : ℂ → ℂ := fun p =>
    if p = 1 then (if χ = 1 then F 1 else 0) else -((zeroMult χ p : ℂ) * F p)
  have hP_strict : ∀ p ∈ P, (1 : ℝ) / 4 < p.re ∧ p.re < 2 ∧ -T < p.im ∧ p.im < T := by
    intro p hp
    dsimp [P] at hp
    split_ifs at hp with h1
    · rcases Finset.mem_insert.mp hp with rfl | hZ
      · exact ⟨by norm_num, by norm_num, by simp; linarith only [hT], by simp; linarith only [hT]⟩
      · exact hZin_strict p hZ
    · exact hZin_strict p hp
  -- Holomorphic remainder `H` using `dslope F`.
  let H : ℂ → ℂ := fun s =>
    (if χ = 1 then dslope F 1 s else 0) -
    (∑ ρ ∈ Z_in, (zeroMult χ ρ : ℂ) * dslope F ρ s) -
    F s * (∑ ρ ∈ Z_out, (zeroMult χ ρ : ℂ) / (s - ρ)) -
    F s * (deriv g s / g s)
  have hU_open : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hR_sub_U : Rbox ⊆ {s : ℂ | 0 < s.re} := fun s hs => by
    show 0 < s.re
    have h1 : (1 : ℝ) / 4 ≤ s.re := (Complex.mem_reProdIm.mp hs).1.1
    linarith only [h1]
  have hF_diff_R : DifferentiableOn ℂ F Rbox := hF_diff_U.mono hR_sub_U
  have hH_diff : DifferentiableOn ℂ H Rbox := by
    have h1 : DifferentiableOn ℂ (fun s => if χ = 1 then dslope F 1 s else 0) Rbox := by
      by_cases hχ : χ = 1
      · simp only [hχ, ↓reduceIte]
        have hd1 : DifferentiableOn ℂ (dslope F 1) {s : ℂ | 0 < s.re} :=
          (Complex.differentiableOn_dslope (hU_open.mem_nhds (by show 0 < (1 : ℂ).re; norm_num))).mpr hF_diff_U
        exact hd1.mono hR_sub_U
      · simp only [hχ, ↓reduceIte]; exact differentiableOn_const 0
    have h2 : DifferentiableOn ℂ (fun s => ∑ ρ ∈ Z_in, (zeroMult χ ρ : ℂ) * dslope F ρ s) Rbox := by
      refine DifferentiableOn.fun_sum fun ρ hρ => ?_
      have hρ_U : ρ ∈ {s : ℂ | 0 < s.re} := by
        show 0 < ρ.re; linarith only [(hZin_strict ρ hρ).1]
      have hdρ : DifferentiableOn ℂ (dslope F ρ) {s : ℂ | 0 < s.re} :=
        (Complex.differentiableOn_dslope (hU_open.mem_nhds hρ_U)).mpr hF_diff_U
      exact (differentiableOn_const _).fun_mul (hdρ.mono hR_sub_U)
    have h3 : DifferentiableOn ℂ (fun s => F s * ∑ ρ ∈ Z_out, (zeroMult χ ρ : ℂ) / (s - ρ)) Rbox := by
      refine hF_diff_R.fun_mul (DifferentiableOn.fun_sum fun ρ hρ => ?_)
      refine (differentiableOn_const _).fun_div (differentiableOn_id.fun_sub (differentiableOn_const ρ)) fun s hs => ?_
      exact sub_ne_zero.mpr fun h => hZout_disj ρ hρ (h ▸ hs)
    have h4 : DifferentiableOn ℂ (fun s => F s * (deriv g s / g s)) Rbox :=
      hF_diff_R.fun_mul
        ((hg_diff.deriv.differentiableOn.mono (subset_univ Rbox)).fun_div
          (hg_diff.differentiableOn.mono (subset_univ Rbox))
          fun s hs => hg_ne s (hR_sub_ball hs))
    exact ((h1.fun_sub h2).fun_sub h3).fun_sub h4
  -- Show `F s * negLogDerivL χ s = H s + ∑ p ∈ P, res p * (s - p)⁻¹` at any `s ∈ Rbox` avoiding `P` and zeros.
  have hdecomp : ∀ s ∈ Rbox, s ≠ 1 → entireL χ s ≠ 0 →
      F s * negLogDerivL χ s = H s + ∑ p ∈ P, res p * (s - p)⁻¹ := by
    intro s hs hs1 hFs_ne
    have hLs_ne : χ.LFunction s ≠ 0 := fun h0 => by
      apply hFs_ne; rw [entireL_apply_of_ne_one χ hs1, h0]; split_ifs <;> simp
    have hs_ne_Zbig : ∀ ρ ∈ Z_big, s ≠ ρ := fun ρ hρ h => hFs_ne (h ▸ ((mem_diskZeros_iff χ).mp hρ).2)
    have hF_logd : deriv (entireL χ) s / entireL χ s =
        (∑ ρ ∈ Z_big, (zeroMult χ ρ : ℂ) / (s - ρ)) + deriv g s / g s := by
      have hP_der := hasDerivAt_prod_sub_pow Z_big (zeroMult χ) s hs_ne_Zbig
      have hmul_der := hP_der.fun_mul (hg_diff s).hasDerivAt
      have hfun : entireL χ = fun z => (∏ ρ ∈ Z_big, (z - ρ) ^ zeroMult χ ρ) * g z := funext hfac
      have hder_eq : deriv (entireL χ) s =
          (∏ ρ ∈ Z_big, (s - ρ) ^ zeroMult χ ρ) * (∑ ρ ∈ Z_big, (zeroMult χ ρ : ℂ) / (s - ρ)) * g s +
            (∏ ρ ∈ Z_big, (s - ρ) ^ zeroMult χ ρ) * deriv g s := by
        rw [hfun]; exact hmul_der.deriv
      have hPs_ne : (∏ ρ ∈ Z_big, (s - ρ) ^ zeroMult χ ρ) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr (hs_ne_Zbig ρ hρ))
      have hgs_ne : g s ≠ 0 := hg_ne s (hR_sub_ball hs)
      have hfac_s : entireL χ s = (∏ ρ ∈ Z_big, (s - ρ) ^ zeroMult χ ρ) * g s := hfac s
      rw [hder_eq, hfac_s]
      field_simp [hPs_ne, hgs_ne]
    have hsplit : (∑ ρ ∈ Z_big, (zeroMult χ ρ : ℂ) / (s - ρ)) =
        (∑ ρ ∈ Z_in, (zeroMult χ ρ : ℂ) / (s - ρ)) +
        (∑ ρ ∈ Z_out, (zeroMult χ ρ : ℂ) / (s - ρ)) :=
      (Finset.sum_filter_add_sum_filter_not Z_big _ _).symm
    have hD_eq : negLogDerivL χ s =
        (if χ = 1 then (1 : ℂ) / (s - 1) else 0) -
        (∑ ρ ∈ Z_in, (zeroMult χ ρ : ℂ) / (s - ρ)) -
        (∑ ρ ∈ Z_out, (zeroMult χ ρ : ℂ) / (s - ρ)) -
        deriv g s / g s := by
      rw [negLogDerivL_eq_of_ne_one χ hs1 hLs_ne, hF_logd, hsplit]; ring
    have hsumP : (∑ p ∈ P, res p * (s - p)⁻¹) =
        (if χ = 1 then F 1 * (s - 1)⁻¹ else 0) -
        ∑ ρ ∈ Z_in, (zeroMult χ ρ : ℂ) * F ρ * (s - ρ)⁻¹ := by
      have hZin_sum : (∑ ρ ∈ Z_in, res ρ * (s - ρ)⁻¹) =
          -(∑ ρ ∈ Z_in, (zeroMult χ ρ : ℂ) * F ρ * (s - ρ)⁻¹) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun ρ hρ => ?_
        have hρ1 : ρ ≠ 1 := fun h => h1_not_Zin (h ▸ hρ)
        dsimp [res]; simp only [hρ1, ↓reduceIte]; ring
      dsimp [P]
      split_ifs with h1
      · rw [Finset.sum_insert h1_not_Zin, hZin_sum]
        dsimp [res]; simp only [↓reduceIte, h1]; ring
      · rw [hZin_sum]; ring
    have hdslope_1 : (if χ = 1 then dslope F 1 s else 0) + (if χ = 1 then F 1 * (s - 1)⁻¹ else 0) =
        F s * (if χ = 1 then (1 : ℂ) / (s - 1) else 0) := by
      split_ifs
      · rw [dslope_of_ne F hs1, slope_def_field]
        have hs10 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
        field_simp [hs10]
        ring
      · simp
    have hdslope_Zin :
        -(∑ ρ ∈ Z_in, (zeroMult χ ρ : ℂ) * dslope F ρ s) -
          (∑ ρ ∈ Z_in, (zeroMult χ ρ : ℂ) * F ρ * (s - ρ)⁻¹) =
        -(F s * ∑ ρ ∈ Z_in, (zeroMult χ ρ : ℂ) / (s - ρ)) := by
      rw [Finset.mul_sum, sub_eq_add_neg, ← neg_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      have hsρ : s ≠ ρ := hs_ne_Zbig ρ (Finset.mem_filter.mp hρ).1
      rw [dslope_of_ne F hsρ, slope_def_field]
      have hsρ0 : s - ρ ≠ 0 := sub_ne_zero.mpr hsρ
      field_simp [hsρ0]
      ring
    rw [hD_eq, hsumP]
    dsimp [H]
    linear_combination -hdslope_1 - hdslope_Zin
  -- Apply `rectIntegral_eq_sum_simple_poles`.
  have hres_sum : (∑ p ∈ P, res p) =
      (if χ = 1 then F 1 else 0) - ∑ ρ ∈ Z_in, kernelZeroTerm χ F ρ := by
    have hZin_sum : (∑ ρ ∈ Z_in, res ρ) = -(∑ ρ ∈ Z_in, kernelZeroTerm χ F ρ) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      have hρ1 : ρ ≠ 1 := fun h => h1_not_Zin (h ▸ hρ)
      obtain ⟨hbig, hre, _, _⟩ := Finset.mem_filter.mp hρ
      have h0 := ((mem_diskZeros_iff χ).mp hbig).2
      dsimp [res]; unfold kernelZeroTerm
      simp only [hρ1, ↓reduceIte, hre, h0, and_self]
    dsimp [P]
    split_ifs with h1
    · rw [Finset.sum_insert h1_not_Zin, hZin_sum]
      dsimp [res]; simp only [↓reduceIte, h1]; ring
    · rw [hZin_sum]; ring
  rw [← hres_sum]
  refine rectIntegral_eq_sum_simple_poles (by norm_num) (by linarith only [hT]) P res hP_strict hH_diff
    ?_ ?_ ?_ ?_
  · intro x hx
    set s : ℂ := (x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I
    refine hdecomp s (Complex.mem_reProdIm.mpr ⟨by simpa [s] using hx,
        by simpa [s] using left_mem_Icc.mpr (by linarith only [hT] : -T ≤ T)⟩)
      (fun h => by have := congrArg Complex.im h; simp [s] at this; linarith only [this, hT])
      (hno_zero s (by simp [s]; linarith only [hx.1]) (Or.inr (by simp [s])))
  · intro x hx
    set s : ℂ := (x : ℂ) + (T : ℂ) * Complex.I
    refine hdecomp s (Complex.mem_reProdIm.mpr ⟨by simpa [s] using hx,
        by simpa [s] using right_mem_Icc.mpr (by linarith only [hT] : -T ≤ T)⟩)
      (fun h => by have := congrArg Complex.im h; simp [s] at this; linarith only [this, hT])
      (hno_zero s (by simp [s]; linarith only [hx.1]) (Or.inl (by simp [s])))
  · intro y hy
    set s : ℂ := (2 : ℂ) + (y : ℂ) * Complex.I
    refine hdecomp s (Complex.mem_reProdIm.mpr ⟨by simpa [s] using right_mem_Icc.mpr (by norm_num : (1 : ℝ) / 4 ≤ 2),
        by simpa [s] using hy⟩)
      (fun h => by have := congrArg Complex.re h; simp [s] at this)
      (entireL_two_add_ne_zero χ y)
  · intro y hy
    set s : ℂ := ((1 / 4 : ℝ) : ℂ) + (y : ℂ) * Complex.I
    refine hdecomp s (Complex.mem_reProdIm.mpr ⟨by simpa [s] using left_mem_Icc.mpr (by norm_num : (1 : ℝ) / 4 ≤ 2),
        by simpa [s] using hy⟩)
      (fun h => by have := congrArg Complex.re h; simp [s] at this)
      (fun h0 => by
        have := entireL_re_eq_half_of_eq_zero hGRH hprim (by simp [s]) h0
        simp [s] at this)

/-- Shift an analytic kernel from the right vertical line to the quarter-line,
taking the pole at one and all zeros in the positive half-plane. -/
theorem primitive_kernel_contour_shift (hGRH : DirichletGRH) {d : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) (K : ℂ → ℂ)
    (hK_diff : DifferentiableOn ℂ K {s : ℂ | 0 < s.re})
    (hright : Integrable (fun u : ℝ => K (2 + (u : ℂ) * Complex.I) *
      negLogDerivL χ (2 + (u : ℂ) * Complex.I)))
    (hleft : Integrable (fun u : ℝ => K ((1/4 : ℝ) + (u : ℂ) * Complex.I) *
      negLogDerivL χ ((1/4 : ℝ) + (u : ℂ) * Complex.I)))
    (hzeros : Summable (kernelZeroTerm χ K))
    (hhorizontal : ∃ A R : ℝ, 0 ≤ A ∧
      ∀ σ ∈ Icc ((1 : ℝ)/4) 2, ∀ u : ℝ, R ≤ |u| →
        ‖K ((σ : ℂ) + (u : ℂ) * Complex.I)‖ ≤ A/(1+|u|)^2) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ u : ℝ, K (2 + (u : ℂ) * Complex.I) * negLogDerivL χ (2 + (u : ℂ) * Complex.I)) =
      (if χ = 1 then K 1 else 0) - (∑' ρ : ℂ, kernelZeroTerm χ K ρ) +
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ u : ℝ, K ((1/4 : ℝ) + (u : ℂ) * Complex.I) *
          negLogDerivL χ ((1/4 : ℝ) + (u : ℂ) * Complex.I) := by
  -- Choose a sequence of good heights `T j ∈ [j + 2, j + 3]`.
  have hchoose : ∀ j : ℕ, ∃ T ∈ Icc ((j + 2 : ℕ) : ℝ) ((j + 2 : ℕ) + 1),
      (∀ s : ℂ, 0 < s.re → (s.im = T ∨ s.im = -T) → entireL χ s ≠ 0) ∧
      (∀ σ ∈ Icc ((1 : ℝ) / 4) 2,
        ‖negLogDerivL χ ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤
          4000000 * (Real.log (2 * (d : ℝ) * (2 + T))) ^ 2 ∧
        ‖negLogDerivL χ ((σ : ℂ) + (-T : ℂ) * Complex.I)‖ ≤
          4000000 * (Real.log (2 * (d : ℝ) * (2 + T))) ^ 2) :=
    fun j => exists_good_height hGRH hprim (show 2 ≤ j + 2 by omega)
  choose T hT_mem hT_nozero hT_bd using hchoose
  have hT_ge2 : ∀ j : ℕ, (2 : ℝ) ≤ T j := fun j => by
    have h1 := (hT_mem j).1
    have h2 : (2 : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ j + 2 by omega)
    linarith only [h1, h2]
  have hT_top : Tendsto T atTop atTop :=
    tendsto_atTop_mono (fun j => by
      have h1 := (hT_mem j).1
      have h2 : (j : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by exact_mod_cast (show j ≤ j + 2 by omega)
      linarith only [h1, h2]) tendsto_natCast_atTop_atTop
  have hnegT_bot : Tendsto (fun j => -T j) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hT_top
  set G : ℂ → ℂ := fun s => K s * negLogDerivL χ s
  set Zbox : ℕ → Finset ℂ := fun j =>
    (diskZeros χ 2 (T j + 2)).filter fun ρ => 0 < ρ.re ∧ -(T j) < ρ.im ∧ ρ.im < T j
  -- Rewrite the finite rectangle identity at height `T j`.
  have h2pi_ne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hstep : ∀ j : ℕ,
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ u in (-T j)..(T j), G (2 + (u : ℂ) * Complex.I)) =
      (if χ = 1 then K 1 else 0) -
      (∑ ρ ∈ Zbox j, kernelZeroTerm χ K ρ) +
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ u in (-T j)..(T j), G ((1 / 4 : ℝ) + (u : ℂ) * Complex.I)) -
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ((∫ σ in ((1 : ℝ) / 4)..2, G ((σ : ℂ) + ((-T j : ℝ) : ℂ) * Complex.I)) -
         (∫ σ in ((1 : ℝ) / 4)..2, G ((σ : ℂ) + (T j : ℂ) * Complex.I))) := by
    intro j
    have hid :
        (∫ σ in ((1 : ℝ) / 4)..2, G ((σ : ℂ) + ((-T j : ℝ) : ℂ) * Complex.I)) -
        (∫ σ in ((1 : ℝ) / 4)..2, G ((σ : ℂ) + (T j : ℂ) * Complex.I)) +
        Complex.I * (∫ u in (-T j)..(T j), G (2 + (u : ℂ) * Complex.I)) -
        Complex.I * (∫ u in (-T j)..(T j), G ((1 / 4 : ℝ) + (u : ℂ) * Complex.I)) =
        2 * (Real.pi : ℂ) * Complex.I *
          ((if χ = 1 then K 1 else 0) -
            ∑ ρ ∈ Zbox j, kernelZeroTerm χ K ρ) :=
      rect_kernel_contour_identity hGRH hprim K hK_diff (hT_ge2 j) (hT_nozero j)
    have hdiv := congrArg (fun z => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * z) hid
    simp only [inv_mul_cancel_left₀ h2pi_ne] at hdiv
    have hcoef : (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * Complex.I = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
      push_cast; field_simp [Complex.I_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    rw [mul_sub, mul_add, mul_sub, ← mul_assoc, ← mul_assoc, hcoef] at hdiv
    linear_combination hdiv
  have hlim_right := (intervalIntegral_tendsto_integral hright hnegT_bot hT_top).const_mul
    (((1 / (2 * Real.pi) : ℝ) : ℂ))
  -- Limit 2: Left vertical line tends to `(1/(2π)) ∫_ℝ G(1/4 + iu) du`.
  have hlim_left : Tendsto
      (fun j => ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ u in (-T j)..(T j), G ((1 / 4 : ℝ) + (u : ℂ) * Complex.I)))
      atTop (𝓝 (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ u : ℝ, G ((1 / 4 : ℝ) + (u : ℂ) * Complex.I))) :=
    (intervalIntegral_tendsto_integral (hleft) hnegT_bot hT_top).const_mul _
  -- Limit 3: Zero sum over `Zbox j` tends to `∑' ρ, kernelZeroTerm χ K ρ`.
  have hlim_zeros : Tendsto (fun j => ∑ ρ ∈ Zbox j, kernelZeroTerm χ K ρ)
      atTop (𝓝 (∑' ρ : ℂ, kernelZeroTerm χ K ρ)) := by
    refine tendsto_sum_of_exhaustion hzeros fun s => ?_
    let M_s : ℝ := (∑ ρ ∈ s, |ρ.im|) + 1
    filter_upwards [hT_top.eventually_gt_atTop M_s] with j hj ρ hρs hne
    have hcond : 0 < ρ.re ∧ entireL χ ρ = 0 := by
      by_contra hnot; apply hne; unfold kernelZeroTerm; simp only [hnot, ↓reduceIte]
    have hρ_im_lt : |ρ.im| < T j := by
      have hle : |ρ.im| ≤ ∑ w ∈ s, |w.im| :=
        Finset.single_le_sum (f := fun w : ℂ => |w.im|) (fun _ _ => abs_nonneg _) hρs
      linarith only [hle, hj]
    have hhalf := entireL_re_eq_half_of_eq_zero hGRH hprim hcond.1 hcond.2
    have hball : ρ ∈ closedBall (2 : ℂ) (T j + 2) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hsq : ‖ρ - 2‖ ^ 2 ≤ (T j + 2) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        have h1 : (ρ - 2).re = -3 / 2 := by simp [hhalf]; norm_num
        have h2 : (ρ - 2).im = ρ.im := by simp
        rw [h1, h2]
        have him2 : ρ.im ^ 2 ≤ (T j) ^ 2 := by
          nlinarith only [(abs_lt.mp hρ_im_lt).1, (abs_lt.mp hρ_im_lt).2]
        nlinarith only [him2, hT_ge2 j]
      have hnn : 0 ≤ ‖ρ - 2‖ := norm_nonneg _
      nlinarith only [hsq, hnn, hT_ge2 j]
    exact Finset.mem_filter.mpr
      ⟨(mem_diskZeros_iff χ).mpr ⟨hball, hcond.2⟩, hcond.1, (abs_lt.mp hρ_im_lt).1, (abs_lt.mp hρ_im_lt).2⟩
  -- Limit 4: Horizontal edges tend to `0`.
  have hhoriz_zero : ∀ sgn : Bool,
      Tendsto (fun j => ∫ σ in ((1 : ℝ) / 4)..2,
        G ((σ : ℂ) + ((if sgn then T j else -T j : ℝ) : ℂ) * Complex.I)) atTop (𝓝 0) := by
    intro sgn
    have hClog_pos : 0 < Real.log (2 * (d : ℝ)) + 4 := by
      have hd : (1 : ℝ) ≤ d := Nat.one_le_cast.mpr (NeZero.pos d)
      have : 0 ≤ Real.log (2 * (d : ℝ)) := Real.log_nonneg (by linarith only [hd])
      linarith only [this]
    obtain ⟨A, R, hA, hdecay⟩ := hhorizontal
    set C_h : ℝ := (7 / 4 : ℝ) * A * 4000000 * (Real.log (2 * (d : ℝ)) + 4) ^ 2
    have hbound : ∀ᶠ j in atTop,
        ‖∫ σ in ((1 : ℝ) / 4)..2,
          G ((σ : ℂ) + ((if sgn then T j else -T j : ℝ) : ℂ) * Complex.I)‖ ≤
          C_h / (1 + T j) := by
      filter_upwards [hT_top.eventually_ge_atTop R] with j hj
      have hT_nn : 0 ≤ T j := by linarith only [hT_ge2 j]
      have hτ_abs : |if sgn then T j else -T j| = T j := by
        cases sgn <;> simp [abs_of_nonneg hT_nn]
      have hlog_le : Real.log (2 * (d : ℝ) * (2 + T j)) ≤
          (Real.log (2 * (d : ℝ)) + 4) * Real.sqrt (1 + T j) := by
        have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
        rw [Real.log_mul (by positivity) (by positivity)]
        have h1 := log_two_add_le_two_sqrt hT_nn
        have hsqrt4 : Real.sqrt 4 = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two]
        have h2 : Real.sqrt (2 + T j) ≤ 2 * Real.sqrt (1 + T j) := by
          calc Real.sqrt (2 + T j) ≤ Real.sqrt (4 * (1 + T j)) :=
                Real.sqrt_le_sqrt (by linarith only [hT_nn])
            _ = 2 * Real.sqrt (1 + T j) := by rw [Real.sqrt_mul (by norm_num), hsqrt4]
        have hsq1 : (1 : ℝ) ≤ Real.sqrt (1 + T j) := by
          rw [Real.le_sqrt zero_le_one (by positivity)]; linarith only [hT_nn]
        have hlog2d : 0 ≤ Real.log (2 * (d : ℝ)) := Real.log_nonneg (by
          have hd : (1 : ℝ) ≤ d := Nat.one_le_cast.mpr (NeZero.pos d); linarith only [hd])
        nlinarith only [h1, h2, hsq1, hlog2d]
      have hlog_sq : (Real.log (2 * (d : ℝ) * (2 + T j))) ^ 2 ≤
          (Real.log (2 * (d : ℝ)) + 4) ^ 2 * (1 + T j) := by
        have hlog_nn : 0 ≤ Real.log (2 * (d : ℝ) * (2 + T j)) := by
          have := one_le_log_two_mul_d_mul d (T j)
          rw [abs_of_nonneg hT_nn] at this; linarith only [this]
        have hsq := pow_le_pow_left₀ hlog_nn hlog_le 2
        rw [mul_pow, Real.sq_sqrt (by positivity)] at hsq
        exact hsq
      have hpt : ∀ σ ∈ uIoc ((1 : ℝ) / 4) 2,
          ‖G ((σ : ℂ) + ((if sgn then T j else -T j : ℝ) : ℂ) * Complex.I)‖ ≤
            A * 4000000 * (Real.log (2 * (d : ℝ)) + 4) ^ 2 / (1 + T j) := by
        intro σ hσ
        rw [Set.uIoc_of_le (by norm_num)] at hσ
        have hσ_Icc : σ ∈ Icc ((1 : ℝ) / 4) 2 := ⟨hσ.1.le, hσ.2⟩
        dsimp [G]
        rw [norm_mul]
        have hker := hdecay σ hσ_Icc (if sgn then T j else -T j) (by rwa [hτ_abs])
        rw [hτ_abs] at hker
        have hD : ‖negLogDerivL χ ((σ : ℂ) + ((if sgn then T j else -T j : ℝ) : ℂ) * Complex.I)‖ ≤
            4000000 * (Real.log (2 * (d : ℝ) * (2 + T j))) ^ 2 := by
          cases sgn
          · simpa using (hT_bd j σ hσ_Icc).2
          · simpa using (hT_bd j σ hσ_Icc).1
        calc _ ≤ (A / (1 + T j)^2) *
              (4000000 * ((Real.log (2 * (d : ℝ)) + 4)^2 * (1 + T j))) := by
                exact mul_le_mul hker
                  (hD.trans (mul_le_mul_of_nonneg_left hlog_sq (by norm_num)))
                  (norm_nonneg _) (by positivity)
          _ = A * 4000000 * (Real.log (2 * (d : ℝ)) + 4)^2 / (1 + T j) := by
                have hpos : 1 + T j ≠ 0 := by linarith only [hT_nn]
                field_simp [hpos]
      have hlen : |(2 : ℝ) - 1 / 4| = 7 / 4 := by norm_num
      have hint_le := intervalIntegral.norm_integral_le_of_norm_le_const hpt
      rw [hlen] at hint_le
      calc ‖∫ σ in ((1 : ℝ) / 4)..2,
            G ((σ : ℂ) + ((if sgn then T j else -T j : ℝ) : ℂ) * Complex.I)‖
          ≤ (A * 4000000 * (Real.log (2 * (d : ℝ)) + 4) ^ 2 / (1 + T j)) * (7 / 4) := hint_le
        _ = C_h / (1 + T j) := by dsimp [C_h]; ring
    have htend_rhs : Tendsto (fun j => C_h / (1 + T j)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun j => 1 + T j) atTop atTop := tendsto_atTop_add_const_left atTop 1 hT_top
      simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp h1).const_mul C_h
    exact tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound htend_rhs)
  have hlim_rhs : Tendsto
      (fun j =>
        (if χ = 1 then K 1 else 0) -
        (∑ ρ ∈ Zbox j, kernelZeroTerm χ K ρ) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ u in (-T j)..(T j), G ((1 / 4 : ℝ) + (u : ℂ) * Complex.I)) -
        (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ((∫ σ in ((1 : ℝ) / 4)..2, G ((σ : ℂ) + ((-T j : ℝ) : ℂ) * Complex.I)) -
           (∫ σ in ((1 : ℝ) / 4)..2, G ((σ : ℂ) + (T j : ℂ) * Complex.I))))
      atTop
      (𝓝 ((if χ = 1 then K 1 else 0) -
        (∑' ρ : ℂ, kernelZeroTerm χ K ρ) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ u : ℝ, G ((1 / 4 : ℝ) + (u : ℂ) * Complex.I))) := by
    have hbot : Tendsto (fun j => ∫ σ in ((1 : ℝ) / 4)..2, G ((σ : ℂ) + ((-T j : ℝ) : ℂ) * Complex.I))
        atTop (𝓝 0) := by simpa using hhoriz_zero false
    have htop : Tendsto (fun j => ∫ σ in ((1 : ℝ) / 4)..2, G ((σ : ℂ) + (T j : ℂ) * Complex.I))
        atTop (𝓝 0) := by simpa using hhoriz_zero true
    have herr : Tendsto (fun j => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ((∫ σ in ((1 : ℝ) / 4)..2, G ((σ : ℂ) + ((-T j : ℝ) : ℂ) * Complex.I)) -
         (∫ σ in ((1 : ℝ) / 4)..2, G ((σ : ℂ) + (T j : ℂ) * Complex.I))))
        atTop (𝓝 0) := by
      simpa using (hbot.sub htop).const_mul (2 * (Real.pi : ℂ) * Complex.I)⁻¹
    simpa only [sub_zero] using (((tendsto_const_nhds.sub hlim_zeros).add hlim_left).sub herr)
  exact tendsto_nhds_unique hlim_right (hlim_rhs.congr fun j => (hstep j).symm)

/-- **Module A3 Main Theorem (`primitive_smoothed_explicit_formula`)**:
Under `DirichletGRH`, for every primitive Dirichlet character `χ mod d`, `Y ≥ 2`, and `t : ℝ`,
```
∑_{n=1}^Y Λ(n) χ(n) w(n/Y) e(t n)
  = 1_{χ=1} f̃(1) - ∑'_ρ m_ρ f̃(ρ) + (1 / (2π)) ∫_ℝ f̃(1/4 + iu) (-L'/L)(1/4 + iu, χ) du.
``` -/
theorem primitive_smoothed_explicit_formula (hGRH : DirichletGRH) {d : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) {Y : ℕ} (hY : 2 ≤ Y) (t : ℝ) :
    (∑ n ∈ Finset.Icc 1 Y,
      (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod d) *
        scaledTiltedBump Y t (n : ℝ)) =
      (if χ = 1 then mellin (scaledTiltedBump Y t) 1 else 0) -
      (∑' ρ : ℂ, zeroTerm χ Y t ρ) +
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ u : ℝ, mellin (scaledTiltedBump Y t) ((1 / 4 : ℝ) + (u : ℂ) * Complex.I) *
          negLogDerivL χ ((1 / 4 : ℝ) + (u : ℂ) * Complex.I) := by
  have hY1 : 1 ≤ Y := by omega
  have hY_pos : (0 : ℝ) < (Y : ℝ) := Nat.cast_pos.mpr (by omega)
  rw [smoothedPrimeSum_eq_verticalIntegral χ hY1 t]
  apply primitive_kernel_contour_shift hGRH hprim
    (mellin (scaledTiltedBump Y t))
    (fun s hs => (differentiableAt_mellin_scaledTiltedBump hY1 (t := t)
      (by linarith only [show 0 < s.re from hs])).differentiableWithinAt)
    (integrable_two_line χ hY1 t) (integrable_quarter_line hGRH hprim hY1 t)
    (summable_zeroTerm hGRH hprim hY1 t)
  refine ⟨(Y : ℝ)^2 * 15000, 4 * Real.pi * |t*(Y:ℝ)|+2, by positivity, ?_⟩
  intro σ hσ u hu
  rw [mellin_scaledTiltedBump_eq hY1 t _, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hY_pos]
  have hre : ((σ : ℂ) + (u : ℂ)*Complex.I).re=σ := by simp
  rw [hre]
  have hYpow : (Y:ℝ)^σ ≤ (Y:ℝ)^(2:ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hY1) hσ.2
  calc _ ≤ (Y:ℝ)^2 * (15000/(1+|u|)^2) :=
        mul_le_mul hYpow (quarticKernel_norm_le_tail hσ.1 hσ.2 hu) (norm_nonneg _) (by positivity)
    _ = _ := by ring

end ContourShiftAndExplicitFormula

end FareyGoldbach
