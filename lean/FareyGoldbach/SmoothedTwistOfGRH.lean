import FareyGoldbach.PrimitiveSmoothedTwist
import FareyGoldbach.DyadicAssembly

/-!
# Module A5: Reduction to Primitive Characters & End-to-End Closure (`DirichletGRH → Target`)

This module reduces arbitrary (possibly imprimitive) Dirichlet characters `χ mod d` to their
associated primitive character `χ* = χ.primitiveCharacter` of conductor `d* ∣ d`, bounds the
finite prime-power discrepancy using Stage 1's `PrimeSums.nonCoprimeVonMangoldt_le`, deduces
`SmoothedTwistEstimate` from `DirichletGRH`, and composes with Stage 1's
`target_of_smoothedTwistEstimate` to prove the end-to-end arbitrary-modulus Goldbach theorem:
```
theorem target_of_dirichletGRH : DirichletGRH → Target
```
-/

open Real Complex Set
open scoped BigOperators Classical

namespace FareyGoldbach

section PrimitiveReduction

/-- For any Dirichlet character `χ mod d` (`d ≥ 1`), `χ` is principal iff its primitive
character `χ.primitiveCharacter` is principal. -/
lemma eq_one_iff_primitiveCharacter_eq_one {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) :
    χ = 1 ↔ χ.primitiveCharacter = 1 := by
  have : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  rw [DirichletCharacter.eq_one_iff_conductor_eq_one,
      DirichletCharacter.eq_one_iff_conductor_eq_one,
      (DirichletCharacter.isPrimitive_def _).mp χ.primitiveCharacter_isPrimitive]

/-- Discrepancy between `smoothedTiltedRemainder` for `χ mod d` and for its primitive character
`χ.primitiveCharacter`: supported exclusively on prime powers sharing a prime factor with `d`,
hence bounded by `4 * log(2d) * log Y ≤ 8 * √(Y * (1 + |t| * Y)) * log(2 * d * Y)`. -/
lemma norm_smoothedTiltedRemainder_sub_primitive_le {Y d : ℕ} [NeZero d]
    (χ : DirichletCharacter ℂ d) (t : ℝ) (hY : 2 ≤ Y) :
    ‖smoothedTiltedRemainder χ Y t - smoothedTiltedRemainder χ.primitiveCharacter Y t‖ ≤
      8 * Real.sqrt ((Y : ℝ) * (1 + |t| * (Y : ℝ))) * Real.log (2 * (d : ℝ) * (Y : ℝ)) := by
  have : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  have h1_iff := eq_one_iff_primitiveCharacter_eq_one χ
  have hind : (if χ = 1 then (1 : ℂ) else 0) = if χ.primitiveCharacter = 1 then (1 : ℂ) else 0 := by
    by_cases h : χ = 1
    · simp only [h, h1_iff.mp h, ↓reduceIte]
    · simp only [h, mt h1_iff.mpr h, ↓reduceIte]
  have hdiff_eq :
      smoothedTiltedRemainder χ Y t - smoothedTiltedRemainder χ.primitiveCharacter Y t =
      ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => ¬ Nat.Coprime n d),
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (χ (n : ZMod d) - χ.primitiveCharacter (n : ZMod χ.conductor)) *
          (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * e (t * (n : ℝ)) := by
    unfold smoothedTiltedRemainder
    rw [← Finset.sum_sub_distrib, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hind]
    by_cases hcop : Nat.Coprime n d
    · rw [ite_eq_right_iff.mpr fun h => absurd hcop h]
      have hiscop : IsCoprime (n : ℤ) (d : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
      have hchar_eq : χ.primitiveCharacter (n : ZMod χ.conductor) = χ (n : ZMod d) := by
        have h := DirichletCharacter.primitiveCharacter_apply_of_isCoprime χ hiscop
        simpa using h
      rw [hchar_eq]; ring
    · rw [ite_eq_left_iff.mpr fun h => absurd hcop h]; ring
  rw [hdiff_eq]
  have hterm_le : ∀ n ∈ (Finset.Icc 1 Y).filter (fun n => ¬ Nat.Coprime n d),
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (χ (n : ZMod d) - χ.primitiveCharacter (n : ZMod χ.conductor)) *
          (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * e (t * (n : ℝ))‖ ≤
        2 * ArithmeticFunction.vonMangoldt n := by
    intro n _
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, norm_e, mul_one,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        abs_of_nonneg (quarticBump_nonneg _)]
    have hsub_le : ‖χ (n : ZMod d) - χ.primitiveCharacter (n : ZMod χ.conductor)‖ ≤ 2 := by
      have h1 := norm_dirichletChar_le_one χ (n : ZMod d)
      have h2 := norm_dirichletChar_le_one χ.primitiveCharacter (n : ZMod χ.conductor)
      have htri := norm_sub_le (χ (n : ZMod d)) (χ.primitiveCharacter (n : ZMod χ.conductor))
      linarith only [htri, h1, h2]
    have hw_le : quarticBump ((n : ℝ) / (Y : ℝ)) ≤ 1 := quarticBump_le_one _
    have hlam_nn : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hw_nn : 0 ≤ quarticBump ((n : ℝ) / (Y : ℝ)) := quarticBump_nonneg _
    calc ArithmeticFunction.vonMangoldt n *
          ‖χ (n : ZMod d) - χ.primitiveCharacter (n : ZMod χ.conductor)‖ *
          quarticBump ((n : ℝ) / (Y : ℝ))
        ≤ ArithmeticFunction.vonMangoldt n * 2 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsub_le hlam_nn) hw_le hw_nn (by positivity)
      _ = 2 * ArithmeticFunction.vonMangoldt n := by ring
  have hsum_le :
      ‖∑ n ∈ (Finset.Icc 1 Y).filter (fun n => ¬ Nat.Coprime n d),
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (χ (n : ZMod d) - χ.primitiveCharacter (n : ZMod χ.conductor)) *
          (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * e (t * (n : ℝ))‖ ≤
        4 * Real.log (2 * (d : ℝ)) * Real.log (Y : ℝ) := by
    have hnc := nonCoprimeVonMangoldt_le Y d (by omega) (NeZero.pos d)
    calc ‖∑ n ∈ (Finset.Icc 1 Y).filter (fun n => ¬ Nat.Coprime n d),
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              (χ (n : ZMod d) - χ.primitiveCharacter (n : ZMod χ.conductor)) *
              (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * e (t * (n : ℝ))‖
        ≤ ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => ¬ Nat.Coprime n d),
            ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              (χ (n : ZMod d) - χ.primitiveCharacter (n : ZMod χ.conductor)) *
              (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * e (t * (n : ℝ))‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => ¬ Nat.Coprime n d),
            2 * ArithmeticFunction.vonMangoldt n := Finset.sum_le_sum hterm_le
      _ = 2 * ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => ¬ Nat.Coprime n d),
            ArithmeticFunction.vonMangoldt n := (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * (2 * Real.log (2 * (d : ℝ)) * Real.log (Y : ℝ)) :=
            mul_le_mul_of_nonneg_left hnc (by norm_num)
      _ = 4 * Real.log (2 * (d : ℝ)) * Real.log (Y : ℝ) := by ring
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hY2 : (2 : ℝ) ≤ Y := Nat.ofNat_le_cast.mpr hY
  have hY_pos : (0 : ℝ) < Y := by linarith only [hY2]
  have hlog2d_le : Real.log (2 * (d : ℝ)) ≤ Real.log (2 * (d : ℝ) * (Y : ℝ)) :=
    Real.log_le_log (by positivity) (by nlinarith only [hd_pos, hY2])
  have hlogY_le : Real.log (Y : ℝ) ≤ 2 * Real.sqrt ((Y : ℝ) * (1 + |t| * (Y : ℝ))) := by
    have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hY_pos)
    rw [Real.log_sqrt hY_pos.le] at h1
    have h2 : Real.sqrt (Y : ℝ) ≤ Real.sqrt ((Y : ℝ) * (1 + |t| * (Y : ℝ))) := by
      refine Real.sqrt_le_sqrt ?_
      have : 0 ≤ |t| * (Y : ℝ) := by positivity
      nlinarith only [hY_pos, this]
    linarith only [h1, h2]
  have hlog2d_nn : 0 ≤ Real.log (2 * (d : ℝ)) := Real.log_nonneg (by
    have hd1 : (1 : ℝ) ≤ d := Nat.one_le_cast.mpr (NeZero.pos d); linarith only [hd1])
  have hlogY_nn : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by linarith only [hY2])
  calc ‖∑ n ∈ (Finset.Icc 1 Y).filter (fun n => ¬ Nat.Coprime n d),
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (χ (n : ZMod d) - χ.primitiveCharacter (n : ZMod χ.conductor)) *
            (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * e (t * (n : ℝ))‖
      ≤ 4 * Real.log (2 * (d : ℝ)) * Real.log (Y : ℝ) := hsum_le
    _ ≤ 4 * Real.log (2 * (d : ℝ) * (Y : ℝ)) * (2 * Real.sqrt ((Y : ℝ) * (1 + |t| * (Y : ℝ)))) := by
        have hmul := mul_le_mul hlog2d_le hlogY_le hlogY_nn (by linarith only [hlog2d_nn, hlog2d_le])
        nlinarith only [hmul]
    _ = 8 * Real.sqrt ((Y : ℝ) * (1 + |t| * (Y : ℝ))) * Real.log (2 * (d : ℝ) * (Y : ℝ)) := by ring

/-- **Stage 2 Main Theorem (`DirichletGRH → SmoothedTwistEstimate`)**:
Dirichlet GRH implies the sharp single-logarithm smoothed twisted explicit-formula bound
for all Dirichlet characters `χ mod d` (primitive or imprimitive), `Y ≥ 2`, and `|t| ≤ 1/2`. -/
theorem smoothedTwistEstimate_of_dirichletGRH : DirichletGRH → SmoothedTwistEstimate := by
  intro hGRH
  refine ⟨600000000008, by norm_num, ?_⟩
  intro Y d _ χ t hY ht
  have : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  have hprim : χ.primitiveCharacter.IsPrimitive := χ.primitiveCharacter_isPrimitive
  have hcond_le : χ.conductor ≤ d := Nat.le_of_dvd (NeZero.pos d) χ.conductor_dvd_level
  have hprim_bd := primitive_smoothedTwist_bound hGRH hprim hY ht
  have hdiff_bd := norm_smoothedTiltedRemainder_sub_primitive_le χ t hY
  have hlog_mono : Real.log (2 * (χ.conductor : ℝ) * (Y : ℝ)) ≤ Real.log (2 * (d : ℝ) * (Y : ℝ)) := by
    have hcond_pos : (0 : ℝ) < (χ.conductor : ℝ) := Nat.cast_pos.mpr (NeZero.pos χ.conductor)
    have hY_pos : (0 : ℝ) < (Y : ℝ) := Nat.cast_pos.mpr (by omega)
    have hle : (χ.conductor : ℝ) ≤ (d : ℝ) := Nat.cast_le.mpr hcond_le
    exact Real.log_le_log (by positivity) (by nlinarith only [hle, hY_pos])
  have hprim_d : ‖smoothedTiltedRemainder χ.primitiveCharacter Y t‖ ≤
      600000000000 * Real.sqrt ((Y : ℝ) * (1 + |t| * (Y : ℝ))) * Real.log (2 * (d : ℝ) * (Y : ℝ)) :=
    hprim_bd.trans (mul_le_mul_of_nonneg_left hlog_mono (by positivity))
  have htri := norm_le_norm_sub_add (smoothedTiltedRemainder χ Y t)
    (smoothedTiltedRemainder χ.primitiveCharacter Y t)
  linarith only [htri, hdiff_bd, hprim_d]

/-- **End-to-End Main Theorem (`DirichletGRH → Target`)**:
Under Dirichlet GRH, there exists an absolute constant `C > 0` such that for EVERY `X ≥ 3`,
EVERY positive integer modulus `1 ≤ r ≤ X` (prime or composite, odd or even), and EVERY pair
of coprime residue classes `b₁, b₂ mod r`, the binary Goldbach exceptional set satisfies
```
E_r(X; b₁, b₂) ≤ C * min (X / r) ((φ(r) / r)³ * √(X * r) * log³(2 * X)).
``` -/
theorem target_of_dirichletGRH : DirichletGRH → Target :=
  fun hGRH => target_of_smoothedTwistEstimate (smoothedTwistEstimate_of_dirichletGRH hGRH)

end PrimitiveReduction

end FareyGoldbach
