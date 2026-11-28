import FareyGoldbach.ZeroFreeLocal

/-! # The 3–4–1 logarithmic derivative inequality -/

open Complex Filter
open scoped Classical

namespace FareyGoldbach

private noncomputable def zfWeight (d : ℕ) (χ : DirichletCharacter ℂ d) (n : ℕ) : ℂ :=
  χ (n:ZMod d)*(ArithmeticFunction.vonMangoldt n:ℂ)

private theorem zfSeries {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (σ t : ℝ) (hσ : 1<σ) :
    HasSum (fun n => (LSeries.term (zfWeight d χ) (zeroFreePoint σ t) n).re)
      ((negLogDerivL χ (zeroFreePoint σ t)).re) := by
  have hs : 1 < (zeroFreePoint σ t).re := by simpa using hσ
  have HH := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
  have h : HasSum (LSeries.term (zfWeight d χ) (zeroFreePoint σ t))
      (negLogDerivL χ (zeroFreePoint σ t)) := by
    rw [← LSeries_twist_vonMangoldt_eq_negLogDerivL χ hs]
    exact HH.hasSum
  exact Complex.hasSum_re h

private theorem zfTerm {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (σ t : ℝ)
    {n : ℕ} (hn : n≠0) :
    LSeries.term (zfWeight d χ) (zeroFreePoint σ t) n =
      ((ArithmeticFunction.vonMangoldt n*(n:ℝ)^(-σ):ℝ):ℂ) *
        (χ (n:ZMod d) * (n:ℂ)^(-((t:ℂ)*I))) := by
  have hn' : (n:ℂ)≠0 := Nat.cast_ne_zero.mpr hn
  rw [LSeries.term_of_ne_zero hn]
  simp only [zfWeight,zeroFreePoint,div_eq_mul_inv, Complex.cpow_neg,
    Complex.cpow_add _ _ hn',Complex.ofReal_mul,Complex.ofReal_cpow (Nat.cast_nonneg _),
    Complex.ofReal_natCast,Complex.ofReal_neg,mul_inv_rev]
  ring

private theorem zfTrigonometric {z : ℂ} (hz : ‖z‖≤1) : 0≤3+4*z.re+(z^2).re := by
  have hnorm : z.re^2+z.im^2=‖z‖^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    ring
  rw [sq,Complex.mul_re]
  nlinarith only [hnorm,sq_nonneg (z.re+1),mul_nonneg (sub_nonneg.mpr hz)
    (add_nonneg zero_le_one (norm_nonneg z))]

/-- Positivity of the real part of the logarithmic derivative of the standard
3–4–1 product, with the untwisted zeta factor at level one. -/
theorem zeroFree_logDeriv_341 {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d)
    (σ t : ℝ) (hσ : 1<σ) :
    0 ≤ 3*(negLogDerivL (1:DirichletCharacter ℂ 1) (zeroFreePoint σ 0)).re +
      4*(negLogDerivL χ (zeroFreePoint σ t)).re +
      (negLogDerivL (χ^2) (zeroFreePoint σ (2*t))).re := by
  have hsum := (((zfSeries (1:DirichletCharacter ℂ 1) σ 0 hσ).mul_left (3:ℝ)).add
    ((zfSeries χ σ t hσ).mul_left (4:ℝ))).add (zfSeries (χ^2) σ (2*t) hσ)
  rw [← hsum.tsum_eq]
  apply tsum_nonneg
  intro n
  by_cases hn : n=0
  · simp [hn]
  let w : ℝ := ArithmeticFunction.vonMangoldt n*(n:ℝ)^(-σ)
  let p : ℂ := (n:ℂ)^(-((t:ℂ)*I))
  let z := χ (n:ZMod d)*p
  have hp : ‖p‖=1 := by
    dsimp [p]
    rw [← Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))]
    simp [Complex.mul_re]
  have hz : ‖z‖≤1 := by dsimp [z]; rw [norm_mul,hp,mul_one]; exact χ.norm_le_one _
  have hphase : (n:ℂ)^(-(((2*t:ℝ):ℂ)*I))=p^2 := by
    dsimp [p]
    rw [sq,← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
    congr 1
    push_cast
    ring
  have hpr : (1:DirichletCharacter ℂ 1) (n:ZMod 1) = 1 := by
    rw [show (n:ZMod 1) = 1 from Subsingleton.elim _ _,map_one]
  have hchar : (χ^2) (n:ZMod d)=(χ (n:ZMod d))^2 := by simp [sq,MulChar.mul_apply]
  have h₂ : (χ^2) (n:ZMod d)*(n:ℂ)^(-(((2*t:ℝ):ℂ)*I)) = z^2 := by rw [hchar,hphase]; exact (mul_pow _ _ 2).symm
  simp only [zfTerm _ _ _ hn,hpr,
    Complex.ofReal_zero,zero_mul,neg_zero,Complex.cpow_zero,mul_one,h₂]
  change 0≤3*((w:ℂ)).re + 4*((w:ℂ)*z).re + ((w:ℂ)*z^2).re
  simp only [Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hw : 0≤w := mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  nlinarith only [mul_nonneg hw (zfTrigonometric hz)]

end FareyGoldbach
