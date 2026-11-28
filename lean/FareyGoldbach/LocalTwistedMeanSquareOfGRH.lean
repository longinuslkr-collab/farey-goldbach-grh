import FareyGoldbach.LocalContourMeanSquare
import FareyGoldbach.SmoothedTwistOfGRH
import FareyGoldbach.ShortEvenDensity

/-! # Local twisted mean square and short-interval Goldbach for all characters -/

open MeasureTheory Filter
open scoped BigOperators Classical Topology

namespace FareyGoldbach

/-- Passing to the primitive character changes only powers of primes dividing the level.
The bound is uniform in the additive frequency. -/
theorem continuousTwistedRemainder_sub_primitive_le {Y d : ℕ} [NeZero d]
    (χ : DirichletCharacter ℂ d) (t : ℝ) (hY : 2 ≤ Y) :
    ‖continuousTwistedRemainder χ Y t - continuousTwistedRemainder χ.primitiveCharacter Y t‖ ≤
      8 * Real.sqrt (Y:ℝ) * Real.log (2*(d:ℝ)*Y) := by
  let _ : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  have hpr := eq_one_iff_primitiveCharacter_eq_one χ
  have hmain : (if χ = 1 then shortContinuousMain Y t else 0) =
      (if χ.primitiveCharacter = 1 then shortContinuousMain Y t else 0) :=
    if_congr hpr rfl rfl
  unfold continuousTwistedRemainder shortTwistedRemainderWith
  rw [hmain, sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib]
  let s := (Finset.Icc 1 Y).filter (fun n => ¬ Nat.Coprime n d)
  let f (n : ℕ) := (ArithmeticFunction.vonMangoldt n : ℂ) *
      (χ (n : ZMod d) - χ.primitiveCharacter (n : ZMod χ.conductor)) * scaledTiltedBump Y t (n:ℝ)
  have hf (n : ℕ) : ‖f n‖ ≤ 2*ArithmeticFunction.vonMangoldt n := by
    have he : ‖scaledTiltedBump Y t (n:ℝ)‖ ≤ 1 := by
      unfold scaledTiltedBump
      rw [norm_mul,norm_e,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (quarticBump_nonneg _)]
      exact quarticBump_le_one _
    have hc : ‖χ (n : ZMod d) - χ.primitiveCharacter (n : ZMod χ.conductor)‖ ≤ 2 := by
      linarith only [norm_sub_le (χ (n : ZMod d)) (χ.primitiveCharacter (n : ZMod χ.conductor)),
        norm_dirichletChar_le_one χ (n : ZMod d),norm_dirichletChar_le_one χ.primitiveCharacter (n : ZMod χ.conductor)]
    unfold f
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hc ArithmeticFunction.vonMangoldt_nonneg) he
      (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have heq : ∑ n ∈ Finset.Icc 1 Y,
      ((ArithmeticFunction.vonMangoldt n : ℂ)*χ (n : ZMod d)*scaledTiltedBump Y t (n : ℝ) -
      (ArithmeticFunction.vonMangoldt n : ℂ)*χ.primitiveCharacter (n : ZMod χ.conductor)*scaledTiltedBump Y t (n : ℝ)) =
      ∑ n ∈ s, f n := by
    dsimp only [s]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hcop : Nat.Coprime n d
    · have hh := DirichletCharacter.primitiveCharacter_apply_of_isCoprime χ
          (Nat.isCoprime_iff_coprime.mpr hcop)
      have hchar : χ.primitiveCharacter (n : ZMod χ.conductor) = χ (n : ZMod d) := by simpa using hh
      simp [hcop,hchar]
    · simp only [hcop,not_false_eq_true,ite_true,f]
      ring
  rw [heq]
  have hnc := nonCoprimeVonMangoldt_le Y d (by omega) (NeZero.pos d)
  have hd1 : (1:ℝ) ≤ d := Nat.one_le_cast.mpr (NeZero.pos d)
  have hY2 : (2:ℝ) ≤ Y := by exact_mod_cast hY
  have hy : (0:ℝ)<Y := by linarith
  have hdlog : 0 ≤ Real.log (2*(d:ℝ)) := Real.log_nonneg (by linarith)
  have hlogY : 0 ≤ Real.log (Y:ℝ) := Real.log_nonneg (by linarith)
  have hl : Real.log (2*(d:ℝ)) ≤ Real.log (2*(d:ℝ)*Y) := Real.log_le_log
    (by linarith) (by nlinarith only [mul_le_mul_of_nonneg_left hY2 (by linarith : 0≤2*(d:ℝ)),hd1])
  have hyl : Real.log (Y:ℝ) ≤ 2*Real.sqrt (Y:ℝ) := by
    have hh := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hy)
    rw [Real.log_sqrt hy.le] at hh
    linarith
  calc _ ≤ ∑ n ∈ s, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ s, 2*ArithmeticFunction.vonMangoldt n := Finset.sum_le_sum fun n _ => hf n
    _ = 2*∑ n ∈ s, ArithmeticFunction.vonMangoldt n := (Finset.mul_sum _ _ _).symm
    _ ≤ 2*(2*Real.log (2*(d:ℝ))*Real.log (Y:ℝ)) := mul_le_mul_of_nonneg_left hnc (by norm_num)
    _ ≤ _ := by nlinarith only [mul_le_mul hl hyl hlogY (hdlog.trans hl)]

/-- The conductor reduction preserves the mean-square scale, uniformly in the level. -/
theorem localTwistedMeanSquare_of_primitive
    (h : ∃ C : ℝ, 0 < C ∧ ∀ (Y d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d),
      χ.IsPrimitive → ∀ ξ : ℝ, 2 ≤ Y → 1/(Y:ℝ) ≤ ξ → ξ ≤ 1/2 →
      (∫ t in -ξ..ξ, ‖continuousTwistedRemainder χ Y t‖^2) ≤ C*(Y:ℝ)*ξ*Real.log (2*(d:ℝ)*Y)^2) :
    LocalTwistedMeanSquare := by
  obtain ⟨C,hC,hm⟩ := h
  refine ⟨2*C+256,by linarith,?_⟩
  intro Y d hd χ ξ hY hξ hξ'
  let _ : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  have hY' : (0:ℝ)<Y := Nat.cast_pos.mpr (by omega)
  have hξ0 : 0 ≤ ξ := (by positivity : 0≤1/(Y:ℝ)).trans hξ
  have hcond : χ.conductor ≤ d := Nat.le_of_dvd (NeZero.pos d) χ.conductor_dvd_level
  have hc1 : (1:ℝ) ≤ χ.conductor := Nat.one_le_cast.mpr (NeZero.pos χ.conductor)
  have hY1 : (1:ℝ) ≤ Y := by exact_mod_cast (by omega : 1≤Y)
  have hlog0 : 0 ≤ Real.log (2*(χ.conductor:ℝ)*Y) := Real.log_nonneg (by
    nlinarith only [mul_le_mul hc1 hY1 (by norm_num : (0:ℝ)≤1) (Nat.cast_nonneg (α:=ℝ) χ.conductor)])
  have hlog := Real.log_le_log (by positivity : 0<2*(χ.conductor:ℝ)*Y)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcond) (by norm_num : (0:ℝ)≤2)) hY'.le)
  set P : ℝ := (Y:ℝ)*Real.log (2*(d:ℝ)*Y)^2
  let F := continuousTwistedRemainder χ.primitiveCharacter Y
  let G := continuousTwistedRemainder χ Y
  have hF : Continuous F := continuous_shortTwistedRemainderWith _ _ _
  have hG : Continuous G := continuous_shortTwistedRemainderWith _ _ _
  have hsq t : ‖G t - F t‖^2 ≤ 64*P := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) (continuousTwistedRemainder_sub_primitive_le χ t hY) 2
    rw [mul_pow,mul_pow,Real.sq_sqrt hY'.le] at hh
    exact hh.trans_eq (by dsimp only [P]; ring)
  have hpt t : ‖G t‖^2 ≤ 2*‖F t‖^2+128*P := by
    have htri := norm_le_norm_sub_add (G t) (F t)
    have hh := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith only [hh,hsq t,sq_nonneg (‖F t‖-‖G t-F t‖)]
  have hF2 : Continuous (fun t => ‖F t‖^2) := hF.norm.pow 2
  have hconst : IntervalIntegrable (fun _ : ℝ => 128*P) volume (-ξ) ξ := continuous_const.intervalIntegrable _ _
  have hi : (∫ t in -ξ..ξ, ‖G t‖^2) ≤ ∫ t in -ξ..ξ, 2*‖F t‖^2+128*P :=
    intervalIntegral.integral_mono_on (μ:=volume) (by linarith) ((hG.norm.pow 2).intervalIntegrable _ _)
      (((hF2.const_mul 2).add continuous_const).intervalIntegrable _ _) (fun t _ => hpt t)
  rw [intervalIntegral.integral_add ((hF2.const_mul _).intervalIntegrable _ _) hconst,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const] at hi
  have hp := (hm Y χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive ξ hY hξ hξ').trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog 2) (by positivity))
  change (∫ t in -ξ..ξ, ‖F t‖^2) ≤ _ at hp
  change (∫ t in -ξ..ξ, ‖G t‖^2) ≤ _
  simp only [smul_eq_mul] at hi
  dsimp only [P] at hi
  linarith only [hi,hp]
/-- Dirichlet GRH gives the short-arc twisted mean square uniformly over all characters. -/
theorem localTwistedMeanSquare_of_dirichletGRH (hGRH : DirichletGRH) : LocalTwistedMeanSquare :=
  localTwistedMeanSquare_of_primitive (primitive_local_twisted_mean_square hGRH)

/-- The short-interval estimate holds for arbitrary nonempty translated windows. -/
theorem short_double_average_of_dirichletGRH (hGRH : DirichletGRH) : ShortDoubleAvgBound :=
  short_double_average_of_localTwistedMeanSquare (localTwistedMeanSquare_of_dirichletGRH hGRH)

/-- When the window includes a complete period the elementary cap is exactly proportional
to its length divided by the modulus. -/
theorem short_double_average_long_window_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ C : ℝ, 0<C ∧ ∀ {X Δ r : ℕ} (hr : 0<r), 2≤X → r≤Δ → Δ≤X →
      shortDoubleAvgExceptions X Δ r hr ≤ C*min ((Δ:ℝ)/r) (shortDoubleAvgAnalyticCap X Δ r) :=
  shortDoubleAvgBound_long_window (short_double_average_of_dirichletGRH hGRH)

/-- Density of the double-averaged exceptions relative to the number of periods. -/
theorem short_double_average_density_one_of_dirichletGRH (hGRH : DirichletGRH)
    (X Δ r : ℕ→ℕ) (hr : ∀ n,0<r n) (hX : ∀ n,2≤X n) (hrX : ∀ n,r n≤X n)
    (hΔ : ∀ n,1≤Δ n) (hΔX : ∀ n,Δ n≤X n)
    (hP : Tendsto (fun n => shortDoubleAvgParameter (X n) (Δ n) (r n)) atTop atTop) :
    Tendsto (fun n => shortDoubleAvgExceptions (X n) (Δ n) (r n) (hr n) / ((Δ n:ℝ)/r n)) atTop (𝓝 0) :=
  shortDoubleAvgDensity_of_bound (short_double_average_of_dirichletGRH hGRH) X Δ r hr hX hrX hΔ hΔX hP

/-- The ordinary binary Goldbach exceptional count in a single translated window. -/
theorem short_goldbach_exceptions_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ C : ℝ, 0<C ∧ ∀ {X Δ : ℕ}, 2≤X → 1≤Δ → Δ≤X →
      ((shortGoldbachExceptions X Δ).card:ℝ) ≤ C*min (Δ:ℝ) (Real.sqrt (Δ:ℝ)*Real.log (2*(X:ℝ))^3) := by
  obtain ⟨C,hC,hb⟩ := short_double_average_long_window_of_dirichletGRH hGRH
  refine ⟨C,hC,fun {X Δ} hX hΔ hΔX => ?_⟩
  simpa [shortDoubleAvgExceptions_one,shortDoubleAvgAnalyticCap] using hb (r:=1) (by decide) hX hΔ hΔX

/-- Under Dirichlet GRH, the fraction of actual even targets without a representation
vanishes when the length exceeds the sixth logarithmic power in the limit. -/
theorem short_goldbach_even_exception_density_zero_of_dirichletGRH (hGRH : DirichletGRH)
    (X Δ : ℕ → ℕ) (hX : ∀ n, 2≤X n) (hΔ : ∀ n, 1≤Δ n) (hΔX : ∀ n, Δ n≤X n)
    (hP : Tendsto (fun n => (Δ n:ℝ)/Real.log (2*(X n:ℝ))^6) atTop atTop) :
    Tendsto (fun n => ((shortGoldbachExceptions (X n) (Δ n)).card:ℝ) /
      ((shortEvenIntegers (X n) (Δ n)).card:ℝ)) atTop (𝓝 0) :=
  short_goldbach_even_exception_density_zero_of_bound
    (short_double_average_of_dirichletGRH hGRH) X Δ hX hΔ hΔX hP

/-- At modulus one, the actual proportion of even integers representable as a sum of
two primes tends to one for Δ/log⁶(2X) tending to infinity. -/
theorem short_goldbach_even_density_one_of_dirichletGRH (hGRH : DirichletGRH)
    (X Δ : ℕ → ℕ) (hX : ∀ n, 2≤X n) (hΔ : ∀ n, 1≤Δ n) (hΔX : ∀ n, Δ n≤X n)
    (hP : Tendsto (fun n => (Δ n:ℝ)/Real.log (2*(X n:ℝ))^6) atTop atTop) :
    Tendsto (fun n => ((shortGoldbachRepresented (X n) (Δ n)).card:ℝ) /
      ((shortEvenIntegers (X n) (Δ n)).card:ℝ)) atTop (𝓝 1) :=
  short_goldbach_even_density_one_of_bound (short_double_average_of_dirichletGRH hGRH) X Δ hX hΔ hΔX hP

end FareyGoldbach

