import FareyGoldbach.SmoothedTwistOfGRH

/-! # Conductor reduction for the sharp von Mangoldt sum -/

open scoped Classical

namespace FareyGoldbach

private theorem sharp_character_discrepancy {X d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d)
    (hX : 2≤X) :
    ‖(∑ n∈Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ)*χ n) -
      (∑ n∈Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ)*χ.primitiveCharacter n)‖ ≤
      4*Real.log (2*(d:ℝ))*Real.log (X:ℝ) := by
  have : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  let bad := (Finset.Icc 1 X).filter (fun n => ¬n.Coprime d)
  let dχ := fun (n:ℕ) => χ n - χ.primitiveCharacter n
  have heq : (∑ n∈Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ)*χ n) -
      (∑ n∈Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ)*χ.primitiveCharacter n) =
      ∑ n∈bad, (ArithmeticFunction.vonMangoldt n : ℂ)*dχ n := by
    rw [←Finset.sum_sub_distrib, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [←mul_sub]
    by_cases h : n.Coprime d
    · have hc : χ.primitiveCharacter n = χ n := by
        simpa using (DirichletCharacter.primitiveCharacter_apply_of_isCoprime χ
          (Nat.isCoprime_iff_coprime.mpr h))
      simp [h,hc]
    · simp [h,dχ]
  have hbound (n:ℕ) : ‖dχ n‖≤2 := (norm_sub_le _ _).trans
    (by linarith only [norm_dirichletChar_le_one χ (n:ZMod d),
      norm_dirichletChar_le_one χ.primitiveCharacter (n:ZMod χ.conductor)])
  rw [heq]
  calc _ ≤ ∑ n∈bad, ‖(ArithmeticFunction.vonMangoldt n:ℂ)*dχ n‖ := norm_sum_le _ _
       _ ≤ ∑ n∈bad, 2*ArithmeticFunction.vonMangoldt n := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
            mul_comm (2:ℝ)]
          exact mul_le_mul_of_nonneg_left (hbound n) ArithmeticFunction.vonMangoldt_nonneg
       _ = 2*∑ n∈bad, ArithmeticFunction.vonMangoldt n := (Finset.mul_sum _ _ _).symm
       _ ≤ 4*Real.log (2*(d:ℝ))*Real.log (X:ℝ) := by
          have h := nonCoprimeVonMangoldt_le X d (by omega) (NeZero.pos d)
          change 2*(∑ n∈(Finset.Icc 1 X).filter (fun n => ¬n.Coprime d), _) ≤ _
          linarith only [h]

/-- Removing primitivity costs at most four in the constant, uniformly in the
original modulus and its conductor. -/
theorem sharpVonMangoldtTwist_of_primitive_bound (C:ℝ) (hC:0<C)
    (hprimitive : ∀ (X d:ℕ) [NeZero d] (χ : DirichletCharacter ℂ d), χ.IsPrimitive → 2≤X →
      ‖(∑ n∈Finset.Icc 1 X,(ArithmeticFunction.vonMangoldt n:ℂ)*χ n)-
        (if χ=1 then (X:ℂ) else 0)‖ ≤ C*Real.sqrt (X:ℝ)*Real.log (2*(d:ℝ)*(X:ℝ))^2) :
    ∀ (X d:ℕ) [NeZero d] (χ : DirichletCharacter ℂ d), 2≤X →
      ‖(∑ n∈Finset.Icc 1 X,(ArithmeticFunction.vonMangoldt n:ℂ)*χ n)-
        (if χ=1 then (X:ℂ) else 0)‖ ≤ (C+4)*Real.sqrt (X:ℝ)*Real.log (2*(d:ℝ)*(X:ℝ))^2 := by
  intro X d _ χ hX
  have : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  let L := Real.log (2*(d:ℝ)*(X:ℝ))
  have hx : 1≤(X:ℝ) := by exact_mod_cast (show 1≤X by omega)
  have hd : 1≤(d:ℝ) := by exact_mod_cast (NeZero.pos d)
  have hq : 1≤(χ.conductor:ℝ) := by exact_mod_cast (NeZero.pos χ.conductor)
  have hqd : (χ.conductor:ℝ)≤d := by
    exact_mod_cast (Nat.le_of_dvd (NeZero.pos d) χ.conductor_dvd_level)
  have hX0 : 0<(X:ℝ) := by linarith
  have hd0 : 0<(d:ℝ) := by linarith
  have hq0 : 0<(χ.conductor:ℝ) := by linarith
  have hl1 : Real.log (2*(d:ℝ))≤L := Real.log_le_log (by positivity)
    (le_mul_of_one_le_right (by positivity) hx)
  have hl2 : Real.log (X:ℝ)≤L := Real.log_le_log hX0
    (le_mul_of_one_le_left hX0.le (by linarith))
  have hc1 : Real.log (2*(χ.conductor:ℝ)*(X:ℝ))≤L := by
    exact Real.log_le_log (by positivity) (by gcongr)
  have hc0 : 0≤Real.log (2*(χ.conductor:ℝ)*(X:ℝ)) := Real.log_nonneg (by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hx)])
  have hL := hc0.trans hc1
  have hprod : Real.log (2*(d:ℝ))*Real.log (X:ℝ)≤L^2 := by
    rw [pow_two]
    exact mul_le_mul hl1 hl2 (Real.log_nonneg hx) hL
  have hp := hprimitive X χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive hX
  have hpc := hp.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc0 hc1 2) (by positivity))
  have hdis := sharp_character_discrepancy χ hX
  have hind : (if χ=1 then (X:ℂ) else 0) = if χ.primitiveCharacter=1 then (X:ℂ) else 0 := by
    rw [eq_one_iff_primitiveCharacter_eq_one χ]
  rw [hind]
  let etaSum := ∑ n∈Finset.Icc 1 X,(ArithmeticFunction.vonMangoldt n:ℂ)*χ.primitiveCharacter n
  let sum := ∑ n∈Finset.Icc 1 X,(ArithmeticFunction.vonMangoldt n:ℂ)*χ n
  let main := if χ.primitiveCharacter=1 then (X:ℂ) else 0
  change ‖sum-main‖≤(C+4)*Real.sqrt (X:ℝ)*L^2
  calc ‖sum-main‖ = ‖(sum-etaSum)+(etaSum-main)‖ := by congr 1; abel
       _ ≤ ‖sum-etaSum‖+‖etaSum-main‖ := norm_add_le _ _
       _ ≤ 4*L^2+C*Real.sqrt (X:ℝ)*L^2 := add_le_add
          (hdis.trans (by linarith only [hprod])) hpc
       _ ≤ _ := by
          have hsqrt : 1≤Real.sqrt (X:ℝ) := Real.one_le_sqrt.mpr hx
          nlinarith only [mul_nonneg (sub_nonneg.mpr hsqrt) (sq_nonneg L)]

end FareyGoldbach
