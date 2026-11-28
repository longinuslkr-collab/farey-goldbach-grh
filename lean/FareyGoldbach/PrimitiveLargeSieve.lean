import FareyGoldbach.AdditiveLargeSieve
import FareyGoldbach.AveragedRemainder
import FareyGoldbach.LocalLogDerivative

/-! # From additive large sieve to the large sieve for primitive Dirichlet characters -/

open scoped BigOperators Classical

namespace FareyGoldbach

/-- The primitive-character square sum at one level, including the classical factor
`q / φ(q)`. Defining the level zero value makes finite sums over levels ordinary sums. -/
noncomputable def primitiveCharacterEnergy (q : ℕ) (s : Finset ℕ) (a : ℕ→ℂ) : ℝ :=
  if hq : 0<q then
    letI : NeZero q := ⟨hq.ne'⟩
    (q:ℝ)/q.totient * ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
      (fun χ => χ.IsPrimitive), ‖∑ n∈s,a n*χ (n : ZMod q)‖^2
  else 0

theorem primitiveCharacterEnergy_of_pos {q : ℕ} [NeZero q] (hq : 0<q)
    (s : Finset ℕ) (a : ℕ→ℂ) :
    primitiveCharacterEnergy q s a =
      (q:ℝ)/q.totient * ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
        (fun χ => χ.IsPrimitive), ‖∑ n∈s,a n*χ (n : ZMod q)‖^2 := by
  simp [primitiveCharacterEnergy,hq]

private lemma stdAddChar_nat_mul {q : ℕ} [NeZero q] (n b : ℕ) :
    ZMod.stdAddChar ((n:ZMod q)*(b:ZMod q)) = e ((n:ℝ)*b/q) := by
  have h := ZMod.stdAddChar_coe (N:=q) ((n:ℤ)*(b:ℤ))
  push_cast at h
  rw [h,e]
  congr 1
  push_cast
  ring

private lemma primitive_gauss_identity {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (s : Finset ℕ) (a : ℕ→ℂ) :
    (q:ℝ)*‖∑ n∈s,a n*χ (n:ZMod q)‖^2 =
      ‖∑ z∈zmodUnitsFinset q, (∑ n∈s,a n*ZMod.stdAddChar ((n:ZMod q)*z))*χ⁻¹ z‖^2 := by
  let G := gaussSum χ⁻¹ ZMod.stdAddChar
  have hG : ‖G‖ = Real.sqrt (q:ℝ) := χ⁻¹.norm_gaussSum_stdAddChar hχ.inv
  have hshift (n : ℕ) : χ (n:ZMod q)*G =
      ∑ z∈zmodUnitsFinset q, χ⁻¹ z * ZMod.stdAddChar ((n:ZMod q)*z) := by
    have h := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ.inv (n:ZMod q)
    rw [inv_inv] at h
    change _*gaussSum χ⁻¹ ZMod.stdAddChar = _
    rw [←h]
    unfold gaussSum
    simp only [AddChar.mulShift_apply]
    symm
    apply Finset.sum_subset (Finset.filter_subset ..)
    intro z _ hz
    have hnon : ¬ IsUnit z := fun hu => hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩)
    rw [MulChar.map_nonunit _ hnon,zero_mul]
  have hsum : (∑ n∈s,a n*χ (n:ZMod q))*G =
      ∑ z∈zmodUnitsFinset q, (∑ n∈s,a n*ZMod.stdAddChar ((n:ZMod q)*z))*χ⁻¹ z := by
    rw [Finset.sum_mul]
    simp_rw [mul_assoc, hshift, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [←hsum,norm_mul,mul_pow,hG,Real.sq_sqrt (Nat.cast_nonneg _),mul_comm]

/-- At one level, multiplicative Parseval bounds the primitive-character energy
by the additive energies at the distinct reduced fractions of that denominator. -/
theorem primitiveCharacterEnergy_le_additive {q : ℕ} (hq : 0<q) (s : Finset ℕ) (a : ℕ→ℂ) :
    primitiveCharacterEnergy q s a ≤
      ∑ b∈coprimeClasses q, ‖∑ n∈s,a n*e ((n:ℝ)*b/q)‖^2 := by
  let : NeZero q := ⟨hq.ne'⟩
  let D (z : ZMod q) := ∑ n∈s, a n*ZMod.stdAddChar ((n:ZMod q)*z)
  let A (χ : DirichletCharacter ℂ q) := ‖∑ z∈zmodUnitsFinset q,D z*χ z‖^2
  let P := (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive)
  have hsum : (q:ℝ)*(∑ χ∈P,‖∑ n∈s,a n*χ (n:ZMod q)‖^2) ≤
      ∑ χ : DirichletCharacter ℂ q, A χ := by
    rw [Finset.mul_sum]
    calc _ = ∑ χ∈P,A χ⁻¹ := Finset.sum_congr rfl fun χ hχ =>
             primitive_gauss_identity χ (Finset.mem_filter.mp hχ).2 s a
         _ ≤ ∑ χ : DirichletCharacter ℂ q,A χ⁻¹ := Finset.sum_le_sum_of_subset_of_nonneg
             (Finset.filter_subset ..) (fun χ _ _ => sq_nonneg _)
         _ = _ := Equiv.sum_comp (Equiv.inv (DirichletCharacter ℂ q)) A
  have htot : (0:ℝ)<q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
  have hmul := mul_le_mul_of_nonneg_left hsum (show 0≤1/(q.totient:ℝ) by positivity)
  have hparse := mul_parseval_units hq D
  rw [primitiveCharacterEnergy_of_pos hq]
  calc _ = (1/(q.totient:ℝ))*((q:ℝ)*(∑ χ∈P,‖∑ n∈s,a n*χ (n:ZMod q)‖^2)) := by
           dsimp only [P]; ring
       _ ≤ _ := hmul
       _ = ∑ z∈zmodUnitsFinset q, ‖D z‖^2 := hparse.symm
       _ = _ := by
         refine Finset.sum_bij (fun z _ => z.val) ?_ ?_ ?_ ?_
         · intro z hz
           apply mem_coprimeClasses.mpr
           exact ⟨z.val_lt,(ZMod.isUnit_iff_coprime z.val q).mp (by simpa using (Finset.mem_filter.mp hz).2)⟩
         · intro z _ w _ h
           simpa using congrArg (fun n:ℕ => (n:ZMod q)) h
         · intro b hb
           have h := mem_coprimeClasses.mp hb
           exact ⟨(b:ZMod q), Finset.mem_filter.mpr ⟨Finset.mem_univ _,(ZMod.isUnit_iff_coprime _ _).mpr h.2⟩,
             ZMod.val_natCast_of_lt h.1⟩
         · intro z _
           apply congrArg (fun w : ℂ => ‖w‖^2)
           refine Finset.sum_congr rfl fun n _ => ?_
           rw [←stdAddChar_nat_mul,ZMod.natCast_zmod_val]

/-- The multiplicative large sieve for primitive Dirichlet characters on the interval
(M, M+N], with the conductor weight q / φ(q) and an explicit constant. -/
theorem primitive_large_sieve (M N Q : ℕ) (a : ℕ → ℂ) :
    (∑ q ∈ Finset.Icc 1 Q, primitiveCharacterEnergy q (Finset.Ioc M (M+N)) a) ≤
      50*((N:ℝ)+(Q:ℝ)^2)*(∑ n ∈ Finset.Ioc M (M+N), ‖a n‖^2) := by
  apply le_trans _ (additive_large_sieve M N Q a)
  exact Finset.sum_le_sum fun q hq =>
    primitiveCharacterEnergy_le_additive (Finset.mem_Icc.mp hq).1 _ a

end FareyGoldbach
