import FareyGoldbach.ChenConductorExpansion

/-! # Products of primitive characters at coprime levels -/

open scoped Classical

namespace FareyGoldbach

/-- Product at level `m*n` of the two lifted characters. -/
noncomputable def chenCRTChar {m n : ℕ} (χ : DirichletCharacter ℂ m)
    (ψ : DirichletCharacter ℂ n) : DirichletCharacter ℂ (m*n) :=
  χ.changeLevel (Nat.dvd_mul_right m n) * ψ.changeLevel (Nat.dvd_mul_left n m)

theorem chenCRTChar_apply {m n : ℕ} [NeZero m] [NeZero n]
    (χ : DirichletCharacter ℂ m) (ψ : DirichletCharacter ℂ n) (a : ℕ) :
    chenCRTChar χ ψ (a : ZMod (m*n)) = χ (a : ZMod m) * ψ (a : ZMod n) := by
  simp only [chenCRTChar,MulChar.mul_apply,chenChangeLevel_apply_mask,
    Nat.mul_div_cancel_left _ (NeZero.pos m),Nat.mul_div_cancel _ (NeZero.pos n),chenMaskedChar]
  by_cases hm : a.Coprime m
  · by_cases hn : a.Coprime n
    · rw [ite_eq_left hn,ite_eq_left hm]
    · have hψ : ψ (a : ZMod n) = 0 := MulChar.map_nonunit _
        (fun hu => hn ((ZMod.isUnit_iff_coprime _ _).mp hu))
      simp [hn,hψ]
  · have hχ : χ (a : ZMod m) = 0 := MulChar.map_nonunit _
      (fun hu => hm ((ZMod.isUnit_iff_coprime _ _).mp hu))
    simp [hm,hχ]

/-- Primitivity of the CRT product. The conductor of each factor divides the
product conductor by cancellation of the coprime other conductor. -/
theorem chenCRTChar_isPrimitive {m n : ℕ} [NeZero m] [NeZero n] (hmn : m.Coprime n)
    {χ : DirichletCharacter ℂ m} {ψ : DirichletCharacter ℂ n}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) : (chenCRTChar χ ψ).IsPrimitive := by
  let A := χ.changeLevel (Nat.dvd_mul_right m n)
  let B := ψ.changeLevel (Nat.dvd_mul_left n m)
  have hA : A.conductor=m := (χ.conductor_changeLevel _).trans hχ
  have hB : B.conductor=n := (ψ.conductor_changeLevel _).trans hψ
  change (A*B).conductor=m*n
  apply Nat.dvd_antisymm (A*B).conductor_dvd_level
  apply hmn.mul_dvd_of_dvd_of_dvd
  · have hd := DirichletCharacter.conductor_mul_dvd_lcm_conductor (A*B) B⁻¹
    rw [mul_inv_cancel_right,DirichletCharacter.conductor_inv,hA,hB] at hd
    exact hmn.dvd_of_dvd_mul_right (hd.trans (Nat.lcm_dvd_mul _ _))
  · have hd := DirichletCharacter.conductor_mul_dvd_lcm_conductor (A*B) A⁻¹
    rw [mul_comm A B,mul_inv_cancel_right,DirichletCharacter.conductor_inv,hA,hB] at hd
    rw [mul_comm B A] at hd
    exact hmn.symm.dvd_of_dvd_mul_right (hd.trans (Nat.lcm_dvd_mul _ _))

theorem chenCRTChar_injective {m n : ℕ} [NeZero m] [NeZero n] (hmn : m.Coprime n) :
    Function.Injective (fun p : DirichletCharacter ℂ m × DirichletCharacter ℂ n =>
      chenCRTChar p.1 p.2) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ he
  let f := DirichletCharacter.changeLevel (R:=ℂ) (Nat.dvd_mul_right m n)
  let g := DirichletCharacter.changeLevel (R:=ℂ) (Nat.dvd_mul_left n m)
  change f a * g b = f c * g d at he
  have hr : f (a/c) = g (d/b) := by
    rw [map_div,map_div]
    exact div_eq_div_iff_mul_eq_mul.mpr (by simpa only [mul_comm (g d) (f c)] using he)
  have hmc : (f (a/c)).conductor∣m := by
    rw [DirichletCharacter.conductor_changeLevel]
    exact (a/c).conductor_dvd_level
  have hnc : (f (a/c)).conductor∣n := by
    rw [hr,DirichletCharacter.conductor_changeLevel]
    exact (d/b).conductor_dvd_level
  have hf1 : f (a/c) = 1 := DirichletCharacter.eq_one_iff_conductor_eq_one.mpr
    (Nat.eq_one_of_dvd_coprimes hmn hmc hnc)
  have hac : a=c := div_eq_one.mp
    (DirichletCharacter.changeLevel_injective _ (hf1.trans (map_one f).symm))
  subst c
  have hbd := DirichletCharacter.changeLevel_injective _ (mul_left_cancel he)
  exact Prod.ext rfl hbd

/-- Evaluation after lifting the two characters combines their cofactor masks. -/
theorem chenCRTChar_changeLevel_mask {m n r d : ℕ} [NeZero m] [NeZero n]
    (hm : m∣r) (hn : n∣d) (χ : DirichletCharacter ℂ m) (ψ : DirichletCharacter ℂ n)
    (a : ℕ) : χ.changeLevel hm (a : ZMod r) * ψ.changeLevel hn (a : ZMod d) =
      chenMaskedChar (chenCRTChar χ ψ) ((r/m)*(d/n)) a := by
  rw [chenChangeLevel_apply_mask,chenChangeLevel_apply_mask]
  simp only [chenMaskedChar,chenCRTChar_apply,Nat.coprime_mul_iff_right]
  split_ifs <;> first | rfl | simp_all

end FareyGoldbach
