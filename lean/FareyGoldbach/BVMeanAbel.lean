import FareyGoldbach.BombieriVinogradovInterface

/-! # Abel summation inside the primitive character first moment -/

open Finset
open scoped Classical

namespace FareyGoldbach

noncomputable def bvPrimitiveAverage (D : ℕ) (F : (q : ℕ) → DirichletCharacter ℂ q → ℝ) : ℝ :=
  ∑ q ∈ Ico 2 D, if h : 0<q then
    letI : NeZero q := ⟨h.ne'⟩
    (∑ χ∈(univ : Finset (DirichletCharacter ℂ q)).filter (·.IsPrimitive), F q χ)/(q.totient:ℝ)
  else 0

theorem bvPrimitiveAverage_norm (D : ℕ) (F : (q : ℕ) → DirichletCharacter ℂ q → ℂ) :
    bvPrimitiveAverage D (fun q χ => ‖F q χ‖) =
      ∑ q∈Ico 2 D, chenPrimitiveNorm q (F q)/(q:ℝ) := by
  apply sum_congr rfl
  intro q hq
  have hp : 0<q := by have := (mem_Ico.mp hq).1; omega
  let _ : NeZero q := ⟨hp.ne'⟩
  dsimp only
  rw [dite_eq_left hp,chenPrimitiveNorm_div_eq_avg]

theorem bvPrimitiveAverage_mono {D : ℕ} {F G : (q : ℕ) → DirichletCharacter ℂ q → ℝ}
    (h : ∀ q∈Ico 2 D, ∀ χ, χ.IsPrimitive → F q χ≤G q χ) :
    bvPrimitiveAverage D F≤bvPrimitiveAverage D G := by
  apply sum_le_sum
  intro q hq
  have hp : 0<q := by have := (mem_Ico.mp hq).1; omega
  simp only [dite_eq_left hp]
  exact div_le_div_of_nonneg_right (sum_le_sum fun χ hχ => h q hq χ (mem_filter.mp hχ).2)
    (Nat.cast_nonneg _)

theorem bvPrimitiveAverage_add (D : ℕ) (F G : (q : ℕ) → DirichletCharacter ℂ q → ℝ) :
    bvPrimitiveAverage D (fun q χ => F q χ+G q χ) =
    bvPrimitiveAverage D F + bvPrimitiveAverage D G := by
  unfold bvPrimitiveAverage
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro q hq
  have hp : 0<q := by have := (mem_Ico.mp hq).1; omega
  simp only [dite_eq_left hp,sum_add_distrib,add_div]

theorem bvPrimitiveAverage_mul (D : ℕ) (c : ℝ) (F : (q : ℕ) → DirichletCharacter ℂ q → ℝ) :
    bvPrimitiveAverage D (fun q χ => c*F q χ) = c*bvPrimitiveAverage D F := by
  unfold bvPrimitiveAverage
  rw [mul_sum]
  apply sum_congr rfl
  intro q hq
  have hp : 0<q := by have := (mem_Ico.mp hq).1; omega
  simp only [dite_eq_left hp,←Finset.mul_sum,mul_div_assoc]

theorem bvPrimitiveAverage_sum {ι : Type*} (D : ℕ) (s : Finset ι)
    (F : ι → (q : ℕ) → DirichletCharacter ℂ q → ℝ) :
    bvPrimitiveAverage D (fun q χ => ∑ i∈s,F i q χ) = ∑ i∈s,bvPrimitiveAverage D (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bvPrimitiveAverage]
  | @insert a s ha ih =>
    simp only [sum_insert ha]
    rw [bvPrimitiveAverage_add,ih]

theorem bvPrimitiveAverage_const_le (D : ℕ) {B : ℝ} (hB : 0≤B) :
    bvPrimitiveAverage D (fun _ _ => B)≤(D:ℝ)*B := by
  have h (q : ℕ) (hq : q∈Ico 2 D) :
      chenPrimitiveNorm q (fun _ => (B:ℂ))/(q:ℝ)≤B := by
    let _ : NeZero q := ⟨by have := (mem_Ico.mp hq).1; omega⟩
    exact chenPrimitiveNorm_div_le_of_bound _ hB (fun _ _ => by simp [Real.norm_eq_abs,abs_of_nonneg hB])
  have heq : bvPrimitiveAverage D (fun _ _ => B) =
      ∑ q∈Ico 2 D,chenPrimitiveNorm q (fun _ => (B:ℂ))/(q:ℝ) := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hB] using
      bvPrimitiveAverage_norm D (fun _ _ => (B:ℂ))
  rw [heq]
  apply (sum_le_sum h).trans
  rw [sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by simp [Nat.card_Ico])) hB

theorem bvPrimitiveAverage_abel {D N : ℕ} (w : ℕ → ℝ)
    (g : ℕ → (q : ℕ) → DirichletCharacter ℂ q → ℂ) {B : ℝ}
    (hw : ∀ i, 0≤w i) (hm : Antitone w)
    (hs : ∀ j≤N, bvPrimitiveAverage D (fun q χ => ‖∑ i∈range (j+1),g i q χ‖)≤B) :
    bvPrimitiveAverage D (fun q χ => ‖∑ i∈range (N+1),w i • g i q χ‖)≤w 0*B := by
  let S (j q : ℕ) (χ : DirichletCharacter ℂ q) := ∑ i∈range (j+1),g i q χ
  have point (q : ℕ) (χ : DirichletCharacter ℂ q) :
      ‖∑ i∈range (N+1),w i • g i q χ‖ ≤ w N*‖S N q χ‖+
      ∑ i∈range N,(w i-w (i+1))*‖S i q χ‖ := by
    rw [Finset.sum_range_by_parts]
    simp only [Nat.add_sub_cancel]
    apply (norm_sub_le ..).trans
    apply add_le_add
    · rw [norm_smul, Real.norm_eq_abs,abs_of_nonneg (hw N)]
    · apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro i _
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr (hm (Nat.le_succ i))),neg_sub]
  apply (bvPrimitiveAverage_mono (fun q _ χ _ => point q χ)).trans
  rw [bvPrimitiveAverage_add,bvPrimitiveAverage_mul,bvPrimitiveAverage_sum]
  simp_rw [bvPrimitiveAverage_mul]
  calc _ ≤ w N*B+∑ i∈range N,(w i-w (i+1))*B := by
          apply add_le_add (mul_le_mul_of_nonneg_left (hs N le_rfl) (hw N))
          exact sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hs i (mem_range.mp hi).le)
            (sub_nonneg.mpr (hm (Nat.le_succ i)))
    _ = _ := by rw [←sum_mul,Finset.sum_range_sub']; ring

end FareyGoldbach
