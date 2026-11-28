import FareyGoldbach.PrimitiveLargeSieve

/-! # A uniform Pólya–Vinogradov bound from the finite Fourier transform -/

open scoped Classical BigOperators

namespace FareyGoldbach

private lemma pv_std_nat {q : ℕ} [NeZero q] (n : ℕ) (z : ZMod q) :
    ZMod.stdAddChar ((n:ZMod q)*z) = e (((z.val:ℝ)/q)*n) := by
  have h := ZMod.stdAddChar_coe (N:=q) ((n:ℤ)*(z.val:ℤ))
  push_cast at h
  rw [ZMod.natCast_zmod_val] at h
  rw [h,e]
  congr 1
  push_cast
  ring

private lemma pv_geom (Y : ℕ) {a q : ℕ} (ha : 1≤a) (haq : a<q) :
    ‖∑ n∈Finset.range Y, e (((a:ℝ)/q)*n)‖ ≤ (q:ℝ)/a+(q:ℝ)/(q-a:ℕ) := by
  have hq : (0:ℝ)<q := Nat.cast_pos.mpr (by omega)
  have hap : (0:ℝ)<a := Nat.cast_pos.mpr ha
  have hqa : (0:ℝ)<(q-a:ℕ) := Nat.cast_pos.mpr (by omega)
  have hh : (0:ℝ)<(a:ℝ)/q := by positivity
  have hcast : ((q-a:ℕ):ℝ)=(q:ℝ)-a := Nat.cast_sub haq.le
  by_cases h : 2*a≤q
  · have hr : (a:ℝ)/q≤1/2 := (div_le_iff₀ hq).mpr (by
      have hv : 2*(a:ℝ)≤q := by exact_mod_cast h
      linarith)
    apply (norm_sum_e_le Y hh.ne' (by simpa [abs_of_pos hh] using hr)).trans
    rw [abs_of_pos hh]
    have hil : 1/(2*((a:ℝ)/q))=(q:ℝ)/a/2 := by field_simp
    rw [hil]
    linarith only [div_nonneg hq.le hap.le,div_nonneg hq.le hqa.le]
  · let β : ℝ := (a:ℝ)/q-1
    have hβ : β<0 := by dsimp [β]; rw [sub_neg,div_lt_one hq]; exact_mod_cast haq
    have hβhalf : |β|≤1/2 := by
      rw [abs_of_neg hβ]
      dsimp [β]
      have hv : (q:ℝ)≤2*a := by exact_mod_cast (by omega : q≤2*a)
      have hhalf : 1/2≤(a:ℝ)/q := (le_div_iff₀ hq).mpr (by linarith only [hv])
      linarith
    have he (n : ℕ) : e (((a:ℝ)/q)*n) = e (β*n) := by
      apply e_eq_of_sub_int (k:=(n:ℤ))
      dsimp [β]
      push_cast
      ring
    simp_rw [he]
    apply (norm_sum_e_le Y hβ.ne hβhalf).trans
    have hh' : 1/(2*|β|)=(q:ℝ)/(q-a:ℕ)/2 := by
      rw [abs_of_neg hβ,hcast]
      dsimp [β]
      have hr : (q:ℝ)-a≠0 := sub_ne_zero.mpr (by exact_mod_cast haq.ne')
      have hβ' : (a:ℝ)/q-1= -((q:ℝ)-a)/q := by field_simp; ring
      rw [hβ']
      field_simp [hr]
    rw [hh']
    linarith only [div_nonneg hq.le hap.le,div_nonneg hq.le hqa.le]

private lemma pv_harmonic {q : ℕ} (hq : 2≤q) :
    (∑ a ∈ Finset.Icc 1 (q-1), ((q:ℝ)/a+(q:ℝ)/(q-a:ℕ))) ≤
        4*(q:ℝ)*Real.log (2*(q:ℝ)) := by
  let S := Finset.Icc 1 (q-1)
  have hrev : (∑ a∈S, (q:ℝ)/(q-a:ℕ)) = ∑ a∈S, (q:ℝ)/a := by
    apply Finset.sum_bij (fun a _ => q-a)
    · intro a ha; simp only [S,Finset.mem_Icc] at ha ⊢; omega
    · intro a ha b hb h; simp only [S,Finset.mem_Icc] at ha hb; omega
    · intro a ha
      refine ⟨q-a,?_,by have := (Finset.mem_Icc.mp ha).2; omega⟩
      simp only [S,Finset.mem_Icc] at ha ⊢; omega
    · intro _ _; rfl
  have hsum : (∑ a∈S,(q:ℝ)/a) ≤ (q:ℝ)*(1+Real.log (q:ℝ)) := by
    have H := harmonic_le_one_add_log (by omega : 1≤q)
    calc
      _ = (q:ℝ)*∑ a∈S,1/(a:ℝ) := by simp [Finset.mul_sum, div_eq_mul_inv]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply le_trans _ H
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro a ha
          simp only [S,Finset.mem_Icc] at ha ⊢
          omega
        · exact fun _ _ _ => by positivity
  change (∑ a∈S, _) ≤ _
  rw [Finset.sum_add_distrib,hrev]
  have hq' : (0:ℝ)<q := Nat.cast_pos.mpr (by omega)
  rw [Real.log_mul (by norm_num) hq'.ne']
  have hl : (1/2:ℝ)≤Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hlq : 0≤Real.log (q:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤q))
  nlinarith only [hsum, mul_nonneg hq'.le (sub_nonneg.mpr hl),mul_nonneg hq'.le hlq]

/-- Pólya–Vinogradov, with a uniform explicit constant for a prefix of any length. -/
theorem polya_vinogradov {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2≤q) (Y : ℕ) :
    ‖∑ n∈Finset.Icc 1 Y, χ (n:ZMod q)‖ ≤ 4*Real.sqrt (q:ℝ)*Real.log (2*(q:ℝ)) := by
  let : Fact (1<q) := ⟨hq⟩
  let G := gaussSum χ⁻¹ ZMod.stdAddChar
  let D (z : ZMod q) := ∑ n∈Finset.range (Y+1), ZMod.stdAddChar ((n:ZMod q)*z)
  have hG : ‖G‖ = Real.sqrt (q:ℝ) := χ⁻¹.norm_gaussSum_stdAddChar hχ.inv
  have hshift (n : ℕ) : χ (n:ZMod q)*G =
      ∑ z : ZMod q, χ⁻¹ z * ZMod.stdAddChar ((n:ZMod q)*z) := by
    have H := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ.inv (n:ZMod q)
    rw [inv_inv] at H
    exact H.symm
  have hexp : (∑ n∈Finset.range (Y+1), χ (n:ZMod q))*G = ∑ z : ZMod q, D z*χ⁻¹ z := by
    rw [Finset.sum_mul]
    simp_rw [hshift]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    dsimp only [D]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => mul_comm _ _
  have hI : (Finset.range (Y+1)).erase 0 = Finset.Icc 1 Y := by ext n; simp; omega
  have hzero : χ (0:ZMod q) = 0 := χ.map_zero
  have hsum : (∑ n∈Finset.range (Y+1), χ (n:ZMod q)) = ∑ n∈Finset.Icc 1 Y, χ (n:ZMod q) := by
    rw [← hI]
    symm
    apply Finset.sum_erase
    simpa only [Nat.cast_zero] using hzero
  have he : (∑ z : ZMod q, ‖D z*χ⁻¹ z‖) = ∑ z∈(Finset.univ : Finset (ZMod q)).erase 0, ‖D z*χ⁻¹ z‖ := by
    symm
    apply Finset.sum_erase
    simp [MulChar.map_zero]
  have H : (∑ z∈(Finset.univ : Finset (ZMod q)).erase 0, ‖D z*χ⁻¹ z‖) ≤
      ∑ a∈Finset.Icc 1 (q-1), ((q:ℝ)/a+(q:ℝ)/(q-a:ℕ)) := by
    apply Finset.sum_le_sum_of_injOn (fun z => z.val)
    · intro z hz w hw h; simpa using congrArg (fun n:ℕ => (n:ZMod q)) h
    · intro j hj
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hj
      have hn : z≠0 := (Finset.mem_erase.mp hz).1
      have hval : z.val≠0 := fun h => hn (by simpa using congrArg (fun n:ℕ => (n:ZMod q)) h)
      exact Finset.mem_Icc.mpr ⟨by omega, by have := z.val_lt; omega⟩
    · intro z hz
      have hn : z≠0 := (Finset.mem_erase.mp hz).1
      have hv : 1≤z.val := Nat.one_le_iff_ne_zero.mpr fun h => hn (by
        simpa using congrArg (fun n:ℕ => (n:ZMod q)) h)
      rw [norm_mul]
      apply le_trans (mul_le_mul_of_nonneg_left (χ⁻¹.norm_le_one z) (norm_nonneg _))
      rw [mul_one]
      dsimp [D]
      simp_rw [pv_std_nat]
      exact pv_geom (Y+1) hv z.val_lt
    · intro _ _ _; positivity
  have hsq : 0<Real.sqrt (q:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  apply (le_of_mul_le_mul_right ?_ hsq)
  calc
    _ = ‖(∑ n∈Finset.range (Y+1), χ (n:ZMod q))*G‖ := by rw [norm_mul,hG,hsum]
    _ ≤ 4*(q:ℝ)*Real.log (2*(q:ℝ)) := by
      rw [hexp]
      exact (norm_sum_le _ _).trans (he.le.trans (H.trans (pv_harmonic hq)))
    _ = _ := by
      have hh := congrArg (fun t : ℝ => 4*t*Real.log (2*(q:ℝ))) (Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) q))
      nlinarith only [hh]

end FareyGoldbach
