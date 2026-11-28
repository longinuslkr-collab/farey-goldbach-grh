import FareyGoldbach.BVMeanAbel

/-! # Removing logarithmic weights and higher prime powers -/

open Finset
open scoped Classical

namespace FareyGoldbach

/-- The reciprocal log, held constant up to the square root of the terminal cutoff. -/
noncomputable def bvPrimeWeight (N i : ℕ) : ℝ :=
  (Real.log (max (Real.sqrt N) (i:ℝ)))⁻¹

theorem bvWeight_bounds {N : ℕ} (hN : 2≤Real.log (N:ℝ)) :
    (∀ i, 0≤bvPrimeWeight N i ∧ bvPrimeWeight N i≤1) ∧
    Antitone (bvPrimeWeight N) ∧ bvPrimeWeight N 0=2/Real.log (N:ℝ) := by
  have hs : 1≤Real.log (Real.sqrt N) := by rw [Real.log_sqrt (Nat.cast_nonneg _)]; linarith
  have hroot : 0<Real.sqrt (N:ℝ) := by
    by_contra! h
    rw [le_antisymm h (Real.sqrt_nonneg _),Real.log_zero] at hs
    norm_num at hs
  have hl (i : ℕ) : 1≤Real.log (max (Real.sqrt N) (i:ℝ)) :=
    hs.trans (Real.log_le_log hroot (le_max_left ..))
  refine ⟨fun i => ⟨inv_nonneg.mpr (zero_le_one.trans (hl i)),inv_le_one_of_one_le₀ (hl i)⟩,?_,?_⟩
  · intro i j hij
    exact inv_anti₀ (zero_lt_one.trans_le (hl i)) (Real.log_le_log
      (hroot.trans_le (le_max_left ..)) (max_le_max_left _ (Nat.cast_le.mpr hij)))
  · rw [bvPrimeWeight,Nat.cast_zero,max_eq_left (Real.sqrt_nonneg _),Real.log_sqrt (Nat.cast_nonneg _)]
    ring

private theorem bvPrimes_eq (N : ℕ) : (Icc 1 N).filter Nat.Prime=N.primesLE := by
  ext n
  simp only [mem_filter,mem_Icc,Nat.mem_primesLE]
  exact ⟨fun h => ⟨h.1.2,h.2⟩, fun h => ⟨⟨h.2.pos,h.1⟩,h.2⟩⟩

theorem bv_range_mangoldt (n : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (∑ i∈range (n+1),(ArithmeticFunction.vonMangoldt i:ℂ)*χ i) =
    ∑ i∈Icc 1 n,(ArithmeticFunction.vonMangoldt i:ℂ)*χ i := by
  have hh : range (n+1) = insert 0 (Icc 1 n) := by ext i; simp; omega
  rw [hh,sum_insert (by simp)]
  simp

theorem bvPrimeWeight_approx {N q : ℕ} (χ : DirichletCharacter ℂ q)
    (hN : 2≤Real.log (N:ℝ)) (hNnat : 1≤N) :
    ‖(∑ p∈N.primesLE,χ p)-
      ∑ i∈range (N+1),bvPrimeWeight N i • ((ArithmeticFunction.vonMangoldt i:ℂ)*χ i)‖
    ≤ Real.sqrt N + 2*Real.sqrt N*Real.log N := by
  let w := bvPrimeWeight N
  let f (i : ℕ) := w i • ((ArithmeticFunction.vonMangoldt i:ℂ)*χ i)
  have hw := (bvWeight_bounds hN).1
  have hloge : 0<Real.log (Real.sqrt N) := by rw [Real.log_sqrt (Nat.cast_nonneg _)]; linarith
  have hprime (p : ℕ) (hp : p.Prime) : ‖χ p-f p‖ ≤ (if (p:ℝ)≤Real.sqrt N then 1 else 0) := by
    have hpR : 0<(p:ℝ) := Nat.cast_pos.mpr hp.pos
    have hpl : 0<Real.log (p:ℝ) := Real.log_pos (Nat.one_lt_cast.mpr hp.two_le)
    have he : χ p-f p = (1-w p*Real.log p) • χ p := by
      change χ p-(w p:ℂ)*((ArithmeticFunction.vonMangoldt p:ℂ)*χ p) =
        ((1-w p*Real.log p : ℝ):ℂ)*χ p
      rw [ArithmeticFunction.vonMangoldt_apply_prime hp, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_one]
      ring
    rw [he,norm_smul,Real.norm_eq_abs]
    by_cases ht : (p:ℝ)≤Real.sqrt N
    · rw [ite_eq_left ht]
      have hle : w p*Real.log p≤1 := by
        dsimp [w,bvPrimeWeight]
        rw [max_eq_left ht,inv_mul_le_iff₀ hloge,mul_one]
        exact Real.log_le_log hpR ht
      rw [abs_of_nonneg (sub_nonneg.mpr hle)]
      have hpos : 0≤w p*Real.log p := mul_nonneg (hw p).1 hpl.le
      exact (mul_le_mul_of_nonneg_left (χ.norm_le_one _) (sub_nonneg.mpr hle)).trans
        (by linarith)
    · rw [ite_eq_right ht]
      have heq : w p*Real.log p=1 := by
        dsimp [w,bvPrimeWeight]
        rw [max_eq_right (le_of_not_ge ht),inv_mul_cancel₀ hpl.ne']
      rw [heq,sub_self,abs_zero,zero_mul]
  have htotal : ‖(∑ p∈N.primesLE,χ p)-(∑ p∈N.primesLE,f p)‖≤Real.sqrt N := by
    rw [←sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply (sum_le_sum (fun p hp => hprime p (Nat.mem_primesLE.mp hp).2)).trans
    rw [←Finset.sum_filter]
    have hsub : N.primesLE.filter (fun p : ℕ => (p:ℝ)≤Real.sqrt N) ⊆ Icc (1:ℕ) ⌊Real.sqrt N⌋₊ := by
      intro p hp
      obtain ⟨hp,hle⟩ := mem_filter.mp hp
      exact mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hp).2.pos,Nat.le_floor hle⟩
    simpa using (Nat.cast_le.mpr (card_le_card hsub) : (_:ℝ)≤_).trans
      (show ((Icc 1 ⌊Real.sqrt (N:ℝ)⌋₊).card:ℝ)≤Real.sqrt N by
        simpa using Nat.floor_le (Real.sqrt_nonneg (N:ℝ)))
  have hS := Finset.sum_filter_add_sum_filter_not (Icc 1 N) Nat.Prime f
  rw [bvPrimes_eq] at hS
  have hrange : (∑ i∈range (N+1),f i)= ∑ i∈Icc 1 N,f i := by
    have hh : range (N+1) = insert 0 (Icc 1 N) := by ext i; simp; omega
    rw [hh,sum_insert (by simp)]
    simp [f]
  change ‖_ - ∑ i∈range (N+1),f i‖ ≤ _
  rw [hrange,←hS,sub_add_eq_sub_sub]
  apply (norm_sub_le ..).trans
  apply add_le_add htotal
  apply (norm_sum_le _ _).trans
  have hh (i : ℕ) : ‖f i‖≤ArithmeticFunction.vonMangoldt i := by
    rw [show f i = w i • ((ArithmeticFunction.vonMangoldt i:ℂ)*χ i) from rfl,
      norm_smul,Real.norm_eq_abs,abs_of_nonneg (hw i).1,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have hχ := mul_le_mul_of_nonneg_left (χ.norm_le_one i) (ArithmeticFunction.vonMangoldt_nonneg (n:=i))
    exact (mul_le_of_le_one_left (by positivity) (hw i).2).trans (by simpa using hχ)
  apply (sum_le_sum (fun i _ => hh i)).trans
  have h := Chebyshev.psi_sub_theta_eq_sum_not_prime (N:ℝ)
  have hei : Ioc 0 N = Icc 1 N := by ext n; simp; omega
  rw [Nat.floor_natCast, hei] at h
  exact h.symm.le.trans (Chebyshev.psi_sub_theta_le (Nat.one_le_cast.mpr hNnat))

theorem bvPrime_average_le {N D : ℕ} {B : ℝ}
    (hl : 2≤Real.log (N:ℝ)) (hn : 1≤N)
    (hB : ∀ X≤N, (∑ q ∈ Ico 2 D, chenPrimitiveNorm q (fun χ =>
      ∑ n ∈ Icc 1 X, (ArithmeticFunction.vonMangoldt n:ℂ)*χ n)/(q:ℝ)) ≤ B) :
    bvPrimitiveAverage D (fun _ χ => ‖∑ p∈N.primesLE, χ p‖) ≤
      2/Real.log (N:ℝ)*B + (D:ℝ)*(Real.sqrt N+2*Real.sqrt N*Real.log N) := by
  let f (n q : ℕ) (χ : DirichletCharacter ℂ q) := (ArithmeticFunction.vonMangoldt n:ℂ)*χ n
  let T (q : ℕ) (χ : DirichletCharacter ℂ q) := ∑ i∈range (N+1),bvPrimeWeight N i • f i q χ
  let K := Real.sqrt N+2*Real.sqrt N*Real.log N
  have hk : 0≤K := by
    dsimp only [K]
    have hlog : 0≤Real.log (N:ℝ) := by linarith only [hl]
    positivity
  have hval (q : ℕ) (χ : DirichletCharacter ℂ q) :
      ‖∑ p∈N.primesLE, χ p‖ ≤ ‖T q χ‖+K := by
    have h := bvPrimeWeight_approx χ hl hn
    have ht : (∑ p∈N.primesLE,χ p) = (∑ p∈N.primesLE,χ p)-T q χ+T q χ := by abel
    calc _ = ‖(∑ p∈N.primesLE,χ p)-T q χ+T q χ‖ := congrArg norm ht
      _ ≤ _ := norm_add_le .. 
      _ ≤ ‖T q χ‖+K := by linarith only [(show ‖(∑ p∈N.primesLE,χ p)-T q χ‖≤K from h)]
  apply (bvPrimitiveAverage_mono (fun q _ χ _ => hval q χ)).trans
  rw [bvPrimitiveAverage_add]
  apply add_le_add _ (bvPrimitiveAverage_const_le D hk)
  have hw := bvWeight_bounds hl
  rw [←hw.2.2]
  apply bvPrimitiveAverage_abel (bvPrimeWeight N) f (fun i => (hw.1 i).1) hw.2.1
  intro X hXN
  dsimp only [f]
  simp_rw [bv_range_mangoldt]
  rw [bvPrimitiveAverage_norm]
  exact hB X hXN

end FareyGoldbach
