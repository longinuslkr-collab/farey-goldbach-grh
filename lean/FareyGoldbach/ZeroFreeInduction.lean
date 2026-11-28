import FareyGoldbach.ZeroFreeLocal
import FareyGoldbach.PrimeSums

/-! # The logarithmic derivative under a change of level -/

open Complex Filter
open scoped Topology Classical

namespace FareyGoldbach

private noncomputable def levelEuler {q : ℕ} (ψ : DirichletCharacter ℂ q) (p : ℕ)
    (s : ℂ) : ℂ :=
  1 - ψ (p : ZMod q) * (p : ℂ) ^ (-s)

private theorem levelEuler_hasDerivAt {q : ℕ} (ψ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) (s : ℂ) :
    HasDerivAt (levelEuler ψ p)
      (ψ (p : ZMod q) * (p : ℂ) ^ (-s) * (Real.log (p : ℝ) : ℂ)) s := by
  have hp₀ : (p:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h := ((hasDerivAt_id s).neg.const_cpow (c := (p:ℂ)) (Or.inl hp₀)).const_mul
    (ψ (p : ZMod q))
  have H := (hasDerivAt_const s (1:ℂ)).sub h
  convert H using 1
  · rfl
  · rw [←Complex.natCast_log]
    simp only [Pi.neg_apply,id_eq]
    ring

private theorem norm_euler_sub_le {q p : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q)
    (hp : p.Prime) {s : ℂ} (hs : 1<s.re) :
    ‖ψ (p : ZMod q) * (p : ℂ)^(-s)‖ ≤ (p : ℝ)⁻¹ := by
  rw [norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) (ψ.norm_le_one _)).trans
  rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (by simp only [neg_re]; linarith),
    neg_re,←Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hp.one_le) (by linarith)

private theorem norm_levelEuler_ge {q p : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q)
    (hp : p.Prime) {s : ℂ} (hs : 1<s.re) :
    (1:ℝ)/2 ≤ ‖levelEuler ψ p s‖ := by
  have hsmall := (norm_euler_sub_le ψ hp hs).trans (show (p:ℝ)⁻¹≤1/2 by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) (Nat.cast_le.mpr hp.two_le))
  have h := norm_sub_norm_le (1:ℂ) (ψ (p : ZMod q) * (p : ℂ)^(-s))
  simp only [norm_one] at h
  unfold levelEuler
  linarith only [h,hsmall]

private theorem norm_logDeriv_levelEuler_le {q p : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q)
    (hp : p.Prime) {s : ℂ} (hs : 1<s.re) :
    ‖logDeriv (levelEuler ψ p) s‖ ≤ Real.log (p:ℝ) := by
  have hlog : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hp.one_le)
  have hsmall := (norm_euler_sub_le ψ hp hs).trans (show (p:ℝ)⁻¹≤1/2 by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) (Nat.cast_le.mpr hp.two_le))
  have hE := norm_levelEuler_ge ψ hp hs
  rw [logDeriv_apply,(levelEuler_hasDerivAt ψ hp s).deriv,norm_div,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hlog]
  apply (div_le_iff₀ (by linarith only [hE])).mpr
  calc
    _ ≤ (1/2:ℝ)*Real.log (p:ℝ) := mul_le_mul_of_nonneg_right hsmall hlog
    _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hE hlog

/-- The Euler factors removed from a character under induction contribute
at most the logarithm of its new modulus to the logarithmic derivative. -/
theorem norm_negLogDerivL_changeLevel_sub_le_log {q d : ℕ} [NeZero q] [NeZero d]
    (hqd : q ∣ d) (ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1<s.re) :
    ‖negLogDerivL (DirichletCharacter.changeLevel hqd ψ) s - negLogDerivL ψ s‖ ≤
      Real.log (d:ℝ) := by
  classical
  let E (z : ℂ) := ∏ p ∈ d.primeFactors, levelEuler ψ p z
  have hs1 : s≠1 := by
    intro h
    simp [h] at hs
  have hE (p : ℕ) (hp : p ∈ d.primeFactors) : levelEuler ψ p s ≠ 0 := by
    have := norm_levelEuler_ge ψ (Nat.prime_of_mem_primeFactors hp) hs
    intro h
    rw [h,norm_zero] at this
    norm_num at this
  have hdE (p : ℕ) (hp : p ∈ d.primeFactors) : DifferentiableAt ℂ (levelEuler ψ p) s :=
    (levelEuler_hasDerivAt ψ (Nat.prime_of_mem_primeFactors hp) s).differentiableAt
  have hE₀ : E s≠0 := Finset.prod_ne_zero_iff.mpr hE
  have hEd : DifferentiableAt ℂ E s := DifferentiableAt.fun_finsetProd hdE
  have hL : ψ.LFunction s≠0 := ψ.LFunction_ne_zero_of_one_le_re (Or.inr hs1) hs.le
  have he : (DirichletCharacter.changeLevel hqd ψ).LFunction =ᶠ[𝓝 s]
      (fun z => ψ.LFunction z * E z) := by
    filter_upwards [eventually_ne_nhds hs1] with z hz
    exact DirichletCharacter.LFunction_changeLevel hqd ψ (Or.inr hz)
  have hld := (logDeriv_congr_nhds he).eq_of_nhds
  rw [logDeriv_fun_mul s hL hE₀ (ψ.differentiableAt_LFunction _ (Or.inl hs1)) hEd] at hld
  have hx : ∀ {k : ℕ} [NeZero k] (φ : DirichletCharacter ℂ k),
      negLogDerivL φ s = -logDeriv φ.LFunction s := by
    intros
    simp only [negLogDerivL,logDeriv_apply,neg_div]
  have hprod : logDeriv E s = ∑ p ∈ d.primeFactors, logDeriv (levelEuler ψ p) s :=
    logDeriv_fun_prod hE hdE
  have hlog : ∑ p ∈ d.primeFactors, Real.log (p:ℝ) ≤ Real.log (d:ℝ) := by
    rw [←Real.log_prod (fun _ hp => Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero)]
    apply Real.log_le_log (Finset.prod_pos (fun _ hp =>
      Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos))
    rw [←Nat.cast_prod]
    exact Nat.cast_le.mpr (Nat.le_of_dvd (NeZero.pos d) (Nat.prod_primeFactors_dvd d))
  rw [hx,hx,hld,show ∀ a b : ℂ, -(a+b) - -a = -b by intros; ring,norm_neg,hprod]
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun p hp =>
    norm_logDeriv_levelEuler_le ψ (Nat.prime_of_mem_primeFactors hp) hs).trans hlog)

theorem norm_negLogDerivL_changeLevel_sub_le {q d : ℕ} [NeZero q] [NeZero d]
    (hqd : q ∣ d) (ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1<s.re) :
    ‖negLogDerivL (DirichletCharacter.changeLevel hqd ψ) s - negLogDerivL ψ s‖ ≤
      2*Real.log (2*(d:ℝ)) := by
  have hd : (1:ℝ)≤d := Nat.one_le_cast.mpr (NeZero.pos d)
  have hlog := Real.log_le_log (show (0:ℝ)<d by positivity) (show (d:ℝ)≤2*d by linarith)
  have hlog₀ := Real.log_nonneg (show (1:ℝ)≤2*d by linarith)
  exact (norm_negLogDerivL_changeLevel_sub_le_log hqd ψ hs).trans (by linarith)

/-- The pole and logarithmic error also control the logarithmic derivative
of an induced character. -/
theorem zeroFree_induced_logDeriv_upper :
    ∃ C : ℝ, 0<C ∧ ∀ (d : ℕ) [NeZero d] (ψ : DirichletCharacter ℂ d) (σ t : ℝ),
      1<σ → σ≤2 →
      (negLogDerivL ψ ((σ:ℂ)+(t:ℂ)*I)).re ≤
        (if ψ=1 then ((1:ℂ)/((σ:ℂ)+(t:ℂ)*I-1)).re else 0) +
          C*Real.log (2*(d:ℝ)*(2+|t|)) := by
  classical
  refine ⟨812001,by norm_num,?_⟩
  intro d _ ψ σ t hσ hσ'
  let _ : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero⟩
  let φ := ψ.primitiveCharacter
  let s := zeroFreePoint σ t
  have hφ : φ.IsPrimitive := ψ.primitiveCharacter_isPrimitive
  have hc : DirichletCharacter.changeLevel ψ.conductor_dvd_level φ = ψ :=
    ψ.changeLevel_primitiveCharacter
  have hcp := DirichletCharacter.changeLevel_eq_one_iff (χ:=φ) ψ.conductor_dvd_level
  have hp : ψ=1 ↔ φ=1 :=
    ⟨fun h => hcp.mp (hc.trans h),fun h => hc.symm.trans (hcp.mpr h)⟩
  have hd : (0:ℝ)<d := Nat.cast_pos.mpr (NeZero.pos d)
  have hq : (0:ℝ)<ψ.conductor := Nat.cast_pos.mpr (NeZero.pos _)
  have hQ : (ψ.conductor:ℝ)≤d :=
    Nat.cast_le.mpr (Nat.le_of_dvd (NeZero.pos d) ψ.conductor_dvd_level)
  have hlog : Real.log (2*(ψ.conductor:ℝ)*(2+|t|)) ≤
      Real.log (2*(d:ℝ)*(2+|t|)) := by
    apply Real.log_le_log (by positivity)
    gcongr
  have hlog' : Real.log (d:ℝ) ≤ Real.log (2*(d:ℝ)*(2+|t|)) := by
    apply Real.log_le_log (by positivity)
    have ht : (0:ℝ)≤|t| := abs_nonneg _
    nlinarith only [ht,hd,mul_nonneg hd.le ht]
  have hcor := norm_negLogDerivL_changeLevel_sub_le_log ψ.conductor_dvd_level φ
    (s:=s) (by simpa [s] using hσ)
  rw [hc] at hcor
  have hs₀ := (Complex.re_le_norm _).trans hcor
  have hφ₀ := zeroFree_primitive_logDeriv_upper hφ σ t hσ hσ'
  change (negLogDerivL ψ s).re ≤ _
  simp only [Complex.sub_re] at hs₀
  rw [←hp] at hφ₀
  dsimp only [s,zeroFreePoint] at hs₀ ⊢
  linarith only [hs₀,hφ₀,hlog',mul_le_mul_of_nonneg_left hlog
    (show (0:ℝ)≤812000 by norm_num)]

end FareyGoldbach
