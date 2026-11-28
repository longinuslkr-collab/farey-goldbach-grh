import FareyGoldbach.ZeroFreeLocal

/-! # Logarithmic derivative on the boundary of a zero-free rectangle -/

open Complex Metric
open scoped Classical

namespace FareyGoldbach

/-- On the left and horizontal sides of a rectangle, a zero-free strip twice
as wide gives uniform separation from every zero in the local expansion. -/
theorem norm_negLogDerivL_le_of_zero_free_strip {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) {η T : ℝ} (hη : 0<η) (hη' : η≤1/4) (hT : 1≤T)
    (hzero : ∀ z : ℂ, 1-2*η ≤ z.re → |z.im|≤T+2 → entireL χ z≠0)
    {s : ℂ} (hsL : 1-η≤s.re) (hsR : s.re≤2) (hsT : |s.im|≤T)
    (hboundary : s.re=1-η ∨ |s.im|=T) :
    ‖negLogDerivL χ s‖ ≤ 813000*Real.log (2*(q:ℝ)*(2+T))/η := by
  let L := Real.log (2*(q:ℝ)*(2+T))
  let Z := diskZeros χ (2+(s.im:ℂ)*I) (15/8)
  have hqp : (0:ℝ)<q := Nat.cast_pos.mpr (NeZero.pos q)
  have hl : Real.log (2*(q:ℝ)*(2+|s.im|))≤L := by
    dsimp only [L]
    exact Real.log_le_log (by positivity)
      (mul_le_mul_of_nonneg_left (add_le_add_right hsT 2) (by positivity))
  have hL : 1≤L := (one_le_log_two_mul_d_mul q s.im).trans hl
  have hP : η≤‖s-1‖ := by
    rcases hboundary with h | h
    · have h' := Complex.abs_re_le_norm (s-1)
      simpa [Complex.sub_re,h,abs_of_pos hη] using h'
    · have h' := Complex.abs_im_le_norm (s-1)
      simp only [Complex.sub_im,Complex.one_im,sub_zero,h] at h'
      linarith only [hη',hT,h']
  have hne : s≠1 := fun he => by simp [he,not_le.mpr hη] at hP
  have hE := hzero s (by linarith only [hsL,hη]) (by linarith only [hsT])
  have hLne : χ.LFunction s≠0 := by
    rw [entireL_apply_of_ne_one χ hne] at hE
    split at hE
    · exact right_ne_zero_of_mul hE
    · exact hE
  have hmem : s ∈ closedBall (2+(s.im:ℂ)*I) (7/4) := by
    rw [mem_closedBall,dist_eq_norm]
    have he : s-(2+(s.im:ℂ)*I) = ((s.re-2:ℝ):ℂ) := by
      apply Complex.ext <;> simp [Complex.sub_re,Complex.sub_im]
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hsR)]
    linarith only [hη',hsL]
  have hdist (z : ℂ) (hz : z∈Z) : η ≤ ‖s-z‖ := by
    obtain ⟨hm,he⟩ := (mem_diskZeros_iff χ).mp hz
    rw [mem_closedBall,dist_eq_norm] at hm
    have him := (Complex.abs_im_le_norm _).trans hm
    change |(z-zeroFreePoint 2 s.im).im| ≤ 15/8 at him
    rw [Complex.sub_im,zeroFreePoint_im] at him
    have hh : |z.im|≤T+2 := by
      have htri := abs_add_le (z.im-s.im) s.im
      rw [sub_add_cancel] at htri
      linarith only [htri,him,hsT]
    have hleft : z.re < 1-2*η := lt_of_not_ge (fun h => hzero z h hh he)
    have h := le_trans (le_abs_self (s.re-z.re)) (Complex.abs_re_le_norm (s-z))
    linarith only [hleft,hsL,h]
  have hsum : ‖∑ z∈Z,(zeroMult χ z:ℂ)/(s-z)‖ ≤ 217*L/η := by
    calc
      _ ≤ ∑ z∈Z, ‖(zeroMult χ z:ℂ)/(s-z)‖ := norm_sum_le _ _
      _ ≤ ∑ z∈Z, (zeroMult χ z:ℝ)/η := by
        apply Finset.sum_le_sum
        intro z hz
        rw [norm_div,Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hη (hdist z hz)
      _ ≤ _ := by
        rw [← Finset.sum_div]
        exact div_le_div_of_nonneg_right ((diskZeroCount_le hprim s.im).trans
          (mul_le_mul_of_nonneg_left hl (by norm_num))) hη.le
  have hpole : ‖if χ=1 then (1:ℂ)/(s-1) else 0‖ ≤ 1/η := by
    split
    · rw [norm_div,norm_one]
      exact div_le_div_of_nonneg_left zero_le_one hη hP
    · simp; positivity
  have happ := (local_negLogDeriv_approx hprim s.im hmem hne hLne).trans
    (mul_le_mul_of_nonneg_left hl (by norm_num : (0:ℝ)≤812000))
  let P : ℂ := if χ=1 then (1:ℂ)/(s-1) else 0
  let S : ℂ := ∑ z∈Z,(zeroMult χ z:ℂ)/(s-z)
  change ‖negLogDerivL χ s-(P-S)‖≤812000*L at happ
  change ‖P‖≤1/η at hpole
  change ‖S‖≤217*L/η at hsum
  calc
    _ ≤ ‖negLogDerivL χ s-(P-S)‖+‖P-S‖ := norm_le_norm_sub_add ..
    _ ≤ 812000*L+(1/η+217*L/η) := add_le_add happ ((norm_sub_le ..).trans (add_le_add hpole hsum))
    _ ≤ _ := by
      change _ ≤ 813000*L/η
      apply (le_div_iff₀ hη).mpr
      have hcancel₁ : (1/η)*η=1 := div_mul_cancel₀ _ hη.ne'
      have hcancel₂ : (217*L/η)*η=217*L := div_mul_cancel₀ _ hη.ne'
      nlinarith only [hL,mul_nonneg (zero_le_one.trans hL) (sub_nonneg.mpr hη'),hcancel₁,hcancel₂]


/-- On the right of the line of absolute convergence every twisted logarithmic
derivative is majorized by the ordinary zeta logarithmic derivative. -/
theorem norm_negLogDerivL_le_levelOne_re {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) (hσ : 1<σ) :
    ‖negLogDerivL χ (zeroFreePoint σ t)‖ ≤ (negLogDerivL (1:DirichletCharacter ℂ 1) (σ:ℂ)).re := by
  let F (n:ℕ) := χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)
  let G (n:ℕ) := (1:DirichletCharacter ℂ 1) (n:ZMod 1)*(ArithmeticFunction.vonMangoldt n:ℂ)
  let s := zeroFreePoint σ t
  have hs : 1<s.re := by simpa [s] using hσ
  have hF : Summable (LSeries.term F s) := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
  have hG : Summable (LSeries.term G (σ:ℂ)) :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt (1:DirichletCharacter ℂ 1) hσ
  have hGsum := Complex.hasSum_re hG.hasSum
  have hmajor (n : ℕ) : ‖LSeries.term F s n‖ ≤ (LSeries.term G (σ:ℂ) n).re := by
    by_cases h : n=0
    · simp [h]
    have hpr : (1:DirichletCharacter ℂ 1) (n:ZMod 1)=1 := by
      rw [show (n:ZMod 1)=1 from Subsingleton.elim _ _,map_one]
    rw [LSeries.norm_term_eq,ite_eq_right h,LSeries.term_of_ne_zero h]
    have hh : G n / (n:ℂ)^(σ:ℂ) = ((ArithmeticFunction.vonMangoldt n/(n:ℝ)^σ:ℝ):ℂ) := by
      simp only [G,hpr,one_mul,Complex.ofReal_div,Complex.ofReal_cpow (Nat.cast_nonneg _),
        Complex.ofReal_natCast]
    rw [hh,Complex.ofReal_re,show s.re=σ from zeroFreePoint_re σ t]
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
    simp only [F,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)
  have hcomp := hF.norm.tsum_le_tsum hmajor hGsum.summable
  have hnegF := LSeries_twist_vonMangoldt_eq_negLogDerivL χ hs
  have hnegG := LSeries_twist_vonMangoldt_eq_negLogDerivL (1:DirichletCharacter ℂ 1)
      (s:=(σ:ℂ)) hσ
  change (∑' n,LSeries.term F s n)=_ at hnegF
  change (∑' n,LSeries.term G (σ:ℂ) n)=_ at hnegG
  calc
    _ = ‖∑' n,LSeries.term F s n‖ := congrArg norm hnegF.symm
    _ ≤ _ := (norm_tsum_le_tsum_norm hF.norm).trans (hcomp.trans_eq
      (hGsum.tsum_eq.trans (congrArg Complex.re hnegG)))

theorem norm_negLogDerivL_le_inv_add {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) (hσ : 1<σ) (hσ' : σ≤2) :
    ‖negLogDerivL χ (zeroFreePoint σ t)‖ ≤ 1/(σ-1)+812000*Real.log 4 := by
  apply (norm_negLogDerivL_le_levelOne_re χ σ t hσ).trans
  have hb := zeroFree_primitive_logDeriv_upper (χ:=(1:DirichletCharacter ℂ 1))
    DirichletCharacter.isPrimitive_one_level_one σ 0 hσ hσ'
  change (negLogDerivL (1:DirichletCharacter ℂ 1) (zeroFreePoint σ 0)).re ≤
    (if (1:DirichletCharacter ℂ 1)=1 then ((1:ℂ)/(zeroFreePoint σ 0-1)).re else 0) +
    812000*Real.log (2*((1:ℕ):ℝ)*(2+|0|)) at hb
  simp only [ite_true,zeroFree_pole_re] at hb
  simp only [zeroFreePoint,Nat.cast_one,mul_one,abs_zero,add_zero,
    Complex.ofReal_zero,zero_mul,show (2:ℝ)*2=4 by norm_num] at hb
  have hreal : zeroFreeKernel (σ-1) 0 = 1/(σ-1) := by
    unfold zeroFreeKernel
    field_simp [(sub_pos.mpr hσ).ne']
    ring
  rw [hreal] at hb
  exact hb

end FareyGoldbach
