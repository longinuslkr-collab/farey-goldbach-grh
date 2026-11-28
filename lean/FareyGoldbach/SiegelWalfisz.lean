import FareyGoldbach.SmallConductorFiniteRange
import FareyGoldbach.SmallConductorPerron
import FareyGoldbach.SmallConductorRightTail
import FareyGoldbach.SmallConductorPowers
import FareyGoldbach.SmallConductorRectangle
import FareyGoldbach.SmallConductorScales
import FareyGoldbach.SmallConductorZeroFree

/-! # Siegel–Walfisz by one zero-free Perron rectangle -/

open Complex Filter MeasureTheory Set
open scoped Classical Interval

namespace FareyGoldbach

private theorem eventually_smallConductor_vonMangoldt (A B : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → 2≤X → (q:ℝ)≤(Real.log (X:ℝ))^A →
        ‖(∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n:ℂ)*χ (n:ZMod q)) -
          (if χ=1 then (X:ℂ) else 0)‖ ≤ C*(X:ℝ)/(Real.log (X:ℝ))^B := by
  obtain ⟨a,ha,ha₁,hgeom⟩ := eventually_smallConductor_rectangle_geometry A (2*B+12)
  let C₁ := 1626000/a
  let C₂ := 1+812000*Real.log 4
  let J := (((2*(3*B+13)).factorial:ℕ):ℝ)/a^(2*(3*B+13))
  have hC₁ : 0<C₁ := by dsimp only [C₁]; positivity
  have hlog4 : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have hC₂ : 0<C₂ := by dsimp only [C₂]; positivity
  have hJ : 0≤J := by dsimp only [J]; positivity
  let C := 26+(12500*C₂)*3+50000*C₁*(J+3)
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  filter_upwards [hgeom] with X hgeomX
  intro q _ χ hprim hX hq
  let L := Real.log (X:ℝ)
  let δ : ℝ := (L^(B+3))⁻¹
  let T := L^(2*B+12)
  let σ := 1+L⁻¹
  let η := a/Real.sqrt L
  let R := (X:ℝ)/L^B
  have hXp : 0<X := by omega
  have hx : (0:ℝ)<X := Nat.cast_pos.mpr hXp
  obtain ⟨hL,hgeo⟩ := hgeomX
  change 10≤L at hL
  have hL₁ : 1≤L := by linarith only [hL]
  have hLp : 0<L := zero_lt_one.trans_le hL₁
  have hRt : 0≤R := by dsimp only [R]; positivity
  have hsqrt : 0<Real.sqrt L := Real.sqrt_pos.mpr hLp
  have hsqrt₁ : 1≤Real.sqrt L := Real.one_le_sqrt.mpr hL₁
  have hη : 0<η := by dsimp only [η]; positivity
  have hη₁ : η≤1/4 := (div_le_self ha.le hsqrt₁).trans (ha₁.trans (by norm_num))
  have hδ : 0<δ := by dsimp only [δ]; positivity
  have hδ₁ : δ≤1/4 := by
    have hh : (4:ℝ)≤L^(B+3) := (show (4:ℝ)≤L by linarith only [hL]).trans
      (le_self_pow₀ hL₁ (by omega))
    simpa only [one_div] using (inv_le_inv₀ (by positivity) (by norm_num)).mpr hh
  have hσ : 1<σ := lt_add_of_pos_right _ (inv_pos.mpr hLp)
  have hσ₂ : σ≤2 := by
    have hh := inv_le_one_of_one_le₀ hL₁
    dsimp only [σ]
    linarith only [hh]
  have hT : 1≤T := one_le_pow₀ hL₁
  obtain ⟨hheight,hzero⟩ := hgeo q χ hprim hq
  have hmlog : 813000*Real.log (2*(q:ℝ)*(2+T))/η ≤ C₁*L := by
    have ht : |T|≤T+2 := by rw [abs_of_nonneg (by linarith only [hT])]; linarith
    have he := hheight T ht
    rw [abs_of_nonneg (by linarith only [hT])] at he
    calc
      _ ≤ (813000*(2*Real.sqrt L))/η :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num)) hη.le
      _ = C₁*L := by
        dsimp only [η,C₁]
        field_simp
        nlinarith only [Real.sq_sqrt hLp.le]
  have hbd (x t : ℝ) (hx₀ : 1-η≤x) (hx₂ : x≤2) (ht : |t|≤T)
      (hb : x=1-η ∨ |t|=T) :
      ‖negLogDerivL χ ((x:ℂ)+(t:ℂ)*I)‖ ≤ C₁*L := by
    have h := norm_negLogDerivL_le_of_zero_free_strip hprim hη hη₁ hT hzero
      (s:=zeroFreePoint x t) (by simpa only [zeroFreePoint_re] using hx₀)
      (by simpa only [zeroFreePoint_re] using hx₂)
      (by simpa only [zeroFreePoint_im] using ht)
      (by simpa only [zeroFreePoint_re,zeroFreePoint_im] using hb)
    exact h.trans hmlog
  have hrectangle : ∀ s∈Icc (1-η) σ ×ℂ Icc (-T) T, entireL χ s≠0 := by
    intro s hs
    obtain ⟨hr,hi⟩ := Complex.mem_reProdIm.mp hs
    exact hzero s (by linarith only [hr.1,hη]) ((abs_le.mpr hi).trans (by linarith))
  have hrbd (t : ℝ) : ‖negLogDerivL χ ((σ:ℂ)+(t:ℂ)*I)‖ ≤ C₂*L := by
    have h := norm_negLogDerivL_le_inv_add χ σ t hσ hσ₂
    have he : 1/(σ-1)=L := by dsimp only [σ]; rw [add_sub_cancel_left,one_div,inv_inv]
    rw [he] at h
    refine h.trans ?_
    dsimp only [C₂]
    nlinarith only [mul_nonneg hlog4 (sub_nonneg.mpr hL₁)]
  have hδle : δ≤1 := hδ₁.trans (by norm_num)
  have ⟨hleftBudget,htailBudget,hrampBudget,hhorizBudget⟩ :=
    smallConductor_power_budget B hx hL₁ ha
  let v (t : ℝ) := (σ:ℂ)+(t:ℂ)*I
  let f (t : ℝ) := smallConductorKernel X δ (v t)*negLogDerivL χ (v t)
  let S := ∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n:ℂ)*χ (n:ZMod q)
  let W := smallConductorWeightedVonMangoldt χ X δ
  let U := (2*(Real.pi:ℂ))⁻¹*(∫ t in -T..T, f t)
  let P := if χ=1 then smallConductorKernel X δ 1 else 0
  let E := if χ=1 then (X:ℂ) else 0
  have hramp : ‖S-W‖ ≤ 8*R := by
    rw [norm_sub_rev]
    apply (norm_smallConductorWeightedVonMangoldt_sub_sharp_le χ hX hδ hδ₁).trans
    change 8*δ*(X:ℝ)*L ≤ 8*R
    rw [mul_assoc 8 δ,mul_assoc 8]
    exact mul_le_mul_of_nonneg_left hrampBudget (by norm_num)
  have hpole : ‖P-E‖ ≤ 18*R := by
    have h' : δ*(X:ℝ)≤R := (le_mul_of_one_le_right (by positivity) hL₁).trans hrampBudget
    apply le_trans _ (mul_le_mul_of_nonneg_left h' (by norm_num : (0:ℝ)≤18))
    dsimp only [P,E]
    split_ifs
    · rw [←mul_assoc]
      exact norm_smallConductorKernel_at_one_sub_le hXp hδ hδle
    · simp only [sub_self,norm_zero]
      positivity
  have htail : ‖W-U‖ ≤ (12500*C₂)*3*R := by
    have he : W=(2*(Real.pi:ℂ))⁻¹*(∫ t : ℝ, f t) :=
      smallConductorWeightedVonMangoldt_eq_integral χ hXp hδ hδle hσ hσ₂
    rw [he]
    apply (norm_smallConductor_right_tail χ hXp hδ hδle hσ hσ₂ hT
      (mul_nonneg hC₂.le hLp.le) hrbd).trans
    calc
      _ = (12500*C₂)*((X:ℝ)^σ*L/(δ^2*T^2)) := by ring
      _ ≤ (12500*C₂)*(3*R) := mul_le_mul_of_nonneg_left htailBudget (by positivity)
      _ = _ := by ring
  have hrect : ‖U-P‖ ≤ 50000*C₁*(J+3)*R := by
    have hb := smallConductorRectangle_bound χ hX hδ hδle hη hη₁ hσ hσ₂ hT
      (mul_nonneg hC₁.le hLp.le) hrectangle
      (fun t ht => hbd (1-η) t le_rfl (by linarith only [hη]) (abs_le.mpr ht) (Or.inl rfl))
      (fun x hx t ht => hbd x t hx.1 (hx.2.trans hσ₂) ht.le (Or.inr ht))
    apply hb.trans
    calc
      _ = (50000*C₁)*((X:ℝ)^(1-η)*L*T+(X:ℝ)^σ*L/(δ^2*T^3)) := by ring
      _ ≤ (50000*C₁)*(J*R+3*R) :=
        mul_le_mul_of_nonneg_left (add_le_add hleftBudget hhorizBudget) (by positivity)
      _ = _ := by ring
  change ‖S-E‖ ≤ _
  calc
    _ ≤ ‖S-W‖+‖W-U‖+‖U-P‖+‖P-E‖ := by
      have h := norm_sub_le_norm_sub_add_norm_sub S W E
      have h' := norm_sub_le_norm_sub_add_norm_sub W U E
      have h'' := norm_sub_le_norm_sub_add_norm_sub U P E
      linarith only [h,h',h'']
    _ ≤ 8*R+(12500*C₂)*3*R+50000*C₁*(J+3)*R+18*R :=
      add_le_add (add_le_add (add_le_add hramp htail) hrect) hpole
    _ = _ := by dsimp only [C,R,L]; ring

/-- Uniform sharp von Mangoldt estimates at every fixed logarithmic conductor
range. The modulus-one character gives the principal main term. -/
theorem unconditional_smallConductor_vonMangoldt (A B : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ (X q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → 2≤X → (q:ℝ)≤(Real.log (X:ℝ))^A →
      ‖(∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n:ℂ)*χ (n:ZMod q)) -
        (if χ=1 then (X:ℂ) else 0)‖ ≤ C*(X:ℝ)/(Real.log (X:ℝ))^B := by
  obtain ⟨C,hC,H⟩ := eventually_smallConductor_vonMangoldt A B
  exact smallConductorMangoldt_of_eventual hC H

end FareyGoldbach
