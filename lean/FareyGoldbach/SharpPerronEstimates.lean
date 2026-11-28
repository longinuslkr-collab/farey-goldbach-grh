import FareyGoldbach.SharpPerronInversion
import FareyGoldbach.SharpPerronZeroSum

/-! # Bounds for the zero sum and the vertical integrals of the sharp Perron kernel -/

open Filter MeasureTheory Set
open scoped Topology

namespace FareyGoldbach

theorem scaledSharpPerronKernel_differentiableOn {X : ℕ} (hX : 2≤X) :
    DifferentiableOn ℂ (scaledSharpPerronKernel X) {s : ℂ | 0<s.re} :=
  fun _ hs => (differentiableAt_scaledSharpPerronKernel hX hs).differentiableWithinAt

private theorem sharp_kernel_log_bound {X d : ℕ} [NeZero d] (hX : 2≤X)
    {s : ℂ} (hσ : 1/4≤s.re) (hσ₂ : s.re≤2)
    {x : ℝ} (hx : 0≤x) (hγ : x≤|s.im|+1) :
    ‖sharpPerronKernel (sharpPerronWidth X) s‖ * Real.log (2*(d:ℝ)*(2+x)) ≤
      500000*Real.log (2*(d:ℝ)*(X:ℝ))*sharpPerronMajorant (sharpPerronHeight X) x := by
  let T := sharpPerronHeight X
  let L := Real.log (2*(d:ℝ)*(X:ℝ))
  let b := 1+|s.im|
  let a := 1+x
  have hT : 0<T := by dsimp [T,sharpPerronHeight]; positivity
  have ha : 0<a := by dsimp [a]; positivity
  have hb : 0<b := by dsimp [b]; positivity
  have hab : a≤2*b := by dsimp [a,b]; linarith only [hγ, abs_nonneg s.im]
  have hL : 0≤L := zero_le_one.trans (sharpPerron_log_ge_one hX)
  have hℓ : 0≤Real.log (2*(d:ℝ)*(2+x)) := by
    have hh := one_le_log_two_mul_d_mul d x
    rw [abs_of_nonneg hx] at hh
    linarith only [hh]
  have hδ := sharpPerronWidth_pos hX
  have hδ₁ := (sharpPerronWidth_le_quarter hX).trans (by norm_num : (1:ℝ)/4≤1)
  have hK := sharpPerronKernel_norm_le_min_height hδ hδ₁ hσ hσ₂
  have hs := sharpPerron_log_split (d:=d) hX hx
  have hab₁ : 1/b≤2/a := by
    calc _ = 2/(2*b) := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) ha hab
  have hab₃ : 1/(sharpPerronWidth X^2*b^3)≤8*T^2/a^3 := by
    calc _ = 8*T^2/(2*b)^3 := by
              dsimp [sharpPerronWidth]
              change 1/((1/T)^2*b^3)=_
              field_simp [hT.ne',hb.ne']
              norm_num
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (pow_pos ha 3)
        (pow_le_pow_left₀ ha.le hab 3)
  by_cases hxT : x≤T
  · rw [sharpPerronMajorant_of_le (by rwa [abs_of_nonneg hx]), abs_of_nonneg hx]
    have hK' : ‖sharpPerronKernel (sharpPerronWidth X) s‖ ≤ 12500*(2/a) :=
      hK.trans (mul_le_mul_of_nonneg_left ((min_le_left _ _).trans hab₁) (by norm_num))
    calc _ ≤ (12500*(2/a))*(3*L) := mul_le_mul hK' (hs.1 hxT) hℓ (by positivity)
      _ = 75000*L*(1/a) := by ring
      _ ≤ 500000*L*(1/a) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num) hL) (by positivity)
  · have hxT' : T≤x := le_of_not_ge hxT
    rw [sharpPerronMajorant_of_ge (by rwa [abs_of_nonneg hx]), abs_of_nonneg hx]
    have hK' : ‖sharpPerronKernel (sharpPerronWidth X) s‖ ≤ 12500*(8*T^2/a^3) :=
      hK.trans (mul_le_mul_of_nonneg_left ((min_le_right _ _).trans hab₃) (by norm_num))
    calc _ ≤ (12500*(8*T^2/a^3))*(4*L*(a/T)) :=
           mul_le_mul hK' (hs.2 hxT') hℓ (by positivity)
      _ = 400000*L*(T/a^2) := by field_simp [ha.ne',hT.ne']; ring
      _ ≤ 500000*L*((1+T)/a^2) := mul_le_mul
        (mul_le_mul_of_nonneg_right (by norm_num) hL)
        (div_le_div_of_nonneg_right (by linarith) (sq_nonneg _))
        (by positivity) (by positivity)

private theorem kernel_mul_log_scaled {X d : ℕ} [NeZero d] (hX : 2≤X)
    {s : ℂ} (hσ : 1/4≤s.re) (hhalf : s.re≤1/2)
    {x : ℝ} (hx : 0≤x) (hx' : x≤|s.im|+1) :
    ‖scaledSharpPerronKernel X s‖ * Real.log (2*(d:ℝ)*(2+x)) ≤
      (Real.sqrt (X:ℝ) * 500000 * Real.log (2*(d:ℝ)*(X:ℝ))) *
        sharpPerronMajorant (sharpPerronHeight X) x := by
  have hxr : (1:ℝ)≤X := Nat.one_le_cast.mpr (by omega)
  have hK := sharp_kernel_log_bound (d:=d) hX hσ (hhalf.trans (by norm_num)) hx hx'
  have hlog : 0≤Real.log (2*(d:ℝ)*(2+x)) := by
    have hh := one_le_log_two_mul_d_mul d x
    rw [abs_of_nonneg hx] at hh
    linarith only [hh]
  rw [scaledSharpPerronKernel,norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hxr)]
  have hpow : (X:ℝ)^s.re≤Real.sqrt (X:ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hxr hhalf
  calc _ = (X:ℝ)^s.re *
        (‖sharpPerronKernel (sharpPerronWidth X) s‖ * Real.log (2*(d:ℝ)*(2+x))) := by ring
    _ ≤ Real.sqrt (X:ℝ) *
        (500000*Real.log (2*(d:ℝ)*(X:ℝ))*sharpPerronMajorant (sharpPerronHeight X) x) :=
          mul_le_mul hpow hK (by positivity) (by positivity)
    _ = _ := by ring

theorem sharpPerron_zero_bound (hGRH : DirichletGRH) {d X : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) (hX : 2≤X) :
    Summable (fun ρ => ‖kernelZeroTerm χ (scaledSharpPerronKernel X) ρ‖) ∧
      (∑' ρ, ‖kernelZeroTerm χ (scaledSharpPerronKernel X) ρ‖) ≤
        1000000000*Real.sqrt (X:ℝ)*Real.log (2*(d:ℝ)*(X:ℝ))^2 := by
  let T := sharpPerronHeight X
  let L := Real.log (2*(d:ℝ)*(X:ℝ))
  let A := Real.sqrt (X:ℝ)*500000*L
  have hT : 0≤T := by dsimp [T,sharpPerronHeight]; positivity
  have hL : 0≤L := zero_le_one.trans (sharpPerron_log_ge_one hX)
  have hA : 0≤A := by dsimp only [A]; positivity
  have hb (k : ℤ) : 0≤A*sharpPerronMajorant T (k:ℝ) :=
    mul_nonneg hA (sharpPerronMajorant_nonneg hT _)
  have hsum := (sharpPerronMajorant_int_summable hT).mul_left A
  have hB (k : ℤ) (ρ : ℂ) (hρ : ρ∈bandZeros χ k) :
      ‖scaledSharpPerronKernel X ρ‖*Real.log (2*(d:ℝ)*(2+|(k:ℝ)|)) ≤
        A*sharpPerronMajorant T (k:ℝ) := by
    obtain ⟨hre,hzero,hk₁,hk₂⟩ := (mem_bandZeros_iff hGRH hprim).mp hρ
    have hs := entireL_re_eq_half_of_eq_zero hGRH hprim hre hzero
    have hk : |(k:ℝ)|≤|ρ.im|+1 := by
      apply abs_le.mpr
      constructor <;> linarith only [hk₁,hk₂, le_abs_self ρ.im, neg_abs_le ρ.im]
    have h := kernel_mul_log_scaled (d:=d) hX (by linarith only [hs]) hs.le (abs_nonneg (k:ℝ)) hk
    simpa only [A,T,L,sharpPerronMajorant,abs_abs] using h
  obtain ⟨h₁,h₂⟩ := kernelZeroTerm_tsum_le_of_bandBound hGRH hprim
    (scaledSharpPerronKernel X) _ hb hsum hB
  refine ⟨h₁,h₂.trans ?_⟩
  simp only [tsum_mul_left]
  have hmass := (sharpPerronMajorant_mass_le (d:=d) hX).2
  calc _ ≤ 217*(A*(9*L)) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmass hA) (by norm_num)
    _ = 976500000*(Real.sqrt (X:ℝ)*L^2) := by dsimp only [A]; ring
    _ ≤ 1000000000*(Real.sqrt (X:ℝ)*L^2) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = _ := by dsimp only [L]; ring

private theorem continuous_negLogDerivL_line {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d)
    {σ : ℝ} (hσ : σ≠1)
    (hn : ∀ u : ℝ, entireL χ ((σ:ℂ)+(u:ℂ)*Complex.I)≠0) :
    Continuous (fun u : ℝ => negLogDerivL χ ((σ:ℂ)+(u:ℂ)*Complex.I)) := by
  refine continuous_iff_continuousAt.mpr fun u => ?_
  have hne : (σ:ℂ)+(u:ℂ)*Complex.I≠1 := fun h => hσ (by simpa using congrArg Complex.re h)
  exact ContinuousAt.comp (f := fun v : ℝ => (σ:ℂ)+(v:ℂ)*Complex.I)
    (g := negLogDerivL χ) (continuousAt_negLogDerivL χ hne (hn u)) (by fun_prop)

theorem sharpPerron_quarter_bound (hGRH : DirichletGRH) {d X : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) (hX : 2≤X) :
    let G := fun u : ℝ => scaledSharpPerronKernel X ((1/4:ℝ)+(u:ℂ)*Complex.I) *
      negLogDerivL χ ((1/4:ℝ)+(u:ℂ)*Complex.I)
    Integrable G ∧ ‖∫ u : ℝ, G u‖ ≤
      4000000000000*Real.sqrt (X:ℝ)*Real.log (2*(d:ℝ)*(X:ℝ))^2 := by
  let s (u : ℝ) : ℂ := ((1/4:ℝ):ℂ)+(u:ℂ)*Complex.I
  let T := sharpPerronHeight X
  let L := Real.log (2*(d:ℝ)*(X:ℝ))
  let A := 812870*(Real.sqrt (X:ℝ)*500000*L)
  let G := fun u : ℝ => scaledSharpPerronKernel X (s u) * negLogDerivL χ (s u)
  have hL : 0≤L := zero_le_one.trans (sharpPerron_log_ge_one hX)
  have hA : 0≤A := by dsimp only [A]; positivity
  have hT : 0≤T := by dsimp [T,sharpPerronHeight]; positivity
  have hre (u : ℝ) : (s u).re=1/4 := by simp [s]
  have hK : Continuous (fun u : ℝ => scaledSharpPerronKernel X (s u)) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    exact (differentiableAt_scaledSharpPerronKernel hX (by rw [hre]; norm_num)).continuousAt.comp
      (g := scaledSharpPerronKernel X) (f := s) (show ContinuousAt s u from by dsimp [s]; fun_prop)
  have hD : Continuous (fun u : ℝ => negLogDerivL χ (s u)) :=
    continuous_negLogDerivL_line χ (by norm_num) (fun u h0 => by
      have h := entireL_re_eq_half_of_eq_zero hGRH hprim (by rw [hre]; norm_num) h0
      linarith only [h,hre u])
  have hb (u : ℝ) : ‖G u‖ ≤ A*sharpPerronMajorant T u := by
    have hq := negLogDeriv_quarter hGRH hprim u
    have h := kernel_mul_log_scaled (d:=d) hX (s:=s u) (by rw [hre]) (by rw [hre]; norm_num)
      (abs_nonneg u) (by simp [s])
    have hp : sharpPerronMajorant T |u|=sharpPerronMajorant T u := by simp [sharpPerronMajorant]
    rw [hp] at h
    dsimp only [G]
    rw [norm_mul]
    calc _ ≤ ‖scaledSharpPerronKernel X (s u)‖ *
          (812870*Real.log (2*(d:ℝ)*(2+|u|))) := mul_le_mul_of_nonneg_left hq (norm_nonneg _)
      _ = 812870*(‖scaledSharpPerronKernel X (s u)‖*Real.log (2*(d:ℝ)*(2+|u|))) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ)≤812870)).trans_eq (by dsimp only [A,L]; ring)
  have hint := (sharpPerronMajorant_integrable hT).const_mul A
  have hG : Integrable G := hint.mono' (hK.mul hD).aestronglyMeasurable (Eventually.of_forall hb)
  refine ⟨hG,?_⟩
  calc ‖∫ u : ℝ, G u‖ ≤ ∫ u : ℝ, ‖G u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ, A*sharpPerronMajorant T u := integral_mono hG.norm hint hb
    _ = A*(∫ u : ℝ, sharpPerronMajorant T u) := integral_const_mul _ _
    _ ≤ A*(8*L) := mul_le_mul_of_nonneg_left (sharpPerronMajorant_mass_le (d:=d) hX).1 hA
    _ = 3251480000000*(Real.sqrt (X:ℝ)*L^2) := by dsimp only [A]; ring
    _ ≤ 4000000000000*(Real.sqrt (X:ℝ)*L^2) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = _ := by dsimp only [L]; ring

theorem sharpPerron_horizontal_decay {X : ℕ} (hX : 2≤X) :
    ∃ A : ℝ, 0≤A ∧ ∀ σ ∈ Set.Icc ((1:ℝ)/4) 2, ∀ u : ℝ,
      ‖scaledSharpPerronKernel X ((σ:ℂ)+(u:ℂ)*Complex.I)‖ ≤ A/(1+|u|)^2 := by
  let T := sharpPerronHeight X
  have hXr : (1:ℝ)≤X := Nat.one_le_cast.mpr (by omega)
  have hT : 0<T := by dsimp [T,sharpPerronHeight]; positivity
  refine ⟨(X:ℝ)^2*12500*T^2,by positivity,?_⟩
  intro σ hσ u
  let s : ℂ := (σ:ℂ)+(u:ℂ)*Complex.I
  let b := 1+|u|
  have hb : 0<b := by dsimp [b]; positivity
  have hre : s.re=σ := by simp [s]
  have him : s.im=u := by simp [s]
  have hδ := sharpPerronWidth_pos hX
  have hδ₁ := (sharpPerronWidth_le_quarter hX).trans (by norm_num : (1:ℝ)/4≤1)
  have hk := sharpPerronKernel_norm_le_min_height (s:=s) hδ hδ₁ (by rw [hre]; exact hσ.1)
    (by rw [hre]; exact hσ.2)
  have hk' : ‖sharpPerronKernel (sharpPerronWidth X) s‖ ≤ 12500*(T^2/b^3) := by
    rw [him] at hk
    apply hk.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    refine (min_le_right _ _).trans_eq ?_
    change 1/((1/T)^2*b^3)=_
    field_simp [hT.ne',hb.ne']
  change ‖scaledSharpPerronKernel X s‖ ≤ _
  rw [scaledSharpPerronKernel,norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hXr),hre]
  have hp : (X:ℝ)^σ≤(X:ℝ)^2 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hXr (by simpa using hσ.2)
  calc _ ≤ (X:ℝ)^2*(12500*(T^2/b^3)) := mul_le_mul hp hk' (norm_nonneg _) (by positivity)
    _ = ((X:ℝ)^2*12500*T^2)/b^3 := by ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hb)
      have hb₁ : 1≤b := by dsimp [b]; linarith only [abs_nonneg u]
      exact (pow_le_pow_right₀ hb₁ (by norm_num : (2:ℕ)≤3))

theorem sharpPerron_two_integrable {d X : ℕ} [NeZero d]
    (χ : DirichletCharacter ℂ d) (hX : 2≤X) :
    Integrable (fun u : ℝ => scaledSharpPerronKernel X (2+(u:ℂ)*Complex.I)) ∧
    Integrable (fun u : ℝ => scaledSharpPerronKernel X (2+(u:ℂ)*Complex.I) *
      negLogDerivL χ (2+(u:ℂ)*Complex.I)) := by
  obtain ⟨A,_,hA⟩ := sharpPerron_horizontal_decay hX
  let s (u : ℝ) : ℂ := 2+(u:ℂ)*Complex.I
  have hK : Continuous (fun u : ℝ => scaledSharpPerronKernel X (s u)) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    exact (differentiableAt_scaledSharpPerronKernel hX (by norm_num [s])).continuousAt.comp
      (g := scaledSharpPerronKernel X) (f := s) (show ContinuousAt s u from by dsimp [s]; fun_prop)
  have hmaj (u : ℝ) : sharpPerronMajorant 0 u = 1/(1+|u|)^2 := by
    rw [sharpPerronMajorant_of_ge (abs_nonneg u),add_zero]
  have hf : Integrable (fun u : ℝ => scaledSharpPerronKernel X (s u)) := by
    refine ((sharpPerronMajorant_integrable (le_rfl : (0:ℝ)≤0)).const_mul A).mono' hK.aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [hmaj]
    simpa only [s,Complex.ofReal_ofNat,mul_one_div] using hA 2 (by constructor <;> norm_num) u
  have hD : Continuous (fun u : ℝ => negLogDerivL χ (s u)) := by
    apply continuous_negLogDerivL_line χ (by norm_num)
    exact entireL_two_add_ne_zero χ
  refine ⟨hf,?_⟩
  let C₂ : ℝ := ∑' n : ℕ, 2/(n:ℝ)^(3/2:ℝ)
  refine (hf.norm.mul_const C₂).mono' ((hK.mul hD).aestronglyMeasurable)
    (Eventually.of_forall fun u => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_negLogDerivL_two_le χ u) (norm_nonneg _)

end FareyGoldbach
