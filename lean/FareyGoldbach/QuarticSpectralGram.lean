import FareyGoldbach.PrimitiveSmoothedTwist
import FareyGoldbach.CompactFourierL2

/-! # Gram integral for quartic-weighted zero ordinates -/

open Real Complex Set MeasureTheory
open scoped BigOperators Classical ComplexConjugate FourierTransform

namespace FareyGoldbach

/-- The inner product of the Mellin phases attached to two zero ordinates whose
difference is `τ`. The factor `x⁻¹` comes from two critical-line densities. -/
noncomputable def quarticSpectralGram (τ : ℝ) : ℂ :=
  ∫ x in Ioi (0:ℝ), (quarticBump x : ℂ)^2 * (x:ℂ)^(-1+(τ:ℂ)*I)

private lemma short_quartic_on_unit {x : ℝ} (hx : x ∈ Ioc (0:ℝ) 1) :
    quarticBump x = 16*x^2*(1-x)^2 := by
  rcases hx.2.eq_or_lt with rfl | h
  · norm_num [quarticBump]
  · exact quarticBump_of_mem hx.1 h

theorem quarticSpectralGram_eq (τ : ℝ) :
    quarticSpectralGram τ = 6144 / ((4+(τ:ℂ)*I)*(5+(τ:ℂ)*I)*(6+(τ:ℂ)*I)*
      (7+(τ:ℂ)*I)*(8+(τ:ℂ)*I)) := by
  let s : ℂ := (τ:ℂ)*I
  let f (n : ℕ) (x : ℝ) := (x:ℂ)^(s-1) *
    (Ioc (0:ℝ) 1).indicator (fun z : ℝ ↦ (z:ℂ)^(n:ℂ)) x
  have hmon (n : ℕ) (hn : 0<n) : IntegrableOn (f n) (Ioi 0) ∧
      (∫ x in Ioi (0:ℝ), f n x) = 1/(s+n) :=
    hasMellin_cpow_Ioc (n:ℂ) (by
      simp [s]; exact_mod_cast hn : 0 < s.re+(n:ℂ).re)
  let c : Fin 5 → ℂ := ![1,-4,6,-4,1]
  have hi (j : Fin 5) : IntegrableOn (fun x ↦ c j * f (4+j.val) x) (Ioi 0) :=
    (hmon (4+j.val) (by omega)).1.const_mul (c j)
  have he : quarticSpectralGram τ = 256*∑ j : Fin 5, c j / (s+((4+j.val:ℕ):ℂ)) := by
    rw [show (∑ j : Fin 5, c j / (s+((4+j.val:ℕ):ℂ))) =
      (∫ x in Ioi (0:ℝ), ∑ j : Fin 5, c j*f (4+j.val) x) by
      rw [integral_finsetSum _ (fun j _ ↦ hi j)]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [integral_const_mul,(hmon (4+j.val) (by omega)).2]; ring]
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
    by_cases hm : x ∈ Ioc (0:ℝ) 1
    · simp only [Fin.sum_univ_succ, c, f, Set.indicator_of_mem hm, Complex.cpow_natCast,
        short_quartic_on_unit hm]
      norm_num
      simp only [s]; ring_nf
    · have hz := quarticBump_eq_zero_of_not_mem (x:=x) (fun h ↦ hm ⟨h.1,h.2.le⟩)
      simp [f, hm, hz]
  rw [he]
  have hne (n : ℕ) (hn : 0<n) : (n:ℂ)+s ≠ 0 := by
    intro h; have he := congrArg Complex.re h
    simp [s] at he
    omega
  change _ = 6144/((4+s)*(5+s)*(6+s)*(7+s)*(8+s))
  simp only [Fin.sum_univ_succ,c]
  norm_num
  rw [add_comm s 4,add_comm s 5,add_comm s 6,add_comm s 7,add_comm s 8]
  have h4 : (4:ℂ)+s ≠ 0 := hne 4 (by norm_num)
  have h5 : (5:ℂ)+s ≠ 0 := hne 5 (by norm_num)
  have h6 : (6:ℂ)+s ≠ 0 := hne 6 (by norm_num)
  have h7 : (7:ℂ)+s ≠ 0 := hne 7 (by norm_num)
  have h8 : (8:ℂ)+s ≠ 0 := hne 8 (by norm_num)
  field_simp [h4,h5,h6,h7,h8]
  ring

private lemma gram_factor_norm (a τ : ℝ) :
    ‖(a:ℂ)+(τ:ℂ)*I‖^2 = a^2+τ^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

theorem norm_quarticSpectralGram_le (τ : ℝ) :
    ‖quarticSpectralGram τ‖ ≤ 52/(1+τ^2) := by
  let n (a : ℝ) := ‖(a:ℂ)+(τ:ℂ)*I‖
  have hna (a : ℝ) : a ≤ n a := by
    simpa [n] using Complex.re_le_norm ((a:ℂ)+(τ:ℂ)*I)
  have hns (a : ℝ) (ha : 1 ≤ a) : Real.sqrt (1+τ^2) ≤ n a := by
    apply (Real.sqrt_le_iff).2
    refine ⟨norm_nonneg _, ?_⟩
    dsimp [n]; rw [gram_factor_norm]
    nlinarith [sq_nonneg (a-1)]
  have h45 := mul_le_mul (hna 4) (hna 5) (by norm_num) (norm_nonneg _)
  have h456 := mul_le_mul h45 (hna 6) (by norm_num) (by positivity : 0 ≤ n 4*n 5)
  have h78 := mul_le_mul (hns 7 (by norm_num)) (hns 8 (by norm_num))
    (Real.sqrt_nonneg _) (norm_nonneg _)
  rw [← sq, Real.sq_sqrt (by positivity)] at h78
  have hall := mul_le_mul h456 h78 (by positivity) (by positivity : 0 ≤ n 4*n 5*n 6)
  have hp : 0 < n 4*n 5*n 6*n 7*n 8 := by
    have hx (a : ℝ) (ha : 0 < a) : 0 < n a := ha.trans_le (hna a)
    exact mul_pos (mul_pos (mul_pos (mul_pos (hx 4 (by norm_num)) (hx 5 (by norm_num)))
      (hx 6 (by norm_num))) (hx 7 (by norm_num))) (hx 8 (by norm_num))
  rw [quarticSpectralGram_eq]
  simp only [norm_div, norm_mul]
  norm_num
  change 6144 / (n 4*n 5*n 6*n 7*n 8) ≤ 52/(1+τ^2)
  apply (div_le_div_iff₀ hp (by positivity)).2
  nlinarith only [hall, sq_nonneg τ]

private lemma gram_radius_sum (N : ℕ) :
    ∑ j ∈ Finset.range N, (1:ℝ)/(1+(j:ℝ)^2) ≤ 3 := by
  have h (j : ℕ) : (1:ℝ)/(1+(j:ℝ)^2) ≤ 3*(1/((j:ℝ)+1)-1/((j:ℝ)+2)) := by
    have hdiff : (1:ℝ)/((j:ℝ)+1)-1/((j:ℝ)+2) = 1/(((j:ℝ)+1)*((j:ℝ)+2)) := by
      field_simp; ring
    rw [hdiff, mul_one_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    by_cases hj : j = 0
    · subst j; norm_num
    · have h1 : (1:ℝ) ≤ j := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hj)
      nlinarith [mul_nonneg (by linarith : 0 ≤ (j:ℝ)-1) (by linarith : 0 ≤ 2*(j:ℝ)-1)]
  refine (Finset.sum_le_sum fun j _ ↦ h j).trans ?_
  rw [← Finset.mul_sum]
  have hh := Finset.sum_range_sub' (fun j : ℕ ↦ (1:ℝ)/(j+1)) N
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, div_one] at hh
  have hsub : ∑ j ∈ Finset.range N, (1/((j:ℝ)+1)-1/((j:ℝ)+2)) = 1-1/((N:ℝ)+1) := by
    convert hh using 2 with j
    ring
  rw [hsub]; nlinarith [show 0 ≤ (1:ℝ)/((N:ℝ)+1) by positivity]

private lemma gram_unit_count (hGRH : DirichletGRH) {d : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hp : χ.IsPrimitive) {T : ℝ} (hT : 0 ≤ T)
    (S : Finset ℂ) (u : ℝ)
    (hS : ∀ ρ ∈ S, 0 < ρ.re ∧ entireL χ ρ = 0 ∧ |ρ.im| ≤ T ∧ |ρ.im-u| ≤ 1) :
    ∑ ρ ∈ S, (zeroMult χ ρ : ℝ) ≤ 217*Real.log (2*(d:ℝ)*(T+3)) := by
  have hlog : 0 ≤ Real.log (2*(d:ℝ)*(T+3)) := by
    apply Real.log_nonneg
    have hd : (1:ℝ) ≤ d := Nat.one_le_cast.mpr (NeZero.pos d)
    nlinarith [mul_nonneg (by linarith : 0 ≤ (d:ℝ)-1) hT]
  rcases S.eq_empty_or_nonempty with h | ⟨ζ,hζ⟩
  · simp [h]; positivity
  have hz := hS ζ hζ
  have hu : |u| ≤ T+1 := by
    calc |u| = |u-ζ.im+ζ.im| := by congr 1; ring
      _ ≤ |u-ζ.im|+|ζ.im| := abs_add_le _ _
      _ ≤ T+1 := by rw [abs_sub_comm]; linarith [hz.2.2.1,hz.2.2.2]
  refine (zeroCount_unit hGRH hp u S (fun ρ hρ ↦
    ⟨(hS ρ hρ).1,(hS ρ hρ).2.1,(hS ρ hρ).2.2.2⟩)).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hd : 0 < (d:ℝ) := Nat.cast_pos.mpr (NeZero.pos d)
  exact Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

private lemma gram_radius_count (hGRH : DirichletGRH) {d : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hp : χ.IsPrimitive) {T : ℝ} (hT : 0 ≤ T)
    (S : Finset ℂ) (u : ℝ) (n : ℕ)
    (hS : ∀ ρ ∈ S, 0 < ρ.re ∧ entireL χ ρ = 0 ∧ |ρ.im| ≤ T ∧
      ⌊|ρ.im-u|⌋₊ = n) :
    ∑ ρ ∈ S, (zeroMult χ ρ : ℝ) ≤ 434*Real.log (2*(d:ℝ)*(T+3)) := by
  let p := fun (ρ : ℂ) ↦ u ≤ ρ.im
  have hband (ρ : ℂ) (hρ : ρ ∈ S) : (n:ℝ) ≤ |ρ.im-u| ∧ |ρ.im-u| < n+1 := by
    have hfloor := (hS ρ hρ).2.2.2
    exact ⟨hfloor ▸ Nat.floor_le (abs_nonneg _),hfloor ▸ Nat.lt_floor_add_one _⟩
  have ha := gram_unit_count hGRH hp hT (S.filter p) (u+n) (fun ρ hρ ↦ by
    obtain ⟨hρ,hp⟩ := Finset.mem_filter.mp hρ
    obtain ⟨h₁,h₂,h₃,_⟩ := hS ρ hρ
    refine ⟨h₁,h₂,h₃,?_⟩
    have h := hband ρ hρ
    rw [abs_of_nonneg (sub_nonneg.mpr hp)] at h
    exact abs_le.mpr ⟨by linarith,by linarith⟩)
  have hb := gram_unit_count hGRH hp hT (S.filter (fun ρ ↦ ¬ p ρ)) (u-n) (fun ρ hρ ↦ by
    obtain ⟨hρ,hp⟩ := Finset.mem_filter.mp hρ
    obtain ⟨h₁,h₂,h₃,_⟩ := hS ρ hρ
    refine ⟨h₁,h₂,h₃,?_⟩
    have h := hband ρ hρ
    rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge hp))] at h
    exact abs_le.mpr ⟨by linarith,by linarith⟩)
  have he := Finset.sum_filter_add_sum_filter_not S p (fun ρ ↦ (zeroMult χ ρ : ℝ))
  linarith

theorem quarticSpectralGram_row_le (hGRH : DirichletGRH) {d : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hp : χ.IsPrimitive) {T : ℝ} (hT : 0 ≤ T)
    (S : Finset ℂ) (u : ℝ)
    (hS : ∀ ρ ∈ S, 0 < ρ.re ∧ entireL χ ρ = 0 ∧ |ρ.im| ≤ T) :
    ∑ ρ ∈ S, (zeroMult χ ρ : ℝ) * ‖quarticSpectralGram (ρ.im-u)‖ ≤
      67704*Real.log (2*(d:ℝ)*(T+3)) := by
  let j := fun (ρ : ℂ) ↦ ⌊|ρ.im-u|⌋₊
  let N := S.sup j + 1
  have hmap (ρ) (hρ : ρ ∈ S) : j ρ ∈ Finset.range N :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup hρ))
  rw [← Finset.sum_fiberwise_of_maps_to (s:=S) (t:=Finset.range N) (g:=j) hmap]
  let L := Real.log (2*(d:ℝ)*(T+3))
  have hL : 0 ≤ L := by
    apply Real.log_nonneg
    have hd : (1:ℝ) ≤ d := Nat.one_le_cast.mpr (NeZero.pos d)
    nlinarith [mul_nonneg (by linarith : 0 ≤ (d:ℝ)-1) hT]
  have hrow n : ∑ ρ ∈ S.filter (fun ρ ↦ j ρ = n), (zeroMult χ ρ : ℝ) *
      ‖quarticSpectralGram (ρ.im-u)‖ ≤ (434*52*L)*(1/(1+(n:ℝ)^2)) := by
    let B := S.filter (fun ρ ↦ j ρ = n)
    have hb := gram_radius_count hGRH hp hT B u n (fun ρ hρ ↦ by
      obtain ⟨hρ,hj⟩ := Finset.mem_filter.mp hρ
      exact ⟨(hS ρ hρ).1,(hS ρ hρ).2.1,(hS ρ hρ).2.2,hj⟩)
    calc
      _ ≤ ∑ ρ ∈ B, (zeroMult χ ρ:ℝ)*(52/(1+(n:ℝ)^2)) := Finset.sum_le_sum fun ρ hρ ↦ by
        have hn : (n:ℝ) ≤ |ρ.im-u| := (Finset.mem_filter.mp hρ).2 ▸ Nat.floor_le (abs_nonneg _)
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        refine (norm_quarticSpectralGram_le _).trans ?_
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        have hh := pow_le_pow_left₀ (Nat.cast_nonneg n) hn 2
        rw [sq_abs] at hh; linarith
      _ = (∑ ρ ∈ B, (zeroMult χ ρ:ℝ))*(52/(1+(n:ℝ)^2)) := (Finset.sum_mul ..).symm
      _ ≤ (434*L)*(52/(1+(n:ℝ)^2)) := mul_le_mul_of_nonneg_right hb (by positivity)
      _ = _ := by ring
  refine (Finset.sum_le_sum fun n _ ↦ hrow n).trans ?_
  rw [← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left (gram_radius_sum N) (by positivity : 0 ≤ 434*52*L)
  change _ ≤ 67704*L
  linarith

private noncomputable def gramDensity (s : ℂ) : ℝ → ℂ :=
  (Ioi (0:ℝ)).indicator (fun x ↦ (quarticBump x:ℂ)*(x:ℂ)^(s-1))

private lemma gramDensity_meas (s : ℂ) : Measurable (gramDensity s) := by
  unfold gramDensity
  refine Measurable.indicator ?_ measurableSet_Ioi
  exact (Complex.continuous_ofReal.measurable.comp continuous_quarticBump.measurable).mul
    (Complex.continuous_ofReal.measurable.pow_const _)

private lemma gramDensity_memLp {s : ℂ} (hs : s.re = 1/2) (p : ENNReal) :
    MemLp (gramDensity s) p := by
  refine (memLp_indicator_const (μ:=volume) p measurableSet_Ioc.nullMeasurableSet
    (16:ℝ) (Or.inr (by simp : volume (Ioc (0:ℝ) 1) ≠ ⊤))).mono'
    (gramDensity_meas s).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  by_cases hx : x ∈ Ioc (0:ℝ) 1
  · rw [Set.indicator_of_mem hx, gramDensity, Set.indicator_of_mem (show x ∈ Ioi (0:ℝ) from hx.1)]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (quarticBump_nonneg x),
      Complex.norm_cpow_eq_rpow_re_of_pos hx.1, Complex.sub_re, hs, Complex.one_re]
    have he := Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 (show (-1:ℝ) ≤ 1/2-1 by norm_num)
    rw [Real.rpow_neg_one] at he
    refine (mul_le_mul_of_nonneg_left he (quarticBump_nonneg _)).trans ?_
    rw [short_quartic_on_unit hx, ← div_eq_mul_inv, div_le_iff₀ hx.1]
    have hb : (1-x)^2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) hx.1.le]
    have hb' : x^2 ≤ x := by nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) hx.1.le]
    nlinarith [mul_le_mul_of_nonneg_left hb (sq_nonneg x)]
  · rw [Set.indicator_of_notMem hx]
    by_cases h : x ∈ Ioi (0:ℝ)
    · have hz : quarticBump x = 0 := quarticBump_eq_zero_of_not_mem (fun h ↦ hx ⟨h.1,h.2.le⟩)
      simp [gramDensity,h,hz]
    · simp [gramDensity,h]

private lemma gramDensity_conj (s : ℂ) (x : ℝ) :
    conj (gramDensity s x) = gramDensity (conj s) x := by
  by_cases hx : x ∈ Ioi (0:ℝ)
  · have ha : (x:ℂ).arg ≠ π := by
      rw [Complex.arg_ofReal_of_nonneg (le_of_lt hx)]; exact Real.pi_pos.ne
    simp only [gramDensity, Set.indicator_of_mem hx, map_mul, Complex.conj_ofReal]
    have h := Complex.cpow_conj (x:ℂ) (s-1) ha
    simpa only [Complex.conj_ofReal, map_sub, map_one] using
      congrArg (fun z : ℂ ↦ (quarticBump x:ℂ)*z) h.symm
  · simp [gramDensity,hx]

private lemma gramDensity_inner {s z : ℂ} (hs : s.re=1/2) (hz : z.re=1/2) :
    (∫ x, conj (gramDensity s x) * gramDensity z x) = quarticSpectralGram (z.im-s.im) := by
  unfold quarticSpectralGram
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s:=Ioi (0:ℝ))
    (f:=fun x ↦ conj (gramDensity s x)*gramDensity z x) (fun x hx ↦ by simp [gramDensity,hx])]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  rw [gramDensity_conj]
  simp only [gramDensity, Set.indicator_of_mem hx]
  have hpow : (x:ℂ)^(conj s-1) * (x:ℂ)^(z-1) = (x:ℂ)^(-1+((z.im-s.im:ℝ):ℂ)*I) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hx))]
    congr 1
    apply Complex.ext <;> simp [hs,hz] <;> ring
  rw [← hpow]; ring

private theorem gramDensity_fourier (s : ℂ) (lam : ℝ) :
    𝓕 (gramDensity s) (-lam) = quarticKernel lam s := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s:=Ioi (0:ℝ))
    (f:=fun x : ℝ ↦ Complex.exp (↑(-2*π*x*(-lam))*I) • gramDensity s x)
    (fun x hx ↦ by simp [gramDensity,hx])]
  unfold quarticKernel mellin
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  simp only [smul_eq_mul, gramDensity, Set.indicator_of_mem hx, quarticTilted, e]
  push_cast
  ring_nf

private theorem gramDensity_energy {S : Finset ℂ} (hS : ∀ ρ ∈ S, ρ.re=1/2) (a : ℂ → ℂ) :
    (∫ x, ‖∑ ρ ∈ S, a ρ*gramDensity ρ x‖^2) ≤
      ∑ ρ ∈ S, ∑ ζ ∈ S, ‖a ρ‖ * ‖a ζ‖ * ‖quarticSpectralGram (ζ.im-ρ.im)‖ := by
  let F (x : ℝ) := ∑ ρ ∈ S, a ρ*gramDensity ρ x
  let G (ρ ζ : ℂ) (x : ℝ) := conj (a ρ)*a ζ*(conj (gramDensity ρ x)*gramDensity ζ x)
  have hi {ρ ζ : ℂ} (hρ : ρ∈S) (hζ : ζ∈S) : Integrable (G ρ ζ) := by
    have hm := (gramDensity_memLp (s := conj ρ) (by simpa using hS ρ hρ) 2).integrable_mul
      (gramDensity_memLp (hS ζ hζ) 2)
    simpa [G, gramDensity_conj] using hm.const_mul (conj (a ρ)*a ζ)
  have he (x : ℝ) : (‖F x‖^2 : ℂ) = ∑ ρ ∈ S, ∑ ζ ∈ S, G ρ ζ x := by
    rw [← Complex.mul_conj', mul_comm]
    simp only [F, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, G]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro ρ _
    apply Finset.sum_congr rfl; intro ζ _; ring
  have heq : ((∫ x, ‖F x‖^2 : ℝ) : ℂ) =
      ∑ ρ ∈ S, ∑ ζ ∈ S, conj (a ρ)*a ζ*quarticSpectralGram (ζ.im-ρ.im) := by
    rw [← integral_complex_ofReal]
    simp only [Complex.ofReal_pow, he]
    rw [integral_finsetSum S (fun ρ hρ ↦ integrable_finsetSum S fun ζ hζ ↦ hi hρ hζ)]
    refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
    rw [integral_finsetSum S fun ζ hζ ↦ hi hρ hζ]
    apply Finset.sum_congr rfl; intro ζ hζ
    dsimp only [G]
    rw [integral_const_mul, gramDensity_inner (hS ρ hρ) (hS ζ hζ)]
  have hN := congrArg norm heq
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun x ↦ sq_nonneg _)] at hN
  change (∫ x, ‖F x‖^2) ≤ _
  rw [hN]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ _ ↦ (norm_sum_le _ _).trans ?_)
  exact Finset.sum_le_sum fun ζ _ ↦ by simp

private lemma gram_fourier_apply (f : ℝ → ℂ) (t : ℝ) :
    𝓕 f (-t) = ∫ x, e (t*x)*f x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul, e]
  congr 2; push_cast; ring

private lemma gram_fourier_finset (S : Finset ℂ) (a : ℂ → ℂ)
    (hs : ∀ ρ ∈ S, ρ.re = 1/2) (t : ℝ) :
    𝓕 (fun x ↦ ∑ ρ ∈ S, a ρ*gramDensity ρ x) (-t) =
      ∑ ρ ∈ S, a ρ*quarticKernel t ρ := by
  rw [gram_fourier_apply]
  simp only [Finset.mul_sum]
  have hi (ρ : ℂ) (hρ : ρ ∈ S) :
      Integrable (fun x ↦ e (t*x)*(a ρ*gramDensity ρ x)) := by
    have h := (memLp_one_iff_integrable.mp (gramDensity_memLp (hs ρ hρ) 1)).const_mul (a ρ)
    refine h.norm.mono' (((continuous_e_real.comp (continuous_const.mul continuous_id)).measurable.mul
      (measurable_const.mul (gramDensity_meas ρ))).aestronglyMeasurable) ?_
    exact ae_of_all _ fun x ↦ by simp only [norm_mul, norm_e, one_mul]; rfl
  rw [integral_finsetSum S hi]
  refine Finset.sum_congr rfl fun ρ _ ↦ ?_
  rw [← gramDensity_fourier, gram_fourier_apply, ← integral_const_mul]
  apply integral_congr_ae; filter_upwards with x; ring

private lemma gram_low_rep {d Y : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    (hY : 2 ≤ Y) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, 0 < ρ.re ∧ entireL χ ρ = 0 ∧ ρ.re=1/2) (t : ℝ) :
    (∑ ρ ∈ S, zeroTerm χ Y t ρ) =
      𝓕 (fun x ↦ ∑ ρ ∈ S, ((zeroMult χ ρ:ℂ)*((Y:ℝ):ℂ)^ρ)*gramDensity ρ x) (-(t*(Y:ℝ))) := by
  rw [gram_fourier_finset S _ (fun ρ hρ ↦ (hS ρ hρ).2.2)]
  refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
  simp only [zeroTerm,(hS ρ hρ).1,(hS ρ hρ).2.1,and_self,ite_true,
    mellin_scaledTiltedBump_eq (by omega : 1 ≤ Y),mul_assoc]

theorem lowZeroSum_continuous (hGRH : DirichletGRH) {d Y : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hp : χ.IsPrimitive) (hY : 2 ≤ Y) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, 0 < ρ.re ∧ entireL χ ρ=0) :
    Continuous (fun t ↦ ∑ ρ ∈ S, zeroTerm χ Y t ρ) := by
  have hs ρ (hρ : ρ ∈ S) := entireL_re_eq_half_of_eq_zero hGRH hp (hS ρ hρ).1 (hS ρ hρ).2
  have hf := funext (gram_low_rep hY S (fun ρ hρ ↦ ⟨(hS ρ hρ).1,(hS ρ hρ).2,hs ρ hρ⟩))
  rw [hf]
  have hi := memLp_one_iff_integrable.mp (memLp_finsetSum S fun ρ hρ ↦
    (gramDensity_memLp (hs ρ hρ) 1).const_mul ((zeroMult χ ρ:ℂ)*((Y:ℝ):ℂ)^ρ))
  exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hi).comp (continuous_id.mul continuous_const).neg

/-- The bounded spectrum contributes one logarithm per unit-band row and one through the
total zero multiplicity. There is no spacing hypothesis on distinct zeros. -/
theorem lowZeroSum_meanSquare (hGRH : DirichletGRH) {d Y : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hp : χ.IsPrimitive) (hY : 2 ≤ Y) {T ξ : ℝ}
    (hT : 0 ≤ T) (hξ : 0 ≤ ξ) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, 0 < ρ.re ∧ entireL χ ρ=0 ∧ |ρ.im| ≤ T) :
    (∫ t in (-ξ)..ξ, ‖∑ ρ ∈ S, zeroTerm χ Y t ρ‖^2) ≤
      67704*Real.log (2*(d:ℝ)*(T+3))*∑ ρ ∈ S, (zeroMult χ ρ:ℝ) := by
  let a (ρ : ℂ) := (zeroMult χ ρ:ℂ)*((Y:ℝ):ℂ)^ρ
  let F (x : ℝ) := ∑ ρ ∈ S, a ρ*gramDensity ρ x
  let L := Real.log (2*(d:ℝ)*(T+3))
  have hs ρ (hρ : ρ ∈ S) := entireL_re_eq_half_of_eq_zero hGRH hp (hS ρ hρ).1 (hS ρ hρ).2.1
  have hf p : MemLp F p := memLp_finsetSum S fun ρ hρ ↦ (gramDensity_memLp (hs ρ hρ) p).const_mul (a ρ)
  have hYpos : (0:ℝ) < Y := by positivity
  have ha ρ (hρ : ρ∈S) : ‖a ρ‖ = (zeroMult χ ρ:ℝ)*Real.sqrt (Y:ℝ) := by
    dsimp only [a]
    rw [norm_mul,Complex.norm_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hYpos,
      hs ρ hρ,Real.sqrt_eq_rpow]
  have hene := gramDensity_energy hs a
  change (∫ x, ‖F x‖^2) ≤ _ at hene
  have hup : (∫ x, ‖F x‖^2) ≤ (Y:ℝ)*(67704*L)*∑ ρ ∈ S, (zeroMult χ ρ:ℝ) := by
    refine hene.trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro ρ hρ
    rw [ha ρ hρ]
    have hrow := quarticSpectralGram_row_le hGRH hp hT S ρ.im hS
    calc
      _ = ((Y:ℝ)*zeroMult χ ρ) * ∑ ζ ∈ S, (zeroMult χ ζ:ℝ)*‖quarticSpectralGram (ζ.im-ρ.im)‖ := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro ζ hζ; rw [ha ζ hζ]
        have hh := Real.sq_sqrt hYpos.le
        ring_nf; rw [hh]; ring
      _ ≤ ((Y:ℝ)*zeroMult χ ρ)*(67704*L) := mul_le_mul_of_nonneg_left hrow (by positivity)
      _ = _ := by ring
  have hrep t := gram_low_rep hY S (fun ρ hρ ↦ ⟨(hS ρ hρ).1,(hS ρ hρ).2.1,hs ρ hρ⟩) t
  have hi := integrable_fourier_norm_sq (memLp_one_iff_integrable.mp (hf 1)) (hf 2)
  let g (u : ℝ) := ‖𝓕 F u‖^2
  have hscl : Integrable (fun t : ℝ ↦ g (-(Y:ℝ)*t)) := hi.comp_mul_left' (neg_ne_zero.mpr hYpos.ne')
  calc
    _ = ∫ t in (-ξ)..ξ, g (-(Y:ℝ)*t) := by
      apply intervalIntegral.integral_congr; intro t _
      change ‖∑ ρ ∈ S, zeroTerm χ Y t ρ‖^2 = ‖𝓕 F (-(Y:ℝ)*t)‖^2
      rw [hrep,neg_mul,mul_comm (Y:ℝ) t]
    _ ≤ ∫ t, g (-(Y:ℝ)*t) := by
      rw [intervalIntegral.integral_of_le (by linarith : -ξ ≤ ξ)]
      exact setIntegral_le_integral hscl (ae_of_all _ fun _ ↦ sq_nonneg _)
    _ = (Y:ℝ)⁻¹ * ∫ x, ‖F x‖^2 := by
      rw [Measure.integral_comp_mul_left, abs_inv, abs_neg, abs_of_pos hYpos, smul_eq_mul]
      rw [show (∫ u, g u) = ∫ x, ‖F x‖^2 from
        integral_fourier_norm_sq_eq (memLp_one_iff_integrable.mp (hf 1)) (hf 2)]
    _ ≤ _ := by
      refine (mul_le_mul_of_nonneg_left hup (by positivity)).trans_eq ?_
      field_simp [hYpos.ne']; ring

/-- Low-height contribution to the localized mean square, uniform in the conductor. -/
theorem lowZeroBand_meanSquare (hGRH : DirichletGRH) :
    ∃ C : ℝ, 0<C ∧ ∀ {d Y : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d},
      χ.IsPrimitive → ∀ (T : ℕ) (ξ : ℝ), 2 ≤ Y → 1 ≤ T → T ≤ 11*Y → 0 ≤ ξ →
      Continuous (fun t ↦ ∑ ρ ∈ (Finset.Icc (-(T:ℤ)) (T:ℤ)).biUnion (bandZeros χ),
        zeroTerm χ Y t ρ) ∧
      (∫ t in -ξ..ξ, ‖∑ ρ ∈ (Finset.Icc (-(T:ℤ)) (T:ℤ)).biUnion (bandZeros χ),
        zeroTerm χ Y t ρ‖^2) ≤ C*(T:ℝ)*Real.log (2*(d:ℝ)*Y)^2 := by
  refine ⟨500000000,by norm_num,?_⟩
  intro d Y hd χ hp T ξ hY hT hTY hξ
  let B := Finset.Icc (-(T:ℤ)) (T:ℤ)
  let S := B.biUnion (bandZeros χ)
  let L := Real.log (2*(d:ℝ)*Y)
  let M := Real.log (2*(d:ℝ)*((T:ℝ)+1+3))
  have hd1 : (1:ℝ) ≤ d := Nat.one_le_cast.mpr (NeZero.pos d)
  have hY2 : (2:ℝ) ≤ Y := by exact_mod_cast hY
  have hT1 : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hTY' : (T:ℝ) ≤ 11*(Y:ℝ) := by exact_mod_cast hTY
  have hbase : (4:ℝ) ≤ 2*(d:ℝ)*Y := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ (d:ℝ)-1) (Nat.cast_nonneg Y)]
  have hL : 0 ≤ L := Real.log_nonneg (by linarith)
  have hM : 0 ≤ M := by
    apply Real.log_nonneg
    nlinarith [mul_nonneg (by linarith : 0 ≤ (d:ℝ)-1) (Nat.cast_nonneg T)]
  have hML : M ≤ 3*L := by
    have h13 : 13 ≤ (2*(d:ℝ)*Y)^2 := by nlinarith [sq_nonneg (2*(d:ℝ)*Y-4)]
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<13) h13
    rw [Real.log_pow] at hh
    have hcmp : 2*(d:ℝ)*((T:ℝ)+1+3) ≤ 13*(2*(d:ℝ)*Y) := by
      have hh' := mul_le_mul_of_nonneg_left (by linarith : (T:ℝ)+1+3 ≤ 13*Y)
        (by positivity : 0 ≤ 2*(d:ℝ))
      linarith
    have h := Real.log_le_log (by positivity : 0 < 2*(d:ℝ)*((T:ℝ)+1+3)) hcmp
    rw [Real.log_mul (by norm_num : (13:ℝ) ≠ 0)
      (by linarith : 2*(d:ℝ)*Y ≠ 0)] at h
    norm_num at hh
    dsimp [L,M]; linarith
  have hband {k : ℤ} (hk : k∈B) {ρ : ℂ} (hρ : ρ ∈ bandZeros χ k) :
      0 < ρ.re ∧ entireL χ ρ=0 ∧ |ρ.im| ≤ (T:ℝ)+1 := by
    obtain ⟨hz,hz',hl,hu⟩ := (mem_bandZeros_iff hGRH hp).mp hρ
    obtain ⟨hkl,hku⟩ := Finset.mem_Icc.mp hk
    have hlk : -(T:ℝ) ≤ (k:ℝ) := by exact_mod_cast hkl
    have huk : (k:ℝ) ≤ T := by exact_mod_cast hku
    exact ⟨hz,hz',abs_le.mpr ⟨by linarith,by linarith⟩⟩
  have hs ρ (hρ : ρ∈S) : 0 < ρ.re ∧ entireL χ ρ=0 ∧ |ρ.im| ≤ (T:ℝ)+1 := by
    obtain ⟨k,hk,hρ⟩ := Finset.mem_biUnion.mp hρ
    exact hband hk hρ
  refine ⟨lowZeroSum_continuous hGRH hp hY S (fun ρ hρ ↦ ⟨(hs ρ hρ).1,(hs ρ hρ).2.1⟩),?_⟩
  have hmass : ∑ ρ ∈ S, (zeroMult χ ρ:ℝ) ≤ 651*(T:ℝ)*M := by
    have hc : B.card = 2*T+1 := by dsimp [B]; rw [Int.card_Icc]; omega
    change ∑ ρ ∈ B.biUnion _, _ ≤ _
    rw [Finset.sum_biUnion (fun i _ j _ hij ↦ bandZeros_disjoint χ hij)]
    calc
      _ ≤ ∑ _k ∈ B, 217*M := Finset.sum_le_sum fun k hk ↦
        gram_unit_count hGRH hp (by positivity : 0 ≤ (T:ℝ)+1) (bandZeros χ k) k (fun ρ hρ ↦ by
          have h := hband hk hρ
          obtain ⟨_,_,hl,hu⟩ := (mem_bandZeros_iff hGRH hp).mp hρ
          exact ⟨h.1,h.2.1,h.2.2,abs_le.mpr ⟨by linarith,by linarith⟩⟩)
      _ = ((2*(T:ℝ)+1)*217)*M := by simp [hc,nsmul_eq_mul]; ring
      _ ≤ _ := by apply mul_le_mul_of_nonneg_right _ hM; linarith
  have he := lowZeroSum_meanSquare hGRH hp hY (by positivity : 0≤(T:ℝ)+1) hξ S hs
  refine he.trans ?_
  change 67704*M * _ ≤ 500000000*(T:ℝ)*L^2
  refine (mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ 67704*M)).trans ?_
  have hh := pow_le_pow_left₀ hM hML 2
  have hh' := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg T)
  nlinarith [mul_nonneg (Nat.cast_nonneg T) (sq_nonneg L)]

end FareyGoldbach
