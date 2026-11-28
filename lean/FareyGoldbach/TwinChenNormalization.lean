import FareyGoldbach.ChenAPComparisons
import FareyGoldbach.ChenSwitchingScales

/-! # Singular normalization at the source size of the shifted-prime sieve -/

open Filter Finset
open scoped Topology Classical

namespace FareyGoldbach

/-- The even local obstruction is `2*r`, and the Euler product is taken
through the source size `M`, including the factors at primes not dividing it. -/
noncomputable def twinChenU (M r : ℕ) : ℝ := chenSingularAtCutoff (2*r) (M+1)

theorem twinChenU_ge_half {M : ℕ} (hM : 2≤M) (r : ℕ) : (1:ℝ)/2≤twinChenU M r :=
  chenSingularAtCutoff_ge_half (even_two_mul r) (by omega)

theorem twinChen_singular_cutoff_example :
    chenSingularAtCutoff 2 4=3/2 ∧ chenCanonicalU 2=2 := by
  have h₄ : chenPrimesBelow 4={2,3} := by decide
  have h₃ : chenPrimesBelow 3={2} := by decide
  norm_num [chenCanonicalU,chenSingularAtCutoff,h₄,h₃,localFactor]

private theorem square_tail {w W : ℕ} (hw : 4≤w) (hwW : w≤W) :
    ∑ p∈Ico w W, 1/((p:ℝ)-1)^2≤1/((w:ℝ)-2) := by
  have ht : (∑ p∈Ico w W, 1/((p:ℝ)-1)^2)≤1/((w:ℝ)-2)-1/((W:ℝ)-2) := by
    induction W,hwW using Nat.le_induction with
    | base => simp
    | succ p hp ih =>
      have hpr : (4:ℝ)≤p := by exact_mod_cast hw.trans hp
      have h₀ : 0<(p:ℝ)-2 := by linarith
      have h₁ : 0<(p:ℝ)-1 := by linarith
      have h : 1/((p:ℝ)-1)^2≤1/((p:ℝ)-2)-1/((p:ℝ)-1) := by field_simp; nlinarith
      rw [Finset.sum_Ico_succ_top hp,Nat.cast_succ,show (p:ℝ)+1-2=(p:ℝ)-1 by ring]
      linarith only [h,ih]
  have hWr : (4:ℝ)≤W := by exact_mod_cast hw.trans hwW
  linarith only [ht,one_div_nonneg.mpr (by linarith : 0≤(W:ℝ)-2)]

/-- Once all divisors have entered, the remaining factors are the universal
ones. Their squared-reciprocal tail is uniform in the auxiliary modulus. -/
theorem twinChen_singular_tail {K w W : ℕ} (hK : 0<K) (he : Even K)
    (hKw : K<w) (hw : 4≤w) (hwW : w≤W) :
    |chenSingularAtCutoff K W/chenSingularAtCutoff K w-1|≤
      Real.exp (1/((w:ℝ)-2))-1 := by
  let T := chenPrimesBelow W \ chenPrimesBelow w
  have hsub : chenPrimesBelow w⊆chenPrimesBelow W := by
    intro p hp
    obtain ⟨hI,hp⟩ := mem_filter.mp hp
    obtain ⟨hlo,hhi⟩ := mem_Icc.mp hI
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hlo,by omega⟩,hp⟩
  have hmem {p : ℕ} (hp : p∈T) : p.Prime ∧ p∈Ico w W := by
    obtain ⟨hp₁,hp₂⟩ := mem_sdiff.mp hp
    obtain ⟨hI,hpr⟩ := mem_filter.mp hp₁
    obtain ⟨hlo,hhi⟩ := mem_Icc.mp hI
    have hwp : w≤p := by
      by_contra! hlt
      exact hp₂ (mem_filter.mpr ⟨mem_Icc.mpr ⟨hlo,by omega⟩,hpr⟩)
    exact ⟨hpr,mem_Ico.mpr ⟨hwp,by omega⟩⟩
  have hloc (p : ℕ) (hp : p∈T) :
      ‖localFactor 1 K p‖=1/((p:ℝ)-1)^2 := by
    obtain ⟨hpr,hpI⟩ := hmem hp
    have hn : ¬p∣K := fun hd => (hKw.trans_le (mem_Ico.mp hpI).1).not_ge (Nat.le_of_dvd hK hd)
    have ho : ¬p∣1 := fun hd => hpr.ne_one (Nat.dvd_one.mp hd)
    simp [localFactor,ho,hn]
  have htail := (sum_congr rfl hloc).le.trans
    ((sum_le_sum_of_subset_of_nonneg (fun p hp => (hmem hp).2)
      (fun p _ _ => one_div_nonneg.mpr (sq_nonneg ((p:ℝ)-1)))).trans (square_tail hw hwW))
  have hprod := T.norm_prod_one_add_sub_one_le (localFactor 1 K)
  rw [Real.norm_eq_abs] at hprod
  have hd := Finset.prod_sdiff (f:=fun p => 1+localFactor 1 K p) hsub
  change (∏ p∈T,(1+localFactor 1 K p))*chenSingularAtCutoff K w=chenSingularAtCutoff K W at hd
  have hS := (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2)
    (chenSingularAtCutoff_ge_half he (by omega : 3≤w))).ne'
  rw [←hd,mul_div_cancel_right₀ _ hS]
  exact hprod.trans (sub_le_sub_right (Real.exp_le_exp.mpr htail) 1)

theorem twinChen_modulus_lt_cutoff {δ a : ℝ} (hδ : 0≤δ) (ha : δ<a) :
    ∀ᶠ M : ℕ in atTop, ∀ r : ℕ, (r:ℝ)≤(M:ℝ)^δ → 2*r<chenPowerLevel a M := by
  let b := (a+δ)/2
  have h₁ : δ<b := by dsimp [b]; linarith
  have h₂ : b<a := by dsimp [b]; linarith
  have hpow := (tendsto_rpow_atTop (sub_pos.mpr h₁)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hpow.eventually_ge_atTop (2:ℝ),
    eventually_rpow_add_one_le_powerLevel (hδ.trans h₁.le) h₂,eventually_ge_atTop (1:ℕ)]
      with M hpow hcut hM r hr
  have hp : (0:ℝ)<M := Nat.cast_pos.mpr hM
  change 2≤(M:ℝ)^(b-δ) at hpow
  have hv : (M:ℝ)^(b-δ)*(M:ℝ)^δ=(M:ℝ)^b := by rw [←Real.rpow_add hp,sub_add_cancel]
  have hh := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hp.le δ)
  rw [hv] at hh
  exact_mod_cast (show (2:ℝ)*(r:ℝ)<(chenPowerLevel a M:ℝ) by linarith only [hh,hr,hcut])

theorem twinChen_density_log_tendsto {δ a : ℝ} (hδ : 0≤δ) (ha : δ<a) (ha₁ : a≤1)
    (r : ℕ→ℕ) (hr : ∀ M, 1≤M → 0<r M ∧ (r M:ℝ)≤(M:ℝ)^δ) :
    Tendsto (fun M : ℕ => chenDensityProduct (2*r M) (chenPowerLevel a M)*
      Real.log (M:ℝ)/twinChenU M (r M)) atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant)/a)) := by
  let w := chenPowerLevel a
  let R (M : ℕ) := twinChenU M (r M)/chenSingularAtCutoff (2*r M) (w M)
  have hap := hδ.trans_lt ha
  have hw := chenPowerLevel_tendsto_atTop hap
  have hwr := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp hw
  have ht : Tendsto (fun M => (w M:ℝ)-2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro A
    filter_upwards [hwr.eventually_ge_atTop (A+2)] with M hh
    change A+2≤(w M:ℝ) at hh
    linarith only [hh]
  have hz := ((tendsto_const_nhds (x:=(1:ℝ))).div_atTop ht).rexp.sub_const 1
  simp only [Real.exp_zero,sub_self] at hz
  have hR : Tendsto R atTop (𝓝 1) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hz
    filter_upwards [hw.eventually_ge_atTop 4,twinChen_modulus_lt_cutoff hδ ha,
      eventually_ge_atTop (1:ℕ)] with M hw₄ hh hM
    obtain ⟨hr₁,hr₂⟩ := hr M hM
    rw [Real.norm_eq_abs]
    exact twinChen_singular_tail (by positivity) (even_two_mul _) (hh _ hr₂) hw₄
      ((chenPowerLevel_le_self ha₁ hM).trans (Nat.le_succ _))
  have h := (((chenMertensProduct_tendsto.comp hw).div hR one_ne_zero).div
    (chenLogPowerLevel_tendsto hap) hap.ne')
  rw [div_one] at h
  apply h.congr'
  filter_upwards [hw.eventually_ge_atTop 2,eventually_ge_atTop (2:ℕ)] with M hw₂ hM
  have hm : (2:ℝ)≤M := by exact_mod_cast hM
  have hw' : (2:ℝ)≤w M := by exact_mod_cast hw₂
  have hlog := Real.log_pos (by linarith : (1:ℝ)<M)
  have hlogw := Real.log_pos (by linarith : (1:ℝ)<w M)
  change (Real.log (w M:ℝ)*chenMertensProduct (w M)/R M)/
    (Real.log (w M:ℝ)/Real.log (M:ℝ))=_
  rw [chenDensityProduct_eq_mertens_mul_singular ((by decide : 1≤2).trans hw₂)]
  dsimp only [R]
  rw [div_div_eq_mul_div]
  field_simp
  rfl

end FareyGoldbach
