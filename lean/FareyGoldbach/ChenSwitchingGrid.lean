import FareyGoldbach.ChenMediumReciprocal

/-! # Upper quadrature for the outer switching integral -/

open Filter Finset Set MeasureTheory
open scoped Topology

namespace FareyGoldbach

noncomputable def chenSwitchStep (K : ℕ) : ℝ := (1/3-1/8)/(K:ℝ)
noncomputable def chenSwitchGrid (K i : ℕ) : ℝ := 1/8+(i:ℝ)*chenSwitchStep K

theorem chenSwitchGrid_properties {K : ℕ} (hK : 0<K) :
    chenSwitchGrid K 0=1/8 ∧ chenSwitchGrid K K=1/3 ∧
    StrictMono (chenSwitchGrid K) ∧ ∀ i, chenSwitchGrid K (i+1)-chenSwitchGrid K i=chenSwitchStep K := by
  have hk := Nat.cast_pos (α:=ℝ).mpr hK
  have hstep : 0<chenSwitchStep K := by dsimp [chenSwitchStep]; positivity
  refine ⟨by simp [chenSwitchGrid],by dsimp [chenSwitchGrid,chenSwitchStep]; field_simp; ring,
    fun i j hij => add_lt_add_right (mul_lt_mul_of_pos_right (Nat.cast_lt.mpr hij) hstep) _,?_⟩
  intro i
  simp only [chenSwitchGrid,Nat.cast_add_one]
  ring

noncomputable def chenSwitchCellCoeff (a b h : ℝ) : ℝ :=
  let v := (1-a)/2+h
  Real.log ((v/(1-b-v))/((1/3)/(1-b-1/3)))/(1-b)

theorem chenSwitchCellCoeff_integral {a b h : ℝ} (ha : 1/8≤a) (hab : a≤b) (hb : b≤1/3)
    (hh : 0<h) (hh' : h≤1/24) :
    (∫ v in (1/3:ℝ)..((1-a)/2+h),2/(v*(1-b-v)))/2 = chenSwitchCellCoeff a b h := by
  rw [chen_prime_band_kernel_integral_eq (by norm_num) (by linarith) (by linarith)]
  unfold chenSwitchCellCoeff
  ring

private noncomputable def switchDomain : Set (ℝ×ℝ×ℝ) :=
  Set.Icc (1/8) (1/3) ×ˢ (Set.Icc (1/8) (1/3) ×ˢ Set.Icc 0 (1/24))

private theorem cellCoeff_continuous : ContinuousOn
    (fun x : ℝ×ℝ×ℝ => chenSwitchCellCoeff x.1 x.2.1 x.2.2) switchDomain := by
  intro x hx
  obtain ⟨⟨ha,ha'⟩,⟨hb,hb'⟩,hc,hc'⟩ := hx
  have hv : 0<(1-x.1)/2+x.2.2 := by linarith
  have hd : 0<1-x.2.1-((1-x.1)/2+x.2.2) := by linarith
  have he : 0<1-x.2.1-1/3 := by linarith
  have hf : 0<1-x.2.1 := by linarith
  unfold chenSwitchCellCoeff
  fun_prop (disch := positivity)

private theorem cellCoeff_diagonal {t : ℝ} (ht : t≤1/3) :
    chenSwitchCellCoeff t t 0 = Real.log (2-3*t)/(1-t) := by
  dsimp only [chenSwitchCellCoeff]
  have h₂ : 1-t-((1-t)/2+0)≠0 := by linarith
  have h₃ : 1-t-1/3≠0 := by linarith
  have hrat : ((1-t)/2+0)/(1-t-((1-t)/2+0))=1 := by
    apply (div_eq_one_iff_eq h₂).mpr
    ring
  rw [hrat,show (1:ℝ)/((1/3)/(1-t-1/3)) = 2-3*t by field_simp; ring]

private theorem switch_integrable {a b : ℝ} (ha : 1/8≤a) (hab : a≤b) (hb : b≤1/3) :
    IntervalIntegrable (fun t : ℝ => Real.log (2-3*t)/(t*(1-t))) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro t ht
  have ht₀ : 0<t := by linarith only [ha,ht.1]
  have ht₁ : 0<1-t := by linarith only [hb,ht.2]
  have ht₂ : 0<2-3*t := by linarith only [hb,ht.2]
  fun_prop (disch := positivity)

theorem chenSwitchGrid_upper {ε : ℝ} (hε : 0<ε) :
    ∃ K : ℕ, 0<K ∧ chenSwitchStep K≤1/24 ∧
      (∑ i∈range K, (Real.log (chenSwitchGrid K (i+1))-Real.log (chenSwitchGrid K i)) *
        chenSwitchCellCoeff (chenSwitchGrid K i) (chenSwitchGrid K (i+1)) (chenSwitchStep K))
        ≤ chenSwitchIntegral+ε := by
  let H := Real.log (1/3)-Real.log (1/8)
  have hH : 0<H := sub_pos.mpr (Real.log_lt_log (by norm_num) (by norm_num))
  let e := ε/H
  have he : 0<e := div_pos hε hH
  have hC : IsCompact switchDomain := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨δ,hδ,hcont⟩ := Metric.uniformContinuousOn_iff.mp
    (hC.uniformContinuousOn_of_continuous cellCoeff_continuous) e he
  have hmesh : Tendsto chenSwitchStep atTop (𝓝 0) := by
    change Tendsto (fun K : ℕ => ((1/3:ℝ)-1/8)/(K:ℝ)) atTop (𝓝 0)
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul ((1/3:ℝ)-1/8)
  obtain ⟨K,hK,hsmall⟩ := ((eventually_ge_atTop (1:ℕ)).and
    (hmesh.eventually_lt_const (lt_min hδ (by norm_num : (0:ℝ)<1/24)))).exists
  obtain ⟨hsδ,hsquarter⟩ := lt_min_iff.mp hsmall
  let g := chenSwitchGrid K
  let s := chenSwitchStep K
  obtain ⟨hg₀,hgK,hg,hstep⟩ := chenSwitchGrid_properties hK
  have hs : 0<s := by dsimp [s,chenSwitchStep]; positivity
  have hbounds (i : ℕ) (hi : i<K) : 1/8≤g i ∧ g i≤g (i+1) ∧ g (i+1)≤1/3 :=
    ⟨hg₀ ▸ hg.monotone (Nat.zero_le i),hg.monotone (Nat.le_succ i),hgK ▸ hg.monotone hi⟩
  let I (i : ℕ) := ∫ t in g i..g (i+1), Real.log (2-3*t)/(t*(1-t))
  let V (i : ℕ) := Real.log (g (i+1))-Real.log (g i)
  have hcell (i : ℕ) (hi : i<K) : V i*chenSwitchCellCoeff (g i) (g (i+1)) s ≤ I i+e*V i := by
    obtain ⟨ha,hab,hb⟩ := hbounds i hi
    have hapos : 0<g i := by linarith
    have hInv : IntervalIntegrable (fun t:ℝ => t⁻¹) volume (g i) (g (i+1)) :=
      ContinuousOn.intervalIntegrable_of_Icc hab
        (continuousOn_id.inv₀ fun t ht => (hapos.trans_le ht.1).ne')
    have hV : (∫ t in g i..g (i+1), t⁻¹)=V i := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => Real.hasDerivAt_log (hapos.trans_le ((uIcc_of_le hab) ▸ ht : t∈Set.Icc _ _).1).ne') hInv
    let W := chenSwitchCellCoeff (g i) (g (i+1)) s
    have hloc (t : ℝ) (ht : t∈Set.Icc (g i) (g (i+1))) :
        W-e ≤ Real.log (2-3*t)/(1-t) := by
      have h₁ : (g i,g (i+1),s)∈switchDomain :=
        ⟨⟨ha,hab.trans hb⟩,⟨ha.trans hab,hb⟩,hs.le,hsquarter.le⟩
      have ht₁ := ha.trans ht.1
      have ht₂ := ht.2.trans hb
      have h₂ : (t,t,(0:ℝ))∈switchDomain := ⟨⟨ht₁,ht₂⟩,⟨ht₁,ht₂⟩,le_rfl,by norm_num⟩
      have hd : dist (g i,g (i+1),s) (t,t,0)<δ := by
        simp only [Prod.dist_eq,Real.dist_eq,max_lt_iff,sub_zero,abs_lt]
        have hh : g (i+1)-g i=s := hstep i
        exact ⟨⟨by linarith [ht.2],by linarith [ht.1]⟩,⟨by linarith [ht.2],by linarith [ht.1]⟩,
          by linarith,hsδ⟩
      have h := hcont _ h₁ _ h₂ hd
      change dist W (chenSwitchCellCoeff t t 0)<e at h
      rw [cellCoeff_diagonal ht₂,Real.dist_eq,abs_lt] at h
      linarith only [h.2]
    have hm := intervalIntegral.integral_mono_on hab (hInv.const_mul (W-e)) (switch_integrable ha hab hb)
      (fun t ht => (mul_le_mul_of_nonneg_right (hloc t ht) (inv_nonneg.mpr (hapos.trans_le ht.1).le)).trans_eq
        (by simp only [div_eq_mul_inv,mul_inv_rev]; ring :
          (Real.log (2-3*t)/(1-t))*t⁻¹ = Real.log (2-3*t)/(t*(1-t))))
    rw [intervalIntegral.integral_const_mul,hV] at hm
    change (W-e)*V i≤I i at hm
    change V i*W≤_
    linarith only [hm]
  have hIa := intervalIntegral.sum_integral_adjacent_intervals (a:=g) (n:=K)
    (fun i hi => switch_integrable (hbounds i hi).1 (hbounds i hi).2.1 (hbounds i hi).2.2)
  have hIs : ∑ i∈range K,I i=chenSwitchIntegral := by simpa only [I,g,hg₀,hgK,chenSwitchIntegral] using hIa
  have hVs : ∑ i∈range K,V i=H := by
    simpa only [V,H,g,hg₀,hgK] using Finset.sum_range_sub (fun j => Real.log (g j)) K
  refine ⟨K,hK,hsquarter.le,(Finset.sum_le_sum (fun i hi => hcell i (mem_range.mp hi))).trans_eq ?_⟩
  rw [Finset.sum_add_distrib,←Finset.mul_sum,hIs,hVs]
  dsimp [e]
  field_simp

end FareyGoldbach
