import FareyGoldbach.ChenMertens
import FareyGoldbach.ChenActualSieveParameters

/-! # Uniform comparison with the singular product through the target -/

open Filter
open scoped Topology Classical

namespace FareyGoldbach

/-- All prime factors of `N` occur at this canonical endpoint. -/
noncomputable def chenCanonicalU (N : ℕ) : ℝ := chenSingularAtCutoff N (N+1)

theorem chenCanonicalU_ge_half {N : ℕ} (he : Even N) (hN : 2≤N) :
    (1:ℝ)/2≤chenCanonicalU N := chenSingularAtCutoff_ge_half he (by omega)

private theorem square_tail_shift (w T : ℕ) (hw : 4≤w) :
    (∑ p∈Finset.Ico w T, 1/((p:ℝ)-1)^2) ≤ 1/((w:ℝ)-2) := by
  by_cases hwT : w≤T
  · have hh : (∑ p∈Finset.Ico w T,1/((p:ℝ)-1)^2)≤1/((w:ℝ)-2)-1/((T:ℝ)-2) := by
      induction T,hwT using Nat.le_induction with
      | base => simp
      | succ p hp ih =>
        have hp4 : (4:ℝ)≤p := by exact_mod_cast hw.trans hp
        have h₀ : 0<(p:ℝ)-2 := by linarith
        have h₁ : 0<(p:ℝ)-1 := by linarith
        have hx : 1/((p:ℝ)-1)^2≤1/((p:ℝ)-2)-1/((p:ℝ)-1) := by
          field_simp
          nlinarith
        rw [Finset.sum_Ico_succ_top hp,Nat.cast_succ]
        rw [show (p:ℝ)+1-2=(p:ℝ)-1 by ring]
        linarith only [hx,ih]
    have ht : (4:ℝ)≤T := by exact_mod_cast hw.trans hwT
    linarith only [hh,one_div_nonneg.mpr (by linarith : 0≤(T:ℝ)-2)]
  · rw [Finset.Ico_eq_empty_of_le (by omega),Finset.sum_empty]
    have hw' : (4:ℝ)≤w := by exact_mod_cast hw
    exact one_div_nonneg.mpr (by linarith)

/-- A finite bound for the relative change from cutoff `w` to cutoff `N+1`.
Primes dividing `N` contribute at most their number times `1/(w−1)`. -/
theorem chenCanonicalU_ratio_sub_one_le {N w : ℕ} (he : Even N) (hw : 4≤w) (hNw : w≤N+1) :
    |chenCanonicalU N/chenSingularAtCutoff N w-1| ≤
      Real.exp (2*Real.log (2*(N:ℝ))/((w:ℝ)-1)+1/((w:ℝ)-2))-1 := by
  classical
  let T := chenPrimesBelow (N+1) \ chenPrimesBelow w
  have hsub : chenPrimesBelow w ⊆ chenPrimesBelow (N+1) := by
    intro p hp
    obtain ⟨hI,hpp⟩ := Finset.mem_filter.mp hp
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hI
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlo,by omega⟩,hpp⟩
  have htp {p} (hp : p∈T) : p.Prime ∧ w≤p ∧ p≤N := by
    obtain ⟨hp₀,hp₁⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hI,hpp⟩ := Finset.mem_filter.mp hp₀
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hI
    have hw' : w≤p := by
      by_contra! h
      exact hp₁ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlo,by omega⟩,hpp⟩)
    exact ⟨hpp,hw',by omega⟩
  have hcomp := Finset.prod_sdiff (f:=fun p ↦ 1+localFactor 1 N p) hsub
  change (∏ p∈T,(1+localFactor 1 N p))*chenSingularAtCutoff N w=chenCanonicalU N at hcomp
  have hSn : chenSingularAtCutoff N w≠0 := (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2)
    (chenSingularAtCutoff_ge_half he (by omega))).ne'
  rw [← hcomp,mul_div_cancel_right₀ _ hSn]
  have hw' : (4:ℝ)≤w := by exact_mod_cast hw
  have hw0 : 0<(w:ℝ)-1 := by linarith
  let e (p : ℕ) : ℝ := if p∣N then 1/((w:ℝ)-1) else 0
  have hpt (p : ℕ) (hp : p∈T) : ‖localFactor 1 N p‖≤e p+1/((p:ℝ)-1)^2 := by
    obtain ⟨hpp,hwp,_⟩ := htp hp
    have hp' : (w:ℝ)≤p := by exact_mod_cast hwp
    have hp0 : 0<(p:ℝ)-1 := by linarith
    have hp1 : ¬p∣1 := fun h ↦ hpp.ne_one (Nat.dvd_one.mp h)
    simp only [localFactor,ite_eq_right hp1, Real.norm_eq_abs,e]
    by_cases h : p∣N
    · simp only [ite_eq_left h,abs_of_nonneg (one_div_nonneg.mpr hp0.le)]
      have hle := one_div_le_one_div_of_le hw0 (by linarith : (w:ℝ)-1≤(p:ℝ)-1)
      linarith only [hle,one_div_nonneg.mpr (sq_nonneg ((p:ℝ)-1))]
    · simp [h]
  have hdiv : T.filter (·∣N) ⊆ N.primeFactors := by
    intro p hp
    obtain ⟨hpT,hpN⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(htp hpT).1,hpN,by omega⟩
  have he₁ : (∑ p∈T,e p)≤2*Real.log (2*(N:ℝ))/((w:ℝ)-1) := by
    have hsum : (∑ p∈T,e p)=((T.filter (·∣N)).card:ℝ)/((w:ℝ)-1) := by
      unfold e
      rw [← Finset.sum_filter]
      simp [div_eq_mul_inv]
    rw [hsum]
    apply div_le_div_of_nonneg_right _ hw0.le
    exact (Nat.cast_le.mpr (Finset.card_le_card hdiv)).trans (primeFactors_card_le_two_log (by omega))
  have hT : T ⊆ Finset.Ico w (N+1) := fun p hp ↦
    Finset.mem_Ico.mpr ⟨(htp hp).2.1,Nat.lt_succ_of_le (htp hp).2.2⟩
  have he₂ : (∑ p∈T,1/((p:ℝ)-1)^2)≤1/((w:ℝ)-2) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hT (fun i _ _ ↦ one_div_nonneg.mpr (sq_nonneg _))).trans
      (square_tail_shift w (N+1) hw)
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib] at hsum
  have hprod := T.norm_prod_one_add_sub_one_le (localFactor 1 N)
  rw [Real.norm_eq_abs] at hprod
  exact hprod.trans (sub_le_sub_right (Real.exp_le_exp.mpr (hsum.trans (add_le_add he₁ he₂))) _)

/-- Uniform singular-series normalization at each fixed positive power cutoff. -/
theorem chenDensityProduct_cutoff_normalized {a : ℝ} (ha : 0<a) (ha₁ : a≤1) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop, Even N →
      |Real.log (chenPowerLevel a N : ℝ)*chenDensityProduct N (chenPowerLevel a N)/chenCanonicalU N
       - Real.exp (-Real.eulerMascheroniConstant)| ≤ ε := by
  let w := chenPowerLevel a
  let R (N : ℕ) := if Even N then chenCanonicalU N/chenSingularAtCutoff N (w N) else 1
  have hw := chenPowerLevel_tendsto_atTop ha
  have hw' := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp hw
  have hlog := chenLogTwo_div_powerLevel_tendsto ha
  have hdom : Tendsto (fun N : ℕ ↦ 4*(Real.log (2*(N:ℝ))/(w N:ℝ))+2/(w N:ℝ)) atTop (𝓝 0) := by
    simpa only [w,Function.comp_apply,mul_zero,add_zero] using
      (hlog.const_mul (4:ℝ)).add ((tendsto_const_nhds (x:=(2:ℝ))).div_atTop hw')
  have hexp := hdom.rexp.sub_const 1
  simp only [Real.exp_zero,sub_self] at hexp
  have hR : Tendsto R atTop (𝓝 1) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _)) _ hexp
    filter_upwards [hw.eventually_ge_atTop 4,eventually_ge_atTop (2:ℕ)] with N h₀ hN
    have hw₀ : (4:ℝ)≤w N := by exact_mod_cast h₀
    have hw₁ : (0:ℝ)<w N := by linarith
    have hNr : (2:ℝ)≤N := by exact_mod_cast hN
    have hlog₀ : 0≤Real.log (2*(N:ℝ)) := Real.log_nonneg (by linarith)
    have hi : 1/((w N:ℝ)-1) ≤ 2/(w N:ℝ) :=
      (div_le_div_iff₀ (by linarith) hw₁).mpr (by linarith)
    have h₁ : 2*Real.log (2*(N:ℝ))/((w N:ℝ)-1) ≤ 4*(Real.log (2*(N:ℝ))/(w N:ℝ)) := by
      calc
        _ = (2*Real.log (2*(N:ℝ)))*(1/((w N:ℝ)-1)) := by ring
        _ ≤ (2*Real.log (2*(N:ℝ)))*(2/(w N:ℝ)) := mul_le_mul_of_nonneg_left hi (by positivity)
        _ = _ := by ring
    have h₂ : 1/((w N:ℝ)-2)≤2/(w N:ℝ) :=
      (div_le_div_iff₀ (by linarith) hw₁).mpr (by linarith)
    by_cases he : Even N
    · change ‖R N-1‖≤Real.exp (_+_)-1
      simp only [R,ite_eq_left he,Real.norm_eq_abs]
      apply (chenCanonicalU_ratio_sub_one_le he h₀ _).trans
      · exact sub_le_sub_right (Real.exp_le_exp.mpr (add_le_add h₁ h₂)) _
      · exact (chenPowerLevel_le_self ha₁ (by omega)).trans (by omega)
    · change ‖R N-1‖≤Real.exp (_+_)-1
      simp only [R,ite_eq_right he,sub_self,norm_zero]
      exact sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have h := (chenMertensProduct_tendsto.comp hw).div hR one_ne_zero
  rw [div_one] at h
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp h ε hε,hw.eventually_ge_atTop 1] with N hN hw₀ he
  change dist (Real.log (w N:ℝ)*chenMertensProduct (w N)/R N) _<ε at hN
  rw [Real.dist_eq] at hN
  rw [chenDensityProduct_eq_mertens_mul_singular hw₀]
  simpa only [R,ite_eq_left he,div_div_eq_mul_div,mul_assoc] using hN.le
end FareyGoldbach
