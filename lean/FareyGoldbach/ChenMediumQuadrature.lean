import FareyGoldbach.ChenMediumMass

/-! # Upper and lower sums for the moving medium-prime interval -/

open Filter Finset Set MeasureTheory
open scoped Topology

namespace FareyGoldbach

noncomputable def chenLogWeight (θ t : ℝ) : ℝ := 2/(θ-t)
private noncomputable def C (B θ : ℝ) : ℝ := 2/(θ-B)^2
private noncomputable def step (A B : ℝ) (K : ℕ) : ℝ := (B-A)/(K:ℝ)
private noncomputable def grid (A B : ℝ) (K i : ℕ) : ℝ := A+(i:ℝ)*step A B K

private theorem w_mono_error {B θ u v : ℝ} (hθ : B<θ) (huv:u≤v) (hv:v≤B) :
    chenLogWeight θ u ≤ chenLogWeight θ v ∧ chenLogWeight θ v-chenLogWeight θ u ≤ C B θ*(v-u) := by
  have h₀ : 0<θ-B := by linarith
  have h₁ : 0<θ-v := by linarith
  have h₂ : 0<θ-u := by linarith
  constructor
  · exact div_le_div_of_nonneg_left (by norm_num) h₁ (by linarith)
  · have hd : (θ-B)^2 ≤ (θ-v)*(θ-u) := by
      rw [sq]; exact mul_le_mul (by linarith) (by linarith) h₀.le h₁.le
    have he : chenLogWeight θ v-chenLogWeight θ u = (2/((θ-v)*(θ-u)))*(v-u) := by
      unfold chenLogWeight; field_simp; ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos h₀) hd)
      (sub_nonneg.mpr huv)

private theorem grid_std {A B : ℝ} (hAB : A≤B) {K : ℕ} (hK:0<K) :
    grid A B K 0=A ∧ grid A B K K=B ∧ Monotone (grid A B K) ∧ ∀ i, grid A B K (i+1)-grid A B K i=step A B K := by
  have h : 0<(K:ℝ) := Nat.cast_pos.mpr hK
  have hs : 0≤step A B K := div_nonneg (sub_nonneg.mpr hAB) h.le
  refine ⟨by simp [grid],by dsimp [grid,step]; field_simp; ring,
    fun i j hij => add_le_add (le_refl _) (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) hs),?_⟩
  intro i; simp only [grid,Nat.cast_add_one]; ring

private theorem sum_grid {f : ℕ→ℕ} (hf : Monotone f) (g : ℕ→ℝ) (K : ℕ) :
    ∑ i ∈ Finset.range K, ∑ q ∈ Finset.Ico (f i) (f (i+1)), g q = ∑ q ∈ Finset.Ico (f 0) (f K), g q := by
  induction K with
  | zero => simp
  | succ K ih => rw [sum_range_succ,ih,sum_Ico_consecutive g (hf (Nat.zero_le K)) (hf (Nat.le_succ K))]

private theorem tag_mem {N q : ℕ} (hN : 2≤N) (hq : q.Prime) {u v : ℝ}
    (hm : q∈Finset.Ico (chenPowerLevel u N) (chenPowerLevel v N)) :
    u-Real.log 2/Real.log (N:ℝ) ≤ Real.log (q:ℝ)/Real.log (N:ℝ) ∧
      Real.log (q:ℝ)/Real.log (N:ℝ) ≤ v := by
  have hn : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hl := Real.log_pos hn
  have hq₁ : (1:ℝ)≤q := Nat.one_le_cast.mpr hq.one_le
  obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp hm
  have hu' : (N:ℝ)^u < (q:ℝ)+1 :=
    (Nat.lt_floor_add_one _).trans_le (add_le_add (Nat.cast_le.mpr hlo) (le_refl _))
  have hv' : (q:ℝ) ≤ (N:ℝ)^v :=
    (Nat.cast_le.mpr hhi.le).trans (Nat.floor_le (Real.rpow_nonneg (by linarith) _))
  have h₁ := Real.log_le_log (Real.rpow_pos_of_pos (by linarith : 0<(N:ℝ)) u)
    (hu'.le.trans (show (q:ℝ)+1≤2*(q:ℝ) by linarith))
  have h₂ := Real.log_le_log (by linarith : 0<(q:ℝ)) hv'
  rw [Real.log_rpow (by linarith : 0<(N:ℝ)),Real.log_mul (by norm_num) (by linarith)] at h₁
  rw [Real.log_rpow (by linarith : 0<(N:ℝ))] at h₂
  exact ⟨by apply (le_div_iff₀ hl).2; field_simp; linarith,(div_le_iff₀ hl).2 h₂⟩

noncomputable def chenWeightedBandBetween (N : ℕ) (A B θ : ℝ) : ℝ :=
  ∑ q ∈ Finset.Ico (chenPowerLevel A N) (chenPowerLevel B N),
    chenLogWeight θ (Real.log (q:ℝ)/Real.log (N:ℝ))*chenBandWeight N q

private noncomputable def mass (N : ℕ) (u v : ℝ) : ℝ :=
  ∑ q ∈ Finset.Ico (chenPowerLevel u N) (chenPowerLevel v N), chenBandWeight N q

private noncomputable def approx (A B : ℝ) (N K : ℕ) (θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range K, chenLogWeight θ (grid A B K (i+1))*mass N (grid A B K i) (grid A B K (i+1))

private noncomputable def limitingApprox (A B : ℝ) (K : ℕ) (θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range K, chenLogWeight θ (grid A B K (i+1))*(Real.log (grid A B K (i+1))-Real.log (grid A B K i))

private theorem weighted_band_enclosure {A B θ : ℝ} (hAB : A≤B) (hθ:B<θ) {K N : ℕ} (hK:0<K) (hN:2≤N) :
    approx A B N K θ-C B θ*(step A B K+Real.log 2/Real.log (N:ℝ))*mass N A B ≤ chenWeightedBandBetween N A B θ ∧
      chenWeightedBandBetween N A B θ ≤ approx A B N K θ := by
  obtain ⟨hzero,hend,hmono,hstep⟩ := grid_std hAB hK
  let F (i : ℕ) := chenPowerLevel (grid A B K i) N
  let w (q : ℕ) := chenLogWeight θ (Real.log (q:ℝ)/Real.log (N:ℝ))
  let v (i : ℕ) := chenLogWeight θ (grid A B K (i+1))
  let E := C B θ*(step A B K+Real.log 2/Real.log (N:ℝ))
  have hF : Monotone F := fun i j hij => Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le
    (Nat.one_le_cast.mpr (by omega : 1≤N)) (hmono hij))
  have hpt (i : ℕ) (hi : i∈Finset.range K) (q : ℕ) (hq : q∈Finset.Ico (F i) (F (i+1))) :
      (v i-E)*chenBandWeight N q ≤ w q*chenBandWeight N q ∧ w q*chenBandWeight N q ≤ v i*chenBandWeight N q := by
    by_cases hp : q.Prime
    · have hv : grid A B K (i+1)≤B := (hmono (Finset.mem_range.mp hi)).trans_eq hend
      have ht := tag_mem hN hp hq
      have hb := w_mono_error hθ ht.2 hv
      have hgap : grid A B K (i+1)-Real.log (q:ℝ)/Real.log (N:ℝ) ≤ step A B K+Real.log 2/Real.log (N:ℝ) := by
        linarith only [ht.1,hstep i]
      have hC : 0≤C B θ := by unfold C; positivity
      have hdiff := hb.2.trans (mul_le_mul_of_nonneg_left hgap hC)
      exact ⟨mul_le_mul_of_nonneg_right (by dsimp [w,v,E]; linarith only [hdiff]) (chenBandWeight_nonneg ..),
        mul_le_mul_of_nonneg_right hb.1 (chenBandWeight_nonneg ..)⟩
    · simp [chenBandWeight,hp]
  have hm : mass N A B = ∑ i∈Finset.range K, mass N (grid A B K i) (grid A B K (i+1)) := by
    simpa only [F,hzero,hend,mass] using (sum_grid hF (chenBandWeight N) K).symm
  have hw : chenWeightedBandBetween N A B θ = ∑ i∈Finset.range K, ∑ q∈Finset.Ico (F i) (F (i+1)), w q*chenBandWeight N q := by
    simpa only [F,hzero,hend,chenWeightedBandBetween,chenPowerLevel,w] using
      (sum_grid hF (fun q => w q*chenBandWeight N q) K).symm
  rw [hw,hm]
  change (∑ i∈Finset.range K,v i*_) - E*_ ≤ _ ∧ _ ≤ ∑ i∈Finset.range K,v i*_
  rw [Finset.mul_sum,←Finset.sum_sub_distrib]
  constructor
  · refine Finset.sum_le_sum fun i hi => ?_
    rw [←sub_mul, mass, Finset.mul_sum]
    exact Finset.sum_le_sum fun q hq => (hpt i hi q hq).1
  · refine Finset.sum_le_sum fun i hi => ?_
    rw [mass,Finset.mul_sum]
    exact Finset.sum_le_sum fun q hq => (hpt i hi q hq).2

private theorem cellInt {B θ a b : ℝ} (hθ : B<θ) (ha:0<a) (hab:a≤b) (hb:b≤B) :
    IntervalIntegrable (fun t : ℝ => 2/(t*(θ-t))) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro t ht
  have h₁ := ha.trans_le ht.1
  have h₂ : 0<θ-t := by linarith [ht.2]
  fun_prop (disch := positivity)

private theorem cell_integral_enclosure {B θ a b : ℝ} (hθ :B<θ) (ha:0<a) (hab:a≤b) (hb:b≤B) :
    let I := ∫ t in a..b, 2/(t*(θ-t))
    let H := Real.log b-Real.log a
    (chenLogWeight θ b-C B θ*(b-a))*H ≤ I ∧ I ≤ chenLogWeight θ b*H := by
  have hC : 0≤C B θ := by unfold C; positivity
  have hI := cellInt hθ ha hab hb
  have hi : IntervalIntegrable (fun t:ℝ => t⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact continuousOn_id.inv₀ fun t ht => (ha.trans_le ht.1).ne'
  have hinv : (∫ t in a..b, t⁻¹) = Real.log b-Real.log a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => Real.hasDerivAt_log
      (ha.trans_le ((uIcc_of_le hab) ▸ ht : t∈Icc a b).1).ne') hi
  have hw (t:ℝ) (ht:t∈Icc a b) : chenLogWeight θ t*t⁻¹=2/(t*(θ-t)) := by
    have ht₀ := ha.trans_le ht.1
    have hd : 0<θ-t := by linarith [ht.2]
    unfold chenLogWeight
    field_simp
  dsimp only
  rw [←hinv,←intervalIntegral.integral_const_mul,←intervalIntegral.integral_const_mul]
  constructor
  · refine intervalIntegral.integral_mono_on hab (hi.const_mul _) hI (fun t ht => ?_)
    have hh := w_mono_error hθ ht.2 hb
    have h : chenLogWeight θ b-C B θ*(b-a)≤chenLogWeight θ t := by
      linarith only [hh.2,mul_le_mul_of_nonneg_left (sub_le_sub_left ht.1 b) hC]
    exact (mul_le_mul_of_nonneg_right h (inv_nonneg.mpr (ha.trans_le ht.1).le)).trans_eq (hw t ht)
  · refine intervalIntegral.integral_mono_on hab hI (hi.const_mul _) (fun t ht => ?_)
    have h := mul_le_mul_of_nonneg_right (w_mono_error hθ ht.2 hb).1 (inv_nonneg.mpr (ha.trans_le ht.1).le)
    rw [←hw t ht]
    exact h

private theorem integral_enclosure {A B θ : ℝ} (hA:0<A) (hAB:A≤B) (hθ :B<θ) {K : ℕ} (hK:0<K) :
    limitingApprox A B K θ-C B θ*step A B K*(Real.log B-Real.log A) ≤ (∫ t in A..B, 2/(t*(θ-t))) ∧
    (∫ t in A..B, 2/(t*(θ-t))) ≤ limitingApprox A B K θ := by
  obtain ⟨hzero,hend,hmono,hstep⟩ := grid_std hAB hK
  let H (i : ℕ) := Real.log (grid A B K (i+1))-Real.log (grid A B K i)
  let I (i : ℕ) := ∫ t in grid A B K i..grid A B K (i+1), 2/(t*(θ-t))
  have hpos (i : ℕ) : 0<grid A B K i := by
    have hh := hmono (Nat.zero_le i); rw [hzero] at hh; linarith
  have hub (i : ℕ) (hi:i<K) : grid A B K (i+1)≤B := (hmono hi).trans_eq hend
  have hI := intervalIntegral.sum_integral_adjacent_intervals (a:=grid A B K) (n:=K)
    (fun i hi => cellInt hθ (hpos i) (hmono (Nat.le_succ i)) (hub i hi))
  rw [hzero,hend] at hI
  have hH : ∑ i∈Finset.range K,H i=Real.log B-Real.log A := by
    simpa only [hzero,hend,H] using Finset.sum_range_sub (fun j => Real.log (grid A B K j)) K
  rw [←hI,←hH]
  unfold limitingApprox
  rw [Finset.mul_sum,←Finset.sum_sub_distrib]
  constructor
  · refine Finset.sum_le_sum fun i hi => ?_
    change _*H i-_*H i ≤ I i
    rw [←sub_mul,←hstep i]
    exact (cell_integral_enclosure hθ (hpos i) (hmono (Nat.le_succ i)) (hub i (Finset.mem_range.mp hi))).1
  · exact Finset.sum_le_sum fun i hi =>
      (cell_integral_enclosure hθ (hpos i) (hmono (Nat.le_succ i)) (hub i (Finset.mem_range.mp hi))).2

private theorem approx_tendsto (hm : ChenReciprocalMertens) {A B:ℝ} (hA:0<A) (hAB:A≤B) {K : ℕ} (hK:0<K) (θ : ℝ) :
    Tendsto (fun N => approx A B N K θ) atTop (𝓝 (limitingApprox A B K θ)) := by
  obtain ⟨hzero,_,hmono,_⟩ := grid_std hAB hK
  unfold approx limitingApprox
  apply tendsto_finsetSum
  intro i _
  have hpos : 0<grid A B K i := by have hh := hmono (Nat.zero_le i); rw [hzero] at hh; linarith
  exact (chen_band_mass_tendsto_of_mertens hm hpos (hmono (Nat.le_succ i))).const_mul _

theorem chen_weighted_band_between_tendsto_of_mertens (hm : ChenReciprocalMertens) {A B θ : ℝ} (hA:0<A) (hAB:A≤B) (hθ:B<θ) :
    Tendsto (fun N => chenWeightedBandBetween N A B θ) atTop (𝓝 ((∫ t in A..B, 2/(t*(θ-t))))) := by
  let H := Real.log B-Real.log A
  have hH : Tendsto (fun N => mass N A B) atTop (𝓝 H) :=
    chen_band_mass_tendsto_of_mertens hm hA hAB
  have hmesh : Tendsto (fun K:ℕ => C B θ*step A B K*H) atTop (𝓝 0) := by
    have h := ((tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul (B-A)).const_mul (C B θ)
    simpa only [step,div_eq_mul_inv,mul_zero,zero_mul,Function.comp_apply] using h.mul_const H
  have hx : Tendsto (fun N:ℕ => Real.log 2/Real.log (N:ℝ)) atTop (𝓝 0) := by
    have hh := (tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))).const_mul (Real.log 2)
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_apply] using hh
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K,hK,hsmall⟩ := ((eventually_ge_atTop (1:ℕ)).and (hmesh.eventually_lt_const hε)).exists
  have hK₀ : 0<K := by omega
  obtain ⟨hi₁,hi₂⟩ := integral_enclosure hA hAB hθ hK₀
  have hA := approx_tendsto hm hA hAB hK₀ θ
  have hcor := (((hx.const_add (step A B K)).const_mul (C B θ)).mul hH)
  rw [add_zero] at hcor
  have hlo := (hA.sub hcor).eventually_const_lt (show (∫ t in A..B, 2/(t*(θ-t)))-ε<limitingApprox A B K θ-C B θ*step A B K*H by
    linarith only [hi₂,hsmall])
  have hhi := hA.eventually_lt_const (show limitingApprox A B K θ<(∫ t in A..B, 2/(t*(θ-t)))+ε by
    dsimp [H] at hsmall; linarith only [hi₁,hsmall])
  filter_upwards [hlo,hhi,eventually_ge_atTop (2:ℕ)] with N hlo hhi hN
  obtain ⟨h₁,h₂⟩ := weighted_band_enclosure hAB hθ hK₀ hN
  rw [Real.dist_eq,abs_lt]
  exact ⟨by linarith only [hlo,h₁],by linarith only [hhi,h₂]⟩

noncomputable def chenWeightedBand (N : ℕ) (θ : ℝ) : ℝ :=
  chenWeightedBandBetween N (1/8) (1/3) θ

theorem chen_weighted_band_tendsto_of_mertens (hm : ChenReciprocalMertens) {θ : ℝ} (hθ:1/3<θ) :
    Tendsto (fun N => chenWeightedBand N θ) atTop (𝓝 (chenMediumMainCoeff θ)) := by
  rw [←chen_medium_integral_eq hθ]
  exact chen_weighted_band_between_tendsto_of_mertens hm (by norm_num) (by norm_num) hθ

end FareyGoldbach
