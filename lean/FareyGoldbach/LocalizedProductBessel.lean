import FareyGoldbach.DyadicAssembly
import Mathlib.MeasureTheory.Integral.Prod

open scoped BigOperators ENNReal
open MeasureTheory Set

namespace FareyGoldbach

/-- A bounded measurable periodic representative on the line, for use on arcs
that may cross an endpoint of the unit interval. -/
structure BoundedPeriodicFunction where
  toFun : ℝ → ℂ
  measurable : Measurable toFun
  bounded : ∃ B : ℝ, ∀ x, ‖toFun x‖ ≤ B
  periodic : Function.Periodic toFun 1

instance : CoeFun BoundedPeriodicFunction (fun _ => ℝ → ℂ) := ⟨BoundedPeriodicFunction.toFun⟩

/-- Fourier coefficient on the full unit interval. -/
noncomputable def shortFourierCoeff (f : ℝ → ℂ) (k : ℕ) : ℂ :=
  ∫ x in (0:ℝ)..1, f x * e (-((k:ℝ)*x))

private noncomputable def box (d : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ s in (0:ℝ)..d, f (x+s)

private noncomputable def mass (d : ℝ) (f : BoundedPeriodicFunction) (x : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..d, ‖f (x+s)‖^2

private lemma box_meas {f : ℝ → ℂ} (hf : Measurable f) {d : ℝ} (hd : 0 ≤ d) :
    Measurable (box d f) := by
  let g := fun p : ℝ × ℝ => f (p.1+p.2)
  have hg : Measurable g := hf.comp (measurable_fst.add measurable_snd)
  have h := hg.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 d))
  change Measurable (fun x => ∫ s in (0:ℝ)..d, f (x+s))
  simpa only [intervalIntegral.integral_of_le hd,g] using h.measurable

private lemma mass_meas (f : BoundedPeriodicFunction) {d : ℝ} (hd : 0 ≤ d) :
    Measurable (mass d f) := by
  let g := fun p : ℝ × ℝ => ‖f (p.1+p.2)‖^2
  have hg : Measurable g := ((f.measurable.comp (measurable_fst.add measurable_snd)).norm).pow_const 2
  have h := hg.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 d))
  change Measurable (fun x => ∫ s in (0:ℝ)..d, ‖f (x+s)‖^2)
  simpa only [intervalIntegral.integral_of_le hd,g] using h.measurable

private lemma mass_nonneg (f : BoundedPeriodicFunction) {d : ℝ} (hd : 0 ≤ d) (x : ℝ) :
    0 ≤ mass d f x := intervalIntegral.integral_nonneg hd (fun _ _ => sq_nonneg _)

private lemma mass_bdd (f : BoundedPeriodicFunction) {d : ℝ} (hd : 0 ≤ d) :
    ∃ B : ℝ, ∀ x, ‖mass d f x‖ ≤ B := by
  obtain ⟨B,hB⟩ := f.bounded
  refine ⟨B^2*d,fun x => ?_⟩
  have hp (s : ℝ) : ‖‖f (x+s)‖^2‖ ≤ B^2 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB _) 2
  exact (intervalIntegral.norm_integral_le_of_norm_le_const (fun s _ => hp s)).trans_eq
    (by simp [abs_of_nonneg hd])

private lemma bounded_swap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {f : ℝ × ℝ → E} (hf : Measurable f) {B : ℝ} (hB : ∀ p, ‖f p‖ ≤ B)
    {d : ℝ} (hd : 0 ≤ d) :
    (∫ x in (0:ℝ)..1, ∫ s in (0:ℝ)..d, f (x,s)) =
    ∫ s in (0:ℝ)..d, ∫ x in (0:ℝ)..1, f (x,s) := by
  simp only [intervalIntegral.integral_of_le hd,intervalIntegral.integral_of_le zero_le_one]
  apply integral_integral_swap
  have hi : Integrable f ((volume.restrict (Ioc (0:ℝ) 1)).prod (volume.restrict (Ioc (0:ℝ) d))) :=
    Integrable.mono' (integrable_const B) hf.aestronglyMeasurable (Filter.Eventually.of_forall hB)
  exact hi

private lemma periodic_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hp : Function.Periodic f 1) (s : ℝ) :
    (∫ x in (0:ℝ)..1, f (x+s)) = ∫ x in (0:ℝ)..1, f x := by
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add,add_zero,add_comm 1 s] using hp.intervalIntegral_add_eq s 0

private lemma integral_mass (f : BoundedPeriodicFunction) {d : ℝ} (hd : 0 ≤ d) :
    (∫ x in (0:ℝ)..1, mass d f x) = d*(∫ x in (0:ℝ)..1, ‖f x‖^2) := by
  obtain ⟨B,hB⟩ := f.bounded
  let g := fun p : ℝ × ℝ => ‖f (p.1+p.2)‖^2
  have hm : Measurable g := ((f.measurable.comp (measurable_fst.add measurable_snd)).norm).pow_const 2
  have hb (p : ℝ × ℝ) : ‖g p‖ ≤ B^2 := by
    dsimp only [g]; rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB _) 2
  have hp : Function.Periodic (fun x => ‖f x‖^2) 1 := fun x => by dsimp only; rw [f.periodic x]
  change (∫ x in (0:ℝ)..1, ∫ s in (0:ℝ)..d, g (x,s)) = _
  rw [bounded_swap hm hb hd]
  dsimp only [g]
  simp_rw [periodic_integral hp]
  simp [intervalIntegral.integral_const]

private lemma neg_freq (k : ℕ) : Continuous (fun x : ℝ => e (-((k:ℝ)*x))) := by
  simpa only [neg_mul] using continuous_e_mul (-(k:ℝ))

private lemma neg_freq_periodic (k : ℕ) :
    Function.Periodic (fun x : ℝ => e (-((k:ℝ)*x))) 1 := by
  intro x
  change e (-((k:ℝ)*(x+1))) = e (-((k:ℝ)*x))
  rw [show -((k:ℝ)*(x+1)) = -((k:ℝ)*x)+((-(k:ℤ):ℤ):ℝ) by push_cast; ring,e_add_int]

private lemma coeff_box {f : ℝ → ℂ} (hf : Measurable f) (hp : Function.Periodic f 1)
    {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) {d : ℝ} (hd : 0 ≤ d) (j : ℕ) :
    shortFourierCoeff (box d f) j = (∫ s in (0:ℝ)..d, e ((j:ℝ)*s))*shortFourierCoeff f j := by
  let g := fun p : ℝ × ℝ => f (p.1+p.2)*e (-((j:ℝ)*p.1))
  have hm : Measurable g := (hf.comp (measurable_fst.add measurable_snd)).mul
    ((neg_freq j).measurable.comp measurable_fst)
  have hb (p : ℝ × ℝ) : ‖g p‖ ≤ B := by dsimp [g]; rw [norm_mul,norm_e,mul_one]; exact hB _
  have hfirst : shortFourierCoeff (box d f) j =
      ∫ x in (0:ℝ)..1, ∫ s in (0:ℝ)..d, g (x,s) := by
    unfold shortFourierCoeff
    apply intervalIntegral.integral_congr
    intro x _
    dsimp [box,g]; rw [intervalIntegral.integral_mul_const]
  have hsecond (s : ℝ) : (∫ x in (0:ℝ)..1, g (x,s)) = shortFourierCoeff f j * e ((j:ℝ)*s) := by
    let h := fun x : ℝ => f x * e (-((j:ℝ)*x))
    have hper : Function.Periodic h 1 := hp.mul (neg_freq_periodic j)
    have he (x : ℝ) : g (x,s) = h (x+s)*e ((j:ℝ)*s) := by
      dsimp [g,h]; rw [mul_assoc,← e_add]; congr 2; ring
    simp_rw [he]
    rw [intervalIntegral.integral_mul_const,periodic_integral hper]
    rfl
  rw [hfirst,bounded_swap hm hb hd]
  simp_rw [hsecond]
  rw [intervalIntegral.integral_const_mul,mul_comm]

private lemma multiplier_lower {K j : ℕ} {d : ℝ} (hd : 0 ≤ d) (hkd : (K:ℝ)*d ≤ 1/8)
    (hj : j ≤ K) : d/2 ≤ ‖∫ s in (0:ℝ)..d, e ((j:ℝ)*s)‖ := by
  have he (s : ℝ) : (e ((j:ℝ)*s)).re = Real.cos (2*Real.pi*((j:ℝ)*s)) := by
    unfold e
    simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using
      Complex.exp_ofReal_mul_I_re (2*Real.pi*((j:ℝ)*s))
  have hlow (s : ℝ) (hs : s ∈ Icc 0 d) : (1/2:ℝ) ≤ (e ((j:ℝ)*s)).re := by
    rw [he,← Real.cos_pi_div_three]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (by have := hs.1; positivity) (by linarith [Real.pi_pos])
    have hjs : (j:ℝ)*s ≤ (K:ℝ)*d := mul_le_mul (Nat.cast_le.mpr hj) hs.2 hs.1 (Nat.cast_nonneg _)
    nlinarith only [mul_le_mul_of_nonneg_left (hjs.trans hkd) Real.pi_pos.le,Real.pi_pos]
  have hi := intervalIntegral.integral_mono_on (μ:=volume) hd
    (f:=fun _ : ℝ => (1/2:ℝ)) (g:=fun s : ℝ => (e ((j:ℝ)*s)).re)
    (intervalIntegrable_const) ((Complex.continuous_re.comp (continuous_e_mul (j:ℝ))).intervalIntegrable _ _) hlow
  have hre := Complex.reCLM.intervalIntegral_comp_comm ((continuous_e_mul (j:ℝ)).intervalIntegrable 0 d (μ:=volume))
  change (∫ s in (0:ℝ)..d, (e ((j:ℝ)*s)).re) = (∫ s in (0:ℝ)..d, e ((j:ℝ)*s)).re at hre
  rw [hre,intervalIntegral.integral_const] at hi
  exact (show d/2 ≤ (∫ s in (0:ℝ)..d, e ((j:ℝ)*s)).re by
    simpa only [sub_zero,smul_eq_mul,div_eq_mul_inv,one_mul] using hi).trans (Complex.re_le_norm _)

private noncomputable def modProduct (u v : BoundedPeriodicFunction) (m : ℕ) (x : ℝ) :=
  (u x*v x)*e (-((m:ℝ)*x))

private lemma modProduct_norm (u v : BoundedPeriodicFunction) (m : ℕ) (x : ℝ) :
    ‖modProduct u v m x‖ = ‖u x‖*‖v x‖ := by simp [modProduct,norm_e]

private lemma box_product_sq (u v : BoundedPeriodicFunction) (m : ℕ) {d : ℝ} (hd : 0 ≤ d) (x : ℝ) :
    ‖box d (modProduct u v m) x‖^2 ≤ mass d u x*mass d v x := by
  let μ := volume.restrict (Ioc (0:ℝ) d)
  have hm (w : BoundedPeriodicFunction) : Measurable (fun s => ‖w (x+s)‖) :=
    (w.measurable.comp (measurable_const.add measurable_id)).norm
  have hmem (w : BoundedPeriodicFunction) : MemLp (fun s => ‖w (x+s)‖) (ENNReal.ofReal 2) μ := by
    obtain ⟨B,hB⟩ := w.bounded
    apply MemLp.of_bound (hm w).aestronglyMeasurable B
    exact Filter.Eventually.of_forall fun s => by simp only [Real.norm_of_nonneg (norm_nonneg _)]; exact hB _
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ:=μ) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun s => norm_nonneg (u (x+s))))
    (Filter.Eventually.of_forall (fun s => norm_nonneg (v (x+s)))) (hmem u) (hmem v)
  simp only [Real.rpow_two,← Real.sqrt_eq_rpow] at hcs
  have hu : 0 ≤ mass d u x := mass_nonneg _ hd _
  have hv : 0 ≤ mass d v x := mass_nonneg _ hd _
  have h : ‖box d (modProduct u v m) x‖ ≤ Real.sqrt (mass d u x)*Real.sqrt (mass d v x) := by
    apply (intervalIntegral.norm_integral_le_integral_norm hd).trans
    simpa only [modProduct_norm,mass,intervalIntegral.integral_of_le hd,μ] using hcs
  calc _ ≤ (Real.sqrt (mass d u x)*Real.sqrt (mass d v x))^2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
       _ = _ := by rw [mul_pow,Real.sq_sqrt hu,Real.sq_sqrt hv]

private lemma box_product_energy (u v : BoundedPeriodicFunction) (m K : ℕ) {d : ℝ} (hd : 0 ≤ d)
    (hkd : (K:ℝ)*d ≤ 1/8) :
    (d/2)^2* ∑ k ∈ Finset.Icc m (m+K), ‖shortFourierCoeff (fun t => u t*v t) k‖^2 ≤
      ∫ x in (0:ℝ)..1, mass d u x * mass d v x := by
  let f := modProduct u v m
  have hm : Measurable f := (u.measurable.mul v.measurable).mul (neg_freq m).measurable
  have hp : Function.Periodic f 1 := (u.periodic.mul v.periodic).mul (neg_freq_periodic m)
  obtain ⟨U,hU⟩ := u.bounded
  obtain ⟨V,hV⟩ := v.bounded
  have hU0 : 0 ≤ U := (norm_nonneg _).trans (hU 0)
  have hB (t : ℝ) : ‖f t‖ ≤ U*V := (modProduct_norm _ _ _ _).le.trans
    (mul_le_mul (hU t) (hV t) (norm_nonneg _) hU0)
  have hbox (t : ℝ) : ‖box d f t‖ ≤ U*V*d :=
    (intervalIntegral.norm_integral_le_of_norm_le_const (fun s _ => hB (t+s))).trans_eq (by simp [abs_of_nonneg hd])
  have hc (j : ℕ) : shortFourierCoeff f j = shortFourierCoeff (fun t => u t*v t) (m+j) := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [f,modProduct]
    rw [mul_assoc,← e_add]
    congr 2
    push_cast
    ring
  have hI : Finset.Icc m (m+K) = Finset.Ico m (m+K+1) := by ext i; simp
  rw [hI,Finset.sum_Ico_eq_sum_range,show m+K+1-m=K+1 by omega,Finset.mul_sum]
  calc _ ≤ ∑ j ∈ Finset.range (K+1), ‖shortFourierCoeff (box d f) j‖^2 := by
           refine Finset.sum_le_sum fun j hj => ?_
           rw [coeff_box hm hp hB hd,hc,norm_mul,mul_pow]
           exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity)
             (multiplier_lower hd hkd (by have := Finset.mem_range.mp hj; omega)) 2) (sq_nonneg _)
       _ ≤ ∫ x in (0:ℝ)..1, ‖box d f x‖^2 := bessel_intervalIntegral (box_meas hm hd) hbox _
       _ ≤ _ := by
         obtain ⟨T1,hT1⟩ := mass_bdd u hd
         obtain ⟨T2,hT2⟩ := mass_bdd v hd
         have hT0 : 0 ≤ T1 := (norm_nonneg _).trans (hT1 0)
         apply intervalIntegral.integral_mono_on zero_le_one
         · apply intervalIntegrable_of_measurable_bounded (B:=(U*V*d)^2) ((box_meas hm hd).norm.pow_const 2)
           intro x; rw [Real.norm_of_nonneg (sq_nonneg _)]
           exact pow_le_pow_left₀ (norm_nonneg _) (hbox x) 2
         · apply intervalIntegrable_of_measurable_bounded (B:=T1*T2) ((mass_meas u hd).mul (mass_meas v hd))
           intro x; change ‖mass d u x*mass d v x‖ ≤ _; rw [norm_mul]; exact mul_le_mul (hT1 _) (hT2 _) (norm_nonneg _) hT0
         · exact fun x _ => box_product_sq u v m hd x

/-- Local energy on a centered arc. A periodic representative counts wrapped
pieces without any convention at the endpoints. -/
noncomputable def localizedArcMass (f : ℝ → ℂ) (K : ℕ) (x : ℝ) : ℝ :=
  ∫ t in (x-1/(K:ℝ))..(x+1/(K:ℝ)), ‖f t‖^2

/-- Squared product coefficients in the closed integer window from m to m+K. -/
noncomputable def productWindowEnergy (u v : ℝ → ℂ) (m K : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc m (m+K), ‖shortFourierCoeff (fun t => u t*v t) k‖^2

private lemma mass_le_arc (f : BoundedPeriodicFunction) {d : ℝ} {K : ℕ}
    (hd : 0 ≤ d) (hdK : d ≤ 1/(K:ℝ)) (x : ℝ) : mass d f x ≤ localizedArcMass f K x := by
  unfold mass localizedArcMass
  rw [intervalIntegral.integral_comp_add_left (fun t => ‖f t‖^2) x,add_zero]
  apply intervalIntegral.integral_mono_interval (sub_le_self x (by positivity))
    (by linarith) (by linarith) (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  obtain ⟨T,hT⟩ := f.bounded
  apply intervalIntegrable_of_measurable_bounded (B:=T^2) (f.measurable.norm.pow_const 2)
  exact fun t => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (norm_nonneg _) (hT _) 2

private lemma mass_int (f : BoundedPeriodicFunction) {d : ℝ} (hd : 0 ≤ d) :
    IntervalIntegrable (mass d f) volume 0 1 := by
  obtain ⟨B,hB⟩ := mass_bdd f hd
  exact intervalIntegrable_of_measurable_bounded (mass_meas f hd) hB

private lemma mass_pair_int (u v : BoundedPeriodicFunction) {d : ℝ} (hd : 0 ≤ d) :
    IntervalIntegrable (fun x => mass d u x*mass d v x) volume 0 1 := by
  obtain ⟨B,hB⟩ := mass_bdd u hd
  obtain ⟨C,hC⟩ := mass_bdd v hd
  have hb : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  apply intervalIntegrable_of_measurable_bounded (B:=B*C) ((mass_meas u hd).mul (mass_meas v hd))
  exact fun x => by change ‖mass d u x*mass d v x‖ ≤ _; rw [norm_mul]; exact mul_le_mul (hB _) (hC _) (norm_nonneg _) hb

/-- Localized product Bessel with sums over independent index sets. The local
hypothesis is imposed after summing the first family. -/
theorem sum_localized_product_bessel {ι η : Type*} (s : Finset ι) (t : Finset η)
    (u : ι → BoundedPeriodicFunction) (v : η → BoundedPeriodicFunction)
    (m K : ℕ) (hK : 0 < K) {A : ℝ}
    (hA : ∀ x : ℝ, ∑ i ∈ s, localizedArcMass (u i) K x ≤ A) :
    (∑ i ∈ s, ∑ j ∈ t, productWindowEnergy (u i) (v j) m K) ≤
      32*(K:ℝ)*A*(∑ j ∈ t, ∫ x in (0:ℝ)..1, ‖v j x‖^2) := by
  classical
  let d := 1/(8*(K:ℝ))
  have hk : (0:ℝ)<K := Nat.cast_pos.mpr hK
  have hd : 0 < d := by dsimp [d]; positivity
  have hkd : (K:ℝ)*d ≤ 1/8 := by dsimp [d]; field_simp; linarith
  have hdK : d ≤ 1/(K:ℝ) := by dsimp [d]; apply one_div_le_one_div_of_le hk; linarith
  let c := (d/2)^2
  have hc : 0 < c := by dsimp only [c]; positivity
  have hu (x : ℝ) : (∑ i ∈ s, mass d (u i) x) ≤ A :=
    (Finset.sum_le_sum (fun i _ => mass_le_arc (u i) hd.le hdK x)).trans (hA x)
  have hj (j : η) : c*(∑ i ∈ s, productWindowEnergy (u i) (v j) m K) ≤
      (A*d)*(∫ x in (0:ℝ)..1, ‖v j x‖^2) := by
    calc _ = ∑ i ∈ s, c*productWindowEnergy (u i) (v j) m K := Finset.mul_sum ..
         _ ≤ ∑ i ∈ s, ∫ x in (0:ℝ)..1, mass d (u i) x * mass d (v j) x :=
           Finset.sum_le_sum (fun i _ => box_product_energy (u i) (v j) m K hd.le hkd)
         _ = ∫ x in (0:ℝ)..1, (∑ i ∈ s, mass d (u i) x)*mass d (v j) x := by
           simp_rw [Finset.sum_mul]
           rw [intervalIntegral_finset_sum (fun i _ => mass_pair_int (u i) (v j) hd.le)]
         _ ≤ ∫ x in (0:ℝ)..1, A*mass d (v j) x := by
           apply intervalIntegral.integral_mono_on zero_le_one
           · simp_rw [Finset.sum_mul]
             exact intervalIntegrable_finset_sum s (fun i _ => mass_pair_int (u i) (v j) hd.le)
           · exact (mass_int (v j) hd.le).const_mul _
           · exact fun x _ => mul_le_mul_of_nonneg_right (hu x) (mass_nonneg _ hd.le _)
         _ = _ := by rw [intervalIntegral.integral_const_mul,integral_mass (v j) hd.le]; ring
  apply le_of_mul_le_mul_left _ hc
  rw [Finset.sum_comm,Finset.mul_sum]
  calc _ ≤ ∑ j ∈ t, (A*d)*(∫ x in (0:ℝ)..1, ‖v j x‖^2) := Finset.sum_le_sum (fun j _ => hj j)
       _ = _ := by
         rw [← Finset.mul_sum]
         have hrel : c*(32*(K:ℝ))=d := by dsimp only [c,d]; field_simp; ring
         calc _ = (c*(32*(K:ℝ)))*A*(∑ j ∈ t, ∫ x in (0:ℝ)..1, ‖v j x‖^2) := by rw [hrel]; ring
              _ = _ := by ring

/-- Localized product Bessel on an arbitrary window, with no dependence on its
left endpoint. -/
theorem localized_product_bessel (u v : BoundedPeriodicFunction) (m K : ℕ)
    (hK : 0 < K) {A : ℝ} (hA : ∀ x : ℝ, localizedArcMass u K x ≤ A) :
    productWindowEnergy u v m K ≤
      32*(K:ℝ)*A*(∫ x in (0:ℝ)..1, ‖v x‖^2) := by
  simpa using sum_localized_product_bessel ({()} : Finset Unit) ({()} : Finset Unit)
    (fun _ => u) (fun _ => v) m K hK (A:=A) (fun x => by simpa using hA x)

/-- Arithmetic-mean version. Only the first family's mean local energy is used,
so individual members may have different concentrations. -/
theorem averaged_localized_product_bessel {ι η : Type*} (s : Finset ι) (t : Finset η)
    (hs : s.Nonempty) (ht : t.Nonempty) (u : ι → BoundedPeriodicFunction)
    (v : η → BoundedPeriodicFunction) (m K : ℕ) (hK : 0 < K) {A : ℝ}
    (hA : ∀ x : ℝ, (∑ i ∈ s, localizedArcMass (u i) K x)/(s.card:ℝ) ≤ A) :
    (∑ i ∈ s, ∑ j ∈ t, productWindowEnergy (u i) (v j) m K)/((s.card:ℝ)*(t.card:ℝ)) ≤
      32*(K:ℝ)*A*((∑ j ∈ t, ∫ x in (0:ℝ)..1, ‖v j x‖^2)/(t.card:ℝ)) := by
  have hS : (0:ℝ) < s.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hs)
  have hT : (0:ℝ) < t.card := Nat.cast_pos.mpr (Finset.card_pos.mpr ht)
  have h := sum_localized_product_bessel s t u v m K hK (A:=A*(s.card:ℝ))
    (fun x => (div_le_iff₀ hS).mp (hA x))
  apply (div_le_iff₀ (mul_pos hS hT)).2
  exact h.trans_eq (by field_simp)


/-- Squared Fourier coefficients on the integer frequency window from m to m+K,
including windows wholly or partly below zero. -/
noncomputable def signedProductWindowEnergy (u v : ℝ → ℂ) (m : ℤ) (K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (K+1), ‖∫ x in (0:ℝ)..1,
    (u x*v x)*e (-(((m+(j:ℤ):ℤ):ℝ)*x))‖^2

private noncomputable def signedModulate (v : BoundedPeriodicFunction) (m : ℤ) : BoundedPeriodicFunction where
  toFun := fun x => v x*e (-(m:ℝ)*x)
  measurable := v.measurable.mul (continuous_e_mul (-(m:ℝ))).measurable
  bounded := by
    obtain ⟨B,hB⟩ := v.bounded
    exact ⟨B,fun x => by rw [norm_mul,norm_e,mul_one]; exact hB x⟩
  periodic := v.periodic.mul (fun x => by
    rw [show -(m:ℝ)*(x+1) = -(m:ℝ)*x + ((-m:ℤ):ℝ) by push_cast; ring,e_add_int])

private lemma signedModulate_norm (v : BoundedPeriodicFunction) (m : ℤ) (x : ℝ) :
    ‖signedModulate v m x‖ = ‖v x‖ := by simp [signedModulate,norm_e]

private lemma signedModulate_window (u v : BoundedPeriodicFunction) (m : ℤ) (K : ℕ) :
    productWindowEnergy u (signedModulate v m) 0 K = signedProductWindowEnergy u v m K := by
  unfold productWindowEnergy signedProductWindowEnergy
  have hw : Finset.Icc 0 (0+K) = Finset.range (K+1) := by ext j; simp
  rw [hw]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : shortFourierCoeff (fun x => u x*signedModulate v m x) j =
      ∫ x in (0:ℝ)..1, (u x*v x)*e (-(((m+(j:ℤ):ℤ):ℝ)*x)) := by
    apply intervalIntegral.integral_congr
    intro x _
    change u x*(v x*e (-(m:ℝ)*x))*e (-((j:ℝ)*x)) = _
    rw [← mul_assoc,mul_assoc (u x*v x),← e_add]
    congr 2
    push_cast
    ring
  rw [hc]

/-- Localized product Bessel on a window with signed left endpoint. -/
theorem localized_product_bessel_int (u v : BoundedPeriodicFunction) (m : ℤ) (K : ℕ)
    (hK : 0 < K) {A : ℝ} (hA : ∀ x : ℝ, localizedArcMass u K x ≤ A) :
    signedProductWindowEnergy u v m K ≤ 32*(K:ℝ)*A*(∫ x in (0:ℝ)..1, ‖v x‖^2) := by
  simpa only [signedModulate_window,signedModulate_norm] using
    localized_product_bessel u (signedModulate v m) 0 K hK hA

/-- The arithmetic-mean bound has the same constant for every signed window. -/
theorem averaged_localized_product_bessel_int {ι η : Type*} (s : Finset ι) (t : Finset η)
    (hs : s.Nonempty) (ht : t.Nonempty) (u : ι → BoundedPeriodicFunction)
    (v : η → BoundedPeriodicFunction) (m : ℤ) (K : ℕ) (hK : 0 < K) {A : ℝ}
    (hA : ∀ x : ℝ, (∑ i ∈ s, localizedArcMass (u i) K x)/(s.card:ℝ) ≤ A) :
    (∑ i ∈ s, ∑ j ∈ t, signedProductWindowEnergy (u i) (v j) m K)/((s.card:ℝ)*(t.card:ℝ)) ≤
      32*(K:ℝ)*A*((∑ j ∈ t, ∫ x in (0:ℝ)..1, ‖v j x‖^2)/(t.card:ℝ)) := by
  simpa only [signedModulate_window,signedModulate_norm] using
    averaged_localized_product_bessel s t hs ht u (fun j => signedModulate (v j) m) 0 K hK hA

end FareyGoldbach