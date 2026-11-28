import FareyGoldbach.LocalTwistedMeanSquare

/-! # Spectral tails for the local twisted mean square -/

open Complex Real MeasureTheory Set Filter
open scoped Classical

namespace FareyGoldbach

noncomputable def localSpectralCutoff (Y : ℕ) (ξ : ℝ) : ℕ := ⌈20 * (Y : ℝ) * ξ⌉₊

theorem localSpectralCutoff_bounds {Y : ℕ} {ξ : ℝ} (hY : 2 ≤ Y)
    (hξ : 1 / (Y : ℝ) ≤ ξ) (hξ' : ξ ≤ 1 / 2) :
    1 ≤ localSpectralCutoff Y ξ ∧ localSpectralCutoff Y ξ ≤ 11 * Y ∧
    (localSpectralCutoff Y ξ : ℝ) ≤ 21 * (Y : ℝ) * ξ := by
  have hY' : (0 : ℝ) < Y := Nat.cast_pos.mpr (by omega)
  have hprod : 1 ≤ (Y : ℝ) * ξ := by
    have h := (div_le_iff₀ hY').mp hξ
    simpa only [mul_comm ξ] using h
  have hN : (20 * (Y : ℝ) * ξ) ≤ (localSpectralCutoff Y ξ : ℝ) := Nat.le_ceil _
  have hN' : (localSpectralCutoff Y ξ : ℝ) < 20 * (Y : ℝ) * ξ + 1 :=
    Nat.ceil_lt_add_one (by nlinarith only [hprod])
  refine ⟨?_, ?_, by linarith only [hprod,hN']⟩
  · exact_mod_cast (show (1 : ℝ) ≤ (localSpectralCutoff Y ξ : ℝ) by nlinarith only [hN,hprod])
  · have h := mul_le_mul_of_nonneg_left hξ' (show 0 ≤ 20 * (Y : ℝ) by positivity)
    have hY₂ : (2 : ℝ) ≤ Y := by exact_mod_cast hY
    exact_mod_cast (show (localSpectralCutoff Y ξ : ℝ) ≤ 11 * (Y : ℝ) by linarith only [h,hN',hY₂])

theorem localSpectralCutoff_tail {Y : ℕ} {ξ t : ℝ} (hY : 2 ≤ Y)
    (hξ : 1 / (Y : ℝ) ≤ ξ) (ht : |t| ≤ ξ) :
    4 * Real.pi * |t * (Y : ℝ)| + 3 ≤ (localSpectralCutoff Y ξ : ℝ) := by
  have hY' : (0 : ℝ) < Y := Nat.cast_pos.mpr (by omega)
  have hprod : 1 ≤ ξ * (Y : ℝ) := (div_le_iff₀ hY').mp hξ
  have hN : 20 * (Y : ℝ) * ξ ≤ (localSpectralCutoff Y ξ : ℝ) := Nat.le_ceil _
  have hs : |t * (Y : ℝ)| ≤ ξ * (Y : ℝ) := by
    rw [abs_mul, abs_of_pos hY']
    exact mul_le_mul_of_nonneg_right ht hY'.le
  have hp := mul_le_mul_of_nonneg_right (show 4 * Real.pi ≤ 16 by linarith [Real.pi_lt_four])
    (abs_nonneg (t * (Y : ℝ)))
  linarith only [hs,hp,hN,hprod]

private noncomputable def heightEnvelope (u : ℝ) : ℝ := (1 + |u|) ^ (-(3 / 2 : ℝ))

private lemma heightEnvelope_nonneg (u : ℝ) : 0 ≤ heightEnvelope u := Real.rpow_nonneg (by positivity) _

private lemma integrable_heightEnvelope : Integrable heightEnvelope := by
  have hcont : Continuous heightEnvelope := by
    unfold heightEnvelope
    exact Continuous.rpow (continuous_const.add continuous_abs) continuous_const fun u =>
      Or.inl (by positivity)
  have hIoc : IntegrableOn heightEnvelope (Ioc 0 1) :=
    hcont.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hIoi : IntegrableOn heightEnvelope (Ioi 1) := by
    have h := integrableOn_Ioi_rpow_of_lt (a := -(3 / 2 : ℝ)) (c := 1) (by norm_num) zero_lt_one
    refine h.mono' hcont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := zero_lt_one.trans hu
    rw [Real.norm_of_nonneg (heightEnvelope_nonneg _), heightEnvelope, abs_of_pos hu0]
    exact Real.rpow_le_rpow_of_nonpos hu0 (by linarith) (by norm_num)
  have hpos : IntegrableOn heightEnvelope (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact hIoc.union hIoi
  have hneg : IntegrableOn heightEnvelope (Iic 0) := by
    have hi : IntegrableOn heightEnvelope (Iio 0) := by
      have he : (fun x : ℝ ↦ heightEnvelope (-x)) = heightEnvelope := by
        funext x
        simp [heightEnvelope]
      simpa [he] using hpos.comp_neg
    exact hi.congr_set_ae Iio_ae_eq_Iic.symm
  rw [← integrableOn_univ, ← Iic_union_Ioi]
  exact hneg.union hpos

private lemma summable_heightEnvelope : Summable (fun k : ℤ => heightEnvelope (k : ℝ)) := by
  have h1 : Summable (fun n : ℕ => ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  have h2 := (summable_nat_add_iff 1).mpr h1
  have hn : Summable (fun n : ℕ => heightEnvelope (n : ℝ)) := by
    refine h2.congr fun n => ?_
    rw [heightEnvelope, abs_of_nonneg (Nat.cast_nonneg _), Real.rpow_neg (by positivity),
      Nat.cast_add, Nat.cast_one, add_comm]
  rw [summable_int_iff_summable_nat_and_neg]
  exact ⟨by simpa using hn, by simpa [heightEnvelope, abs_neg] using hn⟩

private lemma log_height_over_sq_le {d Y : ℕ} [NeZero d] (hY : 2 ≤ Y) (u : ℝ) :
    Real.log (2 * (d : ℝ) * (2 + |u|)) / (1 + |u|)^2 ≤
      5 * Real.log (2 * (d : ℝ) * Y) * heightEnvelope u := by
  let A := 1 + |u|
  let L := Real.log (2 * (d : ℝ) * Y)
  have hA : 1 ≤ A := by dsimp [A]; exact le_add_of_nonneg_right (abs_nonneg _)
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hroot : 1 ≤ Real.sqrt A := by rw [Real.le_sqrt zero_le_one hAp.le]; simpa using hA
  have hL : 1 ≤ L := one_le_log_two_d_Y hY
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hY' : (2 : ℝ) ≤ Y := by exact_mod_cast hY
  have hlog : Real.log (2 * (d : ℝ)) ≤ L := Real.log_le_log (by positivity) (by nlinarith only [hd,hY'])
  have h2 : 0 < 2 + |u| := by positivity
  have hsqrt1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr h2)
  rw [Real.log_sqrt h2.le] at hsqrt1
  have hsqrt2 : Real.sqrt (2 + |u|) ≤ 2 * Real.sqrt A := by
    calc Real.sqrt (2 + |u|) ≤ Real.sqrt (4*A) := Real.sqrt_le_sqrt (by dsimp [A]; linarith [abs_nonneg u])
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4), show Real.sqrt 4 = 2 by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ)≤2)]]
  have htop : Real.log (2 * (d : ℝ) * (2 + |u|)) ≤ 5 * L * Real.sqrt A := by
    rw [Real.log_mul (by positivity) (by positivity)]
    have h₁ := mul_le_mul_of_nonneg_left hroot (show 0 ≤ L from zero_le_one.trans hL)
    have h₂ := mul_le_mul_of_nonneg_right hL (Real.sqrt_nonneg A)
    nlinarith only [hlog,hsqrt1,hsqrt2,h₁,h₂]
  calc _ ≤ (5 * L * Real.sqrt A) / A^2 := div_le_div_of_nonneg_right htop (by positivity)
    _ = _ := by
      change 5 * L * Real.sqrt A / A^2 = 5 * L * A ^ (-(3 / 2 : ℝ))
      rw [mul_div_assoc, Real.sqrt_eq_rpow, ← Real.rpow_natCast A 2, ← Real.rpow_sub hAp]
      norm_num

/-- Finite spectral truncation using complete unit bands. -/
noncomputable def localLowZeros {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (T : ℕ) : Finset ℂ :=
  (Finset.Icc (-(T : ℤ)) (T : ℤ)).biUnion (bandZeros χ)

theorem zeroSpectralTail_bound (hGRH : DirichletGRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ {d Y : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}, χ.IsPrimitive →
      ∀ (T : ℕ) (t : ℝ), 2 ≤ Y → 4 * Real.pi * |t * (Y : ℝ)| + 3 ≤ (T : ℝ) →
      ‖(∑' ρ, zeroTerm χ Y t ρ) - ∑ ρ ∈ localLowZeros χ T, zeroTerm χ Y t ρ‖ ≤
        C * Real.sqrt (Y : ℝ) * Real.log (2 * (d : ℝ) * Y) := by
  let G := ∑' k : ℤ, heightEnvelope (k : ℝ)
  have hG : 0 ≤ G := tsum_nonneg fun _ => heightEnvelope_nonneg _
  refine ⟨60000*217*5*(1+G), by positivity, ?_⟩
  intro d Y hd χ hprim T t hY hT
  let Z := localLowZeros χ T
  let L := Real.log (2 * (d : ℝ) * Y)
  let C := 60000 * 217 * 5 * Real.sqrt (Y : ℝ) * L
  have hL : 0 ≤ L := zero_le_one.trans (one_le_log_two_d_Y hY)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsum := summable_norm_zeroTerm hGRH hprim (show 1 ≤ Y by omega) t
  have hf := hsum.of_norm
  change ‖(∑' ρ, zeroTerm χ Y t ρ) - ∑ ρ ∈ Z, zeroTerm χ Y t ρ‖ ≤ _
  rw [← hf.sum_add_tsum_compl (s := Z), add_sub_cancel_left]
  refine (norm_tsum_le_tsum_norm (hsum.subtype (fun ρ => ρ ∉ Z))).trans ?_
  refine (hsum.subtype (fun ρ => ρ ∉ Z)).tsum_le_of_sum_le ?_
  intro s
  let f := fun ρ : ℂ => ‖zeroTerm χ Y t ρ‖
  let S := (s.image (fun ρ : {ρ : ℂ // ρ ∉ Z} => ρ.val)).filter
    (fun ρ => 0 < ρ.re ∧ entireL χ ρ = 0)
  let K := S.image (fun ρ => ⌊ρ.im⌋)
  have hS : S ⊆ K.biUnion (bandZeros χ) := by
    intro ρ hρ
    obtain ⟨_, hre, h0⟩ := Finset.mem_filter.mp hρ
    refine Finset.mem_biUnion.mpr ⟨⌊ρ.im⌋, Finset.mem_image_of_mem _ hρ, ?_⟩
    exact (mem_bandZeros_iff hGRH hprim).mpr ⟨hre,h0,Int.floor_le _,Int.lt_floor_add_one _⟩
  have hK (k : ℤ) (hk : k ∈ K) : (T : ℝ) ≤ |(k : ℝ)| := by
    obtain ⟨ρ,hρ,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hρ',hre,h0⟩ := Finset.mem_filter.mp hρ
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hρ'
    by_contra! hn
    have hh := abs_lt.mp hn
    have hmem : ⌊z.val.im⌋ ∈ Finset.Icc (-(T : ℤ)) (T : ℤ) := by
      exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hh.1.le, by exact_mod_cast hh.2.le⟩
    exact z.property (Finset.mem_biUnion.mpr ⟨_,hmem,(mem_bandZeros_iff hGRH hprim).mpr
      ⟨hre,h0,Int.floor_le _,Int.lt_floor_add_one _⟩⟩)
  have hbound (k : ℤ) (hk : k ∈ K) : ∑ ρ ∈ bandZeros χ k, f ρ ≤ C * heightEnvelope (k : ℝ) := by
    have h := sum_norm_zeroTerm_band_le hGRH hprim (Y := Y) (by omega) t k
    rw [ite_eq_left (hT.trans (hK k hk))] at h
    have hmajor := mul_le_mul_of_nonneg_left (log_height_over_sq_le (d := d) hY (k : ℝ))
      (show 0 ≤ 60000*217*Real.sqrt (Y : ℝ) by positivity)
    dsimp [C,L,f]
    exact h.trans (by simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmajor)
  calc ∑ z ∈ s, f z.val = ∑ ρ ∈ S, f ρ := by
        dsimp [S]
        rw [Finset.sum_filter, Finset.sum_image (fun a _ b _ hab => Subtype.ext hab)]
        refine Finset.sum_congr rfl fun z _ => ?_
        dsimp [f]; unfold zeroTerm; split_ifs <;> simp
    _ ≤ ∑ ρ ∈ K.biUnion (bandZeros χ), f ρ :=
        Finset.sum_le_sum_of_subset_of_nonneg hS fun _ _ _ => norm_nonneg _
    _ = ∑ k ∈ K, ∑ ρ ∈ bandZeros χ k, f ρ :=
        Finset.sum_biUnion fun i _ j _ hij => bandZeros_disjoint χ hij
    _ ≤ ∑ k ∈ K, C * heightEnvelope (k : ℝ) := Finset.sum_le_sum hbound
    _ ≤ C * G := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left
          (summable_heightEnvelope.sum_le_tsum K fun k _ => heightEnvelope_nonneg _) hC
    _ ≤ _ := by dsimp [C,L]; nlinarith only [hC]

noncomputable def quarterPoint (u : ℝ) : ℂ := ((1 / 4 : ℝ) : ℂ) + (u : ℂ) * Complex.I

noncomputable def quarterContourIntegrand {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d)
    (Y : ℕ) (t u : ℝ) : ℂ :=
  mellin (scaledTiltedBump Y t) (quarterPoint u) * negLogDerivL χ (quarterPoint u)

set_option maxHeartbeats 500000 in
theorem quarterSpectralTail_bound (hGRH : DirichletGRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ {d Y : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}, χ.IsPrimitive →
      ∀ (T : ℝ) (t : ℝ), 2 ≤ Y → 4 * Real.pi * |t * (Y : ℝ)| + 3 ≤ T →
      ‖(∫ u, quarterContourIntegrand χ Y t u) - ∫ u in Icc (-T) T, quarterContourIntegrand χ Y t u‖ ≤
        C * Real.sqrt (Y : ℝ) * Real.log (2 * (d : ℝ) * Y) := by
  let G := ∫ u, heightEnvelope u
  have hG : 0 ≤ G := integral_nonneg heightEnvelope_nonneg
  refine ⟨15000*812870*5*(1+G), by positivity, ?_⟩
  intro d Y hd χ hprim T t hY hT
  let L := Real.log (2 * (d : ℝ) * Y)
  let C := 15000 * 812870 * 5 * Real.sqrt (Y : ℝ) * L
  let s := Icc (-T) T
  let f := quarterContourIntegrand χ Y t
  have hL : 0 ≤ L := zero_le_one.trans (one_le_log_two_d_Y hY)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hY' : (0 : ℝ) < Y := Nat.cast_pos.mpr (by omega)
  have hY₁ : (1 : ℝ) ≤ Y := Nat.one_le_cast.mpr (by omega)
  have hf : Integrable f := integrable_quarter_line hGRH hprim (by omega) t
  change ‖(∫ u, f u) - ∫ u in s, f u‖ ≤ _
  rw [← integral_add_compl measurableSet_Icc hf, add_sub_cancel_left]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hp (u : ℝ) (hu : u ∈ sᶜ) : ‖f u‖ ≤ C * heightEnvelope u := by
    have hu' : T < |u| := lt_of_not_ge fun h => hu (abs_le.mp h)
    have hker := quarticKernel_norm_le_tail (lam := t * (Y : ℝ)) (σ := 1/4) (γ := u)
      (by norm_num) (by norm_num) (by linarith only [hu',hT])
    have hD := negLogDeriv_quarter hGRH hprim u
    have hD' : ‖negLogDerivL χ (quarterPoint u)‖ ≤
        812870 * Real.log (2 * (d : ℝ) * (2 + |u|)) := hD
    have hy : (Y : ℝ) ^ (1 / 4 : ℝ) ≤ Real.sqrt (Y : ℝ) := by
      rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hY₁ (by norm_num)
    dsimp [f,quarterContourIntegrand]
    rw [norm_mul, mellin_scaledTiltedBump_eq (show 1 ≤ Y by omega) t _, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hY', show (quarterPoint u).re = 1/4 by simp [quarterPoint]]
    have hk' : ‖quarticKernel (t * (Y:ℝ)) (quarterPoint u)‖ ≤ 15000 / (1+|u|)^2 := hker
    have h := mul_le_mul (mul_le_mul hy hk' (norm_nonneg _) (Real.sqrt_nonneg _)) hD'
      (norm_nonneg _) (by positivity)
    refine h.trans ?_
    have hm := mul_le_mul_of_nonneg_left (log_height_over_sq_le (d := d) hY u)
      (show 0 ≤ 15000 * 812870 * Real.sqrt (Y : ℝ) by positivity)
    dsimp [C,L]
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hm
  have hg := integrable_heightEnvelope.const_mul C
  calc ∫ u in sᶜ, ‖f u‖ ≤ ∫ u in sᶜ, C * heightEnvelope u :=
        setIntegral_mono_on hf.norm.integrableOn hg.integrableOn measurableSet_Icc.compl hp
    _ ≤ ∫ u, C * heightEnvelope u :=
        setIntegral_le_integral hg (Eventually.of_forall fun u => mul_nonneg hC (heightEnvelope_nonneg u))
    _ = C * G := integral_const_mul _ _
    _ ≤ _ := by dsimp [C,L]; nlinarith only [hC]

end FareyGoldbach
