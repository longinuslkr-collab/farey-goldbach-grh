import FareyGoldbach.VaughanTwistedSums
import FareyGoldbach.VaughanTypeI
import FareyGoldbach.VaughanTypeII
import FareyGoldbach.DivisorSecondMoment
import FareyGoldbach.ChenSwitchingAssembly

/-! # The large-conductor Vaughan mean value -/

open Finset ArithmeticFunction
open scoped Classical

namespace FareyGoldbach

private theorem bv_log_le {m N : ℕ} (hm : 1≤m) (h : m≤N) :
    Real.log (m:ℝ) ≤ chenSwitchLog N :=
  (Real.log_le_log (Nat.cast_pos.mpr hm) (Nat.cast_le.mpr h)).trans
    (log_le_chenSwitchLog (hm.trans h))

private theorem bv_mangoldt_norm_le {m N : ℕ} (hm : 1≤m) (h : m≤N) :
    ‖(vonMangoldt m:ℂ)‖ ≤ chenSwitchLog N := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg vonMangoldt_nonneg]
  exact vonMangoldt_le_log.trans (bv_log_le hm h)

private theorem bv_alpha_norm_le {U m N : ℕ} (hm : 1≤m) (h : m≤N) :
    ‖(vaughanAlpha U U m:ℂ)‖ ≤ chenSwitchLog N := by
  rw [Complex.norm_real,Real.norm_eq_abs]
  exact (vaughan_alpha_abs_le U U m).trans (bv_log_le hm h)

private theorem bv_coeff_energy_of_pointwise {t : ℕ} (a : ℕ → ℂ) {L : ℝ}
    (h : ∀ m∈Icc 1 t, ‖a m‖≤L) :
    (∑ m∈Icc 1 t, ‖a m‖^2)≤(t:ℝ)*L^2 := by
  calc
    _ ≤ ∑ _m∈Icc 1 t, L^2 :=
      sum_le_sum fun m hm => pow_le_pow_left₀ (norm_nonneg _) (h m hm) 2
    _ = _ := by simp [Nat.card_Icc]

private theorem bv_mu_div_energy {U t N : ℕ} (ht : t≤N) (hN : 1≤N) :
    (∑ m∈Icc 1 t, ‖(vaughanMuDiv U m:ℂ)‖^2)≤(t:ℝ)*((chenSwitchLog N)^2)^2 := by
  by_cases hp : 1≤t
  · have hL₁ := one_le_chenSwitchLog hN
    have hlog : 1+Real.log (t:ℝ)≤chenSwitchLog N := by
      have he : (t:ℝ)≤2*(N:ℝ) := (Nat.cast_le.mpr ht).trans (by
        have : (0:ℝ)≤N := Nat.cast_nonneg _
        linarith)
      exact add_le_add_right (Real.log_le_log (Nat.cast_pos.mpr hp) he) _
    calc
      _ ≤ ∑ m∈Icc 1 t, (m.divisors.card:ℝ)^2 := by
        apply sum_le_sum
        intro m _
        simp only [Complex.norm_real,Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (vaughan_mu_div_abs_le U m) 2
      _ ≤ (t:ℝ)*(1+Real.log (t:ℝ))^3 := sum_divisors_card_sq_le hp
      _ ≤ (t:ℝ)*(chenSwitchLog N)^3 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by
            have := Real.log_nonneg (Nat.one_le_cast.mpr hp)
            positivity) hlog 3) (Nat.cast_nonneg _)
      _ ≤ _ := by
        rw [←pow_mul]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL₁ (by norm_num)) (Nat.cast_nonneg _)
  · have : t=0 := by omega
    subst t
    simp

private theorem bv_initial_segment {q : ℕ} (χ : DirichletCharacter ℂ q)
    (X U : ℕ) :
    vaughanTwist χ X (vaughanCut U vonMangoldt) =
      ∑ m∈Icc 1 U, (if m≤X then (vonMangoldt m:ℂ) else 0)*χ (m:ZMod q) := by
  let T := Icc 1 (min X U)
  have h₁ : T ⊆ Icc 1 X := Icc_subset_Icc_right (min_le_left ..)
  have h₂ : T ⊆ Icc 1 U := Icc_subset_Icc_right (min_le_right ..)
  unfold vaughanTwist
  calc
    _ = ∑ m∈T, ((vaughanCut U vonMangoldt) m:ℂ)*χ (m:ZMod q) := by
      symm
      apply sum_subset h₁
      intro m hm h
      have hu : ¬m≤U := by simp only [T,mem_Icc,le_min_iff] at hm h; omega
      simp only [vaughanCut_apply,ite_eq_right hu,Complex.ofReal_zero,zero_mul]
    _ = ∑ m∈T, (if m≤X then (vonMangoldt m:ℂ) else 0)*χ (m:ZMod q) := by
      apply sum_congr rfl
      intro m hm
      have hh := mem_Icc.mp hm
      rw [vaughanCut_apply,ite_eq_left (hh.2.trans (min_le_right ..)),ite_eq_left (hh.2.trans (min_le_left ..))]
    _ = _ := by
      apply sum_subset h₂
      intro m hm h
      have hh : ¬m≤X := by simp only [T,mem_Icc,le_min_iff] at hm h; omega
      simp only [ite_eq_right hh,zero_mul]

private theorem bv_conductor_norm_sub_sub (q : ℕ)
    (A B C : DirichletCharacter ℂ q → ℂ) :
    chenPrimitiveNorm q (fun χ => A χ-B χ-C χ) ≤
      chenPrimitiveNorm q A+chenPrimitiveNorm q B+chenPrimitiveNorm q C := by
  by_cases hq : 0<q
  · let _ : NeZero q := ⟨hq.ne'⟩
    simp only [chenPrimitiveNorm_of_pos]
    simp only [←mul_add]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply sum_le_sum
    intro χ _
    exact (norm_sub_le ..).trans (add_le_add_left (norm_sub_le ..) _)
  · have h : q=0 := by omega
    subst q
    simp [chenPrimitiveNorm]

/-- The unconditional primitive conductor estimate above a positive cutoff.
The bound holds at every prefix of the original length. -/
theorem vaughan_large_conductor_mangoldt {N X D R : ℕ} (hN : 1≤N) (hX : X≤N)
    (hD : 1≤D) (hDN : D≤N) (hDs : (D:ℝ)≤Real.sqrt (N:ℝ)) (hR : 1≤R) :
    (∑ q∈Ioc R D, chenPrimitiveNorm q (fun χ => vaughanTwist χ X vonMangoldt)/(q:ℝ)) ≤
      13*(chenSwitchLog N)^2*(N:ℝ)^(19/20:ℝ) +
      600000*(chenSwitchLog N)^6*((N:ℝ)/R+(N:ℝ)^(9/10:ℝ)+(D:ℝ)*Real.sqrt N) := by
  let U := chenPowerLevel (1/5) N
  let L := chenSwitchLog N
  let G := (N:ℝ)/R+(N:ℝ)^(9/10:ℝ)+(D:ℝ)*Real.sqrt N
  let a (m : ℕ) := (vaughanAlpha U U m:ℂ)
  let b (m : ℕ) := (vaughanMuDiv U m:ℂ)
  let c (m : ℕ) := (vonMangoldt m:ℂ)
  let A (q : ℕ) (χ : DirichletCharacter ℂ q) :=
    vaughanTwist χ X (vaughanCut U vonMangoldt) -
      vaughanBilinear χ X 1 U 1 a (fun _ => 1) +
      vaughanBilinear χ X 1 U 1 (fun m => (vaughanMu U m:ℂ)) (fun w => (Real.log (w:ℝ):ℂ))
  let B (q : ℕ) (χ : DirichletCharacter ℂ q) :=
    vaughanBilinear χ X (U+1) (U*U) 1 a (fun _ => 1)
  let C (q : ℕ) (χ : DirichletCharacter ℂ q) :=
    vaughanBilinear χ X (U+1) (X/(U+1)) (U+1) b c
  let mean (F : (q : ℕ)→DirichletCharacter ℂ q→ℂ) :=
    ∑ q∈Ioc R D, chenPrimitiveNorm q (F q)/(q:ℝ)
  have hL₁ : 1≤L := one_le_chenSwitchLog hN
  have hL : 0≤L := zero_le_one.trans hL₁
  have hG : 0≤G := by dsimp [G]; positivity
  have ⟨hU,hUp,hU2,hUbig,hXbig⟩ := vaughan_typeII_cutoff_geometry hN hX
  change 1≤U at hU
  have hUN : U≤N := chenPowerLevel_le_self (by norm_num) hN
  have hUreal : (U:ℝ)≤(N:ℝ)^(1/5:ℝ) := Nat.floor_le (by positivity)
  have hA : mean A ≤ 13*L^2*(N:ℝ)^(19/20:ℝ) := by
    simp only [mean,A]
    have hre (q : ℕ) (χ : DirichletCharacter ℂ q) :
        vaughanTwist χ X (vaughanCut U vonMangoldt) = ∑ m∈Icc 1 U,
          (if m≤X then c m else 0)*χ (m:ZMod q) := bv_initial_segment χ X U
    simp_rw [hre]
    simpa only [vaughanBilinear,one_mul] using
      vaughan_typeI_mean_bound N U R D (fun m => X/m)
        (fun m => if m≤X then c m else 0) a (fun m => (vaughanMu U m:ℂ))
        hN hR hD hDN hUreal hDs
        (fun m _ => (Nat.div_le_self ..).trans hX)
        (by
          intro m hm
          split_ifs with hmx
          · exact bv_mangoldt_norm_le (mem_Icc.mp hm).1 (hmx.trans hX)
          · simpa only [norm_zero] using hL)
        (fun m hm => bv_alpha_norm_le (mem_Icc.mp hm).1 ((mem_Icc.mp hm).2.trans hUN))
        (fun m _ => by simpa only [Complex.norm_real,Real.norm_eq_abs] using vaughan_mu_abs_le U m)
  have hB : mean B ≤ 300000*L^3*(L*1)*G :=
    vaughan_typeII_large_conductor U (U*U) X D R N a (fun _ => 1) (fun _ => 1)
      hL zero_le_one hN hU hX (by simpa only [pow_two] using hU2) hDN hR hUp
      (by simpa only [pow_two] using hUbig)
      (fun t ht => bv_coeff_energy_of_pointwise a (fun m hm =>
        bv_alpha_norm_le (mem_Icc.mp hm).1 ((mem_Icc.mp hm).2.trans ht)))
      (fun _ _ => bv_coeff_energy_of_pointwise _ (by simp))
      (fun _ => le_rfl)
  have hC : mean C ≤ 300000*L^3*(L^2*L)*G :=
    vaughan_typeII_large_conductor U (X/(U+1)) X D R N b c (fun _ => U+1)
      (sq_nonneg _) hL hN hU hX ((Nat.div_le_self ..).trans hX) hDN hR hUp hXbig
      (fun _ ht => bv_mu_div_energy ht hN)
      (fun t ht => bv_coeff_energy_of_pointwise c (fun w hw =>
        bv_mangoldt_norm_le (mem_Icc.mp hw).1 ((mem_Icc.mp hw).2.trans ht)))
      (fun _ => Nat.succ_pos U)
  calc
    _ = mean (fun q χ => A q χ-B q χ-C q χ) := by
      unfold mean
      apply sum_congr rfl
      intro q _
      apply congrArg (fun z : ℝ => z/(q:ℝ))
      apply congrArg (chenPrimitiveNorm q)
      exact funext (fun χ => vaughan_twisted_identity χ X U hU)
    _ ≤ mean A+mean B+mean C := by
      unfold mean
      simp only [←Finset.sum_add_distrib,←add_div]
      exact sum_le_sum fun q _ =>
        div_le_div_of_nonneg_right (bv_conductor_norm_sub_sub q (A q) (B q) (C q)) (Nat.cast_nonneg _)
    _ ≤ 13*L^2*(N:ℝ)^(19/20:ℝ) + 300000*L^3*(L*1)*G + 300000*L^3*(L^2*L)*G :=
      add_le_add (add_le_add hA hB) hC
    _ ≤ _ := by
      change _ ≤ 13*L^2*(N:ℝ)^(19/20:ℝ) + 600000*L^6*G
      have hpow : L^4≤L^6 := pow_le_pow_right₀ hL₁ (by norm_num)
      nlinarith only [mul_le_mul_of_nonneg_right hpow hG]

end FareyGoldbach
