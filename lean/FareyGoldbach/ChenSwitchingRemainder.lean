import FareyGoldbach.ChenSwitchingAssembly
import FareyGoldbach.ChenLargeConductor
import FareyGoldbach.ChenSmallConductorInterval
import FareyGoldbach.ChenSwitchingAsymptotics
import FareyGoldbach.ChenSwitchingBudgets

/-! # The switched progression remainder -/

open Filter Finset
open scoped Topology Classical

namespace FareyGoldbach

private theorem chen_sum_conductors_split (E : ℕ→ℝ) (hE : ∀ q,0≤E q) (D R : ℕ) :
    (∑ q∈Finset.Ico 2 D,E q)≤
      (∑ q∈Finset.Icc 2 R,E q)+(∑ q∈Finset.Ioc R D,E q) := by
  rw [←Finset.sum_filter_add_sum_filter_not (Finset.Ico 2 D) (·≤R)]
  apply add_le_add
  · apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun q _ _ => hE q)
    intro q hq
    obtain ⟨hD,hR⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hD).1,hR⟩
  · apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun q _ _ => hE q)
    intro q hq
    obtain ⟨hD,hR⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_Ioc.mpr ⟨lt_of_not_ge hR,(Finset.mem_Ico.mp hD).2.le⟩

private theorem chenSwitch_conductor_cutoff_bounds {N : ℕ} (hN : 1≤N) :
    let L := chenSwitchLog N
    let R := ⌈L^12⌉₊
    1≤R ∧ L^12 ≤ (R:ℝ) ∧ (R:ℝ)≤2*L^12 := by
  let L := chenSwitchLog N
  let R := ⌈L^12⌉₊
  have hL := one_le_chenSwitchLog hN
  have h₁ : (1:ℝ)≤L^12 := one_le_pow₀ hL
  have h₂ : L^12≤(R:ℝ) := Nat.le_ceil _
  have h₃ : (R:ℝ)<L^12+1 := Nat.ceil_lt_add_one (by positivity)
  exact ⟨by exact_mod_cast h₁.trans h₂,h₂,by linarith only [h₁,h₃]⟩

private theorem chenSwitchBox_low_bound {N z y i k R : ℕ} {B : ℝ} (hB : 0≤B)
    (h : ∀ q : ℕ, ∀ [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → 2≤q → q≤R → ‖chenSwitchBoxSum N z y i k χ‖≤B) :
    (∑ q∈Finset.Icc 2 R,chenPrimitiveNorm q (chenSwitchBoxSum N z y i k)/(q:ℝ))≤(R:ℝ)*B := by
  calc _ ≤ ∑ _q∈Finset.Icc 2 R,B := by
          apply Finset.sum_le_sum
          intro q hq
          obtain ⟨hq₂,hqR⟩ := Finset.mem_Icc.mp hq
          let _ : NeZero q := ⟨by omega⟩
          exact chenPrimitiveNorm_div_le_of_bound _ hB (fun χ hχ => h q χ hχ hq₂ hqR)
    _ ≤ _ := by
      rw [Finset.sum_const,nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ hB
      rw [Nat.card_Icc]
      exact_mod_cast (show R+1-2≤R by omega)

private theorem chenSwitchBox_sum_le_of_local
    {N z y i k D R : ℕ} {C : ℝ}
    (hN : 1≤N) (hD : D≤N) (hy : (N:ℝ)^(1/4:ℝ)+1≤(y:ℝ)) (hR : 1≤R) (hC : 0≤C)
    (hsmall : ∀ q : ℕ, ∀ [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → 2≤q → q≤R →
      ‖chenSwitchBoxSum N z y i k χ‖≤
        C*((N:ℝ)/(chenSwitchLog N)^30+(N:ℝ)^(3/4:ℝ)*chenSwitchLog N)) :
    (∑ q∈Finset.Ico 2 D,chenPrimitiveNorm q (chenSwitchBoxSum N z y i k)/(q:ℝ))≤
       (R:ℝ)*(C*((N:ℝ)/(chenSwitchLog N)^30+(N:ℝ)^(3/4:ℝ)*chenSwitchLog N)) +
       100000*(chenSwitchLog N)^2*((N:ℝ)/R+(N:ℝ)^(7/8:ℝ)+(D:ℝ)*Real.sqrt N) := by
  let E (q : ℕ) := chenPrimitiveNorm q (chenSwitchBoxSum N z y i k)/(q:ℝ)
  have hE (q : ℕ) : 0≤E q := div_nonneg (chenPrimitiveNorm_nonneg ..) (Nat.cast_nonneg _)
  have hL := one_le_chenSwitchLog hN
  by_cases hne : (chenSwitchBoxPairs N z y i).Nonempty
  · apply (chen_sum_conductors_split E hE D R).trans
    apply add_le_add
    · exact chenSwitchBox_low_bound (by positivity) hsmall
    · obtain ⟨hW,hWN,hMW,hM,hWpow⟩ := chenSwitchBox_ranges hy hN hne
      exact chen_large_conductor_interval_bound (chenSwitchBoxM i) (chenSwitchBoxW N i) D R N
        (chenSwitchBoxA z y i k) (chenSwitchBoxB k) chenSwitchBoxLo (chenSwitchBoxHi N i)
        hN hW hWN hD hR hMW hM hWpow
        (fun m _ => chenSwitchBoxA_norm_le z y i k m) (fun w _ => chenSwitchBoxB_norm_le k w)
        (fun m _ => chenSwitchBoxLo_pos m) (fun m _ => chenSwitchBoxHi_le N i m)
  · have he : chenSwitchBoxPairs N z y i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have heq (q : ℕ) : E q=0 := by
      unfold E chenPrimitiveNorm
      split_ifs <;> simp [chenSwitchBoxSum_eq_zero_of_empty he]
    change (∑ q∈Finset.Ico 2 D,E q)≤_
    simp_rw [heq]
    rw [Finset.sum_const_zero]
    positivity

private theorem chenSwitching_finite_majorant
    {θ C : ℝ} (hθ : 0<θ) (hhalf : θ<1/2) (hC : 0≤C)
    {N : ℕ} (hN : 1≤N)
    (hy : (N:ℝ)^(1/4:ℝ)+1≤(chenUpperCutoff N:ℝ))
    (hz : (N:ℝ)^(1/16:ℝ)+1≤(chenLowerCutoff N:ℝ))
    (hsmall : ∀ k i q : ℕ, ∀ [NeZero q] (χ : DirichletCharacter ℂ q),
      k∈Finset.Ico 1 (chenPowerLevel θ N) → χ.IsPrimitive →
      2≤q → q≤⌈(chenSwitchLog N)^12⌉₊ →
      ‖chenSwitchBoxSum N (chenLowerCutoff N) (chenUpperCutoff N) i k χ‖≤
        C*((N:ℝ)/(chenSwitchLog N)^30+(N:ℝ)^(3/4:ℝ)*chenSwitchLog N)) :
    chenReducedError N (chenPowerLevel θ N) (chenSwitchingAPError N)≤
      (4+6*(2*C+200000))*((N:ℝ)/(chenSwitchLog N)^4 +
        (N:ℝ)^max (15/16:ℝ) (θ+1/2)*(chenSwitchLog N)^20) := by
  let L := chenSwitchLog N
  let R := ⌈L^12⌉₊
  let D := chenPowerLevel θ N
  let β := max (15/16:ℝ) (θ+1/2)
  let H := (N:ℝ)^β
  let B := (2*C+200000)*((N:ℝ)/L^7+H*L^16)
  have hn : (1:ℝ)≤N := Nat.one_le_cast.mpr hN
  have hp : (0:ℝ)<N := zero_lt_one.trans_le hn
  have hL : 1≤L := one_le_chenSwitchLog hN
  have hH : 0≤H := by dsimp only [H]; positivity
  obtain ⟨hR,hR₁,hR₂⟩ := chenSwitch_conductor_cutoff_bounds hN
  have hRpos : (0:ℝ)<R := Nat.cast_pos.mpr hR
  have hD : D≤N := chenPowerLevel_le_self (by linarith only [hhalf]) hN
  have hzpos : 0<chenLowerCutoff N := by
    have hz₀ : (0:ℝ)<chenLowerCutoff N := by
      exact (by positivity : 0<(N:ℝ)^(1/16:ℝ)+1).trans_le hz
    exact Nat.cast_pos.mp hz₀
  have hβ₁ : (15/16:ℝ)≤β := le_max_left ..
  have hM : (N:ℝ)^(3/4:ℝ)≤H := Real.rpow_le_rpow_of_exponent_le hn (by linarith only [hβ₁])
  have hW : (N:ℝ)^(7/8:ℝ)≤H := Real.rpow_le_rpow_of_exponent_le hn (by linarith only [hβ₁])
  have hDpow : (D:ℝ)*Real.sqrt N≤H := by
    rw [Real.sqrt_eq_rpow]
    calc _ ≤ (N:ℝ)^θ*(N:ℝ)^(1/2:ℝ) := mul_le_mul_of_nonneg_right
          (Nat.floor_le (zero_le_one.trans (Real.one_le_rpow hn hθ.le))) (by positivity)
      _ = (N:ℝ)^(θ+1/2) := by rw [Real.rpow_add hp]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn (le_max_right ..)
  have hZpow : (N:ℝ)/(chenLowerCutoff N:ℝ)≤H := by
    calc _ ≤ (N:ℝ)/(N:ℝ)^(1/16:ℝ) :=
          div_le_div_of_nonneg_left hp.le (by positivity) (by linarith only [hz])
      _ = (N:ℝ)^(15/16:ℝ) := by
        rw [show (15/16:ℝ)=1-1/16 by norm_num,Real.rpow_sub hp,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn hβ₁
  have hB : 0≤B := by dsimp only [B]; positivity
  have hb (k : ℕ) (hk : k∈Finset.Ico 1 D) (i : ℕ) (_hi : i∈Finset.range (N.log2+1)) :
      (∑ q∈Finset.Ico 2 D,chenPrimitiveNorm q
          (chenSwitchBoxSum N (chenLowerCutoff N) (chenUpperCutoff N) i k)/(q:ℝ))≤B := by
    apply (chenSwitchBox_sum_le_of_local hN hD hy hR hC
      (fun q _ χ hχ hq hqR => hsmall k i q χ hk hχ hq hqR)).trans
    have hlow : (N:ℝ)/L^30+(N:ℝ)^(3/4:ℝ)*L ≤ (N:ℝ)/L^30+H*L :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hM (zero_le_one.trans hL))
    have hhigh : (N:ℝ)/R+(N:ℝ)^(7/8:ℝ)+(D:ℝ)*Real.sqrt N ≤
        (N:ℝ)/R+H+H := add_le_add (add_le_add (le_refl _) hW) hDpow
    calc _ ≤ (R:ℝ)*(C*((N:ℝ)/L^30+H*L))+
              100000*L^2*((N:ℝ)/R+H+H) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hlow hC) (Nat.cast_nonneg _))
              (mul_le_mul_of_nonneg_left hhigh (by positivity))
      _ ≤ B := chenSwitchBox_budget_absorb hL hp.le hH hRpos hC hR₁ hR₂
  apply (chenSwitchingReducedError_le_of_boxes hN hzpos hD hB hb).trans
  apply le_trans (add_le_add (mul_le_mul_of_nonneg_left hZpow (by positivity)) (le_refl _))
  exact chenSwitchTotal_budget_absorb hL hp.le hH hC

/-- The switched sequence has distribution to every fixed level used by the
Chen sieve, under the reusable small-conductor prime input. -/
theorem chen_switching_reduced_error_of_smallConductor
    (hSmall : SmallConductorPrimeTwists) {θ : ℝ} (hθ : 11/24<θ) (hhalf : θ<1/2)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,
      chenReducedError N (chenPowerLevel θ N) (chenSwitchingAPError N)≤ε*chenLogScale N := by
  obtain ⟨C,hC,hCevt⟩ := chen_small_conductor_interval_bound hSmall
  have hβ : max (15/16:ℝ) (θ+1/2)<1 := max_lt (by norm_num) (by linarith only [hhalf])
  have hBudget := chenSwitching_budget_small hβ
    (show (0:ℝ)≤4+6*(2*C+200000) by positivity) hε
  filter_upwards [hBudget,hCevt,chenSwitching_cutoffs_eventually,eventually_ge_atTop (1:ℕ)] with
    N hBudget hsmall hcuts hN
  obtain ⟨hy,hz⟩ := hcuts
  apply (chenSwitching_finite_majorant (by linarith only [hθ]) hhalf hC.le hN hy hz ?_).trans hBudget
  intro k i q _ χ hk hχ hq hqR
  let z := chenLowerCutoff N
  let y := chenUpperCutoff N
  have hk₁ := (Finset.mem_Ico.mp hk).1
  have hkN := (Finset.mem_Ico.mp hk).2.le.trans
    (chenPowerLevel_le_self (by linarith only [hhalf]) hN)
  by_cases hne : (chenSwitchBoxPairs N z y i).Nonempty
  · obtain ⟨_,_,hMW,hM,_⟩ := chenSwitchBox_ranges hy hN hne
    have hlo (m : ℕ) (_hm : m∈Finset.Icc 1 (chenSwitchBoxM i))
        (hm₀ : chenSwitchBoxA z y i k m≠0) :
        (N:ℝ)^(1/4:ℝ)+1≤(chenSwitchBoxLo m:ℝ) := by
      have he : chenSwitchBoxActive z y i m ∧ m.Coprime k := by
        by_contra hn
        exact hm₀ (ite_eq_right hn)
      exact hy.trans (Nat.cast_le.mpr (he.1.2.2.2.2.2.trans (le_max_right ..)))
    exact hsmall (chenSwitchBoxM i) (chenSwitchBoxW N i) k q χ
      (chenSwitchBoxA z y i k) chenSwitchBoxLo (chenSwitchBoxHi N i)
      hχ hq hqR hk₁ hkN hMW hM
      (fun m _ => chenSwitchBoxA_norm_le z y i k m) hlo
      (fun m _ => chenSwitchBoxHi_le N i m)
  · have hL := one_le_chenSwitchLog hN
    have he := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [chenSwitchBoxSum_eq_zero_of_empty he,norm_zero]
    positivity

end FareyGoldbach
