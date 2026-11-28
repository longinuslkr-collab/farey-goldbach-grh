import FareyGoldbach.BombieriVinogradovInterface
import FareyGoldbach.BombieriVinogradovBudget
import FareyGoldbach.VaughanMeanValue

/-! # A Bombieri–Vinogradov reduction at fixed powers below one half -/

open Filter Finset ArithmeticFunction
open scoped Topology Classical

namespace FareyGoldbach

private theorem bv_split_conductors (E : ℕ → ℝ) (hE : ∀ q, 0≤E q) (D R : ℕ) :
    (∑ q∈Ico 2 D,E q) ≤ (∑ q∈Icc 2 R,E q) + ∑ q∈Ioc R D,E q := by
  rw [←Finset.sum_filter_add_sum_filter_not (Ico 2 D) (·≤R)]
  apply add_le_add
  · apply sum_le_sum_of_subset_of_nonneg _ (fun q _ _ => hE q)
    intro q hq
    obtain ⟨hd,hr⟩ := mem_filter.mp hq
    exact mem_Icc.mpr ⟨(mem_Ico.mp hd).1,hr⟩
  · apply sum_le_sum_of_subset_of_nonneg _ (fun q _ _ => hE q)
    intro q hq
    obtain ⟨hd,hr⟩ := mem_filter.mp hq
    exact mem_Ioc.mpr ⟨lt_of_not_ge hr,(mem_Ico.mp hd).2.le⟩

private theorem bv_small_conductors_sum {R X : ℕ} {B : ℝ} (hB : 0≤B)
    (h : ∀ q : ℕ, ∀ [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → 2≤q → q≤R → ‖vaughanTwist χ X vonMangoldt‖ ≤ B) :
    (∑ q∈Icc 2 R,chenPrimitiveNorm q (fun χ => vaughanTwist χ X vonMangoldt)/(q:ℝ))≤
      (R:ℝ)*B := by
  calc
    _ ≤ ∑ _q ∈ Icc 2 R,B := by
      apply sum_le_sum
      intro q hq
      obtain ⟨hq₂,hqR⟩ := mem_Icc.mp hq
      let _ : NeZero q := ⟨by omega⟩
      exact chenPrimitiveNorm_div_le_of_bound _ hB (fun χ hχ => h q χ hχ hq₂ hqR)
    _ = ((Icc 2 R).card:ℝ)*B := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact Nat.cast_le.mpr (by rw [Nat.card_Icc]; omega)

/-- At every fixed power below one half, the small-conductor prime estimates
and the unconditional Vaughan bound give the needed primitive first moment.
The estimate is simultaneous for every sharp prefix X ≤ N. -/
theorem bombieri_vinogradov_of_smallConductor (hSmall : SmallConductorPrimeTwists) :
    ChenPrimitiveMangoldtBV := by
  obtain ⟨C,hC,hsmall⟩ := bv_small_conductor_mangoldt hSmall
  intro θ hθ hhalf ε hε
  filter_upwards [hsmall,bv_mangoldt_budget_small hhalf hC.le hε,
    eventually_ge_atTop (2:ℕ)] with N hsmallN hbudget hN
  intro X hX
  let D := chenPowerLevel θ N
  let L := chenSwitchLog N
  let R := ⌈L^12⌉₊
  let B := C*((N:ℝ)/L^29+Real.sqrt (N:ℝ)*L)
  let E (q : ℕ) := chenPrimitiveNorm q (fun χ => vaughanTwist χ X vonMangoldt)/(q:ℝ)
  have hE (q : ℕ) : 0≤E q :=
    div_nonneg (chenPrimitiveNorm_nonneg ..) (Nat.cast_nonneg _)
  have hN₁ : 1≤N := by omega
  have hNr : (1:ℝ)≤N := Nat.one_le_cast.mpr hN₁
  have hθ₀ : 0≤θ := by linarith only [hθ]
  have hR : 1≤R := (bv_cutoff_bounds hN₁).1
  have hD : 1≤D := (Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg _) _)).mpr (by
    simpa only [Nat.cast_one] using Real.one_le_rpow hNr hθ₀)
  have hDN : D≤N := chenPowerLevel_le_self (by linarith only [hhalf]) hN₁
  have hDs : (D:ℝ)≤Real.sqrt (N:ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans
      (Real.rpow_le_rpow_of_exponent_le hNr hhalf.le)
  have hB : 0≤B := by
    have hL := one_le_chenSwitchLog hN₁
    dsimp only [B,L]
    positivity
  change (∑ q∈Ico 2 D,E q) ≤ _
  refine (bv_split_conductors E hE D R).trans ?_
  refine (add_le_add (bv_small_conductors_sum hB ?_)
    (vaughan_large_conductor_mangoldt hN₁ hX hD hDN hDs hR)).trans ?_
  · exact fun q _ χ hχ hq hqR => hsmallN X q χ hX hχ hq hqR
  · change (R:ℝ)*B +
        (13*L^2*(N:ℝ)^(19/20:ℝ) + 600000*L^6*((N:ℝ)/R+(N:ℝ)^(9/10:ℝ)+(D:ℝ)*Real.sqrt N))
        ≤ _
    dsimp only [B]
    rw [←add_assoc,←mul_assoc]
    exact hbudget

end FareyGoldbach
