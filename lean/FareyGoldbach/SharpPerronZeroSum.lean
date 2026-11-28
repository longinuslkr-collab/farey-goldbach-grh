import FareyGoldbach.SmoothedExplicitFormula

/-! # Summing a Mellin kernel over the nontrivial Dirichlet zeros -/

namespace FareyGoldbach

open scoped Classical

/-- A pointwise majorant multiplied by the logarithmic cost of counting zeros
in a unit band controls that entire band, with multiplicity. -/
theorem kernelZeroTerm_band_le (hGRH : DirichletGRH) {d : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) (K : ℂ→ℂ) (k : ℤ) {B : ℝ}
    (hB₀ : 0≤B) (hK : ∀ ρ∈bandZeros χ k,
      ‖K ρ‖*Real.log (2*(d:ℝ)*(2+|(k:ℝ)|))≤B) :
    (∑ ρ∈bandZeros χ k, ‖kernelZeroTerm χ K ρ‖) ≤ 217*B := by
  let L := Real.log (2*(d:ℝ)*(2+|(k:ℝ)|))
  have hL : 0<L := zero_lt_one.trans_le (one_le_log_two_mul_d_mul d (k:ℝ))
  have hcnt : (∑ ρ∈bandZeros χ k,(zeroMult χ ρ:ℝ))≤217*L := by
    apply zeroCount_unit hGRH hprim (k:ℝ)
    intro ρ hρ
    obtain ⟨hre,h0,hlo,hhi⟩ := (mem_bandZeros_iff hGRH hprim).mp hρ
    exact ⟨hre,h0,by rw [abs_le]; constructor <;> linarith only [hlo,hhi]⟩
  calc
    _ ≤ ∑ ρ∈bandZeros χ k,(zeroMult χ ρ:ℝ)*(B/L) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      obtain ⟨hre,h₀,_,_⟩ := (mem_bandZeros_iff hGRH hprim).mp hρ
      rw [kernelZeroTerm,ite_eq_left ⟨hre,h₀⟩,norm_mul,Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left ((le_div_iff₀ hL).mpr (hK ρ hρ)) (Nat.cast_nonneg _)
    _ = (∑ ρ∈bandZeros χ k,(zeroMult χ ρ:ℝ))*(B/L) := (Finset.sum_mul ..).symm
    _ ≤ (217*L)*(B/L) := mul_le_mul_of_nonneg_right hcnt (div_nonneg hB₀ hL.le)
    _ = 217*B := by field_simp

/-- Absolute summability and a uniform global bound follow from one summable
majorant on the integer-indexed unit bands. -/
theorem kernelZeroTerm_tsum_le_of_bandBound (hGRH : DirichletGRH) {d : ℕ} [NeZero d]
    {χ : DirichletCharacter ℂ d} (hprim : χ.IsPrimitive) (K : ℂ→ℂ) (bandBound : ℤ→ℝ)
    (hB₀ : ∀ k,0≤bandBound k) (hB : Summable bandBound)
    (hK : ∀ k ρ, ρ∈bandZeros χ k →
      ‖K ρ‖*Real.log (2*(d:ℝ)*(2+|(k:ℝ)|))≤bandBound k) :
    Summable (fun ρ : ℂ => ‖kernelZeroTerm χ K ρ‖) ∧
      (∑' ρ : ℂ, ‖kernelZeroTerm χ K ρ‖)≤217*∑' k,bandBound k := by
  have hfinite (S : Finset ℂ) :
      (∑ ρ∈S,‖kernelZeroTerm χ K ρ‖)≤217*∑' k,bandBound k := by
    let J := S.image (fun ρ => ⌊ρ.im⌋)
    have hsub : S.filter (fun ρ => 0<ρ.re ∧ entireL χ ρ=0) ⊆ J.biUnion (bandZeros χ) := by
      intro ρ hρ
      obtain ⟨hρS,hre,h0⟩ := Finset.mem_filter.mp hρ
      exact Finset.mem_biUnion.mpr ⟨⌊ρ.im⌋,Finset.mem_image_of_mem _ hρS,
        (mem_bandZeros_iff hGRH hprim).mpr ⟨hre,h0,Int.floor_le _,Int.lt_floor_add_one _⟩⟩
    calc
      _ = ∑ ρ∈S.filter (fun ρ => 0<ρ.re ∧ entireL χ ρ=0), ‖kernelZeroTerm χ K ρ‖ := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun ρ _ => ?_
        unfold kernelZeroTerm
        split_ifs <;> simp
      _ ≤ ∑ ρ∈J.biUnion (bandZeros χ),‖kernelZeroTerm χ K ρ‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)
      _ = ∑ k∈J,∑ ρ∈bandZeros χ k,‖kernelZeroTerm χ K ρ‖ :=
        Finset.sum_biUnion fun _ _ _ _ hne => bandZeros_disjoint χ hne
      _ ≤ ∑ k∈J,217*bandBound k := Finset.sum_le_sum fun k _ =>
        kernelZeroTerm_band_le hGRH hprim K k (hB₀ k) (hK k)
      _ = 217*∑ k∈J,bandBound k := (Finset.mul_sum ..).symm
      _ ≤ 217*∑' k,bandBound k :=
        mul_le_mul_of_nonneg_left (hB.sum_le_tsum J fun k _ => hB₀ k) (by norm_num)
  exact ⟨summable_of_sum_le (fun _ => norm_nonneg _) hfinite,
    Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) hfinite⟩

end FareyGoldbach
