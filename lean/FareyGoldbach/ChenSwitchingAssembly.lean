import FareyGoldbach.ChenSwitchingBoxes
import FareyGoldbach.ChenSwitchingPrincipal
import FareyGoldbach.ChenConductorExpansion
import FareyGoldbach.ChenIntervalLargeSieve

/-! # From boxwise character bounds to the switched progression discrepancy -/

open Finset
open scoped Classical

namespace FareyGoldbach

theorem chenPrimitiveNorm_div_eq_avg {q : ℕ} [NeZero q] (F : DirichletCharacter ℂ q → ℂ) :
    chenPrimitiveNorm q F/(q:ℝ) =
      (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (·.IsPrimitive), ‖F χ‖) /
        (q.totient:ℝ) := by
  rw [chenPrimitiveNorm_of_pos F]
  have hq : (q:ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  field_simp [hq]

theorem chenPrimitiveNorm_div_le_of_bound {q : ℕ} [NeZero q] (F : DirichletCharacter ℂ q → ℂ)
    {B : ℝ} (hB : 0≤B) (hF : ∀ χ, χ.IsPrimitive → ‖F χ‖≤B) :
    chenPrimitiveNorm q F/(q:ℝ)≤B := by
  let S := (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (·.IsPrimitive)
  have hφ : (0:ℝ)<q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  rw [chenPrimitiveNorm_div_eq_avg]
  apply (div_le_iff₀ hφ).mpr
  have hc : S.card≤q.totient := by
    apply (Finset.card_le_card (Finset.filter_subset ..)).trans_eq
    rw [Finset.card_univ,←Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  calc _ ≤ ∑ _χ∈S, B := Finset.sum_le_sum fun χ hχ => hF χ (Finset.mem_filter.mp hχ).2
    _ = B*(S.card:ℝ) := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hc) hB

theorem chenMaskedPrimitiveMass_le_boxes {q : ℕ} [NeZero q] (N z y k : ℕ) :
    chenMaskedPrimitiveMass (chenSwitchPairs N z y) q k/(q.totient:ℝ) ≤
      ∑ i∈Finset.range (N.log2+1), chenPrimitiveNorm q (chenSwitchBoxSum N z y i k)/(q:ℝ) := by
  let S := (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (·.IsPrimitive)
  rw [chenMaskedPrimitiveMass_of_pos]
  simp_rw [chenMaskedChar,chenSwitch_masked_sum_eq_sum_boxes]
  calc _ ≤ (∑ χ∈S, ∑ i∈Finset.range (N.log2+1), ‖chenSwitchBoxSum N z y i k χ‖)/(q.totient:ℝ) := by
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          exact Finset.sum_le_sum fun χ _ => norm_sum_le _ _
    _ = _ := by
      rw [Finset.sum_comm (s:=S)]
      simp only [Finset.sum_div,chenPrimitiveNorm_div_eq_avg,S]

theorem chenSwitchingReducedError_le_of_boxes {N D : ℕ} {B : ℝ}
    (hN : 1≤N) (hz : 0<chenLowerCutoff N) (hD : D≤N) (hB : 0≤B)
    (hboxes : ∀ k∈Finset.Ico 1 D, ∀ i∈Finset.range (N.log2+1),
      (∑ q∈Finset.Ico 2 D,
        chenPrimitiveNorm q (chenSwitchBoxSum N (chenLowerCutoff N) (chenUpperCutoff N) i k)/(q:ℝ))≤B) :
    chenReducedError N D (chenSwitchingAPError N)≤
      4*(chenSwitchLog N)^3*((N:ℝ)/(chenLowerCutoff N:ℝ)) + 6*(chenSwitchLog N)^3*B := by
  let z := chenLowerCutoff N
  let y := chenUpperCutoff N
  let P := chenSwitchPairs N z y
  let L := chenSwitchLog N
  let R := Finset.Ico 1 D
  have hinj : Set.InjOn (fun x : ℕ×ℕ => x.1*x.2) P := chenSwitchPairs_product_injective N z y
  have hprod (x : ℕ×ℕ) (hx : x∈P) : 0<x.1*x.2 ∧ x.1*x.2≤N :=
    ⟨chenSwitchPairs_product_pos hx,(mem_chenSwitchPairs_iff.mp hx).2.2.2.2.le⟩
  have hrough (x : ℕ×ℕ) (hx : x∈P) (p : ℕ) (hp : p.Prime) (hd : p∣x.1*x.2) :
      z≤p := chenSwitchPairs_rough hx hp hd
  have hpc := chenPair_principal_correction P hN hz hD hinj hprod hrough
  have hsum (k : ℕ) (hk : k∈R) :
      ∑ q∈Finset.Ico 2 D, chenMaskedPrimitiveMass P q k/(q.totient:ℝ)≤3*L*B := by
    calc _ ≤ ∑ q∈Finset.Ico 2 D, ∑ i∈Finset.range (N.log2+1),
            chenPrimitiveNorm q (chenSwitchBoxSum N z y i k)/(q:ℝ) := by
            apply Finset.sum_le_sum
            intro q hq
            let _ : NeZero q := ⟨by have := (Finset.mem_Ico.mp hq).1; omega⟩
            exact chenMaskedPrimitiveMass_le_boxes N z y k
      _ ≤ ∑ _i∈Finset.range (N.log2+1), B := by
        rw [Finset.sum_comm]
        exact Finset.sum_le_sum (fun i hi => hboxes k hk i hi)
      _ ≤ _ := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_right (chen_log2_range_card_le hN) hB
  have hR : R ⊆ Finset.Icc 1 N := fun k hk =>
    Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hk).1,(Finset.mem_Ico.mp hk).2.le.trans hD⟩
  have hL : 0≤L := zero_le_one.trans (one_le_chenSwitchLog hN)
  have htot :
      ∑ k∈R, (1/(k.totient:ℝ))*(∑ q∈Finset.Ico 2 D,chenMaskedPrimitiveMass P q k/(q.totient:ℝ)) ≤
        6*L^3*B := by
    calc _ ≤ ∑ k∈R,(1/(k.totient:ℝ))*(3*L*B) :=
          Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hsum k hk) (by positivity)
      _ = (∑ k∈R, 1/(k.totient:ℝ))*(3*L*B) := by rw [Finset.sum_mul]
      _ ≤ (2*L^2)*(3*L*B) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact (Finset.sum_le_sum_of_subset_of_nonneg hR (fun _ _ _ => by positivity)).trans
          (chen_sum_inv_totient_le hN)
      _ = _ := by ring
  apply le_trans _ (add_le_add hpc htot)
  have hpair := chenPairAP_sum_le P N D
  simpa only [chenReducedError,chenSwitchingAPError,chenAPError,P,z,y,
    chenSwitchPairs_card_progression,chenUnrestrictedB_card_eq_pairs] using hpair

end FareyGoldbach
