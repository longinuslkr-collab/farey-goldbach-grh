import FareyGoldbach.BVMeanAbel
import FareyGoldbach.ChenPrimeAPDistributionOfGRH

/-! # The cofactor mask in the prime progression discrepancy -/

open Finset
open scoped Classical

namespace FareyGoldbach

private def bvPrimePair : ℕ ↪ ℕ×ℕ := ⟨fun p => (1,p),fun _ _ h => congrArg Prod.snd h⟩

private def bvPrimePairs (N : ℕ) : Finset (ℕ×ℕ) := N.primesLE.map bvPrimePair

private theorem bv_bad_prime_card {k : ℕ} (N : ℕ) (hk : 1≤k) :
    (N.primesLE.filter fun p => ¬p.Coprime k).card ≤ k.primeFactors.card := by
  apply card_le_card
  intro p hp
  obtain ⟨hp,hn⟩ := mem_filter.mp hp
  have hpr := (Nat.mem_primesLE.mp hp).2
  exact Nat.mem_primeFactors.mpr ⟨hpr,by simpa [hpr.coprime_iff_not_dvd] using hn,by omega⟩

private theorem bv_masked_prime_sum {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ)
    {k : ℕ} (hk : 1≤k) :
    ‖∑ x∈bvPrimePairs N,chenMaskedChar χ k x.1*chenMaskedChar χ k x.2‖ ≤
      ‖∑ p∈N.primesLE,χ p‖+(k.primeFactors.card:ℝ) := by
  let T := N.primesLE.filter fun p => ¬p.Coprime k
  have he : (∑ x∈bvPrimePairs N,chenMaskedChar χ k x.1*chenMaskedChar χ k x.2) =
      (∑ p∈N.primesLE,χ p)-∑ p∈T,χ p := by
    rw [bvPrimePairs,sum_map]
    change (∑ p∈N.primesLE, chenMaskedChar χ k 1 * chenMaskedChar χ k p) = _
    simp only [chenMaskedChar,ite_eq_left (Nat.coprime_one_left k),Nat.cast_one,map_one,one_mul]
    rw [←Finset.sum_filter]
    have h := Finset.sum_filter_add_sum_filter_not N.primesLE (fun p => p.Coprime k) (fun p => χ p)
    dsimp only [T]
    exact eq_sub_of_add_eq h
  rw [he]
  apply (norm_sub_le ..).trans
  apply add_le_add_right
  calc _ ≤ ∑ p∈T, ‖χ p‖ := norm_sum_le _ _
    _ ≤ ∑ _p∈T,(1:ℝ) := sum_le_sum fun p _ => χ.norm_le_one p
    _ ≤ (k.primeFactors.card:ℝ) := by simpa [T] using (Nat.cast_le (α:=ℝ)).mpr (bv_bad_prime_card N hk)

private theorem bv_bad_prime_log {k N : ℕ} (hk : 1≤k) (hkN : k≤N) :
    (k.primeFactors.card:ℝ)≤2*chenSwitchLog N := by
  apply (primeFactors_card_le_two_log hk).trans
  have hkR : (0:ℝ)<k := Nat.cast_pos.mpr hk
  have hlog := Real.log_le_log (by positivity : 0<2*(k:ℝ))
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hkN : (k:ℝ)≤N) (by norm_num : (0:ℝ)≤2))
  unfold chenSwitchLog
  linarith only [hlog]

private theorem bv_masked_prime_average (N D k : ℕ) (hk : 1≤k) (hkN : k≤N) :
    (∑ q∈Ico 2 D,chenMaskedPrimitiveMass (bvPrimePairs N) q k/(q.totient:ℝ)) ≤
    bvPrimitiveAverage D (fun _ χ => ‖∑ p∈N.primesLE,χ p‖)+(D:ℝ)*(2*chenSwitchLog N) := by
  let F (q : ℕ) (χ : DirichletCharacter ℂ q) :=
    ∑ x∈bvPrimePairs N,chenMaskedChar χ k x.1*chenMaskedChar χ k x.2
  have hF : (∑ q∈Ico 2 D,chenMaskedPrimitiveMass (bvPrimePairs N) q k/(q.totient:ℝ)) =
      bvPrimitiveAverage D (fun q χ => ‖F q χ‖) := by
    rw [bvPrimitiveAverage_norm]
    apply sum_congr rfl
    intro q hq
    let _ : NeZero q := ⟨by have := (mem_Ico.mp hq).1; omega⟩
    rw [chenPrimitiveNorm_div_eq_avg,chenMaskedPrimitiveMass_of_pos]
  rw [hF]
  apply (bvPrimitiveAverage_mono (fun q _ χ _ =>
    (bv_masked_prime_sum χ N hk).trans (add_le_add_right (bv_bad_prime_log hk hkN) _))).trans
  rw [bvPrimitiveAverage_add]
  have hL := one_le_chenSwitchLog (hk.trans hkN)
  exact add_le_add_right (bvPrimitiveAverage_const_le D (by positivity : 0≤2*chenSwitchLog N)) _

/-- The character majorant permits a separate reduced residue for each modulus. -/
theorem bvReducedPrimeClasses_of_average {N D : ℕ} (K : ℕ) (a : ℕ → ℕ)
    (ha : ∀ d, 0<d → d.Coprime K → (a d).Coprime d) (hN : 1≤N) (hD : D≤N) {B : ℝ}
    (hB : 0≤B) (havg : bvPrimitiveAverage D (fun _ χ => ‖∑ p∈N.primesLE,χ p‖)≤B) :
    chenReducedError K D (fun d => ((N.primesLE.filter fun p => p%d=a d%d).card:ℝ) -
      (N.primeCounting:ℝ)/(d.totient:ℝ)) ≤
      (D:ℝ)*(2*chenSwitchLog N)+
        2*(chenSwitchLog N)^2*(B+(D:ℝ)*(2*chenSwitchLog N)) := by
  let L := chenSwitchLog N
  have hL : 1≤L := one_le_chenSwitchLog hN
  let R := (Ico 1 D).filter (fun d => d.Coprime K)
  have hpc (d : ℕ) (hd : d∈R) :
      (((bvPrimePairs N).filter fun x => ¬(x.1*x.2).Coprime d).card:ℝ)/(d.totient:ℝ) ≤ 2*L := by
    obtain ⟨hd1,hdD⟩ := mem_Ico.mp (mem_filter.mp hd).1
    have hφ : (1:ℝ)≤d.totient := Nat.one_le_cast.mpr (Nat.totient_pos.mpr hd1)
    apply (div_le_self (Nat.cast_nonneg _) hφ).trans
    rw [bvPrimePairs,Finset.filter_map,Finset.card_map]
    change ((N.primesLE.filter fun p => ¬(1*p).Coprime d).card:ℝ) ≤ _
    simp only [one_mul]
    exact (Nat.cast_le.mpr (bv_bad_prime_card N hd1)).trans (bv_bad_prime_log hd1 (hdD.le.trans hD))
  have hp : (∑ d∈R, (((bvPrimePairs N).filter fun x => ¬(x.1*x.2).Coprime d).card:ℝ)/(d.totient:ℝ))
      ≤ (D:ℝ)*(2*L) := by
    apply (sum_le_sum hpc).trans
    rw [sum_const,nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact Nat.cast_le.mpr ((card_filter_le ..).trans (by simp [Nat.card_Ico]))
  let bound := B+(D:ℝ)*(2*L)
  have hK : 0≤bound := by dsimp [bound]; positivity
  have hmass (k : ℕ) (hk : k∈Ico 1 D) :
      (∑ q∈Ico 2 D, chenMaskedPrimitiveMass (bvPrimePairs N) q k/(q.totient:ℝ))≤bound := by
    obtain ⟨hk1,hkD⟩ := mem_Ico.mp hk
    exact (bv_masked_prime_average N D k hk1 (hkD.le.trans hD)).trans (add_le_add_left havg _)
  have htot :
      (∑ k∈Ico 1 D,(1/(k.totient:ℝ))*
        (∑ q∈Ico 2 D,chenMaskedPrimitiveMass (bvPrimePairs N) q k/(q.totient:ℝ)))≤2*L^2*bound := by
    calc _ ≤ ∑ k∈Ico 1 D,(1/(k.totient:ℝ))*bound := sum_le_sum fun k hk =>
            mul_le_mul_of_nonneg_left (hmass k hk) (by positivity)
      _ = (∑ k∈Ico 1 D,1/(k.totient:ℝ))*bound := by rw [sum_mul]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hK
        apply le_trans _ (chen_sum_inv_totient_le hN)
        apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
        intro k hk
        exact mem_Icc.mpr ⟨(mem_Ico.mp hk).1,(mem_Ico.mp hk).2.le.trans hD⟩
  apply le_trans _ (add_le_add hp htot)
  have h := sum_le_sum (s:=R) (fun d hd =>
    chenPairAP_discrepancy_le (bvPrimePairs N) (mem_Ico.mp (mem_filter.mp hd).1).1
      (ha d (mem_Ico.mp (mem_filter.mp hd).1).1 (mem_filter.mp hd).2))
  simp_rw [add_div] at h
  rw [sum_add_distrib] at h
  apply le_trans _ (h.trans (add_le_add_right (chenConductorMass_sum_le (bvPrimePairs N) K D) _))
  apply le_of_eq
  apply sum_congr rfl
  intro d _
  rw [bvPrimePairs,card_map,Nat.primesLE_card_eq_primeCounting,filter_map,card_map]
  change |((N.primesLE.filter fun p => p%d=a d%d).card:ℝ)-_| =
    |((N.primesLE.filter fun p => 1*p%d=a d%d).card:ℝ)-_|
  simp only [one_mul]

theorem bvReducedPrimeError_of_average {N D : ℕ} (hN : 1≤N) (hD : D≤N) {B : ℝ}
    (hB : 0≤B) (havg : bvPrimitiveAverage D (fun _ χ => ‖∑ p∈N.primesLE,χ p‖)≤B) :
    chenReducedError N D (chenPrimeAPError N) ≤
      (D:ℝ)*(2*chenSwitchLog N)+
        2*(chenSwitchLog N)^2*(B+(D:ℝ)*(2*chenSwitchLog N)) := by
  have h := bvReducedPrimeClasses_of_average N (fun _ => N) (fun _ _ hd => hd.symm) hN hD hB havg
  simpa only [chenReducedError,chenPrimeAPError,chenAPError,chenDivisible_card_eq_progression,
    chenA_card_eq_primeCounting] using h

end FareyGoldbach
