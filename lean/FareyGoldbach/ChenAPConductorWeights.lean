import FareyGoldbach.ChenConductorExpansion

/-! # Reindexing the conductor packets for two coprime moduli -/

open Finset
open scoped Classical

namespace FareyGoldbach

/-- The cofactor `k=d/q` is fixed before the inner conductor sum. The factor
coming from `r` stays coprime to `q` when the original cutoff `k*q<D` is enlarged. -/
theorem chenAP_conductor_reindex (r N D : ℕ) (E : ℕ → ℕ → ℕ → ℝ)
    (hE : ∀ m q k, 0 ≤ E m q k) :
    (∑ d ∈ (Ico 1 D).filter (fun d => d.Coprime (r*N)),
      (∑ m ∈ r.divisors, ∑ q ∈ d.divisors.filter (fun q => 1<q), E m q (d/q)) /
        (d.totient:ℝ)) ≤
    ∑ m ∈ r.divisors, ∑ k ∈ Ico 1 D, (1/(k.totient:ℝ)) *
      ∑ q ∈ (Ico 2 D).filter (fun q => m.Coprime q), E m q k/(q.totient:ℝ) := by
  classical
  simp_rw [Finset.sum_div]
  rw [Finset.sum_comm]
  refine sum_le_sum fun m hm => ?_
  let F (q k : ℕ) := if m.Coprime q then E m q k / ((k*q).totient:ℝ) else 0
  have hF (q k : ℕ) : 0≤F q k := by dsimp [F]; split <;> positivity [hE m q k]
  calc
    _ = ∑ d ∈ (Ico 1 D).filter (fun d => d.Coprime (r*N)),
        ∑ q ∈ d.divisors.filter (fun q => 1<q), F q (d/q) := by
      refine sum_congr rfl fun d hd => sum_congr rfl fun q hq => ?_
      have hqd := (Nat.mem_divisors.mp (mem_filter.mp hq).1).1
      have hdr := (Nat.coprime_mul_iff_right.mp (mem_filter.mp hd).2).1
      have hmq : m.Coprime q := (hdr.symm.of_dvd_left (Nat.mem_divisors.mp hm).1).of_dvd_right hqd
      simp only [F,ite_eq_left hmq,Nat.div_mul_cancel hqd]
    _ ≤ ∑ d ∈ Ico 1 D, ∑ q ∈ d.divisors.filter (fun q => 1<q), F q (d/q) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset ..) fun d _ _ => sum_nonneg fun q _ => hF q _
    _ = _ := chenSum_divisors_swap D F
    _ ≤ _ := by
      refine sum_le_sum fun k hk => ?_
      apply (sum_le_sum_of_subset_of_nonneg (filter_subset ..)
        (fun q _ _ => hF q k) : _ ≤ ∑ q∈Ico 2 D, F q k).trans
      rw [Finset.mul_sum,Finset.sum_filter]
      refine sum_le_sum fun q hq => ?_
      dsimp only [F]
      split_ifs with hc
      · have hφk : (0:ℝ)<k.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (mem_Ico.mp hk).1)
        have hφq : (0:ℝ)<q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr
          (lt_of_lt_of_le (by decide : 0<2) (mem_Ico.mp hq).1))
        have hden : (k.totient:ℝ)*(q.totient:ℝ) ≤ ((k*q).totient:ℝ) := by
          exact_mod_cast Nat.totient_super_multiplicative k q
        exact (div_le_div_of_nonneg_left (hE ..) (mul_pos hφk hφq) hden).trans_eq (by ring)
      · rfl

end FareyGoldbach
